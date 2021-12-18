{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}

module Main where

import Prelude hiding (append, drop, foldl, reverse, toInteger)

import           Control.Monad                    (forM, replicateM)
import           Crypto.Secp256k1              
import           Crypto.Paillier                  (cipherExp, cipherMul, decrypt, encrypt, genKey)
import           Data.Bifunctor                   (first)
import           Data.ByteString                  (ByteString, append, drop, foldl, reverse, unfoldrN)
import           Data.FiniteField.Base            (order)
import           Data.FiniteField.PrimeField      (PrimeField)
import qualified Data.FiniteField.PrimeField as F (toInteger)
import           Data.List                        ((!!), groupBy, sortBy, transpose)
import           Data.List.Extra                  (allSame)
import           Data.Maybe                       (fromJust)
import           Data.Tuple                       (swap)
import           Data.Word                        (Word8)
import qualified Prelude                     as P (toInteger)
import           Test.QuickCheck                  (Property, quickCheckAll)
import           Test.QuickCheck.Monadic          (assert, monadicIO, run)
import           System.Random                    (Random, randomIO, randomRIO)
import           System.Random.Stateful           (Uniform(..), UniformRange(..))

--

type Fq = PrimeField 115792089237316195423570985008687907852837564279074904382605163141518161494337
q :: Integer
q = order @Fq undefined

instance Random Fq
instance Uniform Fq where
  uniformM = uniformRM (0, fromInteger $ q - 1)
instance UniformRange Fq where
  uniformRM (l, u) g = do
    x <- uniformRM (F.toInteger l, F.toInteger u) g
    return $ fromInteger x

fromByteString :: ByteString -> Fq
fromByteString = fromInteger . foldl f 0 . reverse where f acc w = 256 * acc + P.toInteger w

toByteString :: Fq -> ByteString 
toByteString = reverse . fst . unfoldrN 32 (Just . first fromInteger . swap . flip divMod 256) . F.toInteger

--

type Message = Fq
type SecretKey = Fq
type Signature = (Fq, Fq)

sumP :: [PubKey] -> PubKey
sumP = fromJust . combinePubKeys

aP :: Fq -> PubKey -> PubKey
aP a pk = fromJust . tweakMulPubKey pk . fromJust . tweak $ toByteString a

aG :: Fq -> PubKey
aG = derivePubKey . fromJust . secKey . toByteString

h' :: PubKey -> Fq
h' = fromByteString . drop 1 . exportPubKey True

sign' :: Fq -> SecretKey -> Message -> Signature
sign' k x m = let
  r = h' (aG k)
  s = recip k * (m + x * r)
  in (r, min s $ - s)

sign :: SecretKey -> Message -> IO Signature
sign x m = do
  k <- randomIO
  return $ sign' k x m

verify :: PubKey -> Signature -> Message -> Bool
verify pk (r, recip -> s') m = r == h' (sumP [aG (m * s'), aP (r * s') pk])

--

prop_secp256k1 :: Property
prop_secp256k1 = monadicIO $ do
  x <- randomIO
  m <- randomIO
  (r, s) <- run $ sign x m
  assert $ verify (aG x) (r, s) m
  {-
  let x' = fromJust . secKey $ toByteString x
  let m' = fromJust . msg $ toByteString m
  let rs = fromJust . importCompactSig . fromJust . compactSig $ toByteString r `append` toByteString s
  assert $ verifySig (derivePubKey x') rs m'
  -}

prop_secp256k1mpc :: Property
prop_secp256k1mpc = monadicIO $ do
  t <- randomRIO (1, 5)
  n <- randomRIO (t, t + 5)
  (x, shares) <- run $ mpcgen t n
  let xs = stoa $ take t shares
  ks <- replicateM t randomIO
  rs <- replicateM t randomIO
  let rG = sumP $ map aG rs
  deltas <- run $ mpcmul ks rs
  sigmas <- run $ mpcmul ks xs
  let delta' = recip $ sum deltas
  let r = h' (aP delta' rG)
  m <- randomIO
  let s = sum $ mpcadd (map (m *) ks) (map (r *) sigmas)
  assert $ verify (aG x) (r, s) m

--

type Polyn = [Fq]
type AShare = Fq
type SShare = (Fq, Fq)

foldrS :: (Fq -> Fq -> Fq) -> Fq -> [SShare] -> SShare
foldrS _ _ [] = error "foldrS: empty list of shares"
foldrS f z (unzip -> (is, ss))
  | allSame is = (head is, foldr f z ss)
  | otherwise = error "foldrS: incompatible shares"

sumS :: [SShare] -> SShare
sumS = foldrS (+) 0

--

genA :: Int -> IO [AShare]
genA = flip replicateM randomIO

encodeSV :: Int -> Int -> Fq -> IO ([SShare], [PubKey])
encodeSV t n x = do
  xs <- replicateM (t - 1) randomIO
  let ev i = sum . zipWith (*) (map (i ^) [0 ..])
  let p i = (i, ev i $ x : xs)
  return $ (map (p . fromIntegral) [1 .. n], map aG (x : xs))

encodeS :: Int -> Int -> Fq -> IO ([SShare])
encodeS t n x = do
  (ss, _) <- encodeSV t n x
  return ss

verifyS :: [PubKey] -> SShare -> Bool
verifyS vs (i, s) = aG s == sumP (zipWith ($) f vs) where
  f = map aP $ map (i ^) [0 ..]

stoa :: [SShare] -> [AShare]
stoa (unzip -> (is, ss)) = zipWith (*) (map lambda is) ss where
  lambda i = product js / product js' where
    js = filter (/= i) is
    js' = map (flip (-) i) js

decodeS :: [SShare] -> Fq
decodeS = sum . stoa

{-

prop_shamir_secret_sharing :: Property
prop_shamir_secret_sharing = monadicIO $ do
  t <- randomRIO (1, 5)
  n <- randomRIO (t, t + 5)
  x <- randomIO
  (shares, verifiers) <- run $ encodeSV t n x
  assert $ x == decodeS shares
  assert . and $ map (verifyS verifiers) shares

-}

mpcgen :: Int -> Int -> IO (Fq, [SShare])
mpcgen t n = do
  us <- replicateM n randomIO
  ss <- mapM (encodeS t n) us
  return (sum us, map sumS $ transpose ss)

mpcadd :: [AShare] -> [AShare] -> [AShare]
mpcadd = zipWith (+)

mtoa :: (Fq, Fq) -> IO (Fq, Fq)
mtoa (a, b) = do
  (pubkey, prvkey) <- genKey 2048
  let encrypt' = encrypt pubkey . F.toInteger
  let decrypt' = fromInteger . decrypt prvkey pubkey
  let hadd = cipherMul pubkey
  let hmul x = cipherExp pubkey x . F.toInteger
  a' <- encrypt' a
  beta <- randomIO
  beta' <- encrypt' beta
  let ab' = hmul a' b
  let alpha' = hadd ab' beta'
  let alpha = decrypt' alpha'
  return (alpha, - beta)

mpcmul :: [AShare] -> [AShare] -> IO [AShare]
mpcmul as bs = do
  ab <- forM [ (i, j) | i <- [0 .. length as - 1], j <- [0 .. length bs - 1] ] $ \(i, j) -> do
    (alpha, beta) <- mtoa (as !! i, bs !! j)
    return [(i, alpha), (j, beta)]
  return . map (sum . map snd) . groupBy (\ x y -> fst x == fst y) . sortBy (\ x y -> fst x `compare` fst y) $ concat ab

{-

prop_mpc :: Property
prop_mpc = monadicIO $ do
  t <- randomRIO (1, 5)
  n <- randomRIO (t, t + 5)
  (x, xs) <- run $ mpcgen t n
  (y, ys) <- run $ mpcgen t n
  let xs' = stoa $ take t xs
  let ys' = stoa $ take t ys
  assert $ x + y == sum (mpcadd xs' ys')
  xy <- run $ mpcmul xs' ys'
  assert $ x * y == sum xy

-}

return []

runTests :: IO Bool
runTests = $quickCheckAll

main :: IO Bool
main = runTests
