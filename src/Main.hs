{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}

module Main where

import Prelude hiding (foldl, toInteger)

import           Control.Monad                    (forM, replicateM)
import           Crypto.Secp256k1              
import           Crypto.Paillier                  (cipherExp, cipherMul, decrypt, encrypt, genKey)
import           Data.Bifunctor                   (first)
import           Data.ByteString                  (ByteString, foldl, unfoldr)
import           Data.FiniteField.Base            (order)
import           Data.FiniteField.PrimeField      (PrimeField)
import qualified Data.FiniteField.PrimeField as F (toInteger)
import           Data.List                        ((!!), groupBy, transpose)
import           Data.List.Extra                  (allSame)
import           Data.Tuple                       (swap)
import           Data.Word                        (Word8)
import qualified Prelude                     as P (toInteger)
import           Test.QuickCheck                  (Property, quickCheckAll)
import           Test.QuickCheck.Monadic          (assert, monadicIO, run)
import           System.Random                    (Random, randomIO, randomRIO)
import           System.Random.Stateful           (Uniform(..), UniformRange(..))

--

type Fp = PrimeField 115792089237316195423570985008687907852837564279074904382605163141518161494337
instance Random Fp
instance Uniform Fp where
  uniformM = uniformRM (0, fromInteger $ order @Fp undefined - 1)
instance UniformRange Fp where
  uniformRM (l, u) g = do
    x <- uniformRM (F.toInteger l, F.toInteger u) g
    return $ fromInteger x

fromByteString :: ByteString -> Fp
fromByteString = fromInteger . foldl f 0 where
  f acc w = 256 * acc + P.toInteger w

toByteString :: Fp -> ByteString 
toByteString = unfoldr f . F.toInteger where
  f 0 = Nothing
  f i = Just . first fromInteger . swap $ i `divMod` 256

--

type Polyn = [Fp]
type AShare = Fp
type SShare = (Fp, Fp)

foldrS :: (Fp -> Fp -> Fp) -> Fp -> [SShare] -> SShare
foldrS _ _ [] = error "foldrS: empty list of shares"
foldrS f z (unzip -> (is, ss))
  | allSame is = (head is, foldr f z ss)
  | otherwise = error "foldrS: incompatible shares"

sumS :: [SShare] -> SShare
sumS = foldrS (+) 0

--

genA :: Int -> IO [AShare]
genA = flip replicateM randomIO

encodeS :: Int -> Int -> Fp -> IO [SShare]
encodeS t n x = do
  xs <- replicateM (t - 1) randomIO
  let ev i = sum . zipWith (*) (map (i ^) [0 ..])
  let p i = (i, ev i $ x : xs)
  return $ map (p . fromIntegral) [1 .. n]

stoa :: [SShare] -> [AShare]
stoa (unzip -> (is, ss)) = zipWith (*) (map lambda is) ss where
  lambda i = product js / product js' where
    js = filter (/= i) is
    js' = map (flip (-) i) js

decodeS :: [SShare] -> Fp
decodeS = sum . stoa

--

prop_shamir_secret_sharing :: Property
prop_shamir_secret_sharing = monadicIO $ do
  t <- randomRIO (1, 5)
  n <- randomRIO (t, t + 5)
  x <- randomIO
  shares <- run $ encodeS t n x
  assert $ x == decodeS shares

--

mpcgen :: Int -> Int -> IO (Fp, [SShare])
mpcgen t n = do
  us <- replicateM n randomIO
  ss <- mapM (encodeS t n) us
  return (sum us, map sumS $ transpose ss)

mpcadd :: [AShare] -> [AShare] -> [AShare]
mpcadd = zipWith (+)

mtoa :: (Fp, Fp) -> IO (Fp, Fp)
mtoa (a, b) = do
  (pubkey, prvkey) <- genKey 100
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
  return . map (sum . map snd) . groupBy (\ x y -> fst x == fst y) $ concat ab

--

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

--

return []

runTests :: IO Bool
runTests = $quickCheckAll

main :: IO Bool
main = runTests
