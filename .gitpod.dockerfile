FROM haskell:latest
USER root
RUN apt-get update && apt-get -y install pkg-config libsecp256k1-0 libsecp256k1-dev

