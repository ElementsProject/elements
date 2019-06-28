FROM ubuntu:18.04

RUN set -ex \
    && apt-get -y update \
    && apt-get -y install make automake cmake curl g++-multilib libtool \
        binutils-gold bsdmainutils pkg-config python3 patch git golang-go \
    && git clone https://github.com/buildkite/github-release.git \
    && go get github.com/google/go-github/github \
    && go get github.com/oleiade/reflections \
    && go get golang.org/x/oauth2 \
    && git clone https://github.com/commerceblock/ocean.git \
    && cd ocean/depends \
    && make \
