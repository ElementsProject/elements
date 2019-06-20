FROM ubuntu:18.04

ARG token
ENV GITHUB_RELEASE_ACCESS_TOKEN=$token
ARG repository
ENV GITHUB_RELEASE_REPOSITORY=$repository
ARG commit
ENV GITHUB_RELEASE_COMMIT=$commit
ARG tag
ENV GITHUB_RELEASE_TAG=$tag

RUN set -ex \
    && apt-get -y update \
    && apt-get -y install make automake cmake curl g++-multilib libtool \
        binutils-gold bsdmainutils pkg-config python3 patch git golang-go \
    && git clone https://github.com/commerceblock/ocean.git \
    && cd ocean/depends \
    && make \
    && cd .. \
    && ./autogen.sh \
    && ./configure --enable-glibc-back-compat \
        --prefix=`pwd`/depends/x86_64-pc-linux-gnu \
        LDFLAGS="-static-libstdc++" \
    && make \
    && mkdir -p ocean-$(git rev-parse --short HEAD)/usr/local/bin \
    && cp src/oceand ocean-$(git rev-parse --short HEAD)/usr/local/bin/ \
    && cp src/ocean-cli ocean-$(git rev-parse --short HEAD)/usr/local/bin/ \
    && cp src/ocean-tx ocean-$(git rev-parse --short HEAD)/usr/local/bin/ \
    && mkdir -p ocean-$(git rev-parse --short HEAD)/DEBIAN \
    && cp contrib/docker/dpkg-build/control \
        ocean-$(git rev-parse --short HEAD)/DEBIAN/ \
    && sed -i "s/Version:*/Version: $(git rev-parse --short HEAD)/" \
        ocean-$(git rev-parse --short HEAD)/DEBIAN/control \
    && dpkg-deb --build ocean-$(git rev-parse --short HEAD) \
    && git clone https://github.com/buildkite/github-release.git \
    && go get github.com/google/go-github/github \
    && go get github.com/oleiade/reflections \
    && go get golang.org/x/oauth2 \
    && go run github-release/main.go "Debian package" \
        ocean-$(git rev-parse --short HEAD).deb
