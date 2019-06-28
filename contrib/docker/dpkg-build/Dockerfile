FROM commerceblock/debbase:latest

ARG token
ENV GITHUB_RELEASE_ACCESS_TOKEN=$token
ARG repository
ENV GITHUB_RELEASE_REPOSITORY=$repository
ARG commit
ENV GITHUB_RELEASE_COMMIT=$commit
ARG tag
ENV GITHUB_RELEASE_TAG=$tag

RUN set -ex \
    && cd ocean \
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
    && go run github-release/main.go "Debian package" \
        ocean-$(git rev-parse --short HEAD).deb
