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
    && git pull \
    && export gittag=$(git describe --tags --match '[0-9].[0-9].[0-9]*') \
    && export GITHUB_RELEASE_TAG=$gittag \
    && ./autogen.sh \
    && ./configure --enable-glibc-back-compat \
        --prefix=`pwd`/depends/x86_64-pc-linux-gnu \
        LDFLAGS="-static-libstdc++" \
    && make \
    && mkdir -p ocean-$gittag/usr/local/bin \
    && cp src/oceand ocean-$gittag/usr/local/bin/ \
    && cp src/ocean-cli ocean-$gittag/usr/local/bin/ \
    && cp src/ocean-tx ocean-$gittag/usr/local/bin/ \
    && mkdir -p ocean-$gittag/DEBIAN \
    && cp contrib/docker/dpkg-build/control \
        ocean-$gittag/DEBIAN/ \
    && sed -i "s/Version: .*/Version: $gittag/" \
        ocean-$gittag/DEBIAN/control \
    && dpkg-deb --build ocean-$gittag \
    && go run github-release/main.go "Debian package" \
        ocean-$gittag.deb
