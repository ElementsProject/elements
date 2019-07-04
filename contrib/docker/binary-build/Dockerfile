FROM commerceblock:ubuntuoceanbase

ARG token
ENV GITHUB_RELEASE_ACCESS_TOKEN=$token
ARG repository
ENV GITHUB_RELEASE_REPOSITORY=$repository
ARG commit
ENV GITHUB_RELEASE_COMMIT=$commit
ARG tag
ENV GITHUB_RELEASE_TAG=$tag

RUN set -ex \
    && git clone https://github.com/commerceblock/ocean.git \
    && export gittag=$(git describe --tags --match '[0-9].[0-9].[0-9]*') \
    && export GITHUB_RELEASE_TAG=$gittag \
    && git checkout $gittag \
    && cd ocean/depends \
    && make \
    && cd .. \
    && ./autogen.sh \
    && ./configure --enable-glibc-back-compat \
        --prefix=`pwd`/depends/x86_64-pc-linux-gnu LDFLAGS="-static-libstdc++" \
    && make \
    && tar -cvf ocean.tar --directory src oceand ocean-cli ocean-tx \
    && go run github-release/main.go "Linux binaries" ocean.tar
