FROM commerceblock/rpmbase:latest

ARG token
ENV GITHUB_RELEASE_ACCESS_TOKEN=$token
ARG repository
ENV GITHUB_RELEASE_REPOSITORY=$repository
ARG commit
ENV GITHUB_RELEASE_COMMIT=$commit
ARG tag
ENV GITHUB_RELEASE_TAG=$tag

SHELL [ "/usr/bin/scl", "enable", "devtoolset-7"]
RUN set -ex \
    && cd ocean \
    && git pull \
    && export gittag=$(git describe --tags --match '[0-9].[0-9].[0-9]*') \
    && export GITHUB_RELEASE_TAG=$gittag
    && git checkout $gittag \
    && ./autogen.sh \
    && ./configure --enable-glibc-back-compat \
        --prefix=`pwd`/depends/x86_64-pc-linux-gnu \
        LDFLAGS="-static-libstdc++" \
        CC="/opt/rh/devtoolset-7/root/usr/bin/gcc" \
        CXX="/opt/rh/devtoolset-7/root/usr/bin/g++" \
        LD_LIBRARY_PATH="/opt/rh/devtoolset-7/root/usr/lib64:/opt/rh/devtoolset-7/root/usr/lib:/opt/rh/devtoolset-7/root/usr/lib64/dyninst:/opt/rh/devtoolset-7/root/usr/lib/dyninst:/opt/rh/devtoolset-7/root/usr/lib64:/opt/rh/devtoolset-7/root/usr/lib" \
    && make \
    && cd contrib/docker/rpm-build \
    && sed -i "s/Release: .*/Release: ${gittag//-}/" \
       ocean.spec \
    && rpmbuild -bb ocean.spec \
    && export GOROOT=/usr/local/go \
    && export GOPATH=$HOME \
    && export PATH=$GOPATH/bin:$GOROOT/bin:$PATH \
    && git clone https://github.com/buildkite/github-release.git \
    && go run github-release/main.go "RPM package" \
        /root/rpmbuild/RPMS/x86_64/ocean-1.0-${gittag//-}.x86_64.rpm
