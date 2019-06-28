FROM centos:centos7.6.1810

RUN set -x \
    && yum install -y epel-release \
    && yum install -y centos-release-scl \
    && yum groupinstall -y "Development Tools" "Development Libraries" \
    && yum install -y \
    rpm-build \
    git \
    curl \
    libtool \
    binutils \
    bsdmainutils \
    pkgconfig \
    python36 \
    patch \
    autogen \
    which \
    wget \
    glibc-devel \
    libstdc++-devel\
    glibc \
    gd \
    gd-devel \
    libstdc++ \
    autoconf \
    automake \
    bison \
    flex \
    gcc \
    gcc-c++ \
    libgcc \
    glibc-devel \
    glibc-common \
    glibc-headers \
    kernel-headers \
    gettext \
    make \
    redhat-rpm-config \
    libdb4-cxx \
    libdb4-cxx-devel \
    boost-devel \
    openssl-devel \
    protobuf-devel \
    db4-devel \
    zlib-devel \
    swig \
    openssl-devel \
    libevent-devel \
    libdb4-devel \
    python3 \
    bzip2 \
    libstdc++.x86_64 \
    devtoolset-7 \
    devtoolset-7-gcc.x86_64 \
    devtoolset-7-gcc-c++.x86_64 \
    devtoolset-7-libstdc++-devel.x86_64 \
    scl-utils \
    && ln -s -f /usr/bin/python36 /usr/bin/python3 \
    && wget https://dl.google.com/go/go1.12.6.linux-amd64.tar.gz \
    && tar -xzf go1.12.6.linux-amd64.tar.gz \
    && mv go /usr/local \
    && export GOROOT=/usr/local/go \
    && export GOPATH=$HOME \
    && export PATH=$GOPATH/bin:$GOROOT/bin:$PATH \
    && go get github.com/google/go-github/github \
    && go get github.com/oleiade/reflections \
    && go get golang.org/x/oauth2 \
    && git clone https://github.com/commerceblock/ocean.git \
    && cd ocean/depends \
    && make
