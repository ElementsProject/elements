FROM centos:centos7.6.1810

RUN set -x \
    && yum install -y epel-release \
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
    && ln -s -f /usr/bin/python36 /usr/bin/python3 \
    && wget https://dl.google.com/go/go1.12.6.linux-amd64.tar.gz \
    && tar -xzf go1.12.6.linux-amd64.tar.gz \
    && mv go /usr/local \
    && export GOROOT=/usr/local/go \
    && export GOPATH=$HOME \
    && export PATH=$GOPATH/bin:$GOROOT/bin:$PATH \
    && git clone https://github.com/commerceblock/ocean.git -b docker_rpm_spec \
    && cd ocean/depends \
    && make \
    && cd .. \
    && ./autogen.sh \
    && ./configure --enable-glibc-back-compat \
        --prefix=`pwd`/depends/x86_64-pc-linux-gnu \
        LDFLAGS="-static-libstdc++" \
        CC="/usr/bin/gcc" \
    && make \
    && cd ocean/contrib/docker/rpm-build \
    && rpmbuild ocean.spec
