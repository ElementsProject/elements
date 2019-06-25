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
    bzip2 \
    libstdc++.x86_64 \
    devtoolset-7-gcc.x86_64 \
    devtoolset-7-gcc-c++.x86_64 \
    devtoolset-7-libstdc++-devel.x86_64 \
    && ln -s -f /usr/bin/python36 /usr/bin/python3 \
    && wget http://ftp.mirrorservice.org/sites/sourceware.org/pub/gcc/releases/gcc-7.3.0/gcc-7.3.0.tar.gz \
    && tar zxf gcc-7.3.0.tar.gz \
    && cd gcc-7.3.0 \
    && ./contrib/download_prerequisites \
    && ./configure --disable-multilib --enable-languages=c,c++ \
    && make \
    && make install \
    && cd .. \
    && wget https://dl.google.com/go/go1.12.6.linux-amd64.tar.gz \
    && tar -xzf go1.12.6.linux-amd64.tar.gz \
    && mv go /usr/local \
    && export GOROOT=/usr/local/go \
    && export GOPATH=$HOME \
    && export PATH=$GOPATH/bin:$GOROOT/bin:$PATH \
    && git clone https://github.com/commerceblock/ocean.git -b docker_rpm_spec \
    && cd ocean/depends \
    && make \
    && cd ..

RUN scl enable devtoolset-7 bash \
    && ./autogen.sh \
    && ./configure --enable-glibc-back-compat \
        --prefix=`pwd`/depends/x86_64-pc-linux-gnu \
        LDFLAGS="-static-libstdc++" \
        CC="/opt/rh/devtoolset-7/root/usr/bin/gcc" \
        CXX="/opt/rh/devtoolset-7/root/usr/bin/g++" \
        LD_LIBRARY_PATH="/opt/rh/devtoolset-7/root/usr/lib64:/opt/rh/devtoolset-7/root/usr/lib:/opt/rh/devtoolset-7/root/usr/lib64/dyninst:/opt/rh/devtoolset-7/root/usr/lib/dyninst:/opt/rh/devtoolset-7/root/usr/lib64:/opt/rh/devtoolset-7/root/usr/lib" \
    && make \
    && cd ocean/contrib/docker/rpm-build \
    && rpmbuild ocean.spec
