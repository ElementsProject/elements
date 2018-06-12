FROM centos:centos7.4.1708

ENV GOSU_VERSION 1.10
ENV GOSU_ARCH amd64
ENV GOSU_URL https://github.com/tianon/gosu/releases/download
ENV GOSU_APP ${GOSU_URL}/${GOSU_VERSION}/gosu-${GOSU_ARCH}
ENV GOSU_ASC ${GOSU_URL}/${GOSU_VERSION}/gosu-${GOSU_ARCH}.asc
ENV DB4_VERSION 4.8.30.NC
ENV DB4_HASH 12edc0df75bf9abd7f82f821795bcee50f42cb2e5f76a6a281b85732798364ef
ENV DB4_URL http://download.oracle.com/berkeley-db/db-${DB4_VERSION}.tar.gz

COPY . /usr/src/package

# Setup required system packages
RUN set -x \
    && yum install -y epel-release

RUN set -x \
    && yum install -y \
        gcc \
        gcc-c++ \
        make \
        git \
        curl-devel \
        libevent-devel \
        tcl-devel \
        tk-devel \
        curl-devel \
        zlib-devel \
        bzip2-devel \
        openssl-devel \
        ncurses-devel \
        readline-devel \
        gdbm-devel \
        file \
        libpcap-devel \
        xz-devel \
        expat-devel \
        snappy-devel \
        libevent-devel \
        libdb4-devel \
        libdb4-cxx-devel \
        zeromq-devel \
        gmp-devel \
        mpfr-devel \
        libmpc-devel \
        which \
        autoconf \
        automake \
        libtool \
        boost-devel \
        iproute \
        jq \
        python36

# gosu
RUN set -x \
    && adduser -m bitcoin \
    && chown bitcoin:bitcoin /home/bitcoin \
	&& curl -o /usr/local/bin/gosu -SL ${GOSU_APP} \
	&& curl -o /usr/local/bin/gosu.asc -SL ${GOSU_ASC} \
	&& export GNUPGHOME="$(mktemp -d)" \
	&& gpg --keyserver ha.pool.sks-keyservers.net --recv-keys \
        B42F6819007F00F88E364FD4036A9C25BF357DD4 \
	&& gpg --batch --verify /usr/local/bin/gosu.asc /usr/local/bin/gosu \
	&& rm -rf "$GNUPGHOME" /usr/local/bin/gosu.asc \
	&& chmod +x /usr/local/bin/gosu \
    && gosu nobody true

# Build Berkeley DB
RUN set -x \
    && cd /usr/src \
    && curl ${DB4_URL} -o db-${DB4_VERSION} \
    && echo "${DB4_HASH} db-${DB4_VERSION}" | sha256sum -c || exit 1 \
    && tar zxvf db-${DB4_VERSION} \
    && cd db-${DB4_VERSION}/build_unix \
    && ../dist/configure --prefix=/usr --enable-compat185 \
        --enable-dbm --disable-static --enable-cxx --with-pic \
    && make -j$(nproc) \
    && make install \
    && make clean

# Build Package
RUN set -x \
    && cd /usr/src/package \
    && ./autogen.sh \
    && ./configure \
    && make -j$(nproc) \
    && make install \
    && make clean

# Cleanup
RUN set -x \
    && yum clean all \
    && rm -rf /var/cache/yum \
    && rm -rf /usr/src/{package,db-"$DB4_VERSION"}

COPY docker/docker-entrypoint.sh /docker-entrypoint.sh

ENTRYPOINT ["/docker-entrypoint.sh"]
CMD ["elementsd"]