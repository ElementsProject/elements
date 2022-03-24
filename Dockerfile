# This Dockerfile builds Elements and packages it into a minimal `final` image

# Define default versions so that they don't have to be repeated throughout the file
ARG VER_ALPINE=3.15

# $USER name, and data $DIR to be used in the `final` image
ARG USER=elements
ARG DIR=/data

#
# This downloads a pre-built BerkeleyDB to make sure
# the overall build time of this Dockerfile fits within CI limits.
#
FROM ghcr.io/runcitadel/berkeleydb:main AS berkeleydb


FROM alpine:${VER_ALPINE} AS builder

ARG VERSION
ARG SOURCE

RUN apk add --no-cache \
        autoconf \
        automake \
        boost-dev \
        sqlite-dev \
        build-base clang clang-dev lld \
        chrpath \
        file \
        libevent-dev \
        libressl \
        libtool \
        linux-headers \
        zeromq-dev

# Fetch pre-built berkeleydb
COPY  --from=berkeleydb /opt/ /opt/

# Change to the extracted directory
WORKDIR /elements

# Copy bitcoin source (downloaded & verified in previous stages)
COPY  .  .

ENV ELEMENTS_PREFIX /opt/element

RUN ./autogen.sh

# TODO: Try to optimize on passed params
RUN ./configure LDFLAGS=-L/opt/db4/lib/ CPPFLAGS=-I/opt/db4/include/ \
    CXXFLAGS="-O2" CC=clang CXX=clang++ \
    --prefix="/opt/element" \
    --disable-man \
    --disable-shared \
    --disable-ccache \
    --disable-tests \
    --disable-bench \
    --enable-static \
    --enable-reduce-exports \
    --enable-c++17 \
    --without-gui \
    --without-libs \
    --with-utils \
    --with-sqlite=yes \
    --with-daemon

RUN make -j$(nproc)
RUN make install

FROM alpine:${VER_ALPINE} AS final

ARG USER
ARG DIR

RUN apk add --no-cache \
        boost-filesystem \
        boost-thread \
        libevent \
        libsodium \
        libstdc++ \
        libzmq \
        sqlite-libs

COPY --from=builder /opt/element/bin/elements* /usr/local/bin/

RUN adduser --disabled-password \
            --home "$DIR/" \
            --gecos "" \
            "$USER"

USER $USER

# Prevents `VOLUME $DIR/.bitcoind/` being created as owned by `root`
RUN mkdir -p "$DIR/.elements/"

# Expose volume containing all `bitcoind` data
VOLUME $DIR/.elements/

ENTRYPOINT ["elementsd"]
