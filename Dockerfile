FROM ubuntu:bionic

LABEL name="Elements image"
RUN apt-get update -y 

# Install apt dependencies
RUN apt install git build-essential libtool autotools-dev autoconf pkg-config libssl-dev libboost-all-dev libqt5core5a libqt5dbus5 qttools5-dev qttools5-dev-tools libprotobuf-dev protobuf-compiler imagemagick librsvg2-bin libqrencode-dev autoconf openssl libssl-dev libevent-dev libminiupnpc-dev jq wget bsdmainutils libdb++-dev -y 

# Install berkeley db
RUN mkdir bdb4
RUN wget 'http://download.oracle.com/berkeley-db/db-4.8.30.NC.tar.gz'
RUN tar -xzvf db-4.8.30.NC.tar.gz
RUN sed -i 's/__atomic_compare_exchange/__atomic_compare_exchange_db/g' db-4.8.30.NC/dbinc/atomic.h
WORKDIR db-4.8.30.NC/build_unix/
RUN ../dist/configure --enable-cxx --disable-shared --with-pic --prefix=/bdb4/
RUN make install

# Build elements
ADD . /code
WORKDIR /code
RUN ./autogen.sh
RUN ./configure LDFLAGS="-L/bdb4/lib/" CPPFLAGS="-I/bdb4/include/"
RUN make
RUN make install


