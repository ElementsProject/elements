FROM commerceblock/base:d7cf239

COPY . /usr/src/package

# Build Ocean
RUN set -ex \
    && cd /usr/src/package \
    && ./autogen.sh \
    && ./configure --without-gui \
    && make clean \
    && make \
    && echo "Running tests" \
    && make check \
    && echo "Running Python QA tests" \
    && ./qa/pull-tester/rpc-tests.py \
    && make install \
    && make clean \
    && cd /usr/src \
    && mkdir -p /home/bitcoin/.bitcoin \
    && cp -R package/doc/terms-and-conditions /home/bitcoin/.bitcoin \
    && chown -R bitcoin:bitcoin /home/bitcoin \
    && rm -rf package

COPY contrib/docker/docker-entrypoint.sh /docker-entrypoint.sh

ENTRYPOINT ["/docker-entrypoint.sh"]
CMD ["oceand"]
