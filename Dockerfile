FROM commerceblock/base

COPY . /usr/src/package

# Build Ocean
RUN set -ex \
    && cd /usr/src/package \
    && ./autogen.sh \
    && ./configure \
    && make clean \
    && make  -j$(nproc)\
    && echo "Running tests" \
    && make check \
    && echo "Running Python QA tests" \
    && ./qa/pull-tester/rpc-tests.py \
    && make install \
    && make clean \
    && cd /usr/src \
    && rm -rf /usr/src/package

COPY contrib/docker/docker-entrypoint.sh /docker-entrypoint.sh

ENTRYPOINT ["/docker-entrypoint.sh"]
CMD ["oceand"]
