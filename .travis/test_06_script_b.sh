#!/usr/bin/env bash
#
# Copyright (c) 2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

export LC_ALL=C.UTF-8

cd "build/elements-$HOST" || (echo "could not enter distdir build/bitcoin-$HOST"; exit 1)

if [ "$RUN_UNIT_TESTS" = "true" ]; then
  BEGIN_FOLD unit-tests
  DOCKER_EXEC LD_LIBRARY_PATH=$TRAVIS_BUILD_DIR/depends/$HOST/lib make $MAKEJOBS check VERBOSE=1
  END_FOLD
fi

if [ "$RUN_FUNCTIONAL_TESTS" = "true" ]; then
  BEGIN_FOLD functional-tests
  DOCKER_EXEC test/functional/test_runner.py --ci --combinedlogslen=4000 --coverage --quiet --failfast
  END_FOLD
fi

if [ "$RUN_FUZZ_TESTS" = "true" ]; then
  BEGIN_FOLD fuzz-tests
  DOCKER_EXEC test/fuzz/test_runner.py -l DEBUG ${DIR_FUZZ_IN}
  END_FOLD
fi

if [ "$RUN_UNIT_TESTS" = "true" ]; then
  BEGIN_FOLD unit-tests
  DOCKER_EXEC LD_LIBRARY_PATH=$TRAVIS_BUILD_DIR/depends/$HOST/lib make $MAKEJOBS check VERBOSE=1
  END_FOLD
fi

if [ "$RUN_BITCOIN_TESTS" = "true" ]; then
    BEGIN_FOLD bitcoin-functional-tests
    DOCKER_EXEC test/bitcoin_functional/functional/test_runner.py --combinedlogslen=4000 --coverage --quiet --failfast ${extended}
    END_FOLD
fi

if [ "$RUN_FEDPEG_BITCOIND_TEST" = "true" ]; then
    BEGIN_FOLD fedpeg-bitcoind-test
    BITCOIND_VERSION=0.18.0
    BITCOIND_ARCH=x86_64-linux-gnu
    DOCKER_EXEC curl -O https://bitcoincore.org/bin/bitcoin-core-$BITCOIND_VERSION/bitcoin-$BITCOIND_VERSION-$BITCOIND_ARCH.tar.gz
    DOCKER_EXEC tar -zxf bitcoin-$BITCOIND_VERSION-$BITCOIND_ARCH.tar.gz
    DOCKER_EXEC test/functional/feature_fedpeg.py --parent_bitcoin --parent_binpath $(pwd)/bitcoin-$BITCOIND_VERSION/bin/bitcoind
    END_FOLD
fi

if [ "$TRAVIS_EVENT_TYPE" = "cron" ]; then
  extended="--extended --exclude feature_pruning"
fi
