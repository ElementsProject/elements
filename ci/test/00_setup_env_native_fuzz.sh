#!/usr/bin/env bash
#
# Copyright (c) 2019-2022 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

export LC_ALL=C.UTF-8

export CI_IMAGE_NAME_TAG="ubuntu:24.04"
export CONTAINER_NAME=ci_native_fuzz
export PACKAGES="clang-16 llvm-16 libclang-rt-16-dev python3 libevent-dev bsdmainutils libboost-dev libsqlite3-dev"
export NO_DEPENDS=1
export RUN_UNIT_TESTS=false
export RUN_FUNCTIONAL_TESTS=false
export RUN_FUZZ_TESTS=true
export FUZZ_TESTS_CONFIG="--exclude=coins_view"  # work around https://github.com/bitcoin/bitcoin/issues/22233
export GOAL="install"
export BITCOIN_CONFIG="--enable-fuzz --with-sanitizers=fuzzer,address,undefined,integer CC='clang-16 -ftrivial-auto-var-init=pattern' CXX='clang++-16 -ftrivial-auto-var-init=pattern'"
export CCACHE_SIZE=200M
