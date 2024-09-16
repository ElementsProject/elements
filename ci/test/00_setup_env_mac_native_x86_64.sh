#!/usr/bin/env bash
#
# Copyright (c) 2019-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

export LC_ALL=C.UTF-8

export HOST=x86_64-apple-darwin
export PIP_PACKAGES="zmq lief"
export GOAL="install"
# ELEMENTS: add -fno-stack-check to work around clang bug on macos
export BITCOIN_CONFIG="--with-gui --enable-reduce-exports CXXFLAGS=-fno-stack-check"
export CI_OS_NAME="macos"
export NO_DEPENDS=1
export OSX_SDK=""
export CCACHE_SIZE=300M
export RUN_SECURITY_TESTS="true"
