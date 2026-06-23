#!/usr/bin/env bash
#
# Copyright (c) 2019-present The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

export LC_ALL=C.UTF-8

# Homebrew's python@3.12 is marked as externally managed (PEP 668).
# Therefore, `--break-system-packages` is needed.
export PIP_PACKAGES="--break-system-packages zmq"
export GOAL="install"
export CMAKE_GENERATOR="Ninja"
# ELEMENTS: add -fno-stack-check to work around clang bug on macos
# ELEMENTS: add -Wno-error=deprecated-declarations for C++20 deprecation warnings with boost 1.85
export BITCOIN_CONFIG="\
 -DBUILD_GUI=ON \
 -DWITH_ZMQ=ON \
 -DREDUCE_EXPORTS=ON \
 -DCMAKE_CXX_FLAGS='-fno-stack-check -Wno-error=deprecated-declarations' \
"
export CI_OS_NAME="macos"
export NO_DEPENDS=1
export OSX_SDK=""
