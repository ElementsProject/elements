#!/usr/bin/env bash
#
# Copyright (c) 2020-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

export LC_ALL=C.UTF-8

export HOST=i686-pc-linux-gnu
export CONTAINER_NAME=ci_i686_centos
export DOCKER_NAME_TAG=quay.io/centos/centos:stream8
export DOCKER_PACKAGES="gcc-c++ glibc-devel.x86_64 libstdc++-devel.x86_64 glibc-devel.i686 libstdc++-devel.i686 ccache libtool make git python3 python3-pip which patch lbzip2 xz procps-ng dash rsync coreutils bison"
export PIP_PACKAGES="pyzmq"
export GOAL="install"
export BITCOIN_CONFIG="--enable-zmq --with-gui=qt5 --enable-reduce-exports"
export CONFIG_SHELL="/bin/dash"
export TEST_RUNNER_ENV="LC_ALL=en_US.UTF-8"
