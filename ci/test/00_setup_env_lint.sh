#!/usr/bin/env bash
#
# Copyright (c) 2019-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

export LC_ALL=C.UTF-8

export HOST="x86_64-pc-linux-gnu"
export CONTAINER_NAME=ci_lint
export DOCKER_NAME_TAG=ubuntu:focal
export RUN_LINT=true
export RUN_UNIT_TESTS=false
export RUN_FUNCTIONAL_TESTS=false
export GOAL=""
export BITCOIN_CONFIG=""