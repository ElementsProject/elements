#!/bin/bash

# This script is to be used to generate Gitian builds for Elements releases.
# Requirements:
# - One needs the OSX SDK file in the following location:
#   bec9d089ebf2e2dd59b1a811a38ec78ebd5da18cbbcd6ab39d1e59f64ac5033f  $HOME/blockstream/gitian/MacOSX10.11.sdk.tar.gz
#   The file can be downloaded here:
#   https://bitcoincore.org/depends-sources/sdks/MacOSX10.11.sdk.tar.gz
#
# - On an Arch machine, I had to install and start apt-cacher-ng.
#   Any non-Debian environment probably should do the same.
#   $ sudo systemctl start apt-cacher-ng
# 
# - You'll need a bunch of basic packages from your distro. Non-exhaustive:
#   git, docker
#
# - User must have access to /tmp. /tmp/gitian and /tmp/elements are used in the process.
#
#
#
# Using the script:
# Just invoke the script and pass the tag you want to build as an argument:
# ./gitian-build.sh elements-0.18.1.6



: ${1?Need commit hash or tag}

rm -fr /tmp/gitian /tmp/elements
export USE_DOCKER=1
export NUM_JOB=$(cat /proc/cpuinfo | grep ^processor | wc -l)

export CI_PROJECT_DIR=/tmp/elements
export CI_COMMIT_TAG=$1
git clone https://github.com/devrandom/gitian-builder.git /tmp/gitian           

RESULT_DIR=$HOME/blockstream/gitian/out/$CI_COMMIT_TAG
mkdir -p "$RESULT_DIR"

git clone https://github.com/ElementsProject/elements.git ${CI_PROJECT_DIR}
cd ${CI_PROJECT_DIR}
mkdir /tmp/gitian/inputs
cp $HOME/blockstream/gitian/MacOSX10.11.sdk.tar.gz /tmp/gitian/inputs/MacOSX10.11.sdk.tar.gz

cd /tmp/gitian

bin/make-base-vm --docker --suite bionic --arch amd64

bin/gbuild --num-make ${NUM_JOB} --memory 10000 --url elements=${CI_PROJECT_DIR} --commit elements=${CI_COMMIT_TAG} ${CI_PROJECT_DIR}/contrib/gitian-descriptors/gitian-linux.yml

cp result/* $RESULT_DIR
cp -r build/out/* $RESULT_DIR

bin/gbuild --num-make ${NUM_JOB} --memory 10000 --url elements=${CI_PROJECT_DIR} --commit elements=${CI_COMMIT_TAG} ${CI_PROJECT_DIR}/contrib/gitian-descriptors/gitian-win.yml

cp result/* $RESULT_DIR
cp -r build/out/* $RESULT_DIR

bin/gbuild --num-make ${NUM_JOB} --memory 10000 --url elements=${CI_PROJECT_DIR} --commit elements=${CI_COMMIT_TAG} ${CI_PROJECT_DIR}/contrib/gitian-descriptors/gitian-osx.yml

cp result/* $RESULT_DIR
cp -r build/out/* $RESULT_DIR

# Afterwards, move all but the following files into another folder (I call it `unused`):
# - elements-<version>-aarch64-linux-gnu.tar.gz
# - elements-<version>-arm-linux-gnueabihf.tar.gz
# - elements-<version>-i686-pc-linux-gnu.tar.gz
# - elements-<version>-osx64.tar.gz
# - elements-<version>-osx-unsigned.dmg
# - elements-<version>-osx-unsigned.tar.gz
# - elements-<version>-riscv64-linux-gnu.tar.gz
# - elements-<version>-win32-setup-unsigned.exe
# - elements-<version>-win32.zip
# - elements-<version>-win64-setup-unsigned.exe
# - elements-<version>-win64.zip
# - elements-<version>-win-unsigned.tar.gz
# - elements-<version>-x86_64-linux-gnu.tar.gz

# Then create SHA256SUMS.asc as follows:
#sha256sum <all files except unused; you get this by typing * then tab> | gpg2 --armor --clearsign > SHA256SUMS.asc

