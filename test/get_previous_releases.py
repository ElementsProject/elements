#!/usr/bin/env python3
#
# Copyright (c) 2018-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
#
# Download or build previous releases.
# Needs curl and tar to download a release, or the build dependencies when
# building a release.

import argparse
import contextlib
from fnmatch import fnmatch
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import hashlib

SHA256_SUMS = {
    "0e2819135366f150d9906e294b61dff58fd1996ebd26c2f8e979d6c0b7a79580": "bitcoin-0.14.3-aarch64-linux-gnu.tar.gz",
    "d86fc90824a85c38b25c8488115178d5785dbc975f5ff674f9f5716bc8ad6e65": "bitcoin-0.14.3-arm-linux-gnueabihf.tar.gz",
    "1b0a7408c050e3d09a8be8e21e183ef7ee570385dc41216698cc3ab392a484e7": "bitcoin-0.14.3-osx64.tar.gz",
    "706e0472dbc933ed2757650d54cbcd780fd3829ebf8f609b32780c7eedebdbc9": "bitcoin-0.14.3-x86_64-linux-gnu.tar.gz",
    #
    "d40f18b4e43c6e6370ef7db9131f584fbb137276ec2e3dba67a4b267f81cb644": "bitcoin-0.15.2-aarch64-linux-gnu.tar.gz",
    "54fb877a148a6ad189a1e1ab1ff8b11181e58ff2aaf430da55b3fd46ae549a6b": "bitcoin-0.15.2-arm-linux-gnueabihf.tar.gz",
    "87e9340ff3d382d543b2b69112376077f0c8b4f7450d372e83b68f5a1e22b2df": "bitcoin-0.15.2-osx64.tar.gz",
    "566be44190fd76daa01f13d428939dadfb8e3daacefc8fa17f433cad28f73bd5": "bitcoin-0.15.2-x86_64-linux-gnu.tar.gz",
    #
    "0768c6c15caffbaca6524824c9563b42c24f70633c681c2744649158aa3fd484": "bitcoin-0.16.3-aarch64-linux-gnu.tar.gz",
    "fb2818069854a6ad20ea03b28b55dbd35d8b1f7d453e90b83eace5d0098a2a87": "bitcoin-0.16.3-arm-linux-gnueabihf.tar.gz",
    "78c3bff3b619a19aed575961ea43cc9e142959218835cf51aede7f0b764fc25d": "bitcoin-0.16.3-osx64.tar.gz",
    "5d422a9d544742bc0df12427383f9c2517433ce7b58cf672b9a9b17c2ef51e4f": "bitcoin-0.16.3-x86_64-linux-gnu.tar.gz",
    #
    "5a6b35d1a348a402f2d2d6ab5aed653a1a1f13bc63aaaf51605e3501b0733b7a": "bitcoin-0.17.2-aarch64-linux-gnu.tar.gz",
    "d1913a5d19c8e8da4a67d1bd5205d03c8614dfd2e02bba2fe3087476643a729e": "bitcoin-0.17.2-arm-linux-gnueabihf.tar.gz",
    "a783ba20706dbfd5b47fbedf42165fce70fbbc7d78003305d964f6b3da14887f": "bitcoin-0.17.2-osx64.tar.gz",
    "943f9362b9f11130177839116f48f809d83478b4c28591d486ee9a7e35179da6": "bitcoin-0.17.2-x86_64-linux-gnu.tar.gz",
    #
    "88f343af72803b851c7da13874cc5525026b0b55e63e1b5e1298390c4688adc6": "bitcoin-0.18.1-aarch64-linux-gnu.tar.gz",
    "cc7d483e4b20c5dabd4dcaf304965214cf4934bcc029ca99cbc9af00d3771a1f": "bitcoin-0.18.1-arm-linux-gnueabihf.tar.gz",
    "b7bbcee7a7540f711b171d6981f939ca8482005fde22689bc016596d80548bb1": "bitcoin-0.18.1-osx64.tar.gz",
    "425ee5ec631ae8da71ebc1c3f5c0269c627cf459379b9b030f047107a28e3ef8": "bitcoin-0.18.1-riscv64-linux-gnu.tar.gz",
    "600d1db5e751fa85903e935a01a74f5cc57e1e7473c15fd3e17ed21e202cfe5a": "bitcoin-0.18.1-x86_64-linux-gnu.tar.gz",
    #
    "3a80431717842672df682bdb619e66523b59541483297772a7969413be3502ff": "bitcoin-0.19.1-aarch64-linux-gnu.tar.gz",
    "657f28213823d240dd3324d14829702f9ad6f0710f8bdd1c379cb3c447197f48": "bitcoin-0.19.1-arm-linux-gnueabihf.tar.gz",
    "1ae1b87de26487075cd2fd22e0d4ead87d969bd55c44f2f1d873ecdc6147ebb3": "bitcoin-0.19.1-osx64.tar.gz",
    "aa7a9563b48aa79252c8e7b6a41c07a5441bd9f14c5e4562cc72720ea6cb0ee5": "bitcoin-0.19.1-riscv64-linux-gnu.tar.gz",
    "5fcac9416e486d4960e1a946145566350ca670f9aaba99de6542080851122e4c": "bitcoin-0.19.1-x86_64-linux-gnu.tar.gz",
    #
    "60c93e3462c303eb080be7cf623f1a7684b37fd47a018ad3848bc23e13c84e1c": "bitcoin-0.20.1-aarch64-linux-gnu.tar.gz",
    "55b577e0fb306fb429d4be6c9316607753e8543e5946b542d75d876a2f08654c": "bitcoin-0.20.1-arm-linux-gnueabihf.tar.gz",
    "b9024dde373ea7dad707363e07ec7e265383204127539ae0c234bff3a61da0d1": "bitcoin-0.20.1-osx64.tar.gz",
    "fa71cb52ee5e0459cbf5248cdec72df27995840c796f58b304607a1ed4c165af": "bitcoin-0.20.1-riscv64-linux-gnu.tar.gz",
    "376194f06596ecfa40331167c39bc70c355f960280bd2a645fdbf18f66527397": "bitcoin-0.20.1-x86_64-linux-gnu.tar.gz",

    "43416854330914992bbba2d0e9adf2a6fff4130be9af8ae2ef1186e743d9a3fe": "bitcoin-0.21.0-aarch64-linux-gnu.tar.gz",
    "f028af308eda45a3c4c90f9332f96b075bf21e3495c945ebce48597151808176": "bitcoin-0.21.0-arm-linux-gnueabihf.tar.gz",
    "695fb624fa6423f5da4f443b60763dd1d77488bfe5ef63760904a7b54e91298d": "bitcoin-0.21.0-osx64.tar.gz",
    "f8b2adfeae021a672effbc7bd40d5c48d6b94e53b2dd660f787340bf1a52e4e9": "bitcoin-0.21.0-riscv64-linux-gnu.tar.gz",
    "da7766775e3f9c98d7a9145429f2be8297c2672fe5b118fd3dc2411fb48e0032": "bitcoin-0.21.0-x86_64-linux-gnu.tar.gz",

    "ac718fed08570a81b3587587872ad85a25173afa5f9fbbd0c03ba4d1714cfa3e": "bitcoin-22.0-aarch64-linux-gnu.tar.gz",
    "b8713c6c5f03f5258b54e9f436e2ed6d85449aa24c2c9972f91963d413e86311": "bitcoin-22.0-arm-linux-gnueabihf.tar.gz",
    "2744d199c3343b2d94faffdfb2c94d75a630ba27301a70e47b0ad30a7e0155e9": "bitcoin-22.0-osx64.tar.gz",
    "2cca5f99007d060aca9d8c7cbd035dfe2f040dd8200b210ce32cdf858479f70d": "bitcoin-22.0-powerpc64-linux-gnu.tar.gz",
    "91b1e012975c5a363b5b5fcc81b5b7495e86ff703ec8262d4b9afcfec633c30d": "bitcoin-22.0-powerpc64le-linux-gnu.tar.gz",
    "9cc3a62c469fe57e11485fdd32c916f10ce7a2899299855a2e479256ff49ff3c": "bitcoin-22.0-riscv64-linux-gnu.tar.gz",
    "59ebd25dd82a51638b7a6bb914586201e67db67b919b2a1ff08925a7936d1b16": "bitcoin-22.0-x86_64-linux-gnu.tar.gz",

    "06f4c78271a77752ba5990d60d81b1751507f77efda1e5981b4e92fd4d9969fb":  "bitcoin-23.0-aarch64-linux-gnu.tar.gz",
    "952c574366aff76f6d6ad1c9ee45a361d64fa04155e973e926dfe7e26f9703a3":  "bitcoin-23.0-arm-linux-gnueabihf.tar.gz",
    "7c8bc63731aa872b7b334a8a7d96e33536ad77d49029bad179b09dca32cd77ac":  "bitcoin-23.0-arm64-apple-darwin.tar.gz",
    "2caa5898399e415f61d9af80a366a3008e5856efa15aaff74b88acf429674c99":  "bitcoin-23.0-powerpc64-linux-gnu.tar.gz",
    "217dd0469d0f4962d22818c368358575f6a0abcba8804807bb75325eb2f28b19":  "bitcoin-23.0-powerpc64le-linux-gnu.tar.gz",
    "078f96b1e92895009c798ab827fb3fde5f6719eee886bd0c0e93acab18ea4865":  "bitcoin-23.0-riscv64-linux-gnu.tar.gz",
    "c816780583009a9dad426dc0c183c89be9da98906e1e2c7ebae91041c1aaaaf3":  "bitcoin-23.0-x86_64-apple-darwin.tar.gz",
    "2cca490c1f2842884a3c5b0606f179f9f937177da4eadd628e3f7fd7e25d26d0":  "bitcoin-23.0-x86_64-linux-gnu.tar.gz",
}


@contextlib.contextmanager
def pushd(new_dir) -> None:
    previous_dir = os.getcwd()
    os.chdir(new_dir)
    try:
        yield
    finally:
        os.chdir(previous_dir)


def download_binary(tag, args) -> int:
    if Path(tag).is_dir():
        if not args.remove_dir:
            print('Using cached {}'.format(tag))
            return 0
        shutil.rmtree(tag)
    Path(tag).mkdir()
    bin_path = 'bin/bitcoin-core-{}'.format(tag[1:])
    match = re.compile('v(.*)(rc[0-9]+)$').search(tag)
    if match:
        bin_path = 'bin/bitcoin-core-{}/test.{}'.format(
            match.group(1), match.group(2))
    platform = args.platform
    if tag < "v23" and platform in ["x86_64-apple-darwin", "arm64-apple-darwin"]:
        platform = "osx64"
    tarball = 'bitcoin-{tag}-{platform}.tar.gz'.format(
        tag=tag[1:], platform=platform)
    tarballUrl = 'https://bitcoincore.org/{bin_path}/{tarball}'.format(
        bin_path=bin_path, tarball=tarball)

    print('Fetching: {tarballUrl}'.format(tarballUrl=tarballUrl))

    header, status = subprocess.Popen(
        ['curl', '--head', tarballUrl], stdout=subprocess.PIPE).communicate()
    if re.search("404 Not Found", header.decode("utf-8")):
        print("Binary tag was not found")
        return 1

    curlCmds = [
        ['curl', '--remote-name', tarballUrl]
    ]

    for cmd in curlCmds:
        ret = subprocess.run(cmd).returncode
        if ret:
            return ret

    hasher = hashlib.sha256()
    with open(tarball, "rb") as afile:
        hasher.update(afile.read())
    tarballHash = hasher.hexdigest()

    if tarballHash not in SHA256_SUMS or SHA256_SUMS[tarballHash] != tarball:
        if tarball in SHA256_SUMS.values():
            print("Checksum did not match")
            return 1

        print("Checksum for given version doesn't exist")
        return 1
    print("Checksum matched")

    # Extract tarball
    ret = subprocess.run(['tar', '-zxf', tarball, '-C', tag,
                          '--strip-components=1',
                          'bitcoin-{tag}'.format(tag=tag[1:])]).returncode
    if ret:
        return ret

    Path(tarball).unlink()
    return 0


def build_release(tag, args) -> int:
    githubUrl = "https://github.com/bitcoin/bitcoin"
    if args.remove_dir:
        if Path(tag).is_dir():
            shutil.rmtree(tag)
    if not Path(tag).is_dir():
        # fetch new tags
        subprocess.run(
            ["git", "fetch", githubUrl, "--tags"])
        output = subprocess.check_output(['git', 'tag', '-l', tag])
        if not output:
            print('Tag {} not found'.format(tag))
            return 1
    ret = subprocess.run([
        'git', 'clone', githubUrl, tag
    ]).returncode
    if ret:
        return ret
    with pushd(tag):
        ret = subprocess.run(['git', 'checkout', tag]).returncode
        if ret:
            return ret
        host = args.host
        if args.depends:
            with pushd('depends'):
                ret = subprocess.run(['make', 'NO_QT=1']).returncode
                if ret:
                    return ret
                host = os.environ.get(
                    'HOST', subprocess.check_output(['./config.guess']))
        config_flags = '--prefix={pwd}/depends/{host} '.format(
            pwd=os.getcwd(),
            host=host) + args.config_flags
        cmds = [
            './autogen.sh',
            './configure {}'.format(config_flags),
            'make',
        ]
        for cmd in cmds:
            ret = subprocess.run(cmd.split()).returncode
            if ret:
                return ret
        # Move binaries, so they're in the same place as in the
        # release download
        Path('bin').mkdir(exist_ok=True)
        files = ['bitcoind', 'bitcoin-cli', 'bitcoin-tx']
        for f in files:
            Path('src/'+f).rename('bin/'+f)
    return 0


def check_host(args) -> int:
    args.host = os.environ.get('HOST', subprocess.check_output(
        './depends/config.guess').decode())
    if args.download_binary:
        platforms = {
            'aarch64-*-linux*': 'aarch64-linux-gnu',
            'x86_64-*-linux*': 'x86_64-linux-gnu',
            'x86_64-apple-darwin*': 'x86_64-apple-darwin',
            'aarch64-apple-darwin*': 'arm64-apple-darwin',
        }
        args.platform = ''
        for pattern, target in platforms.items():
            if fnmatch(args.host, pattern):
                args.platform = target
        if not args.platform:
            print('Not sure which binary to download for {}'.format(args.host))
            return 1
    return 0


def main(args) -> int:
    Path(args.target_dir).mkdir(exist_ok=True, parents=True)
    print("Releases directory: {}".format(args.target_dir))
    ret = check_host(args)
    if ret:
        return ret
    if args.download_binary:
        with pushd(args.target_dir):
            for tag in args.tags:
                ret = download_binary(tag, args)
                if ret:
                    return ret
        return 0
    args.config_flags = os.environ.get('CONFIG_FLAGS', '')
    args.config_flags += ' --without-gui --disable-tests --disable-bench'
    with pushd(args.target_dir):
        for tag in args.tags:
            ret = build_release(tag, args)
            if ret:
                return ret
    return 0


if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument('-r', '--remove-dir', action='store_true',
                        help='remove existing directory.')
    parser.add_argument('-d', '--depends', action='store_true',
                        help='use depends.')
    parser.add_argument('-b', '--download-binary', action='store_true',
                        help='download release binary.')
    parser.add_argument('-t', '--target-dir', action='store',
                        help='target directory.', default='releases')
    parser.add_argument('tags', nargs='+',
                        help="release tags. e.g.: v0.18.1 v0.20.0rc2")
    args = parser.parse_args()
    sys.exit(main(args))
