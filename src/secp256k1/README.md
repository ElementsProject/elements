libsecp256k1-zkp
================

![Dependencies: None](https://img.shields.io/badge/dependencies-none-success)

A fork of [libsecp256k1](https://github.com/bitcoin-core/secp256k1) with support for advanced and experimental features

Added features:
* Experimental module for ECDSA adaptor signatures.
* Experimental module for ECDSA sign-to-contract.
* Experimental modules for Confidential Assets (Pedersen commitments, range proofs, and [surjection proofs](src/modules/surjection/surjection.md)).
* Experimental module for [address whitelisting](src/modules/whitelist/whitelist.md).
* Experimental module for Schnorr signature half-aggregation.

Experimental features are made available for testing and review by the community. The APIs of these features should not be considered stable.

Build steps
-----------

Obtaining and verifying
-----------------------

The git tag for each release (e.g. `v0.6.0`) is GPG-signed by one of the maintainers.
For a fully verified build of this project, it is recommended to obtain this repository
via git, obtain the GPG keys of the signing maintainer(s), and then verify the release
tag's signature using git.

This can be done with the following steps:

1. Obtain the GPG keys listed in [SECURITY.md](./SECURITY.md).
2. If possible, cross-reference these key IDs with another source controlled by its owner (e.g.
   social media, personal website). This is to mitigate the unlikely case that incorrect 
   content is being presented by this repository.
3. Clone the repository: 
    ```
    git clone https://github.com/bitcoin-core/secp256k1
    ```
4. Check out the latest release tag, e.g. 
    ```
    git checkout v0.6.0
    ```
5. Use git to verify the GPG signature: 
   ```
   % git tag -v v0.6.0 | grep -C 3 'Good signature'

   gpg: Signature made Mon 04 Nov 2024 12:14:44 PM EST
   gpg:                using RSA key 4BBB845A6F5A65A69DFAEC234861DBF262123605
   gpg: Good signature from "Jonas Nick <jonas@n-ck.net>" [unknown]
   gpg:                 aka "Jonas Nick <jonasd.nick@gmail.com>" [unknown]
   gpg: WARNING: This key is not certified with a trusted signature!
   gpg:          There is no indication that the signature belongs to the owner.
   Primary key fingerprint: 36C7 1A37 C9D9 88BD E825  08D9 B1A7 0E4F 8DCD 0366
        Subkey fingerprint: 4BBB 845A 6F5A 65A6 9DFA  EC23 4861 DBF2 6212 3605
   ```

Building with Autotools
-----------------------

    $ ./autogen.sh       # Generate a ./configure script
    $ ./configure        # Generate a build system
    $ make               # Run the actual build process
    $ make check         # Run the test suite
    $ sudo make install  # Install the library into the system (optional)

To compile optional modules (such as Schnorr signatures), you need to run `./configure` with additional flags (such as `--enable-module-schnorrsig`). Run `./configure --help` to see the full list of available flags. For experimental modules, you will also need `--enable-experimental` as well as a flag for each individual module, e.g. `--enable-module-rangeproof`.

Building with CMake
-------------------

To maintain a pristine source tree, CMake encourages to perform an out-of-source build by using a separate dedicated build tree.

### Building on POSIX systems

    $ cmake -B build              # Generate a build system in subdirectory "build"
    $ cmake --build build         # Run the actual build process
    $ ctest --test-dir build      # Run the test suite
    $ sudo cmake --install build  # Install the library into the system (optional)

To compile optional modules (such as Schnorr signatures), you need to run `cmake` with additional flags (such as `-DSECP256K1_ENABLE_MODULE_SCHNORRSIG=ON`). Run `cmake -B build -LH` or `ccmake -B build` to see the full list of available flags.

### Cross compiling

To alleviate issues with cross compiling, preconfigured toolchain files are available in the `cmake` directory.
For example, to cross compile for Windows:

    $ cmake -B build -DCMAKE_TOOLCHAIN_FILE=cmake/x86_64-w64-mingw32.toolchain.cmake

To cross compile for Android with [NDK](https://developer.android.com/ndk/guides/cmake) (using NDK's toolchain file, and assuming the `ANDROID_NDK_ROOT` environment variable has been set):

    $ cmake -B build -DCMAKE_TOOLCHAIN_FILE="${ANDROID_NDK_ROOT}/build/cmake/android.toolchain.cmake" -DANDROID_ABI=arm64-v8a -DANDROID_PLATFORM=28

### Building on Windows

The following example assumes Visual Studio 2022. Using clang-cl is recommended.

In "Developer Command Prompt for VS 2022":

    >cmake -B build -T ClangCL
    >cmake --build build --config RelWithDebInfo

Usage examples
-----------

Usage examples can be found in the [examples](examples) directory. To compile them you need to configure with `--enable-examples`.
  * [ECDSA example](examples/ecdsa.c)
  * [Schnorr signatures example](examples/schnorr.c)
  * [Deriving a shared secret (ECDH) example](examples/ecdh.c)
  * [ElligatorSwift key exchange example](examples/ellswift.c)
  * [MuSig2 Schnorr multi-signatures example](examples/musig.c)

To compile the examples, make sure the corresponding modules are enabled.

Benchmark
------------
If configured with `--enable-benchmark` (which is the default), binaries for benchmarking the libsecp256k1-zkp functions will be present in the root directory after the build.

To print the benchmark result to the command line:

    $ ./bench_name

To create a CSV file for the benchmark result :

    $ ./bench_name | sed '2d;s/ \{1,\}//g' > bench_name.csv

Reporting a vulnerability
------------

See [SECURITY.md](SECURITY.md)

Contributing to libsecp256k1
------------

See [CONTRIBUTING.md](CONTRIBUTING.md)
