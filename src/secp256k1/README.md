libsecp256k1-zkp
================

![Dependencies: None](https://img.shields.io/badge/dependencies-none-success)

A fork of [libsecp256k1](https://github.com/bitcoin-core/secp256k1) with support for advanced and experimental features such as Confidential Assets and MuSig2 

Added features:
* Experimental module for ECDSA adaptor signatures.
* Experimental module for ECDSA sign-to-contract.
* Experimental module for [MuSig2](src/modules/musig/musig.md).
* Experimental module for Confidential Assets (Pedersen commitments, range proofs, and [surjection proofs](src/modules/surjection/surjection.md)).
* Experimental module for Bulletproofs++ range proofs.
* Experimental module for [address whitelisting](src/modules/whitelist/whitelist.md).

Experimental features are made available for testing and review by the community. The APIs of these features should not be considered stable.

Build steps
-----------

Building with Autotools
-----------------------

    $ ./autogen.sh
    $ ./configure
    $ make
    $ make check  # run the test suite
    $ sudo make install  # optional

To compile optional modules (such as Schnorr signatures), you need to run `./configure` with additional flags (such as `--enable-module-schnorrsig`). Run `./configure --help` to see the full list of available flags. For experimental modules, you will also need `--enable-experimental` as well as a flag for each individual module, e.g. `--enable-module-musig`.

Building with CMake (experimental)
----------------------------------

To maintain a pristine source tree, CMake encourages to perform an out-of-source build by using a separate dedicated build tree.

### Building on POSIX systems

    $ mkdir build && cd build
    $ cmake ..
    $ cmake --build .
    $ ctest  # run the test suite
    $ sudo cmake --build . --target install  # optional

To compile optional modules (such as Schnorr signatures), you need to run `cmake` with additional flags (such as `-DSECP256K1_ENABLE_MODULE_SCHNORRSIG=ON`). Run `cmake .. -LH` to see the full list of available flags.

### Cross compiling

To alleviate issues with cross compiling, preconfigured toolchain files are available in the `cmake` directory.
For example, to cross compile for Windows:

    $ cmake .. -DCMAKE_TOOLCHAIN_FILE=../cmake/x86_64-w64-mingw32.toolchain.cmake

To cross compile for Android with [NDK](https://developer.android.com/ndk/guides/cmake) (using NDK's toolchain file, and assuming the `ANDROID_NDK_ROOT` environment variable has been set):

    $ cmake .. -DCMAKE_TOOLCHAIN_FILE="${ANDROID_NDK_ROOT}/build/cmake/android.toolchain.cmake" -DANDROID_ABI=arm64-v8a -DANDROID_PLATFORM=28

### Building on Windows

To build on Windows with Visual Studio, a proper [generator](https://cmake.org/cmake/help/latest/manual/cmake-generators.7.html#visual-studio-generators) must be specified for a new build tree.

The following example assumes using of Visual Studio 2022 and CMake v3.21+.

In "Developer Command Prompt for VS 2022":

    >cmake -G "Visual Studio 17 2022" -A x64 -S . -B build
    >cmake --build build --config RelWithDebInfo

Usage examples
-----------

Usage examples can be found in the [examples](examples) directory. To compile them you need to configure with `--enable-examples`.
  * [ECDSA example](examples/ecdsa.c)
  * [Schnorr signatures example](examples/schnorr.c)
  * [Deriving a shared secret (ECDH) example](examples/ecdh.c)
  * [MuSig example](examples/musig.c)

To compile the Schnorr signature, ECDH and MuSig examples, you need to enable the corresponding module by providing a flag to the `configure` script, for example `--enable-module-schnorrsig`.

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
