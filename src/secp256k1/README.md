libsecp256k1-zkp
================

[![Build Status](https://api.cirrus-ci.com/github/BlockstreamResearch/secp256k1-zkp.svg?branch=master)](https://cirrus-ci.com/github/BlockstreamResearch/secp256k1-zkp)
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

libsecp256k1-zkp is built using autotools:

    $ ./autogen.sh
    $ ./configure
    $ make
    $ make check  # run the test suite
    $ sudo make install  # optional

To compile optional modules (such as Schnorr signatures), you need to run `./configure` with additional flags (such as `--enable-module-schnorrsig`). Run `./configure --help` to see the full list of available flags. For experimental modules, you will also need `--enable-experimental` as well as a flag for each individual module, e.g. `--enable-module-musig`.

Usage examples
-----------

Usage examples can be found in the [examples](examples) directory. To compile them you need to configure with `--enable-examples`.
  * [ECDSA example](examples/ecdsa.c)
  * [Schnorr signatures example](examples/schnorr.c)
  * [Deriving a shared secret (ECDH) example](examples/ecdh.c)
  * [MuSig example](examples/musig.c)

To compile the Schnorr signature, ECDH and MuSig examples, you need to enable the corresponding module by providing a flag to the `configure` script, for example `--enable-module-schnorrsig`.

Test coverage
-----------

This library aims to have full coverage of the reachable lines and branches.

To create a test coverage report, configure with `--enable-coverage` (use of GCC is necessary):

    $ ./configure --enable-coverage

Run the tests:

    $ make check

To create a report, `gcovr` is recommended, as it includes branch coverage reporting:

    $ gcovr --exclude 'src/bench*' --print-summary

To create a HTML report with coloured and annotated source code:

    $ mkdir -p coverage
    $ gcovr --exclude 'src/bench*' --html --html-details -o coverage/coverage.html

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
