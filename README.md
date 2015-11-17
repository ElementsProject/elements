The Elements Project
=================================
This is the integration and staging tree for the Elements Project, a series of
improvements and extensions to the Bitcoin protocol.

What is the Elements Project?
-----------------
Elements is an open source collaborative project where we work on a collection
of experiments to more rapidly bring technical innovation to Bitcoin.  Elements
are features that are proposed and developed in this technical community that in
arbitrary combinations can be fashioned into sidechains.

https://github.com/ElementsProject/elementsproject.github.io

Learn more on [the Elements Project website](https://www.elementsproject.org).

What is Bitcoin?
----------------
https://www.bitcoin.org

Bitcoin is an experimental new digital currency that enables instant payments to
anyone, anywhere in the world. Bitcoin uses peer-to-peer technology to operate
with no central authority: managing transactions and issuing money are carried
out collectively by the network. Elements Alpha is the name of open source
software which enables the use of this currency.

For more information, as well as an immediately useable, binary version of
the Bitcoin Core software, see https://www.bitcoin.org/en/download.

What is Elements Alpha?
-----------------------
https://github.com/ElementsProject/elements/tree/alpha

Elements Alpha is the Elements project's first experimental test chain.

Compared to Bitcoin itself, it adds the following features:
 * [Confidential Transactions][confidential-transactions]
 * [Segregated Witness][segregated-witness]
 * [Relative Lock Time][relative-lock-time]
 * [Schnorr Signatures][schnorr-signatures]
 * [Additional opcodes][opcodes]
 * [Deterministic Peg (pegged to Bitcoin's testnet currency).][deterministic-peg]
 * [Signed Blocks][signed-blocks]

Getting Started
---------------
See alpha-README.md for build and use instructions.

License
-------
Elements Alpha is released under the terms of the MIT license. See [COPYING](COPYING) for more
information or see http://opensource.org/licenses/MIT.

## Testing
Testing and code review is the bottleneck for development; we get more pull
requests than we can review and test on short notice. Please be patient and help out by testing
other people's pull requests, and remember this is a security-critical project where any mistake might cost people
lots of money.

### Automated Testing

Developers are strongly encouraged to write unit tests for new code, and to
submit new unit tests for old code. Unit tests can be compiled and run
(assuming they weren't disabled in configure) with: `make check`

There are also [regression and integration tests](/qa) of the RPC interface, written
in Python, that are run automatically on the build server.
These tests can be run with: `qa/pull-tester/rpc-tests.py`

The Travis CI system makes sure that every pull request is built for Windows
and Linux, OSX, and that unit and sanity tests are automatically run.

### Manual Quality Assurance (QA) Testing

Changes should be tested by somebody other than the developer who wrote the
code. This is especially important for large or high-risk changes. It is useful
to add a test plan to the pull request description if testing the changes is
not straightforward.

[confidential-transactions]: https://www.elementsproject.org/elements/confidential-transactions
[segregated-witness]: https://www.elementsproject.org/elements/segregated-witness
[relative-lock-time]: https://www.elementsproject.org/elements/relative-lock-time
[schnorr-signatures]: https://www.elementsproject.org/elements/schnorr-signatures
[opcodes]: https://www.elementsproject.org/elements/opcodes
[deterministic-peg]: https://www.elementsproject.org/elements/deterministic-pegs
[signed-blocks]: https://www.elementsproject.org/elements/signed-blocks
