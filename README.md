Elements blockchain platform
=================================
This is the integration and staging tree for the Elements blockchain platform,
a collection of feature experiments and extensions to the Bitcoin protocol.
This platform enables anyone to build their own businesses or networks
pegged to Bitcoin as a sidechain or run as a standalone blockchain with arbitrary asset tokens.

Confidential Assets
----------------
The latest feature in the Elements blockchain platform is Confidential Assets,
the ability to issue multiple assets on a blockchain where asset identifiers
and amounts are blinded yet auditable through the use of applied cryptography.

 * [Announcement of Confidential Assets](https://blockstream.com/2017/04/03/blockstream-releases-elements-confidential-assets.html)
 * [Confidential Assets Whitepaper](https://blockstream.com/bitcoin17-final41.pdf) to be presented [April 7th at Financial Cryptography 2017](http://fc17.ifca.ai/bitcoin/schedule.html) in Malta
 * [Confidential Assets Tutorial](contrib/assets_tutorial/assets_tutorial.sh)
 * [Confidential Assets Demo](https://github.com/ElementsProject/confidential-assets-demo)
 * [Elements Code Tutorial](https://elementsproject.org/elements-code-tutorial/overview) covering blockchain configuration and how to use the main features.

Features of the Elements blockchain platform
----------------

Compared to Bitcoin itself, it adds the following features:
 * [Confidential Assets][asset-issuance]
 * [Confidential Transactions][confidential-transactions]
 * [Federated Two-Way Peg][federated-peg]
 * [Signed Blocks][signed-blocks]
 * [Additional opcodes][opcodes]

Previous elements that have been integrated into Bitcoin:
 * Segregated Witness
 * Relative Lock Time

Elements deferred for additional research and standardization:
 * [Schnorr Signatures][schnorr-signatures]

License
-------
Elements is released under the terms of the MIT license. See [COPYING](COPYING) for more
information or see http://opensource.org/licenses/MIT.

[confidential-transactions]: https://elementsproject.org/features/confidential-transactions
[opcodes]: https://elementsproject.org/features/opcodes
[federated-peg]: https://elementsproject.org/features#federatedpeg
[signed-blocks]: https://elementsproject.org/features#signedblocks
[asset-issuance]: https://elementsproject.org/features/issued-assets
[schnorr-signatures]: https://elementsproject.org/features/schnorr-signatures

What is the Elements Project?
-----------------
Elements is an open source, sidechain-capable blockchain platform. It also allows experiments to more rapidly bring technical innovation to the Bitcoin ecosystem.

Learn more on the [Elements Project website](https://elementsproject.org)

https://github.com/ElementsProject/elementsproject.github.io
