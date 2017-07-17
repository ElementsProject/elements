Elements blockchain platform
=================================
This is the integration and staging tree for the Elements blockchain platform,
a collection of feature experiments and extensions to the Bitcoin protocol.
This platform enables anyone to build their own businesses or networks
involving sidechain pegged Bitcoin or arbitrary asset tokens.

Confidential Assets
----------------
The latest feature in the Elements blockchain platform is Confidential Assets,
the ability to issue multiple assets on a blockchain where asset identifiers
and amounts are blinded yet auditable through the use of applied cryptography.

 * [Announcement of Confidential Assets](https://blockstream.com/2017/04/03/blockstream-releases-elements-confidential-assets.html)
 * [Confidential Assets Whitepaper](https://blockstream.com/bitcoin17-final41.pdf) to be presented [April 7th at Financial Cryptography 2017](http://fc17.ifca.ai/bitcoin/schedule.html) in Malta
 * [Confidential Assets Tutorial](contrib/assets_tutorial/assets_tutorial.sh)
 * [Confidential Assets Demo](https://github.com/ElementsProject/confidential-assets-demo)

Features of the Elements blockchain platform
----------------

Compared to Bitcoin itself, it adds the following features:
 * [Confidential Assets][asset-issuance]
 * [Confidential Transactions][confidential-transactions]
 * [Additional opcodes][opcodes]
 * [Deterministic Peg][deterministic-peg]
 * [Signed Blocks][signed-blocks]

Previous elements that have been integrated into Bitcoin:
 * [Segregated Witness][segregated-witness]
 * [Relative Lock Time][relative-lock-time]

Elements deferred for additional research and standardization:
 * [Schnorr Signatures][schnorr-signatures]

License
-------
Elements is released under the terms of the MIT license. See [COPYING](COPYING) for more
information or see http://opensource.org/licenses/MIT.

[confidential-transactions]: https://www.elementsproject.org/elements/confidential-transactions
[segregated-witness]: https://www.elementsproject.org/elements/segregated-witness
[relative-lock-time]: https://www.elementsproject.org/elements/relative-lock-time
[schnorr-signatures]: https://www.elementsproject.org/elements/schnorr-signatures
[opcodes]: https://www.elementsproject.org/elements/opcodes
[deterministic-peg]: https://www.elementsproject.org/elements/deterministic-pegs
[signed-blocks]: https://www.elementsproject.org/elements/signed-blocks
[asset-issuance]: https://www.elementsproject.org/elements/asset-issuance

What is the Elements Project?
-----------------
Elements is an open source collaborative project where we work on a collection
of experiments to more rapidly bring technical innovation to the Bitcoin ecosystem.

https://github.com/ElementsProject/elementsproject.org

Learn more on [the Elements Project website](https://www.elementsproject.org).
