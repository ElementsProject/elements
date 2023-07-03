# Elements Confidential Transactions

## Audience

This document provides an overview and introduction to
the Confidential Assets implementation in Elements. A list of relevant
RPCs is provided as well as a list of references providing further
information.  

A working knowledge of Bitcoin and Elements, familiarity with Elements
Remote Procedure Calls (RPCs), and some knowledge of the cryptography
used in Bitcoin are assumed.


## Overview of Confidential Assets

Using Elements, the sender of a transaction can hide the amounts and
types of assets in a transaction’s outputs, in such a way that: 

1. Only the sender and receiver of the transaction can see the actual
amounts and types of assets.
2. A verifier can prove that all assets coming out of a transaction
went into it. 
3. The amounts and assets of the outputs may be revealed to a third
party, by the receiver or by the sender. 

This feature is called Confidential Assets. To create a confidential
assets transaction, the recipient generates a Confidential Address and
provides it to the sender. The sender uses the address to create a
Confidential Transaction, and "blinds" its outputs, obscuring the type
and quantity of assets while guaranteeing the integrity of the
transaction. The recipient may later "unblind" and spend the
transaction's outputs at will. The unblinding process is called
"rewinding", or "rewinding the range proof", and requires the private
blinding key of the confidential address. Either the sender or a
receiver may also share a blinding key with a third party, enabling
them to view, but not to spend, the transaction's outputs. 

Confidential Assets transactions do not conceal the transaction ids or indexes on
the inputs (the transaction graph is public, as it is with Bitcoin). 

A Confidential Transaction must also include an explicit (unblinded)
fee output, paid in the sidechain's default asset (L-BTC for Liquid).


## Cryptographic Primitives

Elements' Confidential Assets capability is built on four cryptographic primitives
implemented in the secpk25k1-zkp C++ library [^1]:


### Pedersen Commitments

In a confidential transaction, asset types and amounts are blinded
using Pedersen commitments and mapped to  "asset commitments" and
"value commitments".  These commitments obscure both the asset types
and amounts, while allowing a verifier to prove that the sum of a
transaction's inputs is equal to the sum of its outputs plus the
transaction fee, without needing to see the actual amounts.


### Range Proofs

When constructing a confidential transaction using Pedersen
commitments, it is possible to introduce an output with a negative
value, thereby causing coin inflation in other outputs. To prevent
this, a cryptographic range proof is included in each blinded
transaction output. A range proof allows a verifier to prove that an
output's value lies within a specified non-negative range, without
having to see the actual value.


### Surjection Proofs

When assets are blinded in a transaction, a verifier cannot see which
input assets are sent to which outputs. A Surjection proof [^2] allows
a verifier to prove that an output’s asset appears in at least one
input, without revealing the actual asset type. In other words, the 
mapping from input assets to the output asset must be an "onto" function, or a
"surjection". Every blinded transaction output has a Surjection
proof.


### Elliptic Curve Diffie-Hellman (ECDH)

The receiver and the sender need a shared secret to blind and unblind
the outputs and to create the range proof. ECDH key exchange is used
to create the shared secret. When generating a Confidential Address,
the receiver creates a private blinding key and embeds the public key
in the address. The sender generates an ephemeral keypair, and with
the address' public blinding key, uses ECDH to generate a shared
secret. The sender's key for the ECDH key exchange is written into the
`ConfidentialNonce` field of the transaction output.

See the "Confidential Assets" paper [^3] for more detailed information
and references.

## Transaction Layout and Size Considerations

The layout and fields of a Confidential Transaction are described in
[elements-tx-format.md](./elements-tx-format.md).

Confidential Transactions are significantly larger than
non-confidential transactions due to the addition of the range and
surjection proofs.  Each blinded output adds about 4k bytes to the
transaction. As the proofs are stored in output witness fields, each
blinded output adds about 1k vBytes to the virtual size of the
transaction (please see https://en.bitcoin.it/wiki/Weight_units for
information about transaction size measurements).


### Range Proofs

A range proof proves that a value lies within a specific range. The
exact range is determined by the parameters of the range proof. A
tradeoff exists between the size of the range, and the size of the
proof’s serialization in the transaction output.  A larger range
requires a larger proof. In Elements, the default size of the range
proof is 52 bits, allowing a value up to 2^52-1 satoshis to be
represented. In Elements, it is possible to create more than 21
million satoshis of an asset over multiple issuances, but it is not
possible to send more than 21 million in any one unconfidential output.  The range
proof parameters are not part of consensus, and may be overridden and
adjusted using the `ct_bits` elements configuration parameter. Reducing
the number of bits will reduce the size of a transaction, and  also
reduce the maximum provable value of any output. 

An Elements range proof is a Borromean ring signature [^4] over
possible values of each digit in the base 4 representation of an
output value. Each digit requires the storage of 4+1 elliptic curve
points. Not including a fixed size header for the range proof, the
space required for a range proof in Elements is approximately 80 bytes
per bit of precision (default 52). 

The [secp256k1-zkp range proof implementation](https://github.com/BlockstreamResearch/secp256k1-zkp/blob/master/include/secp256k1_rangeproof.h)
supports a maximum range of 64 bits. A range proof supporting a 64 bit
range has a size of 5134 bytes.

Bulletproofs are another type of range proof that can be used for
confidential transactions. Bulletproofs are much smaller than the
range proofs currently used in Elements. See [^5] for more
information about Bulletproofs.


### Surjection Proofs

A surjection proof is a ring signature over the differences between
input and output commitments. The space required for a surjection
proof in Elements is proportional to the number of transaction inputs.
Each input adds approximately 40 bytes to the surjection proof.  In
the Elements implementation, a maximum of 256 inputs is supported. See
[^2] for more information on serialization size, and [^4] for more
information on ring signatures.


## Confidential Addresses

A confidential address combines a segwit address and a public blinding
key into a single checksummed string. This address format is called
"blech32" and is based on the "bech32" format that was introduced for
segwit. Liquid production addresses use the prefix "lq1". Liquid
regtest (elementsregtest) addresses use the prefix "el1".   

By default, the Elements RPC `getnewaddress` will return a
confidential address. A non-confidential segwit address and a public
blinding key may be combined with the RPC `createblindedaddress` to
create a confidential address. 

See the python script [../test/functional/test_framework/liquid_addr.py](../test/functional/test_framework/liquid_addr.py)
for a reference implementation of blech32 addresses.


## Workflow Considerations

The steps for manually creating a confidential transaction using
Elements RPCs are as follows: 

1. `createrawtransaction` – adds inputs and outputs to an empty
transaction. Any outputs using confidential addresses will be blinded.
2. `fundrawtransaction` – adds inputs to pay for the transaction, and
an output for change.
3. `blindrawtransaction` - blinds the outputs of a transaction, using
inputs from the wallet.
4. `rawblindrawtransaction` - can be used to blind
a transaction whose inputs are not from the local wallet; input
blinding factors must be provided.
5. `signrawtransaction` - signs inputs using the wallet. At this
point, the transaction may be broadcasted, using `sendrawtransaction`.

In the construction of a Pedersen Commitment, random blinding factors
are used in every transaction output value commitment except the
last. The last blinding factor is chosen so that the blinding factors
(and therefore the commitments) sum to zero. As a consequence, when
blinding a transaction, there must be at least one output available to
"balance the blinding factors". The Elements RPCs
`blindrawtransaction` and `blindrawtransaction` may add an additional
zero-valued output.


## Asset Issuances and Reissuances

An asset issuance creates a non-zero amount of a new asset, and zero
or more reissuance  token that may be used to create more of the same
asset at a later time. Reissuance tokens are also called "inflation
keys".  

In Elements, there are four types of transaction inputs:

1. "typical" inputs that spend UTXOs
2. coinbase inputs
3. peg-ins
4. asset issuances/reissuances.  

An asset issuance input defines the ID of a new asset, some non-zero amount
of the asset to be issued, and zero or more reissuance tokens. While
the ID of the asset must be explicit (it is a property derived
from the issuance itself), the amount of the asset issued and the
number of reissuance tokens may be blinded in the input.  

An asset reissuance input issues an additional amount of an existing
asset. The ID of the asset being reissued cannot be blinded, but the
amount of additional asset being created can be blinded in the input. 

The range proofs for an input's issuance and reissuance amounts are
stored in the input witness. 

The non-fee outputs of an issuance transaction, as in any transaction
in Elements, may be blinded. There will be at least one output for the
new asset, an explicit (unblinded) output for the transaction fee, an
optional change output, and optionally at least one output for
reissuance tokens. 

See the elements transaction format document
[elements-tx-format.md](./elements-tx-format.md) for more information.

The private key used to blind the amount of an issuance or reissuance
input may be revealed or imported into an Elements wallet, using the
RPCs `dumpissuanceblindingkey` or `importissuanceblindingkey`,
respectively.  

In summary, the id of an issued or reissued asset is always explicit,
but the issued amounts and destinations may be blinded and kept
confidential. 


## Partially Signed Elements Transactions (PSET)

Partially Signed Bitcoin Transactions (PSBT) is a document standard
that allows multiple parties to construct and sign a bitcoin
transaction offline, before broadcasting it. Elements expands on PSBT
to provide support for assets and confidential transactions, with
Partially Signed Elements Transactions (PSET).  

Several Elements RPCs provide support for working with PSETs. Note
that the PSET RPCs in Elements retain "psbt" in their names of RPCs
adapted from Bitcoin core. 

A description of PSET is outside the scope of this document. Please
see [pset.mediawiki](./pset.mediawiki) for more information.


## Elements RPCs

RPCs that are directly related to Confidential Transactions are listed 
here in the groups listed in the Elements help text. Note that some raw 
transaction RPCs appear in the Wallet section. See the Elements RPC help 
for details on parameters and invocation.


### Util

`createblindedaddress`
Creates a confidential address by combining an unconfidential address
and a public blinding key.


### Raw Transactions

`analyzepsbt`
Provides information about the blinding status of a PSET's outputs.

`createpsbt`
All blinding parameters may be set explicitly when defining a PSET.

`decoderawtransaction`
Displays a JSON representation of a raw transaction. Useful for
inspecting confidential parameters. When the wallet is able to unblind
a parameter, the unblinded value will replace the blinded value. The
"ConfidentialNonce" parameter will be displayed as "commitmentnonce".

`gettransaction`
For a transaction in this wallet, displays properties of the
transaction, including some confidential parameters such as asset and
value blinders ("blinding factors").

`getrawtransaction <txid> true`
With `verbose=true` and `txindex=1`, `getrawtransaction` will display
public details of a transaction's confidential parameters. Use
`unblindrawtransaction` followed by `decoderawtransaction` to unblind and
decode the transaction's private parameters.

`blindrawtransaction`
Blinds the outputs of a raw transaction (as might be created by
`createrawtransaction`), using only wallet inputs.

`rawblindrawtransaction`
Blinds the outputs of a raw transaction (as might be created by
`createrawtransaction`). This RPC requires that all blinding factors be
provided explicitly. 


### Wallet  - Keys and Addresses

`getnewaddress`
By default, generates a confidential address encoded as blech32 (see
"Confidential Addresses" section above). The public key is embedded in
the address along with the ScriptPubKey. A confidential address is a
tuple (confidential_key, unconfidential address). 

`getaddressinfo`
Displays the (public) confidential and unconfidential properties of an address.

`dumpblindingkey`
Reveals the private blinding key for a confidential address. A
third-party will need this key to unblind transactions (see
"Third-party Unblinding" below). 

`dumpissuanceblindingkey`
Reveals the private blinding key that was used to blind the amounts on
an issuance input. This key is required when using reissuance tokens. 

`dumpmasterblindingkey`
Reveals the wallet's master blinding key from which all blinding keys for generated addresses are derived.  See SLIP-007.

`importaddress`
A confidential address may be imported at any time. However, in order
to unblind outputs for a confidential address, it is necessary to also
import the blinding key for that address' public blinding key 
(called "confidential_key" in the RPC help). 
See the `importblindingkey` RPC.

`importblindingkey`
Imports the private blinding key associated with an address.

`importissuanceblindingkey`
Imports a private blinding key that may be used to unblind the amounts
on an issuance input or to reissue additional amounts of an asset (using
reissuance tokens). 

`importmasterblindingkey`
***Use with caution!*** Importing a master blinding key into a wallet will
erase the existing master blinding key, potentially making all
addresses owned by that wallet unspendable.


### Wallet - Transactions

`blindrawtransaction`
Blinds the outputs of a raw transaction (as might be created by `createrawtransaction`)


`unblindrawtransaction`
Unblinds a raw transaction, using addresses and blinding keys known to
the wallet (they must have been previously imported, see "Third-party
Unblinding" below).


## Third-party Unblinding (Watch-only wallets)

A third-party may be granted the ability to unblind the amounts and
assets in a confidential transaction, without being able to spend the
transaction’s UTXOs. Using Elements, the third-party would create a
"watch-only wallet" for the addresses in question, and import the
private blinding keys for those addresses.  

Let's suppose that Alice has sent a confidential transaction to
Bob. Bob wants Victor to be able to see what and how much was sent. 

Victor, with Bob’s help, creates a watch-only wallet in Elements:

1. for each address of interest A, Victor runs the RPC `importaddress
<A>`

2. Bob exports the blinding key for address A using `dumpblindingkey
<A>` and shares it with Victor.

3. Victor imports the blinding key for the address using `importblindingkey <A> <blinding key>`

Once the blinding key is imported, the Elements wallet will treat the
Confidential address address as watch-only, and its outputs will be
visible in transaction details and in the wallet balance.  

Please note that if Bob reuses an address A, Victor will also be able
to see the amounts and values in any transaction sending to A. 

Alternatively, a watch-only wallet may import the master blinding key
of another wallet. The watch-only wallet would then be able to view
the UTXOs for any confidential address created by the original
wallet. 

Anyone with the blinding key for an output's confidential address can rewind 
the rangeproof for the output, and reveal the blinding factors and actual amounts and
assets that were committed to.  

Please see the [Elements Project
tutorial](https://elementsproject.org/elements-code-tutorial/advanced-examples)
for examples of how to unblind with Elements.


## Wallet Considerations

An Elements wallet has a "master blinding key", from which all
blinding keys for that wallet are deterministically derived. A
blinding key for an address is generated as `HMAC_SHA256(master
blinding key, <address ScriptPubKey>)`. See SLIP-0077 [^6]. 

Each confidential address has an associated confidential_key, which is
a public key embedded in the address and used by the sender to create
a nonce. The private key for the confidential_key is called "blinding
key" for the address.


## Example Code

See
[contrib/assets_tutorial/assets_tutorial.py](../contrib/assets_tutorial/assets_tutorial.py)
for examples of using confidential transactions with assets. 

See
[test/functional/feature_confidential_transactions.py](../test/functional/feature_confidential_transactions.py)
for functional tests that exercise the confidential assets feature of
Elements.


## Other systems using Confidential Assets and Transactions

- Mimblewimble
- Monero
- Tari


## References

1. Blockstream Research. *libsecp256k1-zkp*
https://github.com/BlockstreamResearch/secp256k1-zkp Retrieved
2023-03-08

2. Andrew Poelstra. *Surjection Proof Module*
https://github.com/BlockstreamResearch/secp256k1-zkp/blob/master/src/modules/surjection/surjection.md
Retrieved 2023-03-08

3. Andrew Poelstra, Adam Back, Mark Friedenbach, Gregory Maxwell,
Pieter Wuille.  *Confidential
Assets*. https://blockstream.com/bitcoin17-final41.pdf Retrieved
2023-03-08.

4. Gregory Maxwell, Andrew Poelstra. *Borromean Ring Signatures*
https://www.semanticscholar.org/paper/Borromean-Ring-Signatures-%E2%88%97-Maxwell-Poelstra/4160470c7f6cf05ffc81a98e8fd67fb0c84836ea?p2df

5. Benedikt Bunz, Jonathan Bootle, Dan Boneh, Andrew Poelstra, Pieter
Wuille, Greg Maxwell. *Bulletproofs: Short Proofs for Confidential
Transactions and
More.* https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=8418611
Retrieved 2023-03-08.
 
6. SLIP-077 Proposal for wallet blinding key
derivation. https://github.com/satoshilabs/slips/blob/master/slip-0077.md 


## See Also


1. The Elements Project. *Confidential
Transactions.* https://elementsproject.org/features/confidential-transactions
Retrieved 2023-03-08

2. Tari Labs University. *Confidential Assets*
https://tlu.tarilabs.com/digital-assets/confidential-assets Retrieved
2023-03-08

3. Adam Gibson. *An investigation into Confidential
Transactions.* https://github.com/AdamISZ/ConfidentialTransactionsDoc/blob/master/essayonCT.pdf. Retrieved
2023-03-08. This document is a highly readable introduction to CT as
they were implemented in the Elements Alpha. Note that it does not
describe how asset blinding, surjection proofs, and the method of
blinding key derivation described is different than Elements’ current
algorithm.

4. Elements Project Developers. *Liquid Confidential Transaction
Walkthrough with
Libwally.* https://wally.readthedocs.io/en/release_0.8.8/Liquid/

