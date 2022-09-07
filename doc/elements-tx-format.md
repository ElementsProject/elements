# Elements Transaction Format

This document describes the format used to serialize Elements transactions. Once a transaction has been converted into this raw, serialized form, it can be broadcast across the network.

This document assumes some familiarity with Bitcoin and Elements (UTXOs, [Script](https://en.bitcoin.it/wiki/Script), assets, peg-ins, etc.). For more information on those, please refer to the [Bitcoin Wiki](https://en.bitcoin.it/wiki/Main_Page) and the [Elements Code Tutorial](https://elementsproject.org/elements-code-tutorial/overview).

### Data Types

*Notes*:
* Fields in the following table are listed in the same order in which they are serialized.

* The *Encoding* column in the following tables indicates how the fields are serialized.

* All values are defined in terms of the smallest indivisible unit. For example, a value of 1 L-BTC would be defined as 100,000,000 (L-Satoshis).

#### Transaction

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Version | Yes | 4 bytes | `int32_t` | Little-endian | Transaction version number. Currently version 2 (see [BIP 68](https://github.com/bitcoin/bips/blob/master/bip-0068.mediawiki#specification)). | |
| Flags | Yes | 1 byte | `unsigned char` | | 1 if the transaction contains a witness, otherwise 0. All other values are invalid. |
| Num Inputs | Yes | Varies | `VarInt` | | Number of inputs to the transaction. |
| Inputs | Yes | Varies | `Vector<TxIn>` | | |
| Num Outputs | Yes | Varies | `VarInt` | | Number of outputs from the transaction. |
| Outputs | Yes | Varies | `Vector<TxOut>` | | |
| Locktime | Yes | 4 bytes | `uint32_t` | Little-endian | See [BIP 113](https://github.com/bitcoin/bips/blob/master/bip-0113.mediawiki). |
| Witness | Only if flags is 1 | Varies | `Witness` | | See [BIP 141](https://github.com/bitcoin/bips/blob/master/bip-0141.mediawiki). Note that Elements witnesses contain more data than Bitcoin witnesses. This extra data is described further below. |

Notable differences from Bitcoin:
- In Bitcoin the *Flags* field is optional and it is two bytes long. In Elements, this field is mandatory and it is reduced to one byte.
- In Bitcoin, only inputs have witnesses. In Elements, each output also has a witness section associated with it.
- In Bitcoin transactions the *Locktime* appears immediately after the witnesses, whereas in Elements transactions it appears right before them.

This is the overarching structure of a serialized transaction. The rest of this document contains further details on specific parts, as well as examples.

#### Variable Length Integer (VarInt)

This data type is derived from Bitcoin, and allows an integer to be encoded with a variable length (which depends on the represented value), in order to save space.
Variable length integers always precede a vector of a type of data that may vary in length and are used to indicate this length.
Longer numbers are encoded in little-endian.

| Value | Size | Format | Example |
| ----- | ---- | ------ | ------- |
| < `0xFD` | 1 byte | `uint8_t` | `0x0F` = 15 |
| <= `0xFFFF` | 3 bytes | `0xFD` followed by the number as a `uint16_t` | `0xFD 00FF` = 65 280 |
| <= `0xFFFF FFFF` | 5 bytes | `0xFE` followed by the number as a `uint32_t` | `0xFE 0000 00FF` = 4 278 190 080 |
| <= `0xFFFF FFFF FFFF FFFF` | 9 bytes | `0xFF` followed by the number as a `uint64_t` | `0xFF 0000 0000 0000 00FF` = 18 374 686 479 671 623 680 |

#### Vector\<Type\>

Each `Vector` begins with a `VarInt` describing the number of items it contains.

If the vector is of type `hex`, then the size / structure of each individual item is not known in advance. In this case, each item begins with a `VarInt` describing its size `s` in bytes, followed by `s` bytes which should be interpreted as the item itself.
Otherwise, size prefixes are omitted, and each item should be interpreted in accordance with the vector's type.

In other words, the vector is serialized as follows: `[Length (n)][Item #1][Item #2][...][Item #n]`.

Refer to the examples section below for more concrete examples of serialized vectors.

#### TxIn

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Output Hash (TXID) | Yes | 32 bytes | `hex` | [^1] | |
| Output Index | Yes | 4 bytes | `uint32_t` | Little-endian | **Input is a coinbase**: `0xffffffff`<br><br>The two most significant bits are reserved for flags.<br><br>**Input is a peg-in:** second most significant bit is 1.<br><br>**Input has an asset issuance:** most significant bit is 1. |
| ScriptSig Length | Yes | Varies | `VarInt` | | Set to `0x00` if the transaction is SegWit and the witness contains the signature. |
| ScriptSig | If ScriptSig Length is non-zero | Varies | `hex` | | |
| Sequence | Yes | 4 bytes | `uint32_t` | Little-endian | |
| Asset Issuance | Only if the transaction has an issuance (as indicated by the Output Index) | Varies | `AssetIssuance` |  | |

[^1]: The hex encodings of hashes by the Elements client (TXID, asset ID) are byte-reversed, and so the bytes will need to be re-reversed to match the serialized data. This is the same situation as in Bitcoin. For example, the hash `1123...deff` would be displayed by the Bitcoin and Elements clients as `ffde...2311`. This is primarily for historical reasons: the Bitcoin client has always interpreted and displayed hashes as little-endian integers and parsed their bytes in reverse order.

Notable differences from Bitcoin:
- In Elements, the *Output Index* field uses the two most significant bits to flag if the transaction is a peg-in transaction (1 << 30) or if it is an issuance (1 << 31). If these flags are present, they must be removed to refer to the output's index.
- Inputs can allow for the issuance of new assets or for reissuances of these assets. To create a new asset, any input being spent can be used and a 0 value must be used in the issuance's blinding nonce field. To reissue an asset, the asset blinding factor is used in the issuance's blinding nonce field, and the asset being spent must be of the reissuance token's asset type.

#### TxOut

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Asset | Yes | 33 bytes | `ConfidentialAsset` | | Cannot be null. |
| Amount | Yes | 9 or 33 bytes | `ConfidentialAmount` | | Cannot be null. |
| Nonce | Yes | 1 or 33 bytes | `ConfidentialNonce` | | |
| ScriptPubKey Length | Yes | Varies | `VarInt` | | | |
| ScriptPubKey | If ScriptPubKey Length is non-zero | Varies | `hex` | | |

#### Witness

As noted above, the witness is only present for SegWit transactions.

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Input Witnesses | Yes | Varies | `Vector<InputWitness>` | | There is exactly one input witness for each input in the transaction.<br><br>This number is not explicitly included in the witness — it is implied by the number of inputs. |
| Output Witnesses | Yes | Varies | `Vector<OutputWitness>` | | There is exactly one output witness for each output in the transaction.<br><br>This number is not explicitly included in the witness — it is implied by the number of outputs. |

#### InputWitness

SegWit transactions have one such witness for each input.

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Issuance Amount Range Proof | Yes | Varies | `Proof` | | `0x00` → null. |
| Inflation Keys Range Proof | Yes | Varies | `Proof` | | `0x00` → null. |
| Script Witness | Yes | Varies | `Vector<hex>` | | The vector represents the witness stack.<br>Can be empty (length of 0). |
| Peg-in Witness | Yes | Varies | `Vector<hex>` | | The vector represents the witness stack.<br>Can be empty (length of 0). |

The range proofs must be empty if their associated amounts (issuance / inflation keys) are explicit.
Refer [here](https://elementsproject.org/features/confidential-transactions/investigation) for more details on range proofs.

A non-empty peg-in witness stack should always have a length of 6, and the items should be interpreted as follows:

1. The little-endian 64-bit value of the peg-in for the peg-in transaction.
2. Asset ID of the asset being pegged in.
3. The 32 byte genesis hash of the blockchain which originated the peg-in.
4. Claim script for the peg-in transaction.
5. The mainchain peg-in transaction serialized without witnesses.
6. Merkle proof of transaction inclusion, from the mainchain.

See *Example #3* in the Examples section below for a concrete example.

Notable differences from Bitcoin:
- Each input witness has four fields, rather than just one witness stack.

#### OutputWitness

SegWit transactions have one such witness for each output.

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Surjection Proof | Yes | Varies | `Proof` | | A non-null value indicates that the corresponding output's asset is blinded. |
| Range Proof | Yes | Varies | `Proof` | | A non-null value indicates that the corresponding output's value is blinded. |

It is possible for an output's asset to be blinded but not its value, and vice-versa.

More details:
- [Confidential Assets](https://blockstream.com/bitcoin17-final41.pdf)
- [Range Proofs](https://elementsproject.org/features/confidential-transactions/investigation)
- [Surjection Proofs](https://github.com/ElementsProject/elements/blob/master/src/secp256k1/src/modules/surjection/surjection.md)
#### AssetIssuance

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Asset Blinding Nonce | Yes | 32 bytes | `hex` | | Zero for a new asset issuance; otherwise a blinding factor for the input. |
| Asset Entropy | Yes | 32 bytes | `hex` | | **New issuances:** Freeform entropy field, no consensus-defined meaning, but is used as additional entropy to the asset tag calculation.<br><br>**Reissuances:** Required to be the asset's entropy value (from its initial issuance). |
| Amount | Yes | 1 or 9 or 33 bytes | `ConfidentialAmount` | | Amount of the asset to issue. Both explicit and blinded amounts are supported.<br><br>**Note**: cannot be explicitly set to 0 (should be null instead). |
| Num Inflation Keys | Yes | 1 or 9 or 33 bytes | `ConfidentialAmount` | | Number of inflation keys to issue. Both explicit and blinded amounts are supported.<br><br>**Notes:**<br>  - Cannot be explicitly set to 0 (should be null instead).<br>  - Inflation keys cannot be reissued. |

#### ConfidentialAsset

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Header | Yes | 1 byte | | | A header byte of `0x00` indicates a “null” value with no subsequent bytes.<br><br>A header byte of `0x01` indicates an “explicit” value with the following 32 bytes denoting the key used to generate the asset ID (little-endian).<br><br>A header byte of `0x0a` or `0x0b` indicates a blinded value encoded as a compressed elliptic curve point. With the least significant bit of the header byte denoting the least significant bit of the y-coordinate, and the remaining 32 bytes denoting the x-coordinate (big-endian). The point must be a point on the curve. |
| Value | If header byte is not `0x00` | 32 bytes | `hex` | Depends on header byte | |

#### ConfidentialAmount

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Header | Yes | 1 byte | | | A header byte of `0x00` indicates a “null” value with no subsequent bytes.<br><br>A header byte of `0x01` indicates an “explicit” value with the following 8 bytes denoting a 64-bit value (big-endian).  This value must be between 0 and `MAX_MONEY` inclusive.<br><br>A header byte of `0x08` or `0x09` indicates a blinded value encoded as a compressed elliptic curve point. With the least significant bit of the header byte denoting the least significant bit of the y-coordinate, and the remaining 32 bytes denoting the x-coordinate (big-endian). The point must be a point on the curve. |
| Value | If header byte is not `0x00` | 8 or 32 bytes | `hex` | Big-endian | |

#### ConfidentialNonce

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Header | Yes | 1 byte | | | A header byte of `0x00` indicates a “null” value with no subsequent bytes.<br><br>A header byte of `0x01` indicates an “explicit” value with the following 32 bytes denoting a value (big-endian).<br><br>A header byte of `0x02` or `0x03` indicates a compressed elliptic curve point. With the least significant bit of the header byte denoting the least significant bit of the y-coordinate, and the remaining 32 bytes denoting the x-coordinate (big-endian). This point is not required to be on the curve. |
| Value | If header byte is not `0x00` | 32 bytes | `hex` | Big-endian | |

#### Proof

| Field | Required | Size | Data Type | Encoding | Notes |
| ----- | -------- | ---- | --------- | -------- | ----- |
| Length | Yes | Varies | `VarInt` | | `0x00` → null. |
| Value | If header byte is not `0x00` | Varies | `hex` | Big-endian | The proof itself. This should be interpreted based on the context (surjection proof, range proof, etc). |
## Examples

#### Example 1
Signed transaction on liquidtestnet, moving 2 existing tL-BTC outputs into two new outputs with sizes: 0.00055 tL-BTC, 0.01 tL-BTC.

Raw hex:
```
02000000010290683fa6b0393b659df707b65e05cbfdf92cc2688589a0ed4931e8a61dfe64c40000000000ffffffff8d83eb1b0826f46d473003d041116927470e2ce0f7cc0c634a983d438d770ac80000000000ffffffff0201499a818545f6bae39fc03b637f2a4e1e64e590cac1bc3a6f6d71aa4443654c1401000000000000d6d8028272c6d7d23b5d8836daac705b4a312b0ebc03f87290da2ed511a833096f0d8e1600144447cb259b2a9857922c5a19cd6449b227dd6c3501499a818545f6bae39fc03b637f2a4e1e64e590cac1bc3a6f6d71aa4443654c140100000000000f42400372fdd5c6e805a50d73ab15ec41cfaadcbe408ecc7a5867621918f1070f84ec9516001424ae71d4804ca7dd1fa66486a87af9dff1663c8400000000000002463043021f3a851011d5b7b52c9761e8a0bd558f2d43129bd1602ffc30945c0a9eaeeaa4022078763819f41ed3084d88fbd3ccf00f8107db76a431a3c085191e3aceb1cb12b0012103207312a1d3e7c2aa5c5212e18f2fe0095e8d11e9ca78f4acc7f6e40dbd21d2ed0000000247304402203e13aa1c792fc14ff06f2c2269e7fff35dc7710dbd73bca3738d21888f031a72022008f9eeb1ea00a8da358321a23e9cd14f6163f609ba391205d5eadcf47661288f012103daa4c9684c369d4420b9f20e4116362b6a3786e9a12a4e1927d1a25c4ffd931b0000000000
```

Deserialization:
```
02000000 ............................. Version

01 ................................... Flags (0x01 → witness data is present)

02 ................................... Num Inputs
|
|                                      Input #1
| 90683fa6b0393b659df707b65e05cbfd
| f92cc2688589a0ed4931e8a61dfe64c4 ... Outpoint TXID: c464fe1da6e83149eda0898568c22cf9fdcb055eb607f79d653b39b0a63f6890
| 00000000 ........................... Outpoint index
|
| 00 ................................. ScriptSig length
| | .................................. ScriptSig (empty: segwit transaction)
|
| ffffffff ........................... Sequence number: UINT32_MAX
|
|                                      Input #2
| 8d83eb1b0826f46d473003d041116927
| 470e2ce0f7cc0c634a983d438d770ac8 ... Outpoint TXID: c80a778d433d984a630cccf7e02c0e4727691141d00330476df426081beb838d
| 00000000 ........................... Outpoint index
|
| 00 ................................. ScriptSig length
| | .................................. ScriptSig (empty)
|
| ffffffff ........................... Sequence number: UINT32_MAX

02 ................................... Num Outputs
|
|                                      Output #1
| 01 ................................. Asset Header (0x01 → explicit)
| 499a818545f6bae39fc03b637f2a4e1e
| 64e590cac1bc3a6f6d71aa4443654c14 ... Asset ID: 144c654344aa716d6f3abcc1ca90e5641e4e2a7f633bc09fe3baf64585819a49
|
| 01 ................................. Amount header (0x01 → explicit)
| 000000000000d6d8 ................... Amount: 0xd6d8 tL-Satoshis = 0.00055 tL-BTC
|
| 02 ................................. Nonce header (0x02 → compressed point)
| 8272c6d7d23b5d8836daac705b4a312b
| 0ebc03f87290da2ed511a833096f0d8e ... Nonce x-coordinate (big-endian)
|
| 16 ................................. ScriptPubKey length (0x16 = 22 bytes)
| | 00144447cb259b2a9857922c5a19cd
| | 6449b227dd6c35 ................... ScriptPubKey
|
|                                      Output #2
| 01 ................................. Asset header (0x01 → explicit)
| 499a818545f6bae39fc03b637f2a4e1e
| 64e590cac1bc3a6f6d71aa4443654c14 ... Asset ID: 144c654344aa716d6f3abcc1ca90e5641e4e2a7f633bc09fe3baf64585819a49
|
| 01 ................................. Amount header (0x01 → explicit)
| 00000000000f4240 ................... Amount: 0xf4240 tL-Satoshis = 0.01 tL-BTC
|
| 03 ................................. Nonce header (0x03 → compressed point)
| 72fdd5c6e805a50d73ab15ec41cfaadc
| be408ecc7a5867621918f1070f84ec95 ... Nonce x-coordinate (big-endian)
|
| 16 ................................. ScriptPubKey length (0x16 = 22 bytes)
| | 001424ae71d4804ca7dd1fa66486a8
| | 7af9dff1663c84 ................... ScriptPubKey

00000000 ............................. Locktime

...................................... Input witnesses (1 per input)
|
|                                      Input #1 witness
| 00 ................................. Issuance amount range proof (null)
| 00 ................................. Inflation keys range proof (null)
| 02 ................................. Script witness stack length
| | 46 ............................... Stack item #1 length (0x46 = 70 bytes)
| | | 3043021f3a851011d5b7b52c9761
| | | e8a0bd558f2d43129bd1602ffc30
| | | 945c0a9eaeeaa4022078763819f4
| | | 1ed3084d88fbd3ccf00f8107db76
| | | a431a3c085191e3aceb1cb12b001 ... Stack item #1
| | 21 ............................... Stack item #2 length (0x21 = 33 bytes)
| | | 03207312a1d3e7c2aa5c5212e18f
| | | 2fe0095e8d11e9ca78f4acc7f6e4
| | | 0dbd21d2ed ..................... Stack item #2
| 00 ................................. Peg-in witness (0x00 → null)
|
|                                      Input #2 witness
| 00 ................................. Issuance amount range proof (0x00 → null)
| 00 ................................. Inflation keys range proof (0x00 → null)
| 02 ................................. Script witness stack length
| | 47 ............................... Stack item #1 length (0x47 = 71 bytes)
| | | 304402203e13aa1c792fc14ff06f
| | | 2c2269e7fff35dc7710dbd73bca3
| | | 738d21888f031a72022008f9eeb1
| | | ea00a8da358321a23e9cd14f6163
| | | f609ba391205d5eadcf47661288f
| | | 01 ............................. Stack item #1
| | 21 ............................... Stack item #2 length (0x21 = 33 bytes)
| | | 03daa4c9684c369d4420b9f20e41
| | | 16362b6a3786e9a12a4e1927d1a2
| | | 5c4ffd931b ..................... Stack item #2
| 00 ................................. Peg-in witness stack length

...................................... Output witnesses (1 per output)
|
|                                      Output #1 witness
| 00 ................................. Surjection proof length
| 00 ................................. Range proof length
|
|                                      Output #2 witness
| 00 ................................. Surjection proof length
| 00 ................................. Range proof length
```

#### Example 2
Signed transaction issuing 33 units of a new asset on regtest.

Raw hex:
```
020000000101eb87c50cb285fc7262a00ceefda34aaaac951ce5dd3e95c1bc85b7ce6a218ea50000008000fdffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000c4b20100010000000029b92700050b3cefc49d6412e3d5f7e418319b4e7d0b505c32b632fe882ff59c5f54e60d43b50866abe471dfadfb650825abe6f757860b6760d30ff62bc7c9ebd438608f45368b02115750003261bc64bb73d83401a912796d0c0fb9d54c72751a7ca7a5149a9bdf1976a914031d2893a2c3a3bc6a8a04fda5ffb75ffe11a8b788ac0a3b2ca466dbac12b36dff8b0457fdda3a987141042175d4f230a92b15a390441c08f27d5f8d5de47d6d0e1ff49fb2e1fb60548494baed86f9e84b39e1fdce3c8da703b1fe30c45ce67e5f1a1f209ee01251d94cfa29b6f13a500b891c5bb4811873d01976a914b559decb917ff2a5c9d4553ff692889ae7f8577288ac01230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b201000000000000000000036a01000b1df891f7d1a2feffb5ea3ddc9a8083ec7ebd3074f5b6df16da1060eb1b40c06d08c1533ecae1f143762b2a4ebf6db111e801a0884771cdc0fb5ce1faa4aa29f42a0367e4e9d0fc453f01024bdb22c60edac28ca8962c670635514c155245cec1d12816001439b9791c9e35bba2c35a9ae829f3d22889b604ed01230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b20100000000000069dc000000000000000002473044022062d246df3e46f806c78eb39ad2feaaad1a43fa6ecac464e27895de0a38646d6502200334e8de266d42ff440af0e59861d7a11d3529df8f584c558cf4879ef89d51fa012102d8aefaed1152469fa73d5ac7a152a632e70a15a135d9f46c76f01578a3dd9f9100830300077b8d6962c63f392384c853936e6a1883f226f712b50f94afe34a3eda584a13083767a68601bcd503b4ecd3a01db8d24494b8716b729ed3bf9f211e49fcd120c7ff3c96a0e6a316e042ee065c357d239aac8082a9d9a0a28c0c660fe41ddf838ad71f57eea71141d92c466cb25f1e6c17f85ef4f3c13db1ac3bf34fcc92f05435fd4e106033000000000000000173018401ee7e89f24062d2ae20b572e748d61b6703e05c8f00ce5b5f0bdcd906ce6d52ed7043d447bf995806f81b1d1ab576a16837fcb0cc87f35389375ce157989396fa3c741aaddf9f2f51b0d74e58e00a63ae41e0a549151148c98b8b17b8e32fc7ba198e7d70c4b3d6726215a65064442e4942c395a5991beb5fbc8e5c330440bbd518839a9f82b7598254b48cc016f720b201fb763a898f2e6b752f5ceea5b4acf95d26be640ea0d30293fcab9bcbde8a7910aabfec5202e14f9b53d38d2b076ae5e976a67922cb2bf7cad416706a67189d3170996af2be84a0cc00bb0daee179ab8ab84dbbbe91df33e0b4a96c163be02330a3fca52cd22eaf97482bc5bc2731bb647cf98de4220e85f0040fdf6518955516311d31b9efc839cb1bf0567d0259246befcbf453be2fc96d740eedb8c787e0d7f256f4fadabc93b69a6b33ad37ef9d322bc2072d09376ad94d4ccf35298b92411955ecdd10c0f709e679f810120065318f4f61c7a1a1ce2912d69c1a9528ce0dbbf3414c163de2e6728b0533d1fa5294882ae4418839e9387c2edf18837ca5e043f217c46689a0565ddc986d1d67b303ccd20655b8d09716a12229c0aa0e251fe27b64b6fc947d76a79f3783ddf4bc4f3a046ac571ccfc4078b345f8b8c610c3e278707fe95293e6398905cede394ef56e319ce62604ac0b6c06c6b60f9e67d1385f77b4a9c3cf04a5f0badc0ec0a891632baeece44348c0acb7d79aa81dedb19994eb4ec5f980075b26032011413cb23db747eec6566c267f925f085e0619e5f36aca9d729d5a461a5c6feca3a6ae4f1646936b78a09b742268179a5312cb354314af217086148f67453765c128b4e73b6310346ef322067e3459499ba1a5f9835571f58c1e3fef2d38720abcf10abbef8034d2df80bb1976a6ae7181ba79c7770d9d45bf4394afa88c7046d80dbca64497ce4c598767befe25bfed700329f23c5828d25e5143d59e074e1270ab366995e28b7ea38cc49693b4b846e370e00e2ffb514c21bebb4822984d53cefdb5233d1bb3523dd18769ae587df4ae4626bb426a545ffa13db6fc74027407fbb67116935ff3f3ff681fd4becd2c8eb646eeb3e9953f0973c48c966e5bb9f9dcff7917da1c8d35cda5142aadd496b9f1087cc0cf31e49a10186de859eae75086f0feed31fe26fd132a6c1f257bf4a2bab1489b92ef0ce81bcbc2e27f2f375f2cc40e937d9113ef762313561ad4d213d80d50cdcafa5b63331a3d7c9e706e3ffeba1613c44d6e1fa2e2696ace82629e3c73388273de64d27853395a6b39e573673fa67dbb87a5064ddd8cdc64d209473b7c3d7a57b4c860b6dc9c67c52bed10c9c9719fa94e7d54901d2e5a6b2702756035f50fc15f933458148ebf5e39027ef3d8c26e0c08d3a46b7a6db64af1283245c639d77bac0d408e5a1cfff9ad3ba606da3821a7e30fcedca5a26e7725eacb782e2584039222e89008ef8bebb3a1b15756eebe7e9b2f75237ea151240c37de4d8706ec6510039c1a62d191653e1b74d96514062aa7cbc44364859c81ca483b653d3ec4dc419a4de73504e2855b7f4523d2f0fbef3af886051cda5fc126a10e32c29c167134f24f6f69aa706682693c4ea5993f1bba6582901a5f60d89b7a2c33ef2cac071011d8f2259acb6f5703c10a40e85ebfd3f0d2b659aadffec1a4e2e0b3e09926f386b357c548315f4687a04b8eb1346c1ba81d94ae25120f3f8756cd2f52b38e022b99aac08c6614a0138f83100545b1ae976c950ec773ce47bbfe004354b7be0a38fce14e20f87ab9ef0df0a38da0e38c1dfbef7f21f6331f39cd5430bae5cdb5bb6139e45eb96ca61910d749661870965d199e1125e5e605d761b55f855f5aab2b7e861951d21dd985bc781b96a7d0e604a72741260d3cff1e78ebc2c81ee745c198f1c5be512659dd8bb3048c3975369f96a6003e458d411c036a3e19b9afffd83bd37d1783b5eb206d02c142ad0993edc36c297f26fec85a4c2fd62a154548db4ae4e7a9bb71e11e3084a01694c8d62345ce24e285e36020114a541dbe12764a56ae12875428cbe7f5b816717d9297eb4774072848fa1df905c8ab38ccfbac4449a5ca7e832237b823b6f6f190afb6851ecaca29ef9cc1bb1f22e08986f17cc1791cbb238030be1e18dada5cd27ce13aef1807cf4d9dc9dc18c46af06020945f8e3f25270c36a8247002f154d3efb49fe326ce5e84bb0671f75ff565376d5519b583453d2b7eb99c921318fc7a39bc897b192c4369cfa4d1f1681adfaee7915659755d0fd1b5fbab93c6310e60e87f2807f0d1673428be1b20bae9422380fcc5e0bb80d2fbf2b576908b4d9724c286f4677f831276d7f4d581cda6e7fa9554da396e0d9272030448cbca088aaf3f3ddae6135c0307791cb7665fe402254f6a11de9a7caa9b4be9f8672a6b3d5f8ec51f6fd668cc4c8abec0484128d4a22c548203d23bae49242f92c7fe771e15e0f8226f364f18bc31fcc774ef014f81f6bef19c7f8dd38cc833a72acdff0d267e641dc79f7f549e0acc4fbff637ad0e1d1088fb08eb53e5b2b7a9b50b44c43d44d3798651000ae834753882a6067479404bd08cf48e5e04aa8ed3a2a9999a298afca1614de0674f996dbfe26a43366ac324abbcaab0468baf627b465090609ced0e4b81dc3901dbacb078af52d105215e47a3e11f13036b197d78aea2a57a0fc02f4d029fbd73f537325f71332acd690033eda9773d8a4ca02deb43e112a7a662eadbf42f6cb6589044945aff650a06f0035bc2d2db71d7e7b5857987cdb3f0f273d6cb02b7cf3372423b53f94471be02b04cdf5450495397be8d70637a13cacf65c711427b06d758d7bbac4641ffa82b02acdd67baae7789a0ff582d2899ab4cfd78a0429413d3bdc9c59941eddb2863c54fcbe69a44a08c4775fd8387a45442379d3ee933b840790aaa10384a816584066c16c21720ebb2a5ddd1767d4ef096f204779d2389e1d0edbc4a903a591f9d9c9cc28aee4c41dae939d25aee05a06140394a237077bcbe7c6e68ac4e241bed6572266f1a9027a4b704f26517e480a2ad2d23c4233639605757d22723c574f830756365706d9c640ff27483238eb7412ce7bc8c299cc486534d60077cd32bdd62b3d94d82c7a86a2507584a0c8167a3742a469b94591192a4c6f4d33c803e8185810675cb751ec1565f3253da6275f67338bb583bcccfda79a45889d1329d997d3693d77567aa8b4e47addd67a9bf33b9890e9aa4f9bad3f415a93105688947c59009e3877ee3ed5a5f5da8ca2fcca30c506ac6fdc58bb5556709a9d537edda9f037feffc3dab5c7399834a86fd1d6e76fb545d4284c9c2194b7760d0162aa83eab396899e8ec872fc71f0cc5520b1c14a27ff6b299d6086006ff1d5d0b529636a0ee1ebc8b5e5ebf299fd6830019f5af984aa92c0e1cc8dee7707a00e4caa64b4e36b1c82542795e2b6351251965e22043046190812e12c4aecb39d32f10a3c79b6c69685e9a655ba47bfe746ef436d5c5b92178c8a32d92c474ae6790463ad91c49fa6f3a72c12d2519a7f59961ecf852fb8b327ee73d83a3adbe4494355b4ce8b797420f92f7d2bd48fc79f7c51fd6a60b812eb886dd6abee0af227ecfdaf775a02bccdabd91983402289e04d893ae6ec063e783f5636f2e4aca3fe363f6056bcd250034c959dbe9b08b9e42ff0c07bdc939304750e7591a9b2449b22f9be20430bbc970ec466a39ef73877e4465e446135550645b091dd463563808608887a37cd8d01e3b3b7f9c8985a68eaaf5cefdef67ba39874d2240253bf3e6444fbd7bc0895d330dd080a45fab6d939f7064df00805cb70ee0d1fa81c559e7ddd137e343978b7d272899db5f796ae53a08724e2f672ac6be9147246a9fe229e2aec3225c3db0d19c40041010a9469f634373b625d7bdeb24f55c169c92a6079aa64622e6afc0f9972554919dfe07b02dbd3a47473cf2c572724ffce5303aae6362f2f17dff570732a58af763a50b175b68e55c531c3b4eee2b5dfff150c8bb5fd0733892c86257841df69a437621c571e0403fc86c1b491a9fd9d093e4d6d2426db8e025a0d6909d34c19ce64567fa13504188aa511693c3e2ce0560e3e64d817b0b08cd82053b8a90e38f05a7f9c8f761507d24f609f7832c345b033cc791d8e1466a9989205854a00ce44d16b615da5bda6affccd6c8f738dc2a7f39a8620b8096702a77049612fb80d4a68be2fc3adcf26ef62be3f18b1e4187a525b1531e47bf1e12411d0d1dc9db2ed9289757b57e3a9a0f707a19d55e6e2d0af0f37ce887a4e9baef1a0e5520d6dcaf514189f7397b02893cbf2a1ce6c42dda9b480c8b4153021ef988bddd1237ae15aeac3b1ba771bde709316961276a3440d5935d10a286b2ba6f1d4dbe627f5b0b91c1462e3e613ab470525c30b16cbb15469a80a52490b41b8ea9ca7015087b2a9e5033e105ed77292aa3df03e6d953496270e542188e7f2c4efbbd3011a885495f34858591ff50d38800930b4acbf8893cd0a27238df98123e3c367ca089b442e4b1fe0b70e2e10681bbefc0caf5ae1b952a8ce2daca355551c948ff58bb78e0a7fc6467073423468103f43b59cdcfe1f9207e707c671d4b30c1d0d5bda907ad21b1606f47bc9c5ca0f3dadbd1eb3e61febbe7b06652c5f6fc54bff99c037bdfa540617c432bc0db445008e58276ac84b76dd31a5611dab588a2b7060668f46e2e6d37c126e462f2911ecc9d42c398b1d2ac2df6e2873361ec6c0d93192b92e3aeb33209d2839b33835c0d58090376e496e3d59eda0d44f36c4a12265eb7a7ad7e4bb3abea403e8679e9a9d19f6e0ae81dcbcc47ad67760886b4097bdc514d09cdde427af5704ff433c6b92d41d22991e479943def7d0cdfee9454bb33a3f996e1e1e75aa347d31dc27aa1e3c1433f3694bf06c25a78367c3f605f379c8ce5d9210788a84b782fa835fc5a3b48338540347311eea661d4101578824dcecee10931e28b43c4fd56519666a060b6af5721e3a62570153f7fbafb3875fea186ce6cac608cf005a7d4a99853ca5c34975f93776a119ea099607699aa34cdbd803387d46faabe7775e129926727cc25ca94b742065c012b5f827c35689d9c60ecbbc4e8ac5e73dd1a267ee7d4f1b072eac9ff0dab38ea320cdf4c3f5e511c567fc655a542e8e60641b4b281d581e9a3dd7c6b2ff240be1f3b9f39f2bd998472acb9d6c77b10c549e7608a2630ef82d6ea5f6e05519d4c05b7294cf9ef19e1a46276a365ad932de33aeb9daa45021eaaf7c15b2f0606a154196e7da39c0827e927259441e4aa04043c9dd3be5674745aec8dfeaaf2aefd0a973af41a4e253c650bec72932f20bb33505e1874687796d50d25113a5ee995b4ffd7582df9809e4a3793ebbb0e9273ba8968486449d43bb48bb9627cf14c43ca8b2610b208f5332d126a7a421752dd24f7f791c4992d8c201dcf68fb2648c944efdb65432adb6dbfba92bf40b6fc316601a2e2c3f20fdf0665c8f57cc71f849c504ff7f9d8771fd5fcb9f4db51284f4cd34650dd677535acbd7472582b6d025110e4d0252b39b8f68d1142cd135a9a106670b5028f03928d805eef5951530b9646c3087b66e99071686b98af8b0c3391fdc78847e5fb7471276a8697ce8a964dd20ac638cb22a06b61f6e7fab5f84ee8443ddc6f78c206a1890eed282ebd2fe3f44bb6d9de87e185475c3912842f065909b6acf6a44f935d830327aef47a5f00218adf3c4f1a82b7b01e30efc84ff0d83c188dc4bf2be4db8b6ddab0b40af4e17bcad98bd931723fcd4fece0d2be77eb94600de204fa289bb5ffbf28ba81e2a2002bb8d21fc8da5f18c4050b43383030007b5838d73f86ee7e4773a383f2aca5407b3d1a33951a1de1eb6f9153607c6e43fd230512e32f97fa1e352a6f4b3ea37f41f48dec18babb4a97b6e8a2446184234bf02606ce6335cfcc3fe067b8bfd599260477ad6026538b2f7e023bf3093efd0132bab96492fd93a477432fde7b6e926a41017573ee62efe39433759808c1595fd4e10603300000000000000017ac624014bb2b3e59dead05ebe5c0e2e043acd3c4144b84b00ea4184e81a7106296627f3252c3e91a91f0ae78851858815f4db4353223ce9a4046db13a7e2e28488cfa2282f67167995a10b8a1e18f0322e2d2240437713cda84e0036431a644bbf85804b4d9ef680dc883b580a31f9b29a715858c47301b16a82542e84d5c2107ec964880045d4f17c9699a0f17d43ad8eab1a7a98dfa0cb87db58622c214022ac9f64ebe9abac08a640a38435a820364acb645fe1a26d8fa80dc3e352523aa8ff0f41bfc8c0a4a3a2d9a06ce31da68ab6fec1c00706ffc89a7156de77b3ad9c8f339b9a70837818fdfdce7d403c7011b5a8760bce70d6a2762b0cff05b611ed63d3f55016077267058725873de4cacb2bba3509748568d1989319d93b161d90aa73ac8b8f131cba3797b68f6aece34d60512942b322bebb1773124ac36af18302c12778df3c9a00d7eaedbab56b6c1ec55e03a73196e08155abb8bd6cffa472846e23809eaddf566f4bc71757390e4627b02ade91c0d2805c8c03a27af16b125bf7749a461f00ad106d119d20289ae342aea0818e407d149db20340a790dbfba8385159a3d2a54fa5e453fc427d5c7e2c2e0ae61d6b895813ec29e4a63c200c49f2cb1cd33fcb5a2bf320c5b3c5e4a64298588b3aa2325c3aaeafcc0b6b36b77f35ae148fd42b7099a30f22f40cbea3343059bacc969b91821ecc6ce58a11e76cb8e31ff80dfe4ee6bc1da5dcfff05c2594bed8c28b3e6942a7677aafca100e1e4fe67e34d211a27b3cdb148b9038494b8344ed29ec7f6ca5ba720e24189023f375d93412d926c78920384ff91207cc65766906a0c00d9545a91c4f7905b35581641a27521bd688107ad14f7237e98b3e317bfbd1e457b34d278add9a49d49aa6605297c0afc0c57bd307450037abdc7cbdc0b60ae2c98ec917b7abc234406cd917bda641976b2fda227b69f25a6cd96a11151e512b04a5d4d03f12b9371df1c26bcf475e11573320628b5ef1f75903852a7c329f97175309cddd2f1cef67abf6b16ea2d0dbd19234cbc892b74d8d203c25bced1de40dacd1b11112ec7991663d8ab050e76b4804b022a696ea71177562d0517be4ba78d9c9e4f25b9e9a14867d382be74cb0367febf32733ff3be09a8ee9a319e5aa4e158ff9d0270e3d4e5d8165e570f3ba8c1b00780003c7da3274a024eca45627661b2dd26925a5f17e701ba89dce2cf66d934f17ab3242ca8343dafd83f689d6ff992094db8ca3bac2c6b51b6a9fe0a10121e7bd786950079ccfd2cffd0e62b96d792e969e2f08a76503510e40f5f9adadc005f1f7f0fdfca04e47803f6017a0611b81db7bf8d190b9bee5b60f05935d65517c0385b8672bdb7635eaf895aae94fdefdfd5f89aa573546011baf511b30f0afaf632ad30c005b00d8cfe1ad70228ff1f510eb611126d5032b7f5e0c701f32a453cf119963a255f2946d1b8d10a550522ee651b9ac72dcbea91ec9510ac4477e712746a71255776c083e9ae1212d0e0490b9444673de82b5e7f3fd41e40d380d9b71914700fbc44ef471c0d6875ba6bafeb366aacac2279c3316fbe832df965ac6e0446cd40e2826cf66c775adf1cfdf0fcfe2dbdd09afa760aa02490f9f8f8e4dfa22598f892e8b54ced951be227ffc66071b2051a595b9d29654ae494e50359c245a412a935cf5838ee1383747213ce2f6c724a53bda8a21d8c22a3a1ed1e9193d91235fa0f038b715e2605ce955de05392f2884f9cad3d4bf927c71fd6fc92897e6db08793736f6347b8a5f7a0601e020d2b30956fc4bc219f52f7f908dda49059619475c043a5520df99e300426325bd09284f956f141a16d4c3a7db5d1a7f5f6cb77a5579e59ef23ff00870503ae64261efb5060420095510493ec7448a50df0f70d610607132107639578a38823c88b4780e9c9c7d2b6a97338cdbe0526a7bccc9101b71684d66526bd844fe1f31d2477aa2c497190ef95a2adf1d956cdd8feabe01ca2c910fb467e0fbdf60dcad8902d76078355069a0d9f7bb8ea39b9071ffba938fa7750e153c2e2a1d885c970f216b13f21a61fbd251b7d54a0976b685cd871145bb077ab280965861e7eed3475c470a0ad33f649eb34a516dc0f8e30b62e5978196097036046a90a8e4b30a7054eb366925b500d66459f90f9f78ba45b874755a7fcb84a23ca727a013c1b2a3a3aae1e82c42598dc25cd6e0a908c885754c862a78ee152585b809948b7faef8ebf66d270b924ef2e040c5518e766930e14f69499a93ecf7d2066e875d9d2aa13bd477c30eb44ad6d1f6206489b52288e8ea09987fd1b082017fcefb2518032e32b8028b280f0d6c0efd57d3e1ca5a3b133b2cd69bdff1fd300b8dee2a22afad898d7fb5d9e71f683f6fcbf1733862358d6a6450a52b46ba0b036f2a788d9ef04d2063821fa6abbf0ce2b520febddb39f4b2ef320bdd03d0508fea9ea9f575e6710d0ec26d12b3d19cfd97b89298f91bd7ae128ede0979a2f163fcdc233295f43f39261c7c289edee0297c6e9028a56eb355f5f3bf5bf7adb28254d0f5f96aa050f57df31dd0d4ab35081dae1ee2346852b10c52a73fe9507ad3ea7b447055a09bafa445bb4d2d53b7bee69c6bbefc7e591f1d47195a09dfd10f86ef2b395decbf145867561d7172e0f8db65b8bcc92271718f3102ebd6e25e6d8080380ef4bfad49537eff4a8e4064e2d5f416fc89f68d16346f12466d494ab46b16d2d34db0f2584bbf7d857a3c9c907f24a201c7161cf1a5c61b5c701eeb4da950fe723cb5202c43cfcf8a3a7cbd660c522f5808f1edfb6fecf4c0427924000233c8c59b219eb8200cc7665af5564f4f66cdc90dac4743a4dd4ef4953babc537cc7d3a72ffef5f0e90508c66244d6134f1f983105ea3d7dc347b7f4cf1f9fa45f2eb5778288d3f6fffd1854c92d79e474e1a6b162106260beb53625bd227bb063a2cdcde8b87898fa2a7ddec3c1c17cf48a169ed660c9d18784d36ae245a0a42fc3db6c30cef1b2f0455b4468998b877c0185f9617af48c04154dd8436d199fdc24a4681c5e6a57163ef2e7fb245fb7d32c800a26453ded5357268813ff2876b13bf215110e97385d47bc74e86821fddcd2b27eea2f3ae14d779290e6b8c9c094f046eff92baf693d0dac4153c68db30ce42e9a3b9f1aca84a4c4cb9d88d06d67e6dd1eec12daadabc3067cf056f9b78fca64b5de3c5e8d67a577f65d362f62fee93d28cdad20a4096e3862bbfeea699cf924fb3442a45acf50afd95072d82fc190b042f6b46bb7f2ecaf436aaebb626cb29beb0f0f53b42ff8b0269b3d042bcd2af36a68e96aa3f589b23d56d32ad424dd54f9cca635247b96b4ec6b5753724ec3e46d6e72df6f75217cc8d0685ad244dbab2b8f999ed45f3bf2dbe24e474323b442e2972fb000b7cb7d7718e580264d70c474fc3d5751d0dc57e4150057cdde5cfa928ec7a9023d6d8b99d178396460ea232271c6a4b6476e30e70318ba5ce90af3929e83f2b52465341e3614ea9886174bfe5be852f7baee22a2a2382c8414582b983feda8e41ae561fa6046f90fd5172de2e48395bf69a69d61f50547858f897cdc1ae3461ee2108f5f9fa342b3e2acae5b9e91498f86a9a2140a5d1c368b796ecd3cd4f58d3f415a6d7ae6f1c87039d5194611b7ecfc27579c197f7d5b97c3ddc64a36d98549e202dad22cef97b938a1a26e01d70e1c6b7ef571cbc36b8e4a6faef49c3a728b943a7ac19e42921a4b26e705f772c6be11bc14dcc861531d6f94f8c06c518db02333cdbee18f1fcc36fa1fe43b7e432f8223fcd15afd58279bc4d2893eadad4df64857a78c13cf534770386631dc2903306acc227bbf64f522f57fa804d89aab9f2d58b9f55f0065af975b01493d25f42352a09f5e1ce9253f9450dca111bddf1a14e6cf657cf35d955a031e8c340025c9e1243d91499b1452e7cf969e0c668db7af9b786207c4b63161574e932a10d0c09b99b13a2fca842f8edab4e0d4cc6ff1a1c83ef33a5cbcb61440d36d90e5c6f39dcc93d5279cdd1da40cf83c950f5eb312bb7549040504096f40d2f178c7762ae375fd2303ed0b0def24a51248e7ee38f81921e4bd7dc2f75fb34ae5ce40375ad74cf8ba962e95ab1fef880045e7dae964d24d7e0bf0a688ca400b695d50095d8933447fb87259b90d11b1e79e61852748200508f9aea66746cc56a11e9f528039710b7736028eaead6e2469a013c5b0ddaf4c3fdf919b1c2e8d0f2fb43d5c7deefe59860a871590a0888aaed31b612f3c2daa4a8ab8272dd2d7d332c53eaa06ea39b1511075d7ad59c479b97f8b5c119f8d6860676267235d5e86b58faed3b63574828bfb81c891c1c52d6543a0c02f974a38a9c08005240bba60f8ba792df9c8cf1cbab7d6825fd9d9726ae3d69f6333c47d476413022128e059b59befba4718cfb15cecbc4f12fce564d257968c9c76616659cefc5235e1c5f3ce23a547f7743984e0075392eb98d2dace6f5c32243c75f39bc3b64e53a5bb579586f0b8d02e4d95822834d79a8812381bbb34fd33f82757cf3f021d73ddd671c7a622c695f170144457d8cac8e4116bb236205504697b7daca842dcecfcc93b9fda4c7796ac01791b48e23f555d70807d4d91ae0a250badc108e53dd6f0c589a2af4f9b312d63843ed5b5eddb4618051fe860dd2e767f9567bd88c708682d27ba00f45d2fd734dbb261e5a8e72e144ce463f86e5265e2727fbc4d986d6b78ea5754038d4dac3f9cc0bf7d8de35485e0aaa95b366394b9d62e03d6726d968faed71214b41d25f943d3675cd9507e268a39810fa0329c14b3e253f3a4b04b820fec8688e992fae04f284bfeeec337798ae635e11b0a3028e52d12e98af6613e741eb7549d17043b3e85772f7feaf3ad59c339cb2dd6493ae589a9a2a5f6ceeb26d9bd69e7552326a7cbe66c6b72e5d6867a48e880adf13820c307b07789436f8e3e48ac1397ddb287063f0a4e93637c74e5d3adb690d280d70c92b72c35796292f8cdf9e010829b2c05fd70beccadaac6aa1fac37b21ffe588e9a7916557d81c68c5ea4aad5b9fc84bb34a012d3dbf34f7549c149b65cf7f3bdb2bae90ce7442e4eb5f999357eab3efa6023b2d724de9ff37405754f30c604c98ec6a4029d9f10673ccc250638fc0e9f7ac845d5a8c054cc7cd12fdb33ed99b9dbbab76bfc31e1fb374a8925696e462fee5eba65734a7a45e9f36c94f72bf5e604013c050cf11722b3445f60663087fc7cdcd0473548886cbe9f7fb1b20e8dac09a06f721baa52f451658d2e9d2987625373c7eedfc2b2d9069ea7deb9b73c687bfbd3848c0a0493056f4dab79628f980f6b15743113abcda09bd3c064195711cd407f25c55b30d93aecc1e74fca79393d3b2ce975a4c68dd7c73d9693f03b7a54dce0abdcf056c69ebb4bf3c12b37ef4592c8ca6529968656b5e9c5a783b9250321f625b80f8be23aac67a9aecff0630033446d6e9242deda32e69706553e8a883bbdc7bb0f3ce9dc9f209f70bc1acbdf55e963808e09e1aa844c55073a40cde54d51df8da937f6af0bc41443f4f0670f62fde0a9acb065d635c391b85f51a09573ac0fd2e2c4329f019fa80d3f953aa0e2ea4ca634d450c172add5798aeb1d9f4747430e2599b15e91f7554bc3249d61611b240b9b4bd23f054e5a092db733f6dfde58d14732702f72035482f028bec5e498e7615b636fa88bd33713eae711c470068df6fa0bca8cdd4b837a58c4f071e0f9c149ad081d746ed91d1892b795ea91dd7c35d61d3822d9c532cd92ef032fe3a2334ebd3d11efabea68e5c4549493ea730d193c37a99d784fae178b0b97d71f1e6b454080a9f9d0cb6d7c5abe9044000083030007e2d81658dcbb09fe2bcc6039aa5979dcb52f20bfc1f38ca06b907f1b50bf8d6ad9a584e1c56387643830db7936d40fe224efe60fb930cb04f9440472e54aca84378f419e46c71c589e9375489f63007d94f6273bb71b8b979e8c29b110774f4a134192b6e97973a7b59856c16f31b7da29b62146993018bc11ed5fd3b101a3fafd4e10603300000000000000011f237d01dee9accf2b04b3d556546ee762947f9dfa883b33e14e6836ea22eb1cb870bfabd11b70e7698339d143cf5fdefa4d0c70ad353d64c70a306b5bb430b9db3e6ea2ba67d1e23086301e9460b0e37a21a4af7a88d638fa2801c545c3e2269edfe060b701bdfc360c4bcb8b2a85bfd5f32e7150afed4e143b9d49ee4723ad4a91aaccdbbf02f102b5c50b86563bf6f7be984c3feb0c09082ba0ffffc4f0ffacc268cd16f4a4fafd123dd56a0b799ec8c983de4e61c1a9a31a12b62df42a5ecb5cf1557a8e696bb75ca0011a93afce62d6e1d2051312dbcf3cba126e40bea6f1bb484f6e9685972196a34b8fa21f15a114aa5e587a1aa096df1849d759d1f3805370958130bc84ee698e9d8d4f6165927afd97f385a9e00692612b42ada360f54850f7a4211cbc75ba092f8b9048fe986bf3d0fdfaad7365a9d27b159eab72daa0f27650d11ecc5dc2dba72715e2ab64d0d69813926433dd4d898196f5f3d3ecdf91e1fc5da7ba84796f7a7fdb2faa5e522ca69f3cdd5d79e2e789eb5f4e37e84c472d40fcde5a2f92c337f71ba7817fc6f8e2f6fd40e78219e6cbbd5235ce87546b25f28da5e7981ad41ec31c1068564e4e7ccb0086c6de5cd3e9a0a35401dade57bab5d1e29b271442e74043335586dae671c6a1f0d39d33ac625a3fd91dcd39bc7762dc9cb142ae1cbe98247274cf32b8e098a4b261e803b3b565dad624a0c7658d7915fd9cf85dcf680e0804b6d5c45b7c471b28ca977f74c2e3e8a19085e738da7343d6da6055c9db7a55f4e83216e3f4b53747c24155593ce7799a4badffb042792050b8750a2e1c5a0b523563b7a4a722221b9db48e4f7bc1592e8434d9714103fe656f5a1e633e9bb391a6a6bbf140abed684bdccacd7f936f44a355462f5444b5b46953fd717cbe1962d10eff2e830d31d26926b4fe6eef3caa3494728a7b60827847c0c791f4e988bda8608ac111ed157ea70a644ba4ca2080014e78898c0e734474759d1bb2b72a32323a066118ad6e257eff2f70a72c4d91dcc1d7a63f2caf70e335051f96a60e53935061e970e925c09e8a1705d436b8a621749f2c91000c3eb8bcfe1f28e1f8d48fd7430ceff117cab4088d8f97eead05a03937cb3c1eea73cea61c5cd70a45e55c3b0e01b26bdd66de6c5d3736452bf288dd7971a6fbb049bd69c6b64466dca73a499377eb4c1d2fb50c9c7e318e9db244cbd62849ea2a93354d673ed4962cf284e03ecf9572e4c5ce189a5b3804cca03acd987860f2fbf6d7d120f9f1f7e7302b2263c74f826519c3bf9d659d5b82c66ba1d82ccff68c485a7c05d0d54d7cf9bab4b6e6e3e096cf553089466ff9136758e5a24cbb821ae3788af85c8c1d4ee0967c83bdc4c60931da80b2294d4cabeece14e815ed77d9d7dc5ec08894ff14e3dc4018d280541f95fda96245107b4e939f926955da2d6ad914c2bbf7256f3f0133ecd5ffa900f28ee37940cf14389358cfd2bd4113ad6b5f86d9a5fe512194db90f71bd0104ecf09026be281a873ed6fbafeda6a5e3cf6708b59d099027baa1bc38fd219e0cc5a51ba566ccaa7532f97b93f0c3e1c58f9b6a61104dff30188bfd6751e0c3a776e7f1103a7746812888c419c7e22ec39255fcda90e9d91702daf57a8e0acf3ce2936b912a143e60ae8e684528305d900b645236b3208f50071ee0ecc4cee96e987158c9a2b3bd4d02e26a6f58ff6eba14677fe9a6c2150ca36e9e624ed3cac31f84c37f902dc1977c45b3f0f7bfb759f4cee3b50e39afb6f890758696373177ea83fe9f83b8c258a3b848e8eb51678190957760981aa6b1b6c7be83bcd915f26430acbbc11850517a64eb3a76613c18cec4a613212599d89b78eb360084dc3cbca6bf41620b8fc240fe05a97eac84a9c9423779868e64d0e30367342e53ddd25ef3e6320b32d610c1cf36064b98fc1840c09b270ec19028824c77f32c53058205b13bd7b535dae930782ac50992655ba5cb1754d7a5d2675bec2f2df360f37a55abbc79bf3640232898ce2ef65d56c51cc113c8374e29bbdf08531ec905f9304b65783138e85279b0889cbfbc4e37bb057f1c52646197eb878443fd4b8a4339fd881431dc56a2aaade1f35af446d14607130b5f34e8e94fe99a087c21cfc19b9cf933a6752fcb85bde504cd39a1f5206559b6b2b811d0f729331f2874be5289bae9abe1b13929f7c2fc21911f57f680ed93e59404a90d42b506e86c294023a64a68310647cf12a7d357c6fc489a9f5adb150700197c1fcce0081582096f51882eb24aa16ad3a4abfb7bb9f42259329aeacd7de66a7c26f99effcff4c2ada7c43eb3f4d7feea046c20d24b5de325b8ba88a94ca51bb0503baac90b8bc279f3208307bd5dc02580a58d879dce26b8e895b7620c868bdae0653fb2a65e6341ec229cde0ce6e22827c1db8c1f8399e7ed1f27b37c702ad18c1860f4a39a2f155403b73bad9e4c939241d4c9fd24d19c2e27e86a718710b359c8ec64ab23767c7cce01051f6ebb54ad979357062f36744e0b38d9f8b764206f3ba105a29f9f51c4537a55981e92c9b1d2befac7786c6e9835183221d7ad74876a53b7cde1b6addab4962bb78b5ba078d895bd24437f0aaaee1a0ab668c3e051dc127f8567e8382ed8fcb4c44c41f89dee8d01767bf6f308bdfd8c5bb2ebc13520634e1f1c0fe6fa018f41cb82ab7a38878cb34cb5cde341f7f07241da5f451ad812d6864a12a55f96d787946db0b7c3f8edcd72a6c94020c49c847023c32aed17da2cfa362709e8e48ace25cc200e55f34383e7135c581bb676444feba1842571736a3de27b4a1c85edfc3e4c519c95eb95b61d1b59b41278385d1a1ff3f6643228aa1dcc24a0f2e18967e18a02d81ac352db95901c3be77c18e0ebb421e67ed3d18193223327aa5ea0eafe15a9cad5a6bc7243bdeea019477a5ae0b4983732e4180c05dd487058eefe106a1f947a03e39247d73c39a1695c865d88a196f58ce627f94a2c37438733e1074d09abc8291093d256b742a2f4143799316f5e27f95a2a9a2ebb6348bd89d281389c14e5c49d109b4f3639668787db5b44509fa457968d67eecaae9222b4d77d27626233f050b114b17d5eca37778d33f40b6004ef2daea2dfaa5af6e4eb2d9beb4faf0b4b69eda1930eb30288b429f9a2398fa304e12344d5300a04db40b7810ff9ff12be30152986e67a24e991666114585ea43126721375dafbe15bfc3a7753439d96b164aef2e7a94a68e2d62c6c041ae39bb88788b513bb8db4916760f5eebc01e0dd471af4808ab52f1f52027276a2a01e80ca32f2e434f05a3d682e0f0ef7af641eedbf463f5b47c55e207f6de63b288400e749647fd59b0f34abe3a0da78210435c961e9ebe1cd0d67443bdc51c9c904853967425c33a0c6384334de11ee4b8d4c28e5eccc82e9847c4c9f30911d1662b492bead1ded616e07a892908d36202ae2fb8f02cc144b46bb47a1f8d5c4f9433fa5648818949a268d84434fd091d4cd8409436e939b5d94a4494da2bc74a200c5f4a6d2a35208dc6e397ed28a99b140abfbc093d4c2602bb563daf9419d181d7ccdcb51cf7b0c6d08f8c5788cae6d29d81e97383084067e243aa44d331eb4db05cec1d216eff9c156d44d079e1e11d63139874e283083584a41cc08fb89929b6d791941dfc8638d1ca60a30b8e90b80e2a1e0e0bc4083724659bac3e37a45db1d08746b573349fde4b1006fe5d70bc936af204e79e9d5661066dd89c74892938052d08683e8ff77faee4c7bd84d639ac55b4e4a1b94f4805e51e107e79c8fbe3d3715ce7fb83f5bb833af2772944fffe1255db50bf5e143510aacea6623e7a5e792e952a6d9ada9dd19f1fb9989da3e537fac693cedd5aaaea52eebb4fe57444251f676baeb0e4af5a7771d43d30724f1dbfc4dd8a9b714b7285dda451bbd2362f8de9f334273d8da8b6e7ebade130f4c4de5c260d583917bfcf23d7468341deae11f035bd8ad90a5a33d8aa978afd584bb94fb841177ba544e84d51c8cd78db0f421ce2b212f562ba330869c27bb43937c323b9d0b52dfcc518062f997c4134cc7b822f6e6c34021d591521206977ca56200016e6a92fceeddf87dee6c2c636d59765433c197c7017ae9d6d8096b60997d45041b31ebc67762b6ed6f4a7e392befb9c5302a82e4229d2a04aca5800a0711c2b87138120ab23865e6ef8de0c57569fc794b96df35eabec453dc08479ae28d635490bb5a090b8c14dfc4fcca63b3c09ef20039557c318f4fd1173548c6166cb213c90e90fa9dbc6f3156d94d02ca04eee5b6170c631ce80d3c8e254c458604e7b97226098257a81155b4c8ce67ddfdb63bb61befcfa4107456c446da18f633aa358e527bd45c38f884cb5f2742f99537f2acf8430b5dcef4e781e9db9207349e9f70b56566fbd059a7f510dd797d291a28281a1db21788f5b9747f8c6c2b0c9687de964d9c3977416e3523d30241c71f4f7e9465ed19f3622ce61c855de8d1de85b539560954e5070343a960c9a5073e8a7d8d7b334a83fbc3f7cfd0848b70d8d9b51b3c73de14bc4889c4765a931df1f459d082c99a15b929e32647374becd9fa4d44c4d49696a9d223c5d09569e15991a56cbc525b90fe10c4ca89c37a9bc1d7bd82f076dfdabefc05a61e5bcd855e2ce4445753f99accaa8a9bd4617126fdee2ce2f7773f6c11151ace46c0e5a2e0d09e60110975566d2eb66c71e2026d898fb46a05213b586f51802b58d40f0c8918ae6a872472f993d066e7564ece033575e54282d6c1ec0a3c28bf802f5bf1411eb640ae59f87bd483eb945758fc0ff41a24197f45fc74c0dd1b44505733ef003367c11061a517396abd797836811840be07cd82eca10361cef7062a64adff8a2824df963e50e33c425664b448b9a9090dceda7def721bdc79d77ec55f33cda11cd01304ff7d5b7ed9bdff0eef35b73cb9297980b099befe3301cd929ad26f2343172e7a4bc9a0a4a3b8ea6b9c5c890bfed367092b568f071bd45ce86b4d358400ada8586ac55ed79fb6d418b1e4af866506f0fdf4b34b85ea0622a56ef594fe13b6681c5cbefcc419faa61bdedab42795a9228b4d8e81fa6cb6b2ee28f5572bea938233613870e9dcabc3ad85e5d82a7b4cea2df421cb632206693924156a8bf994a5e35a5452770e1fd5e2223dd9fdc71ca520d63cddb75fcba780cc3ada6dfc9b600be971e0c0fbf80d787b0797593f929b4233caea8c10a7e40f688c6e08787dd3c8f70e37a466691e15c6b2135ea98d84d76faa2d0f8b0497f5de99bbd761390c5c71338503f127d6d693e8315ee47580d015069cc55c3981061891aa344cf149af0794da62dd9155fde7d0e6f770371185ff0470ecc7723e34e7975034eab05d49e2b14de91cd435178f94ca7b5a516a63b069ddbdf0cae6f36ff90e680f52d9a542b9bc0473ea22e996f03494e7fc8399f46fbc13a3c61fe7b1c6270403b1d6a904b1971aad75d5433b9a9ff79969db6788b31c2262cc29e635562e43399f18f226029ef17eadf3f34815abda0c86f10098344652cc5e0b26ccf98d1c9483aef00144a32f82b7381b8e785a8a1dae6f8f0f2ab5064a7d10ee9a0a752fccdaf83aae448cd54cf4008e24f494f86fe78c24411d5ac2496ffb5b7b736dad9065a01e878e1e8fd32988ea46d310de32d4f5e6aed603dbcd513dbda5ce62aee5ccd737ffc89b16098fe24e9fe9166204b61eeac9625359887a91a1bda1f67bbbc325321d36c6f41b1a6bda0fc5d3686c0c73c26fdbcee6cfff3fba124b39a78d4585230e4d55fbc92acb3797808c06f4c0997b62529ba0c5b5b11ec314211323eed3afdbc907282c5a802a0d9a5b45fa4490c8f986a0000
```

Deserialization:
```
02000000 ............................. Version

01 ................................... Flags (0x01 → witness data is present)

01 ................................... Num inputs
|
|                                      Input #1
| eb87c50cb285fc7262a00ceefda34aaa
| ac951ce5dd3e95c1bc85b7ce6a218ea5 ... Outpoint TXID: a58e216aceb785bcc1953edde51c95acaa4aa3fdee0ca06272fc85b20cc587eb
| 00000080 ........................... Output Index (little-endian → 0x80000000 → most significant bit is 1 → asset issuance)
|
| 00 ................................. ScriptSig length
| | .................................. ScriptSig (empty: segwit transaction)
|
| fdffffff ........................... Sequence number
|
| .................................... Asset issuance
| | 000000000000000000000000000000
| | 000000000000000000000000000000
| | 0000 ............................. Asset blinding nonce (0 for new asset issuance)
| |
| | 000000000000000000000000000000
| | 000000000000000000000000000000
| | 0000 ............................. Asset entropy
| |
| | 01 ............................... Amount header (0x01 → explicit, unblinded value)
| | 00000000c4b20100 ................. Amount: 0xc4b20100 = 3,300,000,000 → 33 units (each divisible by 100,000,000)
| |
| | 01 ............................... Num inflation keys header (0x01 → explicit, unblinded value)
| | 0000000029b92700 ................. Value. 0x29b92700 = 700,000,000 inflation keys

05 ................................... Num outputs
|
|                                      Output #1
| 0b ................................. Asset header (0x0b → blinded value)
| 3cefc49d6412e3d5f7e418319b4e7d0b
| 505c32b632fe882ff59c5f54e60d43b5 ... Asset x-coordinate (big-endian)
|
| 08 ................................. Amount header (0x08 → blinded value)
| 66abe471dfadfb650825abe6f757860b
| 6760d30ff62bc7c9ebd438608f45368b ... Amount x-coordinate (big-endian)
|
| 02 ................................. Nonce header (0x02 → blinded value)
| 115750003261bc64bb73d83401a91279
| 6d0c0fb9d54c72751a7ca7a5149a9bdf ... Nonce x-coordinate (big-endian)
|
| 19 ................................. ScriptPubKey length (0x19 = 25)
| | 76a914031d2893a2c3a3bc6a8a
| | 04fda5ffb75ffe11a8b788ac ......... ScriptPubKey
|
|                                      Output #2
| 0a ................................. Asset header (0x0a → blinded value)
| 3b2ca466dbac12b36dff8b0457fdda3a
| 987141042175d4f230a92b15a390441c ... Asset x-coordinate (big-endian)
|
| 08 ................................. Amount header (0x08 → blinded value)
| f27d5f8d5de47d6d0e1ff49fb2e1fb60
| 548494baed86f9e84b39e1fdce3c8da7 ... Amount x-coordinate (big-endian)
|
| 03 ................................. Nonce header (0x03 → blinded value)
| b1fe30c45ce67e5f1a1f209ee01251d9
| 4cfa29b6f13a500b891c5bb4811873d0 ... Nonce x-coordinate (big-endian)
|
| 19 ................................. ScriptPubKey length (0x19 = 25)
| | 76a914b559decb917ff2a5c9d4553f
| | f692889ae7f8577288ac ............. ScriptPubKey
|
|                                      Output #3
| 01 ................................. Asset header (0x01 → explicit, unblinded value)
| 230f4f5d4b7c6fa845806ee4f6771345
| 9e1b69e8e60fcee2e4940c7a0d5de1b2 ... Asset value
|
| 01 ................................. Amount header (0x01 → explicit, unblinded value)
| 0000000000000000 ................... Amount
|
| 00 ................................. Nonce header (0x00 → null)
|
| 03 ................................. ScriptPubKey length
| | 6a0100 ........................... ScriptPubKey
|
|                                      Output #4
| 0b ................................. Asset header (0x0b → blinded value)
| 1df891f7d1a2feffb5ea3ddc9a8083ec
| 7ebd3074f5b6df16da1060eb1b40c06d ... Asset x-coordinate (big-endian)
|
| 08 ................................. Amount header (0x08 → blinded value)
| c1533ecae1f143762b2a4ebf6db111e8
| 01a0884771cdc0fb5ce1faa4aa29f42a ... Amount x-coordinate (big-endian)
|
|                                      Nonce
| 03 ................................. Nonce header (0x03 → blinded value)
| 67e4e9d0fc453f01024bdb22c60edac2
| 8ca8962c670635514c155245cec1d128 ... Nonce x-coordinate (big-endian)
|
| 16 ................................. ScriptPubKey length (0x16 = 22)
| | 001439b9791c9e35bba2c35a9ae82
| | 9f3d22889b604ed .................. ScriptPubKey
|
|                                      Output #5
| 01 ................................. Asset header (0x01 → explicit, unblinded value)
| 230f4f5d4b7c6fa845806ee4f6771345
| 9e1b69e8e60fcee2e4940c7a0d5de1b2 ... Asset ID: b2e15d0d7a0c94e4e2ce0fe6e8691b9e451377f6e46e8045a86f7c4b5d4f0f23
|
| 01 ................................. Amount header (0x01 → explicit, unblinded value)
| 00000000000069dc ................... Amount: 0x00000000000069dc = 0.00027100. Recall: values are divisible by 100,000,000.
|
| 00 ................................. Nonce header (0x00 → null)
|
| 00 ................................. ScriptPubKey length

00000000 ............................. Locktime

...................................... Input witnesses (1 per input)
|
|                                      Input witness #1
| 00 ................................. Issuance amount range proof (0x00  → null)
| 00 ................................. Inflation keys range proof (0x00 → null)
| 02 ................................. Script witness stack
| | 47 ............................... Stack item #1 length (0x47 = 71 bytes)
| | | 3044022062d246df3e46f806c78e
| | | b39ad2feaaad1a43fa6ecac464e2
| | | 7895de0a38646d6502200334e8de
| | | 266d42ff440af0e59861d7a11d35
| | | 29df8f584c558cf4879ef89d51fa
| | | 01 ............................. Stack item #1
| | 21 ............................... Stack item #2 length (0x21 = 33 bytes)
| | | 02d8aefaed1152469fa73d5ac7a1
| | | 52a632e70a15a135d9f46c76f015
| | | 78a3dd9f91 ..................... Stack item #2
| 00 ................................. Peg-in witness length

...................................... Output witnesses (1 per output)
|
|                                      Output witness #1
| 83 ................................. Surjection proof length (0x83 = 131 bytes)
| | 0300077b8d6962c63f392384c85393
| | 6e6a1883f226f712b50f94afe34a3e
| | da584a13083767a68601bcd503b4ec
| | d3a01db8d24494b8716b729ed3bf9f
| | 211e49fcd120c7ff3c96a0e6a316e0
| | 42ee065c357d239aac8082a9d9a0a2
| | 8c0c660fe4ddf838ad71f57eea7114
| | 1d92c466cb25f1e6c17f85ef4f3c13
| | db1ac3bf34fcc92f05435 ............ Surjection proof
| fd4e10 ............................. Range proof length (0xfd4e10 = 4174, refer to VarInt docs for deserialization info)
| | 60330000000000000001730184(..) ... Range proof (shortened for brevity)

|                                      Output witness #2
| 83 ................................. Surjection proof length (0x83 = 131 bytes)
| | 030007b5838d73f86ee7e4773a383f
| | 2aca5407b3d1a33951a1de1eb6f915
| | 3607c6e43fd230512e32f97fa1e352
| | a6f4b3ea37f41f48dec18babb4a97b
| | 6e8a2446184234bf02606ce6335cfc
| | c3fe067b8bfd599260477ad6026538
| | b2f7e023bf3093efd0132bab96492f
| | d93a477432fde7b6e926a41017573e
| | e62efe39433759808c1595 ........... Surjection proof
| fd4e10 ............................. Range proof length (0xfd4e10 = 4174, refer to VarInt docs for deserialization info)
| | 603300000000000000017ac624(..) ... Range proof (shortened for brevity)
|
|                                      Output witness #3
| 00 ................................. Surjection proof length
| 00 ................................. Range proof length
|
|                                      Output witness #4
| 83 ................................. Surjection proof length (0x83 = 131 bytes)
| | 030007e2d81658dcbb09fe2bcc6039
| | aa5979dcb52f20bfc1f38ca06b907f
| | 1b50bf8d6ad9a584e1c56387643830
| | db7936d40fe224efe60fb930cb04f9
| | 440472e54aca84378f419e46c71c58
| | 9e9375489f63007d94f6273bb71b8b
| | 979e8c29b110774f4a134192b6e979
| | 73a7b59856c16f31b7da29b6214699
| | 3018bc11ed5fd3b101a3fa ........... Surjection proof
| fd4e10 ............................. Range proof length (0xfd4e10 = 4174, refer to VarInt docs for deserialization info)
| | 603300000000000000011f237(..)  ... Range proof (shortened for brevity)
|
|                                      Output witness #5
| 00 ................................. Surjection proof length
| 00 ................................. Range proof length
```

#### Example 3

Signed peg-in claim transaction on liquidv1 (production liquid).

Raw hex:
```
0200000001013d0bfb6e61989331d67dac3b6adf067afda20f504cabb1a7364853a68a0bb6df0000004000ffffffff02016d521c38ec1ea15734ae22b7c46064412829c0d0579f0a713d1c04ede979026f0100000000002b09c1001600143921df9000812998ceff99b610437734d552424f016d521c38ec1ea15734ae22b7c46064412829c0d0579f0a713d1c04ede979026f01000000000000002700000000000000000247304402204f84bb59c2af17b76ba71486a3fe4941829f0b5d23bda5c9f49c449489693e5002206e1f3bba907e511e99bf317059264f89a56c50c56fefa82583b8e941b865facc012102e776bdb5d8fc14d24b330c0efbf34227cbba1cf25eb0778aa45f8b7cb34950460608e8092b0000000000206d521c38ec1ea15734ae22b7c46064412829c0d0579f0a713d1c04ede979026f206fe28c0ab6f1b372c1a6a246ae63f74f931e8365e15a089c68d6190000000000160014504b2e2f011741aec712fb2f51dc1537272f284a53020000000113391c88becfe2a855a74fb1890cabef7c81a4be742771046ca0c38e29cfada501000000000000008001e8092b000000000017a9144d733642e6cc020cfd3b2ae52e4ef1b50be6a15f8700000000fd990100004020fe6c0db88a5a5b747b9fa39abbf100641325110dd17c00000000000000000000da21e101b583f398f9d46d97b4d083f6142b0fc67dff71bb2969862fa9e346fe2a05fc627efd0917b8cc42a7bd0900000a874b10883f43cb8d4e8703e8861296688ded81d601a6cb4b68b9680faf7974401da4d3e264de6948f2df86a20cc7dc588a3ff8cc05c27afdd35b1cf50ccf7ae4acf64afb05980884134795302653d442be5f7dd80071ab56b25f57d411545122e475f642f7d98042282c59203e09cd3db6544fc4aac33069ab94057358815a3a6b9e1cb47d349006a33832c6a8a32105d1f16a63982aeea22f19d2c365030d4e3d0bfb6e61989331d67dac3b6adf067afda20f504cabb1a7364853a68a0bb6df9231e9542459531f983b26c6dff457ec9af808191d709c761c22d86a8e59d8200f580dc22957e89c3fe8f3d5dc34f9add75e288041f2b4bc5639ee915535a187c89756e0bd15f3b539864dd4e6dacea4fdd5daa290523e4cf9231cccab094c7efc9f6cf9bc4679908cffcb16a2ff3ec061c66bfa15b886c08c6973776d2fba78035dd70300000000
```

Deserialization:
```
02000000 ............................. Version

01 ................................... Flags (0x01 → witness data is present)
|
|                                      Input #1
| 3d0bfb6e61989331d67dac3b6adf067a
| fda20f504cabb1a7364853a68a0bb6df ... Outpoint TXID: dfb60b8aa6534836a7b1ab4c500fa2fd7a06df6a3bac7dd6319398616efb0b3d
| 00000040 ........................... Output Index (little-endian → 0x40000000 → second most significant bit is 1 → peg-in)
|
| 00 ................................. ScriptSig length
| | .................................. ScriptSig (empty: segwit transaction)
|
| ffffffff ........................... Sequence number: UINT32_MAX

02 ................................... Num outputs
|
|                                      Output #1
| 01 ................................. Asset header (0x01 → explicit, unblinded value)
| 6d521c38ec1ea15734ae22b7c4606441
| 2829c0d0579f0a713d1c04ede979026f ... Asset ID: 6f0279e9ed041c3d710a9f57d0c02928416460c4b722ae3457a11eec381c526d
|
| 01 ................................. Amount header (0x01 → explicit, unblinded value)
| 00000000002b09c1 ................... Amount: 0.02820545 L-BTC
|
| 00 ................................. Nonce header (0x00 → null)
|
| 16 ................................. ScriptPubKey length (0x16 = 22)
| | 00143921df9000812998ceff99b610
| | 437734d552424f ................... ScriptPubKey
|
|                                      Output #2
| 01 ................................. Asset header (0x01 → explicit, unblinded value)
| 6d521c38ec1ea15734ae22b7c4606441
| 2829c0d0579f0a713d1c04ede979026f ... Asset ID: 6f0279e9ed041c3d710a9f57d0c02928416460c4b722ae3457a11eec381c526d
|
| 01 ................................. Amount header (0x01 → explicit, unblinded value)
| 0000000000000027 ................... Amount: 0.00000039 L-BTC
|
| 00 ................................. Nonce header (0x00 → null)
|
| 00 ................................. ScriptPubKey length
| | .................................. ScriptSig (empty: segwit transaction)

00000000 ............................. Locktime

...................................... Input witnesses (1 per input)
|
|                                      Input witness #1
| 00 ................................. Issuance amount range proof (null)
| 00 ................................. Inflation keys range proof (null)
| 02 ................................. Script witness stack length
| | 47 ............................... Stack item #1 length (0x47 = 71 bytes)
| | | 304402204f84bb59c2af17b76ba7
| | | 1486a3fe4941829f0b5d23bda5c9
| | | f49c449489693e5002206e1f3bba
| | | 907e511e99bf317059264f89a56c
| | | 50c56fefa82583b8e941b865facc
| | | 01 ............................. Stack item #1
| | 21 ............................... Stack item #2 length (0x21 = 33 bytes)
| | | 02e776bdb5d8fc14d24b330c0efb
| | | f34227cbba1cf25eb0778aa45f8b
| | | 7cb3495046 ..................... Stack item #2
| 06 ................................. Peg-in witness stack length
| | 08 ............................... Stack item #1 length
| | | e8092b0000000000 ............... Peg-in value (little-endian): 0x2b09e8 = 0.02820545 BTC)
| | 20 ............................... Stack item #2 length (0x20 = 32)
| | | 6d521c38ec1ea15734ae22b7c46064
| | | 412829c0d0579f0a713d1c04ede979
| | | 026f ........................... Asset ID: 6f0279e9ed041c3d710a9f57d0c02928416460c4b722ae3457a11eec381c526d
| | 20 ............................... Stack item #3 length (0x20 = 32)
| | | 6fe28c0ab6f1b372c1a6a246ae63f7
| | | 4f931e8365e15a089c68d619000000
| | | 0000 ........................... Genesis hash: 000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f
| | 16 ............................... Stack item #4 length (0x16 = 22)
| | | 0014504b2e2f011741aec712fb2f51
| | | dc1537272f284a ................. Claim script
| | 53 ............................... Stack item #5 length
| | | 020000000113391c88becfe2a855a7
| | | 4fb1890cabef7c81a4be742771046c
| | | a0c38e29cfada50100000000000000
| | | 8001e8092b000000000017a9144d73
| | | 3642e6cc020cfd3b2ae52e4ef1b50b
| | | e6a15f8700000000 ............... Serialized mainchain peg-in transaction
| | fd9901 ........................... Stack item #6 length (0xfd9901 = 409, refer to VarInt docs for deserialization info)
| | | 00004020fe6c0db88a5a5b747b(..).. Mainchain transaction inclusion merkle proof (shortened for brevity)

...................................... Output witnesses (1 per output)
|
|                                      Output #1 witness
| 00 ................................. Surjection proof length
| 00 ................................. Range proof length
|
|                                      Output #2 witness
| 00 ................................. Surjection proof length
| 00 ................................. Range proof length
```
