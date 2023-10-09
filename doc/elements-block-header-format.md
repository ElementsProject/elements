# Elements Block Header Format

This document describes the format used to serialize Elements block headers.

The relevant C++ serialization code is in [`src/primitives/block.h`](https://github.com/ElementsProject/elements/blob/elements-22.1/src/primitives/block.h#L240)

_Notes_:

- Fields in the following tables are serialized in the order they are listed, from top to bottom.

- The Byte Order column shows the [Endianness](https://en.wikipedia.org/wiki/Endianness) of the serialized bytes.

- In the LiquidV1 chain, Dynamic Federations (DynaFed) has been active since block height `1517040`.

#### "CompactSize" Encoding

Inherited from Bitcoin, Elements encodes the lengths of vectors using an encoding _"known inside the Bitcoin Core codebase as the CompactSize encoding, though it has historically been referred to in external protocol documentation as VarInt."_

[Bitcoin Stack Exchange](https://bitcoin.stackexchange.com/a/114585/134939)

- If the length of the vector is less than 253, then 1 byte is used to encode the value itself.
- If the length is 253 up to 65535 (uint16 max), then the length is encoded as `0xFD` + 2 bytes for the value.
- If the length is 65536 up to 4294967295 (uint32 max), then the length is encoded as `0xFE` + 4 bytes for the value.
- If the length is larger than 4294967295, then the length is encoded as `0xFF` + 8 bytes for the value.

All values above are encoded in little endian.

Link to Elements source: [`src/serialize.h`](https://github.com/ElementsProject/elements/blob/elements-22.1/src/serialize.h#L234)

## Data Types

### Block Header (`class CBlockHeader`)

---

**Pre-DynaFed Headers**

> Before block height `1517039`, DynaFed was not yet active on LiquidV1.

| Field               | Required         | Size     | Data Type  | Byte Order    | Notes                                                                                                                                                                           |
| ------------------- | ---------------- | -------- | ---------- | ------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Version             | Yes              | 4 bytes  | `int32_t`  | little endian | Normally `0x2000000` (decimal `536870912`) unless additional [version bits signalling](https://github.com/ElementsProject/elements/blob/elements-22.1/src/chainparams.cpp#L344) |
| Previous Block Hash | Yes              | 32 bytes | `uint256`  | little endian | Hashes are serialized in [reverse byte order](https://bitcoin.stackexchange.com/a/116731/134939)                                                                                |
| Merkle Root         | Yes              | 32 bytes | `uint256`  | little endian |                                                                                                                                                                                 |
| Timestamp           | Yes              | 4 bytes  | `uint32_t` | little endian | [Unix time](https://en.wikipedia.org/wiki/Unix_time)                                                                                                                            |
| Block Height        | No               | 4 bytes  | `uint32_t` | little endian | Included when option `-con_blockheightinheader=1`, which is active for LiquidV1                                                                                                 |
| Proof               | Yes <sup>1</sup> | Variable | `CProof`   |               | Required when `-con_signed_blocks=1`, which was active for LiquidV1 pre-dynafed                                                                                                 |
| Bits                | Yes <sup>2</sup> | 4 bytes  | `uint32_t` | little endian | Required when `-con_signed_blocks=0`                                                                                                                                            |
| Nonce               | Yes <sup>2</sup> | 4 bytes  | `uint32_t` | little endian | Required when `-con_signed_blocks=0`                                                                                                                                            |

1. Proof is only required for signed blockchains.
2. Bits and Nonce are required for Proof of Work blockchains. See [Bitcoin docs](https://developer.bitcoin.org/reference/block_chain.html#target-nbits).

#### Proof (`class CProof`)

| Field     | Required | Size     | Data Type | Notes                                           |
| --------- | -------- | -------- | --------- | ----------------------------------------------- |
| Challenge | Yes      | Variable | `CScript` | Block "public key"                              |
| Solution  | Yes      | Variable | `CScript` | Satisfying witness to the challenge, or nothing |

---

**DynaFed Headers**

DynaFed has been active on LiquidV1 from block height `1517040` onwards.

| Field               | Required | Size     | Data Type                       | Byte Order    | Notes                                                                                                                                                        |
| ------------------- | -------- | -------- | ------------------------------- | ------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Version             | Yes      | 4 bytes  | `int32_t`                       | little endian | Dynafed version is `0xa0000000` (`2684354560`) which is the normal version `0x20000000` bitwise OR'd with the dynafed mask `0x80000000` <sup>1</sup>         |
| Previous Block Hash | Yes      | 32 bytes | `uint256`                       | little endian | Hashes are serialized in [reverse byte order](https://bitcoin.stackexchange.com/a/116731/134939)                                                             |
| Merkle Root         | Yes      | 32 bytes | `uint256`                       | little endian |                                                                                                                                                              |
| Timestamp           | Yes      | 4 bytes  | `uint32_t`                      | little endian | [Unix time](https://en.wikipedia.org/wiki/Unix_time)                                                                                                         |
| Block Height        | No       | 4 bytes  | `uint32_t`                      | little endian | Included when option `-con_blockheightinheader=1`, which is active for LiquidV1                                                                              |
| DynaFed Parameters  | Yes      | Variable | `DynafedParams`                 |               |                                                                                                                                                              |
| Signblock Witness   | Yes      | Variable | `vector<vector<unsigned char>>` |               | The witness is not serialized [for hashes or weight calculation](https://github.com/ElementsProject/elements/blob/elements-22.1/src/primitives/block.h#L259) |

1. Elements [removes the DynaFed mask](https://github.com/ElementsProject/elements/blob/elements-22.1/src/chain.h#L366) during deserialization. The DynaFed version mask is `0x80000000`.

#### DynaFed Parameters (`class DynaFedParams`)

| Field    | Required | Size | Data Type           | Notes                                                                                                                                            |
| -------- | -------- | ---- | ------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------ |
| Current  | Yes      |      | `DynaFedParamEntry` | The active DynaFed parameters at this height                                                                                                     |
| Proposed | Yes      |      | `DynaFedParamEntry` | The proposed DynaFed parameters for the next [epoch](https://github.com/ElementsProject/elements/blob/elements-22.1/src/chainparamsbase.cpp#L60) |

In DynaFed, the chain is initialized with a *dynamic epoch length*. This is the number of blocks that Dynamic Federation voting and enforcement are in effect for. In Liquid this value is 20160 blocks, approximately 2 weeks. When DynaFed is active, the Current parameters will always either be a Full set of all fields in the DynaFedParamEntry (given below), or a set of Compact parameters indicating no change since the previous Full parameters. During a normal non-proposing epoch, the Proposed parameters will be Null, indicating that no change in the Federation is being proposed for the next epoch. During a proposing epoch, block producers will include their intended parameters in the Proposed field, either as Full parameters or Compact parameters committing to their previous proposal.

In order for a Proposed entry to be locked-in, at the end of the proposing epoch at least 4/5 blocks in that epoch must agree on the same Proposed parameters. If that condition is satisfied, then in the following epoch those Proposed parameters will become the Current parameters. There is a configurable `total_valid_epochs` consensus setting that defines how many epochs a given fedpegscript is valid for. In Liquid, this value is 2, meaning that once Proposed parameters become Current (ie. a successful transition), the fedpegscript of the previous epoch is valid for a grace period of 1 more epoch.
#### DynaFed Parameters Entry (`class DynaFedParamEntry`)

| Field                   | Required          | Size     | Data Type                       | Byte Order    | Notes                                                                                                                                                         |
| ----------------------- | ----------------- | -------- | ------------------------------- | ------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Entry Type              | Yes               | 1 byte   | `unsigned char`                 |               | `0` -> Null params, `1` -> Compact params, `2` -> Full Params                                                                                                 |
| Signblock Script        | Entry Types 1 & 2 |          | `CScript`                       |               | "scriptPubKey" used for block signing                                                                                                                         |
| Signblock Witness Limit | Entry Types 1 & 2 | 4 bytes  | `uint32_t`                      | little endian | Maximum size in bytes of the size of a blocksigning witness                                                                                                   |
| Elided Root             | Entry Type 1 only | 32 bytes | `uint256`                       |               | Only non-zero when Entry Type is 1 (pruned/compact). This hash commits to the pruned fields, which are considered unchanged since the last Full params entry. |
| Fed Peg Program         | Entry Type 2 only |          | `CScript`                       |               | The "scriptPubKey" of the fedpegscript                                                                                                                        |
| Fed Peg Script          | Entry Type 2 only |          | `CScript`                       |               | The witnessScript for witness v0, or otherwise undefined.                                                                                                     |
| Extension Space         | Entry Type 2 only |          | `vector<vector<unsigned char>>` |               | Interpreted as pairs of Pegout Authorization Keys (PAKs) on LiquidV1                                                                                          |

---

### Examples

#### Pre-DynaFed

| Block Height | Block Hash                                                         | Link to header hex                                                                                                                    |
| ------------ | ------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------- |
| `1517039`  | `33a0890bea61d70b9dd1bd23f12e447730336906a44cdea621cba6d65fe90013` | [blockstream.info](https://blockstream.info/liquid/api/block/33a0890bea61d70b9dd1bd23f12e447730336906a44cdea621cba6d65fe90013/header) |

4 bytes - **version** (`0x20000000 | 0x02000000` - 25th bit [dynafed signalling](https://github.com/ElementsProject/elements/blob/elements-22.1/src/chainparams.cpp#L344))

`00000022`

32 bytes - **previous block hash**

`f66be8726f4afecc9a7b087a78cd25edd53485755d26e456d546bcc0613a30f9`

32 bytes - **Merkle root**

`58427ea62f97951868724d09a55fd7808093f4b8c3a01cd96d4203f02759e877`

4 bytes - **timestamp** (`1633382159`)

`0f6f5b61`

4 bytes - **block height** (`1517039`)

`ef251700`

**proof**

**challenge**

1 byte - **compactsize identifier** (`253` = 2 byte length)

`fd`

2 bytes - **number of bytes of challenge** (`513`)

`0102`

513 bytes - **challenge**

`5b21026a2a106ec32c8a1e8052e5d02a7b0a150423dbd9b116fc48d46630ff6e6a05b92102791646a8b49c2740352b4495c118d876347bf47d0551c01c4332fdc2df526f1a2102888bda53a424466b0451627df22090143bbf7c060e9eacb1e38426f6b07f2ae12102aee8967150dee220f613de3b239320355a498808084a93eaf39a34dcd62024852102d46e9259d0a0bb2bcbc461a3e68f34adca27b8d08fbe985853992b4b104e27412102e9944e35e5750ab621e098145b8e6cf373c273b7c04747d1aa020be0af40ccd62102f9a9d4b10a6d6c56d8c955c547330c589bb45e774551d46d415e51cd9ad5116321033b421566c124dfde4db9defe4084b7aa4e7f36744758d92806b8f72c2e943309210353dcc6b4cf6ad28aceb7f7b2db92a4bf07ac42d357adf756f3eca790664314b621037f55980af0455e4fb55aad9b85a55068bb6dc4740ea87276dc693f4598db45fa210384001daa88dabd23db878dbb1ce5b4c2a5fa72c3113e3514bf602325d0c37b8e21039056d089f2fe72dbc0a14780b4635b0dc8a1b40b7a59106325dd1bc45cc70493210397ab8ea7b0bf85bc7fc56bb27bf85e75502e94e76a6781c409f3f2ec3d1122192103b00e3b5b77884bf3cae204c4b4eac003601da75f96982ffcb3dcb29c5ee419b92103c1f3c0874cfe34b8131af34699589aacec4093399739ae352e8a46f80a6f68375fae`

**solution**

1 byte - **compactsize identifier** (`253` = 2 byte length)

`fd`

2 bytes - **number of bytes of challenge** (`790`)

`1603`

790 bytes - **solution**

`0046304402204491693cf0b5d12c29a8d3cf5a75b4eca2084872aa19aa779913c616c025163c0220244eac0b368fbb79ef44e77e54ec6ba6f82c43abbd8addab50949a5092d52cde473045022100ada3971c376b36d0c98f8029d648a6baa3a436234deb65bb4e21dda5cfa2165c0220138b26f86eb5d9bb8850fd76b9ae2aecf333e5346457cd6ee87203d12a56f72c473045022100855027e207f43db9bd3550369850dd5ccdca833861d7be73fafe3f3e44dbc113022078db3ee49847b60511ec753bdc992aff17415587aa2cdda6708b20d0c9076d6f473045022100f9b3586e166778367c91886baabb7692751df47bc47f5a625782cc545aca79210220147ebd52c711e3c3abd9fdbaee1852ee3d6d5a905d4354491b6cf058bfe5e85a473045022100ad0dabcdd1b27ec88e497a5e669e471c35cab778d8b9ac9e6282fcf28f8d44e902205b9cce643df7d0a982641629be4b01a06d9640d5a41db1bd9a92270d747f253c473045022100ba8af618ec39f16144bd4eb375506df059bea1ed84d68cd0cbd7801c5e27900802206a5b8b250294c669757199fbc1cd82b077e8c10beda0b8aaac4eaf3bf97a292746304402207f868b1344f4be0e7723fced94d3586213a932aa2133853afc0f2cd98ab01cfc02201bc3d422e17363a29d7e9bdd104ad2c01eb60cdaccb82658942ca3fa0a491342473045022100d9b76a60c1ddb9b8bb3efff1b4b9184088c9fcc2ca7fab1013eb39cc3b16a5560220585b60e14ef5f8377df6385216bc4d01c4855656cf9ced057d82562169b48ec3463044022048ff3177c628c8eba7851c5d11edc37be0beac291a05da4b307e4c20839cc04d02203480a49e3b176ff4de805d641a1cb968b399f80b9d07d1090d405b8e6789557f473045022100c43eafab306e95bf9e7390c110c55f4003fb02f3eddb2d430e1caaaf8671b9af02207395cfb718c8ab359e9969774de1ef06c13b9f48b26a2bd7d45e8ab292acdba0473045022100eb9354017e185220795aa8f9dad5f67ed9bddba852891fc2ddbbbd03bda1468a0220230d895481e2b981ba331ded999fe1fd4ce729eb3f1575d71b0c8ca0f4efcf87`

#### DynaFed - Full Parameters

| Block Height | Block Hash                                                         | Link to header hex                                                                                                                    |
| ------------ | ------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------- |
| `1517040`  | `1f8d44d6a34987f59cd19061d0af7b8734ab9129737397a95fc85ba38309ca3d` | [blockstream.info](https://blockstream.info/liquid/api/block/1f8d44d6a34987f59cd19061d0af7b8734ab9129737397a95fc85ba38309ca3d/header) |

4 bytes - **version** (`0x20000000 | 0x80000000`)

`000000a0`

32 bytes - **previous block hash**

`1300e95fd6a6cb21a6de4ca40669333077442ef123bdd19d0bd761ea0b89a033`

32 bytes - **Merkle root**

`b4a1253a088ffa22a87ac183bd9bceff1ec5d74f15c3cab5e8cf6f2eefbb216c`

4 bytes - **timestamp** (`1633462198`)

`b6a75c61`

4 bytes - **block height** (`1517040`)

`f0251700`

**current dynafed params entry**

1 byte - **dynafed param entry type** (`2` = full)

`02`

**signblock script**

1 byte - **number of bytes of script** (`34`)

`22`

34 bytes - **signblock script**

`0020e51211e91d9cf4aec3bdc370a0303acde5d24baedb12235fdd2786885069d91c`

4 bytes - **signblock witness limit** (`1416`)

`88050000`

**fedpeg program**

1 byte - **number of bytes of script** (`23`)

`17`

23 bytes - **fedpeg program**

`a9149e10aa3d2f248e0e42f9bab31e858240e7ed40e487`

**fedpeg script**

1 byte - **compactsize identifier** (`253` = 2 byte length)

`fd`

2 bytes - **number of bytes of script** (`628`)

`7402`

628 bytes - **fedpeg script**

`745c87635b21020e0338c96a8870479f2396c373cc7696ba124e8635d41b0ea581112b678172612102675333a4e4b8fb51d9d4e22fa5a8eaced3fdac8a8cbf9be8c030f75712e6af992102896807d54bc55c24981f24a453c60ad3e8993d693732288068a23df3d9f50d4821029e51a5ef5db3137051de8323b001749932f2ff0d34c82e96a2c2461de96ae56c2102a4e1a9638d46923272c266631d94d36bdb03a64ee0e14c7518e49d2f29bc40102102f8a00b269f8c5e59c67d36db3cdc11b11b21f64b4bffb2815e9100d9aa8daf072103079e252e85abffd3c401a69b087e590a9b86f33f574f08129ccbd3521ecf516b2103111cf405b627e22135b3b3733a4a34aa5723fb0f58379a16d32861bf576b0ec2210318f331b3e5d38156da6633b31929c5b220349859cc9ca3d33fb4e68aa08401742103230dae6b4ac93480aeab26d000841298e3b8f6157028e47b0897c1e025165de121035abff4281ff00660f99ab27bb53e6b33689c2cd8dcd364bc3c90ca5aea0d71a62103bd45cddfacf2083b14310ae4a84e25de61e451637346325222747b157446614c2103cc297026b06c71cbfa52089149157b5ff23de027ac5ab781800a578192d175462103d3bde5d63bdb3a6379b461be64dad45eabff42f758543a9645afd42f6d4248282103ed1e8d5109c9ed66f7941bc53cc71137baa76d50d274bda8d5e8ffbd6e61fe9a5f6702c00fb275522103aab896d53a8e7d6433137bbba940f9c521e085dd07e60994579b64a6d992cf79210291b7d0b1b692f8f524516ed950872e5da10fb1b808b5a526dedc6fed1cf29807210386aa9372fbab374593466bc5451dc59954e90787f08060964d95c87ef34ca5bb5368ae`

**extension space**

1 byte - **number of items in vector** (`40`)

`28`

1 byte - **number of bytes of first item** (`66`)

`42`

66 bytes - **pair of public keys**

`02555f97c44ad9286ef060a02b00e8e6be2626ed3eb9230705d3ca2f977daae61e03cddbc847f64f898b883d717a7f637bedf9ac2ecd243721eada223f1b1790f75b`

1 byte - **number of bytes of second item** (`66`)

`42`

66 bytes - **pair of public keys**

`033fad80bd2b818d1ca8a8d4a25dafcf5e740be07db6788be1f2f15266e3c6805d0253ff3f140ef8f594d54996eab810a82550c79204279920d95681afe699d00da5`

**_... 37 similar omitted pairs of public keys ..._**

1 byte - **number of bytes of last item** (`66`)

`42`

66 bytes - **pair of public keys**

`032d9af13c8d5f5316fd27a14bafb8ec55684ef2e3b5c64b2645e088f570e5d2cb0239590f39508465decfd8a1bdc61b42333297e80588ed826ddd43678edfa6caae`

**proposed dynafed params entry**

1 byte - **dynafed param entry type** (`0` = null)

`00`

**signblock witness**

1 byte - **number of items in vector** (`13`)

`0d`

1 byte - **number of bytes of first stack item** (`0`)

`00`

1 byte - **number of bytes of second stack item** (`71`)

`47`

71 bytes - **stack item**

`304402202b9ed0d3878eaab003014f788a9c64d9aae29ee34a77504be1c63f8362b69ed902200c2c8f4ea161b039c42122bfe4aacaa58ddecf7b135443ee90ba43b29621b0e701`

**_... 4 similar omitted 71 byte stack items ..._**

1 byte - **number of bytes of seventh stack item** (`72`)

`48`

72 bytes - **stack item**

`30450221008a4b2e6e19bf35c2fcd4d7a8aac71112c5167cab14c88d747c955106eed925460220087ef8246a3e7b3734bac9be4ec451f21fb075c3900844882c927b0434f5858f01`

1 byte - **number of bytes of eighth stack item** (`71`)

`47`

71 bytes - **stack item**

`30440220155bc86cd3881f3bcf1bdf9faf01f573ccd7f33e122ac60f65ddbcfa85530ff102207d1bbfb556215d1f1fb77f6ae5167755d549a7d3729ad25dcba45710a425876c01`

1 byte - **number of bytes of ninth stack item** (`72`)

`48`

72 bytes - **stack item**

`3045022100f22bd0d11599e644fd7f3dc2000b3b062c54289e6320de6db4b1498671f8f5f302203b8516986f326816addfea33e33cf60c17317ac3115d83e560063e9d51fbbdb501`

1 byte - **number of bytes of tenth stack item** (`72`)

`48`

72 bytes - **stack item**

`3045022100be32f27c8733c2cbc36a5b1be7f97dafd8b9d45a7e3aaef4b75c71f7f616f5b4022037f98b6970109646157db5e2cf8e0f6c40468ff846c4fe572aa43b6ef709acfe01`

1 byte - **number of bytes of eleventh stack item** (`72`)

`48`

72 bytes - **stack item**

`3045022100e795a36af35bf410e751e3ee003962382567985c9dc7bffaeb6b0ffc84f5ec0402204d90913c6a275ddf1ceae40462fdca00481951d903937d749a67a693c2d62c3101`

1 byte - **number of bytes of twelfth stack item** (`71`)

`47`

71 bytes - **stack item**

`3044022057900b7701dcc3f5bf5a21b221124abfd4dabb8555428fb20714e6512a9f562a022009f6bd4eb984c10a8a13a238271f43a7bafa7de102cd413820ab18ca603c6cf301`

1 byte - **compactsize identifier** (`253`)

`fd`

2 bytes - **number of bytes of thirteenth item** (`513`)

`0102`

513 bytes - **stack item**

`5b21026a2a106ec32c8a1e8052e5d02a7b0a150423dbd9b116fc48d46630ff6e6a05b92102791646a8b49c2740352b4495c118d876347bf47d0551c01c4332fdc2df526f1a2102888bda53a424466b0451627df22090143bbf7c060e9eacb1e38426f6b07f2ae12102aee8967150dee220f613de3b239320355a498808084a93eaf39a34dcd62024852102d46e9259d0a0bb2bcbc461a3e68f34adca27b8d08fbe985853992b4b104e27412102e9944e35e5750ab621e098145b8e6cf373c273b7c04747d1aa020be0af40ccd62102f9a9d4b10a6d6c56d8c955c547330c589bb45e774551d46d415e51cd9ad5116321033b421566c124dfde4db9defe4084b7aa4e7f36744758d92806b8f72c2e943309210353dcc6b4cf6ad28aceb7f7b2db92a4bf07ac42d357adf756f3eca790664314b621037f55980af0455e4fb55aad9b85a55068bb6dc4740ea87276dc693f4598db45fa210384001daa88dabd23db878dbb1ce5b4c2a5fa72c3113e3514bf602325d0c37b8e21039056d089f2fe72dbc0a14780b4635b0dc8a1b40b7a59106325dd1bc45cc70493210397ab8ea7b0bf85bc7fc56bb27bf85e75502e94e76a6781c409f3f2ec3d1122192103b00e3b5b77884bf3cae204c4b4eac003601da75f96982ffcb3dcb29c5ee419b92103c1f3c0874cfe34b8131af34699589aacec4093399739ae352e8a46f80a6f68375fae`

---

#### DynaFed - Compact and Full Parameters

| Block Height | Block Hash                                                         | Link to header hex                                                                                                                    |
| ------------ | ------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------- |
| `2197439`  | `e889f779cd06228fc423b115fc913cbdaf213296b2a465f6869c98bc8d7fbe54` | [blockstream.info](https://blockstream.info/liquid/api/block/e889f779cd06228fc423b115fc913cbdaf213296b2a465f6869c98bc8d7fbe54/header) |

4 bytes - **version** (`0x20000000 | 0x80000000`)

`000000a0`

32 bytes - **previous block hash**

`585732427571f441f406fc65376fb36fdf244c233e4d1e05717acbaed419b72f`

32 bytes - **merkle root**

`9612b230cbb31c872d317c0862bc83dbbeae0b48265138c08803a4d946583c3f`

4 bytes - **timestamp** (`1674644468`)

`f40bd163`

4 bytes - **block height** (`2197439`)

`bf872100`

**current dynafed params**

1 byte - **entry type** (`1` = compact)

`01`

**signblock script**

1 byte - **length** (`34`)

`22`

34 bytes - **script**

`002080d146b4003a2f942bfc9a288c364cb3b7b0d72278d55f7fab93e1cad15331e6`

4 bytes - **signblock witness limit** (`1325`)

`2d050000`

32 bytes - **elided root**

`5615a639dc8fcb963288539533fb031fc8e174680a6c78c2d11f134f38fa47cf`

**proposed dynafed parameters**

1 byte - **entry type** (`2` = full)

`02`

**signblock script**

1 byte - **length** (`34`)

`22`

34 bytes - **script**

`002080d146b4003a2f942bfc9a288c364cb3b7b0d72278d55f7fab93e1cad15331e6`

4 bytes - **signblock witness limit** (`1325`)

`2d050000`

**fedpeg program**

1 byte - **length** (`34`)

`22`

34 bytes - **script**

`0020333a4af67452308b9814ff59dc2fc3d0325fd7fdcb61d108e992b3956095f2fe`

**fedpeg script**

1 byte - **compactsize identifier** (`253` = 2 byte length)

`fd`

2 bytes - **length** (`626`)

`7202`

626 bytes - **script**

`5b21020e0338c96a8870479f2396c373cc7696ba124e8635d41b0ea581112b678172612102675333a4e4b8fb51d9d4e22fa5a8eaced3fdac8a8cbf9be8c030f75712e6af992102896807d54bc55c24981f24a453c60ad3e8993d693732288068a23df3d9f50d4821029e51a5ef5db3137051de8323b001749932f2ff0d34c82e96a2c2461de96ae56c2102a4e1a9638d46923272c266631d94d36bdb03a64ee0e14c7518e49d2f29bc401021031c41fdbcebe17bec8d49816e00ca1b5ac34766b91c9f2ac37d39c63e5e008afb2103079e252e85abffd3c401a69b087e590a9b86f33f574f08129ccbd3521ecf516b2103111cf405b627e22135b3b3733a4a34aa5723fb0f58379a16d32861bf576b0ec2210318f331b3e5d38156da6633b31929c5b220349859cc9ca3d33fb4e68aa08401742103230dae6b4ac93480aeab26d000841298e3b8f6157028e47b0897c1e025165de121035abff4281ff00660f99ab27bb53e6b33689c2cd8dcd364bc3c90ca5aea0d71a62103bd45cddfacf2083b14310ae4a84e25de61e451637346325222747b157446614c2103cc297026b06c71cbfa52089149157b5ff23de027ac5ab781800a578192d175462103d3bde5d63bdb3a6379b461be64dad45eabff42f758543a9645afd42f6d4248282103ed1e8d5109c9ed66f7941bc53cc71137baa76d50d274bda8d5e8ffbd6e61fe9a5fae736402c00fb269522103aab896d53a8e7d6433137bbba940f9c521e085dd07e60994579b64a6d992cf79210291b7d0b1b692f8f524516ed950872e5da10fb1b808b5a526dedc6fed1cf29807210386aa9372fbab374593466bc5451dc59954e90787f08060964d95c87ef34ca5bb53ae68`

**extension space**

1 byte - **number of items in vector** (`50`)

`32`

1 byte - **length**

`42`

66 bytes - **pair of public keys**

`02555f97c44ad9286ef060a02b00e8e6be2626ed3eb9230705d3ca2f977daae61e03cddbc847f64f898b883d717a7f637bedf9ac2ecd243721eada223f1b1790f75b`

**_... 48 similar omitted pairs of public keys ..._**

1 byte - **length**

`42`

66 bytes - **pair of public keys**

`02a04cad1256813f6a27259259911d25889c76aa783f7e89ab07e78b8f2288682e022709b399de547dc3850617092f2e47b0b6bf470a335f763c157c9ef11f7a2666`

**signblock witness**

1 byte - **number of items**

0d

1 byte - **length** (`0`)

`00`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100fd4ef1df91d8d452ef7a3ee2e857e25ed803d0c2ce29bfff56dd95d83ddb434b02206b797496a478fd564857fcc96e52cf92229fb86d95b1dcad87ba73409444f03501`

1 byte - **length** (`71`)

`47`

71 bytes - **item**

`3044022063ed103733c0615b573f063fc4d628aeac157f65d811d52654761b27e26a659a02205c4be52459c4f93a56c16efcdf16c12d4335e5f9f6d67aa727cdf0975bb6019301`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100f27d41105bc2d45a7b97e4687bcb0fc8f69ed86afddb04c85fbfc56db5680ae80220475a210835262b6e1c19d52a253f30fabf8180514c082e932bb536a9c0fda5c101`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100ac357a196dbfc868217e4a8e616e7d4a0130c09bd4fd6daa1bc1cc420d861d960220206e0d6dbe178fef544dd207d9a4bb97144a829b7ddd99d9e77588183332c4af01`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100d697104663cf618f6de31b58c3e1eaea60a81c3255c94b7e36743a564e7aac3d02207f7242fa81cda63a40ab4caa8a304cfb6ca70fd73929a853c39a3eb2b13bd40501`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100ade1bd5f077a510aad2a62fa0237a5f65f7146ae82e86a51a7aefff55932726a02203cb2bc6259cb9d42ef1d988732167c0569beff5f74504af17debeadab168c51401`

1 byte - **length** (`71`)

`47`

71 bytes - **item**

`304402205ffc0ea2db0d9b742ee60d53645c906bd2b44f32940228ca83e12fb7e4c820fa022029b21d81c0d8bce69d08ec89c6ef5eb3af13cbc3e823a475cece2de74d06fa4201`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`30450221009fa0b93828342be5e066b5bcfc57cfd4042206d09c57de24ece2243a88f2ec3702207671c838210b7135809d3d39f7481a394673662c1e0d8abcd0d8c6978f66aad801`

1 byte - **length** (`71`)

`47`

71 bytes - **item**

`304402201bd62398f9ad2c9edf422c6e91177290dcb24b7a6fb1980954b3febd6e1e7a02022015848f2f50797ab940422f62dc8b2db1d4f529a5c86e02104c0767290040242601`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100ac923a1ba600787f5c1a97bffb0c66c6bb73df29b14f223518abc460511c6e8f022050572cc69e12090708581d5db17a706bc0de4e5d158830ea11e639c450b9725301`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100ee51ef890fcc7728f0f27d2c5836929376da7b0fe0b23574248fdc9ccb92ec54022059d82e6dd431ac96e23985dba1dc4a79aedf113182096aecd4020ec65b35bd7d01`

1 byte - **compactsize identifier** (`253` = 2 byte length)

`fd`

2 bytes - **length** (`513`)

`0102`

513 bytes - **item**

`5b21026a2a106ec32c8a1e8052e5d02a7b0a150423dbd9b116fc48d46630ff6e6a05b92103326b356f7ad58556815a3ab2e606789bc5b5d10c2f38ebc7fb4c5692a0d3cfa02102888bda53a424466b0451627df22090143bbf7c060e9eacb1e38426f6b07f2ae12102aee8967150dee220f613de3b239320355a498808084a93eaf39a34dcd62024852102d46e9259d0a0bb2bcbc461a3e68f34adca27b8d08fbe985853992b4b104e27412102e9944e35e5750ab621e098145b8e6cf373c273b7c04747d1aa020be0af40ccd62102f9a9d4b10a6d6c56d8c955c547330c589bb45e774551d46d415e51cd9ad5116321033b421566c124dfde4db9defe4084b7aa4e7f36744758d92806b8f72c2e943309210353dcc6b4cf6ad28aceb7f7b2db92a4bf07ac42d357adf756f3eca790664314b621037f55980af0455e4fb55aad9b85a55068bb6dc4740ea87276dc693f4598db45fa210384001daa88dabd23db878dbb1ce5b4c2a5fa72c3113e3514bf602325d0c37b8e21039056d089f2fe72dbc0a14780b4635b0dc8a1b40b7a59106325dd1bc45cc70493210397ab8ea7b0bf85bc7fc56bb27bf85e75502e94e76a6781c409f3f2ec3d1122192103b00e3b5b77884bf3cae204c4b4eac003601da75f96982ffcb3dcb29c5ee419b92103c1f3c0874cfe34b8131af34699589aacec4093399739ae352e8a46f80a6f68375fae`

---

#### DynaFed - Compact and Null Parameters

| Block Height | Block Hash                                                         | Link to header hex                                                                                                                    |
| ------------ | ------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------- |
| `2197441`  | `b057a10a549fd95f1c8c30bccd3b564232d649b3ed8327c59f6ac523d0b586ad` | [blockstream.info](https://blockstream.info/liquid/api/block/b057a10a549fd95f1c8c30bccd3b564232d649b3ed8327c59f6ac523d0b586ad/header) |

4 bytes - **version** (`0x20000000 | 0x80000000`)

`000000a0`

32 bytes - **previous block hash**

`1c26ca99b0f2f531136eb9703efe4df80dd052d875c4d68dca48dc75d3b7aea0`

32 bytes - **Merkle root**

`1afe52dce37088b9d10080e968ef68f1598148ba3484572a84e8f92a1139cb8f`

4 bytes - **timestamp** (`1674644588`)

`6c0cd163`

4 bytes - **block height** (`2197441`)

`c1872100`

**current dynafed params entry**

1 byte - **dynafed param entry type** (`1` = compact)

`01`

**signblock script**

1 byte - **length** (`34`)

`22`

34 bytes - **script**

`002080d146b4003a2f942bfc9a288c364cb3b7b0d72278d55f7fab93e1cad15331e6`

4 bytes - **signblock witness limit** (`1325`)

`2d050000`

32 bytes - **elided root**

`5740aa3ef1f3172562ff038ba03129cc294e99f6c76874d5ebd82367bbee6005`

**proposed dynafed parameters**

1 byte - **entry type** (`0` = null)

`00`

**signblock witness**

1 byte - **number of items** (`13`)

`0d`

1 byte - **length** (`0`)

`00`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100fc3720634d5db81fea94fb9d9b9040103da9b5a82511f6fd20c92c64f64751e102200de3ab0e8f5f92518ddbda8e89a7a029b1118c6585da891f4b7a32383e74e35001`

1 byte - **length** (`71`)

`47`

71 bytes - **item**

`30440220036bfbc1b6abcef82e98d8c5dc6f3184913cea20713e072a894e46aaed5eb8bc02201f72486f4678e91d80e18e217b91b04d1912f27e0a96e9df0e3e59b26377b8bb01`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100fbb4c6125ed882943def6606fc594c330cb37ab1ccafbc3beb215640fe38c56e02205cb0fc03f083d25585afc46929c0ec9e9a92e8204679d30b0113758db28d11af01`

1 byte - **length** (`71`)

`47`

71 bytes - **item**

`3044022046f6b03990ae67629412ad6d82baefb6723a0d2b788c1bdcb4f210d171c76de602206b62a5ec8a145cc75e7f551c5caed2389a0c39deeae78e4726a06377280f97cb01`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100a2039c740998e4e9104a6dbb4792ca8880c20d3496741e10ffce81d30cfa0b2f02205a51515eca4e56de75cccb15237a1b6661abb63e963aee15f75662478fe506fa01`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100afe2ff3e0cdfd550d3ee976eeaacc724b80de9052edbbd9c78f794d353c9506f02202458326c2412dd261f08dff6b330552cf9372fa3f053d473a49bae29d9f22eaa01`

1 byte - **length** (`71`)

`47`

71 bytes - **item**

`3044022047fa73a69371dc70f8ee689f9d51a94bab0b733d6b3fbc29e82d37cb004427b802201446d330bf611dc1404f4c5146f23bd2c77572c832debbef21c661ad9e815f7f01`

1 byte - **length** (`71`)

`47`

71 bytes - **item**

`304402201182dca00bff9eb7424b309189d02449a0cb492c0669a3f91a22e3d90be6b86d0220147b07c34601c59e067fbd9ce4e7c773c57d64c8c8b2764149be95320d7a767b01`

1 byte - **length** (`71`)

`47`

71 bytes - **item**

`304402203d8ef69431bd0b969b065909d80038386839ce95c8ad7960e9530aa42cdd80d502204b2b54d634e77b89f36bb752e7e5d4294a78c07b2982e3337726d51d94bef33901`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100adb7b7ecfcdb89a474d9dd4f4fa6a6e85549fb0cb6d2519849e1a547576fe6ca0220493d29f4480324723c0af327aa2e21d8bcde23e88f419469f3ebcb0ba1d9816701`

1 byte - **length** (`72`)

`48`

72 bytes - **item**

`3045022100e129c209bb7703c36319c8a03dd2a81a1a3ef9408f5d57cc608942d2d71ee4d7022057913ee7325ca69682bb0439406217501fe4b78acbc748e58bbd24b467e35bf901`

1 byte - **compactsize identifier** (`253` = 2 byte length)

`fd`

2 bytes - **length** (`513`)

`0102`

513 bytes - **item**

`5b21026a2a106ec32c8a1e8052e5d02a7b0a150423dbd9b116fc48d46630ff6e6a05b92103326b356f7ad58556815a3ab2e606789bc5b5d10c2f38ebc7fb4c5692a0d3cfa02102888bda53a424466b0451627df22090143bbf7c060e9eacb1e38426f6b07f2ae12102aee8967150dee220f613de3b239320355a498808084a93eaf39a34dcd62024852102d46e9259d0a0bb2bcbc461a3e68f34adca27b8d08fbe985853992b4b104e27412102e9944e35e5750ab621e098145b8e6cf373c273b7c04747d1aa020be0af40ccd62102f9a9d4b10a6d6c56d8c955c547330c589bb45e774551d46d415e51cd9ad5116321033b421566c124dfde4db9defe4084b7aa4e7f36744758d92806b8f72c2e943309210353dcc6b4cf6ad28aceb7f7b2db92a4bf07ac42d357adf756f3eca790664314b621037f55980af0455e4fb55aad9b85a55068bb6dc4740ea87276dc693f4598db45fa210384001daa88dabd23db878dbb1ce5b4c2a5fa72c3113e3514bf602325d0c37b8e21039056d089f2fe72dbc0a14780b4635b0dc8a1b40b7a59106325dd1bc45cc70493210397ab8ea7b0bf85bc7fc56bb27bf85e75502e94e76a6781c409f3f2ec3d1122192103b00e3b5b77884bf3cae204c4b4eac003601da75f96982ffcb3dcb29c5ee419b92103c1f3c0874cfe34b8131af34699589aacec4093399739ae352e8a46f80a6f68375fae`
