# Elements RPC reference

























Elements includes many of the same Remote Procedure Calls (RPCs) as
Bitcoin Core.  This document only describes Elements RPCs that differ
from Bitcoin Core or that are entirely new.  For any RPCs not
referenced here, please see [Bitcoin.org's Developer
Reference](https://bitcoin.org/en/developer-reference).  The search box
at the top of that page provides a search with auto-completion.

For any RPC in either Elements or Bitcoin Core, you may obtain help at
the command line using the `help` RPC.  For example,

```text
elements-cli help getblockchaininfo
bitcoin-cli help getblockchaininfo
```

## Quick reference

The following short sections categorize the RPCs in this document.  For
a list of RPCs available in Bitcoin Core and which are not changed in
Elements, please see the [Bitcoin.org RPC quick reference][].
The methods in italics exist in Bitcoin Core, but are modified for elements.

### Generating
- [combineblocksigs][]
- [getnewblockhex][]
- [testproposedblock][]

### Raw transactions
- [blindrawtransaction][]
- *[createrawtransaction][]*
- *[decoderawtransaction][]*
- [rawblindrawtransaction][]
- *[sendrawtransaction][]*

### Utility
- [createblindedaddress][]
- [getblockstats][]
- *[getrawtransaction][]*
- *[validateaddress][]*
- [tweakfedpegscript][]

### Wallet
- [claimpegin][]
- [destroyamount][]
- [dumpassetlabels][]
- [dumpblindingkey][]
- [dumpissuanceblindingkey][]
- *[getbalance][]*
- [getpeginaddress][]
- *[gettransaction][]*
- *[getunconfirmedbalance][]*
- *[getwalletinfo][]*
- [importissuanceblindingkey][]
- [issueasset][]
- [listissuances][]
- *[listtransactions][]*
- *[listunspent][]*
- [reissueasset][]
- *[sendtoaddress][]*
- [sendtomainchain][]
- [signblock][]


The following RPCs are listed in alphabetical order.

## blindrawtransaction

The `blindrawtransaction` RPC takes a raw transaction and converts one or
more of its outputs into a [blinded output][].  It returns the modified
raw transaction. The blinding of outputs will be balanced against
any input blinding factors the wallet knows about.

*Parameter #1---the hex string of the raw transaction*

<table>
<thead>
 <tr>
  <th>Name</th>
  <th>Type</th>
  <th>Presence</th>
  <th>Description</th>
 </tr>
</thead>
<tbody>
 <tr>
  <td>hexstring</td>
  <td>string (hex)</td>
  <td>Required<br />(exactly 1)</td>
  <td markdown="block">
  
  The hex string of the [raw transaction][]
  
  </td>
  </tr>
 </tbody>
</table>

*Parameter #2---whether to return a transaction even if the blinding attempt fails*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
<tbody>
  <tr>
   <td>ignoreblindfail</td>
   <td>bool</td>
   <td>Optional<br />(0 or 1)</td>
   <td>Whether to return a transaction (rather than fail) when the blinding attempt fails due to the number of blinded inputs or outputs</td>
  </tr>
 </tbody>
</table>

*Parameter #3---input asset generators*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Generators</td>
   <td>array</td>
   <td>Optional<br />(0 or 1)</td>
   <td>Input asset generators.  Must be empty in the case the wallet knows all transaction inputs, or match the final input commitment list (including ordering) when one or more inputs is not known to the wallet. These are used to prove there are no assets being created out of thin air.  Must not include generators for issuances as those assets are inherently unblinded.</td>
  </tr>

  <tr>
   <td>→<br />assetcommitment</td>
   <td>string (hex)</td>
   <td>Optional<br />(1 or more)</td>
   <td markdown="block">
   
   A hex-encoded asset commitment, one for each input.  Null commitments must be `""`
   
   </td>
  </tr>
 </tbody>
</table>

*Parameter #4---totalblinder*

(Ignored for now.)

*Result---the unsigned raw transaction in hex*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>string</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The resulting unsigned raw transaction in serialized
   transaction format, encoded as hex.  If the transaction couldn't be
   blinded, this will be set to JSON `null` and the JSON-RPC `error`
   field may contain an error message
   
   </td>
  </tr>
 </tbody>
</table>

*Example*

```bash
## Create a raw transaction
raw_tx = $( elements-cli createrawtransaction '''
  [
    {"txid": "43bd75af773cce38fd190f6c0943d311ce2dd8a26c7e7a9e600c58f8b21e53d4",
     "vout": 1
    }
  ]''' \
  '{"CTEpxPMsN3Ms9PU17u3kdPpYZWos4mmtuFNDzoWxuHrnU6zgTyYkRsgN6fyrTuPvGsLbCNA8JUwtKT24": 3.5}'
)

## Blind raw transaction
elements-cli blindrawtransaction $raw_tx
```

*Result:*

```text
10121667c3dcc51290904a6a9eae27337e6ff5602d0deb5ca501f77be96de63f609010000000014dc938002c2a3cfeab4bda3871b360ec023d6c12735940bff465d596bea068fa7491cc4d61976a91491d4b66f220a4f18ff0f392012afc16ef70318ea88ac0000000001000000000101d4531eb2f8580c609e7a7e6ca2d82dce11d343096c0f19fd38ce3c77af75bd430100000000ffffffff010ac4e620b24efc1b4326360f841a25e974811228292c86e747746f6b713fbb4c6d0816565cd68001ecfe16ea6021eb3a650c77cba52b2b7ad986397a983cc4d8772603219ec94cb8f2d7be5537e78f1a0622862781c46abd52045ea6f341c2fca3769d1976a91491d4b66f220a4f18ff0f392012afc16ef70318ea88ac0000004301000193f238a9fa08e185054ba4f836644648814e2470e6f7f341efb4cddadb60ce7f25812dd5436843c534b0737fb0f49112c229bc7bb32528c6713f9e3bd87853f2fd0c0a601f00000000000000014444fbda22779df29a931ad15e868b619afd272c3646e4b78cdd9abb45f631eadf2a74ced958396883dad43efdcc5348c60fb140a24114295026e98ee9e1f8f0794026e23164e99443311b61d6864f6e26c432bfa15bf77c88febbda3201438bde17350976673e678ae75af161596dd1ae9cd35bba1776a664d07e28521f867bc5370b416292c612d47d53f78abbb2a54a1aac80ca7ed180ce37bf084481249b76520b87367e594efc445d204210c1399ae9493c09b8d2edee7e26ad510082847429754510a7e026707400bad637dd23a5cea18623a51f3d2d984e1a2aa545e6868c998d068c1c62c05dbe7070a18aa618310bc951fc96c9e7fa82ef5bf04c35e5489d773600fccb763f378e7288227d5332b0657e82a7a606a5b5b06340f7249c25edb1cbd9217524a7f43951ad8646ed0e60980aa2b5547200ab17d00a1b36c1e289b983ecc731343175257b8525bd626a7737b0abbaf7944f0f26174e96797f53f4a987212348e824d7eae0944f1d791f04659da5f25d80a2d3915bf36cb1bd887b45381cdf7a2d08dc57290e7c55dcfd7c98671a1ebfb99b4a9746592e49d25f04db8ce6e234fd28aa69bb3c8badf4d3dd0623c1781276c114ae46680d9075112f453779fe206cf0b164bd8d1b369f7078c62f071a8065d07eaa7a09e35a2a3294c063e5ae055ea0d61ccd1cc90bea06d52c688cb6c0018cb84d29552d1426e14c7f0f18d17ce5d8b383971cb6fc0d328aa70c1ed930151449105c6d4268e2fd9b66257f7491260cd1a4590e8a52b87e1c54bd6265664b61ad22854d46e351f2cb49d0e6887b0a6a842aac80a7783c3c8c2276f55826efc81e2adbab4dd27d4121aaed8b2ca76c52132fd0f56580d8b93df56aa048557ff4ee6c4c273418920617e54fc86861054cecf3afd00fcbf8c66cd04b4c0fa78bfee23b7b9530c1887c6368bd2e614fbef3f70996218573ce83da9260bad10132a57c9d7ae5b8e4d0a4b1dd34ba4ab7e06f637c30b8b955eb8a407f0fde4473c40455876233352570b120f9b5d60af5648db86015c9809ca5976a7e42d759fb84d39dd0472e438342102e340e0b5c1b28f70168d972b9a30ff6c681d6b7f2f8c4db91982b9248c680c7a0f8f54aeb82a16936e9592503ff3cdea29582850ad92d03d1d0a679acc0925d9b88460312bf7d984de0c48cceed1f531c4439e16a6c9024ecbac54cada9be03601317d398908e6b7376b95d2d0f9c623fae5033420f4027dab1b64c7607407c53c8a09991a4684702494cb33ecbb0aa21236da49f31512230b8d7473e4c717d4b9f10b6d4157c09186d0cf2ba82bd0e73c9f10a3b9ea97881be0a77da059974cc35509e6b61e9b58b516aeec381468e1ef189cd2f74378bd99b83d71c9daefcae46fc447afce0a54764a9f7c0ee6cb0856586aa09ec3a61eb364aafc9b59958f8aa3ed00390b4fe08e545f4f671b8b768533acea291081d71d5b4e09340ce1b15da59a1bad3c1adb862982ed89e3f4e3694ab2388087130d58ff7c782e6b207175aee7f9d0c2c60606f70f7e45f94b5f58d716ca70299bc357c84da9e37120cb2e045dc87ba44ab04fc78f19cbcfba5e7a8d2ca2fb6e86d617ffbef10e1c12985f8dfa445fd55de467c5a193087831c2a863dd17f0aad15936b703e3cc7c2157d2721a2e59e1b07432bbf69b40d9d1418cc2e72818ec785eeabff1fd0996a4882ac89823d6b9e83abaface5ea27fc6c97754c48e7a2cd7e3a5b30e3279adc73a4740d1a558648dcd81af08c5272b7465006bfa42f68047170777c3abf353cfcf70253393aff3f88c35acfec86ab241ffa5fbb7c500690b8b759d13aea10b256c8686bcce2f3eeff9c5275bb479ca076958b2310e9a76a1082af5528c11a2c89517ce7231d192c71828397596ab78d57ff9e98dc3c1fde8dd8031ceb666f56f41eef057f7b13961eb1ae0f9b56b9aaa3f6df7561e155e828022f55dfc0c8fae1f7cd9630a763828e2ff36f31e8aba8f979c0a22a479a978505e1c5d1c66ba1c8f270cfe8cf055098d7e55040c768d5bcab4e7d6bd02adb0445e90615e296bee4b1f7ce06bdfe56c5183ca4053aedddeea9e662f6ebc9b1dc6772ff89d02411f7edefdbe307cc0f402e285c42e50e93ee63a16368298282d49f1f1ea78af507bba34d2f8688840f47b4bdb04d06686cf00e6be1967917930eb4525fe0b915c24d2983aa9daeed29c114f16ed97447d8df79de5bf338e3795753e679c8e3949b0072551d43e529aebc02b737f2ffb498acb41e8a81f0652994ddd1da1a69f38025a7425be293fd2dc79cb65c25065b4c9bc5cae8fd70ea208fb6c9c43e87089b8ee48fa8c0657bd1db5d75291bb076631bd364fd94d176e5dcd2b4466d65b9f172c0e6838b242612548eac84d8f2a8cc64d2d6508b50cbf26c45bdf9d6290ee7bf027aa79d596e29d14c4a16fb959f5a7a8b67152ea76416ad8cd355e9a20b403737e7ec3c654c86215d6398277a70d20b888d10fa5bd9d34ffb06dec5d305337270e60b6697b674f3b1e342406f6b63e323b47de9b4911e22163d608a6f6427de023271a397da39f4a5ae020e81e7b9cf3f5b540893b6e363e990c203c037ea08e0f809d41c12c841e44f1020c0ba4e0c26ca0d63d18bf23f62bbf99bc047fea1738f0a6aa91e3cfb457d16c742a28db6c897795d181f0c62d5d64eabb62c4dc76b731593383fd93c255ca2396d497ac77289628cd0a00182468b400c07514fe580b4eff38aee03790f2ed0d2fe6e9b2e7f3567d81413aba595edbed8717781b7cf41bb84079ee0079c50a35e08abf31faba75b138ae9db837ae0e59162adfabd99d79788eb9cfd6f919699ae3f814a66aead65bae290303f1d5da2a149317b4fded8a0a1f5771ca4624bf72547887e35e6577713fffd51c3752fbf72beb5f579a7b9a8ec2c81c310d24bf81be8cf4c7ff6a002fc4bce3781b7b43259c4886de306629a4c45b03695ef0ff8369930311f1dfb8e08bd8277885116c9351d52e569ae8a6de196a1eb2f9ddce1141cfc3ebefcb68252f75213132a5d7333edf074ed9b7d0108a508a26ba214e8e6a65d46198140663c2138ac6fe5f61a37c8c18fbb01d9a5dfdb57905510df9904847294cd0530ee89188680dc1e92fc941e518a6fea5ccbed671bfb8ffc9bb10a3608b295a53653491726774f561dc6a6b26dae63b58755bee88dfc8be4bc11952f61129fe973c96018dec13d34a07d189bad414b58995e47b0beda165d6cf9ed10e5dc650b4e2ea82ab0c4d2e7eaa9e323529723a89a191a0678f721aff4477db87bedd9b3f80d3bb6d217ebc34fddd743d5847a1f0240c33976fc4453c35aad07d0b77b0ec7149b450d72464ff4a3cc093e032f02702ae5a6887127e5e0c283826712b528f2e3a0d66259f201b24ad853e0d8c49883696ce273399cddd7424b541fe4d6c871f906e885aab02f4e6a11db659890a1c917120ef1f275d56161632d16b205ebdb4adaf022c1a064a29a1cad449a36367392a1311d78ec33da346ebe43ba8b6c7800a3a3a496015420d9ef08d195e6a8fc699520d5f3bae09b1464095dd2c9865f70b525be5962ed9fd3946ab485e800000000
```
  
## claimpegin

The `claimpegin` RPC claims bitcoins that you deposited to a pegin
address on the main chain.  The mainchain deposit transaction must have
at least 10 confirmations before the claim is valid. On some
sidechains you may need to use a special method not described here to
submit the claim to a functionary in order for it to be mined.

*Parameter #1---the mainchain deposit transaction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Bitcoin transaction</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The hex-encoded serialized transaction from the
   mainchain that pays the peg-in address (script)</td>
  </tr>
 </tbody>
</table>

*Parameter #2---proof that the transaction output exists on the mainchain*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Transaction output proof</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="1">
   
   The proof that the deposit transaction output exists
   on the mainchain.  This can be generated by bitcoind's
   `gettxoutproof` RPC for the deposit transaction
   
   </td>
  </tr>
 </tbody>
</table>

*Result---a txid of the sidechain transaction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The hex-encoded serialized transaction on the sidechain</td>
  </tr>
 </tbody>
</table>

*Example*

```text
elements-cli getpeginaddress
{
  "mainchain_address": "2ND8PB9RrfCaAcjfjP1Y6nAgFd9zWHYX4DN",
  "sidechain_address": "2dhKcR3YFm2kwRQtqtvwbpdpeuXcTv4JJyh"
}


bitcoin-cli sendtoaddress 2ND8PB9RrfCaAcjfjP1Y6nAgFd9zWHYX4DN 10.0
f7c750007586f68c6d0b1a85680ef5662561612b9497128d8a8913e9587878b4 

bitcoin-cli getrawtransaction f7c750007586f68c6d0b1a85680ef5662561612b9497128d8a8913e9587878b4
02000000018d894d59f5385d6b9288b7bd9f24a7adacebdc40b8a924906c2c8aa7f91c4b78010000006a473044022064a9b48f7bc2418e77fad36a8624dd7294873708c4ba28e2352f5db95bb4e828022015e7d7fae4c0364a85353ff233057317cc7b3de1426862814ed822e43c3a976601210387ad2ce2348335d816897e433addfbf29be75345f41379908d7805dab63230a9feffffff0200ca9a3b0000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87a83dd0b2000000001976a914488127463e9ccf113b5d3c00ef11c03b6c01659288ac70000000

bitcoin-cli gettxoutproof '["f7c750007586f68c6d0b1a85680ef5662561612b9497128d8a8913e9587878b4"]'
00000020d16f071ecf5eadf983df0ff5690b249cf0fcfb861aefe6e7a3056bafe6b7ad4cda8f9e4c50251134fee4a6b6d86f84821c1e57cf6d08525ed69840cb57564eb0b9ca4259ffff7f200100000002000000022d70b097e6a2217451cd42d1f4170d8c98f8293d674410afc5cdbe53a9c19058b4787858e913898a8d1297942b61612566f50e68851a0b6d8cf686750050c7f70105

elements-cli claimpegin \
    02000000018d894d59f5385d6b9288b7bd9f24a7adacebdc40b8a924906c2c8aa7f91c4b78010000006a473044022064a9b48f7bc2418e77fad36a8624dd7294873708c4ba28e2352f5db95bb4e828022015e7d7fae4c0364a85353ff233057317cc7b3de1426862814ed822e43c3a976601210387ad2ce2348335d816897e433addfbf29be75345f41379908d7805dab63230a9feffffff0200ca9a3b0000000017a914da1745e9b549bd0bfa1a569971c77eba30cd5a4b87a83dd0b2000000001976a914488127463e9ccf113b5d3c00ef11c03b6c01659288ac70000000 \
    00000020d16f071ecf5eadf983df0ff5690b249cf0fcfb861aefe6e7a3056bafe6b7ad4cda8f9e4c50251134fee4a6b6d86f84821c1e57cf6d08525ed69840cb57564eb0b9ca4259ffff7f200100000002000000022d70b097e6a2217451cd42d1f4170d8c98f8293d674410afc5cdbe53a9c19058b4787858e913898a8d1297942b61612566f50e68851a0b6d8cf686750050c7f70105
```

Result:

```text
f4f30db53238a7529bc51fcda04ea22bd8f8b188622a6488da12281874b71f72
```

## combineblocksigs

The `combineblocksigs` RPC merges signatures into a proposed block,
returning the block with signatures and a field indicating whether the
block has sufficient signatures to be valid.

*Parameter #1---the raw block*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Block</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The hex-encoded block to which signatures should be
   added.  This is the entire block, not just the header</td>
  </tr>
 </tbody>
</table>

*Parameter #2---the signatures to add*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Signatures</td>
   <td>array</td>
   <td>Required<br />(exactly 1)</td>
   <td>An array of signatures to add to the block</td>
  </tr>

  <tr>
   <td>→<br>signature</td>
   <td>string (hex)</td>
   <td>Required<br />(1 or more)</td>
   <td>A signature to add to the block.  The format is a
   hex-encoded scriptSig that satisfies the sidechain's block signing
   conditions</td>
  </tr>
 </tbody>
</table>

*Result---the signed block and whether the block is fully signed*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>object</td>
   <td>Required<br />(exactly 1)</td>
   <td>An object containing the results of the
   operation</td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`hex`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The signed block</td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`complete`
   
   </td>
   <td>bool</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   `true` if the block is fully signed.  Otherwise, `false`
   
   </td>
  </tr>
 </tbody>
</table>

*Example*

```bash
elements-cli combineblocksigs \
    00000020286e091284eda64cf4403cd20b5aec10a4c6acc1827505c8504f374e2987a049f1e69dc0cd67429ef6eabdb893ef3147580296e52608174b7bc2c3b570791f93e8c442590100000047522103302836bd4b66aa62e61a62d151ea3005c7545099effe7d93130070ac445ed8a4210367b9e97a6d294fa509927028824b92bbf655ce89a94f727d9cf05350d998728952ae000101000000010000000000000000000000000000000000000000000000000000000000000000ffffffff03510101ffffffff010121667c3dcc51290904a6a9eae27337e6ff5602d0deb5ca501f77be96de63f60901000000000000000000016a00000000 \
    '''[
        "00473045022100e0f5802829623178d4af1fc494175f3c0086f3051bb9af04277926c092c59b13022032a406fdf596c387337529022c76f20a8bb9e3c8da71f726125a95fb7b711d0e",
        "00473045022100ceee7ea45da250d0ed52dfe96f3a4408c5fb4140b0a8307dc4ed33c9a3178f9302205a4d83d56283e0d34407f00f4ce37f0baa4490c252eb91d734adbce60286c38b"
       ]''' 
```

Result:

```json
{
  "hex": "00000020286e091284eda64cf4403cd20b5aec10a4c6acc1827505c8504f374e2987a049f1e69dc0cd67429ef6eabdb893ef3147580296e52608174b7bc2c3b570791f93e8c442590100000047522103302836bd4b66aa62e61a62d151ea3005c7545099effe7d93130070ac445ed8a4210367b9e97a6d294fa509927028824b92bbf655ce89a94f727d9cf05350d998728952ae9100473045022100e0f5802829623178d4af1fc494175f3c0086f3051bb9af04277926c092c59b13022032a406fdf596c387337529022c76f20a8bb9e3c8da71f726125a95fb7b711d0e473045022100ceee7ea45da250d0ed52dfe96f3a4408c5fb4140b0a8307dc4ed33c9a3178f9302205a4d83d56283e0d34407f00f4ce37f0baa4490c252eb91d734adbce60286c38b0101000000010000000000000000000000000000000000000000000000000000000000000000ffffffff03510101ffffffff010121667c3dcc51290904a6a9eae27337e6ff5602d0deb5ca501f77be96de63f60901000000000000000000016a00000000",
  "complete": true
}
```

## createblindedaddress

The `createblindedaddress` RPC creates a blinded address using a
provided blinding pubkey.  The address is not stored in the wallet.

*Parameter #1---the unblinded address to be blinded*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>address</td>
   <td>string (base58)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The unblinded address to be blinded</td>
  </tr>
 </tbody>
</table>

*Parameter #2---the blinding public key*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>key</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The key to use for the blinding</td>
  </tr>
 </tbody>
</table>

*Result---the blinded address*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>string (base58)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The blinded address</td>
  </tr>
 </tbody>
</table>

*Example*

```bash
elements-cli createblindedaddress \
    HEZk3iQi1jC49bxUriTtynnXgWWWdAYx16 \
    033aafdc9ebc5a3b3c0fa027f6cb23f4cea28a94e161ced75f66f1cf17415b2809
```

*Result:*

```text
AgMsLUciLEiMJo7nS5UzgP8b3VCfviduNZtQjZd4vZ5UR1Xyskxhgb3QUsXyctiYn2i28e6DYqdW4aYY
```

## getblockstats

The `getblockstats` RPC lets you compute per block statistics for a given window.
All amounts are in satoshis. It won't work for some heights with pruning.

*Parameter #1---the block hash or height*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>hash_or_height</td>
   <td>numeric or string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The block hash or height of the target block. If height, negative values 
   count back from the current tip</td>
  </tr>
 </tbody>
</table>

*Parameter #2---the values to plot*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>stats</td>
   <td>array</td>
   <td>optional</td>
   <td>Array of values to plot, by default all values. Array of strings, see
   results for possible values.</td>
  </tr>
 </tbody>
</table>

*Result---the statistics for the given block*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>json object</td>
   <td>A JSON object with all the block statistics.</td>
  </tr>
 </tbody>
</table>

*Example*

```bash
elements-cli getblockstats 1000 '["avgfee", "maxfee", "txs"]'
```

*Result:*

```text
{
  "avgfee": xxxxx,          (numeric) Average fee in the block"
  "avgfeerate": xxxxx,      (numeric) Average feerate (in satoshis per virtual byte)"
  "avgtxsize": xxxxx,       (numeric) Average transaction size"
  "blockhash": xxxxx,       (string) The block hash (to check for potential reorgs)"
  "height": xxxxx,          (numeric) The height of the block"
  "ins": xxxxx,             (numeric) The number of inputs (excluding coinbase)"
  "maxfee": xxxxx,          (numeric) Maximum fee in the block"
  "maxfeerate": xxxxx,      (numeric) Maximum feerate (in satoshis per virtual byte)"
  "maxtxsize": xxxxx,       (numeric) Maximum transaction size"
  "medianfee": xxxxx,       (numeric) Truncated median fee in the block"
  "medianfeerate": xxxxx,   (numeric) Truncated median feerate (in satoshis per virtual byte)"
  "mediantime": xxxxx,      (numeric) The block median time past"
  "mediantxsize": xxxxx,    (numeric) Truncated median transaction size"
  "minfee": xxxxx,          (numeric) Minimum fee in the block"
  "minfeerate": xxxxx,      (numeric) Minimum feerate (in satoshis per virtual byte)"
  "mintxsize": xxxxx,       (numeric) Minimum transaction size"
  "outs": xxxxx,            (numeric) The number of outputs"
  "subsidy": xxxxx,         (numeric) The block subsidy"
  "swtotal_size": xxxxx,    (numeric) Total size of all segwit transactions"
  "swtotal_weight": xxxxx,  (numeric) Total weight of all segwit transactions divided by segwit scale factor (4)"
  "swtxs": xxxxx,           (numeric) The number of segwit transactions"
  "time": xxxxx,            (numeric) The block time"
  "total_out": xxxxx,       (numeric) Total amount in all outputs (excluding coinbase and thus reward [ie subsidy + totalfee])"
  "total_size": xxxxx,      (numeric) Total size of all non-coinbase transactions"
  "total_weight": xxxxx,    (numeric) Total weight of all non-coinbase transactions divided by segwit scale factor (4)"
  "totalfee": xxxxx,        (numeric) The fee total"
  "txs": xxxxx,             (numeric) The number of transactions (excluding coinbase)"
  "utxo_increase": xxxxx,   (numeric) The increase/decrease in the number of unspent outputs"
  "utxo_size_inc": xxxxx    (numeric) The increase/decrease in size for the utxo index (not discounting op_return and similar)"
}
```

## createrawtransaction

The `createrawtransaction` RPC creates an unsigned serialized transaction.
The transaction is not stored in the wallet or transmitted to
the network.

The version in Elements is similar to the Bitcoin Core
[`createrawtransaction` RPC][bcc createrawtransaction] but also allows
the user to create explicit fee outputs using the network's `feeAsset`
and define the outputs' asset type.

Element's API changes are emphasized in bold.

*Parameter #1---Inputs*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Inputs

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An array of objects, each one to be used as an input to the transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → Input

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(1 or more)

   </td>

   <td markdown="span">

   An object describing a particular input

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`txid`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The TXID of the outpoint to be spent encoded as hex in RPC byte order

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`vout`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The output index number (vout) of the outpoint to be spent; the first output in a transaction is index `0`

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`Sequence`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The sequence number to use for the input

   </td>

  </tr>
 </tbody>
</table>


*Parameter #2---addresses and amounts*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Outputs

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The addresses and amounts to pay

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>Address/Amount

   </td>

   <td markdown="span">

   string : number (bitcoins)

   </td>

   <td markdown="span">

   Required<br>(1 or more)

   </td>

   <td markdown="span">

   A key/value pair with the address to pay as a string (key) and the amount to pay that address (value) in bitcoins. Address can be CT or non-CT.

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→<br>`data`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   A key/value pair with the value being hex-encoded data to push into OP_RETURN output.

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→<br>`fee`**

   </td>

   <td markdown="span">

   **number ([value amount][])**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The value of the fee output that you want to add**

   </td>

  </tr>
 </tbody>
</table>


*Parameter #3---locktime*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Locktime

   </td>

   <td markdown="span">

   numeric (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Indicates the earliest time (in block height or Unix epoch time) a transaction can be added to the block chain

   </td>

  </tr>
 </tbody>
</table>


**Parameter #4---pairs of addresses to assets**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **Output assets**

   </td>

   <td markdown="span">

   **object**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **A mapping of output addresses to the asset type to be transferred**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→<br>pairing**

   </td>

   <td markdown="span">

   **string (address) : asset (hex)**

   </td>

   <td markdown="span">

   **Optional<br>(0 or more)**

   </td>

   <td markdown="span">

   **A pairing of the address listed in the Outputs object and the asset to be paid**

   </td>

  </tr>
 </tbody>
</table>


*Result---the unsigned raw transaction in hex*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(Exactly 1)

   </td>

   <td markdown="span">

   The resulting unsigned raw transaction in serialized transaction format, encoded as hex.  If the transaction couldn't be generated, this will be set to JSON `null` and the JSON-RPC error field may contain an error message

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli createrawtransaction '''[
  {
    "txid": "43bd75af773cce38fd190f6c0943d311ce2dd8a26c7e7a9e600c58f8b21e53d4",
    "vout": 1
  }
]''' '''{
  "CTEpxPMsN3Ms9PU17u3kdPpYZWos4mmtuFNDzoWxuHrnU6zgTyYkRsgN6fyrTuPvGsLbCNA8JUwtKT24": 3.5
}'''
```

Result:

```text
0100000001d4531eb2f8580c609e7a7e6ca2d82dce11d343096c0f19fd38ce3c77af75bd430100000000ffffffff010121667c3dcc51290904a6a9eae27337e6ff5602d0deb5ca501f77be96de63f609010000000014dc938002c2a3cfeab4bda3871b360ec023d6c12735940bff465d596bea068fa7491cc4d61976a91491d4b66f220a4f18ff0f392012afc16ef70318ea88ac00000000
```

## decoderawtransaction

The `decoderawtransaction` RPC decodes a hex-encoded serialized transaction
string into a JSON object describing the transaction.

The version in Elements is similar to the Bitcoin Core
[`decoderawtransaction` RPC][bcc decoderawtransaction] but also handles
the additional information available in Elements, such as Confidential
Transactions (CT) and multiple asset types.  Element's API changes are
emphasized in bold.

*Parameter #1---serialized transaction in hex*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Serialized Transaction

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The transaction to decode in serialized transaction format

   </td>

  </tr>
 </tbody>
</table>


*Result---the decoded transaction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An object describing the decoded transaction, or JSON `null` if the transaction could not be decoded

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`txid`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The transaction's TXID, encoded as hex in RPC byte order

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`hash`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The transaction hash.  Differs from txid for witness transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; →<br>`withash`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The witness hash.  May be the same as `hash`**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`size`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The serialized transaction size

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`vsize`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The virtual transaction size.  Differs from size for witness transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`version`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The transaction format version number

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`locktime`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The transaction's locktime: either a Unix epoch date or block height

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`vin`

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An array of objects with each object being an input vector (vin) for this transaction.  Input objects will have the same order within the array as they have in the transaction, so the first input listed will be input 0

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>Input

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(1 or more)

   </td>

   <td markdown="span">

   An object describing one of this transaction's inputs.  May be a regular input or a coinbase

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`txid`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The TXID of the outpoint being spent, encoded as hex in RPC byte order.  Not present if this is a coinbase transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`vout`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The output index number (vout) of the outpoint being spent.  The first output in a transaction has an index of `0`.  Not present if this is a coinbase transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`scriptSig`

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   An object describing the signature script of this input.  Not present if this is a coinbase transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`asm`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The signature script in decoded form with non-data-pushing opcodes listed

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`hex`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The signature script, encoded as hex

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`sequence`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The input sequence number

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`txinwitness`

   </td>

   <td markdown="span">

   string : array

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Hex-encoded witness data. Only for segregated witness transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`vout`

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An array of objects each describing an output vector (vout) for this transaction.  Output objects will have the same order within the array as they have in the transaction, so the first output listed will be output 0

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>Output

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(1 or more)

   </td>

   <td markdown="span">

   An object describing one of this transaction's outputs

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`value`

   </td>

   <td markdown="span">

   number ([value amount][])

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The amount paid to this output.  May be `0`.  **Only returned for unblinded outputs**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`value-minimum`**

   </td>

   <td markdown="span">

   **number ([value amount][])**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The minimum amount paid in this output.  Only returned for blinded outputs**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`value-maximum`**

   </td>

   <td markdown="span">

   **number ([value amount][])**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The maximum amount paid in this output.  Only returned for blinded outputs**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`ct-exponent`**

   </td>

   <td markdown="span">

   **number ([value amount][])**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The exponent used in the blinded output**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`ct-bits`**

   </td>

   <td markdown="span">

   **number (int)**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The number of bits used in the blinded output**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`asset`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The asset identifier, if the asset is unblinded**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`assetcommitment`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The asset tag, if the asset is blinded**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`serValue`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The output's value commitment**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`n`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The output index number of this output within this transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`scriptPubKey`

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An object describing the pubkey script

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`asm`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The pubkey script in decoded form with non-data-pushing opcodes listed

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`hex`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The pubkey script, encoded as hex

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`reqSigs`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The number of signatures required; this is always `1` for P2PK, P2PKH, and P2SH (including P2SH multisig because the redeem script is not available in the pubkey script).  It may be greater than 1 for bare multisig.  This value will not be returned for `nulldata` or `nonstandard` script types (see the `type` key below)

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`type`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The type of script.  This will be one of the following:<br> `pubkey` for a P2PK script<br> `pubkeyhash` for a P2PKH script<br> `scripthash` for a P2SH script<br> `multisig` for a bare multisig script<br> `nulldata` for nulldata scripts<br> `nonstandard` for unknown scripts

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`addresses`

   </td>

   <td markdown="span">

   string : array

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The P2PKH or P2SH addresses used in this transaction, or the computed P2PKH address of any pubkeys in this transaction.  This array will not be returned for `nulldata` or `nonstandard` script types

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → → →<br>Address

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(1 or more)

   </td>

   <td markdown="span">

   A P2PKH or P2SH address

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli decoderawtransaction 01000000000101f4733a0e18ee9d316e95a63cae43f5e8e76bc89df43a4c8cadbe7ee88eed9c383900000000fdffffff030a84e9d4f529885885acb98af9fbe7ca733e79a0e149727d32c4d6b924e63b59f608a5cfa07cd85a4ac50c3f7d50be553d963000e51abcb0f12725f327b944e100fc0336b6f172b57ced0d3a79ca0b8e72c1a2adf2a1ac46842698fa9072f50bb2d16a1976a914724e8a79568e237d1c0d9ab78665a97498d273e788ac0b097d9e48b9c5da0cd83f1ed632771d6388c3aab7cced6610da48e40fa136b44c08b82a8da224cf5afb65e039908b8b7f18b59e740c946cba598490b742d6670abd0209335b1957afa7f82117ea9c4eebf2a2febe8b5fdfc4b105d379f375973310ea1976a914812b108ccae333e235ca9a9a5fc14d436df20d3088ac0121667c3dcc51290904a6a9eae27337e6ff5602d0deb5ca501f77be96de63f609010000000000009a24000000000043010001f6f349c59d84c0ae131b20b0fac44aba1e94c47b1fdf7559e598a8ed183b77e4944634e646aa3970cd39eaf02fcea392e49e1bdcb64af882d3fcf98e47c2f716fd2d0e602c0000000000000001fb84397aea881c1d0f25b9ba20f95796efeabadf496272cd3d59edda575912b316de54e0775890c6aa067ccc7387bb0362c4356d05d0ac91a6731d0b230a02d000fbe1ad31f3a8388b646245a3c12ee96b70f7d324071f1e01d6dd06cb0cfa8f02fcdf90c4aaaad5e78622f01a6f78377b10eb5fcbf035b405343f13c8f3ff0b00d3b02f42623a9da7630b41ddb9254e88933a464939a0606de2c6bf2902815c18e59c222fa7be8db92925f33a07d7ffe05935b74aa93a2cdf258624b7a08b9783a900457dd0ceb721246af3436be79eae671bcaae97596ffeee44259cb30585160750f8baaefa4018339043cda82d45eb1b2d29551939e741c2bbbfba087989843fcf93d6f1996f4fc85c606e41f973093519956b5f3e492a791efb402e2fd9537fcec13cfee2b7fd9b07bbcd0f3be5996588ccde78080dc2615c1959060e0a4ec723e7c768cc3a04173e76169c386ac6991cd251e7b3fbf2bb6279a70061ca1195c5ded7d0fee8f62547a72977966cc20b94959ecacbc587bb12066e872fcdf2556a7a08c41932fe699b0207a45c0b3253a1b832c82a86871f7ac700aa457dc15593cb4abf2c659c24779a9e563bfdbeef2b66c716b898865735a08f1e369344c771253309cfb1f75132ec22047e4eb5629cb34da1c0b485f17c992034539324355abfff27a5b0591378ad5e00c27ec2b0a50c150345ed836921d0ae4d5a90c244bbb281ddee46884bd2d361f6ec98fe1a82f5b6084603a57c1aecf38cfdc8b0e73a42da5569eed37cebe9c8977cbb2d61c19d2b8350bce418a9c2cddbecf11f6bd82adb3d579e6b23201d8297097e6fbd2092ce996a2ec52c5dc7dd2a21aed401fb7d871245a4894984655db0c7ceb949a93455a434961b873ecc5bc0a1bb55ef3203e0f6173b64c9520c5344962aef4b4bcfde231cc8400800b806c9872e743cbf02571166980fea33b9ca7fd39e883437646a9966a6dff7bdcb4bcf571adec9f33f54779a91d56128e67b2e5547df1dae75c33f8d8767ae1a178403762be80f799fb8e61bb8693309f1c0444a1a7bda188853219936cc584c534d06ebecde96c83faf2e8f196143b56884584ca1b57c2ab9341d4736184ce7a403a3920c57a998a9901874c7649a6d6283a6ed245450fc4a8f40270b5fb90fcb6702a214471e80761850cd693f60acd34df760779359fe1ca896f3489cb07be948742ddac9fece398c5c6e1f3ce1e9b244e6a5231a3bb9a71590b5ea3adb13668e87db297e5e880a4aeffa91353b9ef9d28e697b09663c7771031a1b5f1ad04597f508b89e77cd32615155c091fda20c805bb2ae23397b19ff8bcb0361b0a1b89b26d32d13dfcec7487e186f9b1a001ad9c2e5830b28e71c5a6f31e5dce3d66feb77ec1b7827fcab89ae8b769a86a88f16093c534efdf4157886434365d85f584e5a834ecda771f7784502db7ae70107314a41b368f1a64e1bf37362b9a0729b45976168adebcfc2a526bd4096bf64afba7054b3010d1eaf1d9ace69c873964fd307104f877e4cf5ed1522590fd7bf33de5ea36a07d8c78ea5b908edbf30b6a6a957d55bc24ad7cc84f70bca098db989c315e15d1dd7ebb4a4ead8faea95b39bd3f917b9dd295f9c180ca85678887079cc673ca33b99648a2493f5e360f0e1daf1cc29d97a14808c8b9c969ea72f1a7fa3b02035b2390116ea794d4f09460d31e11c30709dc99575055bb4329ddfed0830a7d040838ba49eda4222131abf35824289853913235afbab0544d65882cf46e263a01d091e3b54e78af6b70dadd70cc633e84312fb6c583b3282214d66ee1978e12bd3035cd73ddfc7d83daa2a2de821554e22bf321ff4b906a1431b5291329550f05246d9f166e67089cea9a06cb3373d011afae015f4fd5036c561de5ccac8a08b851414b48342ded208d06bf7f5f1ad945edb7d4cc2401042a0f20656825b8a6ff1399af94cfd9fe16e34e3700c932f0dc701af7845e0d7d7b48a281ebfb6f48387e70a34ddd70d60e37e61ae39345c4831ee3f027d813b44661eeea553a940d98fe1189480773a14b51c1fc7cc774f8deaeb559cdf2e542ac5da5dafbcee5d9fa901466ff9d62eb328887d347208d82828aa5b06be830d47361894dbdf086d537e98f6ecac409f590d97b3f326a35831a43ff84b961da4dad249c6489f91c87cdada117f4fd82da956adc75ad0f301cb7b39637af59ac1430ded867ec7d9341fef56bc342644040a1b3a333c532c0ee3516978140c3a32aed603e6aa0badaa02f58f58524b74998a6d0a53bc9ea7218e8276494dd31b85ef1850a8eac394174d84cada75ee371a9bbab7f1d69bc11ba4ba770201641c48644a75db1f7e79ffc67f6ee32fb5ab3c0dc28bd25a9844f4d036e17eb171292ae0b975d5b4fb72c293f989308441d72129ac11af257a40af433923eaba70283dcb6a4cea792d8f7bab4d26ef54e0d60e8712072ad15f7803ba647968b630c473bf5d42ac8423757242924946d7b4be5e39608549a485b5e2db568c967cc14a5cd2d066b14990a1fe4f0ef4c090d399cab5ab49253dad874cd59c8534989a2a5decdef9234dc29ba506930fdebe490b1dcfbc80008fe6cd6229de1b5f235713dad09769c77ac83eca6b2de697d82a44b554c6177a5a316164547ac4e8773d605a325389cc45937f03eafb4da3f75531cc7076d6b3ebe01b6b3aefb56dec41a0f687ef75359d520e7d0f14993c851b7c25786f26f95ccb657e8aa4448d9e879e079b125a6b89839e346f961ab416d461d8d000b3b577515c1977c90dcf909491560258655dfd103f29e9d1f9c552bd625bf9dd46d3ebc1d38550a1f0787d919a6a8674d38332f275e38e706a6b3a101082829179cc73a75733b17324b1f5f75da34f220912cf40bda90a05991487959afa3c87311c224bbe0eabe3e9f92623ff1f514bfa9fe5ea23dcbd53ba3fc67d3817c64ee6cd97840059ad22bc1dba6cc4d22b56fad44ebd8949da46a72d16f6d7d9e312e72dd81500d361868cd86187dc4b0c8914889d906fbe3eebac45eecc5ac37c76db1a83d906ce0cb14f6b7b606a753a3af64a9a98081b7d9da4710a26b36b5d34946a9b304787f592e1558f38e3499a52805bbb1c26aa62b293c8c61c811e45c2cf1c6ada9e316bd6ca40392b6382d8008fd2837c35a25447497250b9d01489d346d3f2a2c8fe531dde113790c5eec426a25e7703c9d653a902cd08e9fa9723dd93557fb591ff3ac26af2a97c493fa0d0a4a880581be7438b7b7391b8d606d77189d80e47a8c4bb5170f7806a2fa82fd755821d83429f8fdfdca069ba5beffff37539a2bbce7fc88c5e32b08fa1a1f84e2adbbf4c04d42f7338ccd849b22eaae05d8ef4d210971eae196382b363517f4f189e9be00a93832d31e38f82a3a67d54ec02b2a5857308c695e8fa84e1860fb1466457eb6f7cd2229b22ba5a656469a868421676421d65e873c7a3c294fe0716a2b7be7b535f4bd279db44547a5c9963a8e0776beb8b4773dd2a64bf7e57616aa4a570c73dc53cc8df626a10b393c3685f453628ca2a7166b196a8fe64158fdddff94ac1593d2a0726352e4aa00a765782a2d80b5850d9fa1fde22c663ab0fd8c8b0a3fd18d6ee11401b4b2a5ffdd86ca45e7e60829c87a00d77a5bab5292181404c9ecc9e1565d7960736e2bff0accfb196d24a0885170e767335bc2600c0e01f19bb11060d8990fbdba1e823455c1044f168f95df0f16e7b382d3e531eb568ea2613b434e6da8827eb9592d1b9190e7d4122b3c5c38dc6b9aa36ed220b1eb9d652bd9ea5ddd94549b67d1cad292d329460251063524263df92793c3054f710fefad4678c3b008bee771f8aa25300d0c93ed1282f0cd202dda06860b223b34f3c2a82969580ed4adc26167ac27b3ff9d8d41d76d74c93826209fbebf5a3943db88e2d418af639c600bb752bbba0905f5a202bef1a067d8a0e541afc30ff4703844195ae62546340234f956942c8063b5876aeda41f73b7756cec39801c823c6aaab57389d8125099eef340b8a9972bf35a3b6759e4315f7f4b780814e91b18013fd6077e108b1a6b4565c886563e659e8e5ec4e547bd81b424dbc338430d31f55b7dd8a13a09b1a327e6d064719bd36b0e1bca19f6e392a45cad50767ab14088454cfee21caf48d35b9af882532d051a186aeee5fb626f68fdd587358c8c05fc5b513de52b5047215332fbd339d25c59e4c2ebf43ddfadf80ee1cc2fc1471426032dd37e492dc98565a2690f7721d8a6d3bd960808e3a332508481a3809577fd7af6c7f424061772927e2618db2b36bb9915b9949fe2f928290676fd85804a7b6e8728e4c21238a0f8038c8df71af3b8ed7bc0396ec56f3312125f662bd0aa43d13947857a7e8e1f1196060bf99e16bf5659cc84581e13066b5b141561071b94d56d2bae2829f90be1a7a91888eeef2a79869239b36ed76fa343d60647a0e9147d0832902335a5bbd2ace061f751279fe92bbc6622becc362c8502018399259eb308a27841fb7f04447836767829a91daa87b8e9a560f329e66c36ffce6da17e66a793c7d9f2b6b0bb91a3bc1b9b271e06fddbaa46559e215374445de508f1122b3c45b5f2ac8b91e42cb500772506cef6feee69c9053765e02abfbdc3b7f4b1493fe7f62874521a92463e25fe3bb0dc33eac73ea455fd375892c9b802445452e757cf1be01c7e7e17f45b0ad0f70ff05d3282fe6a97fe2a03055ff0ec82524239da584726da036d89b92787f66ff753feec53c2f4fefdd05c2b4591901b313ecfa781ae619b571026dc75e2584a1639c551eb92d39523c84155d77e014cef7f3e4f3250f9611323a0396c5c3e23788125a186c285835277c5ed41dcdf5a4e1a07724e14dabdf1d3a16935caa30bee96ab9b8558f849e9e8954314f3dd385f4f30326ec432e1b290b5db74710b57376475a6eac9e42d5cfb80536af68f485cdddce10309958a07f6be9b28bcb427dc2aeb4d1069784326debaeed03511d615de8f6f22933b590230ceed3abced5c5da33edf6ede33e67b36f25dc98d44be5a30c67ca2e53f1935139326c71d4b9fb42f10175a6ffbdbadceb214943010001f24916ee52163d85af9247e668093bd07ef96fc221012f38961e920fc1d66da9b34130a9db24562de7cbd5b0a8ee83937ac68b7a1773dfc477bacd99a4944ea2fdac0a6021000000000000000156746609e3abeb824e79360ad982b4d36aa8680b336c4f3901520e98f9e6c494f9cf7aacbf9e982904d9928adad9477776fe0da2dadcd7a35e67e4fb171c90148608a9148489867aee8598e09d7299083b45744da445013593fdb9b751531adc6a2cde28c88c5d21349042f8ac2c76535496ac7445965b3ef1d971672ef66676c86244561106d58ed59f7183a48860b91663182ee51161332b07310763e13a465e38eb4dfc0a5d3aa80c56be7b1faa451521da5fe4007bc0c9cc70ed7c7e350a09b8d4b57df14d938f37d7066a7cefa0824b2c52922873af82833f9fbc444bdd64f7fbacb524278f5aa4ea40712c7465d8ebf219dbfb26313c6961d8d6b94b68ee660d79e0e09d07dc7156557de74373229c742522cd726759f1cd6a28b0f44409a1a954da00cb8a6400552e7cad45284528f9615cff7cc4da975400d439a450a767b125c333bf9eb8982a6eb11acaf290bb09cd3bbeaeb46cbe5d20bcca34f7d8ec95f8d06febe203ac385c7fbc278476492c8900bdf8638d19dee5b97b452c96a62fe2cc1c90c2f163c558937e117cca9a7c39d366aa4cff5a9ece70fab569847c553d8e90959a0325a9bc93a8e38c76d200eb4453a6ca458fe64e238037b116b9741570d9ad052823d016022f21b24e14c98210496207b8fe5438f9776287a95e0cefc22502c91bb700656ea4e894ad37001dee2b8890e68b5a19e6fdf53edc8ac34cfc35bac68b09e7dcb9e0dac8a308a4c8ff495fbf13ebc20044334eae8a85557081f4f0f18e68e2ee23aec51315dbb23b344c088b58f3535e9dd28e34a9e3204833488fffa33ba67b48d89afd164eae0563b41bb39b5bcf14d58e2e803379aec4777b3e0b848000d1b4b96c169db5d3f5225db8839e29e2d1860dc327c6719d69b2e822c76ad313ff4afa3f4ee4f318d2de2cf9ca146667a0b48615a227933ce021f4cbca9966cef7c6c123e66f3ddb035dc36f5530efde1e781eaa0fc5607b6ba3001cda948461ff0b20967479c64b2420ff2c89f3cbaca89b58ee0336f246195d69aef521aeeae64bdcd2d16f8f2978a76a21e2db033853f21916337f0915325b4381fe4f16d5a968f9a8a07deb34777623d91f8cedd689515c3567cb7d6efb12a237120510813744bfa4c3b69df9b439d03b380ab0c88cc6b930d3ac1de01c390173723c828e9ec9e4669571df81cfe6e2168001af0ab9c0b8db7fe50636870abd11666f6aea07d82f7bb7834cd20b2f1af7d24627774e004cd342c4f3d8a9b511efd3dcd2347339b067cd4f8a1c8c8b78b8d4bb32e3b0bccf8b0fed69c67a2bd969f45d0c1c5fbf0161bf5ebb2919703defc3f6c7609698e72c7f43e77f786148e05fb84951e00ba184f9a3dba686557d16feea0e9e87c06ac3dc50fc6bbf5e4e94f15a0e3d98b64d84cb5a7d82c9d17f37829ef805a200952558ec3e7db18721bea6a4a4a8814d342fb1cf2c25aad4c8f4c227e0320c34f16f542f475b9f52fabe241f05c7a0c735fc297b50675f301963d62b95dab019b774cb5d340f57b951c3ed93ae7dec4f890608c75f39ba9114d53ed7d74809752f234343ed6650bfc1240426356c5913114ffd61f7b6e7e42b7176215f7322fe5462f09120638bf253607fe4866e5e288eac5c24bde654d3e72927dd2b12022ed974d4b5b5f98e4b68960095d3e5b2a726e21bcdabf15aba44b97934af0685384505c750432b3cdeec888d80e5d1a8dcdfa24d1a04c6cf01d46fd512d45e1cf0ca0f8e923ca6918fb04c23908bb4a84146bfe220e6e7302cdf732cd04c3dafae19abd4c70f938482ba1f65fd6830365e636cf15f94aacfecacaca6267718c12011968041913eee011565167d7587aabe2e8ef33ef567e9eecacda34bd510d45ed4630c5396ad7fc75cd82aaee14fe67c57a5b9d6c934bed9ec4e405ebb9e165fc1ece81af23aff05c7fcd79cd90c40a53e2aaf44d63a00ca32c77dc6b1cb1acb70d0d0b84161636e1be9f71d3838b81fa71ceb48476fd7823a642f23bc61c18f69d8db5f27918eca468c00a01dfbc6b66f547fb6d0ecfc6713686c5b66736a4320105111e655290da10f2525da1a826bbc12482dcecd2be0155662400e4e39ac1e60e7a5f0d867bd5f1e7a01e8d2cc87c7ce1528e71f9131c768ce2dc94414f27be8556fc120174e5c25fa728d00a86de4ee57dbe0ae5cea24af31fe5379852048562dabe55132ef64bd8163146213721d21afd0274fd5509b8d6d8d6e384bf965b9e6c6ef94a939798b47b4f17a272f4c866dd5dcd8648143f7a3c0e0bb2fd585c8705cd82c9ecf9de5efd394418c767f4c23b77a59a3cdf440831ba926b054d721d16d6c67876606a4c0cca355a3046641e9615a5b0be540329598e6c968f07a00e6174db53758d367165864f21fd55a28c3fc2b35172ea3cefa260a5621113f63a0352adf6eeacc8eac0b85ff9067f53f89406649b678b4596af28057749bdda873313791b88ffcd44f8413a72dbddb61aada0df3fb5387515329bf80a8b1260e5e60b7cca6ddd91111b31397afdb64359643797c4985157798bf061ca1a0b66706b8ae84c75a1ed904b348b5d0c5c99fb1421ae6714ce02ad164dc0cef7680356913f1ee2ef4420da5fc0f4da6ea93a74592e475004c1d7f9a2219039b376c31f605b77e5d6306f0ec7ae4c220bf95251fb40c1ae7a81b8d006c9b23cc3607cf7c0ed9448c759ea565ae0e5a5c261d44660eab877ea57be8a5f493b8c7328b35de05902462c6b15899eb09f68654db730d4ddd9521d9b45a1a0f899e86857cfaa0aaa2e665ab33efa867781a889c334f92c44b9e4a069952ba5496bcd62fcaca67e1046bdb3a792dbd7107069e77a64ea38782925040e76332ae88511020521f8ed1efe247994e362e9494cadb9d90f02bb80b39a2ee1a96685a27859d832199e3f878e2264a19c868847a276f2ad3c23dc766406295cf1659f4ec532e7a47741b6c95c704ea97a8cf96aa7ec9c2e17f191c0a29e2e331ede5180f00de09dae0f8c900f8d42a936b6ec83c471f38e7e993dc316ca02547a07b6b799f8ca08b545d8623064aa54bb82f0cdd24cb40fd320b5509cbd4405d760b22f7b2b49de82e200aa13930582d1f5e407fe6427013050ccda20d859a046da24e125269d120c8c8128adbd3e0327fc210fb2f7051806fc9f3c2d2db6944ca092df6313774bb677c4149d4784fc60e763d4fcec80202c37e50884d2184cd43536405f455daa096187126e4ad7a42b2b77dec2feba0e784cfffed557dbce053e42095e19122f57980ddd29319bdf35df8ba95f2c10427a42522c326789db6ed73478e5269bec7037474e55e79a71c64325b326e2bd8ae3a60e193cdc8faf18edf5c27c91181c7ba53ef26c9072a08122a5937f8d2e705ad469f7af36dfd1a4b5e71f364df862aaf55372f37ded47461f1a88a31504db3db2c05ed738559f80c7bc6caa867d8bae912e7410f2caa1cd6c4232036b2e409b4a0188134b86264a263352d8f089a6e1efab156f9f230f9e37807e9580278519829231f82c09b096366a8c865f599b9526b33e90f0ffccf0a7a9a3e7f5b6a0262bfd9aa20e9197dab0eec63a5eb25db2a76cde3e4ca6de50b52be40d75be8bd7b0b7733502f799a10475ce103b1c6197bdc1793fbadfde2cadb9e7870d305683b27f29215351919a1891514a90860223c2323dec811ffea95a58c66c6729bdb7f83f24b214a23038bf00ef58d6a84c1b52e5c6b355060a41f275248c9059e062fc959c6a605ad7af37486d22e480a403e3ba08c54f0e26eb9f9bb73f9241cdfd414efaa766c0e0a8cd21e530927722678a729da00003a000000
```

Result:

```json
{
  "txid": "f4f30db53238a7529bc51fcda04ea22bd8f8b188622a6488da12281874b71f72",
  "hash": "de1d75703f06a379d4e7a4286ac4049b1455463c79d0aff7c1d48718a2702486",
  "withash": "a7c367d101036b25a9bd3301fb7f299b2fe2b2454896a38b45ebf5aa2274b6fd",
  "size": 6855,
  "vsize": 1973,
  "version": 1,
  "locktime": 58,
  "vin": [
    {
      "txid": "389ced8ee87ebead8c4c3af49dc86be7e8f543ae3ca6956e319dee180e3a73f4",
      "vout": 57,
      "scriptSig": {
        "asm": "",
        "hex": ""
      },
      "sequence": 4294967293
    }
  ],
  "vout": [
    {
      "value-minimum": 0.00000001,
      "value-maximum": 351843.72088832,
      "ct-exponent": 0,
      "ct-bits": 45,
      "assetcommitment": "0a84e9d4f529885885acb98af9fbe7ca733e79a0e149727d32c4d6b924e63b59f6",
      "serValue": "08a5cfa07cd85a4ac50c3f7d50be553d963000e51abcb0f12725f327b944e100fc",
      "n": 0,
      "scriptPubKey": {
        "asm": "OP_DUP OP_HASH160 724e8a79568e237d1c0d9ab78665a97498d273e7 OP_EQUALVERIFY OP_CHECKSIG",
        "hex": "76a914724e8a79568e237d1c0d9ab78665a97498d273e788ac",
        "reqSigs": 1,
        "type": "pubkeyhash",
        "addresses": [
          "2djr9WWJ7GjF7Pc1syTjg5z3o883EYe4prc"
        ]
      }
    }, 
    {
      "value-minimum": 0.00000001,
      "value-maximum": 171.79869184,
      "ct-exponent": 0,
      "ct-bits": 34,
      "assetcommitment": "0b097d9e48b9c5da0cd83f1ed632771d6388c3aab7cced6610da48e40fa136b44c",
      "serValue": "08b82a8da224cf5afb65e039908b8b7f18b59e740c946cba598490b742d6670abd",
      "n": 1,
      "scriptPubKey": {
        "asm": "OP_DUP OP_HASH160 812b108ccae333e235ca9a9a5fc14d436df20d30 OP_EQUALVERIFY OP_CHECKSIG",
        "hex": "76a914812b108ccae333e235ca9a9a5fc14d436df20d3088ac",
        "reqSigs": 1,
        "type": "pubkeyhash",
        "addresses": [
          "2dmCj9T1PZ2osmWDjsaFsaoToCK2wyGkscT"
        ]
      }
    }, 
    {
      "value": 0.00039460,
      "asset": "09f663de96be771f50cab5ded00256ffe63773e2eaa9a604092951cc3d7c6621",
      "serValue": "010000000000009a24",
      "n": 2,
      "scriptPubKey": {
        "asm": "",
        "hex": "",
        "type": "fee"
      }
    }
  ]
}
```

## destroyamount

The `destroyamount` RPC creates and broadcasts a transaction from your
wallet that destroys the specified amount of the specified asset.  Your
wallet must contain at least the amount of the asset to be destroyed.

*Parameter #1---the asset identifier or label*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>asset</td>
   <td>string</td>
   <td>Required<br />(exactly 1)</td>
   <td>The hexadecimal asset identifier or the asset's label</td>
  </tr>
 </tbody>
</table>

*Parameter #2---the amount to destroy*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>amount</td>
   <td markdown="block">
   
   [value amount][]
   
   </td>
   <td>Required<br />(exactly 1)</td>
   <td>The amount to be destroyed in its normal denomination, which is
   100 millions greater than the minimum unit.  For example, Bitcoin's
   normal unit is a bitcoin and its minimum unit is 0.00000001 bitcoins</td>
  </tr>
 </tbody>
</table>

*Parameter #3---an optional comment*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>comment</td>
   <td>string</td>
   <td>Optional<br />(0 or 1)</td>
   <td>A comment to associate with this transaction in your
   wallet.  This is only part of your wallet; it does not become part of
   the transaction</td>
  </tr>
 </tbody>
</table>

*Result---the transaction identifier*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="1">
   
   `result`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The transaction identifier</td>
  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli destroyamount "bitcoin" 100 "destroy some test bitcoins"
```

Result:

```text
12a6251b3ac7e29edf2ec8483690a21a896392c812192cc1c7a8659c76164ca3
```

## dumpassetlabels

The `dumpassetlabels` RPC returns a list of all asset labels used by the
current daemon.  These labels may then be added to another daemon's
configuration using the `assetdir` confirmation parameter.

*No parameters*

*Result*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>object</td>
   <td>Required<br />(exactly 1)</td>
   <td>The results of the dump.</td>
  </tr>

  <tr>
   <td>→<br>label</td>
   <td>string : string (hex)</td>
   <td>Optional<br />(0 or more)</td>
   <td>The asset label in Unicode paired with the asset identifier
   in hex</td>
  </tr>
 </tbody>
</table>

*Example*

```bash
elements-cli dumpassetlabels
```

Result:

```json
{
  "bitcoin": "09f663de96be771f50cab5ded00256ffe63773e2eaa9a604092951cc3d7c6621",
  "foocoin": "2cc6ef8dc6d1078e03537b5880833bca0232cefae094db1663ddeea877a7f209"
}
```

To add the "foocoin" label to another Elements instance, add the
following line to your configuration file:

```text
assetdir=2cc6ef8dc6d1078e03537b5880833bca0232cefae094db1663ddeea877a7f209:foocoin
```

The "bitcoin" label is hard coded and does not need to be added to your
configuration file.

## dumpblindingkey

The `dumpblindingkey` RPC returns the private blinding key for a
Confidential Transactions (CT) address.

*Parameter #1---the address of the key to return*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>address</td>
   <td>string (base58)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The public CT address corresponding to the private blinding key to retrun.</td>
  </tr>
 </tbody>
</table>

*Result---a private blinding key*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>key</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The private blinding key</td>
  </tr>
 </tbody>
</table>

*Example*

```bash
address=$( elements-cli getnewaddress )
elements-cli dumpblindingkey $address
```

Result:

```text
31b4a0fec3b04514ce26e1cd3af1aaa65bd66e48853b5eb9f9966dcfdd907d2d
```

## dumpissuanceblindingkey

The `dumpissuanceblindingkey` RPC returns the private blinding key for a
previous asset issuance stored in the wallet.

*Parameter #1---the issuance's txid*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>txid</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The txid of the issuance transaction</td>
  </tr>
 </tbody>
</table>

*Parameter #2---the input index (vin) of the asset issuance*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>vin</td>
   <td>number (int)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   Within the asset issuance transaction, this is the
   input index number (vin), with the first input being `0`
   
   </td>
  </tr>
 </tbody>
</table>

*Result---the blinding key*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>key</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The private blinding key</td>
  </tr>
 </tbody>
</table>

*Example*

First, issue an asset:

```bash
elements-cli issueasset 1 1
```

Result

```json
{
  "txid": "62b92d6da48c774009300e591b771c4de8341f811fc84608c6df385d72b3796e",
  "vin": 0,
  "entropy": "75357f93a362771da206115cd4266f01d6b93996c059ac24b1ee609e222946d8",
  "asset": "af71af0ca4eaa64c326ea80fd8e3f550191193793d21a735f9df79cb3ac9181a",
  "token": "b07eb656d11e823351f7e2d7eb90d5f1876fa46af8b0c9dfee0b2e92f4fe6d3a"
}
```

Then, dump its blinding key:

```bash
elements-cli dumpissuanceblindingkey 62b92d6da48c774009300e591b771c4de8341f811fc84608c6df385d72b3796e 0
```

Result:

```text
b5f50dcc0ae9c4d2d7c5062b1e5b9dd76dffc136c33daf7a789c18c8cc219e3e
```

## getbalance

The `getbalance` RPC gets the balance for each of your assets across all
accounts or for a particular account.

The version in Elements is similar to the Bitcoin Core [`getbalance`
RPC][bcc getbalance] but handles multiple asset types instead of just
bitcoins.  Note that it shows reissuance tokens as their own assets.
Element's API changes are emphasized in bold.

*Parameter #1---an account name*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Account

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The name of an account to get the balance for.  An empty string ("") is the default account.  The string `*` will get the balance for all accounts (this is the default behavior)

   </td>

  </tr>
 </tbody>
</table>


*Parameter #2---the minimum number of confirmations*


<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Confirmations

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The minimum number of confirmations an externally-generated transaction must have before it is counted towards the balance.  Transactions generated by this node are counted immediately.  Typically, externally-generated transactions are payments to this wallet and transactions generated by this node are payments to other wallets.  Use `0` to count unconfirmed transactions.  Default is `1`

   </td>

  </tr>
 </tbody>
</table>



*Parameter #3---whether to include watch-only addresses*


<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Include Watch-Only

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If set to `true`, include watch-only addresses in details and calculations as if they were regular addresses belonging to the wallet.  If set to `false` (the default), treat watch-only addresses as if they didn't belong to this wallet

   </td>

  </tr>
 </tbody>
</table>



**Parameter #4---asset identifier**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **Asset identifier**

   </td>

   <td markdown="span">

   **string**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The asset identifier or label of the asset to return.  If this is used, the account argument is ignored.  Note that this also changes the output from a JSON object to a number**

   </td>

  </tr>
 </tbody>
</table>


*Result---the balances*

**If the fourth parameter (asset identifier) is not set, this is a JSON
object:**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **`result`**

   </td>

   <td markdown="span">

   **object**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **An object holding pairs of asset ids and balance amounts**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→<br>amount**

   </td>

   <td markdown="span">

   **string : [value amount][]**

   </td>

   <td markdown="span">

   **Required<br>(1 or more)**

   </td>

   <td markdown="span">

   **An asset identifier or label paired with the balance of that asset.  At a minimum, the `bitcoin` asset will be returned**

   </td>

  </tr>
 </tbody>
</table>


If the fourth parameter (asset identifier) is set, this is a [value
amount][] of that asset's balance:

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   number ([value amount][])

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   **The balance of all accounts in the requested asset**

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli getbalance
```

Result:

```json
{
  "bitcoin": 20999999.99877720,
  "foocoin": 100.00000000,
  "d5fe63f77038c6e3cbd70139b5d30b9c0e885dbbfc916ebb442f9dd367c5c0fb": 1.00000000
}
```

## getnewblockhex

The `getnewblockhex` RPC returns a new proposed (not mined) block.  This block
can then be signed or otherwise processed.

*No parameters*

*Results*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>A hex-encoded serialized block ready to be added to the
   block chain.  It will contain any transactions in the local node's
   memory pool</td>
  </tr>
 </tbody>
</table>

*Example*

```bash
elements-cli getnewblockhex
```

Result:

```text
000000303403aa7551622abfb2338369a553704196e7bd63e6091efe5e370fd52b19647104acd6e9834b7340a9d567bf42b12583076aa409e22f8901548a8ae17945f63ad7e13e59cf0000000151000101000000010000000000000000000000000000000000000000000000000000000000000000ffffffff0502cf000101ffffffff010121667c3dcc51290904a6a9eae27337e6ff5602d0deb5ca501f77be96de63f60901000000000000000000016a00000000
```

## getpeginaddress

The `getpeginaddress` RPC returns two addresses, one for the mainchain
and one for the sidechain; bitcoins sent to the mainchain address may be
claimed using the sidechain address.

*Argument 1---an optional account*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>account</td>
   <td>string</td>
   <td>Optional<br />(0 or 1)</td>
   <td markdown="block">
   
   An account into which the sidechain address should
   be placed.  If no account is provided, the default account (`""`) is
   used.
   
   </td>
  </tr>
 </tbody>
</table>

*Result---an object containing the mainchain and sidechain addresses*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>object</td>
   <td>Required<br />(exactly 1)</td>
   <td>An object containing the mainchain and sidechain addresses</td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`mainchain_address`
   
   </td>
   <td>string (base58)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The address to pay on the mainchain </td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`sidechain_address`
   
   </td>
   <td>string (base58)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The address on the sidechain which will receive the funds sent by `claimpegin`
   
   </td>
  </tr>
 </tbody>
</table>

*Example*

```bash
elements-cli getpeginaddress
```

Result:

```json
{
  "mainchain_address": "2ND8PB9RrfCaAcjfjP1Y6nAgFd9zWHYX4DN",
  "sidechain_address": "2dfbnY6UamxvDDygrAJ6b77Jq6SjCGUeS6q"
}
```

## getrawtransaction

The `getrawtransaction` RPC gets a hex-encoded serialized transaction or
a JSON object describing the transaction. By default, Elements only
stores complete transaction data for UTXOs and your own transactions, so
the RPC may fail on historic transactions unless you use the non-default
`txindex=1` in your startup settings.

Note: if you begin using `txindex=1` after downloading the block chain, you must rebuild your indexes by starting your node with the option  `-reindex`.  This may take quite some time to complete, during which time your node will not process new blocks or transactions. This reindex only needs to be done once.

The version in Elements is similar to the Bitcoin Core
[`getrawtransaction` RPC][bcc getrawtransaction] but also prints
additional information specific to elements, such as Confidential
Transaction (CT) outputs, multiple asset types, and the extra Elements
Script opcodes.
Element's API changes are emphasized in bold.

*Parameter #1---the TXID of the transaction to get*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   TXID

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The TXID of the transaction to get, encoded as hex in RPC byte order

   </td>

  </tr>
 </tbody>
</table>


*Parameter #2---whether to get the serialized or decoded transaction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Format

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Set to `false` (the default) to return the serialized transaction as hex.  Set to `true` to return a decoded transaction as a JSON object.  Before 0.14.0, use `0` and `1`, respectively

   </td>

  </tr>
 </tbody>
</table>


*Result (if transaction not found)---`null`*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   null

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   If the transaction wasn't found, the result will be JSON `null`.  This can occur because the transaction doesn't exist in the block chain or memory pool, or because it isn't part of the transaction index.  See the Bitcoin Core `-help` entry for `-txindex`

   </td>

  </tr>
 </tbody>
</table>


*Result (if verbose=`false`)---the serialized transaction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   If the transaction was found, this will be the serialized transaction, encoded as hex

   </td>

  </tr>
 </tbody>
</table>


*Result (if verbose=`true`)---the decoded transaction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   If the transaction was found, this will be an object describing it

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`hex`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The serialized, hex-encoded data for the provided `txid`

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`txid`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The transaction's TXID, encoded as hex in RPC byte order

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`hash`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The transaction hash.  Differs from txid for witness transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; →<br>`withash`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The witness hash.  May be the same as `hash`**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`size`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The serialized transaction size

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`vsize`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The virtual transaction size.  Differs from size for witness transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`version`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The transaction format version number

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`locktime`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The transaction's locktime: either a Unix epoch date or block height

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`vin`

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An array of objects with each object being an input vector (vin) for this transaction.  Input objects will have the same order within the array as they have in the transaction, so the first input listed will be input 0

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>Input

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(1 or more)

   </td>

   <td markdown="span">

   An object describing one of this transaction's inputs.  May be a regular input or a coinbase

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`txid`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The TXID of the outpoint being spent, encoded as hex in RPC byte order.  Not present if this is a coinbase transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`vout`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The output index number (vout) of the outpoint being spent.  The first output in a transaction has an index of `0`.  Not present if this is a coinbase transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`scriptSig`

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   An object describing the signature script of this input.  Not present if this is a coinbase transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`asm`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The signature script in decoded form with non-data-pushing opcodes listed

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`hex`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The signature script, encoded as hex

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`sequence`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The input sequence number

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`txinwitness`

   </td>

   <td markdown="span">

   string : array

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Hex-encoded witness data. Only for segregated witness transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`vout`

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An array of objects each describing an output vector (vout) for this transaction.  Output objects will have the same order within the array as they have in the transaction, so the first output listed will be output 0

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>Output

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(1 or more)

   </td>

   <td markdown="span">

   An object describing one of this transaction's outputs

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`value`

   </td>

   <td markdown="span">

   number ([value amount][])

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The amount paid to this output.  May be `0`.  **Only returned for unblinded outputs**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`value-minimum`**

   </td>

   <td markdown="span">

   **number ([value amount][])**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The minimum amount paid in this output.  Only returned for blinded outputs**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`value-maximum`**

   </td>

   <td markdown="span">

   **number ([value amount][])**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The maximum amount paid in this output.  Only returned for blinded outputs**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`ct-exponent`**

   </td>

   <td markdown="span">

   **number ([value amount][])**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The exponent used in the blinded output**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`ct-bits`**

   </td>

   <td markdown="span">

   **number (int)**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The number of bits used in the blinded output**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`asset`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The asset identifier, if the asset is unblinded**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`assetcommitment`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The asset tag, if the asset is blinded**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **&#8203; → → →<br>`serValue`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The output's value commitment**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`n`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The output index number of this output within this transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>`scriptPubKey`

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An object describing the pubkey script

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`asm`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The pubkey script in decoded form with non-data-pushing opcodes listed

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`hex`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The pubkey script, encoded as hex

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`reqSigs`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The number of signatures required; this is always `1` for P2PK, P2PKH, and P2SH (including P2SH multisig because the redeem script is not available in the pubkey script).  It may be greater than 1 for bare multisig.  This value will not be returned for `nulldata` or `nonstandard` script types (see the `type` key below)

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`type`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The type of script.  This will be one of the following:<br> `pubkey` for a P2PK script<br> `pubkeyhash` for a P2PKH script<br> `scripthash` for a P2SH script<br> `multisig` for a bare multisig script<br> `nulldata` for nulldata scripts<br> `nonstandard` for unknown scripts

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → →<br>`addresses`

   </td>

   <td markdown="span">

   string : array

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The P2PKH or P2SH addresses used in this transaction, or the computed P2PKH address of any pubkeys in this transaction.  This array will not be returned for `nulldata` or `nonstandard` script types

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → → → →<br>Address

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(1 or more)

   </td>

   <td markdown="span">

   A P2PKH or P2SH address

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`blockhash`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If the transaction has been included in a block on the local best block chain, this is the hash of that block encoded as hex in RPC byte order

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`confirmations`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   If the transaction has been included in a block on the local best block chain, this is how many confirmations it has.  Otherwise, this is `0`

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`time`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If the transaction has been included in a block on the local best block chain, this is the block header time of that block (may be in the future)

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`blocktime`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   This field is currently identical to the time field described above

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli getrawtransaction f4f30db53238a7529bc51fcda04ea22bd8f8b188622a6488da12281874b71f72 1
```

Result:

```json
{
  "hex": "01000000000101[...]00003a000000",
  "txid": "f4f30db53238a7529bc51fcda04ea22bd8f8b188622a6488da12281874b71f72",
  "hash": "de1d75703f06a379d4e7a4286ac4049b1455463c79d0aff7c1d48718a2702486",
  "withash": "a7c367d101036b25a9bd3301fb7f299b2fe2b2454896a38b45ebf5aa2274b6fd",
  "size": 6855,
  "vsize": 1973,
  "version": 1,
  "locktime": 58,
  "vin": [
    {
      "txid": "389ced8ee87ebead8c4c3af49dc86be7e8f543ae3ca6956e319dee180e3a73f4",
      "vout": 57,
      "scriptSig": {
        "asm": "",
        "hex": ""
      },
      "sequence": 4294967293
    }
  ],
  "vout": [
    {
      "value-minimum": 0.00000001,
      "value-maximum": 351843.72088832,
      "ct-exponent": 0,
      "ct-bits": 45,
      "assetcommitment": "0a84e9d4f529885885acb98af9fbe7ca733e79a0e149727d32c4d6b924e63b59f6",
      "serValue": "08a5cfa07cd85a4ac50c3f7d50be553d963000e51abcb0f12725f327b944e100fc",
      "n": 0,
      "scriptPubKey": {
        "asm": "OP_DUP OP_HASH160 724e8a79568e237d1c0d9ab78665a97498d273e7 OP_EQUALVERIFY OP_CHECKSIG",
        "hex": "76a914724e8a79568e237d1c0d9ab78665a97498d273e788ac",
        "reqSigs": 1,
        "type": "pubkeyhash",
        "addresses": [
          "2djr9WWJ7GjF7Pc1syTjg5z3o883EYe4prc"
        ]
      }
    }, 
    {
      "value-minimum": 0.00000001,
      "value-maximum": 171.79869184,
      "ct-exponent": 0,
      "ct-bits": 34,
      "assetcommitment": "0b097d9e48b9c5da0cd83f1ed632771d6388c3aab7cced6610da48e40fa136b44c",
      "serValue": "08b82a8da224cf5afb65e039908b8b7f18b59e740c946cba598490b742d6670abd",
      "n": 1,
      "scriptPubKey": {
        "asm": "OP_DUP OP_HASH160 812b108ccae333e235ca9a9a5fc14d436df20d30 OP_EQUALVERIFY OP_CHECKSIG",
        "hex": "76a914812b108ccae333e235ca9a9a5fc14d436df20d3088ac",
        "reqSigs": 1,
        "type": "pubkeyhash",
        "addresses": [
          "2dmCj9T1PZ2osmWDjsaFsaoToCK2wyGkscT"
        ]
      }
    }, 
    {
      "value": 0.00039460,
      "asset": "09f663de96be771f50cab5ded00256ffe63773e2eaa9a604092951cc3d7c6621",
      "serValue": "010000000000009a24",
      "n": 2,
      "scriptPubKey": {
        "asm": "",
        "hex": "",
        "type": "fee"
      }
    }
  ],
  "blockhash": "5c81a92979fdc82a40d0aa8c1e39976a4fdcd890bf864794243052aae4ddb514",
  "confirmations": 2,
  "time": 1497552832,
  "blocktime": 1497552832
}
```

## gettransaction

The `gettransaction` RPC provides detailed information about an in-wallet
transaction.

The version in Elements is similar to the Bitcoin Core [`gettransaction`
RPC][bcc gettransaction] but also prints extra information about
Elements transactions, such as what asset types it includes besides
bitcoin and whether it uses Confidential Transactions (CT).
Element's API changes are emphasized in bold.

*Parameter #1---a transaction identifier (TXID)*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   TXID

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The TXID of the transaction to get details about.  The TXID must be encoded as hex in RPC byte order

   </td>

  </tr>
 </tbody>
</table>


*Parameter #2---whether to include watch-only addresses in details and calculations*


<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Include Watch-Only

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If set to `true`, include watch-only addresses in details and calculations as if they were regular addresses belonging to the wallet.  If set to `false` (the default), treat watch-only addresses as if they didn't belong to this wallet

   </td>

  </tr>
 </tbody>
</table>



**Parameter #3---asset identifier**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **Asset identifier**

   </td>

   <td markdown="span">

   **string**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **An asset identifier or label to restrict the `amount` field in the results to that particular asset**

   </td>

  </tr>
 </tbody>
</table>


*Result---a description of the transaction*


























<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An object describing how the transaction affects the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`amount`

   </td>

   <td markdown="span">

   **object or number**

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   **If parameter #3 is specified, this is a positive number if this transaction increased the total wallet balance of that asset; a negative number if this transaction decreased the total wallet balance of that asset, or `0` if the transaction had no net effect on wallet balance of that asset.  If Parameter #3 was not specified, this is a JSON object containing pairs of asset names and balance change amounts as described in the previous sentence.**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`fee`

   </td>

   <td markdown="span">

   number (bitcoins)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If an outgoing transaction, this is the fee paid by the transaction, reported as negative bitcoins

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`confirmations`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The number of confirmations the transaction has received.  Will be `0` for unconfirmed and `-1` for conflicted

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`generated`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Set to `true` if the transaction is a coinbase.  Not returned for regular transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`blockhash`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The hash of the block on the local best block chain that includes this transaction, encoded as hex in RPC byte order.  Only returned for confirmed transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`blockindex`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The index of the transaction in the block that includes it.  Only returned for confirmed transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`blocktime`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The block header time (Unix epoch time) of the block on the local best block chain that includes this transaction.  Only returned for confirmed transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`txid`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The TXID of the transaction, encoded as hex in RPC byte order

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`walletconflicts`

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An array containing the TXIDs of other transactions that spend the same inputs (UTXOs) as this transaction.  Array may be empty

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>TXID

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Optional<br>(0 or more)

   </td>

   <td markdown="span">

   The TXID of a conflicting transaction, encoded as hex in RPC byte order

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`time`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   A Unix epoch time when the transaction was added to the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`timereceived`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   A Unix epoch time when the transaction was detected by the local node, or the time of the block on the local best block chain that included the transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`bip125-replaceable`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   Indicates if a transaction is replaceable under BIP 125:<br> `yes` is replaceable<br> `no` not replaceable<br> `unknown` for unconfirmed transactions not in the mempool

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`comment`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   For transaction originating with this wallet, a locally-stored comment added to the transaction.  Only returned if a comment was added

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → <br>`to`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   For transaction originating with this wallet, a locally-stored comment added to the transaction identifying who the transaction was sent to.  Only returned if a comment-to was added

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`details`

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An array containing one object for each input or output in the transaction that affected the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → <br>`involvesWatchonly`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Set to `true` if the input or output involves a watch-only address.  Otherwise not returned

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`account`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The account which the payment was credited to or debited from.  May be an empty string ("") for the default account

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`address`

   </td>

   <td markdown="span">

   string (base58)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If an output, the address paid (may be someone else's address not belonging to this wallet).  If an input, the address paid in the previous output.  May be empty if the address is unknown, such as when paying to a non-standard pubkey script

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`category`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   Set to one of the following values:<br> `send` if sending payment<br> `receive` if this wallet received payment in a regular transaction<br> `generate` if a matured and spendable coinbase<br> `immature` if a coinbase that is not spendable yet<br> `orphan` if a coinbase from a block that's not in the local best block chain

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`amount`

   </td>

   <td markdown="span">

   number ([value amount][])

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   A negative amount if sending payment; a positive amount if receiving payment (including coinbases)

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>`amountblinder`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The amount blinding factor.  May be 32-byte zero**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>`asset`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The hexadecimal asset identifier or the asset's label**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>`assetblinder`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The asset blinders that prevent outside parties from discovering which assets each input spends**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`vout`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   For an output, the output index (vout) for this output in this transaction.  For an input, the output index for the output being spent in its transaction.  Because inputs list the output indexes from previous transactions, more than one entry in the details array may have the same output index

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`fee`

   </td>

   <td markdown="span">

   number (bitcoins)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If sending payment, the fee paid as a negative bitcoins value.  May be `0`.  Not returned if receiving payment

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`abandoned`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Indicates if a transaction was abandoned:<br> `true` if it was abandoned (inputs are respendable)<br> `false`  if it was not abandoned<br>Only returned by *send* category payments

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`hex`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The transaction in serialized transaction format

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli gettransaction f4f30db53238a7529bc51fcda04ea22bd8f8b188622a6488da12281874b71f72
```

Result:

```json
{ 
  "amount": { 
    "bitcoin": 0.00000000 
  }, 
  "fee": -0.00039460, 
  "confirmations": 2, 
  "blockhash": "5c81a92979fdc82a40d0aa8c1e39976a4fdcd890bf864794243052aae4ddb514", 
  "blockindex": 1, 
  "blocktime": 1497552832, 
  "txid": "f4f30db53238a7529bc51fcda04ea22bd8f8b188622a6488da12281874b71f72", 
  "walletconflicts": [ 
  ], 
  "time": 1497551591, 
  "timereceived": 1497551591, 
  "bip125-replaceable": "no", 
  "details": [ 
    { 
      "account": "", 
      "address": "2dmCj9T1PZ2osmWDjsaFsaoToCK2wyGkscT", 
      "category": "send", 
      "amount": -100.00000000, 
      "amountblinder": "2f6c001bdd96ba6950443f46d8ec53ab2a46cc6d3eedf4d9e86dcfff359d5c49", 
      "asset": "09f663de96be771f50cab5ded00256ffe63773e2eaa9a604092951cc3d7c6621", 
      "assetblinder": "ed8030dcfb6a0d299cf548f72e2034f6199f2fc90e6af35457b19f87cf65e16d", 
      "label": "", 
      "vout": 1, 
      "fee": -0.00039460, 
      "abandoned": false 
    },  
    { 
      "account": "", 
      "address": "2dmCj9T1PZ2osmWDjsaFsaoToCK2wyGkscT", 
      "category": "receive", 
      "amount": 100.00000000, 
      "amountblinder": "2f6c001bdd96ba6950443f46d8ec53ab2a46cc6d3eedf4d9e86dcfff359d5c49", 
      "asset": "09f663de96be771f50cab5ded00256ffe63773e2eaa9a604092951cc3d7c6621", 
      "assetblinder": "ed8030dcfb6a0d299cf548f72e2034f6199f2fc90e6af35457b19f87cf65e16d", 
      "label": "", 
      "vout": 1 
    } 
  ], 
  "hex": "01000000000101f4[...]729da00003a000000"
}
```


## getunconfirmedbalance

The `getunconfirmedbalance` RPC returns the wallet's total unconfirmed
balance.

The version in Elements is similar to the Bitcoin Core
[`getunconfirmedbalance` RPC][bcc getunconfirmedbalance] but also prints
other asset types besides bitcoin.
Element's API changes are emphasized in bold.

**Parameter #1---asset identifier**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **Asset identifier**

   </td>

   <td markdown="span">

   **string**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **An asset identifier or label to restrict the `amount` field in the results to that particular asset**

   </td>

  </tr>
 </tbody>
</table>


*Result---the balance of unconfirmed transactions paying this wallet*

**If the parameter (asset identifier) is not set, this is a JSON
object:**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **`result`**

   </td>

   <td markdown="span">

   **object**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **An object holding pairs of asset ids and balance amounts**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→<br>amount**

   </td>

   <td markdown="span">

   **string : [value amount][]**

   </td>

   <td markdown="span">

   **Required<br>(1 or more)**

   </td>

   <td markdown="span">

   **An asset identifier or label paired with the balance of that asset.  At a minimum, the `bitcoin` asset will be returned**

   </td>

  </tr>
 </tbody>
</table>


If the first parameter (asset identifier) is set, this is a [value
amount][] of that asset's balance:

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   number ([value amount][])

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   **The balance of all accounts in the requested asset**

   </td>

  </tr>
 </tbody>
</table>



## getwalletinfo

The `getwalletinfo` RPC provides information about the wallet.

The version in Elements is similar to the Bitcoin Core
[`getwalletinfo` RPC][bcc getwalletinfo] but also prints other asset
types besides bitcoin.
Element's API changes are emphasized in bold.

**Parameter #1---asset identifier**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **Asset identifier**

   </td>

   <td markdown="span">

   **string**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **An asset identifier or label to restrict the `amount` field in the results to that particular asset**

   </td>

  </tr>
 </tbody>
</table>


*Result---information about the wallet*

If the asset identifier parameter is provided, balances will be a number
for just that asset.  If the parameter is not provided, balances will be
a JSON object containing pairs of asset identifiers and values for each
asset held in the wallet.

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An object describing the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`walletversion`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The version number of the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`balance`

   </td>

   <td markdown="span">

   **number or object**

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The balance of the wallet.  **The same as returned by the `getbalance` RPC with the provided parameter**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`unconfirmed_balance`

   </td>

   <td markdown="span">

   **number or object**

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   **The unconfirmed balance of the wallet.  The same as returned by the `getunconfirmedbalance` RPC with the provided parameter**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`immature_balance`

   </td>

   <td markdown="span">

   number or object

   </td>

   <td markdown="span">

   Optional<br>(exactly 1)

   </td>

   <td markdown="span">

   **The balance of the wallet in coins that need more confirmation.  Uses the same rules as the `getbalance` RPC with the provided parameter.  Only returned if there's an immature balance**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`txcount`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The total number of transactions in the wallet (both spends and receives)

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`keypoololdest`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The date as Unix epoch time when the oldest key in the wallet key pool was created; useful for only scanning blocks created since this date for transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`keypoolsize`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The number of keys in the wallet keypool

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`unlocked_until`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Only returned if the wallet was encrypted with the `encryptwallet` RPC. A Unix epoch date when the wallet will be locked, or `0` if the wallet is currently locked

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli getwalletinfo
```

Result:

```json
{
  "walletversion": 130000,
  "balance": {
    "bitcoin": 20790000.09836920,
    "foocoin": 100.00000000,
    "d5fe63f77038c6e3cbd70139b5d30b9c0e885dbbfc916ebb442f9dd367c5c0fb": 1.00000000
  },
  "unconfirmed_balance": {
  },
  "immature_balance": {
    "bitcoin": 0.00039460
  },
  "txcount": 6,
  "keypoololdest": 1497547814,
  "keypoolsize": 100,
  "paytxfee": 0.00000000,
  "hdmasterkeyid": "12d5270d68f38b7d535247ac6885e058ed7cb19d"
}
```

# importblindingkey

The `importblindingkey` RPC imports a private blinding key in hex for a
Confidential Transaction (CT) address.

*Parameter #1---the CT address the key belongs to*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>address</td>
   <td>string (base58)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The address to which the private blinding key
   belongs. This is sometimes referred to as the `confidential_key`
   
   </td>
  </tr>
 </tbody>
</table>

*Parameter #2---the private blinding key*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>hexkey</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The blinding key in hexadecimal</td>
  </tr>
 </tbody>
</table>

*Result---empty on success; error on failure*

No result is returned on success, but an error will be returned in the
JSON-RPC `error` field if the import fails.

*Example*

```bash
address=$( elements-cli getnewaddress )
blinding_key=$( elements-cli dumpblindingkey $address )
elements-cli importblindingkey $address $blinding_key
```

Result:

None.  Import was successful (although, in this example, the blinding
key was already part of the wallet).

## importissuanceblindingkey

The `importissuanceblindingkey` RPC imports a private blinding key for
a previously-created asset issuance.

*Parameter #1---txid of the asset issuance*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>txid</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The txid of the asset issuance.  The issuance
   transaction must be in the wallet</td>
  </tr>
 </tbody>
</table>

*Parameter #2---the input index (vin) of the asset issuance*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>vin</td>
   <td>number (int)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   Within the asset issuance transaction, this is the
   input index number (vin), with the first input being `0`
   
   </td>
  </tr>
 </tbody>
</table>

*Parameter #3---the private blinding key*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>hexkey</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The blinding key in hexadecimal</td>
  </tr>
 </tbody>
</table>

*Result---empty on success; error on failure*

No result is returned on success, but an error will be returned in the
JSON-RPC `error` field if the import fails.

*Example*

```bash
elements-cli importissuanceblindingkey 33d0b9be5f5d7abc075a69a0aa12293350cb3b8c4021c73ef25bbc7d2eac33e6 0 96a57db45e0e9ccd31f525b6fe00a8526c459f2c47b3631c404c31a03e94056a
```

Result: empty (success).

## issueasset

The `issueasset` RPC creates a new asset and returns the asset's hex
identifier.

Note: this command spends one of the bitcoin UTXOs from your wallet, returning
the full amount to a new address in your wallet.  This ensures the
issuance is unique (not practical to duplicate) as described in section
4.4 of the [Confidential Assets][] paper.  However, this also means that
your wallet must contain at least 0.00000001 bitcoins in order for this
call to run.

*Parameter #1---amount to generate*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>assetamount</td>
   <td markdown="block">
   
   [value amount][]
   
   </td>
   <td>Required<br />(exactly 1)</td>
   <td>The amount of the asset to generate.  Each unit of
   this asset will be sub-divisible into 100 million parts just as each
   bitcoin is subdivisible into 100 million base units</td>
  </tr>
 </tbody>
</table>

*Parameter #2---number of reissuance tokens to generate*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>tokenamount</td>
   <td markdown="block">
   
   [value amount][]
   
   </td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The amount of [reissuance token][] to generate.  May
   be 0 to generate no token (preventing reissuance) or any value equal
   to or above 0.00000001 to allow someone with a reissuance token to
   reissue the asset.  No token amount is consumed during the reissuance, so
   you may use any arbitrary value above 0 to allow reissuance
   
   </td>

  </tr>
 </tbody>
</table>

*Parameter #3---whether or not to blind the issuance*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>blind</td>
   <td>bool</td>
   <td>Optional<br />(0 or 1)</td>
   <td>Whether to blind the issuance amount. Default is true</td>
  </tr>
 </tbody>
</table>

*Result---information about the issuance transaction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>object</td>
   <td>Required<br />(exactly 1)</td>
   <td>The results of the issuance</td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`txid`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The txid of the issuance</td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`vin`
   
   </td>
   <td>number (int)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   Within the asset issuance transaction, this is the
   input index number (vin), with the first input being `0`
   
   </td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`entropy`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The [entropy][] value
   
   </td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`asset`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The asset type</td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`token`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The [reissuance token][] value
   
   </td>
  </tr>

 </tbody>
</table>

*Example*

```bash
elements-cli issueasset 100 1 true
```

Result:

```json
{
  "txid": "33d0b9be5f5d7abc075a69a0aa12293350cb3b8c4021c73ef25bbc7d2eac33e6",
  "vin": "0",
  "entropy": "237f46739ec91f6883c40047dfb3fa947fa8ca37749f1a1132ebf4ea280358d2",
  "asset": "72c203c22b599787d362f1ad2766c208117db385f9157d55e501e1da32b156d6",
  "token": "d46db6c277f129abfdd0facd18e8d862daaac3659c2ce531ed69a7f5caccbebb"
}
```

## listissuances

The `listissuances` RPC returns either a list of all issuances for all
assets, or a list of all issuances for a specified asset.

*Parameter #1---an optional asset that results should be limited to*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>asset</td>
   <td>string</td>
   <td>Optional<br />(0 or 1)</td>
   <td>The hex id of the asset you want to list</td>
  </tr>
 </tbody>
</table>

*Result---a list of issuances*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>array</td>
   <td>Required<br />(exactly 1)</td>
   <td>An array containing JSON objects that describe each
   asset issuance.  The array may be empty if the wallet doesn't know of
   any asset issuances, or if none of the issuances match the asset
   searched for</td>
  </tr>

  <tr>
   <td>→<br>issuance</td>
   <td>object</td>
   <td>Optional<br />(0 or more)</td>
   <td>An object containing details about a particular
   asset issuance or reissuance.</td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`isreissuance`
   
   </td>
   <td>bool</td>
   <td>Required<br />(exactly 1)</td>
   <td>True if this is a reissuance; false if this is an original
   issuance.</td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`token`
   
   </td>
   <td>string (hex)</td>
   <td>Optional<br />(0 or 1)</td>
   <td markdown="block">
   
   The identifier for the [reissuance token][] that allows issuing
   more of the asset.  Returned even if the token amount is 0
   (forbidding reissuance), but not returned for reissuances (to reissue,
   use the token from the original issuance)
   
   </td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`tokenamount`
   
   </td>
   <td markdown="block">
   
   number ([value amount][])
   
   </td>
   <td>Optional<br />(0 or 1)</td>
   <td>The number of reissuance tokens created when the
   asset was first issued, or -1 if the number of tokens is unknown to
   the wallet. Not returned for reissuances</td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`tokenblinds`
   
   </td>
   <td>string (hex)</td>
   <td>Optional<br />(0 or 1)</td>
   <td>The blinding factor used for the reissuance tokens Set to 32-byte zero if the reissuance token amount is 0</td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`entropy`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The [entropy][] value
   
   </td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`txid`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The txid of the issuance or reissuance</td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`vin`
   
   </td>
   <td>number (int)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   Within the asset issuance transaction, this is the
   input index number (vin), with the first input being `0`
   
   </td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`asset`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The asset's hex identifier</td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`assetlabel`
   
   </td>
   <td>string</td>
   <td>Optional<br />(0 or 1)</td>
   <td>The asset's label, if known.  Otherwise not returned</td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`assetamount`
   
   </td>
   <td markdown="block">
   
   number ([value amount][])
   
   </td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The amount of the asset issued or reissued.  Set to `-1` if the
   amount was blinded and is unknown to the wallet
   
   </td>
  </tr>

  <tr>
   <td markdown="block">
   
   → →<br>`assetblinds`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The blinding factor used for the issued or reissued asset.</td>
  </tr>

 </tbody>
</table>

*Example*

```bash
elements-cli listissuances
```

Result:

```json
[
  {
    "isreissuance": false,
    "token": "d46db6c277f129abfdd0facd18e8d862daaac3659c2ce531ed69a7f5caccbebb",
    "tokenamount": 1.00000000,
    "tokenblinds": "27d6f40de33121b29f60f34ab16d59106f7e76abf3a66c498b2785265f01eee7",
    "entropy": "237f46739ec91f6883c40047dfb3fa947fa8ca37749f1a1132ebf4ea280358d2",
    "txid": "33d0b9be5f5d7abc075a69a0aa12293350cb3b8c4021c73ef25bbc7d2eac33e6",
    "vin": 0,
    "asset": "72c203c22b599787d362f1ad2766c208117db385f9157d55e501e1da32b156d6",
    "assetamount": 100.00000000,
    "assetblinds": "2b8073a423fac2930fb6c8270af95c1cfe2ee193d8413100abd5efab5d77b712"
  }
]
```

## listtransactions

The `listtransactions` RPC returns the most recent transactions that
affect the wallet.

The version in Elements is similar to the Bitcoin Core
[`listtransactions` RPC][bcc listtransactions] but also prints extra
Elements-specific transaction information, such as Confidential
Transactions (CT) outputs and multiple asset types.
Element's API changes are emphasized in bold.

*Parameter #1---an account name to get transactions from*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Account

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   *Deprecated: will be removed in a later version of Bitcoin Core*<br><br>The name of an account to get transactions from.  Use an empty string ("") to get transactions for the default account.  Default is `*` to get transactions for all accounts.

   </td>

  </tr>
 </tbody>
</table>


*Parameter #2---the number of transactions to get*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Count

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The number of the most recent transactions to list.  Default is `10`

   </td>

  </tr>
 </tbody>
</table>


*Parameter #3---the number of transactions to skip*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Skip

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The number of the most recent transactions which should not be returned.  Allows for pagination of results.  Default is `0`

   </td>

  </tr>
 </tbody>
</table>


*Parameter #4---whether to include watch-only addresses in details and calculations*


<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Include Watch-Only

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If set to `true`, include watch-only addresses in details and calculations as if they were regular addresses belonging to the wallet.  If set to `false` (the default), treat watch-only addresses as if they didn't belong to this wallet

   </td>

  </tr>
 </tbody>
</table>



*Result---payment details*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An array containing objects, with each object describing a **payment** or internal accounting entry (not a transaction).  More than one object in this array may come from a single transaction.  Array may be empty

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>Payment

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Optional<br>(0 or more)

   </td>

   <td markdown="span">

   A payment or internal accounting entry

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`account`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   *Deprecated: will be removed in a later version of Bitcoin Core*<br><br>The account which the payment was credited to or debited from.  May be an empty string ("") for the default account

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`address`

   </td>

   <td markdown="span">

   string (base58)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The address paid in this payment, which may be someone else's address not belonging to this wallet.  May be empty if the address is unknown, such as when paying to a non-standard pubkey script or if this is in the *move* category

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`category`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   Set to one of the following values:<br> `send` if sending payment<br> `receive` if this wallet received payment in a regular transaction<br> `generate` if a matured and spendable coinbase<br> `immature` if a coinbase that is not spendable yet<br> `orphan` if a coinbase from a block that's not in the local best block chain<br> `move` if an off-block-chain move made with the `move` RPC

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`amount`

   </td>

   <td markdown="span">

   number ([value amount][])

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   A negative amount if sending payment; a positive amount if receiving payment (including coinbases)

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>amountblinder**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The amount blinding factor.  May be 32-byte zero**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>asset**

   </td>

   <td markdown="span">

   **string**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The hexadecimal asset identifier or the asset's label**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>assetblinder**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The asset blinders that prevent outside parties from discovering which assets each input spends**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`label`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   A comment for the address/transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`vout`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   For an output, the output index (vout) for this output in this transaction.  For an input, the output index for the output being spent in its transaction.  Because inputs list the output indexes from previous transactions, more than one entry in the details array may have the same output index.  Not returned for *move* category payments

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`fee`

   </td>

   <td markdown="span">

   number (bitcoins)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If sending payment, the fee paid as a negative bitcoins value.  May be `0`. Not returned if receiving payment or for *move* category payments

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`confirmations`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The number of confirmations the transaction has received.  Will be `0` for unconfirmed and `-1` for conflicted.  Not returned for *move* category payments

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`trusted`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Indicates whether we consider the outputs of this unconfirmed transaction safe to spend.  Only returned for unconfirmed transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`generated`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Set to `true` if the transaction is a coinbase.  Not returned for regular transactions or *move* category payments

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`blockhash`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The hash of the block on the local best block chain that includes this transaction, encoded as hex in RPC byte order.  Only returned for confirmed transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`blockindex`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The index of the transaction in the block that includes it.  Only returned for confirmed transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`blocktime`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The block header time (Unix epoch time) of the block on the local best block chain that includes this transaction.  Only returned for confirmed transactions

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`txid`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The TXID of the transaction, encoded as hex in RPC byte order.  Not returned for *move* category payments

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`walletconflicts`

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   An array containing the TXIDs of other transactions that spend the same inputs (UTXOs) as this transaction.  Array may be empty.  Not returned for *move* category payments

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → → →<br>TXID

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Optional<br>(0 or more)

   </td>

   <td markdown="span">

   The TXID of a conflicting transaction, encoded as hex in RPC byte order

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`time`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   A Unix epoch time when the transaction was added to the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`timereceived`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   A Unix epoch time when the transaction was detected by the local node, or the time of the block on the local best block chain that included the transaction.  Not returned for *move* category payments

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`comment`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   For transaction originating with this wallet, a locally-stored comment added to the transaction.  Only returned in regular payments if a comment was added.  Always returned in *move* category payments.  May be an empty string

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`to`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   For transaction originating with this wallet, a locally-stored comment added to the transaction identifying who the transaction was sent to.  Only returned if a comment-to was added.  Never returned by *move* category payments.  May be an empty string

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`otheraccount`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   This is the account the value were moved from or moved to, as indicated by a negative or positive *amount* field in this payment.  Only returned by *move* category payments

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`bip125-replaceable`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   Indicates if a transaction is replaceable under BIP125:<br> `yes` replaceable<br> `no` not replaceable<br> `unknown` for unconfirmed transactions not in the mempool

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`abandoned`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Indicates if a transaction is was abandoned:<br> `true` if it was abandoned (inputs are respendable)<br> `false`  if it was not abandoned<br>Only returned by *send* category payments

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli listtransactions
```

Result:

```json
[
  {
    "account": "",
    "address": "2deEkkAxz9q4vrNcP13QbBGcfqPB1UymRFu",
    "category": "send",
    "amount": -0.10000000,
    "amountblinder": "49bfc4682b2d94b6f11363fee9cc0e5546a56dedf756f51e471baa7e027a4123",
    "asset": "09f663de96be771f50cab5ded00256ffe63773e2eaa9a604092951cc3d7c6621",
    "assetblinder": "771ade3ddd5a7e405cb153911c027649156d838a07482273b5b113c5af2698cf",
    "vout": 1,
    "fee": -0.00038660,
    "confirmations": 0,
    "trusted": true,
    "txid": "7b8236c687e5424f65662fecce4e07523054e89a05b731ef05b6c0235ee5ec04",
    "walletconflicts": [
    ],
    "time": 1498416700,
    "timereceived": 1498416700,
    "bip125-replaceable": "yes",
    "abandoned": false
  }
]
```

## listunspent

The `listunspent` RPC returns an array of unspent transaction outputs
belonging to this wallet.

The version in Elements is similar to the Bitcoin Core
[`listunspent` RPC][bcc listunspent] but also lists Elements-specific
information about unspent transactions, such as their asset type and
Confidential Transactions (CT) information.
Element's API changes are emphasized in bold.

*Parameter #1---the minimum number of confirmations an output must have*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Minimum Confirmations

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The minimum number of confirmations the transaction containing an output must have in order to be returned.  Use `0` to return outputs from unconfirmed transactions. Default is `1`

   </td>

  </tr>
 </tbody>
</table>


*Parameter #2---the maximum number of confirmations an output may have*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Maximum Confirmations

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The maximum number of confirmations the transaction containing an output may have in order to be returned.  Default is `9999999` (~10 million)

   </td>

  </tr>
 </tbody>
</table>


*Parameter #3---the addresses an output must pay*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Addresses

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If present, only outputs which pay an address in this array will be returned.  To return everything, pass an empty array: `[]`

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>Address

   </td>

   <td markdown="span">

   string (base58)

   </td>

   <td markdown="span">

   Required<br>(1 or more)

   </td>

   <td markdown="span">

   A P2PKH or P2SH address

   </td>

  </tr>
 </tbody>
</table>

*Parameter #4---include unsafe*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Include unsafe

   </td>

   <td markdown="span">

   boolean

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If true, Include outputs that are not safe to spend, because they come from unconfirmed untrusted transactions or unconfirmed replacement transactions (cases where we are less sure that a conflictingtransaction won't be mined).

   </td>

  </tr>
 </tbody>
</table>

**Parameter #5---asset filter**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **Asset identifier**

   </td>

   <td markdown="span">

   **string**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **An asset identifier or label to only return entries for that asset.  The default is blank which lists all assets**

   </td>

  </tr>
 </tbody>
</table>


*Result---the list of unspent outputs*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   An array of objects each describing an unspent output.  May be empty

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>Unspent Output

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Optional<br>(0 or more)

   </td>

   <td markdown="span">

   An object describing a particular unspent output belonging to this wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`txid`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The TXID of the transaction containing the output, encoded as hex in RPC byte order

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`vout`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The output index number (vout) of the output within its containing transaction

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`address`

   </td>

   <td markdown="span">

   string (base58)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The P2PKH or P2SH address the output paid.  Only returned for P2PKH or P2SH output scripts

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`account`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   *Deprecated: will be removed in a later version of Bitcoin Core*<br><br>If the address returned belongs to an account, this is the account.  Otherwise not returned

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`scriptPubKey`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The output script paid, encoded as hex

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`redeemScript`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   If the output is a P2SH whose script belongs to this wallet, this is the redeem script

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`amount`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The amount paid to the output

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>`asset`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br />(exactly 1)**

   </td>

   <td markdown="span">

   **The asset identifier in hex**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>`assetcommitment`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Optional<br />(1 or more)**

   </td>

   <td markdown="span">

   **A hex-encoded asset commitment, one for each input.**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>`assetlabel`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Optional<br />(0 or 1)**

   </td>

   <td markdown="span">

   **The asset label, if known.  Otherwise not returned**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`confirmations`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The number of confirmations received for the transaction containing this output

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`spendable`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   Set to `true` if the private key or keys needed to spend this output are part of the wallet.  Set to `false` if not (such as for watch-only addresses)

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>`solvable`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   Set to `true` if the wallet knows how to spend this output.  Set to `false` if the wallet does not know how to spend the output.  It is ignored if the private keys are available 

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ → →<br>`serValue`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The output's value commitment**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>`blinder`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The output's value blinding factor.  May be 32-byte zero if there's no blinding factor**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→ →<br>`assetblinder`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The output's asset blinding factor.  May be 32-byte zero if there's no blinding factor**

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli listunspent
```

Result:

```json
[
  {
    "txid": "389ced8ee87ebead8c4c3af49dc86be7e8f543ae3ca6956e319dee180e3a73f4",
    "vout": 99,
    "scriptPubKey": "51",
    "amount": 210000.00000000,
    "asset": "09f663de96be771f50cab5ded00256ffe63773e2eaa9a604092951cc3d7c6621",
    "assetlabel": "bitcoin",
    "confirmations": 120,
    "spendable": true,
    "solvable": true,
    "serValue": "00508a7119130000",
    "blinder": "0000000000000000000000000000000000000000000000000000000000000000"
  }
]
```

## rawblindrawtransaction

The `rawblindrawtransaction` RPC uses a raw blinding interface (one
without wallet support) to convert one or more outputs of a raw
transaction into blinded Confidential Transactions (CT) outputs,
returning the modified raw transaction.

The output keys used to blind the outputs are defined by giving `createrawtransaction`
CT addresses.

Since there is no access to the wallet, no attempts are made to add additional outputs.

*Parameter #1---the raw transaction whose outputs should be blinded*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Transaction</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The hex-encoded serialized transaction whose outputs
   should be blinded.  The output keys to be used can be specified by
   using a confidential address in the `createrawtransaction` RPC.  The
   transaction must not already have blinded outputs
   
   </td>
  </tr>
 </tbody>
</table>

*Parameter #2---input blinders*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Input Blinders</td>
   <td>array</td>
   <td>Required<br />(exactly 1)</td>
   <td>An array containing the input blinders to use as
   strings.</td>
  </tr>

  <tr>
   <td>→<br>Blinder</td>
   <td>string (hex)</td>
   <td>Required<br />(1 or more)</td>
   <td markdown="block">
   
   The input's blinding factor.  There must be one for each input
   and they must appear in the same order as the inputs.  The blinding
   factor is the `blinder` field returned by the `listunspent` RPC
   
   </td>
  </tr>
 </tbody>
</table>

*Parameter #3---the input amounts*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Input amounts</td>
   <td>array</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   An array containing the amount of each input to use as a [value
   amount][].
   
   </td>
  </tr>

  <tr>
   <td>→<br>amount</td>
   <td markdown="block">
   
   number ([value amount][])
   
   </td>
   <td>Required<br />(1 or more)</td>
   <td>The amount of the input at the same index as this field.</td>
  </tr>
 </tbody>
</table>

*Parameter #4---the asset identifiers*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Asset Identifiers</td>
   <td>array</td>
   <td>Required<br />(exactly 1)</td>
   <td>An array containing the input asset identifiers as
   strings</td>
  </tr>

  <tr>
   <td>→<br>Asset id</td>
   <td>string (hex)</td>
   <td>Required<br />(0 or more)</td>
   <td markdown="block">
   
   An asset identifier (hex, not a label).  There must
   be one for each input and they must appear in the same order as the
   inputs.  The identifier is the `asset` field returned by the
   `listunspent` RPC
   
   </td>
  </tr>
 </tbody>
</table>

*Parameter #5---the asset blinders*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Asset Blinders</td>
   <td>array</td>
   <td>Required<br />(exactly 1)</td>
   <td>An array containing the asset blinders that prevent
   outside parties from discovering which assets each input spends</td>
  </tr>
  
  <tr>
   <td>→<br>asset blind</td>
   <td>string (hex)</td>
   <td>Required<br />(0 or more)</td>
   <td>An asset blind.  There must be one for each input and they must appear in the same order as the inputs.</td>
  </tr>
 </tbody>
</table>

*Parameter #6---(currently ignored)*

*Parameter #7---whether to return a transaction even if blinding fails*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
<tbody>
  <tr>
   <td>ignoreblindfail</td>
   <td>bool</td>
   <td>Optional<br />(0 or 1)</td>
   <td>Whether to return a transaction (rather than fail) when any blinding attempt fails due to the number of blinded inputs or outputs</td>
  </tr>
 </tbody>
</table>

*Result---the unsigned raw transaction in hex*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>string</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The resulting unsigned raw transaction in serialized
   transaction format, encoded as hex.  If the transaction couldn't be
   blinded, this will be set to JSON `null` and the JSON-RPC `error`
   field may contain an error message.
   
   </td>
  </tr>
 </tbody>
</table>

*Example*

```bash
## We'll be using bitcoins in this example
bitcoin_asset_id=09f663de96be771f50cab5ded00256ffe63773e2eaa9a604092951cc3d7c6621

## Create a new address
blinded_addr=$( elements-cli getnewaddress )

## Get the unblinded address
unblinded_addr=$( elements-cli validateaddress $blinded_addr | jq -r .unconfidential )

## Let's create two new inputs by spending some money to the address
txid1=$( elements-cli sendtoaddress $blinded_addr 1 )
txid2=$( elements-cli sendtoaddress $blinded_addr 3 )

## Let's collect the information about the inputs that we'll need later
vout1=$( elements-cli listunspent 0 | jq ".[]|select(.txid == \"$txid1\" and .address == \"$unblinded_addr\") | .vout" )
blinder1=$( elements-cli listunspent 0 | jq -r ".[]|select(.txid == \"$txid1\" and .address == \"$unblinded_addr\") | .blinder" )
assetblinder1=$( elements-cli listunspent 0 | jq -r ".[]|select(.txid == \"$txid1\" and .address == \"$unblinded_addr\") | .assetblinder" )
vout2=$( elements-cli listunspent 0 | jq ".[]|select(.txid == \"$txid2\" and .address == \"$unblinded_addr\") | .vout" )
blinder2=$( elements-cli listunspent 0 | jq -r ".[]|select(.txid == \"$txid2\" and .address == \"$unblinded_addr\") | .blinder" )
assetblinder2=$( elements-cli listunspent 0 | jq -r ".[]|select(.txid == \"$txid2\" and .address == \"$unblinded_addr\") | .assetblinder" )

## Create an unblinded raw transaction
raw_tx=$( 
  elements-cli createrawtransaction '''[
    { "txid": "'$txid1'", "vout": '$vout1', "amount": 1 },
    { "txid": "'$txid2'", "vout": '$vout2', "amount": 3 }
  ]''' '{ "'$blinded_addr'": 3.9, "fee": 0.1 }' 
)

## Blind the transaction
blinded_tx=$(
  elements-cli rawblindrawtransaction $raw_tx \
    "[\"$blinder1\", \"$blinder2\"]" \
    "[1, 3]" \
    "[\"$bitcoin_asset_id\", \"$bitcoin_asset_id\"]" \
    "[\"$assetblinder1\", \"$assetblinder2\"]"
)

## Ensure we can sign it
signed_tx=$( elements-cli signrawtransaction $blinded_tx | jq -r .hex )

## Final validity check: ensure we can broadcast it
elements-cli sendrawtransaction $signed_tx
```

Result:

The transaction was successfully broadcast,

```text
25999796202a90d44a97194c144424a915a9460fefe91227292627c3aabc5522
```


## reissueasset

The `reissueasset` RPC creates more of an already-issued asset.  You
must have a reissuance token in your wallet to create a reissuance, but
none of the token amount will be consumed in the process of reissuing.

*Parameter #1---the asset to reissue*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Asset</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   The asset identifier (in hex).  You must have the
   reissuance token in your wallet (check with the `listissuances`
   RPC)
   
   </td>
  </tr>
 </tbody>
</table>

*Parameter #2---the amount of new assets to issue*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Amount</td>
   <td markdown="block">
   
   number ([value amount][])
   
   </td>
   <td>Required<br />(exactly 1)</td>
   <td>The amount of additional asset to generate</td>
  </tr>
 </tbody>
</table>

*Result---the txid and vout of the reissuance output*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>object</td>
   <td>Required<br />(exactly 1)</td>
   <td>An object containing the txid and vout of the reissuance output</td>
  </tr>
  <tr>
   <td markdown="block">
   
   →<br>`txid`
   
   </td>

   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The txid of the transaction that issues the new value</td>
  </tr>
  <tr>
   <td markdown="block">
   
   →<br>`vout`
   
   </td>

   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The output index (vout) of the reissuance from the transaction that issues the new value</td>
  </tr>
 </tbody>
</table>

*Example*

```bash
elements-cli reissueasset 2cc6ef8dc6d1078e03537b5880833bca0232cefae094db1663ddeea877a7f209 41
```

Result:

```json
{
  "txid": "dc09afa63282dc1c2dd87a00606583c2e183a4ec27753d3cc47754d04e36943f",
  "vin": 0
}
```

## sendrawtransaction

The `sendrawtransaction` RPC validates a transaction and broadcasts it
to the peer-to-peer network.

The version in Elements is similar to the Bitcoin Core
[`sendrawtransaction` RPC][bcc sendrawtransaction] but warns users when
they attempt to send transactions that don't use Confidential
Transaction (CT) blinding but have attached blinding pubkeys to the outputs.
Element's API changes are emphasized in bold.

*Parameter #1---a serialized transaction to broadcast*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Transaction

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The serialized transaction to broadcast, encoded as hex

   </td>

  </tr>
 </tbody>
</table>


*Parameter #2--whether to allow high fees**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Allow High Fees

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Set to `true` to allow the transaction to pay a high transaction fee.  Set to `false` (the default) to prevent Bitcoin Core from broadcasting the transaction if it includes a high fee.  Transaction fees are the sum of the inputs minus the sum of the outputs, so this high fees check helps ensures user including a change address to return most of the difference back to themselves

   </td>

  </tr>
 </tbody>
</table>


**Parameter #3---whether to allow unblinded outputs**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **Allow blind fails**

   </td>

   <td markdown="span">

   **bool**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **If `true`, the transaction will be broadcast even if not all outputs are blinded using CT.  If `false` (the default), an error will be printed if any outputs are unblinded**

   </td>

  </tr>
 </tbody>
</table>


*Result---a TXID or error message*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   null/string (hex)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   If the transaction was accepted by the node for broadcast, this will be the TXID of the transaction encoded as hex in RPC byte order.  If the transaction was rejected by the node, this will set to `null`, the JSON-RPC error field will be set to a code, and the JSON-RPC message field may contain an informative error message

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli sendrawtransaction bdaac7790c5e54bf8dbc9a170a77c43b83ccb35e230926e790b2f8f7801976a9140857ab7d748cd4a65bc3fdd9defea823f1381ad588ac0a72cab357a0ec46ae2c8b956575c11d8e01dd6b657358243c691e1a5faf07358909e8984de82b36bddbaa1d09ac8d34f0c9aef2f20a4806199728217e854db3be9803226cb8c7585b6e65964cc928918d1bc6ba871a1a68a6cfc5ef5e4d7b31d0e19f1976a91434c459c0aa26b5c4c4658e5c705a241b08ab4ee688ac0121667c3dcc51290904a6a9eae27337e6ff5602d0deb5ca501f77be96de63f609010000000000009704000000000043010001739b62e7816fee798e13f9d7af16c4fbe69501cecacb011deef770f9ad97722cf2ff1c179ad5f8cf5cc7ba9480e9202cddc1f82475992684c5fef7e80b396736fd2d0e602c0000000000000001fa0c23cdd6dff657e8d5932b6f856229c45a524fcba2e035d98ff2b23dba3af7c0c427dd47a11fe52b33d036a797f581d1537ef61bebbb5a709d12927f277d4f508ac74d11d214033a937204883b480de87d06791df4418ac5ba2087416d6ee51553fb2e7565db8836489c7acd57b87ed965982950cd7ba61f062e48a111b2a8353216bb2ee59f6f347f0da556535d04fa2652826b28025e422d7763feeea1f846aaa81f0c2d8cefa2cbd40d177b1646a22355c8518026fa5e526cf2e4c47a006b0342bfade0901537e3db3ff37cd3634a5d1add239208c1ba9bf545604c238e18db7bcf145b3880e2063e55a39f9d962b1b26fa2cfc2304eada47261a8a9bf5989a6c756b5387794c75b4ab062fba21a89c135c301324bfe1c9f817a672be056966502c27d34dbba63db626f766e11c0a1554681a5ba4b72f28bb58a9ef85e14bc97a0c9c675749e832535901f271be0513da4c9d0a0da6bb78e2041255ace53211c418501f04afd6e617bdf98ae487825ec85ab6f34a3e25ba08426880bc9c191dc9b34984d05e72483d932d4faad5a1be52a94d188060ac2310014b669facd7d4032ca5af2680537a37eef6838ed9dd8f134e6a0d64896b18d0eb08f6a86321b397e522f490469b474fadc554ef39cd037060f9694128eaf5e931a953b4a912333af42fe9e954f82307022539c0f7b7296de1662fa13cdc7fdb690d7e1cc4f973b2dea61253750f9acf24b1505190a1d93734e410557fa07333cf4276a8c2fd51fd2b4dd1035dbb98bf685527a3fbb6bcbc449f838a7423d7bdb350463afb83c8e4ef2ced8c1b5388d3953def665b9c8074357daa2e4391a9f38ac1ea15718ab264ad73ad51004570073a068814912208be2b64b1660a15ae461e54ad5bedd2e5bc2df460b14bdf085ccd29e5893f37dad73d9caebbfb10221feadd24d9242bc2c67d937190fb71cfe2e37c214ebaf870e45c9e9661877d0dc34fbf69e72a1fd69aa12b09ee3688ebd257acf8f288e6e728662fddf8e4ec964b4e1ac79907f8008d7964927cc3536e7e9b2e5c5eb5293789cc41d44c3343449c2b760d66cd87fe46e986ebaa21ecd8cb23459a12bea484eefe4fb59347b43d6540baf92f217d984c5c73f6e6bad5d19e89f3675b310b62f97b43445326563409c553735af2e6d97552a6d134077299dce80e7f5fd37d8439d3317451a4e01ed8b51a5da5d6fdd768c8c20f888c1118e97b51390b53f86ab2a6330b94e7ebf524e96ba8818b7d8441f52ee1396c0a86e3c3a1ac6022b8194fcd6ec3879adfeb8ae5143720c910863285855b2f1756ad80fa960bba4bb02d1e193514b0cc7fadaafa05cc7c93446c3985c7cd5b07a40757fab0f389d35177e7fa6273246ea4bf1a96b41c7a1bb056efcde9d58cb37220edcf208ee01de92f93b6ac90032cc8b858b74abf11082e37e3f68c220ea7e2a4e0f0b1ef5ebd08c66535ac32a14c871171966113154e250e2b2d10dea457115dbd9c5ead35bbd9e078146b1bc2d640f2ef37af1a62edd310bcd9d683e81fead0b7764f8a204555905e98d38f0f898856b677a6461e7f3fed115a8626f087ab0b6e51fc94403a17ceb9a194317e420fc325f8fbb9c9f9b4ee4cb947b0aba0a4f38b877301a902a87fdefe7aaa177fad971077df67eadbbf4463282383e4ea85a3d012203431800ea6699274bad4182947e95898067f43d20e2a88e878ae308a37f5333592e997f4ab957e066484de592a787cf6fbbf72b0fe6a99353fe696130af405e61c466272c013a1f6965e91f566b6300dd2541cde966ed64fb4c168ebb64502a8095df26f56016c12cef64cfaca44dc4afee95b9fbdd616b6fb23e1527981344df4be3814382ee0474044a98eac2428fd39341ed1beec5f4dbd115129386a1e5e8a5ab293c237a1c6452648a2cab9e769a12c0408f3b0f948594055fa7d080fe262f65babd20b0966c563809e38e2e46ef1c85d01f5bcfd51fa8d6b44725d11ad33c2073389d24571c54738e0a0aec6e5475f6c22b5812c6cf0d230e35c9b052ffa88f4e5ab916f13cfe81b2df4a2c98c448231c0f18fc462460749b0ccc0a0f60755a6b7ab757ef1e9597b8195a28473b13e76c580de36b6c5b0f071b3d05358edf7395bcbc1751e4621d6b10836591ad10a37e9847dc4113f2e048d2bba8d70cf49f3631419cfb58f64c604ed9b30d2c85728988292ee62d628dd86fd59cbbaae56f1d5d86acf73aa8fcf3db345713080fa577d5d5cfa265a00acadd87327afbc554e1d0f681adc62d27b6dcbb79746401aab8ea792b6a4eecdfdba7f0f7d999f44058a7969163db6a74f28e8ed2a9f8fd9b76ac23fab041179c8bc37689b7f9e6a0d468ce941d183629c52f6da4e9a020fa41da6135db5e935c65bfb43457ec8940901116fe265b985a23883cb48eb8e1d3e197c6558655fbd37845667cf8c705990bcf37554cb2890a359acaf8ed15bad999a0fcfd0e5160e2385a77cdbe26ba117b7719834ef159d52d997520704b112c3191726d35f42dd4f4d35a536afe60d770c397679a71efc16c1251ad551c3de806396722a3524276b40bde5563c2d14b62ed6521afa010337f2ecfe1fc002671b6f1c9d5450edb442bbc78195d8d56352630680d4306d7c90542c446d94e6196de44eef1430472c84e5f08b9335fde4694719e43a4d75530ea646b21bbc65e299698aed7e4b58d61078bcb12d7ce4754d28f19b2b4ee3b06be143b2dae8753f7a3075a6ef8fbcc6a7600da3b93200359585decb98c91c4c3d7eb284f6821da7323eb6845daae349cfc5dfc371bdc24690c6afdade80f45f9dfcdf9e72be9ba5a1d96fe8a9be35b13ee9bfcafc024d6d633eaa43c2b61c305a222f21c04c86e93a44b93c016ea2ead2e694d5bb028d44d4654762d2ba092123ccd45b0d0f1fcde2c735cbf32b3cbb97fb75a8919d92418abfcf456e770a52e0b6b046222752aa00a36dd490e9b8b2ecc48ef2127dfdab7b2b06b3dbcf73cee917946e37200f714c1be26bfc2185a7fb56dd5be4e8a090d1eb32d496fed8f339b6b133fa40f79959d5c6bb85dee4e80b37515aee34d5e407c2e85a3a30b4cbb39e7a6b8b0c8e7eb2f7571d7c21fea226aec75eda785f3d7d266d1275cb0327a4fcb38a316be2fa26266b84bf72f207dc2b788c1500011dcedeab5603c855abe3340a95a26d2fba2a60be7f79504daaedd9c11266cdfbccbae592e1423e227fed4fab52385fb685f7247972663f8488efe823f4046f8c12fe179a085d3e48ea0b679892c358e1aa90d7814dd8d7520632532f80fd61b77788a08c8a4207923919c2f935256a2b0a18dca6e684ace5ba8efce20615357b280025f7c9e944239ce934be0d762c48cca41a9cc0281f914979637334401d92ff5d7b218e4415427fc09e2ae960b80bcda5cd9d668dc9926e357c34760b337e749f2e2546ee28ba792cee4ae1a496beda922e3eb001c120bb8169de022f2061c447a30de3a3afa3d2423f5e8c8a86aa6526df4989d838aa21e228309054ea63882163fcb4552ee1d40e4ae7874b1e50fff597e17bc5c9643d3fce08d8ae03cb03057a3e580ed168d52f85c7d1d0e556ad3586acb0a27b9fc24bb821592fa4adf0ee9597fa9c6de9a78a3be19ff54c383d63d5d3a2e073cb598e48b86ff95c4aeb28f7e3f79d18d74690645eaf1aebd5cbd65f59981b5f8bc08032dff7fa5940e5319fd59dfcebe47c8d05577ef80fe88115c8f4271d85eacb7faa54ef283c35a50486c0a0045982d0647eef8f43d4f436aaaf1b100f51ba4d900d0e1bc8905c63e0bcae672b029d5b7287cb1288c5c1b164f45c4310bc61f1c23d7ce94a5146a9aa6f1668e192734638a7c34ca961c0797da693bb0ce59457523c4d7511a3975bd9449f0c2aa6a9c04a995a5dfa7f8fa930e3698a4b3d48c279110859e5ebe3bd1f38a85c0e707add1691a6385358f6e8a54110bd5468c06a52c05b308abbc3d88f03d205f48cea5080947b6acaec955118afde043d51ee2950030fd8b330f81d3eefec32991517fc1cefb08560ed6399ea9bd644dcfd25dd41ef327f91154ad7712ba77fb105bad65c148b6a4c2504c2805d8d92651cb719417a9a054c6aec388c7cec3906d3bb477b6865a2561a3ffe706b6c1f4d2ebbfdc5c055f06561e1e652ce0b36203ccc18533ed9d2cff8a6a180b146ea705a961e010dfb6027f40bc714c94e8d775a93859e224ffbb223f78040debf7a38f6807d62f7b86937f5da1f8012942f873c1b483bd74366dd4132a772eedcbcc91ea725d9cf361565493b214a54dc2c524eca7bdfe107ab7473f4574821f2501a3c3ceb2be94069984274081927b31e6d71cac889357d8f5607690db2ea183ac92e09ca2a1b132f54b2ebde2b2294019df2232efccee6d65629bf1d6b1c5bd4646086690b371428eb5aad1da7a18dcc2bb75d45deb68a46e3fc1393414c90047ac57d929642ef4c57770d33c157e50e3948b266a9d5c3f95ff4683c7cb6cf441ef0eef68273b14a1ae3689ecda0aa1e28e7075bf6c78556218c5e1190558829493048cf3a42878634407f9ae774e3e582f4aa89c7abf07753cc142aca83a58abe6fcf1a7cb9ecf3987d7e85e3ce4e9649eba8195bb4b391d61ef82c683e49e0173a7a062819d3c65c127213cbd37016213e3e29fea1cec8c39b20cf302b52c67612d47902d0c00c97a5aaceff0e8d73318ff716f9e37f964f9e127cb69bfc931efe1a31284c052a84cce9caa268feb6a935eaaeebe64247d4ddd60c7cb938c38ac33861b562eb085bde1fe7ef132245e90b5de7fb21b1c12f5b6cadf3c730eeda839e9d9aaff1cb1a0fccee3e259c3fbe205a4e5a4a6fb2a1099637936a74137e6ca8c953b6a7d1497c0401f5474ca4a73f14260e95de1dd784232b4201da6e78ad58aeb2b5a675d1d5f6f05a3df070d8e80afe1db05883faaf84bfd5b0b0cd956365e8c050c4bf929a6af0abcc1a22fb45b26dd070657658869da1b247a93a239a3123add6470c2f9ed24ec6719841b7595c54703965d9c0f0894acde7ca2feebdfd61e242ef021303d98a7f6f7335f8fa6c3724b039a3e99545dce84fcd29430100010856ff8639c5740c82537e33cb67ec64edc9af640bc975b75d7247a226949278df33b4f75d9fcf4a4ced6356471f804cc6256a121ce8f37116f7d7f4691a0932fd0c0a601f0000000000000001dc0a5106fed0567ca18512e9500c1890c2da903254bf1cd355073c2ce80863cda5600a4a005f642f53557f149d551386bf1a4d4a3e07e8525d09adfd9e03b9ed8cfe06811b0ac94d50055b8f7b5b4cacb7d6872d716b277e0cb1e82ef55cf9c2b28a10fe734d4e785f395681cc999827dc8a7e22eb54e4cfea0285cf2c97b4e6d7d1a22568fb0b7a7a54f8d984de1b9a11be1755285a85f2ed046e2668248851f1a60eb904e1f35c85c47412946790b0099c5759476ccb82cc0b4e0f6689bb527d21fe4a273f216632b0b7454dd990e321e3aa592ca8eb63c6a840e5cd4f6f4977ef07a66345ad88cf5a257e92e9d888237930a6057f905785d1a7fd9c7176a4e3147d4fd7193e6d79a4a7775422025b33781ff3fdba1df936a0242b6f5caac10da9f17375a750c3eb21f3b6c04ba254a34791da4fc8c36d21be0243b7f2f006dd5ff8917e2a27788d92ff757dd122a36e2578e913ede433425af1b59b32ff5ce5332b9e8e46dec4245961f254b73584d9b61f19dfe7f16e2c074e6efdfa699c5554231428e54f1834abc3281dbd78f0dc871c3a38f83623aef57b9392117b4ac149e580bc095d01de6463c38ac6ef394516ef07e2e83e62de9bddc12ed489167a64c9e5d04db562cbcd4369b454b3f49ca072fe1197bd744aa30589200b8f0c797718eaaf3580a6858fe17ec3ada5debdd3dc9d767ea27dbcea0598ede9a579063157f62eacd3f603bb4e6fb187a1240eb4a205f64a6ce750ffc2674e6bc701b2707a8c2296e9807ae9ffaa07d902d4ce5ba308ad2ffcf83a83366e048503dda43f13d4940127bece0f748d178d3a7d09964ceebbcc7a6e459c621527ddb89e9f6b7c5a66c82dc129277a03fda4733dafd823a2234f722f1266b8851f6ff9757332e9a85d2d5e31a745387d6f781c296244439fd6273b46f2b8b65e2991f3ddfe0d38a7df9378e97420116196becf60e2cc910ad45abec12d1847067817ebc5890af2cb5d04c72f716788c4d32a4b6ac5801c278cd9eed23fabff2c67221c8aaf16ac30a36434e39a12044d3d79c78fedac60bad3234955c84c5d05ec9b230037d5387c57a71d620a4044298f1d34d48a5856ab66cab23c229b1fa4fbdef83bae224d2d1365fd028e520c4ab5be98e70bae76213233459f8be6c44a3163b6267b457f1d7345b1bf28171787c89c004a4a46c32857333238ebc64dc118e239da9a4fadd3f36053fb9768eed7160ce33445c711be470899d3bf54a7679e8c77648251ea1de82dd9c70a0eabe2a249781759377d85e5a1f7827989208cfd5c3cebb19e8417aa515f8e3345c7d7a1db6b5e7c6cf4a459f28e1f09664a73bd9f369b65b1f72fda9045007f04a05a19ee34a84825e658a3cef6ab03dd9e04764ceb998ee93a744e4332cb446196c840332e35b3f360f8b220068b22695d09a0c67a0604b7f8a8350a84ede706692c51b128cf34fcfa164866c4df2fdcc45e641cb7fcfda8af2de9d7adf77a6333dd3e37626b7f0818ea55335a72e965fff0c87252def5fe7c29555f35d18f98683c661ed91df6254d84812dc80a6e61686b77add346603d3ec63ff339dfd3942cc32b02f94ae3279ddda9e575a8494c0849de6f2142ea9ad5e2f1fc92444bb4433f27719a3b136e4f6c1bc7e992cc6b432fbad0c79a56286592fa9af5bfc7bb304e8e2e8b510741ab4c455c56c2cd115c1f9899fc960ba902bf680a4c071a6cbe1d4e9858148b2e1a6fd24c31d254b7b9330708e5a8266fdd1688577b65b5fc28fa3d234057812ff0f9f73c4b8bf1358739eec1f07bbcac723c4f60ac8b2cc7ed8f4d32ea2ca01368572caa0f37be5675a11323fccd46c7fabc5cdeb67d83fad371b277f3ddc15f57b8b3a474049cb06c0b3a54b0a978ea3a952cab857ca66c00875239dc43fdabbec41f6818bd2755b659b9c8af0cf232c5294ef92a241e8ef4dc7f3589badb57917ca153470de00eabe2e9828bc8d62cf999bea5142c02b9055c0bf71fc1ec9ae3f8920a6417afd0201bf64210a3fb1bae081f972184ed34c4823d48b4d6bf9b77ddfb00d11093b4a5fecbf7a2a1f284d853bd9a24f4b39327c320e3d1d2382ba8f119c8f16d682639f93d8122ed0aa4ae5f2165ee6c019618e3309823f33974c0fb25a0cfa57f9621b54b12b9ace6cb42c16c0f82fb9626d2d0f12e9601e3bc1c9c6d743f779fb1ea84fc0f3f8c54d1e8068d6ddc4a7d08ae21c3ba30837c321a9dd5e0f014480d60d42f07ac6ad03ee0c677befd947f6c3a9636aaff99e6ef55f06bf258279561c224af8af666343adc9e4efd40b48e700f0db069e9d58668ef81065aa3d1971a31f29e18706d352f0081d829bf281d890288bf29b8ad385b5109c0a49dc3f80497ea8e9253f65964f74b74ddc3c8a7435b95491d7bcadfbc1e39d320993f0bcb742b040e2217343ba48568d586a0ca86943fb1fdfaf3be99e52b90817ba2804f372e7f27113f1dc8d8598853f6dbc00bbc1e6a0573a8cc2e40db3be0a56689cf70c34f9e90b00cfc04159167de04ad37a48db3acaa874413d014f25243326171029a9f579e7b75afc88b0ca0f611877af430084e565b55e40deb827232511948140cb31569e8eb9eb7c0a1c0f91198f215e21496211d609e9af6fb9064883240e8a2f585055d9fed749b9baf4db756f98606626400b5f2870aaeb0710265c26cfea61bddf52bbaea00096e8b42d756e342dafc79afff3552aa2d24a775e405ffe937df441364d5bb62d8770af2217050c8a71d7c9e49fdacd933334b298f30fffff35de92b18661639f61921e540324d331176ba80a794096bba55297ca8edada6ad112cff7b47699079f5f485f22f3333ea9238458da208696eae80864a4d4ccf7af0011384d04ad007b8f01fa47496e6f26e5fc71c6a8fdb52d48062077dfbd2470a7ac9fc050f544162f683571443811d146284e71b1e638a6562403aee71cf7b5e9e6e9c4f418db887d94b231698dbc5ac560b653b940ed8ea3f46d88064cac4cfe01a6af638a3699c88b649b675a912660138de1b050ede4482d39a6ecb29e7fabdf59925c441b61f49f7616b999d493555978e0a2be7caf3d9fe53b285c3a4cefa0ff2ada7187ee2f03b5cc069ccb03fdbcc7133c49156cf847cffc9f19cde1a38eda37ca10fabca17a2859e96ca4bd1baef5e94af0b551b202c60a2c5c90ea46e61eedc87e3cf31b1706dee02245e2d3e65fc6a9da4ea515690f70926daafac9bb7243472d57aadc574a1aba887bc70d0f1767a87e407da8ab3a8b9e3ad225ec6f4ba404ee390a31384fa147742b710078760a8a55715c6d8fbd5683d4ebe3c629f5cd88c278693a98d76afb8ce86c6e6afbc26c0bc7a426ed16241932bf75815c8391f9345699e57930cb4c8b8bb7e3915eba9b8f3e3fc8a624ac0904fec27f487820c108dfd595df26f6139ae6e6bf822c2d02ce72b2c1e7c095a9ab3077591208c51537b008baec90f1dd52c812553b8936bc8a3353ecdfc9f0cc4ea0288c765696fb8cf33929eb78aec94333dc814de874628f994b3524bf24c054f8d16dd75cc61e0860a33a12632bdedfd03b67cebde3fa178c7f978b4de6a31cd7924056e581c70000077000000
```

Result

```text
7b8236c687e5424f65662fecce4e07523054e89a05b731ef05b6c0235ee5ec04
```

## sendtoaddress

The `sendtoaddress` RPC spends an amount to a given address.

The version in Elements is similar to the Bitcoin Core [`sendtoaddress`
RPC][bcc sendtoaddress] but defaults to using Confidential Transactions
(CT) and can send other assets besides bitcoin.
Element's API changes are emphasized in bold.

*Parameter #1---to address*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   To Address

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   A P2PKH or P2SH address to pay

   </td>

  </tr>
 </tbody>
</table>


*Parameter #2---amount to spend*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Amount

   </td>

   <td markdown="span">

   number (**[value amount][]**)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The amount to spent

   </td>

  </tr>
 </tbody>
</table>


*Parameter #3---a comment*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Comment

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   A locally-stored (not broadcast) comment assigned to this transaction.  Default is no comment

   </td>

  </tr>
 </tbody>
</table>


*Parameter #4---a comment about who the payment was sent to*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Comment To

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   A locally-stored (not broadcast) comment assigned to this transaction.  Meant to be used for describing who the payment was sent to. Default is no comment

   </td>

  </tr>
 </tbody>
</table>


*Parameter #5---automatic fee subtraction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Subtract Fee From Amount

   </td>

   <td markdown="span">

   boolean

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The fee will be deducted from the amount being sent. The recipient will receive less bitcoins than you enter in the amount field. Default is `false`

   </td>

  </tr>
 </tbody>
</table>


**Parameter #6---asset to spend**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **Asset identifier**

   </td>

   <td markdown="span">

   **string**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The asset identifier or label of the asset to send.  Defaults to `bitcoin`**

   </td>

  </tr>
 </tbody>
</table>

  
**Parameter #7---whether to allow unblinded outputs**

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   **Allow blind fails**

   </td>

   <td markdown="span">

   **bool**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **If `true`, the transaction will be broadcast even if not all outputs are blinded using CT.  If `false` (the default), an error will be printed if any outputs are unblinded**

   </td>

  </tr>
 </tbody>
</table>


*Result---a TXID of the sent transaction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The TXID of the sent transaction, encoded as hex in RPC byte order

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli sendtoaddress CTEo5b2uQnVjuu78dACjQJHsxXwsuUxsbjeYXHsNHRwbVjk48ibnWaLcrw46udrS4RwjTkwrV5JczhiS 0.1
```

Result:

```text
4fdd4e1e65872d6ab9a25c0b1121159b72994d6503a036fcee073569f47dfdd1
```

## sendtomainchain

The `sendtomainchain` RPC sends bitcoins from your sidechain wallet to an
address on the mainchain.

*Parameter #1---mainchain address*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Address</td>
   <td>string (base58)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The mainchain address to which the the bitcoins should
   be sent.</td>
  </tr>
 </tbody>
</table>

*Parameter #2---amount to send to the mainchain*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Amount</td>
   <td>number (amount)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The amount of bitcoins to send to the mainchain address specified in the previous parameter</td>
  </tr>
 </tbody>
</table>

*Parameter #3---automatic fee subtraction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Subtract Fee From Amount</td>
   <td>boolean</td>
   <td>Optional (0 or 1)</td>
   <td>The fee will be deducted from the amount being sent. The recipient will receive less bitcoins than you enter in the amount field. Default is <code>false</code></td>
  </tr>
 </tbody>
</table>

*Result---txid of the sidechain transaction*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The txid of the sidechain transaction requesting
   that functionaries spend the specified amount of bitcoins to the
   specified mainchain address</td>
  </tr>
 </tbody>
</table>

*Example*

```bash
elements-cli sendtomainchain mgWEy4vBJSHt3mC8C2SEWJQitifb4qeZQq 1
```

Result:

```text
5e9a8c204eb1078de34e5e2c4dee2378168cb37038179d33667a2c74299b6711
```

## signblock

The `signblock` RPC checks a proposed block for validity and then signs it.

*Parameter #1---the proposed block*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Proposed block</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The hex-encoded serialized block to validate and
   sign</td>
  </tr>
 </tbody>
</table>

*Result*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Signature</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The hex-encoded signature for the block from this daemon.</td>
  </tr>
 </tbody>
</table>

*Example*

```bash
block=$( elements-cli getnewblockhex )
elements-cli signblock $block
```

Result:

```text
0047304502210086d3c7191ca37e09640d4f1b3237be3493936dd68279115bc5b988d19a14e5640220193ec3e9a77f974a738ba3f7745e65e253f41ea1fec5a61b87ce0038d00bcf21
```

## testproposedblock

The `testproposedblock` tests a proposed block to see if it is valid and
if extends the best block chain.

*Parameter #1---the proposed block*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Proposed block</td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The hex-encoded serialized block to validate and
   sign.</td>
  </tr>
 </tbody>
</table>

*Result---null on success; error on failure*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>null</td>
   <td>Required<br />(exactly 1)</td>
   <td markdown="block">
   
   A `null` if the block is either currently valid (has signatures)
   or would be valid if signed.  An
   error if the block is not valid, is already part of the best block
   chain, or does not extend the best block
   chain.
   
   </td>
  </tr>
 </tbody>
</table>

*Example*

A valid regtest block not requiring any signatures:

```bash
block=$( elements-cli -regtest getnewblockhex )
elements-cli -regtest testproposedblock $block
```
Result: none (null) since the block is valid.

A valid regtest block already on the best block chain:

```bash
block=$( elements-cli -regtest getblock $( elements-cli -regtest getbestblockhash ) false )
elements-cli -regtest testproposedblock $block
```

Result:

```text
error code: -25
error message:
already have block
```

## tweakfedpegscript

The `tweakfedpegscript` RPC lets you tweak a tx script for the federated peg.

*Parameter #1---the script to tweak the fedpegscript with*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td>Claim script</td>
   <td>string</td>
   <td>Required<br />(exactly 1)</td>
   <td>Script to tweak the fedpegscript with. For example obtained as a result of getpeginaddress.</td>
  </tr>
 </tbody>
</table>

*Result---the statistics for the given block*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="block">
   
   `result`
   
   </td>
   <td>object</td>
   <td>Required<br />(exactly 1)</td>
   <td>An object containing the results of the
   operation</td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`script`
   
   </td>
   <td>string (hex)</td>
   <td>Required<br />(exactly 1)</td>
   <td>The fedpegscript tweaked with claim_script</td>
  </tr>

  <tr>
   <td markdown="block">
   
   →<br>`address`
   
   </td>
   <td>string</td>
   <td>Required<br />(exactly 1)</td>
   <td>The address corresponding to the tweaked fedpegscript</td>
  </tr>
 </tbody>
</table>

## validateaddress

The `validateaddress` RPC returns information about the given address.

The version in Elements is similar to the Bitcoin Core
[`validateaddress` RPC][bcc validateaddress] but also returns
Elements-specific information, such as confidential keys.  Element's API
changes are emphasized in bold.

*Parameter #1---a P2PKH or P2SH address*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   Address

   </td>

   <td markdown="span">

   string (base58)

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   The P2PKH or P2SH address to validate, encoded in base58check format

   </td>

  </tr>
 </tbody>
</table>


*Result---information about the address*

<table>
 <thead>
  <tr>
   <th>Name</th>
   <th>Type</th>
   <th>Presence</th>
   <th>Description</th>
  </tr>
 </thead>
 <tbody>
  <tr>
   <td markdown="span">

   `result`

   </td>

   <td markdown="span">

   object

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   Information about the address

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`isvalid`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Required<br>(exactly 1)

   </td>

   <td markdown="span">

   Set to `true` if the address is a valid P2PKH or P2SH address; set to `false` otherwise

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`address`

   </td>

   <td markdown="span">

   string (base58)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The address given as parameter

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`scriptPubKey`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The hex-encoded scriptPubKey generated by the address

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→<br>`confidential_key`**

   </td>

   <td markdown="span">

   **string (hex)**

   </td>

   <td markdown="span">

   **Required<br>(exactly 1)**

   </td>

   <td markdown="span">

   **The confidentiality pubkey for the address.  If there is none, this is an empty string**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→<br>`unconfidential`**

   </td>

   <td markdown="span">

   **string (base58)**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The non-confidential form of this address.**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`ismine`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Set to `true` if the address belongs to the wallet; set to false if it does not.  Only returned if wallet support enabled

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`iswatchonly`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Set to `true` if the address is watch-only.  Otherwise set to `false`.  Only returned if address is in the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   **→<br>`confidential`**

   </td>

   <td markdown="span">

   **string (base58)**

   </td>

   <td markdown="span">

   **Optional<br>(0 or 1)**

   </td>

   <td markdown="span">

   **The confidential form of this address.  Only returned if this is a local wallet key and you passed in the unconfidential form**

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`isscript`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Set to `true` if a P2SH address; otherwise set to `false`.  Only returned if the address is in the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`script`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Only returned for P2SH addresses belonging to this wallet. This is the type of script:<br> `pubkey` for a P2PK script inside P2SH<br> `pubkeyhash` for a P2PKH script inside P2SH<br> `multisig` for a multisig script inside P2SH<br> `nonstandard` for unknown scripts

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`hex`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Only returned for P2SH addresses belonging to this wallet.  This is the redeem script encoded as hex

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`addresses`

   </td>

   <td markdown="span">

   array

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Only returned for P2SH addresses belonging to the wallet.  A P2PKH addresses used in this script, or the computed P2PKH addresses of any pubkeys in this script.  This array will be empty for `nonstandard` script types

   </td>

  </tr>
  <tr>
   <td markdown="span">

   → →<br>Address

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or more)

   </td>

   <td markdown="span">

   A P2PKH address

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`sigrequired`

   </td>

   <td markdown="span">

   number (int)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Only returned for multisig P2SH addresses belonging to the wallet.  The number of signatures required by this script

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`pubkey`

   </td>

   <td markdown="span">

   string (hex)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The public key corresponding to this address.  Only returned if the address is a P2PKH address in the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`iscompressed`

   </td>

   <td markdown="span">

   bool

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   Set to `true` if a compressed public key or set to `false` if an uncompressed public key.  Only returned if the address is a P2PKH address in the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`account`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   *Deprecated: will be removed in a later version of Bitcoin Core*<br><br>The account this address belong to.  May be an empty string for the default account.  Only returned if the address belongs to the wallet

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`hdkeypath`

   </td>

   <td markdown="span">

   string

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The HD keypath if the key is HD and available

   </td>

  </tr>
  <tr>
   <td markdown="span">

   →<br>`hdmasterkeyid`

   </td>

   <td markdown="span">

   string (hash160)

   </td>

   <td markdown="span">

   Optional<br>(0 or 1)

   </td>

   <td markdown="span">

   The Hash160 of the HD master public key

   </td>

  </tr>
 </tbody>
</table>


*Example*

```bash
elements-cli validateaddress 2deqf58mU3Aa6QEPpqx4RafxTdBsH7qVhTo
```

Result:

```json
{
  "isvalid": true,
  "address": "2deqf58mU3Aa6QEPpqx4RafxTdBsH7qVhTo",
  "scriptPubKey": "76a9143b5e2c72658c005b30c80d78e1c2e8c1630e79e288ac",
  "confidential_key": "",
  "unconfidential": "2deqf58mU3Aa6QEPpqx4RafxTdBsH7qVhTo",
  "ismine": true,
  "iswatchonly": false,
  "confidential": "CTEnUrAxbWK3HN562U1D6FmLsS8yYKXJVnWQQGp8zzBRzc5amJBNfKehvRD73Fc3guxDYsoF7bcMQRb9",
  "isscript": false,
  "pubkey": "03301f612dcf7fae85149d2b1d5efa575e53569025f165a6074ce09e21915e81f9",
  "iscompressed": true,
  "account": "",                                                                                            "hdkeypath": "m/0'/0'/7'",                                                                                "hdmasterkeyid": "12d5270d68f38b7d535247ac6885e058ed7cb19d"                                             }      
```


[bcc createrawtransaction]: https://bitcoin.org/en/developer-reference#createrawtransaction
[confidential assets]: https://blockstream.com/bitcoin17-final41.pdf

# Glossary

For terms common to Bitcoin and Elements, please see the [Bitcoin.org
technical glossary][].

[Bitcoin.org technical glossary]: https://bitcoin.org/en/developer-glossary

*Alphabetical order:*

## Blinded output

[blinded output]: #blinded-output

A Confidential Transaction (CT) output whose output amounts and asset
types are only known to those with the blinding factors---usually just the
payer and the receiver.

## Entropy

[entropy]: #entropy

See definition 18 of the [Confidential Assets][] paper.

## Reissuance tokens

[reissuance token]: #reissuance-tokens
[reissuance tokens]: #reissuance-tokens

When an asset is first issued, an option is available to allow
"reissuing" the asset---creating more of the token.  If the option is
not exercised, the asset supply can only stay the same or decrease.

If the option is exercised, a reissuance token will be created.  The
reissuance token has a value, but the value is not used when reissuing
an asset, so you may choose any value down to 0.00000001.

For details, please see definitions 21 and 22 of the [Confidential Assets][] paper.

## Value amount

[value amount]: #value-amount

Both Bitcoin Core and Elements allow you to specify value amounts used
for Bitcoins and Elements assets as either a number (float) or string.
Strings are accepted because many JSON libraries have difficulty
correctly handling the high-precision values used by Bitcoin and
Elements, where the minimum value is 0.00000001.

[raw transaction]: https://bitcoin.org/en/developer-reference#raw-transaction-format

[bcc createrawtransaction]: https://bitcoin.org/en/developer-reference#createrawtransaction
[bcc decoderawtransaction]: https://bitcoin.org/en/developer-reference#decoderawtransaction
[bcc getbalance]: https://bitcoin.org/en/developer-reference#getbalance
[bcc getrawtransaction]: https://bitcoin.org/en/developer-reference#getrawtransaction
[bcc gettransaction]: https://bitcoin.org/en/developer-reference#gettransaction
[bcc getunconfirmedbalance]: https://bitcoin.org/en/developer-reference#getunconfirmedbalance
[bcc getwalletinfo]: https://bitcoin.org/en/developer-reference#getwalletinfo
[bcc listtransactions]: https://bitcoin.org/en/developer-reference#listtransactions
[bcc listunspent]: https://bitcoin.org/en/developer-reference#listunspent
[bcc sendrawtransaction]: https://bitcoin.org/en/developer-reference#sendrawtransaction
[bcc sendtoaddress]: https://bitcoin.org/en/developer-reference#sendtoaddress
[bcc validateaddress]: https://bitcoin.org/en/developer-reference#validateaddress

[combineblocksigs]: #combineblocksigs
[getnewblockhex]: #getnewblockhex
[testproposedblock]: #testproposedblock
[blindrawtransaction]: #blindrawtransaction
[createrawtransaction]: #createrawtransaction
[decoderawtransaction]: #decoderawtransaction
[rawblindrawtransaction]: #rawblindrawtransaction
[sendrawtransaction]: #sendrawtransaction
[createblindedaddress]: #createblindedaddress
[getblockstats]: #getblockstats
[getrawtransaction]: #getrawtransaction
[validateaddress]: #validateaddress
[tweakfedpegscript]: #tweakfedpegscript
[claimpegin]: #claimpegin
[destroyamount]: #destroyamount
[dumpassetlabels]: #dumpassetlabels
[dumpblindingkey]: #dumpblindingkey
[dumpissuanceblindingkey]: #dumpissuanceblindingkey
[getbalance]: #getbalance
[getpeginaddress]: #getpeginaddress
[gettransaction]: #gettransaction
[getunconfirmedbalance]: #getunconfirmedbalance
[getwalletinfo]: #getwalletinfo
[importissuanceblindingkey]: #importissuanceblindingkey
[issueasset]: #issueasset
[listissuances]: #listissuances
[listtransactions]: #listtransactions
[listunspent]: #listunspent
[reissueasset]: #reissueasset
[sendtoaddress]: #sendtoaddress
[sendtomainchain]: #sendtomainchain
[signblock]: #signblock

[bitcoin.org rpc quick reference]: https://bitcoin.org/en/developer-reference#rpc-quick-reference
