This document proposes new opcodes to be added to the elements network along with the taproot upgrade. The new tapscript `OP_SUCCESS` opcodes allow introducing new opcodes more cleanly than through `OP_NOP`. In this document, we propose modifying the following `OP_SUCCESS`
to have the additional semantics. We use opcodes serially `OP_SUCCESS196`, `197`... in order
to avoid conflict with bitcoin potentially using `OP_SUCESSSx`(assuming bitcoin uses those serially based on availability). The initial version of this document had additional opcodes(`OP_FOR`, multi-byte opcodes) has since been updated to this current version in favor of application complexity.

# Resource Limits

## Changes in Taproot(Including Standardness Policy Changes)
Taproot already increases a lot of resource limitations from segwitv0, so there is no additional need to alter any of those. In particular, from BIP 342

- Script size limit: the maximum script size of 10000 bytes does not apply. Their size is only implicitly bounded by the block weight limit.
- Non-push opcodes limit: The maximum non-push opcodes limit of 201 per script does not apply.
- Sigops limit: The sigops in tapscripts do not count towards the block-wide limit of 80000 (weighted). Instead, there is a per-script sigops budget. The budget equals 50 + the total serialized size in bytes of the transaction input's witness (including the CompactSize prefix). Executing a signature opcode (`OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, or `OP_CHECKSIGADD`) with a non-empty signature decrements the budget by 50. If that brings the budget below zero, the script fails immediately.
- Stack + altstack element count limit: The existing limit of 1000 elements in the stack and altstack together after every executed opcode remains. It is extended to also apply to the size of the initial stack.
- Stack element size limit: The existing limit of maximum 520 bytes per stack element remains, during the stack machine operations. There is an additional policy rule limiting the initial push size to `80` bytes.
# New Opcodes for additional functionality:

1. **Streaming Opcodes for streaming hashes**: There is an existing limitation of `MAX_SCRIPT_ELEMENT_SIZE`(520 bytes) because of which we cannot operate hash functions like `OP_SHA256` on messages more than 520 bytes. This allows hashing on more than 520 bytes while still preserving the existing security against resource exhaustion attacks. The proposal for this  by Russell O'Connor can be found in the description [here](https://github.com/ElementsProject/elements/pull/817).
   1. Define `OP_SUCCESS196` as `OP_SHA256INITIALIZE` which pops a bytestring and push SHA256 context creating by adding the bytestring to the initial SHA256 context.
   1. Define `OP_SUCCESS197` as `OP_SHA256UPDATE` which first pops a bytestring followed by another pop for SHA256 context and pushes an updated context by adding the bytestring to the data stream being hashed.
   1. Define `OP_SUCCESS198` as `OP_SHA256FINALIZE` which first pops a pops a bytestring followed by another pop for SHA256 context and finally pushes a SHA256 hash value after adding the bytestring and completing the padding.


2. **Transaction Introspection codes**: Transaction introspection is already possible in elements script by use of `OP_CHECKSIGFROMSTACKVERIFY`, however the current solutions are really expensive in applications like [covenants](https://github.com/sanket1729/covenants-demo). Therefore, we are not adding any new functionality by supporting introspection, only making it easier to use. The warning still remains the same as with covenants, if the user is inspecting data from parts of the transaction that are not signed, the script can cause unexpected behavior.
For opcodes that inspect data that is not committed in sighash, introspection is safe because any changes to the witness data would cause wtxid to change and it would revalidate the tx again. For pegin inputs, the asset/value/script information will be one from the parent chain.
   - Transaction input introspection opcodes:
      1. Define `OP_SUCCESS199` as `OP_INSPECTINPUTOUTPOINT`: Pop a `CScriptNum` input index `idx` and push the outpoint as a tuple. First push the `txid`(32) of the `prev_out`, followed by a 4 byte push of `vout` followed by a push for the outpoint_flag(1) as defined in [Modified BIP-341 SigMsg for Elements](https://gist.github.com/roconnor-blockstream/9f0753711153de2e254f7e54314f7169).
      1. Define `OP_SUCCESS200` as `OP_INSPECTINPUTASSET`: Pop a `CScriptNum` input index `idx` and push the `nAsset` onto the stack as two elements. The first push the assetID(32), followed by the prefix(1)
      1. Define `OP_SUCCESS201` as `OP_INSPECTINPUTVALUE`: Pop a `CScriptNum` input index `idx` and push the `nValue` as a tuple, value(8 byte LE, 32) followed by prefix(1),
      1. Define `OP_SUCCESS202` as `OP_INSPECTINPUTSCRIPTPUBKEY`: Pop a `CScriptNum` input index `idx` and push the following depending the type of scriptPubkey:
         - If the scriptPubKey is not a native segwit program, push a single sha256 hash of the scriptPubKey on stack top. Next, push a `CScriptNum(-1)` to indicate a non-native segwit scriptPubKey.
         - If the scriptPubKey is a native segwit program, push the witness program(2-40) followed by a push for segwit version(0-1).
      1. Define `OP_SUCCESS203` as `OP_INSPECTINPUTSEQUENCE`: Pop a `CScriptNum` input index `idx` and push the `nSequence`(4) as little-endian number.
      1. Define `OP_SUCCESS204` as `OP_INSPECTINPUTISSUANCE`: Pop a `CScriptNum` input index `idx` and push the assetIssuance information if the asset has issuance, otherwise push an empty vector. Asset Issuance information is pushed as follows
         - Push `nInflationKeys` as tuple, value(8 byte LE, 32) followed by push for prefix(1). In case `nInflationKeys` is null, push a 8 byte LE `0` followed by a push for explicit prefix(1).
         - Push `nAmount` as a tuple, value(8 byte LE, 32) followed by a push for prefix(1). In case `nAmount` is null, push a 8 byte LE `0` followed by a push for explicit prefix(1).
         - Push 32 byte `assetEntropy`
         - Push 32 byte `assetBlindingNonce`
   - Define `OP_SUCCESS205` as `OP_PUSHCURRENTINPUTINDEX` that pushes the current input index as `CScriptNum`. This can be used in conjunction with input introspection opcodes for inspecting current input.
   - Output introspection opcodes:
      1. Define `OP_SUCCESS206` as `OP_INSPECTOUTPUTASSET`: Pop a `CScriptNum` input index `idx` and push the `nAsset` as a tuple, first push the assetID(32), followed by the prefix(1)
      1. Define `OP_SUCCESS207` as `OP_INSPECTOUTPUTVALUE`: Pop a `CScriptNum` input index `idx` and push the `nValue` as a tuple, value(8 byte LE, 32) followed by prefix
      1. Define `OP_SUCCESS208` as `OP_INSPECTOUTPUTNONCE`: Pop a `CScriptNum` input index `idx` and push the `nNonce`(33) onto the stack. If the nonce is null, push an empty vector onto the stack.
      1. Define `OP_SUCCESS209` as `OP_INSPECTOUTPUTSCRIPTPUBKEY`: Pop a `CScriptNum` input index `idx` and push the scriptPubkey onto the stack.
         - If the scriptPubKey is not a native segwit program, push a single sha256 hash of the scriptPubKey on stack top. Next, push a `CScriptNum(-1)` to indicate a non-native segwit scriptPubKey.
         - If the scriptPubKey is a native segwit program, push the witness program(2-40) followed by a push for segwit version(0-1).
   - Transaction introspection opcodes:
      1. Define `OP_SUCCESS210` as `OP_INSPECTVERSION`: Push the nVersion(4) as little-endian.
      1. Define `OP_SUCCESS211` as `OP_INSPECTLOCKTIME`: Push the nLockTime(4) as little-endian.
      1. Define `OP_SUCCESS212` as `OP_INSPECTNUMINPUTS`: Push the number of inputs as CScriptNum
      1. Define `OP_SUCCESS213` as `OP_INSPECTNUMOUTPUTS`: Push the number of outputs as CScriptNum
      1. Define `OP_SUCCESS214` as `OP_TXWEIGHT`: Push the transaction weight (8) as little-endian

3. **Signed 64-bit arithmetic opcodes:** Current operations on `CScriptNum` as limited to 4 bytes and are difficult to compose because of minimality rules. having a fixed width little operations with 8 byte signed operations helps doing calculations on amounts which are encoded as 8 byte little endian.
   - When dealing with overflows, we explicitly return the success bit as a `CScriptNum` at the top of the stack and the result being the second element from the top. If the operation overflows, first the operands are pushed onto the stack followed by success bit. \[`a_second` `a_top`\] overflows, the stack state after the operation is \[`a_second` `a_top` `0`\] and if the operation does not overflow, the stack state is \[`res` `1`\].
   - This gives the user flexibility to deal if they script to have overflows using `OP_IF\OP_ELSE` or `OP_VERIFY` the success bit if they expect that operation would never fail.
When defining the opcodes which can fail, we only define the success path, and assume the overflow behavior as stated above.
   1. Define `OP_SUCCESS215` as `OP_ADD64`: pop the first number(8 byte LE) as `b` followed another pop for `a`(8 byte LE). Push a + b onto the stack. Push 1 `CScriptNum` if there is no overflow. Overflow behavior defined above.
   1. Define `OP_SUCCESS216` as `OP_SUB64`: pop the first number(8 byte LE) as `b` followed another pop for `a`(8 byte LE). Push a - b onto the stack. Push 1 `CScriptNum` if there is no overflow. Overflow behavior defined above.
   1. Define `OP_SUCCESS217` as `OP_MUL64`: pop the first number(8 byte LE) as `b` followed another pop for `a`(8 byte LE). Push `a*b` onto the stack. Push 1 `CScriptNum` if there is no overflow. Overflow behavior defined above.
   1. Define `OP_SUCCESS218` as `OP_DIV64`: pop the first number(8 byte LE) as `b` followed another pop for `a`(8 byte LE). First push remainder `a%b`(must be non-negative and less than |b|) onto the stack followed by quotient(`a//b`) onto the stack. If `b==0` or `a = -2<sup>63</sup> && b = -1`, treat as overflow as defined above. Push 1 `CScriptNum` if there is no overflow.
   1. Define `OP_SUCCESS219` as `OP_NEG64`: pop the first number(8 byte LE) as `a` and pushes `-a` on the stack top. If the number is `-2<sup>63</sup>`(`int64_min`) treat as overflow, otherwise push `CScriptNum` 1 to indicate no overflow.
   1. Define `OP_SUCCESS220` as `OP_LESSTHAN64`(cannot fail!): pop the first number(8 byte LE) as `b` followed another pop for `a`(8 byte LE). Push ` a < b`.
   1. Define `OP_SUCCESS221` as `OP_LESSTHANOREQUAL64`(cannot fail!): pop the first number(8 byte LE) as `b` followed another pop for `a`(8 byte LE). Push ` a <= b`.
   1. Define `OP_SUCCESS222` as `OP_GREATERTHAN64`(cannot fail!): pop the first number(8 byte LE) as `b` followed another pop for `a`(8 byte LE). Push ` a > b`.
   1. Define `OP_SUCCESS223` as `OP_GREATERTHANOREQUAL64`(cannot fail!): pop the first number(8 byte LE) as `b` followed another pop for `a`(8 byte LE). Push ` a >= b`.
   1. Support for binary operations is already available via `OP_AND`, `OP_OR`, `OP_INVERT` and `OP_XOR`

4. **Conversion opcodes:** Methods for conversion from `CScriptNum` to `8-byte LE`, `4-byte LE`.
   1. Define `OP_SUCCESS224` as `OP_SCIPTNUMTOLE64`: pop the stack as minimal `CSciptNum`, push 8 byte signed LE corresponding to that number.
   1. Define `OP_SUCCESS225` as `OP_LE64TOSCIPTNUM`: pop the stack as a 8 byte signed LE. Convert to `CScriptNum` and push it, abort on fail.
   1. Define `OP_SUCCESS226` as `OP_LE32TOLE64`: pop the stack as a 4 byte _unsigned_ LE. Push the corresponding 8 byte _signed_ LE number. Cannot fail, useful for operating of version, locktime, sequence, number of inputs, number of outputs, weight etc.

5. **Crypto**: In order to allow more complex operations on elements, we introduce the following new crypto-operators. Each opcode counts as 50 towards the sigops budget.
   1. Define `OP_SUCCESS227` as `OP_ECMULSCALARVERIFY`which pops three elements from stack as described below: 1) a 32 byte big endian, unsigned scalar `k`. 2) Compressed EC point `P`, and 3) compressed EC point `Q`. Abort if `P`, `Q` is invalid or `k` is not 32 bytes and outside of secp256k1 curve order. Abort if `Q != k*P`.
   1. Define `OP_SUCCESS228` as `OP_TWEAKVERIFY` with the following semantics: Pop the three elements as: 1) 32 byte X-only internal key `P`, 2) a 32 byte big endian, unsigned scalar `k`, and 3) 33 byte compressed point `Q`. Abort if `P`, `Q` is invalid or `k` is not 32 bytes and outside of secp256k1 curve order. Abort if `Q != P + k*G` where `G` is the generator for secp256k1.

6. **Changes to existing Opcodes**:
   - Add `OP_CHECKSIGFROMSTACK` and `OP_CHECKSIGFROMSTACKVERIFY` to follow the semantics from bip340 when witness program is v1. In more detail, the opcodes pops three elements stack 1) 32 byte `pk` Xonly public key 2) Variable length message `msg` and 3) 64 byte Schnorr signature `sig`. Let `res = BIP340_verify(pk, msg, sig)` where `BIP340_verify` is defined for elements [here](https://github.com/ElementsProject/elements/blob/master/doc/taproot-sighash.mediawiki). If opcode is `OP_CHECKSIGFROMSTACKVERIFY`, abort if the verification fails.
   - If the opcode is `OP_CHECKSIGFROMSTACK`, push `0` if an empty sig is provided and push `1` if the verification succeeds. Abort if provided with a non-empty signature that fails the verification. Both `OP_CHECKSIGFROMSTACK` and `OP_CHECKSIGFROMSTACKVERIFY` count as 50 towards the sigops budget.
   - Abort if the pubkey is empty, but allow success for non-empty non-32byte keys for future extension of tagged keys.

# General tips, suggestions and quirks for using Taproot opcodes

- In order to inspect the current input, `OP_PUSHCURRENTINPUTINDEX` can be used in combination with `OP_INSPECTINPUTXX` to obtain information about input being spent on stack
- The input nNonce field is not consistently stored in elements UTXO database. Therefore, it is not covered in sighash or `wtxid` and hence introspecting it is not possible.
- Coversion opcodes can be used be used to convert ScriptNums/LE32 nums to LE64 for operations.