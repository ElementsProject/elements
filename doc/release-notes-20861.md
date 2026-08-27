Wallet and signing
------------------

- ELEMENTS: The default sighash used when signing pre-Taproot (legacy and
  segwit v0) inputs now commits to the output rangeproofs on chains where
  `SIGHASH_RANGEPROOF` is active (i.e. dynafed is active). Concretely, when no
  sighash type is specified, the wallet, the `signrawtransactionwithkey` /
  `signrawtransactionwithwallet` / `walletprocesspsbt` / `descriptorprocesspsbt`
  RPCs, and `elements-tx` now default to `SIGHASH_ALL|RANGEPROOF` instead of
  `SIGHASH_ALL`. This removes the previous default's third-party rangeproof
  (witness) malleability and matches the rangeproof coverage that Taproot inputs
  already have.

  The new default is gated on activation: node-backed signing checks live
  dynafed activation at the current tip, while the offline `elements-tx` tool
  gates on the selected chain's parameters (only chains where dynafed is always
  active). On chains where `SIGHASH_RANGEPROOF` is not active, the historical
  `SIGHASH_ALL` default is used so that signatures remain standard and valid.
  Taproot signing is unaffected: the `SIGHASH_RANGEPROOF` bit is ignored for
  Taproot (which always commits to rangeproofs). Users can still request any
  specific sighash type explicitly to override the default.

Updated RPCs
------------

- Due to [BIP 350](https://github.com/bitcoin/bips/blob/master/bip-0350.mediawiki)
  being implemented, behavior for all RPCs that accept addresses is changed when
  a native witness version 1 (or higher) is passed. These now require a Bech32m
  encoding instead of a Bech32 one, and Bech32m encoding will be used for such
  addresses in RPC output as well. No version 1 addresses should be created
  for mainnet until consensus rules are adopted that give them meaning
  (e.g. through [BIP 341](https://github.com/bitcoin/bips/blob/master/bip-0341.mediawiki)).
  Once that happens, Bech32m is expected to be used for them, so this shouldn't
  affect any production systems, but may be observed on other networks where such
  addresses already have meaning (like signet).
