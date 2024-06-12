# Asset Contracts Version 1 (CBOR format)

## Overview

This document describes:
* A brief history of Elements asset contracts
* A new format for user-supplied asset contracts, based on the RFC 7049 CBOR standard
* Some other tools and interfaces for dealing with assets and asset contracts

The document `asset-values-rpc.md` contains:
* Changes to the way asset values are handled in the Elements RPC interface, to
  cleanly handle assets with different levels of precision (i.e., number of digits after the
  decimal point)

## Glossary

* Asset issuer: The party issuing the asset and writing the asset contract (and the software used for producing and registering the asset contract.)
* Asset (contract) consumer: The party using the information contained in the asset contract (and the software used for this)
* Issuance transaction: The transaction in which a new asset is initially defined.
* Reissuance token: A special asset type, created (optionally) along with another asset, and which can be used to create new units of that asset.
* Atom: The smallest unit of an asset (equivalent to a Satoshi in Bitcoin.)
* Precision: The number of digits after the decimal point in the "decimal" representation of an asset value (e.g. 8 for Bitcoin).
* Known asset: An asset for which a given consumer has seen/processed a valid version 1 contract.
* Whitelisted asset: An asset for which a given consumer has the contract data from an out-of-band source.

## History and motivation

When creating an asset in Elements, some user-supplied data -- the "Ricardian contract" -- is
included in the hash that defines the asset ID. This allows for an asset issuance transaction to
commit to some external information that defines what the asset is.

Although the Elements blockchain consensus (and standardness) rules do not enforce any structure
to the user-supplied data, it was by convention
the hash of a JSON document, with certain fields defining various aspects of the asset
such as its name, issuer, ticker symbol, and precision. This was "version 0" of the asset contract
format (indicated by '"version": 0' in the JSON object.) For example:

```
{
    "entity": {
        "domain": "store.blockstream.com"
    },
    "issuer_pubkey": "023c239fd39ae5fc8b88454fe36cae6a65a10c5b637a28dbcbc423d1e7f3bcc25e",
    "name": "Hat",
    "nonce": "171716",
    "precision": 0,
    "ticker": "HAT",
    "version": 0
}
```

(The example above is given in a pretty-printed style, but the contract is hashed without whitespace.)

The precision, in particular, affects the
interpretation of the asset; assets are represented on the blockchain in smallest-unit "atoms", but the definition of
"one whole unit" (which we will call a "decimal unit") of the asset is set by the precision.
(For example, in the case of Bitcoin the precision is 8, meaning 10<sup>8</sup>
Satoshis per Bitcoin.) In order to display or accept user-friendly asset values, it is necessary
to know the asset precision.

Elements has also been agnostic to how contracts themselves are distributed off-chain. In Liquid, the
contracts have been stored in a registry from which users can retrieve them, and validate them against
the on-chain commitment.

There are several issues with this scheme:
* Hardware wallets may not be able to parse JSON, but they need to know the precision.
* Elements RPC expresses values in decimal units, not atoms/Satoshis. Elements currently ignores the precision entirely, and treats all assets
  like Bitcoin, with an assumed precision of 8. This is dangerously misleading for assets whose precision is not 8, and
  confusing for reissuance tokens (which are assets with no notion of precision.)
* CLI and RPC users may not want to add a hard dependency on an external online registry to obtain the precision of assets.
* JSON-based contracts are much larger than necessary, which is a problem for on-chain approaches
  to solving the distribution problem.

## Solution

Our overall approach to solving the problems above:
* Switch contracts from JSON to (a subset of) CBOR, a compact binary object representation which is a superset
  of JSON (defined in RFC 7049).
* For ease of distribution, define a standard for on-chain distribution of contracts in `OP_RETURN` outputs.
* Everything about this standard is an optional layer on top of the Elements chain; no consensus or
  standardness rule of Elements will require its use.

* Elements Core RPC changes:
  * Retrieve and store asset contracts from `OP_RETURN` outputs in issuance transactions.
    * Validate against the contract hash in the issuance, and against the contract well-formedness
      rules (which are defined below.)
    * Maintain a whitelist of known assets with no on-chain contract, including Bitcoin.
    * Provide new RPCs for working with (providing, retrieving) asset contracts.
  * Significant changes to the handling of asset values in RPC calls, detailed in `asset-values-rpc.md`.

* Elements GUI changes:
  * Display, and accept user entry of, decimal values of known and whitelisted assets (using their contract-specified or whitelist-specified precision.)
  * Do not display, or accept user entry of, values for other assets.
  * Treat reissuance tokens specially, as always having precision 0 (that is, atomic indivisible units.)

* Registry changes:
  * Accept registraton of CBOR contracts.
  * Provide for verification of CBOR contracts against the spec.
  * Stop accepting new JSON contracts (perhaps with a "deprecation phase" where they are discouraged somehow).
  * For convenience, allow retrieval of contracts either in CBOR format, or converted to JSON as described later in this document.

* Tooling:
  * `rust-elements`: support creating, inspecting, and verifying both old and new asset contracts
  * `hal-elements`: support creating, inspecting, and verifying both old and new asset contracts
  * TBD: Usable tooling for registering assets with the registry, and issuing assets on the blockchain.
  * For users needing generic tooling for working with CBOR data: https://github.com/intel/tinycbor, http://cbor.me/

## Contract format

A version 1 asset contract consists of: a single-byte version field (which must be 1), followed by a CBOR-encoded array with 3 elements:
* The precision, encoded as an unsigned integer from 0 to 8.
* The ticker, encoded as a string, 3-5 characters from the character set "[a-zA-Z.-]" (that is, upper and lowercase letters, dot, and dash.)
* A map containing other fields, all of which are OPTIONAL:
  * (The field names `"precision"`, `"ticker"`, and `"entity"` are reserved for backwards compatibility, and may not be used.)
  * `"name"`, a string containing ASCII characters, length 1 to 255 (inclusive)
  * `"issuer_pubkey"`, a byte-string containing a secp256k1 public key in compressed form.
  * `"domain"`, a domain name belonging to the issuer
  * Any other fields desired by the issuer, subject to the restrictions below.
    * For issuers who wish to make use of the onchain contract distribution feature in `OP_RETURN` outputs, attention should be paid to the size of the contract. For ancillary data which should be verifiable, but need not be distributed to all users in-band, it is recommended to store a hash of the data in a field of bytestring type, rather than the data itself.

Further restrictions:
* The entire contract, including the version byte and the entire CBOR structure, MUST be at most 256 bytes in length.
  * This will be enforced as a standardness/policy rule, for contracts encoded in `OP_RETURN` outputs.
  * Consumers SHOULD reject overlong contracts, but are not required to do so.
* Some additional restrictions are imposed on the CBOR data, for security, ease of parsing, and (limited) JSON compatibility:
  * The CBOR must be "well-formed" and "valid", and decoding must be done in "strict mode" if possible, as defined in RFC 7049:
    * Maps MUST NOT have duplicate keys.
    * Strings MUST be valid UTF-8.
    * Consumers MUST NOT depend on the order of entries in maps.
  * Byte strings should be used for binary data (and should be rendered into strings of hex characters if converting to JSON.)
  * Map keys MUST be strings only.
  * All compound types (strings, byte strings, arrays, maps) MUST have lengths encoded up-front; the indefinite length "streaming" forms MUST NOT be used (nor may the `break` value.)
  * CBOR major type 6, "semantic tags," MUST NOT be used (nor any of the features depending on it: dates, bignums, etc.)
  * The "simple value" `undefined`, as well as the float values `+Inf`, `-Inf`, and `NaN`, MUST NOT be used, as they do not exist in JSON.

A contract which complies with the rules above will be called "well-formed". Other contracts are called "invalid".
* For clarity: none of these rules are enforced by consensus or standardness/policy rules of Elements (except the maximum length, for contracts distributed on-chain.)
* This specification describes a layer of tooling which exists on top of those rules.
* Issuers who wish to use "invalid" contracts -- inside a closed ecosystem of their own software -- should expect that their asset contracts will not be interoperable with the broader Elements asset ecosystem:
  * Elements Core and any software depending on it, such as block explorers, will consider such assets "unknown".
  * The Liquid Asset Registry will reject such assets.
  * It will still be possible to distribute such asset contracts onchain as long as they are under the maximum size, but compliant consumers may reject them.

The intent of the restrictions described above is to simplify safe parsing of contracts, without making contract creation difficult for issuers.
* Issuers who want maximum compatibilty for their contracts, including use of the asset registry or Elements Core, MUST ensure their contracts are well-formed.
  * The described subset of CBOR is selected for maximum compatibility; the excluded features are obscure, and users are unlikely to run into any of them by accident.
  * Issuers who use the asset registry can validate their contract against this specification using the registry contract validation API.
  * Other tooling will be available for local validation of contracts, including Elements Core RPC.
* Consumers have some flexibility in parsing contracts.
  * Consumers MUST NOT crash or exhibit exploitable behavior when encountering an invalid contract. Consumers who get contracts from an untrusted source (such as the blockchain) MUST ensure that their code, including third-party code such as a CBOR parser, does not crash or exhibit exploitable behavior regardless of input, including invalid CBOR, or valid CBOR representing an invalid asset contract. Malicious parties can easily put arbitrary data on the blockchain where a contract is expected.
  * Either accepting or rejecting an invalid contract is in compliance with this specification; only crashes and exploitable behavior are prohibited.
  * Consumers who trust and rely on an asset registry MAY assume that version 1 contracts downloaded from the registry are well-formed.
  * Consumers who get their contracts from an untrusted source SHOULD refuse to use assets whose contracts are not well-formed, but are not required to do so.
  * Consumers (such as hardware wallets) who wish to minimize parsing complexity may rely on the fact that a valid version 1 contract will always begin as follows: `0x01 0x83 <1 byte precision, value 0-8> 0x73-0x75 <3-5 byte ticker, ASCII text> ...`
    * Of course, such consumers MUST NOT crash or display exploitable behavior if a contract received from an untrusted source turns out to be invalid.

Registry rules:
* A registry may impose additional restrictions on contracts, beyond those described above.
* In particular, the Liquid Asset Registry imposes the following requirements:
  * The `name`, `issuer_pubkey`, and `domain` fields must be present;
  * The `name` field must be 1-255 bytes of ASCII text;
  * The `issuer_pubkey` field must be a valid `secp256k1` public key;
  * The `domain` field must be a well-formed domain, controlled by the issuer, which must be proven by the existence of a file served over https from that domain.
    * The file is `https://[domain]/.well-known/liquid-asset-proof-[asset ID hex]`, and its contents must be the string "`Authorize linking the domain name [domain] to the Liquid asset [asset ID hex]`" (trailing whitespace is ignored).
    * The domain validation rule helps protect registry users against assets which are intended to spoof other assets.

## JSON conversion

For compatibility with existing clients of the asset registry which use JSON, we define a backwards-compatible conversion from the CBOR format to the JSON format. Users of the registry can request contracts in either format.

The JSON conversion results in a map (JSON object) similar to the contract version 0 format:
* The two initial CBOR precision and ticker values are inserted in the map with the keys `precision` and `ticker`, respectively.
* The `domain` field, if present, is inserted into a JSON object, which is inserted into the contract JSON under the key `entity`.
* All remaining fields in the CBOR object are added directly into the contract JSON object.
* Any CBOR byte strings are converted to JSON strings of hex characters.

This conversion is not reversible, due to the handling of byte strings, as well as the existence of multiple number types in CBOR which all map onto JSON floats. For a reversible human-readable conversion, we recommend using the CBOR "diagnostic notation" defined in RFC 7049. Although it does not have a formal definition, CBOR tooling generally works with this format. It resembles JSON, but the following additions are relevant:
* Byte strings may be indicated using hex strings in a pseudo-JSON notation: `h'0123456789abcdef'`.
* Floating point numbers should be encoded with at least one digit after the decimal point, to distinguish them from integers.
* The specific floating-point encoding may be indicated with a suffix: `1.0_1`, `1.0_2`, and `1.0_3` indicate the number `1.0` encoded with half, single, and double precision, respectively.

## Contract distribution

Because contracts are committed in a hash on the blockchain, consumers are free to get contracts from any source, and can easily verify that a contract is associated with a given asset. However, is is convenient to be able to get contracts directly from the asset issuance transaction on the blockchain. CBOR (being much more compact than JSON) makes this reasonable.
* By convention, a contract (formatted as described above) MAY be provided in an `OP_RETURN` output of the transaction representing the initial issuance of the asset.
  * Asset issuers who want maximum compatibility and distribution of their assets SHOULD provide the contract in this way.
  * Going forward, the Elements Core RPC interface will provide only limited support for assets which do not do so. See `asset-values-rpc.md`.
* In each transaction which contains one or more initial asset issuances (NOT reissuances), asset contract consumers should inspect all `OP_RETURN` outputs for contract data.
  * Consumers SHOULD ignore `OP_RETURN` data larger than the maximum contract size (which is prohibited by standardness anyway.)
  * If the hash of the `OP_RETURN` data matches the asset contract field of ANY asset issuance in the same transaction, it is the contract for that asset.
  * Since no consensus rules are enforced on this data, implementations MUST treat it as untrusted and potentially malicious input.
  * Implementations SHOULD validate contracts found in `OP_RETURN` outputs, ignore contracts which are invalid according to this specification, and treat such assets as unknown, but are not required to do so.
* The `OP_RETURN` data-size policy/standardness limit (normally 80 bytes) will be raised to 256 bytes for a subset of outputs, to accommodate contracts.
  * Any `OP_RETURN` whose hash matches an asset issuance input in the same transaction, will be given the benefit of the raised limit.
