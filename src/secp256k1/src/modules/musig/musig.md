MuSig - Rogue-Key-Resistant Multisignatures Module
===========================

This module implements the MuSig [1] multisignature scheme. The majority of
the module is an API designed to be used by signing or auditing participants
in a multisignature scheme. This involves a somewhat complex state machine
and significant effort has been taken to prevent accidental misuse of the
API in ways that could lead to accidental signatures or loss of key material.

The resulting signatures are valid Schnorr signatures as described in [2].

# Theory

In MuSig all signers contribute key material to a single signing key,
using the equation

    P = sum_i µ_i * P_i

where `P_i` is the public key of the `i`th signer and `µ_i` is a so-called
_MuSig coefficient_ computed according to the following equation

    L = H(P_1 || P_2 || ... || P_n)
    µ_i = H(L || i)

where H is a hash function modelled as a random oracle.

To produce a multisignature `(s, R)` on a message `m` using verification key
`P`, signers act as follows:

1. Each computes a nonce, or ephemeral keypair, `(k_i, R_i)`. Every signer
   communicates `H(R_i)` to every participant (both signers and auditors).
2. Upon receipt of every `H(R_i)`, each signer communicates `R_i` to every
   participant. The recipients check that each `R_i` is consistent with the
   previously-communicated hash.
3. Each signer computes a combined nonce
    `R = sum_i R_i`
   and shared challenge
    `e = H(R || P || m)`
   and partial signature
    `s_i = k_i + µ_i*x_i*e`
   where `x_i` is the secret key corresponding to `P_i`.

The complete signature is then the `(s, R)` where `s = sum_i s_i` and `R = sum_i R_i`.

# API Usage

The following sections describe use of our API, and are mirrored in code in `src/modules/musig/example.c`.

It is essential to security that signers use a unique uniformly random nonce for all
signing sessions, and that they do not reuse these nonces even in the case that a
signing session fails to complete. To that end, all signing state is encapsulated
in the data structure `secp256k1_musig_session`. The API does not expose any
functionality to serialize or deserialize this structure; it is designed to exist
only in memory.

Users who need to persist this structure must take additional security measures
which cannot be enforced by a C API. Some guidance is provided in the documentation
for this data structure in `include/secp256k1_musig.h`.

## Key Generation

To use MuSig, users must first compute their combined public key `P`, which is
suitable for use on a blockchain or other public key repository. They do this
by calling `secp256k1_musig_pubkey_combine`.

This function takes as input a list of public keys `P_i` in the argument
`pubkeys`. It outputs the combined public key `P` in the out-pointer `combined_pk`
and hash `L` in the out-pointer `pk_hash32`, if this pointer is non-NULL.

## Signing

A participant who wishes to sign a message (as opposed to observing/auditing the
signature process, which is also a supported mode) acts as follows.

### Signing Participant

1. The signer starts the session by calling `secp256k1_musig_session_init`.
   This function outputs
   - an initialized session state in the out-pointer `session`
   - an array of initialized signer data in the out-pointer `signers`
   - a commitment `H(R_i)` to a nonce in the out-pointer `nonce_commitment32`
   It takes as input
   - a unique session ID `session_id32`
   - (optionally) a message to be signed `msg32`
   - the combined public key output from `secp256k1_musig_pubkey_combine`
   - the public key hash output from `secp256k1_musig_pubkey_combine`
   - the signer's index `i` `my_index`
   - the signer's secret key `seckey`
2. The signer then communicates `H(R_i)` to all other signers, and receives
   commitments `H(R_j)` from all other signers `j`. These hashes are simply
   length-32 byte arrays which can be communicated however is communicated.
3. Once all signers nonce commitments have been received, the signer records
   these commitments with the function `secp256k1_musig_session_get_public_nonce`.
   If the signer did not provide a message to `secp256k1_musig_session_init`,
   a message must be provided now.
   This function updates in place
   - the session state `session`
   - the array of signer data `signers`
   taking in as input the list of commitments `commitments` and outputting the
   signer's public nonce `R_i` in the out-pointer `nonce`.
4. The signer then communicates `R_i` to all other signers, and receives `R_j`
   from each signer `j`. On receipt of a nonce `R_j` he calls the function
   `secp256k1_musig_set_nonce` to record this fact. This function checks that
   the received nonce is consistent with the previously-received nonce and will
   return 0 in this case. The signer must also call this function with his own
   nonce and his own index `i`.
   These nonces `R_i` are secp256k1 public keys; they should be serialized using
   `secp256k1_ec_pubkey_serialize` and parsed with `secp256k1_ec_pubkey_parse`.
5. Once all nonces have been exchanged in this way, signers are able to compute
   their partial signatures. They do so by calling `secp256k1_musig_session_combine_nonces`
   which updates in place
   - the session state `session`
   - the array of signer data `signers`
   It outputs an auxiliary integer `nonce_is_negated` and has an auxiliary input
   `adaptor`. Both of these may be set to NULL for ordinary signing purposes.
6. The signer computes a partial signature `s_i` using the function
   `secp256k1_musig_partial_sign` which takes the session state as input and
   partial signature as output.
7. The signer then communicates the partial signature `s_i` to all other signers, or
   to a central coordinator. These partial signatures should be serialized using
   `musig_partial_signature_serialize` and parsed using `musig_partial_signature_parse`.
8. Each signer calls `secp256k1_musig_partial_sig_verify` on the other signers' partial
   signatures to verify their correctness. If only the validity of the final signature
   is important, not assigning blame, this step can be skipped.
9. Any signer, or central coordinator, may combine the partial signatures to obtain
   a complete signature using `secp256k1_musig_partial_sig_combine`. This function takes
   a signing session and array of MuSig partial signatures, and outputs a single
   Schnorr signature.

### Non-signing Participant

A participant who wants to verify the signing process, i.e. check that nonce commitments
are consistent and partial signatures are correct without contributing a partial signature,
may do so using the above instructions except for the following changes:

1. A signing session should be produced using `musig_session_init_verifier`
   rather than `musig_session_init`; this function takes no secret data or
   signer index.
2. The participant receives nonce commitments, public nonces and partial signatures,
   but does not produce these values. Therefore `secp256k1_musig_session_get_public_nonce`
   and `secp256k1_musig_partial_sign` are not called.

### Verifier

The final signature is simply a valid Schnorr signature using the combined public key. It
can be verified using the `secp256k1_schnorrsig_verify` with the correct message and
public key output from `secp256k1_musig_pubkey_combine`.

## Atomic Swaps

The signing API supports the production of "adaptor signatures", modified partial signatures
which are offset by an auxiliary secret known to one party. That is,
1. One party generates a (secret) adaptor `t` with corresponding (public) adaptor `T = t*G`.
2. When combining nonces, each party adds `T` to the total nonce used in the signature.
3. The party who knows `t` must "adapt" their partial signature with `t` to complete the
   signature.
4. Any party who sees both the final signature and the original partial signatures
   can compute `t`.

Using these adaptor signatures, two 2-of-2 MuSig signing protocols can be executed in
parallel such that one party's partial signatures are made atomic. That is, when the other
party learns one partial signature, she automatically learns the other. This has applications
in cross-chain atomic swaps.

Such a protocol can be executed as follows. Consider two participants, Alice and Bob, who
are simultaneously producing 2-of-2 multisignatures for two blockchains A and B. They act
as follows.

1. Before the protocol begins, Bob chooses a 32-byte auxiliary secret `t` at random and
   computes a corresponding public point `T` by calling `secp256k1_ec_pubkey_create`.
   He communicates `T` to Alice.
2. Together, the parties execute steps 1-4 of the signing protocol above.
3. At step 5, when combining the two parties' public nonces, both parties call
   `secp256k1_musig_session_combine_nonces` with `adaptor` set to `T` and `nonce_is_negated`
   set to a non-NULL pointer to int.
4. Steps 6 and 7 proceed as before. Step 8, verifying the partial signatures, is now
   essential to the security of the protocol and must not be omitted!

The above steps are executed identically for both signing sessions. However, step 9 will
not work as before, since the partial signatures will not add up to a valid total signature.
Additional steps must be taken, and it is at this point that the two signing sessions
diverge. From here on we consider "Session A" which benefits Alice (e.g. which sends her
coins) and "Session B" which benefits Bob (e.g. which sends him coins).

5. In Session B, Bob calls `secp256k1_musig_partial_sig_adapt` with his partial signature
   and `t`, to produce an adaptor signature. He can then call `secp256k1_musig_partial_sig_combine`
   with this adaptor signature and Alice's partial signature, to produce a complete
   signature for blockchain B.
6. Alice reads this signature from blockchain B. She calls `secp256k1_musig_extract_secret_adaptor`,
   passing the complete signature along with her and Bob's partial signatures from Session B.
   This function outputs `t`, which until this point was only known to Bob.
7. In Session A, Alice is now able to replicate Bob's action, calling
   `secp256k1_musig_partial_sig_adapt` with her own partial signature and `t`, ultimately
   producing a complete signature on blockchain A.

[1] https://eprint.iacr.org/2018/068
[2] https://github.com/sipa/bips/blob/bip-schnorr/bip-schnorr.mediawiki

