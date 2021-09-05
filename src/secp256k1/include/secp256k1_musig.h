#ifndef SECP256K1_MUSIG_H
#define SECP256K1_MUSIG_H

#include "secp256k1_extrakeys.h"

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

/** This module implements a Schnorr-based multi-signature scheme called MuSig
 * (https://eprint.iacr.org/2018/068.pdf). It is compatible with bip-schnorr.
 * There's an example C source file in the module's directory
 * (src/modules/musig/example.c) that demonstrates how it can be used.
 *
 * The documentation in this include file is for reference and may not be sufficient
 * for users to begin using the library. A full description of API usage can be found
 * in src/modules/musig/musig.md
 */

/** Data structure containing auxiliary data generated in `pubkey_combine` and
 *  required for `session_*_init`.
 *  Fields:
 *        magic: Set during initialization in `pubkey_combine` to allow
 *               detecting an uninitialized object.
 *      pk_hash: The 32-byte hash of the original public keys
 *    second_pk: Serialized x-coordinate of the second public key in the list.
 *               Filled with zeros if there is none.
 *    pk_parity: Whether the MuSig-aggregated point was negated when
 *               converting it to the combined xonly pubkey.
 *     is_tweaked: Whether the combined pubkey was tweaked
 *          tweak: If is_tweaked, array with the 32-byte tweak
 * internal_key_parity: If is_tweaked, the parity of the combined pubkey
 *                 before tweaking
 */
typedef struct {
    uint64_t magic;
    unsigned char pk_hash[32];
    unsigned char second_pk[32];
    int pk_parity;
    int is_tweaked;
    unsigned char tweak[32];
    int internal_key_parity;
} secp256k1_musig_pre_session;

/** Data structure containing data related to a signing session resulting in a single
 * signature.
 *
 * This structure is not opaque, but it MUST NOT be copied or read or written to it
 * directly. A signer who is online throughout the whole process and can keep this
 * structure in memory can use the provided API functions for a safe standard
 * workflow. See https://blockstream.com/2019/02/18/musig-a-new-multisignature-standard/
 * for more details about the risks associated with serializing or deserializing this
 * structure.
 *
 * Fields:
 *            magic: Set in `musig_session_init` to allow detecting an
 *                   uninitialized object.
 *            round: Current round of the session
 *      pre_session: Auxiliary data created in `pubkey_combine`
 *      combined_pk: MuSig-computed combined xonly public key
 *        n_signers: Number of signers
 *              msg: The 32-byte message (hash) to be signed
 *       is_msg_set: Whether the above message has been set
 *  has_secret_data: Whether this session object has a signers' secret data; if this
 *                   is `false`, it may still be used for verification purposes.
 *           seckey: If `has_secret_data`, the signer's secret key
 *         secnonce: If `has_secret_data`, the signer's secret nonce
 *            nonce: If `has_secret_data`, the signer's public nonce
 * nonce_commitments_hash: If `has_secret_data` and round >= 1, the hash of all
 *                   signers' commitments
 *   combined_nonce: If round >= 2, the summed combined public nonce
 * combined_nonce_parity: If round >= 2, the parity of the Y coordinate of above
 *                   nonce.
 */
typedef struct {
    uint64_t magic;
    int round;
    secp256k1_musig_pre_session pre_session;
    secp256k1_xonly_pubkey combined_pk;
    uint32_t n_signers;
    int is_msg_set;
    unsigned char msg[32];
    int has_secret_data;
    unsigned char seckey[32];
    unsigned char secnonce[32];
    secp256k1_xonly_pubkey nonce;
    int partial_nonce_parity;
    unsigned char nonce_commitments_hash[32];
    secp256k1_xonly_pubkey combined_nonce;
    int combined_nonce_parity;
} secp256k1_musig_session;

/** Data structure containing data on all signers in a single session.
 *
 * The workflow for this structure is as follows:
 *
 * 1. This structure is initialized with `musig_session_init` or
 *    `musig_session_init_verifier`, which initializes
 *    all other fields. The public session is initialized with the signers'
 *    nonce_commitments.
 *
 * 2. In a non-public session the nonce_commitments are set with the function
 *    `musig_get_public_nonce`, which also returns the signer's public nonce. This
 *    ensures that the public nonce is not exposed until all commitments have been
 *    received.
 *
 * 3. Each individual data struct should be updated with `musig_set_nonce` once a
 *    nonce is available. This function takes a single signer data struct rather than
 *    an array because it may fail in the case that the provided nonce does not match
 *    the commitment. In this case, it is desirable to identify the exact party whose
 *    nonce was inconsistent.
 *
 * Fields:
 *   present: indicates whether the signer's nonce is set
 *     nonce: public nonce, must be a valid curvepoint if the signer is `present`
 * nonce_commitment: commitment to the nonce, or all-bits zero if a commitment
 *                   has not yet been set
 */
typedef struct {
    int present;
    secp256k1_xonly_pubkey nonce;
    unsigned char nonce_commitment[32];
} secp256k1_musig_session_signer_data;

/** Opaque data structure that holds a MuSig partial signature.
 *
 *  The exact representation of data inside is implementation defined and not
 *  guaranteed to be portable between different platforms or versions. It is however
 *  guaranteed to be 32 bytes in size, and can be safely copied/moved. If you need
 *  to convert to a format suitable for storage, transmission, or comparison, use the
 *  `musig_partial_signature_serialize` and `musig_partial_signature_parse`
 *  functions.
 */
typedef struct {
    unsigned char data[32];
} secp256k1_musig_partial_signature;

/** Computes a combined public key and the hash of the given public keys.
 *
 *  Different orders of `pubkeys` result in different `combined_pk`s.
 *
 *  The pubkeys can be sorted before combining with `secp256k1_xonly_sort` which
 *  ensures the same resulting `combined_pk` for the same multiset of pubkeys.
 *  This is useful to do before pubkey_combine, such that the order of pubkeys
 *  does not affect the combined public key.
 *
 *  Returns: 1 if the public keys were successfully combined, 0 otherwise
 *  Args:        ctx: pointer to a context object initialized for verification
 *                    (cannot be NULL)
 *           scratch: scratch space used to compute the combined pubkey by
 *                    multiexponentiation. If NULL, an inefficient algorithm is used.
 *  Out: combined_pk: the MuSig-combined xonly public key (cannot be NULL)
 *       pre_session: if non-NULL, pointer to a musig_pre_session struct to be used in
 *                    `musig_session_init` or `musig_pubkey_tweak_add`.
 *   In:     pubkeys: input array of pointers to public keys to combine. The order
 *                    is important; a different order will result in a different
 *                    combined public key (cannot be NULL)
 *         n_pubkeys: length of pubkeys array. Must be greater than 0.
 */
SECP256K1_API int secp256k1_musig_pubkey_combine(
    const secp256k1_context* ctx,
    secp256k1_scratch_space *scratch,
    secp256k1_xonly_pubkey *combined_pk,
    secp256k1_musig_pre_session *pre_session,
    const secp256k1_xonly_pubkey * const* pubkeys,
    size_t n_pubkeys
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(5);

/** Tweak an x-only public key by adding the generator multiplied with tweak32
 *  to it. The resulting output_pubkey with the given internal_pubkey and tweak
 *  passes `secp256k1_xonly_pubkey_tweak_test`.
 *
 *  This function is only useful before initializing a signing session. If you
 *  are only computing a public key, but not intending to create a signature for
 *  it, you can just use `secp256k1_xonly_pubkey_tweak_add`. Can only be called
 *  once with a given pre_session.
 *
 *  Returns: 0 if the arguments are invalid or the resulting public key would be
 *           invalid (only when the tweak is the negation of the corresponding
 *           secret key). 1 otherwise.
 *  Args:          ctx: pointer to a context object initialized for verification
 *                      (cannot be NULL)
 *         pre_session: pointer to a `musig_pre_session` struct initialized in
 *                      `musig_pubkey_combine` (cannot be NULL)
 *  Out: output_pubkey: pointer to a public key to store the result. Will be set
 *                      to an invalid value if this function returns 0 (cannot
 *                      be NULL)
 *  In: internal_pubkey: pointer to the `combined_pk` from
 *                       `musig_pubkey_combine` to which the tweak is applied.
 *                       (cannot be NULL).
 *              tweak32: pointer to a 32-byte tweak. If the tweak is invalid
 *                       according to secp256k1_ec_seckey_verify, this function
 *                       returns 0. For uniformly random 32-byte arrays the
 *                       chance of being invalid is negligible (around 1 in
 *                       2^128) (cannot be NULL).
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_musig_pubkey_tweak_add(
    const secp256k1_context* ctx,
    secp256k1_musig_pre_session *pre_session,
    secp256k1_pubkey *output_pubkey,
    const secp256k1_xonly_pubkey *internal_pubkey,
    const unsigned char *tweak32
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(4) SECP256K1_ARG_NONNULL(5);

/** Initializes a signing session for a signer
 *
 *  Returns: 1: session is successfully initialized
 *           0: session could not be initialized: secret key or secret nonce overflow
 *  Args:         ctx: pointer to a context object, initialized for signing (cannot
 *                     be NULL)
 *  Out:      session: the session structure to initialize (cannot be NULL)
 *            signers: an array of signers' data to be initialized. Array length must
 *                     equal to `n_signers` (cannot be NULL)
 * nonce_commitment32: filled with a 32-byte commitment to the generated nonce
 *                     (cannot be NULL)
 *  In:  session_id32: a *unique* 32-byte ID to assign to this session (cannot be
 *                     NULL). If a non-unique session_id32 was given then a partial
 *                     signature will LEAK THE SECRET KEY.
 *              msg32: the 32-byte message to be signed. Shouldn't be NULL unless you
 *                     require sharing nonce commitments before the message is known
 *                     because it reduces nonce misuse resistance. If NULL, must be
 *                     set with `musig_session_get_public_nonce`.
 *        combined_pk: the combined xonly public key of all signers (cannot be NULL)
 *        pre_session: pointer to a musig_pre_session struct after initializing
 *                     it with `musig_pubkey_combine` and optionally provided to
 *                     `musig_pubkey_tweak_add` (cannot be NULL).
 *          n_signers: length of signers array. Number of signers participating in
 *                     the MuSig. Must be greater than 0 and at most 2^32 - 1.
 *             seckey: the signer's 32-byte secret key (cannot be NULL)
 */
SECP256K1_API int secp256k1_musig_session_init(
    const secp256k1_context* ctx,
    secp256k1_musig_session *session,
    secp256k1_musig_session_signer_data *signers,
    unsigned char *nonce_commitment32,
    const unsigned char *session_id32,
    const unsigned char *msg32,
    const secp256k1_xonly_pubkey *combined_pk,
    const secp256k1_musig_pre_session *pre_session,
    size_t n_signers,
    const unsigned char *seckey
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(4) SECP256K1_ARG_NONNULL(5) SECP256K1_ARG_NONNULL(7) SECP256K1_ARG_NONNULL(8) SECP256K1_ARG_NONNULL(11);

/** Gets the signer's public nonce given a list of all signers' data with
 *  commitments.  Called by participating signers after
 *  `secp256k1_musig_session_init` and after all nonce commitments have
 *  been collected
 *
 *  Returns: 1: public nonce is written in nonce
 *           0: signer data is missing commitments or session isn't initialized
 *              for signing
 *  Args:        ctx: pointer to a context object (cannot be NULL)
 *           session: the signing session to get the nonce from (cannot be NULL)
 *           signers: an array of signers' data initialized with
 *                    `musig_session_init`. Array length must equal to
 *                    `n_commitments` (cannot be NULL)
 *  Out:     nonce32: filled with a 32-byte public nonce which is supposed to be
 *                    sent to the other signers and then used in `musig_set nonce`
 *                    (cannot be NULL)
 *  In:  commitments: array of pointers to 32-byte nonce commitments (cannot be NULL)
 *     n_commitments: the length of commitments and signers array. Must be the total
 *                    number of signers participating in the MuSig.
 *             msg32: the 32-byte message to be signed. Must be NULL if already
 *                    set with `musig_session_init` otherwise can not be NULL.
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_musig_session_get_public_nonce(
    const secp256k1_context* ctx,
    secp256k1_musig_session *session,
    secp256k1_musig_session_signer_data *signers,
    unsigned char *nonce32,
    const unsigned char *const *commitments,
    size_t n_commitments,
    const unsigned char *msg32
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(4) SECP256K1_ARG_NONNULL(5);

/** Initializes a verifier session that can be used for verifying nonce commitments
 *  and partial signatures. It does not have secret key material and therefore can not
 *  be used to create signatures.
 *
 *  Returns: 1 when session is successfully initialized, 0 otherwise
 *  Args:        ctx: pointer to a context object (cannot be NULL)
 *  Out:     session: the session structure to initialize (cannot be NULL)
 *           signers: an array of signers' data to be initialized. Array length must
 *                    equal to `n_signers`(cannot be NULL)
 *  In:        msg32: the 32-byte message to be signed (cannot be NULL)
 *       combined_pk: the combined xonly public key of all signers (cannot be NULL)
 *       pre_session: pointer to a musig_pre_session struct from
 *                    `musig_pubkey_combine` (cannot be NULL)
 *         pk_hash32: the 32-byte hash of the signers' individual keys (cannot be NULL)
 *       commitments: array of pointers to 32-byte nonce commitments. Array
 *                    length must equal to `n_signers` (cannot be NULL)
 *         n_signers: length of signers and commitments array. Number of signers
 *                    participating in the MuSig. Must be greater than 0 and at most
 *                    2^32 - 1.
 */
SECP256K1_API int secp256k1_musig_session_init_verifier(
    const secp256k1_context* ctx,
    secp256k1_musig_session *session,
    secp256k1_musig_session_signer_data *signers,
    const unsigned char *msg32,
    const secp256k1_xonly_pubkey *combined_pk,
    const secp256k1_musig_pre_session *pre_session,
    const unsigned char *const *commitments,
    size_t n_signers
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(4) SECP256K1_ARG_NONNULL(5) SECP256K1_ARG_NONNULL(6) SECP256K1_ARG_NONNULL(7);

/** Checks a signer's public nonce against a commitment to said nonce, and update
 *  data structure if they match
 *
 *  Returns: 1: commitment was valid, data structure updated
 *           0: commitment was invalid, nothing happened
 *  Args:      ctx: pointer to a context object (cannot be NULL)
 *          signer: pointer to the signer data to update (cannot be NULL). Must have
 *                  been used with `musig_session_get_public_nonce` or initialized
 *                  with `musig_session_init_verifier`.
 *  In:    nonce32: signer's alleged public nonce (cannot be NULL)
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_musig_set_nonce(
    const secp256k1_context* ctx,
    secp256k1_musig_session_signer_data *signer,
    const unsigned char *nonce32
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Updates a session with the combined public nonce of all signers. The combined
 * public nonce is the sum of every signer's public nonce.
 *
 *  Returns: 1: nonces are successfully combined
 *           0: a signer's nonce is missing
 *  Args:        ctx: pointer to a context object (cannot be NULL)
 *           session: session to update with the combined public nonce (cannot be
 *                    NULL)
 *           signers: an array of signers' data, which must have had public nonces
 *                    set with `musig_set_nonce`. Array length must equal to `n_signers`
 *                    (cannot be NULL)
 *         n_signers: the length of the signers array. Must be the total number of
 *                    signers participating in the MuSig.
 *  Out: nonce_parity: if non-NULL, a pointer to an integer that indicates the
 *                    parity of the combined public nonce. Used for adaptor
 *                    signatures.
 *           adaptor: point to add to the combined public nonce. If NULL, nothing is
 *                    added to the combined nonce.
 */
SECP256K1_API int secp256k1_musig_session_combine_nonces(
    const secp256k1_context* ctx,
    secp256k1_musig_session *session,
    const secp256k1_musig_session_signer_data *signers,
    size_t n_signers,
    int *nonce_parity,
    const secp256k1_pubkey *adaptor
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Serialize a MuSig partial signature or adaptor signature
 *
 *  Returns: 1 when the signature could be serialized, 0 otherwise
 *  Args:    ctx: a secp256k1 context object
 *  Out:   out32: pointer to a 32-byte array to store the serialized signature
 *  In:      sig: pointer to the signature
 */
SECP256K1_API int secp256k1_musig_partial_signature_serialize(
    const secp256k1_context* ctx,
    unsigned char *out32,
    const secp256k1_musig_partial_signature* sig
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Parse and verify a MuSig partial signature.
 *
 *  Returns: 1 when the signature could be parsed, 0 otherwise.
 *  Args:    ctx: a secp256k1 context object
 *  Out:     sig: pointer to a signature object
 *  In:     in32: pointer to the 32-byte signature to be parsed
 *
 *  After the call, sig will always be initialized. If parsing failed or the
 *  encoded numbers are out of range, signature verification with it is
 *  guaranteed to fail for every message and public key.
 */
SECP256K1_API int secp256k1_musig_partial_signature_parse(
    const secp256k1_context* ctx,
    secp256k1_musig_partial_signature* sig,
    const unsigned char *in32
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Produces a partial signature
 *
 *  Returns: 1: partial signature constructed
 *           0: session in incorrect or inconsistent state
 *  Args:         ctx: pointer to a context object (cannot be NULL)
 *            session: active signing session for which the combined nonce has been
 *                     computed (cannot be NULL)
 *  Out:  partial_sig: partial signature (cannot be NULL)
 */
SECP256K1_API int secp256k1_musig_partial_sign(
    const secp256k1_context* ctx,
    const secp256k1_musig_session *session,
    secp256k1_musig_partial_signature *partial_sig
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3);

/** Checks that an individual partial signature verifies
 *
 *  This function is essential when using protocols with adaptor signatures.
 *  However, it is not essential for regular MuSig's, in the sense that if any
 *  partial signatures does not verify, the full signature will also not verify, so the
 *  problem will be caught. But this function allows determining the specific party
 *  who produced an invalid signature, so that signing can be restarted without them.
 *
 *  Returns: 1: partial signature verifies
 *           0: invalid signature or bad data
 *  Args:         ctx: pointer to a context object (cannot be NULL)
 *            session: active session for which the combined nonce has been computed
 *                     (cannot be NULL)
 *             signer: data for the signer who produced this signature (cannot be NULL)
 *  In:   partial_sig: signature to verify (cannot be NULL)
 *             pubkey: public key of the signer who produced the signature (cannot be NULL)
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_musig_partial_sig_verify(
    const secp256k1_context* ctx,
    const secp256k1_musig_session *session,
    const secp256k1_musig_session_signer_data *signer,
    const secp256k1_musig_partial_signature *partial_sig,
    const secp256k1_xonly_pubkey *pubkey
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(4) SECP256K1_ARG_NONNULL(5);

/** Combines partial signatures
 *
 *  Returns: 1: all partial signatures have values in range. Does NOT mean the
 *              resulting signature verifies.
 *           0: some partial signature are missing or had s or r out of range
 *  Args:         ctx: pointer to a context object (cannot be NULL)
 *            session: initialized session for which the combined nonce has been
 *                     computed (cannot be NULL)
 *  Out:        sig64: complete signature (cannot be NULL)
 *  In:  partial_sigs: array of partial signatures to combine (cannot be NULL)
 *             n_sigs: number of signatures in the partial_sigs array
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_musig_partial_sig_combine(
    const secp256k1_context* ctx,
    const secp256k1_musig_session *session,
    unsigned char *sig64,
    const secp256k1_musig_partial_signature *partial_sigs,
    size_t n_sigs
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(4);

/** Converts a partial signature to an adaptor signature by adding a given secret
 *  adaptor.
 *
 *  Returns: 1: signature and secret adaptor contained valid values
 *           0: otherwise
 *  Args:         ctx: pointer to a context object (cannot be NULL)
 *  Out:  adaptor_sig: adaptor signature to produce (cannot be NULL)
 *  In:   partial_sig: partial signature to tweak with secret adaptor (cannot be NULL)
 *      sec_adaptor32: 32-byte secret adaptor to add to the partial signature (cannot
 *                     be NULL)
 *       nonce_parity: the `nonce_parity` output of `musig_session_combine_nonces`
 */
SECP256K1_API int secp256k1_musig_partial_sig_adapt(
    const secp256k1_context* ctx,
    secp256k1_musig_partial_signature *adaptor_sig,
    const secp256k1_musig_partial_signature *partial_sig,
    const unsigned char *sec_adaptor32,
    int nonce_parity
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(4);

/** Extracts a secret adaptor from a MuSig, given all parties' partial
 *  signatures. This function will not fail unless given grossly invalid data; if it
 *  is merely given signatures that do not verify, the returned value will be
 *  nonsense. It is therefore important that all data be verified at earlier steps of
 *  any protocol that uses this function.
 *
 *  Returns: 1: signatures contained valid data such that an adaptor could be extracted
 *           0: otherwise
 *  Args:         ctx: pointer to a context object (cannot be NULL)
 *  Out:sec_adaptor32: 32-byte secret adaptor (cannot be NULL)
 *  In:         sig64: complete 2-of-2 signature (cannot be NULL)
 *       partial_sigs: array of partial signatures (cannot be NULL)
 *     n_partial_sigs: number of elements in partial_sigs array
 *   nonce_parity: the `nonce_parity` output of `musig_session_combine_nonces`
 */
SECP256K1_API SECP256K1_WARN_UNUSED_RESULT int secp256k1_musig_extract_secret_adaptor(
    const secp256k1_context* ctx,
    unsigned char *sec_adaptor32,
    const unsigned char *sig64,
    const secp256k1_musig_partial_signature *partial_sigs,
    size_t n_partial_sigs,
    int nonce_parity
) SECP256K1_ARG_NONNULL(1) SECP256K1_ARG_NONNULL(2) SECP256K1_ARG_NONNULL(3) SECP256K1_ARG_NONNULL(4);

#ifdef __cplusplus
}
#endif

#endif
