/***********************************************************************
 * Copyright (c) 2018 Andrew Poelstra                                  *
 * Distributed under the MIT software license, see the accompanying    *
 * file COPYING or https://www.opensource.org/licenses/mit-license.php.*
 ***********************************************************************/

#ifndef SECP256K1_MODULE_MUSIG_TESTS_IMPL_H
#define SECP256K1_MODULE_MUSIG_TESTS_IMPL_H

#include <stdlib.h>
#include <string.h>

#include "../../../include/secp256k1.h"
#include "../../../include/secp256k1_extrakeys.h"
#include "../../../include/secp256k1_musig.h"

#include "session.h"
#include "keyagg.h"
#include "../../scalar.h"
#include "../../scratch.h"
#include "../../field.h"
#include "../../group.h"
#include "../../hash.h"
#include "../../util.h"

#include "vectors.h"

static int create_keypair_and_pk(secp256k1_keypair *keypair, secp256k1_pubkey *pk, const unsigned char *sk) {
    int ret;
    secp256k1_keypair keypair_tmp;
    ret = secp256k1_keypair_create(ctx, &keypair_tmp, sk);
    ret &= secp256k1_keypair_pub(ctx, pk, &keypair_tmp);
    if (keypair != NULL) {
        *keypair = keypair_tmp;
    }
    return ret;
}

/* Just a simple (non-adaptor, non-tweaked) 2-of-2 MuSig aggregate, sign, verify
 * test. */
void musig_simple_test(secp256k1_scratch_space *scratch) {
    unsigned char sk[2][32];
    secp256k1_keypair keypair[2];
    secp256k1_musig_pubnonce pubnonce[2];
    const secp256k1_musig_pubnonce *pubnonce_ptr[2];
    secp256k1_musig_aggnonce aggnonce;
    unsigned char msg[32];
    secp256k1_xonly_pubkey agg_pk;
    secp256k1_musig_keyagg_cache keyagg_cache;
    unsigned char session_id[2][32];
    secp256k1_musig_secnonce secnonce[2];
    secp256k1_pubkey pk[2];
    const secp256k1_pubkey *pk_ptr[2];
    secp256k1_musig_partial_sig partial_sig[2];
    const secp256k1_musig_partial_sig *partial_sig_ptr[2];
    unsigned char final_sig[64];
    secp256k1_musig_session session;
    int i;

    secp256k1_testrand256(msg);
    for (i = 0; i < 2; i++) {
        secp256k1_testrand256(session_id[i]);
        secp256k1_testrand256(sk[i]);
        pk_ptr[i] = &pk[i];
        pubnonce_ptr[i] = &pubnonce[i];
        partial_sig_ptr[i] = &partial_sig[i];

        CHECK(create_keypair_and_pk(&keypair[i], &pk[i], sk[i]));
        CHECK(secp256k1_musig_nonce_gen(ctx, &secnonce[i], &pubnonce[i], session_id[i], sk[i], &pk[i], NULL, NULL, NULL) == 1);
    }

    CHECK(secp256k1_musig_pubkey_agg(ctx, scratch, &agg_pk, &keyagg_cache, pk_ptr, 2) == 1);
    CHECK(secp256k1_musig_nonce_agg(ctx, &aggnonce, pubnonce_ptr, 2) == 1);
    CHECK(secp256k1_musig_nonce_process(ctx, &session, &aggnonce, msg, &keyagg_cache, NULL) == 1);

    for (i = 0; i < 2; i++) {
        CHECK(secp256k1_musig_partial_sign(ctx, &partial_sig[i], &secnonce[i], &keypair[i], &keyagg_cache, &session) == 1);
        CHECK(secp256k1_musig_partial_sig_verify(ctx, &partial_sig[i], &pubnonce[i], &pk[i], &keyagg_cache, &session) == 1);
    }

    CHECK(secp256k1_musig_partial_sig_agg(ctx, final_sig, &session, partial_sig_ptr, 2) == 1);
    CHECK(secp256k1_schnorrsig_verify(ctx, final_sig, msg, sizeof(msg), &agg_pk) == 1);
}

void pubnonce_summing_to_inf(secp256k1_musig_pubnonce *pubnonce) {
    secp256k1_ge ge[2];
    int i;
    secp256k1_gej summed_nonces[2];
    const secp256k1_musig_pubnonce *pubnonce_ptr[2];

    ge[0] = secp256k1_ge_const_g;
    ge[1] = secp256k1_ge_const_g;

    for (i = 0; i < 2; i++) {
        secp256k1_musig_pubnonce_save(&pubnonce[i], ge);
        pubnonce_ptr[i] = &pubnonce[i];
        secp256k1_ge_neg(&ge[0], &ge[0]);
        secp256k1_ge_neg(&ge[1], &ge[1]);
    }

    secp256k1_musig_sum_nonces(ctx, summed_nonces, pubnonce_ptr, 2);
    CHECK(secp256k1_gej_is_infinity(&summed_nonces[0]));
    CHECK(secp256k1_gej_is_infinity(&summed_nonces[1]));
}

int memcmp_and_randomize(unsigned char *value, const unsigned char *expected, size_t len) {
    int ret;
    size_t i;
    ret = secp256k1_memcmp_var(value, expected, len);
    for (i = 0; i < len; i++) {
        value[i] = secp256k1_testrand_bits(8);
    }
    return ret;
}

void musig_api_tests(secp256k1_scratch_space *scratch) {
    secp256k1_scratch_space *scratch_small;
    secp256k1_musig_partial_sig partial_sig[2];
    const secp256k1_musig_partial_sig *partial_sig_ptr[2];
    secp256k1_musig_partial_sig invalid_partial_sig;
    const secp256k1_musig_partial_sig *invalid_partial_sig_ptr[2];
    unsigned char final_sig[64];
    unsigned char pre_sig[64];
    unsigned char buf[32];
    unsigned char sk[2][32];
    secp256k1_keypair keypair[2];
    secp256k1_keypair invalid_keypair;
    unsigned char max64[64];
    unsigned char zeros132[132] = { 0 };
    unsigned char session_id[2][32];
    secp256k1_musig_secnonce secnonce[2];
    secp256k1_musig_secnonce secnonce_tmp;
    secp256k1_musig_secnonce invalid_secnonce;
    secp256k1_musig_pubnonce pubnonce[2];
    const secp256k1_musig_pubnonce *pubnonce_ptr[2];
    unsigned char pubnonce_ser[66];
    secp256k1_musig_pubnonce inf_pubnonce[2];
    const secp256k1_musig_pubnonce *inf_pubnonce_ptr[2];
    secp256k1_musig_pubnonce invalid_pubnonce;
    const secp256k1_musig_pubnonce *invalid_pubnonce_ptr[1];
    secp256k1_musig_aggnonce aggnonce;
    unsigned char aggnonce_ser[66];
    unsigned char msg[32];
    secp256k1_xonly_pubkey agg_pk;
    secp256k1_pubkey full_agg_pk;
    secp256k1_musig_keyagg_cache keyagg_cache;
    secp256k1_musig_keyagg_cache invalid_keyagg_cache;
    secp256k1_musig_session session;
    secp256k1_musig_session invalid_session;
    secp256k1_pubkey pk[2];
    const secp256k1_pubkey *pk_ptr[2];
    secp256k1_pubkey invalid_pk;
    const secp256k1_pubkey *invalid_pk_ptr2[2];
    const secp256k1_pubkey *invalid_pk_ptr3[3];
    unsigned char tweak[32];
    int nonce_parity;
    unsigned char sec_adaptor[32];
    unsigned char sec_adaptor1[32];
    secp256k1_pubkey adaptor;
    int i;

    /** setup **/
    secp256k1_context *none = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
    secp256k1_context *sign = secp256k1_context_create(SECP256K1_CONTEXT_SIGN);
    secp256k1_context *vrfy = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
    secp256k1_context *sttc = secp256k1_context_clone(secp256k1_context_no_precomp);
    int ecount;

    secp256k1_context_set_error_callback(none, counting_illegal_callback_fn, &ecount);
    secp256k1_context_set_error_callback(sign, counting_illegal_callback_fn, &ecount);
    secp256k1_context_set_error_callback(vrfy, counting_illegal_callback_fn, &ecount);
    secp256k1_context_set_error_callback(sttc, counting_illegal_callback_fn, &ecount);
    secp256k1_context_set_illegal_callback(none, counting_illegal_callback_fn, &ecount);
    secp256k1_context_set_illegal_callback(sign, counting_illegal_callback_fn, &ecount);
    secp256k1_context_set_illegal_callback(vrfy, counting_illegal_callback_fn, &ecount);
    secp256k1_context_set_illegal_callback(sttc, counting_illegal_callback_fn, &ecount);

    memset(max64, 0xff, sizeof(max64));
    memset(&invalid_keypair, 0, sizeof(invalid_keypair));
    memset(&invalid_pk, 0, sizeof(invalid_pk));
    memset(&invalid_secnonce, 0, sizeof(invalid_secnonce));
    memset(&invalid_partial_sig, 0, sizeof(invalid_partial_sig));
    pubnonce_summing_to_inf(inf_pubnonce);
    /* Simulate structs being uninitialized by setting it to 0s. We don't want
     * to produce undefined behavior by actually providing uninitialized
     * structs. */
    memset(&invalid_keyagg_cache, 0, sizeof(invalid_keyagg_cache));
    memset(&invalid_pk, 0, sizeof(invalid_pk));
    memset(&invalid_pubnonce, 0, sizeof(invalid_pubnonce));
    memset(&invalid_session, 0, sizeof(invalid_session));

    secp256k1_testrand256(sec_adaptor);
    secp256k1_testrand256(msg);
    secp256k1_testrand256(tweak);
    CHECK(secp256k1_ec_pubkey_create(ctx, &adaptor, sec_adaptor) == 1);
    for (i = 0; i < 2; i++) {
        pk_ptr[i] = &pk[i];
        invalid_pk_ptr2[i] = &invalid_pk;
        invalid_pk_ptr3[i] = &pk[i];
        pubnonce_ptr[i] = &pubnonce[i];
        inf_pubnonce_ptr[i] = &inf_pubnonce[i];
        partial_sig_ptr[i] = &partial_sig[i];
        invalid_partial_sig_ptr[i] = &partial_sig[i];
        secp256k1_testrand256(session_id[i]);
        secp256k1_testrand256(sk[i]);
        CHECK(create_keypair_and_pk(&keypair[i], &pk[i], sk[i]));
    }
    invalid_pubnonce_ptr[0] = &invalid_pubnonce;
    invalid_partial_sig_ptr[0] = &invalid_partial_sig;
    /* invalid_pk_ptr3 has two valid, one invalid pk, which is important to test
     * musig_pubkey_agg */
    invalid_pk_ptr3[2] = &invalid_pk;

    /** main test body **/

    /** Key aggregation **/
    ecount = 0;
    CHECK(secp256k1_musig_pubkey_agg(none, scratch, &agg_pk, &keyagg_cache, pk_ptr, 2) == 1);
    CHECK(secp256k1_musig_pubkey_agg(sign, scratch, &agg_pk, &keyagg_cache, pk_ptr, 2) == 1);
    CHECK(secp256k1_musig_pubkey_agg(vrfy, scratch, &agg_pk, &keyagg_cache, pk_ptr, 2) == 1);
    /* pubkey_agg does not require a scratch space */
    CHECK(secp256k1_musig_pubkey_agg(vrfy, NULL, &agg_pk, &keyagg_cache, pk_ptr, 2) == 1);
    /* A small scratch space works too, but will result in using an ineffecient algorithm */
    scratch_small = secp256k1_scratch_space_create(ctx, 1);
    CHECK(secp256k1_musig_pubkey_agg(vrfy, scratch_small, &agg_pk, &keyagg_cache, pk_ptr, 2) == 1);
    secp256k1_scratch_space_destroy(ctx, scratch_small);
    CHECK(secp256k1_musig_pubkey_agg(vrfy, scratch, NULL, &keyagg_cache, pk_ptr, 2) == 1);
    CHECK(secp256k1_musig_pubkey_agg(vrfy, scratch, &agg_pk, NULL, pk_ptr, 2) == 1);
    CHECK(secp256k1_musig_pubkey_agg(vrfy, scratch, &agg_pk, &keyagg_cache, NULL, 2) == 0);
    CHECK(ecount == 1);
    CHECK(memcmp_and_randomize(agg_pk.data, zeros132, sizeof(agg_pk.data)) == 0);
    CHECK(secp256k1_musig_pubkey_agg(vrfy, scratch, &agg_pk, &keyagg_cache, invalid_pk_ptr2, 2) == 0);
    CHECK(ecount == 2);
    CHECK(memcmp_and_randomize(agg_pk.data, zeros132, sizeof(agg_pk.data)) == 0);
    CHECK(secp256k1_musig_pubkey_agg(vrfy, scratch, &agg_pk, &keyagg_cache, invalid_pk_ptr3, 3) == 0);
    CHECK(ecount == 3);
    CHECK(memcmp_and_randomize(agg_pk.data, zeros132, sizeof(agg_pk.data)) == 0);
    CHECK(secp256k1_musig_pubkey_agg(vrfy, scratch, &agg_pk, &keyagg_cache, pk_ptr, 0) == 0);
    CHECK(ecount == 4);
    CHECK(memcmp_and_randomize(agg_pk.data, zeros132, sizeof(agg_pk.data)) == 0);
    CHECK(secp256k1_musig_pubkey_agg(vrfy, scratch, &agg_pk, &keyagg_cache, NULL, 0) == 0);
    CHECK(ecount == 5);
    CHECK(memcmp_and_randomize(agg_pk.data, zeros132, sizeof(agg_pk.data)) == 0);

    CHECK(secp256k1_musig_pubkey_agg(none, scratch, &agg_pk, &keyagg_cache, pk_ptr, 2) == 1);
    CHECK(secp256k1_musig_pubkey_agg(sign, scratch, &agg_pk, &keyagg_cache, pk_ptr, 2) == 1);
    CHECK(secp256k1_musig_pubkey_agg(vrfy, scratch, &agg_pk, &keyagg_cache, pk_ptr, 2) == 1);

    /* pubkey_get */
    ecount = 0;
    CHECK(secp256k1_musig_pubkey_get(none, &full_agg_pk, &keyagg_cache) == 1);
    CHECK(secp256k1_musig_pubkey_get(none, NULL, &keyagg_cache) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_pubkey_get(none, &full_agg_pk, NULL) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_memcmp_var(&full_agg_pk, zeros132, sizeof(full_agg_pk)) == 0);

    /** Tweaking **/
    {
        int (*tweak_func[2]) (const secp256k1_context* ctx, secp256k1_pubkey *output_pubkey, secp256k1_musig_keyagg_cache *keyagg_cache, const unsigned char *tweak32);
        tweak_func[0] = secp256k1_musig_pubkey_ec_tweak_add;
        tweak_func[1] = secp256k1_musig_pubkey_xonly_tweak_add;
        for (i = 0; i < 2; i++) {
            secp256k1_pubkey tmp_output_pk;
            secp256k1_musig_keyagg_cache tmp_keyagg_cache = keyagg_cache;
            ecount = 0;
            CHECK((*tweak_func[i])(ctx, &tmp_output_pk, &tmp_keyagg_cache, tweak) == 1);
            /* Reset keyagg_cache */
            tmp_keyagg_cache = keyagg_cache;
            CHECK((*tweak_func[i])(none, &tmp_output_pk, &tmp_keyagg_cache, tweak) == 1);
            tmp_keyagg_cache = keyagg_cache;
            CHECK((*tweak_func[i])(sign, &tmp_output_pk, &tmp_keyagg_cache, tweak) == 1);
            tmp_keyagg_cache = keyagg_cache;
            CHECK((*tweak_func[i])(vrfy, &tmp_output_pk, &tmp_keyagg_cache, tweak) == 1);
            tmp_keyagg_cache = keyagg_cache;
            CHECK((*tweak_func[i])(vrfy, NULL, &tmp_keyagg_cache, tweak) == 1);
            tmp_keyagg_cache = keyagg_cache;
            CHECK((*tweak_func[i])(vrfy, &tmp_output_pk, NULL, tweak) == 0);
            CHECK(ecount == 1);
            CHECK(memcmp_and_randomize(tmp_output_pk.data, zeros132, sizeof(tmp_output_pk.data)) == 0);
            tmp_keyagg_cache = keyagg_cache;
            CHECK((*tweak_func[i])(vrfy, &tmp_output_pk, &tmp_keyagg_cache, NULL) == 0);
            CHECK(ecount == 2);
            CHECK(memcmp_and_randomize(tmp_output_pk.data, zeros132, sizeof(tmp_output_pk.data)) == 0);
            tmp_keyagg_cache = keyagg_cache;
            CHECK((*tweak_func[i])(vrfy, &tmp_output_pk, &tmp_keyagg_cache, max64) == 0);
            CHECK(ecount == 2);
            CHECK(memcmp_and_randomize(tmp_output_pk.data, zeros132, sizeof(tmp_output_pk.data)) == 0);
            tmp_keyagg_cache = keyagg_cache;
            /* Uninitialized keyagg_cache */
            CHECK((*tweak_func[i])(vrfy, &tmp_output_pk, &invalid_keyagg_cache, tweak) == 0);
            CHECK(ecount == 3);
            CHECK(memcmp_and_randomize(tmp_output_pk.data, zeros132, sizeof(tmp_output_pk.data)) == 0);
        }
    }

    /** Session creation **/
    ecount = 0;
    CHECK(secp256k1_musig_nonce_gen(none, &secnonce[0], &pubnonce[0], session_id[0], sk[0], &pk[0], msg, &keyagg_cache, max64) == 1);
    CHECK(secp256k1_musig_nonce_gen(vrfy, &secnonce[0], &pubnonce[0], session_id[0], sk[0], &pk[0], msg, &keyagg_cache, max64) == 1);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], session_id[0], sk[0], &pk[0], msg, &keyagg_cache, max64) == 1);
    CHECK(ecount == 0);
    CHECK(secp256k1_musig_nonce_gen(sttc, &secnonce[0], &pubnonce[0], session_id[0], sk[0], &pk[0], msg, &keyagg_cache, max64) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_nonce_gen(sign, NULL, &pubnonce[0], session_id[0], sk[0], &pk[0], msg, &keyagg_cache, max64) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], NULL, session_id[0], sk[0], &pk[0], msg, &keyagg_cache, max64) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], NULL, sk[0], &pk[0], msg, &keyagg_cache, max64) == 0);
    CHECK(ecount == 4);
    CHECK(memcmp_and_randomize(secnonce[0].data, zeros132, sizeof(secnonce[0].data)) == 0);
    /* no seckey and session_id is 0 */
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], zeros132, NULL, &pk[0], msg, &keyagg_cache, max64) == 0);
    CHECK(ecount == 4);
    CHECK(memcmp_and_randomize(secnonce[0].data, zeros132, sizeof(secnonce[0].data)) == 0);
    /* session_id 0 is fine when a seckey is provided */
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], zeros132, sk[0], &pk[0], msg, &keyagg_cache, max64) == 1);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], session_id[0], NULL, &pk[0], msg, &keyagg_cache, max64) == 1);
    CHECK(ecount == 4);
    /* invalid seckey */
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], session_id[0], max64, &pk[0], msg, &keyagg_cache, max64) == 0);
    CHECK(memcmp_and_randomize(secnonce[0].data, zeros132, sizeof(secnonce[0].data)) == 0);
    CHECK(ecount == 4);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], session_id[0], sk[0], NULL, msg, &keyagg_cache, max64) == 0);
    CHECK(ecount == 5);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], session_id[0], sk[0], &invalid_pk, msg, &keyagg_cache, max64) == 0);
    CHECK(ecount == 6);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], session_id[0], sk[0], &pk[0], NULL, &keyagg_cache, max64) == 1);
    CHECK(ecount == 6);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], session_id[0], sk[0], &pk[0], msg, NULL, max64) == 1);
    CHECK(ecount == 6);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], session_id[0], sk[0], &pk[0], msg, &invalid_keyagg_cache, max64) == 0);
    CHECK(ecount == 7);
    CHECK(memcmp_and_randomize(secnonce[0].data, zeros132, sizeof(secnonce[0].data)) == 0);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], session_id[0], sk[0], &pk[0], msg, &keyagg_cache, NULL) == 1);
    CHECK(ecount == 7);

    /* Every in-argument except session_id and pubkey can be NULL */
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[0], &pubnonce[0], session_id[0], NULL, &pk[0], NULL, NULL, NULL) == 1);
    CHECK(secp256k1_musig_nonce_gen(sign, &secnonce[1], &pubnonce[1], session_id[1], sk[1], &pk[1], NULL, NULL, NULL) == 1);

    /** Serialize and parse public nonces **/
    ecount = 0;
    CHECK(secp256k1_musig_pubnonce_serialize(none, NULL, &pubnonce[0]) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_pubnonce_serialize(none, pubnonce_ser, NULL) == 0);
    CHECK(ecount == 2);
    CHECK(memcmp_and_randomize(pubnonce_ser, zeros132, sizeof(pubnonce_ser)) == 0);
    CHECK(secp256k1_musig_pubnonce_serialize(none, pubnonce_ser, &invalid_pubnonce) == 0);
    CHECK(ecount == 3);
    CHECK(memcmp_and_randomize(pubnonce_ser, zeros132, sizeof(pubnonce_ser)) == 0);
    CHECK(secp256k1_musig_pubnonce_serialize(none, pubnonce_ser, &pubnonce[0]) == 1);

    ecount = 0;
    CHECK(secp256k1_musig_pubnonce_parse(none, &pubnonce[0], pubnonce_ser) == 1);
    CHECK(secp256k1_musig_pubnonce_parse(none, NULL, pubnonce_ser) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_pubnonce_parse(none, &pubnonce[0], NULL) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_pubnonce_parse(none, &pubnonce[0], zeros132) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_pubnonce_parse(none, &pubnonce[0], pubnonce_ser) == 1);

    {
        /* Check that serialize and parse results in the same value */
        secp256k1_musig_pubnonce tmp;
        CHECK(secp256k1_musig_pubnonce_serialize(none, pubnonce_ser, &pubnonce[0]) == 1);
        CHECK(secp256k1_musig_pubnonce_parse(none, &tmp, pubnonce_ser) == 1);
        CHECK(secp256k1_memcmp_var(&tmp, &pubnonce[0], sizeof(tmp)) == 0);
    }

    /** Receive nonces and aggregate **/
    ecount = 0;
    CHECK(secp256k1_musig_nonce_agg(none, &aggnonce, pubnonce_ptr, 2) == 1);
    CHECK(secp256k1_musig_nonce_agg(none, NULL, pubnonce_ptr, 2) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_nonce_agg(none, &aggnonce, NULL, 2) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_nonce_agg(none, &aggnonce, pubnonce_ptr, 0) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_nonce_agg(none, &aggnonce, invalid_pubnonce_ptr, 1) == 0);
    CHECK(ecount == 4);
    CHECK(secp256k1_musig_nonce_agg(none, &aggnonce, inf_pubnonce_ptr, 2) == 1);
    {
        /* Check that the aggnonce encodes two points at infinity */
        secp256k1_ge aggnonce_pt[2];
        secp256k1_musig_aggnonce_load(ctx, aggnonce_pt, &aggnonce);
        for (i = 0; i < 2; i++) {
            secp256k1_ge_is_infinity(&aggnonce_pt[i]);
        }
    }
    CHECK(ecount == 4);
    CHECK(secp256k1_musig_nonce_agg(none, &aggnonce, pubnonce_ptr, 2) == 1);

    /** Serialize and parse aggregate nonces **/
    ecount = 0;
    CHECK(secp256k1_musig_aggnonce_serialize(none, aggnonce_ser, &aggnonce) == 1);
    CHECK(secp256k1_musig_aggnonce_serialize(none, NULL, &aggnonce) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_aggnonce_serialize(none, aggnonce_ser, NULL) == 0);
    CHECK(ecount == 2);
    CHECK(memcmp_and_randomize(aggnonce_ser, zeros132, sizeof(aggnonce_ser)) == 0);
    CHECK(secp256k1_musig_aggnonce_serialize(none, aggnonce_ser, (secp256k1_musig_aggnonce*) &invalid_pubnonce) == 0);
    CHECK(ecount == 3);
    CHECK(memcmp_and_randomize(aggnonce_ser, zeros132, sizeof(aggnonce_ser)) == 0);
    CHECK(secp256k1_musig_aggnonce_serialize(none, aggnonce_ser, &aggnonce) == 1);

    ecount = 0;
    CHECK(secp256k1_musig_aggnonce_parse(none, &aggnonce, aggnonce_ser) == 1);
    CHECK(secp256k1_musig_aggnonce_parse(none, NULL, aggnonce_ser) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_aggnonce_parse(none, &aggnonce, NULL) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_aggnonce_parse(none, &aggnonce, zeros132) == 1);
    CHECK(secp256k1_musig_aggnonce_parse(none, &aggnonce, aggnonce_ser) == 1);

    {
        /* Check that serialize and parse results in the same value */
        secp256k1_musig_aggnonce tmp;
        CHECK(secp256k1_musig_aggnonce_serialize(none, aggnonce_ser, &aggnonce) == 1);
        CHECK(secp256k1_musig_aggnonce_parse(none, &tmp, aggnonce_ser) == 1);
        CHECK(secp256k1_memcmp_var(&tmp, &aggnonce, sizeof(tmp)) == 0);
    }

    /** Process nonces **/
    ecount = 0;
    CHECK(secp256k1_musig_nonce_process(none, &session, &aggnonce, msg, &keyagg_cache, &adaptor) == 1);
    CHECK(secp256k1_musig_nonce_process(sign, &session, &aggnonce, msg, &keyagg_cache, &adaptor) == 1);
    CHECK(secp256k1_musig_nonce_process(vrfy, NULL, &aggnonce, msg, &keyagg_cache, &adaptor) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_nonce_process(vrfy, &session, NULL, msg, &keyagg_cache, &adaptor) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_nonce_process(vrfy, &session, (secp256k1_musig_aggnonce*) &invalid_pubnonce, msg, &keyagg_cache, &adaptor) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_nonce_process(vrfy, &session, &aggnonce, NULL, &keyagg_cache, &adaptor) == 0);
    CHECK(ecount == 4);
    CHECK(secp256k1_musig_nonce_process(vrfy, &session, &aggnonce, msg, NULL, &adaptor) == 0);
    CHECK(ecount == 5);
    CHECK(secp256k1_musig_nonce_process(vrfy, &session, &aggnonce, msg, &invalid_keyagg_cache, &adaptor) == 0);
    CHECK(ecount == 6);
    CHECK(secp256k1_musig_nonce_process(vrfy, &session, &aggnonce, msg, &keyagg_cache, NULL) == 1);
    CHECK(ecount == 6);
    CHECK(secp256k1_musig_nonce_process(vrfy, &session, &aggnonce, msg, &keyagg_cache, (secp256k1_pubkey *)&invalid_pk) == 0);
    CHECK(ecount == 7);

    CHECK(secp256k1_musig_nonce_process(vrfy, &session, &aggnonce, msg, &keyagg_cache, &adaptor) == 1);

    ecount = 0;
    memcpy(&secnonce_tmp, &secnonce[0], sizeof(secnonce_tmp));
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &secnonce_tmp, &keypair[0], &keyagg_cache, &session) == 1);
    /* The secnonce is set to 0 and subsequent signing attempts fail */
    CHECK(secp256k1_memcmp_var(&secnonce_tmp, zeros132, sizeof(secnonce_tmp)) == 0);
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &secnonce_tmp, &keypair[0], &keyagg_cache, &session) == 0);
    CHECK(ecount == 1);
    memcpy(&secnonce_tmp, &secnonce[0], sizeof(secnonce_tmp));
    CHECK(secp256k1_musig_partial_sign(none, NULL, &secnonce_tmp, &keypair[0], &keyagg_cache, &session) == 0);
    CHECK(ecount == 2);
    memcpy(&secnonce_tmp, &secnonce[0], sizeof(secnonce_tmp));
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], NULL, &keypair[0], &keyagg_cache, &session) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &invalid_secnonce, &keypair[0], &keyagg_cache, &session) == 0);
    CHECK(ecount == 4);
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &secnonce_tmp, NULL, &keyagg_cache, &session) == 0);
    CHECK(ecount == 5);
    memcpy(&secnonce_tmp, &secnonce[0], sizeof(secnonce_tmp));
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &secnonce_tmp, &invalid_keypair, &keyagg_cache, &session) == 0);
    CHECK(ecount == 6);
    memcpy(&secnonce_tmp, &secnonce[0], sizeof(secnonce_tmp));
    {
        unsigned char sk_tmp[32];
        secp256k1_keypair keypair_tmp;
        secp256k1_testrand256(sk_tmp);
        CHECK(secp256k1_keypair_create(ctx, &keypair_tmp, sk_tmp));
        CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &secnonce_tmp, &keypair_tmp, &keyagg_cache, &session) == 0);
        CHECK(ecount == 7);
        memcpy(&secnonce_tmp, &secnonce[0], sizeof(secnonce_tmp));
    }
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &secnonce_tmp, &keypair[0], NULL, &session) == 0);
    CHECK(ecount == 8);
    memcpy(&secnonce_tmp, &secnonce[0], sizeof(secnonce_tmp));
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &secnonce_tmp, &keypair[0], &invalid_keyagg_cache, &session) == 0);
    CHECK(ecount == 9);
    memcpy(&secnonce_tmp, &secnonce[0], sizeof(secnonce_tmp));
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &secnonce_tmp, &keypair[0], &keyagg_cache, NULL) == 0);
    CHECK(ecount == 10);
    memcpy(&secnonce_tmp, &secnonce[0], sizeof(secnonce_tmp));
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &secnonce_tmp, &keypair[0], &keyagg_cache, &invalid_session) == 0);
    CHECK(ecount == 11);
    memcpy(&secnonce_tmp, &secnonce[0], sizeof(secnonce_tmp));

    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[0], &secnonce[0], &keypair[0], &keyagg_cache, &session) == 1);
    CHECK(secp256k1_musig_partial_sign(none, &partial_sig[1], &secnonce[1], &keypair[1], &keyagg_cache, &session) == 1);

    ecount = 0;
    CHECK(secp256k1_musig_partial_sig_serialize(none, buf, &partial_sig[0]) == 1);
    CHECK(secp256k1_musig_partial_sig_serialize(none, NULL, &partial_sig[0]) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_partial_sig_serialize(none, buf, NULL) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_partial_sig_parse(none, &partial_sig[0], buf) == 1);
    CHECK(secp256k1_musig_partial_sig_parse(none, NULL, buf) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_partial_sig_parse(none, &partial_sig[0], max64) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_partial_sig_parse(none, &partial_sig[0], NULL) == 0);
    CHECK(ecount == 4);

    {
        /* Check that serialize and parse results in the same value */
        secp256k1_musig_partial_sig tmp;
        CHECK(secp256k1_musig_partial_sig_serialize(none, buf, &partial_sig[0]) == 1);
        CHECK(secp256k1_musig_partial_sig_parse(none, &tmp, buf) == 1);
        CHECK(secp256k1_memcmp_var(&tmp, &partial_sig[0], sizeof(tmp)) == 0);
    }

    /** Partial signature verification */
    ecount = 0;
    CHECK(secp256k1_musig_partial_sig_verify(none, &partial_sig[0], &pubnonce[0], &pk[0], &keyagg_cache, &session) == 1);
    CHECK(secp256k1_musig_partial_sig_verify(sign, &partial_sig[0], &pubnonce[0], &pk[0], &keyagg_cache, &session) == 1);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[0], &pubnonce[0], &pk[0], &keyagg_cache, &session) == 1);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[1], &pubnonce[0], &pk[0], &keyagg_cache, &session) == 0);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, NULL, &pubnonce[0], &pk[0], &keyagg_cache, &session) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &invalid_partial_sig, &pubnonce[0], &pk[0], &keyagg_cache, &session) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[0], NULL, &pk[0], &keyagg_cache, &session) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[0], &invalid_pubnonce, &pk[0], &keyagg_cache, &session) == 0);
    CHECK(ecount == 4);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[0], &pubnonce[0], NULL, &keyagg_cache, &session) == 0);
    CHECK(ecount == 5);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[0], &pubnonce[0], &invalid_pk, &keyagg_cache, &session) == 0);
    CHECK(ecount == 6);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[0], &pubnonce[0], &pk[0], NULL, &session) == 0);
    CHECK(ecount == 7);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[0], &pubnonce[0], &pk[0], &invalid_keyagg_cache, &session) == 0);
    CHECK(ecount == 8);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[0], &pubnonce[0], &pk[0], &keyagg_cache, NULL) == 0);
    CHECK(ecount == 9);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[0], &pubnonce[0], &pk[0], &keyagg_cache, &invalid_session) == 0);
    CHECK(ecount == 10);

    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[0], &pubnonce[0], &pk[0], &keyagg_cache, &session) == 1);
    CHECK(secp256k1_musig_partial_sig_verify(vrfy, &partial_sig[1], &pubnonce[1], &pk[1], &keyagg_cache, &session) == 1);

    /** Signature aggregation and verification */
    ecount = 0;
    CHECK(secp256k1_musig_partial_sig_agg(none, pre_sig, &session, partial_sig_ptr, 2) == 1);
    CHECK(secp256k1_musig_partial_sig_agg(none, NULL, &session, partial_sig_ptr, 2) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_partial_sig_agg(none, pre_sig, NULL, partial_sig_ptr, 2) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_partial_sig_agg(none, pre_sig, &invalid_session, partial_sig_ptr, 2) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_partial_sig_agg(none, pre_sig, &session, NULL, 2) == 0);
    CHECK(ecount == 4);
    CHECK(secp256k1_musig_partial_sig_agg(none, pre_sig, &session, invalid_partial_sig_ptr, 2) == 0);
    CHECK(ecount == 5);
    CHECK(secp256k1_musig_partial_sig_agg(none, pre_sig, &session, partial_sig_ptr, 0) == 0);
    CHECK(ecount == 6);
    CHECK(secp256k1_musig_partial_sig_agg(none, pre_sig, &session, partial_sig_ptr, 1) == 1);
    CHECK(secp256k1_musig_partial_sig_agg(none, pre_sig, &session, partial_sig_ptr, 2) == 1);

    /** Adaptor signature verification */
    ecount = 0;
    CHECK(secp256k1_musig_nonce_parity(none, &nonce_parity, &session) == 1);
    CHECK(secp256k1_musig_nonce_parity(none, NULL, &session) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_nonce_parity(none, &nonce_parity, NULL) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_nonce_parity(none, &nonce_parity, &invalid_session) == 0);
    CHECK(ecount == 3);

    ecount = 0;
    CHECK(secp256k1_musig_adapt(none, final_sig, pre_sig, sec_adaptor, nonce_parity) == 1);
    CHECK(secp256k1_musig_adapt(none, NULL, pre_sig, sec_adaptor, 0) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_adapt(none, final_sig, NULL, sec_adaptor, 0) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_adapt(none, final_sig, max64, sec_adaptor, 0) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_adapt(none, final_sig, pre_sig, NULL, 0) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_adapt(none, final_sig, pre_sig, max64, 0) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_adapt(none, final_sig, pre_sig, sec_adaptor, 2) == 0);
    CHECK(ecount == 4);
    /* sig and pre_sig argument point to the same location */
    memcpy(final_sig, pre_sig, sizeof(final_sig));
    CHECK(secp256k1_musig_adapt(none, final_sig, final_sig, sec_adaptor, nonce_parity) == 1);
    CHECK(secp256k1_schnorrsig_verify(vrfy, final_sig, msg, sizeof(msg), &agg_pk) == 1);

    CHECK(secp256k1_musig_adapt(none, final_sig, pre_sig, sec_adaptor, nonce_parity) == 1);
    CHECK(secp256k1_schnorrsig_verify(vrfy, final_sig, msg, sizeof(msg), &agg_pk) == 1);

    /** Secret adaptor can be extracted from signature */
    ecount = 0;
    CHECK(secp256k1_musig_extract_adaptor(none, sec_adaptor1, final_sig, pre_sig, nonce_parity) == 1);
    CHECK(secp256k1_memcmp_var(sec_adaptor, sec_adaptor1, 32) == 0);
    /* wrong nonce parity */
    CHECK(secp256k1_musig_extract_adaptor(none, sec_adaptor1, final_sig, pre_sig, !nonce_parity) == 1);
    CHECK(secp256k1_memcmp_var(sec_adaptor, sec_adaptor1, 32) != 0);
    CHECK(secp256k1_musig_extract_adaptor(none, NULL, final_sig, pre_sig, 0) == 0);
    CHECK(ecount == 1);
    CHECK(secp256k1_musig_extract_adaptor(none, sec_adaptor1, NULL, pre_sig, 0) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_extract_adaptor(none, sec_adaptor1, max64, pre_sig, 0) == 0);
    CHECK(ecount == 2);
    CHECK(secp256k1_musig_extract_adaptor(none, sec_adaptor1, final_sig, NULL, 0) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_extract_adaptor(none, sec_adaptor1, final_sig, max64, 0) == 0);
    CHECK(ecount == 3);
    CHECK(secp256k1_musig_extract_adaptor(none, sec_adaptor1, final_sig, pre_sig, 2) == 0);
    CHECK(ecount == 4);

    /** cleanup **/
    secp256k1_context_destroy(none);
    secp256k1_context_destroy(sign);
    secp256k1_context_destroy(vrfy);
    secp256k1_context_destroy(sttc);
}

void musig_nonce_bitflip(unsigned char **args, size_t n_flip, size_t n_bytes) {
    secp256k1_scalar k1[2], k2[2];

    secp256k1_nonce_function_musig(k1, args[0], args[1], args[2], args[3], args[4], args[5]);
    secp256k1_testrand_flip(args[n_flip], n_bytes);
    secp256k1_nonce_function_musig(k2, args[0], args[1], args[2], args[3], args[4], args[5]);
    CHECK(secp256k1_scalar_eq(&k1[0], &k2[0]) == 0);
    CHECK(secp256k1_scalar_eq(&k1[1], &k2[1]) == 0);
}

void musig_nonce_test(void) {
    unsigned char *args[6];
    unsigned char session_id[32];
    unsigned char sk[32];
    unsigned char pk[33];
    unsigned char msg[32];
    unsigned char agg_pk[32];
    unsigned char extra_input[32];
    int i, j;
    secp256k1_scalar k[6][2];

    secp256k1_testrand_bytes_test(session_id, sizeof(session_id));
    secp256k1_testrand_bytes_test(sk, sizeof(sk));
    secp256k1_testrand_bytes_test(pk, sizeof(pk));
    secp256k1_testrand_bytes_test(msg, sizeof(msg));
    secp256k1_testrand_bytes_test(agg_pk, sizeof(agg_pk));
    secp256k1_testrand_bytes_test(extra_input, sizeof(extra_input));

    /* Check that a bitflip in an argument results in different nonces. */
    args[0] = session_id;
    args[1] = msg;
    args[2] = sk;
    args[3] = pk;
    args[4] = agg_pk;
    args[5] = extra_input;
    for (i = 0; i < count; i++) {
        musig_nonce_bitflip(args, 0, sizeof(session_id));
        musig_nonce_bitflip(args, 1, sizeof(msg));
        musig_nonce_bitflip(args, 2, sizeof(sk));
        musig_nonce_bitflip(args, 3, sizeof(pk));
        musig_nonce_bitflip(args, 4, sizeof(agg_pk));
        musig_nonce_bitflip(args, 5, sizeof(extra_input));
    }
    /* Check that if any argument is NULL, a different nonce is produced than if
     * any other argument is NULL. */
    memcpy(msg, session_id, sizeof(msg));
    memcpy(sk, session_id, sizeof(sk));
    memcpy(pk, session_id, sizeof(session_id));
    memcpy(agg_pk, session_id, sizeof(agg_pk));
    memcpy(extra_input, session_id, sizeof(extra_input));
    secp256k1_nonce_function_musig(k[0], args[0], args[1], args[2], args[3], args[4], args[5]);
    secp256k1_nonce_function_musig(k[1], args[0], NULL, args[2], args[3], args[4], args[5]);
    secp256k1_nonce_function_musig(k[2], args[0], args[1], NULL, args[3], args[4], args[5]);
    secp256k1_nonce_function_musig(k[3], args[0], args[1], args[2], NULL, args[4], args[5]);
    secp256k1_nonce_function_musig(k[4], args[0], args[1], args[2], args[3], NULL, args[5]);
    secp256k1_nonce_function_musig(k[5], args[0], args[1], args[2], args[3], args[4], NULL);
    for (i = 0; i < 6; i++) {
        CHECK(!secp256k1_scalar_eq(&k[i][0], &k[i][1]));
        for (j = i+1; j < 6; j++) {
            CHECK(!secp256k1_scalar_eq(&k[i][0], &k[j][0]));
            CHECK(!secp256k1_scalar_eq(&k[i][1], &k[j][1]));
        }
    }
}

void scriptless_atomic_swap(secp256k1_scratch_space *scratch) {
    /* Throughout this test "a" and "b" refer to two hypothetical blockchains,
     * while the indices 0 and 1 refer to the two signers. Here signer 0 is
     * sending a-coins to signer 1, while signer 1 is sending b-coins to signer
     * 0. Signer 0 produces the adaptor signatures. */
    unsigned char pre_sig_a[64];
    unsigned char final_sig_a[64];
    unsigned char pre_sig_b[64];
    unsigned char final_sig_b[64];
    secp256k1_musig_partial_sig partial_sig_a[2];
    const secp256k1_musig_partial_sig *partial_sig_a_ptr[2];
    secp256k1_musig_partial_sig partial_sig_b[2];
    const secp256k1_musig_partial_sig *partial_sig_b_ptr[2];
    unsigned char sec_adaptor[32];
    unsigned char sec_adaptor_extracted[32];
    secp256k1_pubkey pub_adaptor;
    unsigned char sk_a[2][32];
    unsigned char sk_b[2][32];
    secp256k1_keypair keypair_a[2];
    secp256k1_keypair keypair_b[2];
    secp256k1_pubkey pk_a[2];
    const secp256k1_pubkey *pk_a_ptr[2];
    secp256k1_pubkey pk_b[2];
    const secp256k1_pubkey *pk_b_ptr[2];
    secp256k1_musig_keyagg_cache keyagg_cache_a;
    secp256k1_musig_keyagg_cache keyagg_cache_b;
    secp256k1_xonly_pubkey agg_pk_a;
    secp256k1_xonly_pubkey agg_pk_b;
    secp256k1_musig_secnonce secnonce_a[2];
    secp256k1_musig_secnonce secnonce_b[2];
    secp256k1_musig_pubnonce pubnonce_a[2];
    secp256k1_musig_pubnonce pubnonce_b[2];
    const secp256k1_musig_pubnonce *pubnonce_ptr_a[2];
    const secp256k1_musig_pubnonce *pubnonce_ptr_b[2];
    secp256k1_musig_aggnonce aggnonce_a;
    secp256k1_musig_aggnonce aggnonce_b;
    secp256k1_musig_session session_a, session_b;
    int nonce_parity_a;
    int nonce_parity_b;
    unsigned char seed_a[2][32] = { "a0", "a1" };
    unsigned char seed_b[2][32] = { "b0", "b1" };
    const unsigned char msg32_a[32] = "this is the message blockchain a";
    const unsigned char msg32_b[32] = "this is the message blockchain b";
    int i;

    /* Step 1: key setup */
    for (i = 0; i < 2; i++) {
        pk_a_ptr[i] = &pk_a[i];
        pk_b_ptr[i] = &pk_b[i];
        pubnonce_ptr_a[i] = &pubnonce_a[i];
        pubnonce_ptr_b[i] = &pubnonce_b[i];
        partial_sig_a_ptr[i] = &partial_sig_a[i];
        partial_sig_b_ptr[i] = &partial_sig_b[i];

        secp256k1_testrand256(sk_a[i]);
        secp256k1_testrand256(sk_b[i]);
        CHECK(create_keypair_and_pk(&keypair_a[i], &pk_a[i], sk_a[i]) == 1);
        CHECK(create_keypair_and_pk(&keypair_b[i], &pk_b[i], sk_b[i]) == 1);
    }
    secp256k1_testrand256(sec_adaptor);
    CHECK(secp256k1_ec_pubkey_create(ctx, &pub_adaptor, sec_adaptor) == 1);

    CHECK(secp256k1_musig_pubkey_agg(ctx, scratch, &agg_pk_a, &keyagg_cache_a, pk_a_ptr, 2) == 1);
    CHECK(secp256k1_musig_pubkey_agg(ctx, scratch, &agg_pk_b, &keyagg_cache_b, pk_b_ptr, 2) == 1);

    CHECK(secp256k1_musig_nonce_gen(ctx, &secnonce_a[0], &pubnonce_a[0], seed_a[0], sk_a[0], &pk_a[0], NULL, NULL, NULL) == 1);
    CHECK(secp256k1_musig_nonce_gen(ctx, &secnonce_a[1], &pubnonce_a[1], seed_a[1], sk_a[1], &pk_a[1], NULL, NULL, NULL) == 1);
    CHECK(secp256k1_musig_nonce_gen(ctx, &secnonce_b[0], &pubnonce_b[0], seed_b[0], sk_b[0], &pk_b[0], NULL, NULL, NULL) == 1);
    CHECK(secp256k1_musig_nonce_gen(ctx, &secnonce_b[1], &pubnonce_b[1], seed_b[1], sk_b[1], &pk_b[1], NULL, NULL, NULL) == 1);

    /* Step 2: Exchange nonces */
    CHECK(secp256k1_musig_nonce_agg(ctx, &aggnonce_a, pubnonce_ptr_a, 2) == 1);
    CHECK(secp256k1_musig_nonce_process(ctx, &session_a, &aggnonce_a, msg32_a, &keyagg_cache_a, &pub_adaptor) == 1);
    CHECK(secp256k1_musig_nonce_parity(ctx, &nonce_parity_a, &session_a) == 1);
    CHECK(secp256k1_musig_nonce_agg(ctx, &aggnonce_b, pubnonce_ptr_b, 2) == 1);
    CHECK(secp256k1_musig_nonce_process(ctx, &session_b, &aggnonce_b, msg32_b, &keyagg_cache_b, &pub_adaptor) == 1);
    CHECK(secp256k1_musig_nonce_parity(ctx, &nonce_parity_b, &session_b) == 1);

    /* Step 3: Signer 0 produces partial signatures for both chains. */
    CHECK(secp256k1_musig_partial_sign(ctx, &partial_sig_a[0], &secnonce_a[0], &keypair_a[0], &keyagg_cache_a, &session_a) == 1);
    CHECK(secp256k1_musig_partial_sign(ctx, &partial_sig_b[0], &secnonce_b[0], &keypair_b[0], &keyagg_cache_b, &session_b) == 1);

    /* Step 4: Signer 1 receives partial signatures, verifies them and creates a
     * partial signature to send B-coins to signer 0. */
    CHECK(secp256k1_musig_partial_sig_verify(ctx, &partial_sig_a[0], &pubnonce_a[0], &pk_a[0], &keyagg_cache_a, &session_a) == 1);
    CHECK(secp256k1_musig_partial_sig_verify(ctx, &partial_sig_b[0], &pubnonce_b[0], &pk_b[0], &keyagg_cache_b, &session_b) == 1);
    CHECK(secp256k1_musig_partial_sign(ctx, &partial_sig_b[1], &secnonce_b[1], &keypair_b[1], &keyagg_cache_b, &session_b) == 1);

    /* Step 5: Signer 0 aggregates its own partial signature with the partial
     * signature from signer 1 and adapts it. This results in a complete
     * signature which is broadcasted by signer 0 to take B-coins. */
    CHECK(secp256k1_musig_partial_sig_agg(ctx, pre_sig_b, &session_b, partial_sig_b_ptr, 2) == 1);
    CHECK(secp256k1_musig_adapt(ctx, final_sig_b, pre_sig_b, sec_adaptor, nonce_parity_b) == 1);
    CHECK(secp256k1_schnorrsig_verify(ctx, final_sig_b, msg32_b, sizeof(msg32_b), &agg_pk_b) == 1);

    /* Step 6: Signer 1 signs, extracts adaptor from the published signature,
     * and adapts the signature to take A-coins. */
    CHECK(secp256k1_musig_partial_sign(ctx, &partial_sig_a[1], &secnonce_a[1], &keypair_a[1], &keyagg_cache_a, &session_a) == 1);
    CHECK(secp256k1_musig_partial_sig_agg(ctx, pre_sig_a, &session_a, partial_sig_a_ptr, 2) == 1);
    CHECK(secp256k1_musig_extract_adaptor(ctx, sec_adaptor_extracted, final_sig_b, pre_sig_b, nonce_parity_b) == 1);
    CHECK(secp256k1_memcmp_var(sec_adaptor_extracted, sec_adaptor, sizeof(sec_adaptor)) == 0); /* in real life we couldn't check this, of course */
    CHECK(secp256k1_musig_adapt(ctx, final_sig_a, pre_sig_a, sec_adaptor_extracted, nonce_parity_a) == 1);
    CHECK(secp256k1_schnorrsig_verify(ctx, final_sig_a, msg32_a, sizeof(msg32_a), &agg_pk_a) == 1);
}

void sha256_tag_test_internal(secp256k1_sha256 *sha_tagged, unsigned char *tag, size_t taglen) {
    secp256k1_sha256 sha;
    unsigned char buf[32];
    unsigned char buf2[32];
    size_t i;

    secp256k1_sha256_initialize(&sha);
    secp256k1_sha256_write(&sha, tag, taglen);
    secp256k1_sha256_finalize(&sha, buf);
    /* buf = SHA256(tag) */

    secp256k1_sha256_initialize(&sha);
    secp256k1_sha256_write(&sha, buf, 32);
    secp256k1_sha256_write(&sha, buf, 32);
    /* Is buffer fully consumed? */
    CHECK((sha.bytes & 0x3F) == 0);

    /* Compare with tagged SHA */
    for (i = 0; i < 8; i++) {
        CHECK(sha_tagged->s[i] == sha.s[i]);
    }
    secp256k1_sha256_write(&sha, buf, 32);
    secp256k1_sha256_write(sha_tagged, buf, 32);
    secp256k1_sha256_finalize(&sha, buf);
    secp256k1_sha256_finalize(sha_tagged, buf2);
    CHECK(secp256k1_memcmp_var(buf, buf2, 32) == 0);
}

/* Checks that the initialized tagged hashes initialized have the expected
 * state. */
void sha256_tag_test(void) {
    secp256k1_sha256 sha_tagged;
    {
        char tag[11] = "KeyAgg list";
        secp256k1_musig_keyagglist_sha256(&sha_tagged);
        sha256_tag_test_internal(&sha_tagged, (unsigned char*)tag, sizeof(tag));
    }
    {
        char tag[18] = "KeyAgg coefficient";
        secp256k1_musig_keyaggcoef_sha256(&sha_tagged);
        sha256_tag_test_internal(&sha_tagged, (unsigned char*)tag, sizeof(tag));
    }
}

/* Attempts to create a signature for the aggregate public key using given secret
 * keys and keyagg_cache. */
void musig_tweak_test_helper(const secp256k1_xonly_pubkey* agg_pk, const unsigned char *sk0, const unsigned char *sk1, secp256k1_musig_keyagg_cache *keyagg_cache) {
    secp256k1_pubkey pk[2];
    unsigned char session_id[2][32];
    unsigned char msg[32];
    secp256k1_musig_secnonce secnonce[2];
    secp256k1_musig_pubnonce pubnonce[2];
    const secp256k1_musig_pubnonce *pubnonce_ptr[2];
    secp256k1_musig_aggnonce aggnonce;
    secp256k1_keypair keypair[2];
    secp256k1_musig_session session;
    secp256k1_musig_partial_sig partial_sig[2];
    const secp256k1_musig_partial_sig *partial_sig_ptr[2];
    unsigned char final_sig[64];
    int i;

    for (i = 0; i < 2; i++) {
        pubnonce_ptr[i] = &pubnonce[i];
        partial_sig_ptr[i] = &partial_sig[i];

        secp256k1_testrand256(session_id[i]);
    }
    CHECK(create_keypair_and_pk(&keypair[0], &pk[0], sk0) == 1);
    CHECK(create_keypair_and_pk(&keypair[1], &pk[1], sk1) == 1);
    secp256k1_testrand256(msg);

    CHECK(secp256k1_musig_nonce_gen(ctx, &secnonce[0], &pubnonce[0], session_id[0], sk0, &pk[0], NULL, NULL, NULL) == 1);
    CHECK(secp256k1_musig_nonce_gen(ctx, &secnonce[1], &pubnonce[1], session_id[1], sk1, &pk[1], NULL, NULL, NULL) == 1);

    CHECK(secp256k1_musig_nonce_agg(ctx, &aggnonce, pubnonce_ptr, 2) == 1);
    CHECK(secp256k1_musig_nonce_process(ctx, &session, &aggnonce, msg, keyagg_cache, NULL) == 1);

    CHECK(secp256k1_musig_partial_sign(ctx, &partial_sig[0], &secnonce[0], &keypair[0], keyagg_cache, &session) == 1);
    CHECK(secp256k1_musig_partial_sign(ctx, &partial_sig[1], &secnonce[1], &keypair[1], keyagg_cache, &session) == 1);

    CHECK(secp256k1_musig_partial_sig_verify(ctx, &partial_sig[0], &pubnonce[0], &pk[0], keyagg_cache, &session) == 1);
    CHECK(secp256k1_musig_partial_sig_verify(ctx, &partial_sig[1], &pubnonce[1], &pk[1], keyagg_cache, &session) == 1);

    CHECK(secp256k1_musig_partial_sig_agg(ctx, final_sig, &session, partial_sig_ptr, 2) == 1);
    CHECK(secp256k1_schnorrsig_verify(ctx, final_sig, msg, sizeof(msg), agg_pk) == 1);
}

/* Create aggregate public key P[0], tweak multiple times (using xonly and
 * plain tweaking) and test signing. */
void musig_tweak_test(secp256k1_scratch_space *scratch) {
    unsigned char sk[2][32];
    secp256k1_pubkey pk[2];
    const secp256k1_pubkey *pk_ptr[2];
    secp256k1_musig_keyagg_cache keyagg_cache;
    enum { N_TWEAKS = 8 };
    secp256k1_pubkey P[N_TWEAKS + 1];
    secp256k1_xonly_pubkey P_xonly[N_TWEAKS + 1];
    int i;

    /* Key Setup */
    for (i = 0; i < 2; i++) {
        pk_ptr[i] = &pk[i];
        secp256k1_testrand256(sk[i]);
        CHECK(create_keypair_and_pk(NULL, &pk[i], sk[i]) == 1);
    }
    /* Compute P0 = keyagg(pk0, pk1) and test signing for it */
    CHECK(secp256k1_musig_pubkey_agg(ctx, scratch, &P_xonly[0], &keyagg_cache, pk_ptr, 2) == 1);
    musig_tweak_test_helper(&P_xonly[0], sk[0], sk[1], &keyagg_cache);
    CHECK(secp256k1_musig_pubkey_get(ctx, &P[0], &keyagg_cache));

    /* Compute Pi = f(Pj) + tweaki*G where where j = i-1 and try signing for
     * that key. If xonly is set to true, the function f is normalizes the input
     * point to have an even X-coordinate ("xonly-tweaking").
     * Otherwise, the function f is the identity function. */
    for (i = 1; i <= N_TWEAKS; i++) {
        unsigned char tweak[32];
        int P_parity;
        int xonly = secp256k1_testrand_bits(1);

        secp256k1_testrand256(tweak);
        if (xonly) {
            CHECK(secp256k1_musig_pubkey_xonly_tweak_add(ctx, &P[i], &keyagg_cache, tweak) == 1);
        } else {
            CHECK(secp256k1_musig_pubkey_ec_tweak_add(ctx, &P[i], &keyagg_cache, tweak) == 1);
        }
        CHECK(secp256k1_xonly_pubkey_from_pubkey(ctx, &P_xonly[i], &P_parity, &P[i]));
        /* Check that musig_pubkey_tweak_add produces same result as
         * xonly_pubkey_tweak_add or ec_pubkey_tweak_add. */
        if (xonly) {
            unsigned char P_serialized[32];
            CHECK(secp256k1_xonly_pubkey_serialize(ctx, P_serialized, &P_xonly[i]));
            CHECK(secp256k1_xonly_pubkey_tweak_add_check(ctx, P_serialized, P_parity, &P_xonly[i-1], tweak) == 1);
        } else {
            secp256k1_pubkey tmp_key = P[i-1];
            CHECK(secp256k1_ec_pubkey_tweak_add(ctx, &tmp_key, tweak));
            CHECK(secp256k1_memcmp_var(&tmp_key, &P[i], sizeof(tmp_key)) == 0);
        }
        /* Test signing for P[i] */
        musig_tweak_test_helper(&P_xonly[i], sk[0], sk[1], &keyagg_cache);
    }
}

int musig_vectors_keyagg_and_tweak(enum MUSIG_ERROR *error,
                                   secp256k1_musig_keyagg_cache *keyagg_cache,
                                   unsigned char *agg_pk_ser,
                                   const unsigned char pubkeys33[][33],
                                   const unsigned char tweaks32[][32],
                                   size_t key_indices_len,
                                   const size_t *key_indices,
                                   size_t tweak_indices_len,
                                   const size_t *tweak_indices,
                                   const int *is_xonly) {
    secp256k1_pubkey pubkeys[MUSIG_VECTORS_MAX_PUBKEYS];
    const secp256k1_pubkey *pk_ptr[MUSIG_VECTORS_MAX_PUBKEYS];
    int i;
    secp256k1_pubkey agg_pk;
    secp256k1_xonly_pubkey agg_pk_xonly;

    for (i = 0; i < (int)key_indices_len; i++) {
        if (!secp256k1_ec_pubkey_parse(ctx, &pubkeys[i], pubkeys33[key_indices[i]], 33)) {
            *error = MUSIG_PUBKEY;
            return 0;
        }
        pk_ptr[i] = &pubkeys[i];
    }
    if (!secp256k1_musig_pubkey_agg(ctx, NULL, NULL, keyagg_cache, pk_ptr, key_indices_len)) {
        *error = MUSIG_OTHER;
        return 0;
    }

    for (i = 0; i < (int)tweak_indices_len; i++) {
        if (is_xonly[i]) {
            if (!secp256k1_musig_pubkey_xonly_tweak_add(ctx, NULL, keyagg_cache, tweaks32[tweak_indices[i]])) {
                *error = MUSIG_TWEAK;
                return 0;
            }
        } else {
            if (!secp256k1_musig_pubkey_ec_tweak_add(ctx, NULL, keyagg_cache, tweaks32[tweak_indices[i]])) {
                *error = MUSIG_TWEAK;
                return 0;
            }
        }
    }
    if (!secp256k1_musig_pubkey_get(ctx, &agg_pk, keyagg_cache)) {
        *error = MUSIG_OTHER;
        return 0;
    }

    if (!secp256k1_xonly_pubkey_from_pubkey(ctx, &agg_pk_xonly, NULL, &agg_pk)) {
        *error = MUSIG_OTHER;
        return 0;
    }

    if (agg_pk_ser != NULL) {
        if (!secp256k1_xonly_pubkey_serialize(ctx, agg_pk_ser, &agg_pk_xonly)) {
            *error = MUSIG_OTHER;
            return 0;
        }
    }

    return 1;
}

void musig_test_vectors_keyagg(void) {
    size_t i;
    const struct musig_key_agg_vector *vector = &musig_key_agg_vector;

    for (i = 0; i < sizeof(vector->valid_case)/sizeof(vector->valid_case[0]); i++) {
        const struct musig_key_agg_valid_test_case *c = &vector->valid_case[i];
        enum MUSIG_ERROR error;
        secp256k1_musig_keyagg_cache keyagg_cache;
        unsigned char agg_pk[32];

        CHECK(musig_vectors_keyagg_and_tweak(&error, &keyagg_cache, agg_pk, vector->pubkeys, vector->tweaks, c->key_indices_len, c->key_indices, 0, NULL, NULL));
        CHECK(secp256k1_memcmp_var(agg_pk, c->expected, sizeof(agg_pk)) == 0);
    }

    for (i = 0; i < sizeof(vector->error_case)/sizeof(vector->error_case[0]); i++) {
        const struct musig_key_agg_error_test_case *c = &vector->error_case[i];
        enum MUSIG_ERROR error;
        secp256k1_musig_keyagg_cache keyagg_cache;

        CHECK(!musig_vectors_keyagg_and_tweak(&error, &keyagg_cache, NULL, vector->pubkeys, vector->tweaks, c->key_indices_len, c->key_indices, c->tweak_indices_len, c->tweak_indices, c->is_xonly));
        CHECK(c->error == error);
    }
}

void musig_test_vectors_noncegen(void) {
    size_t i;
    const struct musig_nonce_gen_vector *vector = &musig_nonce_gen_vector;

    for (i = 0; i < sizeof(vector->test_case)/sizeof(vector->test_case[0]); i++) {
        const struct musig_nonce_gen_test_case *c = &vector->test_case[i];
        secp256k1_musig_keyagg_cache keyagg_cache;
        secp256k1_musig_keyagg_cache *keyagg_cache_ptr = NULL;
        secp256k1_musig_secnonce secnonce;
        secp256k1_musig_pubnonce pubnonce;
        const unsigned char *sk = NULL;
        const unsigned char *msg = NULL;
        const unsigned char *extra_in = NULL;
        secp256k1_pubkey pk;
        unsigned char pubnonce66[66];

        if (c->has_sk) {
            sk = c->sk;
        }
        if (c->has_aggpk) {
            /* Create keyagg_cache from aggpk */
            secp256k1_keyagg_cache_internal cache_i;
            secp256k1_xonly_pubkey aggpk;
            memset(&cache_i, 0, sizeof(cache_i));
            CHECK(secp256k1_xonly_pubkey_parse(ctx, &aggpk, c->aggpk));
            CHECK(secp256k1_xonly_pubkey_load(ctx, &cache_i.pk, &aggpk));
            secp256k1_keyagg_cache_save(&keyagg_cache, &cache_i);
            keyagg_cache_ptr = &keyagg_cache;
        }
        if (c->has_msg) {
            msg = c->msg;
        }
        if (c->has_extra_in) {
            extra_in = c->extra_in;
        }

        CHECK(secp256k1_ec_pubkey_parse(ctx, &pk, c->pk, sizeof(c->pk)));
        CHECK(secp256k1_musig_nonce_gen(ctx, &secnonce, &pubnonce, c->rand_, sk, &pk, msg, keyagg_cache_ptr, extra_in) == 1);
        CHECK(secp256k1_memcmp_var(&secnonce.data[4], c->expected_secnonce, 2*32) == 0);
        CHECK(secp256k1_memcmp_var(&secnonce.data[4+2*32], &pk, sizeof(pk)) == 0);

        CHECK(secp256k1_musig_pubnonce_serialize(ctx, pubnonce66, &pubnonce) == 1);
        CHECK(sizeof(c->expected_pubnonce) == sizeof(pubnonce66));
        CHECK(secp256k1_memcmp_var(pubnonce66, c->expected_pubnonce, sizeof(pubnonce66)) == 0);
    }
}


void musig_test_vectors_nonceagg(void) {
    size_t i;
    int j;
    const struct musig_nonce_agg_vector *vector = &musig_nonce_agg_vector;

    for (i = 0; i < sizeof(vector->valid_case)/sizeof(vector->valid_case[0]); i++) {
        const struct musig_nonce_agg_test_case *c = &vector->valid_case[i];
        secp256k1_musig_pubnonce pubnonce[2];
        const secp256k1_musig_pubnonce *pubnonce_ptr[2];
        secp256k1_musig_aggnonce aggnonce;
        unsigned char aggnonce66[66];

        for (j = 0; j < 2; j++) {
            CHECK(secp256k1_musig_pubnonce_parse(ctx, &pubnonce[j], vector->pnonces[c->pnonce_indices[j]]) == 1);
            pubnonce_ptr[j] = &pubnonce[j];
        }
        CHECK(secp256k1_musig_nonce_agg(ctx, &aggnonce, pubnonce_ptr, 2));
        CHECK(secp256k1_musig_aggnonce_serialize(ctx, aggnonce66, &aggnonce));
        CHECK(secp256k1_memcmp_var(aggnonce66, c->expected, 33) == 0);
    }
    for (i = 0; i < sizeof(vector->error_case)/sizeof(vector->error_case[0]); i++) {
        const struct musig_nonce_agg_test_case *c = &vector->error_case[i];
        secp256k1_musig_pubnonce pubnonce[2];
        for (j = 0; j < 2; j++) {
            int expected = c->invalid_nonce_idx != j;
            CHECK(expected == secp256k1_musig_pubnonce_parse(ctx, &pubnonce[j], vector->pnonces[c->pnonce_indices[j]]));
        }
    }
}

void musig_test_set_secnonce(secp256k1_musig_secnonce *secnonce, const unsigned char *secnonce64, const secp256k1_pubkey *pubkey) {
    secp256k1_ge pk;
    secp256k1_scalar k[2];

    secp256k1_scalar_set_b32(&k[0], &secnonce64[0], NULL);
    secp256k1_scalar_set_b32(&k[1], &secnonce64[32], NULL);
    CHECK(secp256k1_pubkey_load(ctx, &pk, pubkey));
    secp256k1_musig_secnonce_save(secnonce, k, &pk);
}

void musig_test_vectors_signverify(void) {
    size_t i;
    const struct musig_sign_verify_vector *vector = &musig_sign_verify_vector;

    for (i = 0; i < sizeof(vector->valid_case)/sizeof(vector->valid_case[0]); i++) {
        const struct musig_valid_case *c = &vector->valid_case[i];
        enum MUSIG_ERROR error;
        secp256k1_musig_keyagg_cache keyagg_cache;
        secp256k1_pubkey pubkey;
        secp256k1_musig_pubnonce pubnonce;
        secp256k1_musig_aggnonce aggnonce;
        secp256k1_musig_session session;
        secp256k1_musig_partial_sig partial_sig;
        secp256k1_musig_secnonce secnonce;
        secp256k1_keypair keypair;
        unsigned char partial_sig32[32];

        CHECK(secp256k1_keypair_create(ctx, &keypair, vector->sk));
        CHECK(musig_vectors_keyagg_and_tweak(&error, &keyagg_cache, NULL, vector->pubkeys, NULL, c->key_indices_len, c->key_indices, 0, NULL, NULL));

        CHECK(secp256k1_musig_aggnonce_parse(ctx, &aggnonce, vector->aggnonces[c->aggnonce_index]));
        CHECK(secp256k1_musig_nonce_process(ctx, &session, &aggnonce, vector->msgs[c->msg_index], &keyagg_cache, NULL));

        CHECK(secp256k1_ec_pubkey_parse(ctx, &pubkey, vector->pubkeys[0], sizeof(vector->pubkeys[0])));
        musig_test_set_secnonce(&secnonce, vector->secnonces[0], &pubkey);
        CHECK(secp256k1_musig_partial_sign(ctx, &partial_sig, &secnonce, &keypair, &keyagg_cache, &session));
        CHECK(secp256k1_musig_partial_sig_serialize(ctx, partial_sig32, &partial_sig));
        CHECK(secp256k1_memcmp_var(partial_sig32, c->expected, sizeof(partial_sig32)) == 0);

        CHECK(secp256k1_musig_pubnonce_parse(ctx, &pubnonce, vector->pubnonces[0]));
        CHECK(secp256k1_musig_partial_sig_verify(ctx, &partial_sig, &pubnonce, &pubkey, &keyagg_cache, &session));
    }
    for (i = 0; i < sizeof(vector->sign_error_case)/sizeof(vector->sign_error_case[0]); i++) {
        const struct musig_sign_error_case *c = &vector->sign_error_case[i];
        enum MUSIG_ERROR error;
        secp256k1_musig_keyagg_cache keyagg_cache;
        secp256k1_pubkey pubkey;
        secp256k1_musig_aggnonce aggnonce;
        secp256k1_musig_session session;
        secp256k1_musig_partial_sig partial_sig;
        secp256k1_musig_secnonce secnonce;
        secp256k1_keypair keypair;
        int expected;

        if (i == 0) {
            /* Skip this vector since the implementation does not error out when
             * the signing key does not belong to any pubkey. */
            continue;
        }
        expected = c->error != MUSIG_PUBKEY;
        CHECK(expected == musig_vectors_keyagg_and_tweak(&error, &keyagg_cache, NULL, vector->pubkeys, NULL, c->key_indices_len, c->key_indices, 0, NULL, NULL));
        CHECK(expected || c->error == error);
        if (!expected) {
            continue;
        }

        expected = c->error != MUSIG_AGGNONCE;
        CHECK(expected == secp256k1_musig_aggnonce_parse(ctx, &aggnonce, vector->aggnonces[c->aggnonce_index]));
        if (!expected) {
            continue;
        }
        CHECK(secp256k1_musig_nonce_process(ctx, &session, &aggnonce, vector->msgs[c->msg_index], &keyagg_cache, NULL));

        CHECK(secp256k1_ec_pubkey_parse(ctx, &pubkey, vector->pubkeys[0], sizeof(vector->pubkeys[0])));
        musig_test_set_secnonce(&secnonce, vector->secnonces[c->secnonce_index], &pubkey);
        {
            /* In the last test vector we sign with an invalid secnonce, which
             * triggers an illegal_callback. Hence, we need to use a custom
             * context that does not abort in this case. */
            secp256k1_context *ctx_tmp = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
            int32_t ecount = 0;
            secp256k1_context_set_error_callback(ctx_tmp, counting_illegal_callback_fn, &ecount);
            secp256k1_context_set_illegal_callback(ctx_tmp, counting_illegal_callback_fn, &ecount);
            expected = c->error != MUSIG_SECNONCE;
            CHECK(expected == secp256k1_musig_partial_sign(ctx_tmp, &partial_sig, &secnonce, &keypair, &keyagg_cache, &session));
            CHECK((!expected) == ecount);
            secp256k1_context_destroy(ctx_tmp);
        }
    }
    for (i = 0; i < sizeof(vector->verify_fail_case)/sizeof(vector->verify_fail_case[0]); i++) {
        const struct musig_verify_fail_error_case *c = &vector->verify_fail_case[i];
        enum MUSIG_ERROR error;
        secp256k1_musig_keyagg_cache keyagg_cache;
        secp256k1_musig_aggnonce aggnonce;
        secp256k1_musig_session session;
        secp256k1_musig_partial_sig partial_sig;
        enum { NUM_PUBNONCES = 3 };
        secp256k1_musig_pubnonce pubnonce[NUM_PUBNONCES];
        const secp256k1_musig_pubnonce *pubnonce_ptr[NUM_PUBNONCES];
        secp256k1_pubkey pubkey;
        int expected;
        size_t j;

        CHECK(NUM_PUBNONCES <= c->nonce_indices_len);
        for (j = 0; j < c->nonce_indices_len; j++) {
            CHECK(secp256k1_musig_pubnonce_parse(ctx, &pubnonce[j], vector->pubnonces[c->nonce_indices[j]]));
            pubnonce_ptr[j] = &pubnonce[j];
        }

        CHECK(musig_vectors_keyagg_and_tweak(&error, &keyagg_cache, NULL, vector->pubkeys, NULL, c->key_indices_len, c->key_indices, 0, NULL, NULL));
        CHECK(secp256k1_musig_nonce_agg(ctx, &aggnonce, pubnonce_ptr, c->nonce_indices_len) == 1);
        CHECK(secp256k1_musig_nonce_process(ctx, &session, &aggnonce, vector->msgs[c->msg_index], &keyagg_cache, NULL));

        CHECK(secp256k1_ec_pubkey_parse(ctx, &pubkey, vector->pubkeys[c->signer_index], sizeof(vector->pubkeys[0])));

        expected = c->error != MUSIG_SIG;
        CHECK(expected == secp256k1_musig_partial_sig_parse(ctx, &partial_sig, c->sig));
        if (!expected) {
            continue;
        }
        expected = c->error != MUSIG_SIG_VERIFY;
        CHECK(expected == secp256k1_musig_partial_sig_verify(ctx, &partial_sig, pubnonce, &pubkey, &keyagg_cache, &session));
    }
    for (i = 0; i < sizeof(vector->verify_error_case)/sizeof(vector->verify_error_case[0]); i++) {
        const struct musig_verify_fail_error_case *c = &vector->verify_error_case[i];
        enum MUSIG_ERROR error;
        secp256k1_musig_keyagg_cache keyagg_cache;
        secp256k1_musig_pubnonce pubnonce;
        int expected;

        expected = c->error != MUSIG_PUBKEY;
        CHECK(expected == musig_vectors_keyagg_and_tweak(&error, &keyagg_cache, NULL, vector->pubkeys, NULL, c->key_indices_len, c->key_indices, 0, NULL, NULL));
        CHECK(expected || c->error == error);
        if (!expected) {
            continue;
        }
        expected = c->error != MUSIG_PUBNONCE;
        CHECK(expected == secp256k1_musig_pubnonce_parse(ctx, &pubnonce, vector->pubnonces[c->nonce_indices[c->signer_index]]));
    }
}

void musig_test_vectors_tweak(void) {
    size_t i;
    const struct musig_tweak_vector *vector = &musig_tweak_vector;
    secp256k1_pubkey pubkey;
    secp256k1_musig_aggnonce aggnonce;
    secp256k1_musig_secnonce secnonce;

    CHECK(secp256k1_musig_aggnonce_parse(ctx, &aggnonce, vector->aggnonce));
    CHECK(secp256k1_ec_pubkey_parse(ctx, &pubkey, vector->pubkeys[0], sizeof(vector->pubkeys[0])));

    for (i = 0; i < sizeof(vector->valid_case)/sizeof(vector->valid_case[0]); i++) {
        const struct musig_tweak_case *c = &vector->valid_case[i];
        enum MUSIG_ERROR error;
        secp256k1_musig_keyagg_cache keyagg_cache;
        secp256k1_musig_pubnonce pubnonce;
        secp256k1_musig_session session;
        secp256k1_musig_partial_sig partial_sig;
        secp256k1_keypair keypair;
        unsigned char partial_sig32[32];

        musig_test_set_secnonce(&secnonce, vector->secnonce, &pubkey);

        CHECK(secp256k1_keypair_create(ctx, &keypair, vector->sk));
        CHECK(musig_vectors_keyagg_and_tweak(&error, &keyagg_cache, NULL, vector->pubkeys, vector->tweaks, c->key_indices_len, c->key_indices, c->tweak_indices_len, c->tweak_indices, c->is_xonly));

        CHECK(secp256k1_musig_nonce_process(ctx, &session, &aggnonce, vector->msg, &keyagg_cache, NULL));

        CHECK(secp256k1_musig_partial_sign(ctx, &partial_sig, &secnonce, &keypair, &keyagg_cache, &session));
        CHECK(secp256k1_musig_partial_sig_serialize(ctx, partial_sig32, &partial_sig));
        CHECK(secp256k1_memcmp_var(partial_sig32, c->expected, sizeof(partial_sig32)) == 0);

        CHECK(secp256k1_musig_pubnonce_parse(ctx, &pubnonce, vector->pubnonces[c->nonce_indices[c->signer_index]]));
        CHECK(secp256k1_musig_partial_sig_verify(ctx, &partial_sig, &pubnonce, &pubkey, &keyagg_cache, &session));
    }
    for (i = 0; i < sizeof(vector->error_case)/sizeof(vector->error_case[0]); i++) {
        const struct musig_tweak_case *c = &vector->error_case[i];
        enum MUSIG_ERROR error;
        secp256k1_musig_keyagg_cache keyagg_cache;
        CHECK(!musig_vectors_keyagg_and_tweak(&error, &keyagg_cache, NULL, vector->pubkeys, vector->tweaks, c->key_indices_len, c->key_indices, c->tweak_indices_len, c->tweak_indices, c->is_xonly));
        CHECK(error == MUSIG_TWEAK);
    }
}

void musig_test_vectors_sigagg(void) {
    size_t i, j;
    const struct musig_sig_agg_vector *vector = &musig_sig_agg_vector;

    for (i = 0; i < sizeof(vector->valid_case)/sizeof(vector->valid_case[0]); i++) {
        const struct musig_sig_agg_case *c = &vector->valid_case[i];
        enum MUSIG_ERROR error;
        unsigned char final_sig[64];
        secp256k1_musig_keyagg_cache keyagg_cache;
        unsigned char agg_pk32[32];
        secp256k1_xonly_pubkey agg_pk;
        secp256k1_musig_aggnonce aggnonce;
        secp256k1_musig_session session;
        secp256k1_musig_partial_sig partial_sig[(sizeof(vector->psigs)/sizeof(vector->psigs[0]))];
        const secp256k1_musig_partial_sig *partial_sig_ptr[(sizeof(vector->psigs)/sizeof(vector->psigs[0]))];

        CHECK(musig_vectors_keyagg_and_tweak(&error, &keyagg_cache, agg_pk32, vector->pubkeys, vector->tweaks, c->key_indices_len, c->key_indices, c->tweak_indices_len, c->tweak_indices, c->is_xonly));
        CHECK(secp256k1_musig_aggnonce_parse(ctx, &aggnonce, c->aggnonce));
        CHECK(secp256k1_musig_nonce_process(ctx, &session, &aggnonce, vector->msg, &keyagg_cache, NULL));
        for (j = 0; j < c->psig_indices_len; j++) {
            CHECK(secp256k1_musig_partial_sig_parse(ctx, &partial_sig[j], vector->psigs[c->psig_indices[j]]));
            partial_sig_ptr[j] = &partial_sig[j];
        }

        CHECK(secp256k1_musig_partial_sig_agg(ctx, final_sig, &session, partial_sig_ptr, c->psig_indices_len) == 1);
        CHECK(secp256k1_memcmp_var(final_sig, c->expected, sizeof(final_sig)) == 0);

        CHECK(secp256k1_xonly_pubkey_parse(ctx, &agg_pk, agg_pk32));
        CHECK(secp256k1_schnorrsig_verify(ctx, final_sig, vector->msg, sizeof(vector->msg), &agg_pk) == 1);
    }
    for (i = 0; i < sizeof(vector->error_case)/sizeof(vector->error_case[0]); i++) {
        const struct musig_sig_agg_case *c = &vector->error_case[i];
        secp256k1_musig_partial_sig partial_sig[(sizeof(vector->psigs)/sizeof(vector->psigs[0]))];
        for (j = 0; j < c->psig_indices_len; j++) {
            int expected = c->invalid_sig_idx != (int)j;
            CHECK(expected == secp256k1_musig_partial_sig_parse(ctx, &partial_sig[j], vector->psigs[c->psig_indices[j]]));
        }
    }
}

void run_musig_tests(void) {
    int i;
    secp256k1_scratch_space *scratch = secp256k1_scratch_space_create(ctx, 1024 * 1024);

    for (i = 0; i < count; i++) {
        musig_simple_test(scratch);
    }
    musig_api_tests(scratch);
    musig_nonce_test();
    for (i = 0; i < count; i++) {
        /* Run multiple times to ensure that pk and nonce have different y
         * parities */
        scriptless_atomic_swap(scratch);
        musig_tweak_test(scratch);
    }
    sha256_tag_test();
    musig_test_vectors_keyagg();
    musig_test_vectors_noncegen();
    musig_test_vectors_nonceagg();
    musig_test_vectors_signverify();
    musig_test_vectors_tweak();
    musig_test_vectors_sigagg();

    secp256k1_scratch_space_destroy(ctx, scratch);
}

#endif
