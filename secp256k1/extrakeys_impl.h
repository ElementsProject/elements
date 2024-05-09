/***********************************************************************
 * Copyright (c) 2020 Jonas Nick                                       *
 * Distributed under the MIT software license, see the accompanying    *
 * file COPYING or https://www.opensource.org/licenses/mit-license.php.*
 ***********************************************************************/

#ifndef SECP256K1_EXTRAKEYS_IMPL
#define SECP256K1_EXTRAKEYS_IMPL

#include "secp256k1.h"
#include "extrakeys.h"

static SECP256K1_INLINE int secp256k1_xonly_pubkey_load(secp256k1_ge *ge, const secp256k1_xonly_pubkey *pubkey) {
    return secp256k1_pubkey_load(ge, (const secp256k1_pubkey *) pubkey);
}

static SECP256K1_INLINE void secp256k1_xonly_pubkey_save(secp256k1_xonly_pubkey *pubkey, secp256k1_ge *ge) {
    secp256k1_pubkey_save((secp256k1_pubkey *) pubkey, ge);
}

static int secp256k1_xonly_pubkey_parse(secp256k1_xonly_pubkey *pubkey, const unsigned char *input32) {
    secp256k1_ge pk;
    secp256k1_fe x;

    ARG_CHECK(pubkey != NULL);
    memset(pubkey, 0, sizeof(*pubkey));
    ARG_CHECK(input32 != NULL);

    if (!secp256k1_fe_set_b32(&x, input32)) {
        return 0;
    }
    if (!secp256k1_ge_set_xo_var(&pk, &x, 0)) {
        return 0;
    }
    if (!secp256k1_ge_is_in_correct_subgroup(&pk)) {
        return 0;
    }
    secp256k1_xonly_pubkey_save(pubkey, &pk);
    return 1;
}

#endif
