/**********************************************************************
 * Copyright (c) 2022 Sanket Kanjalkar                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/
#ifndef SECP256K1_MODULE_BPPP_PP_TRANSCRIPT_IMPL_H
#define SECP256K1_MODULE_BPPP_PP_TRANSCRIPT_IMPL_H

#include "../../group.h"
#include "../../scalar.h"
#include "bppp_util.h"

/* Initializes SHA256 with fixed midstate. This midstate was computed by applying
 * SHA256 to SHA256("Bulletproofs_pp/v0/commitment")||SHA256("Bulletproofs_pp/v0/commitment").
 */
static void secp256k1_bppp_sha256_tagged_commitment_init(secp256k1_sha256 *sha) {
    secp256k1_sha256_initialize(sha);
    sha->s[0] = 0x52fc8185ul;
    sha->s[1] = 0x0e7debf0ul;
    sha->s[2] = 0xb0967270ul;
    sha->s[3] = 0x6f5abfe1ul;
    sha->s[4] = 0x822bdec0ul;
    sha->s[5] = 0x36db8beful;
    sha->s[6] = 0x03d9e1f1ul;
    sha->s[7] = 0x8a5cef6ful;

    sha->bytes = 64;
}

/* Obtain a challenge scalar from the current transcript.*/
static void secp256k1_bppp_challenge_scalar(secp256k1_scalar* ch, const secp256k1_sha256 *transcript, uint64_t idx) {
    unsigned char buf[32];
    secp256k1_sha256 sha = *transcript;
    secp256k1_bppp_le64(buf, idx);
    secp256k1_sha256_write(&sha, buf, 8);
    secp256k1_sha256_finalize(&sha, buf);
    secp256k1_scalar_set_b32(ch, buf, NULL);
}

#endif
