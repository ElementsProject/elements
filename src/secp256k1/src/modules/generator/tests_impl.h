/**********************************************************************
 * Copyright (c) 2016 Pieter Wuille                                   *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_MODULE_GENERATOR_TESTS_H
#define SECP256K1_MODULE_GENERATOR_TESTS_H

#include <string.h>
#include <stdio.h>

#include "../../group.h"
#include "../../scalar.h"
#include "../../testrand.h"
#include "../../util.h"

#include "../../../include/secp256k1_generator.h"

static void test_generator_api(void) {
    unsigned char key[32];
    unsigned char blind[32];
    unsigned char sergen[33];
    secp256k1_generator gen;

    secp256k1_testrand256(key);
    secp256k1_testrand256(blind);

    CHECK(secp256k1_generator_generate(CTX, &gen, key) == 1);
    CHECK_ILLEGAL(CTX, secp256k1_generator_generate(CTX, NULL, key));
    CHECK_ILLEGAL(CTX, secp256k1_generator_generate(CTX, &gen, NULL));

    CHECK(secp256k1_generator_generate_blinded(CTX, &gen, key, blind) == 1);
    CHECK_ILLEGAL(STATIC_CTX, secp256k1_generator_generate_blinded(STATIC_CTX, &gen, key, blind));
    CHECK_ILLEGAL(CTX, secp256k1_generator_generate_blinded(CTX, NULL, key, blind));
    CHECK_ILLEGAL(CTX, secp256k1_generator_generate_blinded(CTX, &gen, NULL, blind));
    CHECK_ILLEGAL(CTX, secp256k1_generator_generate_blinded(CTX, &gen, key, NULL));

    CHECK(secp256k1_generator_serialize(CTX, sergen, &gen) == 1);
    CHECK_ILLEGAL(CTX, secp256k1_generator_serialize(CTX, NULL, &gen));
    CHECK_ILLEGAL(CTX, secp256k1_generator_serialize(CTX, sergen, NULL));

    CHECK(secp256k1_generator_serialize(CTX, sergen, &gen) == 1);
    CHECK(secp256k1_generator_parse(CTX, &gen, sergen) == 1);
    CHECK_ILLEGAL(CTX, secp256k1_generator_parse(CTX, NULL, sergen));
    CHECK_ILLEGAL(CTX, secp256k1_generator_parse(CTX, &gen, NULL));
}

static void test_shallue_van_de_woestijne(void) {
    /* Matches with the output of the shallue_van_de_woestijne.sage SAGE program */
    static const secp256k1_ge_storage results[34] = {
        SECP256K1_GE_STORAGE_CONST(0x851695d4, 0x9a83f8ef, 0x919bb861, 0x53cbcb16, 0x630fb68a, 0xed0a766a, 0x3ec693d6, 0x8e6afa40, 0x4218f20a, 0xe6c646b3, 0x63db6860, 0x5822fb14, 0x264ca8d2, 0x587fdd6f, 0xbc750d58, 0x7e76a7ee),
        SECP256K1_GE_STORAGE_CONST(0x851695d4, 0x9a83f8ef, 0x919bb861, 0x53cbcb16, 0x630fb68a, 0xed0a766a, 0x3ec693d6, 0x8e6afa40, 0x4218f20a, 0xe6c646b3, 0x63db6860, 0x5822fb14, 0x264ca8d2, 0x587fdd6f, 0xbc750d58, 0x7e76a7ee),
        SECP256K1_GE_STORAGE_CONST(0xedd1fd3e, 0x327ce90c, 0xc7a35426, 0x14289aee, 0x9682003e, 0x9cf7dcc9, 0xcf2ca974, 0x3be5aa0c, 0x0225f529, 0xee75acaf, 0xccfc4560, 0x26c5e46b, 0xf80237a3, 0x3924655a, 0x16f90e88, 0x085ed52a),
        SECP256K1_GE_STORAGE_CONST(0xedd1fd3e, 0x327ce90c, 0xc7a35426, 0x14289aee, 0x9682003e, 0x9cf7dcc9, 0xcf2ca974, 0x3be5aa0c, 0xfdda0ad6, 0x118a5350, 0x3303ba9f, 0xd93a1b94, 0x07fdc85c, 0xc6db9aa5, 0xe906f176, 0xf7a12705),
        SECP256K1_GE_STORAGE_CONST(0x2c5cdc9c, 0x338152fa, 0x85de92cb, 0x1bee9907, 0x765a922e, 0x4f037cce, 0x14ecdbf2, 0x2f78fe15, 0x56716069, 0x6818286b, 0x72f01a3e, 0x5e8caca7, 0x36249160, 0xc7ded69d, 0xd51913c3, 0x03a2fa97),
        SECP256K1_GE_STORAGE_CONST(0x2c5cdc9c, 0x338152fa, 0x85de92cb, 0x1bee9907, 0x765a922e, 0x4f037cce, 0x14ecdbf2, 0x2f78fe15, 0xa98e9f96, 0x97e7d794, 0x8d0fe5c1, 0xa1735358, 0xc9db6e9f, 0x38212962, 0x2ae6ec3b, 0xfc5d0198),
        SECP256K1_GE_STORAGE_CONST(0x531f7239, 0xaebc780e, 0x179fbf8d, 0x412a1b01, 0x511f0abc, 0xe0c46151, 0x8b38db84, 0xcc2467f3, 0x82387d45, 0xec7bd5cc, 0x61fcb9df, 0x41cddd7b, 0x217d8114, 0x3577dc8f, 0x23de356a, 0x7e97704e),
        SECP256K1_GE_STORAGE_CONST(0x531f7239, 0xaebc780e, 0x179fbf8d, 0x412a1b01, 0x511f0abc, 0xe0c46151, 0x8b38db84, 0xcc2467f3, 0x7dc782ba, 0x13842a33, 0x9e034620, 0xbe322284, 0xde827eeb, 0xca882370, 0xdc21ca94, 0x81688be1),
        SECP256K1_GE_STORAGE_CONST(0x2c5cdc9c, 0x338152fa, 0x85de92cb, 0x1bee9907, 0x765a922e, 0x4f037cce, 0x14ecdbf2, 0x2f78fe15, 0x56716069, 0x6818286b, 0x72f01a3e, 0x5e8caca7, 0x36249160, 0xc7ded69d, 0xd51913c3, 0x03a2fa97),
        SECP256K1_GE_STORAGE_CONST(0x2c5cdc9c, 0x338152fa, 0x85de92cb, 0x1bee9907, 0x765a922e, 0x4f037cce, 0x14ecdbf2, 0x2f78fe15, 0xa98e9f96, 0x97e7d794, 0x8d0fe5c1, 0xa1735358, 0xc9db6e9f, 0x38212962, 0x2ae6ec3b, 0xfc5d0198),
        SECP256K1_GE_STORAGE_CONST(0x5e5936b1, 0x81db0b65, 0x8e33a8c6, 0x1aa687dd, 0x31d11e15, 0x85e35664, 0x6b4c2071, 0xcde7e942, 0x88bb5332, 0xa8e05654, 0x78d4f60c, 0x0cd979ec, 0x938558f2, 0xcac11216, 0x7c387a56, 0xe3a6d5f3),
        SECP256K1_GE_STORAGE_CONST(0x5e5936b1, 0x81db0b65, 0x8e33a8c6, 0x1aa687dd, 0x31d11e15, 0x85e35664, 0x6b4c2071, 0xcde7e942, 0x7744accd, 0x571fa9ab, 0x872b09f3, 0xf3268613, 0x6c7aa70d, 0x353eede9, 0x83c785a8, 0x1c59263c),
        SECP256K1_GE_STORAGE_CONST(0x657d438f, 0xfac34a50, 0x463fd07c, 0x3f09f320, 0x4c98e8ed, 0x6927e330, 0xc0c7735f, 0x76d32f6d, 0x577c2b11, 0xcaca2f6f, 0xd60bcaf0, 0x3e7cebe9, 0x5da6e1f4, 0xbb557f12, 0x2a397331, 0x81df897f),
        SECP256K1_GE_STORAGE_CONST(0x657d438f, 0xfac34a50, 0x463fd07c, 0x3f09f320, 0x4c98e8ed, 0x6927e330, 0xc0c7735f, 0x76d32f6d, 0xa883d4ee, 0x3535d090, 0x29f4350f, 0xc1831416, 0xa2591e0b, 0x44aa80ed, 0xd5c68ccd, 0x7e2072b0),
        SECP256K1_GE_STORAGE_CONST(0xbe0bc11b, 0x2bc639cb, 0xc28f72a8, 0xd07c21cc, 0xbc06cfa7, 0x4c2ff25e, 0x630c9740, 0x23128eab, 0x6f062fc8, 0x75148197, 0xd10375c3, 0xcc3fadb6, 0x20277e9c, 0x00579c55, 0xeddd7f95, 0xe95604db),
        SECP256K1_GE_STORAGE_CONST(0xbe0bc11b, 0x2bc639cb, 0xc28f72a8, 0xd07c21cc, 0xbc06cfa7, 0x4c2ff25e, 0x630c9740, 0x23128eab, 0x90f9d037, 0x8aeb7e68, 0x2efc8a3c, 0x33c05249, 0xdfd88163, 0xffa863aa, 0x12228069, 0x16a9f754),
        SECP256K1_GE_STORAGE_CONST(0xedd1fd3e, 0x327ce90c, 0xc7a35426, 0x14289aee, 0x9682003e, 0x9cf7dcc9, 0xcf2ca974, 0x3be5aa0c, 0xfdda0ad6, 0x118a5350, 0x3303ba9f, 0xd93a1b94, 0x07fdc85c, 0xc6db9aa5, 0xe906f176, 0xf7a12705),
        SECP256K1_GE_STORAGE_CONST(0xedd1fd3e, 0x327ce90c, 0xc7a35426, 0x14289aee, 0x9682003e, 0x9cf7dcc9, 0xcf2ca974, 0x3be5aa0c, 0x0225f529, 0xee75acaf, 0xccfc4560, 0x26c5e46b, 0xf80237a3, 0x3924655a, 0x16f90e88, 0x085ed52a),
        SECP256K1_GE_STORAGE_CONST(0xaee172d4, 0xce7c5010, 0xdb20a88f, 0x469598c1, 0xd7f7926f, 0xabb85cb5, 0x339f1403, 0x87e6b494, 0x38065980, 0x4de81b35, 0x098c7190, 0xe3380f9d, 0x95b2ed6c, 0x6c869e85, 0xc772bc5a, 0x7bc3d9d5),
        SECP256K1_GE_STORAGE_CONST(0xaee172d4, 0xce7c5010, 0xdb20a88f, 0x469598c1, 0xd7f7926f, 0xabb85cb5, 0x339f1403, 0x87e6b494, 0xc7f9a67f, 0xb217e4ca, 0xf6738e6f, 0x1cc7f062, 0x6a4d1293, 0x9379617a, 0x388d43a4, 0x843c225a),
        SECP256K1_GE_STORAGE_CONST(0xc28f5c28, 0xf5c28f5c, 0x28f5c28f, 0x5c28f5c2, 0x8f5c28f5, 0xc28f5c28, 0xf5c28f5b, 0x6666635a, 0x0c4da840, 0x1b2cf5be, 0x4604e6ec, 0xf92b2780, 0x063a5351, 0xe294bf65, 0xbb2f8b61, 0x00902db7),
        SECP256K1_GE_STORAGE_CONST(0xc28f5c28, 0xf5c28f5c, 0x28f5c28f, 0x5c28f5c2, 0x8f5c28f5, 0xc28f5c28, 0xf5c28f5b, 0x6666635a, 0xf3b257bf, 0xe4d30a41, 0xb9fb1913, 0x06d4d87f, 0xf9c5acae, 0x1d6b409a, 0x44d0749d, 0xff6fce78),
        SECP256K1_GE_STORAGE_CONST(0xecf56be6, 0x9c8fde26, 0x152832c6, 0xe043b3d5, 0xaf9a723f, 0x789854a0, 0xcb1b810d, 0xe2614ece, 0x66127ae4, 0xe4c17a75, 0x60a727e6, 0xffd2ea7f, 0xaed99088, 0xbec465c6, 0xbde56791, 0x37ed5572),
        SECP256K1_GE_STORAGE_CONST(0xecf56be6, 0x9c8fde26, 0x152832c6, 0xe043b3d5, 0xaf9a723f, 0x789854a0, 0xcb1b810d, 0xe2614ece, 0x99ed851b, 0x1b3e858a, 0x9f58d819, 0x002d1580, 0x51266f77, 0x413b9a39, 0x421a986d, 0xc812a6bd),
        SECP256K1_GE_STORAGE_CONST(0xba72860f, 0x10fcd142, 0x23f71e3c, 0x228deb9a, 0xc46c5ff5, 0x90b884e5, 0xcc60d51e, 0x0629d16e, 0x67999f31, 0x5a74ada3, 0x526832cf, 0x76b9fec3, 0xa348cc97, 0x33c3aa67, 0x02bd2516, 0x7814f635),
        SECP256K1_GE_STORAGE_CONST(0xba72860f, 0x10fcd142, 0x23f71e3c, 0x228deb9a, 0xc46c5ff5, 0x90b884e5, 0xcc60d51e, 0x0629d16e, 0x986660ce, 0xa58b525c, 0xad97cd30, 0x8946013c, 0x5cb73368, 0xcc3c5598, 0xfd42dae8, 0x87eb05fa),
        SECP256K1_GE_STORAGE_CONST(0x92ef5657, 0xdba51cc7, 0xf3e1b442, 0xa6a0916b, 0x8ce03079, 0x2ef5657d, 0xba51cc7e, 0xab2beb65, 0x782c65d2, 0x3f1e0eb2, 0x9179a994, 0xe5e8ff80, 0x5a0d50d9, 0xdeeaed90, 0xcec96ca5, 0x973e2ad3),
        SECP256K1_GE_STORAGE_CONST(0x92ef5657, 0xdba51cc7, 0xf3e1b442, 0xa6a0916b, 0x8ce03079, 0x2ef5657d, 0xba51cc7e, 0xab2beb65, 0x87d39a2d, 0xc0e1f14d, 0x6e86566b, 0x1a17007f, 0xa5f2af26, 0x2115126f, 0x31369359, 0x68c1d15c),
        SECP256K1_GE_STORAGE_CONST(0x9468ad22, 0xf921fc78, 0x8de3f1b0, 0x586c58eb, 0x5e6f0270, 0xe950b602, 0x7ada90d9, 0xd71ae323, 0x922a0c6a, 0x9ccc31d9, 0xc3bf87fd, 0x88381739, 0x35fe393f, 0xa64dfdec, 0x29f2846d, 0x12918d86),
        SECP256K1_GE_STORAGE_CONST(0x9468ad22, 0xf921fc78, 0x8de3f1b0, 0x586c58eb, 0x5e6f0270, 0xe950b602, 0x7ada90d9, 0xd71ae323, 0x6dd5f395, 0x6333ce26, 0x3c407802, 0x77c7e8c6, 0xca01c6c0, 0x59b20213, 0xd60d7b91, 0xed6e6ea9),
        SECP256K1_GE_STORAGE_CONST(0x76ddc7f5, 0xe029e59e, 0x22b0e54f, 0xa811db94, 0x5a209c4f, 0x5e912ca2, 0x8b4da6a7, 0x4c1e00a2, 0x1e8f516c, 0x91c20437, 0x50f6e24e, 0x8c2cf202, 0xacf68291, 0xbf8b66eb, 0xf7335b62, 0xec2c88fe),
        SECP256K1_GE_STORAGE_CONST(0x76ddc7f5, 0xe029e59e, 0x22b0e54f, 0xa811db94, 0x5a209c4f, 0x5e912ca2, 0x8b4da6a7, 0x4c1e00a2, 0xe170ae93, 0x6e3dfbc8, 0xaf091db1, 0x73d30dfd, 0x53097d6e, 0x40749914, 0x08cca49c, 0x13d37331),
        SECP256K1_GE_STORAGE_CONST(0xf75763bc, 0x2907e79b, 0x125e33c3, 0x9a027f48, 0x0f8c6409, 0x2153432f, 0x967bc2b1, 0x1d1f5cf0, 0xb4a8edc6, 0x36391b39, 0x9bc219c0, 0x3d033128, 0xdbcd463e, 0xd2506394, 0x061b87a5, 0x9e510235),
        SECP256K1_GE_STORAGE_CONST(0xf75763bc, 0x2907e79b, 0x125e33c3, 0x9a027f48, 0x0f8c6409, 0x2153432f, 0x967bc2b1, 0x1d1f5cf0, 0x4b571239, 0xc9c6e4c6, 0x643de63f, 0xc2fcced7, 0x2432b9c1, 0x2daf9c6b, 0xf9e47859, 0x61aef9fa),
    };

    secp256k1_ge ge;
    secp256k1_fe fe;
    secp256k1_ge_storage ges;
    int i, s;
    for (i = 0; i <= 16; i++) {
        secp256k1_fe_set_int(&fe, i);

        for (s = 0; s < 2; s++) {
            if (s) {
                secp256k1_fe_negate(&fe, &fe, 1);
                secp256k1_fe_normalize(&fe);
            }
            shallue_van_de_woestijne(&ge, &fe);
            CHECK(secp256k1_ge_is_valid_var(&ge));
            secp256k1_ge_to_storage(&ges, &ge);
            CHECK(secp256k1_memcmp_var(&ges, &results[i * 2 + s], sizeof(secp256k1_ge_storage)) == 0);
        }
    }
}

static void test_generator_generate(void) {
    static const secp256k1_ge_storage results[32] = {
        SECP256K1_GE_STORAGE_CONST(0x806cd8ed, 0xd6c153e3, 0x4aa9b9a0, 0x8755c4be, 0x4718b1ef, 0xb26cb93f, 0xfdd99e1b, 0x21f2af8e, 0xc7062208, 0xcc649a03, 0x1bdc1a33, 0x9d01f115, 0x4bcd0dca, 0xfe0b875d, 0x62f35f73, 0x28673006),
        SECP256K1_GE_STORAGE_CONST(0xd91b15ec, 0x47a811f4, 0xaa189561, 0xd13f5c4d, 0x4e81f10d, 0xc7dc551f, 0x4fea9b84, 0x610314c4, 0x9b0ada1e, 0xb38efd67, 0x8bff0b6c, 0x7d7315f7, 0xb49b8cc5, 0xa679fad4, 0xc94f9dc6, 0x9da66382),
        SECP256K1_GE_STORAGE_CONST(0x11c00de6, 0xf885035e, 0x76051430, 0xa3c38b2a, 0x5f86ab8c, 0xf66dae58, 0x04ea7307, 0x348b19bf, 0xe0858ae7, 0x61dcb1ba, 0xff247e37, 0xd38fcd88, 0xf3bd7911, 0xaa4ed6e0, 0x28d792dd, 0x3ee1ac09),
        SECP256K1_GE_STORAGE_CONST(0x986b99eb, 0x3130e7f0, 0xe779f674, 0xb85cb514, 0x46a676bf, 0xb1dfb603, 0x4c4bb639, 0x7c406210, 0xdf900609, 0x8b3ef1e0, 0x30e32fb0, 0xd97a4329, 0xff98aed0, 0xcd278c3f, 0xe6078467, 0xfbd12f35),
        SECP256K1_GE_STORAGE_CONST(0xae528146, 0x03fdf91e, 0xc592977e, 0x12461dc7, 0xb9e038f8, 0x048dcb62, 0xea264756, 0xd459ae42, 0x80ef658d, 0x92becb84, 0xdba8e4f9, 0x560d7a72, 0xbaf4c393, 0xfbcf6007, 0x11039f1c, 0x224faaad),
        SECP256K1_GE_STORAGE_CONST(0x00df3d91, 0x35975eee, 0x91fab903, 0xe3128e4a, 0xca071dde, 0x270814e5, 0xcbda69ec, 0xcad58f46, 0x11b590aa, 0x92d89969, 0x2dbd932f, 0x08013b8b, 0x45afabc6, 0x43677db2, 0x143e0c0f, 0x5865fb03),
        SECP256K1_GE_STORAGE_CONST(0x1168155b, 0x987e9bc8, 0x84c5f3f4, 0x92ebf784, 0xcc8c6735, 0x39d8e5e8, 0xa967115a, 0x2949da9b, 0x0858a470, 0xf403ca97, 0xb1827f6f, 0x544c2c67, 0x08f6cb83, 0xc510c317, 0x96c981ed, 0xb9f61780),
        SECP256K1_GE_STORAGE_CONST(0xe8d7c0cf, 0x2bb4194c, 0x97bf2a36, 0xbd115ba0, 0x81a9afe8, 0x7663fa3c, 0x9c3cd253, 0x79fe2571, 0x2028ad04, 0xefa00119, 0x5a25d598, 0x67e79502, 0x49de7c61, 0x4751cd9d, 0x4fb317f6, 0xf76f1110),
        SECP256K1_GE_STORAGE_CONST(0x9532c491, 0xa64851dd, 0xcd0d3e5a, 0x93e17267, 0xa10aca95, 0xa23781aa, 0x5087f340, 0xc45fecc3, 0xb691ddc2, 0x3143a7b6, 0x09969302, 0x258affb8, 0x5bbf8666, 0xe1192319, 0xeb174d88, 0x308bd57a),
        SECP256K1_GE_STORAGE_CONST(0x6b20b6e2, 0x1ba6cc44, 0x3f2c3a0c, 0x5283ba44, 0xbee43a0a, 0x2799a6cf, 0xbecc0f8a, 0xf8c583ac, 0xf7021e76, 0xd51291a6, 0xf9396215, 0x686f25aa, 0xbec36282, 0x5e11eeea, 0x6e51a6e6, 0xd7d7c006),
        SECP256K1_GE_STORAGE_CONST(0xde27e6ff, 0x219b3ab1, 0x2b0a9e4e, 0x51fc6092, 0x96e55af6, 0xc6f717d6, 0x12cd6cce, 0x65d6c8f2, 0x48166884, 0x4dc13fd2, 0xed7a7d81, 0x66a0839a, 0x8a960863, 0xfe0001c1, 0x35d206fd, 0x63b87c09),
        SECP256K1_GE_STORAGE_CONST(0x79a96fb8, 0xd88a08d3, 0x055d38d1, 0x3346b0d4, 0x47d838ca, 0xfcc8fa40, 0x6d3a7157, 0xef84e7e3, 0x6bab9c45, 0x2871b51d, 0xb0df2369, 0xe7860e01, 0x2e37ffea, 0x6689fd1a, 0x9c6fe9cf, 0xb940acea),
        SECP256K1_GE_STORAGE_CONST(0x06c4d4cb, 0xd32c0ddb, 0x67e988c6, 0x2bdbe6ad, 0xa39b80cc, 0x61afb347, 0x234abe27, 0xa689618c, 0x5b355949, 0xf904fe08, 0x569b2313, 0xe8f19f8d, 0xc5b79e27, 0x70da0832, 0x5fb7a229, 0x238ca6b6),
        SECP256K1_GE_STORAGE_CONST(0x7027e566, 0x3e727c28, 0x42aa14e5, 0x52c2d2ec, 0x1d8beaa9, 0x8a22ceab, 0x15ccafc3, 0xb4f06249, 0x9b3dffbc, 0xdbd5e045, 0x6931fd03, 0x8b1c6a9b, 0x4c168c6d, 0xa6553897, 0xfe11ce49, 0xac728139),
        SECP256K1_GE_STORAGE_CONST(0xee3520c3, 0x9f2b954d, 0xf8e15547, 0xdaeb6cc8, 0x04c8f3b0, 0x9301f53e, 0xe0c11ea1, 0xeace539d, 0x244ff873, 0x7e060c98, 0xe843c353, 0xcd35d2e4, 0x3cd8b082, 0xcffbc9ae, 0x81eafa70, 0x332f9748),
        SECP256K1_GE_STORAGE_CONST(0xdaecd756, 0xf5b706a4, 0xc14e1095, 0x3e2f70df, 0xa81276e7, 0x71806b89, 0x4d8a5502, 0xa0ef4998, 0xbac906c0, 0x948b1d48, 0xe023f439, 0xfd3770b8, 0x837f60cc, 0x40552a51, 0x433d0b79, 0x6610da27),
        SECP256K1_GE_STORAGE_CONST(0x55e1ca28, 0x750fe2d0, 0x57f7449b, 0x3f49d999, 0x3b9616dd, 0x5387bc2e, 0x6e6698f8, 0xc4ea49f4, 0xe339e0e9, 0xa4c7fa99, 0xd063e062, 0x6582bce2, 0x33c6b1ee, 0x17a5b47f, 0x6d43ecf8, 0x98b40120),
        SECP256K1_GE_STORAGE_CONST(0xdd82cac2, 0x9e0e0135, 0x4964d3bc, 0x27469233, 0xf13bbd5e, 0xd7aff24b, 0x4902fca8, 0x17294b12, 0x561ab1d6, 0xcd9bcb6e, 0x805585cf, 0x3df8714c, 0x1bfa6304, 0x5efbf122, 0x1a3d8fd9, 0x3827764a),
        SECP256K1_GE_STORAGE_CONST(0xda5cbfb7, 0x3522e9c7, 0xcb594436, 0x83677038, 0x0eaa64a9, 0x2eca3888, 0x0fe4c9d6, 0xdeb22dbf, 0x4f46de68, 0x0447c780, 0xc54a314b, 0x5389a926, 0xbba8910b, 0x869fc6cd, 0x42ee82e8, 0x5895e42a),
        SECP256K1_GE_STORAGE_CONST(0x4e09830e, 0xc8894c58, 0x4e6278de, 0x167a96b0, 0x20d60463, 0xee48f788, 0x4974d66e, 0x871e35e9, 0x21259c4d, 0x332ca932, 0x2e187df9, 0xe7afbc23, 0x9d171ebc, 0x7d9e2560, 0x503f50b1, 0x9fe45834),
        SECP256K1_GE_STORAGE_CONST(0xabfff6ca, 0x41dcfd17, 0x03cae629, 0x9d127971, 0xf19ee000, 0x2db332e6, 0x5cc209a3, 0xc21b8f54, 0x65991d60, 0xee54f5cc, 0xddf7a732, 0xa76b0303, 0xb9f519a6, 0x22ea0390, 0x8af23ffa, 0x35ae6632),
        SECP256K1_GE_STORAGE_CONST(0xc6c9b92c, 0x91e045a5, 0xa1913277, 0x44d6fce2, 0x11b12c7c, 0x9b3112d6, 0xc61e14a6, 0xd6b1ae12, 0x04ab0396, 0xebdc4c6a, 0xc213cc3e, 0x077a2e80, 0xb4ba7b2b, 0x33907d56, 0x2c98ccf7, 0xb82a2e9f),
        SECP256K1_GE_STORAGE_CONST(0x66f6e6d9, 0xc4bb9a5f, 0x99085781, 0x83cb9362, 0x2ea437d8, 0xccd31969, 0xffadca3a, 0xff1d3935, 0x50a5b06e, 0x39e039d7, 0x1dfb2723, 0x18db74e5, 0x5af64da1, 0xdfc34586, 0x6aac3bd0, 0x5792a890),
        SECP256K1_GE_STORAGE_CONST(0x58ded03c, 0x98e1a890, 0x63fc7793, 0xe3ecd896, 0x235e75c9, 0x82e7008f, 0xddbf3ca8, 0x5b7e9ecb, 0x34594776, 0x58ab6821, 0xaf43a453, 0xa946fda9, 0x13d24999, 0xccf22df8, 0xd291ef59, 0xb08975c0),
        SECP256K1_GE_STORAGE_CONST(0x74557864, 0x4f2b0486, 0xd5beea7c, 0x2d258ccb, 0x78a870e1, 0x848982d8, 0xed3f91a4, 0x9db83a36, 0xd84e940e, 0x1d33c28a, 0x62398ec8, 0xc493aee7, 0x7c2ba722, 0x42dee7ae, 0x3c35c256, 0xad00cf42),
        SECP256K1_GE_STORAGE_CONST(0x7fc7963a, 0x16abc8fb, 0x5d61eb61, 0x0fc50a68, 0x754470d2, 0xf43df3be, 0x52228f66, 0x522fe61b, 0x499f9e7f, 0x462c6545, 0x29687af4, 0x9f7c732d, 0x48801ce5, 0x21acd546, 0xc6fb903c, 0x7c265032),
        SECP256K1_GE_STORAGE_CONST(0xb2f6257c, 0xc58df82f, 0xb9ba4f36, 0x7ededf03, 0xf8ea10f3, 0x104d7ae6, 0x233b7ac4, 0x725e11de, 0x9c7a32df, 0x4842f33d, 0xaad84f0b, 0x62e88b40, 0x46ddcbde, 0xbbeec6f8, 0x93bfde27, 0x0561dc73),
        SECP256K1_GE_STORAGE_CONST(0xe2cdfd27, 0x8a8e22be, 0xabf08b79, 0x1bc6ae38, 0x41d22a9a, 0x9472e266, 0x1a7c6e83, 0xa2f74725, 0x0e26c103, 0xe0dd93b2, 0x3724f3b7, 0x8bb7366e, 0x2c245768, 0xd64f3283, 0xd8316e8a, 0x1383b977),
        SECP256K1_GE_STORAGE_CONST(0x757c13e7, 0xe866017e, 0xe6af61d7, 0x161d208a, 0xc438f712, 0x242fcd23, 0x63a10e59, 0xd67e41fb, 0xb550c6a9, 0x4ddb15f3, 0xfeea4bfe, 0xd2faa19f, 0x2aa2fbd3, 0x0c6ae785, 0xe357f365, 0xb30d12e0),
        SECP256K1_GE_STORAGE_CONST(0x528d525e, 0xac30095b, 0x5e5f83ca, 0x4d3dea63, 0xeb608f2d, 0x18dd25a7, 0x2529c8e5, 0x1ae5f9f1, 0xfde2860b, 0x492a4106, 0x9f356c05, 0x3ebc045e, 0x4ad08b79, 0x3e264935, 0xf25785a9, 0x8690b5ee),
        SECP256K1_GE_STORAGE_CONST(0x150df593, 0x5b6956a0, 0x0cfed843, 0xb9d6ffce, 0x4f790022, 0xea18730f, 0xc495111d, 0x91568e55, 0x6700a2ca, 0x9ff4ed32, 0xc1697312, 0x4eb51ce3, 0x5656344b, 0x65a1e3d5, 0xd6c1f7ce, 0x29233f82),
        SECP256K1_GE_STORAGE_CONST(0x38e02eaf, 0x2c8774fd, 0x58b8b373, 0x732457f1, 0x16dbe53b, 0xea5683d9, 0xada20dd7, 0x14ce20a6, 0x6ac5362e, 0xbb425416, 0x8250f43f, 0xa4ee2b63, 0x0406324f, 0x1c876d60, 0xebe5be2c, 0x6eb1515b),
    };
    secp256k1_generator gen;
    secp256k1_ge ge;
    secp256k1_ge_storage ges;
    int i;
    unsigned char v[32];
    unsigned char s[32] = {0};
    secp256k1_scalar sc;
    secp256k1_scalar_set_b32(&sc, s, NULL);
    for (i = 1; i <= 32; i++) {
        memset(v, 0, 31);
        v[31] = i;
        CHECK(secp256k1_generator_generate_blinded(CTX, &gen, v, s));
        secp256k1_generator_load(&ge, &gen);
        secp256k1_ge_to_storage(&ges, &ge);
        CHECK(secp256k1_memcmp_var(&ges, &results[i - 1], sizeof(secp256k1_ge_storage)) == 0);
        CHECK(secp256k1_generator_generate(CTX, &gen, v));
        secp256k1_generator_load(&ge, &gen);
        secp256k1_ge_to_storage(&ges, &ge);
        CHECK(secp256k1_memcmp_var(&ges, &results[i - 1], sizeof(secp256k1_ge_storage)) == 0);
    }

    /* There is no range restriction on the value, but the blinder must be a
     * valid scalar. Check that an invalid blinder causes the call to fail
     * but not crash. */
    memset(v, 0xff, 32);
    CHECK(secp256k1_generator_generate(CTX, &gen, v));
    memset(s, 0xff, 32);
    CHECK(!secp256k1_generator_generate_blinded(CTX, &gen, v, s));
}

static void test_generator_fixed_vector(void) {
    const unsigned char two_g[33] = {
        0x0b,
        0xc6, 0x04, 0x7f, 0x94, 0x41, 0xed, 0x7d, 0x6d, 0x30, 0x45, 0x40, 0x6e, 0x95, 0xc0, 0x7c, 0xd8,
        0x5c, 0x77, 0x8e, 0x4b, 0x8c, 0xef, 0x3c, 0xa7, 0xab, 0xac, 0x09, 0xb9, 0x5c, 0x70, 0x9e, 0xe5
    };
    unsigned char result[33];
    secp256k1_generator parse;

    CHECK(secp256k1_generator_parse(CTX, &parse, two_g));
    CHECK(secp256k1_generator_serialize(CTX, result, &parse));
    CHECK(secp256k1_memcmp_var(two_g, result, 33) == 0);

    result[0] = 0x0a;
    CHECK(secp256k1_generator_parse(CTX, &parse, result));
    result[0] = 0x08;
    CHECK(!secp256k1_generator_parse(CTX, &parse, result));
}

static void test_pedersen_api(void) {
    secp256k1_pedersen_commitment commit;
    const secp256k1_pedersen_commitment *commit_ptr = &commit;
    unsigned char blind[32];
    unsigned char blind_out[32];
    const unsigned char *blind_ptr = blind;
    unsigned char *blind_out_ptr = blind_out;
    uint64_t val = secp256k1_testrand32();

    secp256k1_testrand256(blind);
    CHECK(secp256k1_pedersen_commit(CTX, &commit, blind, val, secp256k1_generator_h) != 0);
    CHECK_ILLEGAL(STATIC_CTX, secp256k1_pedersen_commit(STATIC_CTX, &commit, blind, val, secp256k1_generator_h));

    CHECK_ILLEGAL(CTX, secp256k1_pedersen_commit(CTX, NULL, blind, val, secp256k1_generator_h));
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_commit(CTX, &commit, NULL, val, secp256k1_generator_h));
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_commit(CTX, &commit, blind, val, NULL));

    CHECK(secp256k1_pedersen_blind_sum(CTX, blind_out, &blind_ptr, 1, 1) != 0);
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_blind_sum(CTX, NULL, &blind_ptr, 1, 1));
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_blind_sum(CTX, blind_out, NULL, 1, 1));
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_blind_sum(CTX, blind_out, &blind_ptr, 0, 1));
    CHECK(secp256k1_pedersen_blind_sum(CTX, blind_out, &blind_ptr, 0, 0) != 0);

    CHECK(secp256k1_pedersen_commit(CTX, &commit, blind, val, secp256k1_generator_h) != 0);
    CHECK(secp256k1_pedersen_verify_tally(CTX, &commit_ptr, 1, &commit_ptr, 1) != 0);
    CHECK(secp256k1_pedersen_verify_tally(CTX, NULL, 0, &commit_ptr, 1) == 0);
    CHECK(secp256k1_pedersen_verify_tally(CTX, &commit_ptr, 1, NULL, 0) == 0);
    CHECK(secp256k1_pedersen_verify_tally(CTX, NULL, 0, NULL, 0) != 0);
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_verify_tally(CTX, NULL, 1, &commit_ptr, 1));
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_verify_tally(CTX, &commit_ptr, 1, NULL, 1));

    CHECK(secp256k1_pedersen_blind_generator_blind_sum(CTX, &val, &blind_ptr, &blind_out_ptr, 1, 0) != 0);
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_blind_generator_blind_sum(CTX, &val, &blind_ptr, &blind_out_ptr, 1, 1));
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_blind_generator_blind_sum(CTX, &val, &blind_ptr, &blind_out_ptr, 0, 0));
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_blind_generator_blind_sum(CTX, NULL, &blind_ptr, &blind_out_ptr, 1, 0));
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_blind_generator_blind_sum(CTX, &val, NULL, &blind_out_ptr, 1, 0));
    CHECK_ILLEGAL(CTX, secp256k1_pedersen_blind_generator_blind_sum(CTX, &val, &blind_ptr, NULL, 1, 0));
}

static void test_pedersen(void) {
    secp256k1_pedersen_commitment commits[19];
    const secp256k1_pedersen_commitment *cptr[19];
    unsigned char blinds[32*19];
    const unsigned char *bptr[19];
    secp256k1_scalar s;
    uint64_t values[19];
    int64_t totalv;
    int i;
    int inputs;
    int outputs;
    int total;
    inputs = (secp256k1_testrand32() & 7) + 1;
    outputs = (secp256k1_testrand32() & 7) + 2;
    total = inputs + outputs;
    for (i = 0; i < 19; i++) {
        cptr[i] = &commits[i];
        bptr[i] = &blinds[i * 32];
    }
    totalv = 0;
    for (i = 0; i < inputs; i++) {
        values[i] = secp256k1_testrandi64(0, INT64_MAX - totalv);
        totalv += values[i];
    }
    for (i = 0; i < outputs - 1; i++) {
        values[i + inputs] = secp256k1_testrandi64(0, totalv);
        totalv -= values[i + inputs];
    }
    values[total - 1] = totalv;

    for (i = 0; i < total - 1; i++) {
        random_scalar_order(&s);
        secp256k1_scalar_get_b32(&blinds[i * 32], &s);
    }
    CHECK(secp256k1_pedersen_blind_sum(CTX, &blinds[(total - 1) * 32], bptr, total - 1, inputs));
    for (i = 0; i < total; i++) {
        unsigned char result[33];
        secp256k1_pedersen_commitment parse;

        CHECK(secp256k1_pedersen_commit(CTX, &commits[i], &blinds[i * 32], values[i], secp256k1_generator_h));
        CHECK(secp256k1_pedersen_commitment_serialize(CTX, result, &commits[i]));
        CHECK(secp256k1_pedersen_commitment_parse(CTX, &parse, result));
        CHECK(secp256k1_memcmp_var(&commits[i], &parse, 33) == 0);
    }
    CHECK(secp256k1_pedersen_verify_tally(CTX, cptr, inputs, &cptr[inputs], outputs));
    CHECK(secp256k1_pedersen_verify_tally(CTX, &cptr[inputs], outputs, cptr, inputs));
    if (inputs > 0 && values[0] > 0) {
        CHECK(!secp256k1_pedersen_verify_tally(CTX, cptr, inputs - 1, &cptr[inputs], outputs));
    }
    random_scalar_order(&s);
    for (i = 0; i < 4; i++) {
        secp256k1_scalar_get_b32(&blinds[i * 32], &s);
    }
    values[0] = INT64_MAX;
    values[1] = 0;
    values[2] = 1;
    for (i = 0; i < 3; i++) {
        CHECK(secp256k1_pedersen_commit(CTX, &commits[i], &blinds[i * 32], values[i], secp256k1_generator_h));
    }
    CHECK(secp256k1_pedersen_verify_tally(CTX, &cptr[0], 1, &cptr[0], 1));
    CHECK(secp256k1_pedersen_verify_tally(CTX, &cptr[1], 1, &cptr[1], 1));
}

static void test_pedersen_commitment_fixed_vector(void) {
    const unsigned char two_g[33] = {
        0x09,
        0xc6, 0x04, 0x7f, 0x94, 0x41, 0xed, 0x7d, 0x6d, 0x30, 0x45, 0x40, 0x6e, 0x95, 0xc0, 0x7c, 0xd8,
        0x5c, 0x77, 0x8e, 0x4b, 0x8c, 0xef, 0x3c, 0xa7, 0xab, 0xac, 0x09, 0xb9, 0x5c, 0x70, 0x9e, 0xe5
    };
    unsigned char result[33];
    secp256k1_pedersen_commitment parse;

    CHECK(secp256k1_pedersen_commitment_parse(CTX, &parse, two_g));
    CHECK(secp256k1_pedersen_commitment_serialize(CTX, result, &parse));
    CHECK(secp256k1_memcmp_var(two_g, result, 33) == 0);

    result[0] = 0x08;
    CHECK(secp256k1_pedersen_commitment_parse(CTX, &parse, result));
    result[0] = 0x0c;
    CHECK(!secp256k1_pedersen_commitment_parse(CTX, &parse, result));
}


static void run_generator_tests(void) {
    int i;

    test_shallue_van_de_woestijne();
    test_generator_fixed_vector();
    test_generator_api();
    test_generator_generate();
    test_pedersen_api();
    test_pedersen_commitment_fixed_vector();
    for (i = 0; i < COUNT / 2 + 1; i++) {
        test_pedersen();
    }
}

#endif
