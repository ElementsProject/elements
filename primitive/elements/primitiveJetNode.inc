/* This file has been automatically generated. */
[ADD_16] =
{ .tag = JET
, .jet = add_16
, .cmr = {{0x55cf8ce6u, 0x6e275d01u, 0xafc1fb35u, 0x10d0b53fu, 0xab54a478u, 0x2a3a48ddu, 0xac494e96u, 0x72fa045du}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw16
, .cost = 133 /* milli weight units */
}
,[ADD_32] =
{ .tag = JET
, .jet = add_32
, .cmr = {{0xfa874e40u, 0x6272c90cu, 0xf0b87b1eu, 0x7b89f661u, 0xf3341b0du, 0x61635cf6u, 0xf5a8a2a5u, 0x3288cfe4u}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw32
, .cost = 133 /* milli weight units */
}
,[ADD_64] =
{ .tag = JET
, .jet = add_64
, .cmr = {{0x1256bc57u, 0x26cdb954u, 0x5821d3d9u, 0x6e7fc732u, 0x86d7db23u, 0xae651710u, 0xff05fcc0u, 0xa9b7c3e9u}}
, .sourceIx = ty_w128
, .targetIx = ty_pbw64
, .cost = 133 /* milli weight units */
}
,[ADD_8] =
{ .tag = JET
, .jet = add_8
, .cmr = {{0xd94b8fb6u, 0xb6025d8du, 0x029df1b0u, 0xa526a42bu, 0x3eae94c8u, 0xa9936ce7u, 0xe2a3b000u, 0x2e7f445du}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw8
, .cost = 133 /* milli weight units */
}
,[ALL_16] =
{ .tag = JET
, .jet = all_16
, .cmr = {{0xc2624c7fu, 0x529d7f8eu, 0x7cb96924u, 0xdf5c48dau, 0x2bf2d927u, 0x96662b0cu, 0x767821e1u, 0x9e7a3600u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[ALL_32] =
{ .tag = JET
, .jet = all_32
, .cmr = {{0x4c060c8bu, 0xd9702441u, 0x11746560u, 0xdd55fbcdu, 0x6104ae34u, 0x35aa4314u, 0xe4ac0e05u, 0x31205e20u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[ALL_64] =
{ .tag = JET
, .jet = all_64
, .cmr = {{0xf52f9febu, 0xc7113bb1u, 0xca14e3d2u, 0xff9c161au, 0x598de5afu, 0xe928c691u, 0x355b9e86u, 0xbe131267u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[ALL_8] =
{ .tag = JET
, .jet = all_8
, .cmr = {{0xe51e0e23u, 0x93315a99u, 0xbfdb3358u, 0x4a4eb6cdu, 0x6a3d03f1u, 0xa760eaa0u, 0x58b14d33u, 0xd2d3f82au}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[AND_16] =
{ .tag = JET
, .jet = and_16
, .cmr = {{0x25172139u, 0x33593c62u, 0x72d8aa0cu, 0x1d996a3au, 0x1c56f80du, 0xd35b0544u, 0x96f9c637u, 0xf69ff921u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[AND_32] =
{ .tag = JET
, .jet = and_32
, .cmr = {{0x4f9d326eu, 0x9e515152u, 0x32f84752u, 0x33f750c0u, 0xa5721255u, 0x806d3d36u, 0xb63ffc14u, 0x99725159u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[AND_64] =
{ .tag = JET
, .jet = and_64
, .cmr = {{0xdf3a07b2u, 0x40eb8c53u, 0x33f7b080u, 0x3d81c875u, 0x69ef5997u, 0xdb56ac37u, 0xad63059fu, 0x0cc0779cu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[AND_8] =
{ .tag = JET
, .jet = and_8
, .cmr = {{0x14769a23u, 0xfcac9546u, 0x229d4c2eu, 0xf3c5d779u, 0xeaf62411u, 0xfa4ca3a0u, 0x6d60c417u, 0xf25b3e30u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[ANNEX_HASH] =
{ .tag = JET
, .jet = annex_hash
, .cmr = {{0x75b1d10eu, 0x8cfe48b1u, 0xf37ce0f0u, 0x3ebde840u, 0x2cae19feu, 0xadc01aecu, 0x28d65d2bu, 0x6445e797u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256mw256
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 465 /* milli weight units */
}
,[ASSET_AMOUNT_HASH] =
{ .tag = JET
, .jet = asset_amount_hash
, .cmr = {{0x2bc01adeu, 0xd5d26123u, 0xd6894a1fu, 0xcb46aa8bu, 0x52a60c0cu, 0x64ec2f34u, 0x4fb60b39u, 0xbf194244u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256pspbw256w256spbw256w64
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 399 /* milli weight units */
}
,[BIP_0340_VERIFY] =
{ .tag = JET
, .jet = bip_0340_verify
, .cmr = {{0xaf924cbeu, 0xc941fd9bu, 0x9e8293efu, 0x903e237bu, 0x01dbcb34u, 0x2b9610beu, 0xf95f59b8u, 0x136ef804u}}
, .sourceIx = ty_w1Ki
, .targetIx = ty_u
, .cost = 50735 /* milli weight units */
}
,[BUILD_TAPBRANCH] =
{ .tag = JET
, .jet = build_tapbranch
, .cmr = {{0x7de0e3c1u, 0x53a860a0u, 0x9201c7e5u, 0x9473f03au, 0xe29aea64u, 0xfb18e879u, 0xa95767d7u, 0xa9b494d0u}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 3167 /* milli weight units */
}
,[BUILD_TAPLEAF_SIMPLICITY] =
{ .tag = JET
, .jet = build_tapleaf_simplicity
, .cmr = {{0x1e610728u, 0x01f53de6u, 0xc009f4f4u, 0x1bdf49f0u, 0xb302edc7u, 0x4cbf9425u, 0x28f2aa19u, 0x5ac04d50u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 2240 /* milli weight units */
}
,[CALCULATE_ASSET] =
{ .tag = JET
, .jet = calculate_asset
, .cmr = {{0xe288fd8cu, 0x56a10616u, 0x1319672bu, 0x385a429eu, 0x4d043f83u, 0xd29d039au, 0x44c3df9cu, 0xc0ab554cu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 794 /* milli weight units */
}
,[CALCULATE_CONFIDENTIAL_TOKEN] =
{ .tag = JET
, .jet = calculate_confidential_token
, .cmr = {{0x82e135bcu, 0x209406fdu, 0x568ee77cu, 0xde6877e9u, 0xcc8e4c2bu, 0x5a698d5du, 0x3fb12108u, 0x11c811cau}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 774 /* milli weight units */
}
,[CALCULATE_EXPLICIT_TOKEN] =
{ .tag = JET
, .jet = calculate_explicit_token
, .cmr = {{0xd72b3977u, 0x21f7ed4cu, 0xab9c0ff0u, 0xd7ced45au, 0xf9549c27u, 0xee2326f6u, 0x1dc87b74u, 0x220e9c46u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 769 /* milli weight units */
}
,[CALCULATE_ISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = calculate_issuance_entropy
, .cmr = {{0xe8064f3fu, 0x65877252u, 0xac161aaau, 0x14d8ea60u, 0x77989cf5u, 0x5549e5b4u, 0x090766a5u, 0xf692f9ddu}}
, .sourceIx = ty_ppw256w32w256
, .targetIx = ty_w256
, .cost = 3564 /* milli weight units */
}
,[CH_16] =
{ .tag = JET
, .jet = ch_16
, .cmr = {{0x723b960cu, 0x6734a988u, 0x32298863u, 0x28485db7u, 0x189d0b3cu, 0xec24c8a0u, 0xb288a459u, 0x7867bb9cu}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[CH_32] =
{ .tag = JET
, .jet = ch_32
, .cmr = {{0xf14782afu, 0x48db5ee8u, 0x424df84du, 0xb55ecd83u, 0x420e4adeu, 0x1e43119au, 0xcb0a065fu, 0x8667507du}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[CH_64] =
{ .tag = JET
, .jet = ch_64
, .cmr = {{0xb1800eacu, 0x70038bdcu, 0x3ee9dd14u, 0x75c11f5au, 0x3b40b3c4u, 0x0ad6c8e6u, 0x67487743u, 0x09c2c2acu}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[CH_8] =
{ .tag = JET
, .jet = ch_8
, .cmr = {{0x5b0b1235u, 0x720bbf0bu, 0x666f35e6u, 0x783a6ab6u, 0xb7848c9du, 0xa47944bcu, 0x914f0560u, 0x38951cf8u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[CHECK_LOCK_DISTANCE] =
{ .tag = JET
, .jet = check_lock_distance
, .cmr = {{0xb92fc87fu, 0x29fe0801u, 0xe8ec7b0bu, 0x5c9be71eu, 0x3a17f929u, 0xbb802e05u, 0x3be0261bu, 0x7c503fadu}}
, .sourceIx = ty_w16
, .targetIx = ty_u
, .cost = 168 /* milli weight units */
}
,[CHECK_LOCK_DURATION] =
{ .tag = JET
, .jet = check_lock_duration
, .cmr = {{0xa371e37du, 0x4412b699u, 0xf0206328u, 0x94490a38u, 0x3e7cd6e4u, 0x70182ee3u, 0x92889d64u, 0x05b3adf0u}}
, .sourceIx = ty_w16
, .targetIx = ty_u
, .cost = 182 /* milli weight units */
}
,[CHECK_LOCK_HEIGHT] =
{ .tag = JET
, .jet = check_lock_height
, .cmr = {{0xcd3db0cbu, 0x9c21f58au, 0x18ea6cc4u, 0x85a78026u, 0x44a1f7d7u, 0xb85ec16fu, 0x855b1abeu, 0xb3c7bf31u}}
, .sourceIx = ty_w32
, .targetIx = ty_u
, .cost = 117 /* milli weight units */
}
,[CHECK_LOCK_TIME] =
{ .tag = JET
, .jet = check_lock_time
, .cmr = {{0xab2c941bu, 0xb3def116u, 0xa592b5beu, 0x8e5fcb3au, 0x74fc961cu, 0x82fb19feu, 0x79680b53u, 0xd521320bu}}
, .sourceIx = ty_w32
, .targetIx = ty_u
, .cost = 95 /* milli weight units */
}
,[CHECK_SIG_VERIFY] =
{ .tag = JET
, .jet = check_sig_verify
, .cmr = {{0x297459d8u, 0x373f8727u, 0xda9f92dau, 0xeab7196bu, 0xed0bd523u, 0x64405521u, 0x4455723au, 0xbac0b085u}}
, .sourceIx = ty_ppw256w512w512
, .targetIx = ty_u
, .cost = 50000 /* milli weight units */
}
,[COMPLEMENT_16] =
{ .tag = JET
, .jet = complement_16
, .cmr = {{0x9d5615f9u, 0x0722d4aeu, 0xfbd8dd09u, 0xc6828843u, 0x68a88f47u, 0x11f62cfeu, 0x029c9f07u, 0x29a27344u}}
, .sourceIx = ty_w16
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[COMPLEMENT_32] =
{ .tag = JET
, .jet = complement_32
, .cmr = {{0x4360c5d2u, 0xa457d443u, 0x219e0267u, 0x74e68deeu, 0x23ef6ec7u, 0xa9137218u, 0x6c9d4603u, 0x94c1519bu}}
, .sourceIx = ty_w32
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[COMPLEMENT_64] =
{ .tag = JET
, .jet = complement_64
, .cmr = {{0x24135882u, 0xf75603d0u, 0x69813490u, 0x2eb50e14u, 0xa9a4a79fu, 0x48e777a6u, 0x97fc02d6u, 0x4c156589u}}
, .sourceIx = ty_w64
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[COMPLEMENT_8] =
{ .tag = JET
, .jet = complement_8
, .cmr = {{0x858b61b0u, 0x7e3d4ef1u, 0x434ec4f4u, 0xaec30d29u, 0x599b8ac3u, 0x8370e58au, 0xfa477b1eu, 0xd39d6b47u}}
, .sourceIx = ty_w8
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[CURRENT_AMOUNT] =
{ .tag = JET
, .jet = current_amount
, .cmr = {{0x2249b61cu, 0x456079b3u, 0x72b1bc12u, 0xd625772du, 0x7dc8e7d8u, 0xc843d31cu, 0xd38dc1d0u, 0xeaffd388u}}
, .sourceIx = ty_u
, .targetIx = ty_pspbw256w256spbw256w64
, .cost = 299 /* milli weight units */
}
,[CURRENT_ANNEX_HASH] =
{ .tag = JET
, .jet = current_annex_hash
, .cmr = {{0x2a06fcc4u, 0x6572e5b3u, 0x863edb47u, 0xcc77a980u, 0xb715d407u, 0xadf8c625u, 0x77e1bb74u, 0x56a2a819u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 128 /* milli weight units */
}
,[CURRENT_ASSET] =
{ .tag = JET
, .jet = current_asset
, .cmr = {{0xd039895eu, 0x438d0fcau, 0xf62521f3u, 0x85634eefu, 0x7a6e7168u, 0x9c9eb15eu, 0x5cd63efeu, 0x5ba8d924u}}
, .sourceIx = ty_u
, .targetIx = ty_spbw256w256
, .cost = 158 /* milli weight units */
}
,[CURRENT_INDEX] =
{ .tag = JET
, .jet = current_index
, .cmr = {{0x60069b2du, 0x6aa06f1eu, 0xf24019b3u, 0xb84efb19u, 0x06ac1004u, 0x9476e5c8u, 0x0ac9aaf5u, 0x0fd1ddedu}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 59 /* milli weight units */
}
,[CURRENT_ISSUANCE_ASSET_AMOUNT] =
{ .tag = JET
, .jet = current_issuance_asset_amount
, .cmr = {{0x1c3c6864u, 0xdd31787fu, 0x25721c46u, 0x59434838u, 0xa07f460eu, 0x512a488fu, 0x0e5da4f9u, 0xae58418du}}
, .sourceIx = ty_u
, .targetIx = ty_mspbw256w64
, .cost = 132 /* milli weight units */
}
,[CURRENT_ISSUANCE_ASSET_PROOF] =
{ .tag = JET
, .jet = current_issuance_asset_proof
, .cmr = {{0x52f89ed9u, 0x965ff116u, 0xb3732122u, 0xa3fb9b8au, 0x3b5dda59u, 0xb3432d77u, 0x717a2060u, 0x8a394ca4u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 129 /* milli weight units */
}
,[CURRENT_ISSUANCE_TOKEN_AMOUNT] =
{ .tag = JET
, .jet = current_issuance_token_amount
, .cmr = {{0x8a9784d9u, 0xc00ddb63u, 0x474965eeu, 0x28015c86u, 0x8ebeb735u, 0x5d22e795u, 0x6c7ea4dbu, 0x97bc6bb4u}}
, .sourceIx = ty_u
, .targetIx = ty_mspbw256w64
, .cost = 127 /* milli weight units */
}
,[CURRENT_ISSUANCE_TOKEN_PROOF] =
{ .tag = JET
, .jet = current_issuance_token_proof
, .cmr = {{0xeb8e1490u, 0x9bf0971du, 0xe3b14e46u, 0xafee8127u, 0x944698d6u, 0xb286af00u, 0xe446c2c8u, 0xc1fed121u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 143 /* milli weight units */
}
,[CURRENT_NEW_ISSUANCE_CONTRACT] =
{ .tag = JET
, .jet = current_new_issuance_contract
, .cmr = {{0x153efc0du, 0x8a739329u, 0xc8dd3731u, 0xea3d06abu, 0x26d4df7cu, 0xa18d8815u, 0x645e6caeu, 0x4f1e4b72u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 146 /* milli weight units */
}
,[CURRENT_PEGIN] =
{ .tag = JET
, .jet = current_pegin
, .cmr = {{0xdf119d08u, 0x35c1b24au, 0xcbe8bc00u, 0x8072056au, 0xa6863401u, 0x9a892174u, 0x1730013eu, 0x76c108f1u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 120 /* milli weight units */
}
,[CURRENT_PREV_OUTPOINT] =
{ .tag = JET
, .jet = current_prev_outpoint
, .cmr = {{0x14addf9du, 0x58716931u, 0x775910c7u, 0xc983f1d4u, 0xf0a0af95u, 0x1f3b0b3fu, 0x3d2cbe62u, 0x95c11d5eu}}
, .sourceIx = ty_u
, .targetIx = ty_pw256w32
, .cost = 120 /* milli weight units */
}
,[CURRENT_REISSUANCE_BLINDING] =
{ .tag = JET
, .jet = current_reissuance_blinding
, .cmr = {{0xe79272ffu, 0x85eb3434u, 0x9fdbcd28u, 0x9d5ab349u, 0x12d47452u, 0x50bd7037u, 0x6567095au, 0x97a0b543u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 200 /* milli weight units */
}
,[CURRENT_REISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = current_reissuance_entropy
, .cmr = {{0x6ababa99u, 0x9abe6662u, 0xcc768c90u, 0x0581a347u, 0xf71ead4du, 0x68091396u, 0xe3e756d6u, 0x6bd55e1eu}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 73 /* milli weight units */
}
,[CURRENT_SCRIPT_HASH] =
{ .tag = JET
, .jet = current_script_hash
, .cmr = {{0xff093823u, 0x75a97b54u, 0xf9ad1c17u, 0xfec20002u, 0x68e4d48eu, 0x3fef2fafu, 0x253f27fbu, 0x801f8dabu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 188 /* milli weight units */
}
,[CURRENT_SCRIPT_SIG_HASH] =
{ .tag = JET
, .jet = current_script_sig_hash
, .cmr = {{0xb3794a09u, 0xbf868684u, 0x5279b6ffu, 0xb236829cu, 0x5d3c8102u, 0xb6cd446eu, 0xbd0214d8u, 0xd9438168u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 542 /* milli weight units */
}
,[CURRENT_SEQUENCE] =
{ .tag = JET
, .jet = current_sequence
, .cmr = {{0xdb7195f6u, 0x9019e0afu, 0xa26440c5u, 0x8e973d42u, 0xc5699ef7u, 0x0732a845u, 0x51049c50u, 0x5f83aa43u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 147 /* milli weight units */
}
,[DECOMPRESS] =
{ .tag = JET
, .jet = decompress
, .cmr = {{0x5985b005u, 0xf201342du, 0x90974927u, 0x30257d68u, 0x3ee54f0du, 0x6bfb68fau, 0xe1821d6au, 0x01fea28cu}}
, .sourceIx = ty_pbw256
, .targetIx = ty_mw512
, .cost = 11173 /* milli weight units */
}
,[DECREMENT_16] =
{ .tag = JET
, .jet = decrement_16
, .cmr = {{0x8873fb6au, 0x447de286u, 0xcd6d64b4u, 0x92d8a1d3u, 0xd7cddfbbu, 0xe675bff5u, 0xc56eba40u, 0xf690dbd3u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw16
, .cost = 109 /* milli weight units */
}
,[DECREMENT_32] =
{ .tag = JET
, .jet = decrement_32
, .cmr = {{0xca2bc9bdu, 0x09c36130u, 0xc52e4cfau, 0x7df6d108u, 0x30616604u, 0x19163d0au, 0x96b669a0u, 0x73966addu}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw32
, .cost = 109 /* milli weight units */
}
,[DECREMENT_64] =
{ .tag = JET
, .jet = decrement_64
, .cmr = {{0xdbc8e757u, 0xbc069624u, 0xb027a9f7u, 0x6f0ae79fu, 0xa20e48b8u, 0x910f7ab4u, 0xa2b16227u, 0xd2b4ccacu}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw64
, .cost = 109 /* milli weight units */
}
,[DECREMENT_8] =
{ .tag = JET
, .jet = decrement_8
, .cmr = {{0xd6ec5fbau, 0x81dcbdd4u, 0x4a1b3ab1u, 0x94add7f5u, 0x42b170cau, 0xdeb465ddu, 0x2f319284u, 0x581a76d6u}}
, .sourceIx = ty_w8
, .targetIx = ty_pbw8
, .cost = 109 /* milli weight units */
}
,[DIV_MOD_16] =
{ .tag = JET
, .jet = div_mod_16
, .cmr = {{0x66ee6d63u, 0x7696760eu, 0xf0903a4eu, 0xe9da7715u, 0xcbf904aau, 0x9f59d84eu, 0xccb35f90u, 0x475d37beu}}
, .sourceIx = ty_w32
, .targetIx = ty_w32
, .cost = 138 /* milli weight units */
}
,[DIV_MOD_32] =
{ .tag = JET
, .jet = div_mod_32
, .cmr = {{0x6c6af762u, 0x0b1d718bu, 0x1e091330u, 0x72b2f204u, 0x358dbe58u, 0x94d3a2c6u, 0x18c2593eu, 0x62f006ccu}}
, .sourceIx = ty_w64
, .targetIx = ty_w64
, .cost = 138 /* milli weight units */
}
,[DIV_MOD_64] =
{ .tag = JET
, .jet = div_mod_64
, .cmr = {{0x2439580du, 0xda934d44u, 0x98fc4177u, 0x4f294de5u, 0x93f44c63u, 0x2f84e721u, 0xa8d5bbdeu, 0x345cce40u}}
, .sourceIx = ty_w128
, .targetIx = ty_w128
, .cost = 138 /* milli weight units */
}
,[DIV_MOD_8] =
{ .tag = JET
, .jet = div_mod_8
, .cmr = {{0x06fb2a19u, 0x7c161d0au, 0x77fc726du, 0x3baa857eu, 0x27f8691bu, 0xcce2b473u, 0xd4d1408cu, 0x17e0321du}}
, .sourceIx = ty_w16
, .targetIx = ty_w16
, .cost = 138 /* milli weight units */
}
,[DIVIDE_16] =
{ .tag = JET
, .jet = divide_16
, .cmr = {{0x701ef05du, 0x05fe5943u, 0x54b2ef79u, 0x6f4ca452u, 0x76daac15u, 0x2592763eu, 0x2a1f6e19u, 0x672576bcu}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 138 /* milli weight units */
}
,[DIVIDE_32] =
{ .tag = JET
, .jet = divide_32
, .cmr = {{0xf883b1c6u, 0x4d044031u, 0xd99e0467u, 0x4254fe2bu, 0xb344bcddu, 0x5438d6eau, 0x01458d9eu, 0x2497702au}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 138 /* milli weight units */
}
,[DIVIDE_64] =
{ .tag = JET
, .jet = divide_64
, .cmr = {{0xaa844cfeu, 0x9a83c526u, 0xd5fb0582u, 0x0d1a6f95u, 0x3eb50c85u, 0x6cda507du, 0xb9be5b7cu, 0x90ab2d14u}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 138 /* milli weight units */
}
,[DIVIDE_8] =
{ .tag = JET
, .jet = divide_8
, .cmr = {{0xbb39218fu, 0x0b2d6930u, 0xa6e41766u, 0xfd5218fau, 0xd1810d17u, 0x6aba801au, 0x26380d35u, 0x1a2d79b1u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 138 /* milli weight units */
}
,[DIVIDES_16] =
{ .tag = JET
, .jet = divides_16
, .cmr = {{0x0e98a53au, 0x6266f4c6u, 0x0bdcaf62u, 0x0dbca76du, 0xb3cc1b59u, 0x8a9c667au, 0xd1da86b5u, 0xc9c0e912u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 138 /* milli weight units */
}
,[DIVIDES_32] =
{ .tag = JET
, .jet = divides_32
, .cmr = {{0x6ed21abfu, 0x022c2ba0u, 0x20e91f0du, 0x09593ba5u, 0x5f742626u, 0x2914e955u, 0xe1791a58u, 0x3b31c07du}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 138 /* milli weight units */
}
,[DIVIDES_64] =
{ .tag = JET
, .jet = divides_64
, .cmr = {{0x3971ea23u, 0x01babb7bu, 0xb54f5f48u, 0x33c63caau, 0x5279d4c2u, 0xb654592fu, 0xbb506eb2u, 0x03b00615u}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 138 /* milli weight units */
}
,[DIVIDES_8] =
{ .tag = JET
, .jet = divides_8
, .cmr = {{0x77635c01u, 0x95719b99u, 0x0feb1431u, 0xb1244eb7u, 0x55aee9bau, 0xcee4b20cu, 0x12be8e23u, 0x9d12f7dcu}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 138 /* milli weight units */
}
,[EQ_16] =
{ .tag = JET
, .jet = eq_16
, .cmr = {{0x081d4c58u, 0x0a515685u, 0xa700cb47u, 0xa5433304u, 0x490add10u, 0x1cbc07c3u, 0xc46efb19u, 0x6b75fe55u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 69 /* milli weight units */
}
,[EQ_256] =
{ .tag = JET
, .jet = eq_256
, .cmr = {{0x56835314u, 0x63050b4fu, 0x9926d0e8u, 0xff64263au, 0x15ceb1ceu, 0xa6541263u, 0x7c235f46u, 0xd7be6605u}}
, .sourceIx = ty_w512
, .targetIx = ty_b
, .cost = 153 /* milli weight units */
}
,[EQ_32] =
{ .tag = JET
, .jet = eq_32
, .cmr = {{0x7387d279u, 0x8a02107eu, 0x2c573671u, 0x27f3f36fu, 0xc9f1970du, 0xafba80f9u, 0x340c168bu, 0x50f7a4e2u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 69 /* milli weight units */
}
,[EQ_64] =
{ .tag = JET
, .jet = eq_64
, .cmr = {{0x0572e16bu, 0xab59d847u, 0x5fda6bfcu, 0xbd496fe7u, 0x534107f6u, 0x291dd7eeu, 0xdbfbf28bu, 0x760aa41au}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 69 /* milli weight units */
}
,[EQ_8] =
{ .tag = JET
, .jet = eq_8
, .cmr = {{0xd42579e4u, 0xe7af6daau, 0x39a54e54u, 0x2747d419u, 0x5c2ab48cu, 0x1fdd7b87u, 0x32e7a52fu, 0xed407599u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 69 /* milli weight units */
}
,[FE_ADD] =
{ .tag = JET
, .jet = fe_add
, .cmr = {{0xdf5c034bu, 0x6459ded2u, 0xf207b5e4u, 0x0f02e508u, 0x76ee6b25u, 0x0cdd8c94u, 0x9fbb783bu, 0x5e9044dau}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 1408 /* milli weight units */
}
,[FE_INVERT] =
{ .tag = JET
, .jet = fe_invert
, .cmr = {{0xc122098fu, 0x95594b72u, 0x1d3a51a3u, 0x1dc1b2c4u, 0x0deccb9bu, 0x3cdc9ab9u, 0x0e561ac2u, 0x1341bce2u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 4008 /* milli weight units */
}
,[FE_IS_ODD] =
{ .tag = JET
, .jet = fe_is_odd
, .cmr = {{0xafa56c6bu, 0x60c52a39u, 0xe5a1610eu, 0xfb8e1ae5u, 0x6f720372u, 0x01cac604u, 0x37b6758au, 0x74469b2au}}
, .sourceIx = ty_w256
, .targetIx = ty_b
, .cost = 311 /* milli weight units */
}
,[FE_IS_ZERO] =
{ .tag = JET
, .jet = fe_is_zero
, .cmr = {{0x511ac5b8u, 0x359c2002u, 0x080a16a1u, 0x1840ab1au, 0xe15b6015u, 0x7372677bu, 0x39a92fd7u, 0xcf3e8eb3u}}
, .sourceIx = ty_w256
, .targetIx = ty_b
, .cost = 299 /* milli weight units */
}
,[FE_MULTIPLY] =
{ .tag = JET
, .jet = fe_multiply
, .cmr = {{0x4db0b0f2u, 0xa2a82138u, 0x7a7dab9cu, 0x5c0ce8ebu, 0xde14d039u, 0x25b56d7fu, 0x309a5e2du, 0x099bf9abu}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 1109 /* milli weight units */
}
,[FE_MULTIPLY_BETA] =
{ .tag = JET
, .jet = fe_multiply_beta
, .cmr = {{0x4532c730u, 0x5f04bb13u, 0x0fef0c4eu, 0x167b9ac0u, 0xcc07bcfcu, 0x66dd2d0cu, 0x678ed913u, 0xaee21d64u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 755 /* milli weight units */
}
,[FE_NEGATE] =
{ .tag = JET
, .jet = fe_negate
, .cmr = {{0x3b1c7d40u, 0x361c5b03u, 0x73771eabu, 0xb066289fu, 0x291f7665u, 0x25eb25abu, 0x42d18dfau, 0x2196da40u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 2187 /* milli weight units */
}
,[FE_NORMALIZE] =
{ .tag = JET
, .jet = fe_normalize
, .cmr = {{0xe089ae03u, 0x972738e5u, 0x8cad4f74u, 0x26e263fau, 0x5e2c6c4bu, 0x5869ef96u, 0x9bec86fcu, 0xb7ad3205u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 2672 /* milli weight units */
}
,[FE_SQUARE] =
{ .tag = JET
, .jet = fe_square
, .cmr = {{0x1f1f57f8u, 0x8b2873f4u, 0xdf4163a6u, 0x8f5398b1u, 0x682a911bu, 0xeb4d6d24u, 0xe8ca271eu, 0x35bae8dbu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 800 /* milli weight units */
}
,[FE_SQUARE_ROOT] =
{ .tag = JET
, .jet = fe_square_root
, .cmr = {{0xb0ea638cu, 0xf250e2a2u, 0x8dcfc8fcu, 0x04094013u, 0x102181f8u, 0x16fefbc6u, 0xcb451be7u, 0x1ee8a805u}}
, .sourceIx = ty_w256
, .targetIx = ty_mw256
, .cost = 12716 /* milli weight units */
}
,[FULL_ADD_16] =
{ .tag = JET
, .jet = full_add_16
, .cmr = {{0x67c57c82u, 0x461860c0u, 0x223a427du, 0xde99e512u, 0x753b0ec5u, 0x2a05dcbeu, 0x718ef30au, 0x2684b681u}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw16
, .cost = 93 /* milli weight units */
}
,[FULL_ADD_32] =
{ .tag = JET
, .jet = full_add_32
, .cmr = {{0x739f5b1eu, 0x9b408b36u, 0x3cdad6bfu, 0x00a8bff5u, 0x22b3d538u, 0x02eaadd8u, 0x94a0107du, 0x203a4600u}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw32
, .cost = 93 /* milli weight units */
}
,[FULL_ADD_64] =
{ .tag = JET
, .jet = full_add_64
, .cmr = {{0x70e1eea5u, 0x3bc9b01bu, 0x0676b5eau, 0x973674d6u, 0xf3c35674u, 0x32f264bcu, 0x60b7ae1fu, 0xf69a402au}}
, .sourceIx = ty_pbw128
, .targetIx = ty_pbw64
, .cost = 93 /* milli weight units */
}
,[FULL_ADD_8] =
{ .tag = JET
, .jet = full_add_8
, .cmr = {{0x37ff9d08u, 0x4dd0517fu, 0xb3897de0u, 0x86381a9cu, 0x2c72440eu, 0xe1bac38du, 0xb7f4f74au, 0x501d54ddu}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw8
, .cost = 93 /* milli weight units */
}
,[FULL_DECREMENT_16] =
{ .tag = JET
, .jet = full_decrement_16
, .cmr = {{0x61e2e85au, 0xb8c7e4c2u, 0xe9dc6eb2u, 0xf060749au, 0x0335412fu, 0x9f3ac8fdu, 0x68f25615u, 0xff067e61u}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw16
, .cost = 109 /* milli weight units */
}
,[FULL_DECREMENT_32] =
{ .tag = JET
, .jet = full_decrement_32
, .cmr = {{0x8be3110bu, 0xdae8d65fu, 0x08331995u, 0xf584bf36u, 0x0236a14cu, 0x61ad2fa6u, 0xe7aeac60u, 0x9bd4dbfau}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw32
, .cost = 109 /* milli weight units */
}
,[FULL_DECREMENT_64] =
{ .tag = JET
, .jet = full_decrement_64
, .cmr = {{0xd0038712u, 0x1999149cu, 0x3a7bd256u, 0xce8bd02du, 0x719f3d5cu, 0x58f10ab6u, 0x757cc023u, 0xd55dbe1bu}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw64
, .cost = 109 /* milli weight units */
}
,[FULL_DECREMENT_8] =
{ .tag = JET
, .jet = full_decrement_8
, .cmr = {{0xe8cc3606u, 0xb1dd7fcfu, 0x64c991b0u, 0xceb9c614u, 0x6cccd089u, 0x4989d8d9u, 0xab97d274u, 0x3ea1a5acu}}
, .sourceIx = ty_pbw8
, .targetIx = ty_pbw8
, .cost = 109 /* milli weight units */
}
,[FULL_INCREMENT_16] =
{ .tag = JET
, .jet = full_increment_16
, .cmr = {{0xceaf13e7u, 0x8e3a3075u, 0xd117480cu, 0x7b72c2bau, 0xd4548cccu, 0xfaf48ea1u, 0xeb677f78u, 0x0e5c0030u}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw16
, .cost = 133 /* milli weight units */
}
,[FULL_INCREMENT_32] =
{ .tag = JET
, .jet = full_increment_32
, .cmr = {{0x7e831288u, 0x87146643u, 0x445af4cau, 0xbb1da50eu, 0x82daeb34u, 0xb7d9a242u, 0xcd00de5fu, 0xbbea5182u}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw32
, .cost = 133 /* milli weight units */
}
,[FULL_INCREMENT_64] =
{ .tag = JET
, .jet = full_increment_64
, .cmr = {{0x93acb583u, 0x1a59b28au, 0xe438876eu, 0x3102f919u, 0x427b8272u, 0x630a8ed7u, 0x8592ef54u, 0x3cfb65f6u}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw64
, .cost = 133 /* milli weight units */
}
,[FULL_INCREMENT_8] =
{ .tag = JET
, .jet = full_increment_8
, .cmr = {{0x921aaaa8u, 0xcac82063u, 0xfbfac051u, 0x17e4a93eu, 0xb2f0b92du, 0x83562199u, 0xebdb8afcu, 0x16b1d52cu}}
, .sourceIx = ty_pbw8
, .targetIx = ty_pbw8
, .cost = 133 /* milli weight units */
}
,[FULL_MULTIPLY_16] =
{ .tag = JET
, .jet = full_multiply_16
, .cmr = {{0x1597386du, 0xa7f0d556u, 0x9966d171u, 0x76eae378u, 0x1bec8fb4u, 0xfde5c8c7u, 0x12daeaa8u, 0x6bd83f37u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 138 /* milli weight units */
}
,[FULL_MULTIPLY_32] =
{ .tag = JET
, .jet = full_multiply_32
, .cmr = {{0xe8b881a1u, 0x26e2c04eu, 0xbd8dc78du, 0x8e24fd92u, 0xcc82ba0cu, 0x41e1a403u, 0xe6431334u, 0xd13c4ec2u}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 138 /* milli weight units */
}
,[FULL_MULTIPLY_64] =
{ .tag = JET
, .jet = full_multiply_64
, .cmr = {{0xdccc7e3cu, 0x397c150au, 0xfdf383beu, 0xd89e95e5u, 0x0594b285u, 0xb8c7d624u, 0xd1b9e059u, 0xe9f7230au}}
, .sourceIx = ty_w256
, .targetIx = ty_w128
, .cost = 138 /* milli weight units */
}
,[FULL_MULTIPLY_8] =
{ .tag = JET
, .jet = full_multiply_8
, .cmr = {{0x20183305u, 0x30454619u, 0xc64f5a10u, 0x9e7b3cceu, 0x817979dbu, 0x5352189eu, 0x3197b051u, 0x99c74de9u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 138 /* milli weight units */
}
,[FULL_SUBTRACT_16] =
{ .tag = JET
, .jet = full_subtract_16
, .cmr = {{0x0919ce69u, 0x1898d27cu, 0x6fc44c13u, 0x7064524eu, 0x413146d1u, 0xce201732u, 0xc975b0d5u, 0x47effa7cu}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw16
, .cost = 104 /* milli weight units */
}
,[FULL_SUBTRACT_32] =
{ .tag = JET
, .jet = full_subtract_32
, .cmr = {{0x810bd282u, 0x67282355u, 0xee694820u, 0x713e68d0u, 0x67bbd8b8u, 0x1ed9138cu, 0x33e51649u, 0x73a56284u}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw32
, .cost = 104 /* milli weight units */
}
,[FULL_SUBTRACT_64] =
{ .tag = JET
, .jet = full_subtract_64
, .cmr = {{0xc867885fu, 0xb9154f6eu, 0x4a68b816u, 0x4ecae1d6u, 0x9feb4f4du, 0xc6c2e1e9u, 0x72af8af8u, 0xc63347f1u}}
, .sourceIx = ty_pbw128
, .targetIx = ty_pbw64
, .cost = 104 /* milli weight units */
}
,[FULL_SUBTRACT_8] =
{ .tag = JET
, .jet = full_subtract_8
, .cmr = {{0xb9f1b9b8u, 0xd10fabbbu, 0xb7df46c8u, 0x75862f7eu, 0x7e701408u, 0x8560b0dau, 0x45480a6cu, 0x7c1259a2u}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw8
, .cost = 104 /* milli weight units */
}
,[GE_IS_ON_CURVE] =
{ .tag = JET
, .jet = ge_is_on_curve
, .cmr = {{0x36d05a72u, 0x9a79b037u, 0xb10b3ab2u, 0xb2c2bfeau, 0x03a01a18u, 0xe0eaf65cu, 0x6f9bc745u, 0xc7c2e6fau}}
, .sourceIx = ty_w512
, .targetIx = ty_b
, .cost = 768 /* milli weight units */
}
,[GE_NEGATE] =
{ .tag = JET
, .jet = ge_negate
, .cmr = {{0x5201d45cu, 0xc1deb3e2u, 0xb949fe66u, 0x0a07c5ceu, 0x69443dbeu, 0xc67cc76bu, 0x2425ff32u, 0xe852e5b4u}}
, .sourceIx = ty_w512
, .targetIx = ty_w512
, .cost = 1596 /* milli weight units */
}
,[GEJ_ADD] =
{ .tag = JET
, .jet = gej_add
, .cmr = {{0x285485c4u, 0x70844925u, 0x10373df4u, 0x3df53407u, 0xacec8fb1u, 0xbd010380u, 0x897b517cu, 0x39cd6319u}}
, .sourceIx = ty_ppw512w256pw512w256
, .targetIx = ty_pw512w256
, .cost = 3274 /* milli weight units */
}
,[GEJ_DOUBLE] =
{ .tag = JET
, .jet = gej_double
, .cmr = {{0x71077458u, 0x5775f91fu, 0x4ce578adu, 0x8d1e6445u, 0x41e21fc6u, 0xc810abdbu, 0x3b3ed211u, 0x5e39cdaeu}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_pw512w256
, .cost = 1899 /* milli weight units */
}
,[GEJ_GE_ADD] =
{ .tag = JET
, .jet = gej_ge_add
, .cmr = {{0x7d7f426eu, 0x42458e45u, 0x771291ccu, 0x9e607e67u, 0x267a3885u, 0xadbebdc3u, 0x69df5966u, 0x3220befbu}}
, .sourceIx = ty_ppw512w256w512
, .targetIx = ty_pw512w256
, .cost = 3004 /* milli weight units */
}
,[GEJ_GE_ADD_EX] =
{ .tag = JET
, .jet = gej_ge_add_ex
, .cmr = {{0xcddae78du, 0x33a22128u, 0xbc2f72a6u, 0x02e0066fu, 0x63fe1862u, 0x57ea348cu, 0x2bb1f7e9u, 0xbf9b0d73u}}
, .sourceIx = ty_ppw512w256w512
, .targetIx = ty_pw256pw512w256
, .cost = 2981 /* milli weight units */
}
,[GEJ_INFINITY] =
{ .tag = JET
, .jet = gej_infinity
, .cmr = {{0x95bd3ce9u, 0x3f0c8e95u, 0xaa2e60a9u, 0xe82657fdu, 0x980f3f27u, 0x7811fb6du, 0x39d1ff12u, 0x1f3f8a14u}}
, .sourceIx = ty_u
, .targetIx = ty_pw512w256
, .cost = 1042 /* milli weight units */
}
,[GEJ_IS_INFINITY] =
{ .tag = JET
, .jet = gej_is_infinity
, .cmr = {{0x6358d3ddu, 0xc7ab52fdu, 0x6ad636adu, 0xf9b9f37eu, 0xaf796f89u, 0xb2d9bfbau, 0x97abee3fu, 0x327b30a4u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
, .cost = 1509 /* milli weight units */
}
,[GEJ_IS_ON_CURVE] =
{ .tag = JET
, .jet = gej_is_on_curve
, .cmr = {{0x6bcc65cfu, 0xed0439f1u, 0x11ee5f5bu, 0x5b4791e1u, 0xe4ad7ff3u, 0x6951a233u, 0x1b18f97fu, 0x7af91398u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
, .cost = 1286 /* milli weight units */
}
,[GEJ_NEGATE] =
{ .tag = JET
, .jet = gej_negate
, .cmr = {{0x0ae36632u, 0x3647831au, 0x3f1c8e51u, 0xf1f6c17eu, 0xec93cf53u, 0x95a27644u, 0x0a246debu, 0xb2efc391u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_pw512w256
, .cost = 1596 /* milli weight units */
}
,[GEJ_NORMALIZE] =
{ .tag = JET
, .jet = gej_normalize
, .cmr = {{0xcb5a52a3u, 0x24295bdau, 0xd42d0fb0u, 0x1f67aadfu, 0x6e10e0b3u, 0xd18c9324u, 0xc3a12a05u, 0xb4fe1d64u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_mw512
, .cost = 5931 /* milli weight units */
}
,[GEJ_RESCALE] =
{ .tag = JET
, .jet = gej_rescale
, .cmr = {{0xe1427860u, 0xb51ba7e7u, 0x072d7569u, 0xc55b8339u, 0xf85b6022u, 0x750c6af5u, 0xaf2a72f1u, 0xb7b6baeeu}}
, .sourceIx = ty_ppw512w256w256
, .targetIx = ty_pw512w256
, .cost = 2462 /* milli weight units */
}
,[GEJ_X_EQUIV] =
{ .tag = JET
, .jet = gej_x_equiv
, .cmr = {{0xa7ee48d5u, 0xfb926d41u, 0xf70bbb0fu, 0x06821375u, 0x343f0d2fu, 0x0e5b1991u, 0x5539d910u, 0x1b8d847au}}
, .sourceIx = ty_pw256pw512w256
, .targetIx = ty_b
, .cost = 1383 /* milli weight units */
}
,[GEJ_Y_IS_ODD] =
{ .tag = JET
, .jet = gej_y_is_odd
, .cmr = {{0xa2d72b1eu, 0x8388a175u, 0x5427a7b2u, 0x55676831u, 0xca76eaddu, 0xa282f97au, 0x343f0eb1u, 0x55f35046u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
, .cost = 5506 /* milli weight units */
}
,[GENERATE] =
{ .tag = JET
, .jet = generate
, .cmr = {{0x0e91f455u, 0x7cb7d4c3u, 0xbbf3f2d0u, 0x74dd6946u, 0x423a3b4fu, 0xacb57a00u, 0xcae43fd6u, 0xa7352a13u}}
, .sourceIx = ty_w256
, .targetIx = ty_pw512w256
, .cost = 49026 /* milli weight units */
}
,[GENESIS_BLOCK_HASH] =
{ .tag = JET
, .jet = genesis_block_hash
, .cmr = {{0x594ccfb4u, 0xb5fa3c0du, 0x3a89dd83u, 0xb74c7543u, 0x2e5557d8u, 0x80fba8afu, 0xa4c80707u, 0x994a9494u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 143 /* milli weight units */
}
,[HIGH_16] =
{ .tag = JET
, .jet = high_16
, .cmr = {{0xae53d2d0u, 0xaa1623b3u, 0xa3c8b553u, 0x826fdef4u, 0x3ff59ea7u, 0xc4a0185cu, 0xf34c1645u, 0x08d8bfbcu}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 57 /* milli weight units */
}
,[HIGH_32] =
{ .tag = JET
, .jet = high_32
, .cmr = {{0x64e7c545u, 0x3c3f8c63u, 0x6c5961f4u, 0x8a57b0ecu, 0x7bdeadedu, 0xa4b35311u, 0x867bde1cu, 0xf7c1c1d8u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 57 /* milli weight units */
}
,[HIGH_64] =
{ .tag = JET
, .jet = high_64
, .cmr = {{0xfdbfad11u, 0x2aff8bd0u, 0x21abeea8u, 0x6888dd28u, 0xba90b1d6u, 0x363b398au, 0x09df9d5fu, 0x40e80608u}}
, .sourceIx = ty_u
, .targetIx = ty_w64
, .cost = 57 /* milli weight units */
}
,[HIGH_8] =
{ .tag = JET
, .jet = high_8
, .cmr = {{0x2d1202eau, 0x633d2d65u, 0xf45eaf80u, 0xea03e5ccu, 0x3d7d9ae4u, 0xa4b37121u, 0x8a0160a6u, 0x93104f69u}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 57 /* milli weight units */
}
,[INCREMENT_16] =
{ .tag = JET
, .jet = increment_16
, .cmr = {{0xef9f6327u, 0x4d9fc071u, 0x0aba342fu, 0xe7ca00d9u, 0x12bf2771u, 0xa940bdd1u, 0x272d289bu, 0x70430044u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw16
, .cost = 133 /* milli weight units */
}
,[INCREMENT_32] =
{ .tag = JET
, .jet = increment_32
, .cmr = {{0x4257a752u, 0xd0895a75u, 0x31a52114u, 0x1553d330u, 0x90b278d0u, 0xbb79d18bu, 0x53cf753cu, 0x76402a0eu}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw32
, .cost = 133 /* milli weight units */
}
,[INCREMENT_64] =
{ .tag = JET
, .jet = increment_64
, .cmr = {{0xb525e554u, 0x40193dc3u, 0xd51d9fc6u, 0xb1f3f291u, 0xf1a2776eu, 0x99a210c9u, 0xfe333677u, 0xd96850f2u}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw64
, .cost = 133 /* milli weight units */
}
,[INCREMENT_8] =
{ .tag = JET
, .jet = increment_8
, .cmr = {{0xb530231au, 0x83320a13u, 0x0f4189f1u, 0xefee5ab2u, 0x9141dce4u, 0xc3149119u, 0xcb21b9cbu, 0x06ce6fa1u}}
, .sourceIx = ty_w8
, .targetIx = ty_pbw8
, .cost = 133 /* milli weight units */
}
,[INPUT_AMOUNT] =
{ .tag = JET
, .jet = input_amount
, .cmr = {{0x5323441bu, 0x79867dfdu, 0xf75f59f3u, 0x532dc516u, 0xdefa9145u, 0xaafb9951u, 0xae89e5b3u, 0xb30be23eu}}
, .sourceIx = ty_w32
, .targetIx = ty_mpspbw256w256spbw256w64
, .cost = 185 /* milli weight units */
}
,[INPUT_AMOUNTS_HASH] =
{ .tag = JET
, .jet = input_amounts_hash
, .cmr = {{0x5346aaf0u, 0x3ac9caf2u, 0xf68cfcdau, 0xdec17c19u, 0xebaff03du, 0xaa15ae74u, 0x1571611bu, 0x0895044bu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 138 /* milli weight units */
}
,[INPUT_ANNEX_HASH] =
{ .tag = JET
, .jet = input_annex_hash
, .cmr = {{0x3df91f8eu, 0xe588aff8u, 0x36c4ad9fu, 0x3b9840e7u, 0x79c4022bu, 0x7a09cb3du, 0xeaeb44d8u, 0x468dd0c9u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 89 /* milli weight units */
}
,[INPUT_ANNEXES_HASH] =
{ .tag = JET
, .jet = input_annexes_hash
, .cmr = {{0x827490bfu, 0x96c1f83bu, 0xaaf7d82cu, 0x7eef453fu, 0xb7493e68u, 0xb9a5b498u, 0xc2dd9983u, 0xb638a176u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 125 /* milli weight units */
}
,[INPUT_ASSET] =
{ .tag = JET
, .jet = input_asset
, .cmr = {{0x0f89057du, 0xff8f5b3du, 0x43e7b07au, 0x75b8c32au, 0xc7177736u, 0x6fc82d3cu, 0xc36d6285u, 0x08384a93u}}
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w256
, .cost = 144 /* milli weight units */
}
,[INPUT_OUTPOINTS_HASH] =
{ .tag = JET
, .jet = input_outpoints_hash
, .cmr = {{0x120b2661u, 0x5e0373ccu, 0xb173d78eu, 0xf37e1c83u, 0x5eb8cf60u, 0x2019b8bfu, 0xf623a134u, 0x28ac63d1u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 141 /* milli weight units */
}
,[INPUT_PEGIN] =
{ .tag = JET
, .jet = input_pegin
, .cmr = {{0x684c9b1au, 0x71fd07d3u, 0x54c0eb24u, 0x1faff747u, 0x601677bdu, 0xbd0287deu, 0x970df386u, 0xc20ddea9u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 162 /* milli weight units */
}
,[INPUT_PREV_OUTPOINT] =
{ .tag = JET
, .jet = input_prev_outpoint
, .cmr = {{0x8af82069u, 0xe2d32b3cu, 0xb298fab7u, 0x548b403cu, 0xe058cc84u, 0x98699560u, 0xac3a9f55u, 0xaa51627du}}
, .sourceIx = ty_w32
, .targetIx = ty_mpw256w32
, .cost = 136 /* milli weight units */
}
,[INPUT_SCRIPT_HASH] =
{ .tag = JET
, .jet = input_script_hash
, .cmr = {{0x6df2547fu, 0x3043f11fu, 0xe6fbcd0bu, 0x682612f9u, 0xf64d836cu, 0x2ae7469du, 0xf5428652u, 0x64162076u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 152 /* milli weight units */
}
,[INPUT_SCRIPT_SIG_HASH] =
{ .tag = JET
, .jet = input_script_sig_hash
, .cmr = {{0x8725a170u, 0x7f605686u, 0xd229608cu, 0x136d832au, 0x57042afdu, 0xcbe1a706u, 0x6892cfc2u, 0x935b8444u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 156 /* milli weight units */
}
,[INPUT_SCRIPT_SIGS_HASH] =
{ .tag = JET
, .jet = input_script_sigs_hash
, .cmr = {{0xb1bfdae8u, 0xf6ec88afu, 0x83aa7576u, 0xc492f525u, 0x3748e8d4u, 0x1f671f9au, 0xf0448713u, 0x90800dbdu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 111 /* milli weight units */
}
,[INPUT_SCRIPTS_HASH] =
{ .tag = JET
, .jet = input_scripts_hash
, .cmr = {{0x32c6b224u, 0x159f2c83u, 0x35f20a95u, 0x7b053885u, 0xa439924au, 0x2fb44e13u, 0x13800a54u, 0xdb112d61u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 156 /* milli weight units */
}
,[INPUT_SEQUENCE] =
{ .tag = JET
, .jet = input_sequence
, .cmr = {{0xdb525e1cu, 0x1071d18cu, 0x53101f6eu, 0xecd9870cu, 0x3d5f1259u, 0xe35665a6u, 0x307a8b64u, 0xce0eda2fu}}
, .sourceIx = ty_w32
, .targetIx = ty_mw32
, .cost = 89 /* milli weight units */
}
,[INPUT_SEQUENCES_HASH] =
{ .tag = JET
, .jet = input_sequences_hash
, .cmr = {{0xec8ed35au, 0x80eddeefu, 0x6da0a006u, 0xcd6a0e27u, 0x5010ec0fu, 0x6fc1b5ecu, 0x9969dd0eu, 0x1abe607cu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 117 /* milli weight units */
}
,[INPUT_UTXOS_HASH] =
{ .tag = JET
, .jet = input_utxos_hash
, .cmr = {{0x39df7578u, 0x397560d5u, 0x232fadfau, 0x058f780bu, 0x44226129u, 0xcbe4dae5u, 0x40d13c42u, 0x20d89fecu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 131 /* milli weight units */
}
,[INPUTS_HASH] =
{ .tag = JET
, .jet = inputs_hash
, .cmr = {{0x16053a9au, 0xd31d50ecu, 0x050495b0u, 0xdb9e0403u, 0x45df24d5u, 0x6932e207u, 0xd27a832bu, 0x6a6801a8u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 114 /* milli weight units */
}
,[INTERNAL_KEY] =
{ .tag = JET
, .jet = internal_key
, .cmr = {{0xe6068a12u, 0xba8a8980u, 0xac2eafa4u, 0xbc0ca0fau, 0x7329db6au, 0xb8455370u, 0x3878fda6u, 0x53c69964u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 108 /* milli weight units */
}
,[IS_ONE_16] =
{ .tag = JET
, .jet = is_one_16
, .cmr = {{0xecc56a7cu, 0x8dae7fb0u, 0x19b9f549u, 0xf83a5da1u, 0x21f374d8u, 0xd45bed50u, 0x778ea6cfu, 0xa9bb9ea0u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ONE_32] =
{ .tag = JET
, .jet = is_one_32
, .cmr = {{0x3f3bc46cu, 0x8c53860cu, 0x49c47028u, 0x11109089u, 0xa2fed0acu, 0xdc3e543bu, 0x8f4c7962u, 0x655f7f93u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ONE_64] =
{ .tag = JET
, .jet = is_one_64
, .cmr = {{0xe7b9c690u, 0x1f20d98cu, 0x65d3e78au, 0xd1716199u, 0x939040d4u, 0xe39780b4u, 0x4344ab80u, 0xbb5f723cu}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ONE_8] =
{ .tag = JET
, .jet = is_one_8
, .cmr = {{0x6aa140d2u, 0xf0e5dd66u, 0xc1210681u, 0x62efc579u, 0xe540f3acu, 0x1c8323d1u, 0xa9226f0eu, 0xb32f8466u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ZERO_16] =
{ .tag = JET
, .jet = is_zero_16
, .cmr = {{0x058368c8u, 0x85f95818u, 0x1676de6du, 0x4d31cabfu, 0x3f7142eeu, 0xa4752128u, 0x01ebe373u, 0x79456c2cu}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ZERO_32] =
{ .tag = JET
, .jet = is_zero_32
, .cmr = {{0x3b739181u, 0x8f80cbd2u, 0x2ed7e5e8u, 0x523c820fu, 0xa0ddc1a6u, 0xc18b0086u, 0xd653ffc3u, 0x7ea7a1acu}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ZERO_64] =
{ .tag = JET
, .jet = is_zero_64
, .cmr = {{0xf81913afu, 0xc609de33u, 0x40a9f67eu, 0x83927b57u, 0x2232eb51u, 0x08c0278cu, 0xbc214761u, 0x92e03cc7u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[IS_ZERO_8] =
{ .tag = JET
, .jet = is_zero_8
, .cmr = {{0xfd9ac08bu, 0x595b1ecbu, 0x848de20fu, 0xf16b7cb2u, 0x7a770a8au, 0x918c018bu, 0x4025f36au, 0xa0c75e32u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[ISSUANCE] =
{ .tag = JET
, .jet = issuance
, .cmr = {{0xf7b6e3c4u, 0x5b16139cu, 0x65ae403du, 0xa60252aeu, 0xf4362ac6u, 0xb1038064u, 0x196db4f6u, 0xcf342f1bu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmb
, .cost = 89 /* milli weight units */
}
,[ISSUANCE_ASSET] =
{ .tag = JET
, .jet = issuance_asset
, .cmr = {{0xfb2b259au, 0x09b3f3b1u, 0xe4314eecu, 0x9d18a0a1u, 0xf734f9a7u, 0x5f586edcu, 0xcccfb9d8u, 0x3443cce7u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 149 /* milli weight units */
}
,[ISSUANCE_ASSET_AMOUNT] =
{ .tag = JET
, .jet = issuance_asset_amount
, .cmr = {{0xf1e9bdecu, 0x382ede64u, 0x226eebcdu, 0x9a446488u, 0xc70c6190u, 0xe2b88db3u, 0x2303947eu, 0x5fe59e1eu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
, .cost = 142 /* milli weight units */
}
,[ISSUANCE_ASSET_AMOUNTS_HASH] =
{ .tag = JET
, .jet = issuance_asset_amounts_hash
, .cmr = {{0xb4efffbbu, 0x92f0dc9cu, 0x918934f2u, 0x9dd6bc97u, 0xe83a1127u, 0xa1b24159u, 0xf8398ac2u, 0x8990c762u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 128 /* milli weight units */
}
,[ISSUANCE_ASSET_PROOF] =
{ .tag = JET
, .jet = issuance_asset_proof
, .cmr = {{0xfeaa9ea6u, 0x8466f476u, 0xb4de3561u, 0x61c70729u, 0xa7a476a6u, 0x576efe66u, 0xe72503efu, 0xf3eaf8bbu}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 133 /* milli weight units */
}
,[ISSUANCE_BLINDING_ENTROPY_HASH] =
{ .tag = JET
, .jet = issuance_blinding_entropy_hash
, .cmr = {{0x26f4cca0u, 0xb7d466dbu, 0x9b2c1f7cu, 0xd92e664du, 0x132187c2u, 0xe2cd799bu, 0x2fb01aaeu, 0x6d9bce10u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 142 /* milli weight units */
}
,[ISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = issuance_entropy
, .cmr = {{0x48654eb9u, 0xd584d7f8u, 0xb8c77d94u, 0x298369d6u, 0x9b2441d7u, 0x5fa69056u, 0xd86b1ef6u, 0x71f7b2b3u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 165 /* milli weight units */
}
,[ISSUANCE_RANGE_PROOFS_HASH] =
{ .tag = JET
, .jet = issuance_range_proofs_hash
, .cmr = {{0x5cea3839u, 0x68f9fb17u, 0x457e5642u, 0x60f26fe0u, 0xb77e66d3u, 0x20b85838u, 0x2580af5cu, 0x978c8215u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 140 /* milli weight units */
}
,[ISSUANCE_TOKEN] =
{ .tag = JET
, .jet = issuance_token
, .cmr = {{0x85e9591cu, 0xf642e78du, 0x5e314b3au, 0xfc016869u, 0x2dbb1f21u, 0x07e516b3u, 0xd40979c3u, 0x1ec08c4bu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 176 /* milli weight units */
}
,[ISSUANCE_TOKEN_AMOUNT] =
{ .tag = JET
, .jet = issuance_token_amount
, .cmr = {{0x8c69f379u, 0x7af5d500u, 0x9f2706e2u, 0xfbbc5f6du, 0x21dfa39du, 0xa9f7101bu, 0xdb5c9a0bu, 0xdc2efbd5u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
, .cost = 152 /* milli weight units */
}
,[ISSUANCE_TOKEN_AMOUNTS_HASH] =
{ .tag = JET
, .jet = issuance_token_amounts_hash
, .cmr = {{0xd02239aeu, 0xeb45b4b1u, 0x12d4cf03u, 0xafe12899u, 0x56666d0du, 0xa0614460u, 0xa1cb342du, 0x1c839313u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 143 /* milli weight units */
}
,[ISSUANCE_TOKEN_PROOF] =
{ .tag = JET
, .jet = issuance_token_proof
, .cmr = {{0xb976fddau, 0x118a6339u, 0x5f7f6f75u, 0x9d855402u, 0xc2f0a0dcu, 0x25660374u, 0xd3b5f32eu, 0x45265351u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 139 /* milli weight units */
}
,[ISSUANCES_HASH] =
{ .tag = JET
, .jet = issuances_hash
, .cmr = {{0x97b7242bu, 0x3266a143u, 0x12b0b6abu, 0xb41a5341u, 0xdda8efd4u, 0xeed43ba8u, 0x58175142u, 0x774f0486u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 124 /* milli weight units */
}
,[LE_16] =
{ .tag = JET
, .jet = le_16
, .cmr = {{0x900c665eu, 0xbe884d50u, 0x71c32b3au, 0x0b6b65a1u, 0x2cbab6f0u, 0x82480efau, 0x06945a06u, 0x5fe15866u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LE_32] =
{ .tag = JET
, .jet = le_32
, .cmr = {{0xef40fc7cu, 0x215856bbu, 0x7e87414au, 0x395b4f02u, 0xe2c4bb16u, 0x7c8526edu, 0x43105d56u, 0x42b0d6b6u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LE_64] =
{ .tag = JET
, .jet = le_64
, .cmr = {{0xf91b2886u, 0xb9da94f7u, 0xe797b758u, 0x14cfeeb2u, 0x8ce073e2u, 0x14e5a55fu, 0x7019b697u, 0x8b0d6742u}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LE_8] =
{ .tag = JET
, .jet = le_8
, .cmr = {{0x8cfb5e97u, 0x85644545u, 0xcc42eb6au, 0x14b7e958u, 0x27949900u, 0xaaa3c5adu, 0xc8024af3u, 0xc2a31b44u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LINEAR_COMBINATION_1] =
{ .tag = JET
, .jet = linear_combination_1
, .cmr = {{0x950786efu, 0xa65a7122u, 0xe2554c6fu, 0xb55124f9u, 0xe5acd82cu, 0x29817affu, 0xc19fc7a9u, 0x27d3a070u}}
, .sourceIx = ty_ppw256pw512w256w256
, .targetIx = ty_pw512w256
, .cost = 83117 /* milli weight units */
}
,[LINEAR_VERIFY_1] =
{ .tag = JET
, .jet = linear_verify_1
, .cmr = {{0x635571b1u, 0x27c01565u, 0x7c1bfb1du, 0x9267bb84u, 0x6a7bf949u, 0x7507aea6u, 0x65373574u, 0x08e711a3u}}
, .sourceIx = ty_pppw256w512w256w512
, .targetIx = ty_u
, .cost = 49791 /* milli weight units */
}
,[LOCK_TIME] =
{ .tag = JET
, .jet = lock_time
, .cmr = {{0xf2a371aau, 0x251729bfu, 0xbbc8b510u, 0x7dbc99e1u, 0x50bf22c1u, 0x2e80c8bbu, 0x9308067fu, 0xa7fc2161u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 59 /* milli weight units */
}
,[LOW_16] =
{ .tag = JET
, .jet = low_16
, .cmr = {{0xb327ae29u, 0x99ed5f59u, 0x421584fdu, 0x537f99c5u, 0xfa10271eu, 0x53e1332bu, 0x1f534635u, 0x540dc84du}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 57 /* milli weight units */
}
,[LOW_32] =
{ .tag = JET
, .jet = low_32
, .cmr = {{0x3a13276cu, 0x6097d272u, 0xdb1398c1u, 0xd03e1302u, 0x2e729d73u, 0xce50f8b2u, 0xe5b2aaf9u, 0x936a2be1u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 57 /* milli weight units */
}
,[LOW_64] =
{ .tag = JET
, .jet = low_64
, .cmr = {{0x0619c995u, 0x66f8d3dcu, 0x826e8ef9u, 0x67657019u, 0x1dbce1a0u, 0x2e74d922u, 0xb1120cb7u, 0x2d38513bu}}
, .sourceIx = ty_u
, .targetIx = ty_w64
, .cost = 57 /* milli weight units */
}
,[LOW_8] =
{ .tag = JET
, .jet = low_8
, .cmr = {{0xaab5a1e3u, 0xe6f02747u, 0xd5b64897u, 0xfe37f2f7u, 0x37ca2be4u, 0xdc9c85a6u, 0xe804ad5eu, 0x95ed0833u}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 57 /* milli weight units */
}
,[LT_16] =
{ .tag = JET
, .jet = lt_16
, .cmr = {{0x267ab9e8u, 0xdeeefa01u, 0xbdd4d9fcu, 0x524bda2cu, 0x4ae5b95eu, 0x7725ab97u, 0xaa042201u, 0x3e86a4aeu}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LT_32] =
{ .tag = JET
, .jet = lt_32
, .cmr = {{0xc31a4716u, 0x1a1b5f77u, 0xe279fd22u, 0xba9ab0c3u, 0xe19c7719u, 0xa00cfee6u, 0x036db68eu, 0x1b9ec6dfu}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LT_64] =
{ .tag = JET
, .jet = lt_64
, .cmr = {{0x586e2b1fu, 0x0b0cfa80u, 0x0f831d35u, 0xed1fdb96u, 0x4feb47bcu, 0x62f7c0d4u, 0x16de3fd8u, 0x3bb25642u}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[LT_8] =
{ .tag = JET
, .jet = lt_8
, .cmr = {{0xafe989bfu, 0xd8ba4dc1u, 0x06d2e3b0u, 0xb30b1d9bu, 0x5e6916ccu, 0xcebcd987u, 0x40b6a9c3u, 0xb903b626u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[MAJ_16] =
{ .tag = JET
, .jet = maj_16
, .cmr = {{0xd447911bu, 0x6fbd547du, 0x430566bcu, 0xe521ccf2u, 0x5dff0ff5u, 0x2ae7ab01u, 0x0b695ae0u, 0x87ec1b71u}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[MAJ_32] =
{ .tag = JET
, .jet = maj_32
, .cmr = {{0x665711e6u, 0x270ba267u, 0x56c0c185u, 0xb70117a1u, 0x296ff6c2u, 0x9e426aa9u, 0x55f61495u, 0x85286c49u}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[MAJ_64] =
{ .tag = JET
, .jet = maj_64
, .cmr = {{0x69f4ced9u, 0xc712736du, 0x0d8ee1c4u, 0xdcda4ff5u, 0x7f24eb31u, 0x42f9e068u, 0x48de60beu, 0x575c9149u}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[MAJ_8] =
{ .tag = JET
, .jet = maj_8
, .cmr = {{0x6bcbfe9cu, 0xf8c13241u, 0x1177ba84u, 0xf40fc84eu, 0x0b8c1644u, 0x24505fddu, 0x3bdf27f7u, 0x2a0df7f6u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[MAX_16] =
{ .tag = JET
, .jet = max_16
, .cmr = {{0x193449e0u, 0xb845be48u, 0xbbb11324u, 0xbac63445u, 0x1a53bf03u, 0x12cb0e8bu, 0x71b1d463u, 0x675692fdu}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 98 /* milli weight units */
}
,[MAX_32] =
{ .tag = JET
, .jet = max_32
, .cmr = {{0xee99dd4cu, 0x3de496a2u, 0x74ce3c06u, 0x50f81c1eu, 0xd9cea85bu, 0xaaf29c21u, 0x33337098u, 0x4ca2535cu}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 98 /* milli weight units */
}
,[MAX_64] =
{ .tag = JET
, .jet = max_64
, .cmr = {{0xfc75a5d0u, 0xc2de6fc6u, 0xc3f3525cu, 0x6e8a8938u, 0x35aa9f7au, 0x8d3d3518u, 0x1d0a581bu, 0x2723ee4eu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 98 /* milli weight units */
}
,[MAX_8] =
{ .tag = JET
, .jet = max_8
, .cmr = {{0xcfcf1720u, 0x71f03ca6u, 0x18ccd358u, 0x21063d4eu, 0xc13ccc6du, 0x73df9946u, 0xe9cdb777u, 0xb11fb437u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 98 /* milli weight units */
}
,[MEDIAN_16] =
{ .tag = JET
, .jet = median_16
, .cmr = {{0x04b102c6u, 0xbf517d0du, 0x5890d55eu, 0x0d1a0c23u, 0x9540820au, 0x0cde2620u, 0xd52c602cu, 0x6556af66u}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 98 /* milli weight units */
}
,[MEDIAN_32] =
{ .tag = JET
, .jet = median_32
, .cmr = {{0x779febffu, 0x10bb1640u, 0xa76edb05u, 0x1058d58fu, 0xe7c379bbu, 0x8b73d2e2u, 0xb1d7c20du, 0x2682c50du}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 98 /* milli weight units */
}
,[MEDIAN_64] =
{ .tag = JET
, .jet = median_64
, .cmr = {{0xdb62cc65u, 0xbe87a907u, 0xb687bc32u, 0x36f75b63u, 0xa7b73d75u, 0x649eb654u, 0xebac1968u, 0x6c32628eu}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 98 /* milli weight units */
}
,[MEDIAN_8] =
{ .tag = JET
, .jet = median_8
, .cmr = {{0x89773702u, 0x27419ec2u, 0x26ba4ad4u, 0x5f44064fu, 0x82f97303u, 0x94cb792du, 0xc543a65bu, 0xcaae7b09u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 98 /* milli weight units */
}
,[MIN_16] =
{ .tag = JET
, .jet = min_16
, .cmr = {{0x0938261du, 0xf2a5a0deu, 0x397126e7u, 0x6541e216u, 0x6b242ae8u, 0x87570dbau, 0xcf9a3b6fu, 0x982133d9u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 98 /* milli weight units */
}
,[MIN_32] =
{ .tag = JET
, .jet = min_32
, .cmr = {{0xa2b85ae1u, 0x70c99f8fu, 0x46a0f8f8u, 0xc21ba6e1u, 0x419b691du, 0x46ef6b28u, 0x73df96dbu, 0xb9858900u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 98 /* milli weight units */
}
,[MIN_64] =
{ .tag = JET
, .jet = min_64
, .cmr = {{0x3ea48619u, 0x3d0d1affu, 0x0cc6eaabu, 0x1831f5f2u, 0x5c30e78du, 0x7e25b0b0u, 0xc2781e1eu, 0xcabf462eu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 98 /* milli weight units */
}
,[MIN_8] =
{ .tag = JET
, .jet = min_8
, .cmr = {{0xe9b4e541u, 0xe30dd518u, 0x37a2388cu, 0xb06c3de9u, 0x0568b4e8u, 0xfe240201u, 0xfda833aeu, 0x57899164u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 98 /* milli weight units */
}
,[MODULO_16] =
{ .tag = JET
, .jet = modulo_16
, .cmr = {{0x6dcfa19bu, 0xf65f478du, 0x306f113fu, 0xbb64b33au, 0xe21e99c0u, 0xe75c46a9u, 0xd87dbdafu, 0x729ec8a4u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 138 /* milli weight units */
}
,[MODULO_32] =
{ .tag = JET
, .jet = modulo_32
, .cmr = {{0x332ad058u, 0x626c5e58u, 0x81c74aabu, 0x45820208u, 0xef3b3ee5u, 0xc08a0de2u, 0x87124592u, 0x111821ecu}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 138 /* milli weight units */
}
,[MODULO_64] =
{ .tag = JET
, .jet = modulo_64
, .cmr = {{0x1f5d0b25u, 0x5fe6d83eu, 0x33d2019au, 0x2c66ece9u, 0x750c0207u, 0x3a10df2au, 0x573bc0e9u, 0x02bc591bu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 138 /* milli weight units */
}
,[MODULO_8] =
{ .tag = JET
, .jet = modulo_8
, .cmr = {{0xfc6685a7u, 0x7098b109u, 0x29c6a2bau, 0x8c97b9a0u, 0xbc64b1f2u, 0x0ae78d53u, 0x9f592be9u, 0x7295079du}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 138 /* milli weight units */
}
,[MULTIPLY_16] =
{ .tag = JET
, .jet = multiply_16
, .cmr = {{0x53cb583eu, 0xdee8bf8du, 0x65dba995u, 0x65708a94u, 0x75a7c375u, 0x3f0983e4u, 0x861f22dfu, 0xb66a3d58u}}
, .sourceIx = ty_w32
, .targetIx = ty_w32
, .cost = 87 /* milli weight units */
}
,[MULTIPLY_32] =
{ .tag = JET
, .jet = multiply_32
, .cmr = {{0x0f2d9ff6u, 0x5ba4942cu, 0x5ffa4d8eu, 0x6e1f5d91u, 0x0c1abbfeu, 0x24d865a0u, 0x2e066720u, 0xe7a4cb66u}}
, .sourceIx = ty_w64
, .targetIx = ty_w64
, .cost = 87 /* milli weight units */
}
,[MULTIPLY_64] =
{ .tag = JET
, .jet = multiply_64
, .cmr = {{0x6a6d34feu, 0xccf3c6cdu, 0xa6355a41u, 0xd074e318u, 0xf91ac098u, 0x21ce0a49u, 0xe25215a9u, 0xce8b4157u}}
, .sourceIx = ty_w128
, .targetIx = ty_w128
, .cost = 87 /* milli weight units */
}
,[MULTIPLY_8] =
{ .tag = JET
, .jet = multiply_8
, .cmr = {{0x4e552afcu, 0x5ddbfe21u, 0xf80e69ffu, 0xf6b21943u, 0xd0994391u, 0x833982efu, 0xdadb867du, 0x06167548u}}
, .sourceIx = ty_w16
, .targetIx = ty_w16
, .cost = 87 /* milli weight units */
}
,[NEGATE_16] =
{ .tag = JET
, .jet = negate_16
, .cmr = {{0x10ddc65du, 0x21f5ad08u, 0x2d70e9afu, 0x9be46dc5u, 0xcb5ee3d6u, 0x16a83b61u, 0xf6d1b445u, 0xf76fc221u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw16
, .cost = 109 /* milli weight units */
}
,[NEGATE_32] =
{ .tag = JET
, .jet = negate_32
, .cmr = {{0x30009b3cu, 0x588c0deeu, 0x3e5bc9a4u, 0x1b2d0bb0u, 0x8c0af0d9u, 0xb42c88a5u, 0xb707e36cu, 0x56482c9bu}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw32
, .cost = 109 /* milli weight units */
}
,[NEGATE_64] =
{ .tag = JET
, .jet = negate_64
, .cmr = {{0xa0c2a166u, 0x13a1fcbcu, 0x1393ca07u, 0x0bb558f6u, 0x57659b07u, 0xf0b43e61u, 0xce9c627eu, 0xd9d7db63u}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw64
, .cost = 109 /* milli weight units */
}
,[NEGATE_8] =
{ .tag = JET
, .jet = negate_8
, .cmr = {{0xcfb438b3u, 0x0788d7dau, 0x99f787f2u, 0xfa89333eu, 0xde1cf63bu, 0x84780226u, 0x24d61590u, 0xad50a737u}}
, .sourceIx = ty_w8
, .targetIx = ty_pbw8
, .cost = 109 /* milli weight units */
}
,[NEW_ISSUANCE_CONTRACT] =
{ .tag = JET
, .jet = new_issuance_contract
, .cmr = {{0x8c01b15fu, 0x01a994ccu, 0xca7bb1f1u, 0x47e938d3u, 0x6c94d3bau, 0x0438679cu, 0x28039d33u, 0x6dc6a61fu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 192 /* milli weight units */
}
,[NONCE_HASH] =
{ .tag = JET
, .jet = nonce_hash
, .cmr = {{0x94e5a03du, 0xd4b87540u, 0x995f73d8u, 0x785c5621u, 0x20905061u, 0x6e765007u, 0xc48b8f25u, 0xc563d9f0u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256mspbw256w256
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 433 /* milli weight units */
}
,[NUM_INPUTS] =
{ .tag = JET
, .jet = num_inputs
, .cmr = {{0x8c2e0971u, 0xf3818f39u, 0x9bdf4164u, 0x7c5491feu, 0xe9aa101eu, 0xe1832ab4u, 0xb4a24c54u, 0x1e0979d5u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 60 /* milli weight units */
}
,[NUM_OUTPUTS] =
{ .tag = JET
, .jet = num_outputs
, .cmr = {{0x447165a3u, 0x76e3668au, 0x5a228bbbu, 0xcd41ab74u, 0xb8b51b95u, 0x61190e34u, 0xe8f668c3u, 0x956b9407u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 60 /* milli weight units */
}
,[ONE_16] =
{ .tag = JET
, .jet = one_16
, .cmr = {{0xef62cf64u, 0xfe058846u, 0x5780e600u, 0xd28c8314u, 0x751c74f5u, 0xd2417fafu, 0x7b58729au, 0x79a403fau}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 53 /* milli weight units */
}
,[ONE_32] =
{ .tag = JET
, .jet = one_32
, .cmr = {{0x0a8186f9u, 0xd66afbccu, 0xb153e89eu, 0x5d21530fu, 0x0d6601fau, 0x359c4a30u, 0x58e909bcu, 0xeffe207du}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 53 /* milli weight units */
}
,[ONE_64] =
{ .tag = JET
, .jet = one_64
, .cmr = {{0x964df8bau, 0xb0508211u, 0x74674476u, 0x12317e1cu, 0x64538de6u, 0xc9b25dd6u, 0xb11860dfu, 0x36739425u}}
, .sourceIx = ty_u
, .targetIx = ty_w64
, .cost = 53 /* milli weight units */
}
,[ONE_8] =
{ .tag = JET
, .jet = one_8
, .cmr = {{0xd3dba301u, 0x75389bf1u, 0x3305156au, 0xf9d69c6bu, 0xa204d3b2u, 0x69bf8e2bu, 0x9038e063u, 0x503ae5cfu}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 53 /* milli weight units */
}
,[OR_16] =
{ .tag = JET
, .jet = or_16
, .cmr = {{0x01fb5f5au, 0xe2aabb88u, 0x93523288u, 0x89bc69c0u, 0xe52eeb96u, 0x715b189eu, 0x333804f0u, 0xa4924c9cu}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[OR_32] =
{ .tag = JET
, .jet = or_32
, .cmr = {{0xb2758f51u, 0x1449f2aau, 0x776643d8u, 0xe04bfb6eu, 0x10b4591du, 0xba919e1cu, 0x194fc89bu, 0xb045fd29u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[OR_64] =
{ .tag = JET
, .jet = or_64
, .cmr = {{0xa40d0b13u, 0x84a3e0b0u, 0xadf5936bu, 0x78279e52u, 0x3fe55bebu, 0x3fe42668u, 0x3bc87ec9u, 0x9bbe279au}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[OR_8] =
{ .tag = JET
, .jet = or_8
, .cmr = {{0xc603c1e8u, 0x1b5a2e8eu, 0x4cbf81d0u, 0x59a5a0c7u, 0xc4d91a17u, 0x928c9d5cu, 0xaebf67b8u, 0x6d0034c3u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[OUTPOINT_HASH] =
{ .tag = JET
, .jet = outpoint_hash
, .cmr = {{0xb30d9892u, 0x050c76bdu, 0xeff8a67fu, 0xd8c3ed60u, 0x52620f2fu, 0x87db347du, 0x0fe61877u, 0x550f0b57u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256pmw256pw256w32
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 427 /* milli weight units */
}
,[OUTPUT_AMOUNT] =
{ .tag = JET
, .jet = output_amount
, .cmr = {{0xcb062822u, 0x9d2cb3eau, 0x72aec00bu, 0x69ccd043u, 0x9c4506beu, 0xef7bb628u, 0xaf5d197fu, 0xe5420f72u}}
, .sourceIx = ty_w32
, .targetIx = ty_mpspbw256w256spbw256w64
, .cost = 166 /* milli weight units */
}
,[OUTPUT_AMOUNTS_HASH] =
{ .tag = JET
, .jet = output_amounts_hash
, .cmr = {{0x7655791bu, 0xc50e7577u, 0xdfc652c2u, 0x10f2afb0u, 0x31369b80u, 0xa3bb38d2u, 0x99445e0bu, 0xdb84375bu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 127 /* milli weight units */
}
,[OUTPUT_ASSET] =
{ .tag = JET
, .jet = output_asset
, .cmr = {{0x20c54582u, 0x850167c7u, 0x5afc3e68u, 0xf4d65b2du, 0x375a8a89u, 0x9c13d11eu, 0xa8dc91cfu, 0x55595d3cu}}
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w256
, .cost = 142 /* milli weight units */
}
,[OUTPUT_NONCE] =
{ .tag = JET
, .jet = output_nonce
, .cmr = {{0xbc8e1c22u, 0x2d1c8f83u, 0x92c2c5c0u, 0xb84f1919u, 0xe68a81e4u, 0x87455ebeu, 0x60e452dfu, 0xad609488u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w256
, .cost = 74 /* milli weight units */
}
,[OUTPUT_NONCES_HASH] =
{ .tag = JET
, .jet = output_nonces_hash
, .cmr = {{0x23233619u, 0x96f9f9b5u, 0xd60ba02cu, 0xf49b53a3u, 0xc2c402d1u, 0x43985c67u, 0x593b22edu, 0x05c902f6u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 111 /* milli weight units */
}
,[OUTPUT_NULL_DATUM] =
{ .tag = JET
, .jet = output_null_datum
, .cmr = {{0xab6a96b6u, 0xf0de074bu, 0x857409adu, 0xdc107a91u, 0x9ea79df8u, 0x64cbac8au, 0x8bd267b4u, 0x47728dd0u}}
, .sourceIx = ty_w64
, .targetIx = ty_mmspw2w256sbw4
, .cost = 73 /* milli weight units */
}
,[OUTPUT_RANGE_PROOF] =
{ .tag = JET
, .jet = output_range_proof
, .cmr = {{0x45a8b746u, 0xa01f59cfu, 0x180ce4f3u, 0x2c57f1dau, 0xe8f16a75u, 0xf994f13au, 0x7b83f8f4u, 0xfc4374abu}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 233 /* milli weight units */
}
,[OUTPUT_RANGE_PROOFS_HASH] =
{ .tag = JET
, .jet = output_range_proofs_hash
, .cmr = {{0x3422555bu, 0xe12dda7eu, 0xc1953601u, 0x1a01acfdu, 0xf0905b39u, 0xbe475801u, 0x5c05d2fdu, 0xe6164cf1u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 111 /* milli weight units */
}
,[OUTPUT_SCRIPT_HASH] =
{ .tag = JET
, .jet = output_script_hash
, .cmr = {{0x88378e35u, 0x4b46b272u, 0xe5cfb0bdu, 0x977f92f3u, 0x09f10dc2u, 0xe0c5aaf8u, 0xd9be81f5u, 0xe0238d44u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 130 /* milli weight units */
}
,[OUTPUT_SCRIPTS_HASH] =
{ .tag = JET
, .jet = output_scripts_hash
, .cmr = {{0x4d128cbcu, 0xfdb9e09cu, 0xd7c3599du, 0x1f29d75au, 0xe718dbf3u, 0xe93d5dbbu, 0xaf8d6e11u, 0x2d58362fu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 122 /* milli weight units */
}
,[OUTPUT_SURJECTION_PROOF] =
{ .tag = JET
, .jet = output_surjection_proof
, .cmr = {{0x516c4fb6u, 0x9a1d40aeu, 0xeddd9a13u, 0x25001d14u, 0x5b5b452du, 0x8c6f6f37u, 0x0e0471ffu, 0x301071c6u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 127 /* milli weight units */
}
,[OUTPUT_SURJECTION_PROOFS_HASH] =
{ .tag = JET
, .jet = output_surjection_proofs_hash
, .cmr = {{0xcfc06c2fu, 0x712638a7u, 0x6474afa3u, 0x43c125c3u, 0xdafccceau, 0x7c147ac6u, 0x79b9f3b6u, 0xcc0a6184u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 163 /* milli weight units */
}
,[OUTPUTS_HASH] =
{ .tag = JET
, .jet = outputs_hash
, .cmr = {{0xdcb53803u, 0xf099efecu, 0xa0564b5bu, 0x25971269u, 0x2814069cu, 0x46dda031u, 0x5bc2678eu, 0xc2900bc1u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 136 /* milli weight units */
}
,[PARSE_LOCK] =
{ .tag = JET
, .jet = parse_lock
, .cmr = {{0x4871cbaeu, 0x527866bau, 0x125081dfu, 0x03751e23u, 0x1a612822u, 0xbd45de3bu, 0xcfe6a8c5u, 0x14e2e743u}}
, .sourceIx = ty_w32
, .targetIx = ty_sw32w32
, .cost = 84 /* milli weight units */
}
,[PARSE_SEQUENCE] =
{ .tag = JET
, .jet = parse_sequence
, .cmr = {{0xfcf5d5cfu, 0x6908935eu, 0x585e9afcu, 0xc00717fdu, 0xb1c54879u, 0x5b23f08bu, 0xb8138317u, 0x7d93cad9u}}
, .sourceIx = ty_w32
, .targetIx = ty_msw16w16
, .cost = 82 /* milli weight units */
}
,[POINT_VERIFY_1] =
{ .tag = JET
, .jet = point_verify_1
, .cmr = {{0x6a089d61u, 0xca200a42u, 0x58e8b5b4u, 0xfe5c08d5u, 0x74856249u, 0x8d75f6c6u, 0x2609bb68u, 0xc98b407cu}}
, .sourceIx = ty_pppw256pbw256w256pbw256
, .targetIx = ty_u
, .cost = 56153 /* milli weight units */
}
,[REISSUANCE_BLINDING] =
{ .tag = JET
, .jet = reissuance_blinding
, .cmr = {{0xb9af1712u, 0xcb93107fu, 0x23367c21u, 0x7f3f0995u, 0x78d7f91fu, 0xe3e6943cu, 0xd6286162u, 0x30cbf6c7u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 82 /* milli weight units */
}
,[REISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = reissuance_entropy
, .cmr = {{0x9ba49e89u, 0x0cf51e18u, 0x243cab94u, 0xf5adeae7u, 0x40756cc9u, 0x5c1a9175u, 0x4a6d2902u, 0x474a20dau}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 179 /* milli weight units */
}
,[SCALAR_ADD] =
{ .tag = JET
, .jet = scalar_add
, .cmr = {{0xa23aa2c3u, 0x3dd1eff2u, 0x49a17c91u, 0xc99a151du, 0x3087dc7cu, 0x4591cf94u, 0xc5c6abc1u, 0xba6d1cecu}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 862 /* milli weight units */
}
,[SCALAR_INVERT] =
{ .tag = JET
, .jet = scalar_invert
, .cmr = {{0xf22df7d7u, 0x5efdea1cu, 0xfc53c570u, 0xcb8b12a2u, 0xd341067cu, 0xb5fe41e9u, 0x9dbd5fb6u, 0x3282e51eu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 3853 /* milli weight units */
}
,[SCALAR_IS_ZERO] =
{ .tag = JET
, .jet = scalar_is_zero
, .cmr = {{0x4162f933u, 0x2703d01eu, 0x8da63686u, 0xe857f28cu, 0x19820310u, 0x722e096bu, 0xb97fb461u, 0xaff5620cu}}
, .sourceIx = ty_w256
, .targetIx = ty_b
, .cost = 323 /* milli weight units */
}
,[SCALAR_MULTIPLY] =
{ .tag = JET
, .jet = scalar_multiply
, .cmr = {{0x72cb0436u, 0xf6f1478cu, 0xcf8c5456u, 0x98c674dfu, 0x03c39a9du, 0x2daba131u, 0x503346efu, 0x30d58c26u}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 1070 /* milli weight units */
}
,[SCALAR_MULTIPLY_LAMBDA] =
{ .tag = JET
, .jet = scalar_multiply_lambda
, .cmr = {{0x2b600337u, 0x64ceec76u, 0x23af54d3u, 0x86f687ceu, 0x30032570u, 0xb56e9d5cu, 0x31648fbfu, 0x65e01427u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 736 /* milli weight units */
}
,[SCALAR_NEGATE] =
{ .tag = JET
, .jet = scalar_negate
, .cmr = {{0x645ae573u, 0xd5d68b2bu, 0x1afeace9u, 0x0639bd3au, 0x289eeb82u, 0x61a6b472u, 0x4c23caa9u, 0x1b36593cu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 726 /* milli weight units */
}
,[SCALAR_NORMALIZE] =
{ .tag = JET
, .jet = scalar_normalize
, .cmr = {{0xdd3765a5u, 0x1661cf66u, 0x06922f61u, 0x9fca6458u, 0x529d1e92u, 0x56098346u, 0x922247bdu, 0x041bc11fu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 740 /* milli weight units */
}
,[SCALAR_SQUARE] =
{ .tag = JET
, .jet = scalar_square
, .cmr = {{0x6bffd435u, 0x3f64fe9du, 0xf8cfcb58u, 0x6dfdd004u, 0x4cb03a6du, 0xe9137d4cu, 0xe994ff9du, 0xa135ffe4u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 822 /* milli weight units */
}
,[SCALE] =
{ .tag = JET
, .jet = scale
, .cmr = {{0x229c9fafu, 0xadd9745eu, 0x00d108b8u, 0x2b836205u, 0x9e83570du, 0xfc36cb1au, 0x2ce9c5c2u, 0xd913c644u}}
, .sourceIx = ty_pw256pw512w256
, .targetIx = ty_pw512w256
, .cost = 75458 /* milli weight units */
}
,[SCRIPT_CMR] =
{ .tag = JET
, .jet = script_cmr
, .cmr = {{0x8a5ff5e2u, 0x03c92e9bu, 0x597d2e67u, 0x23102207u, 0xa1195625u, 0xbf49f8dbu, 0x843a9ff1u, 0xe21554b8u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 110 /* milli weight units */
}
,[SHA_256_BLOCK] =
{ .tag = JET
, .jet = sha_256_block
, .cmr = {{0x45b27886u, 0xa5eed409u, 0xef05b530u, 0xc70e3662u, 0xfaee4312u, 0xd3759df2u, 0x41449836u, 0x1b5117aeu}}
, .sourceIx = ty_pw256w512
, .targetIx = ty_w256
, .cost = 1046 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_1] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_1
, .cmr = {{0x41665490u, 0xd6edb4c5u, 0xd5284568u, 0x2d7cbd1eu, 0x6c0745fau, 0xfcc092f3u, 0xef1b6fe9u, 0xccb42b59u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w8
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 454 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_128] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_128
, .cmr = {{0xed92b891u, 0x9abb891cu, 0x0fd20ffeu, 0xa6caaea1u, 0xbd79b9e3u, 0xa82afe2cu, 0xc0ce4730u, 0x86f2ae2au}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w1Ki
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 401 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_16] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_16
, .cmr = {{0x1ad8c219u, 0xf971a4aeu, 0x29c26995u, 0x97150a11u, 0x5bae2c09u, 0xf3bc5fd8u, 0x79502163u, 0xeedd7b8du}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w128
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 340 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_2] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_2
, .cmr = {{0x25ab7aa9u, 0xf7f857bdu, 0x26895b89u, 0x0df33316u, 0xd70f70b0u, 0xc268ea3eu, 0xc019e03eu, 0x50c5bd7eu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w16
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 576 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_256] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_256
, .cmr = {{0x10de9da4u, 0xe8f7a291u, 0x80843791u, 0x2e24d248u, 0xe84dacd7u, 0x496825d3u, 0xcac50672u, 0x3c21891fu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w2Ki
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 572 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_32] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_32
, .cmr = {{0x6956f807u, 0xb56ed664u, 0x07ede0bfu, 0xffb61869u, 0x9fc57802u, 0xbed344b6u, 0x5eaef139u, 0xec69ef0cu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w256
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 326 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_4] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_4
, .cmr = {{0x77d6f4b1u, 0x3f2c5c42u, 0x5f45fcf1u, 0x869f9aceu, 0x8cc86bd4u, 0x90e7b314u, 0x134ef599u, 0xbbf221bau}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w32
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 570 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_512] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_512
, .cmr = {{0xa8760df3u, 0x76f07e76u, 0x2df6559fu, 0x69b11761u, 0x383b3ff6u, 0xd831fb5bu, 0x542b9172u, 0xfa34b935u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w4Ki
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 559 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_64] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_64
, .cmr = {{0x8048d490u, 0x5c14b182u, 0xd8f83c81u, 0x8d0322c2u, 0xd1e47950u, 0x88981ac7u, 0xab99c87bu, 0x12c6eb88u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w512
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 475 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_8] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_8
, .cmr = {{0xe5c839a5u, 0xa3296cb3u, 0xcd38297fu, 0x92e26363u, 0x0a6f2994u, 0xc9bbbd2au, 0xfa7da83bu, 0x1edce8fbu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w64
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 330 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_BUFFER_511] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_buffer_511
, .cmr = {{0x11b13d73u, 0x30ae18e9u, 0x197b921bu, 0x8125752fu, 0x8fd9b519u, 0x7204da5au, 0x7ea924ecu, 0x072cf5feu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256pmw2Kipmw1Kipmw512pmw256pmw128pmw64pmw32pmw16mw8
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 412 /* milli weight units */
}
,[SHA_256_CTX_8_FINALIZE] =
{ .tag = JET
, .jet = sha_256_ctx_8_finalize
, .cmr = {{0xe8c270dfu, 0x3d70a395u, 0x65d2c645u, 0x3d68e61fu, 0x459783f1u, 0x9aa4f62du, 0xb56c9a1eu, 0xc1125d6au}}
, .sourceIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .targetIx = ty_w256
, .cost = 1205 /* milli weight units */
}
,[SHA_256_CTX_8_INIT] =
{ .tag = JET
, .jet = sha_256_ctx_8_init
, .cmr = {{0x6ecfda8cu, 0x9be3e834u, 0xc5ad10ccu, 0xf25db15eu, 0xce9ba2b3u, 0x73e85ca1u, 0x81e73739u, 0x8da6fc80u}}
, .sourceIx = ty_u
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 237 /* milli weight units */
}
,[SHA_256_IV] =
{ .tag = JET
, .jet = sha_256_iv
, .cmr = {{0x9adb294au, 0xa5639a79u, 0x29acc5eau, 0x858b2a89u, 0xb5c5bfc1u, 0xd0936f89u, 0x32ae6bb2u, 0x9b3ee669u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 107 /* milli weight units */
}
,[SIG_ALL_HASH] =
{ .tag = JET
, .jet = sig_all_hash
, .cmr = {{0x9902bc0fu, 0xf1f59ed5u, 0xd592258bu, 0x7aa891a0u, 0x3567c13bu, 0xf9f67989u, 0xf8d8b463u, 0xf3863f65u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 135 /* milli weight units */
}
,[SOME_16] =
{ .tag = JET
, .jet = some_16
, .cmr = {{0xd98012fdu, 0x0990a170u, 0x4f92803eu, 0xfc14a956u, 0xed3ad37bu, 0x3efc4039u, 0x19af1e20u, 0x8d0b3320u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[SOME_32] =
{ .tag = JET
, .jet = some_32
, .cmr = {{0x7a248151u, 0xb7ba6700u, 0x30d090f0u, 0xa00f423bu, 0xbe153276u, 0xb3a7a303u, 0x33449c67u, 0x60896fabu}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[SOME_64] =
{ .tag = JET
, .jet = some_64
, .cmr = {{0xa3a06c9bu, 0xc478c0d4u, 0x25cb264eu, 0xa9de3e13u, 0x8a7a1384u, 0x9df06169u, 0xe85b5036u, 0xfe976978u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[SOME_8] =
{ .tag = JET
, .jet = some_8
, .cmr = {{0xd6e33068u, 0x8d027532u, 0x098a6e19u, 0xdc417a97u, 0xd9deb05au, 0x86d1f9c0u, 0xc3aaca74u, 0xebc95828u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 98 /* milli weight units */
}
,[SUBTRACT_16] =
{ .tag = JET
, .jet = subtract_16
, .cmr = {{0x142314e6u, 0x74268d2fu, 0xb657ef84u, 0x49853892u, 0xeef46140u, 0x896b720eu, 0x46e8b00du, 0x6d50af54u}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw16
, .cost = 109 /* milli weight units */
}
,[SUBTRACT_32] =
{ .tag = JET
, .jet = subtract_32
, .cmr = {{0x4c459b19u, 0x16e31d51u, 0xcc03e611u, 0x5841fb1fu, 0x9233ff2bu, 0x38d8e711u, 0xe9e016cfu, 0x896531f6u}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw32
, .cost = 109 /* milli weight units */
}
,[SUBTRACT_64] =
{ .tag = JET
, .jet = subtract_64
, .cmr = {{0x6b353ca0u, 0x35bf5a64u, 0xae2c2d4eu, 0x7705dfedu, 0x8b06aa58u, 0x9ca12cc9u, 0x23fd724cu, 0xcbd131edu}}
, .sourceIx = ty_w128
, .targetIx = ty_pbw64
, .cost = 109 /* milli weight units */
}
,[SUBTRACT_8] =
{ .tag = JET
, .jet = subtract_8
, .cmr = {{0x22d24d97u, 0xa4012b0au, 0x57787d72u, 0x94d4d9dbu, 0x9d2b85bau, 0x89bbc8c1u, 0x248fc83au, 0xfd264717u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw8
, .cost = 109 /* milli weight units */
}
,[TAP_ENV_HASH] =
{ .tag = JET
, .jet = tap_env_hash
, .cmr = {{0xa53b8ebdu, 0xe6ed47bdu, 0xaf72a4e1u, 0x39bbf4e1u, 0x75cf69a8u, 0x5df97f9fu, 0x28c4a79fu, 0x2f427737u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 136 /* milli weight units */
}
,[TAPBRANCH] =
{ .tag = JET
, .jet = tapbranch
, .cmr = {{0x22516da6u, 0x8f110893u, 0x5cb3f1c5u, 0x8fa0a4fdu, 0x3b004f81u, 0xf56d62f2u, 0x9388d420u, 0xe2954991u}}
, .sourceIx = ty_w8
, .targetIx = ty_mw256
, .cost = 94 /* milli weight units */
}
,[TAPBRANCH_HASH] =
{ .tag = JET
, .jet = tapbranch_hash
, .cmr = {{0x8f90864au, 0x37619dc0u, 0xb67c8b52u, 0xe7d7ceebu, 0xd3d25ff8u, 0xcae7e7f2u, 0xb163fcaau, 0x24867e32u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 136 /* milli weight units */
}
,[TAPLEAF_HASH] =
{ .tag = JET
, .jet = tapleaf_hash
, .cmr = {{0xbce8d062u, 0xd481e813u, 0x4401dce3u, 0x1ae742acu, 0xa3c20f93u, 0xec640f90u, 0x69ab683cu, 0x167345dau}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 117 /* milli weight units */
}
,[TAPLEAF_VERSION] =
{ .tag = JET
, .jet = tapleaf_version
, .cmr = {{0xfe503a57u, 0x730c66fcu, 0xcd61eb5du, 0xf63e4daau, 0x0c3e13deu, 0x1434a23du, 0x0feb7c0du, 0x72844e54u}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 80 /* milli weight units */
}
,[TX_HASH] =
{ .tag = JET
, .jet = tx_hash
, .cmr = {{0xb7d46672u, 0x64eecda3u, 0x6019f4e3u, 0x26d39327u, 0x701b2488u, 0x4e72dfb4u, 0x810f71c4u, 0xf1782e7au}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 163 /* milli weight units */
}
,[TX_IS_FINAL] =
{ .tag = JET
, .jet = tx_is_final
, .cmr = {{0x7a65d5a6u, 0x05d47087u, 0xb47ffc6cu, 0xff037044u, 0xda7095b6u, 0xe190b41au, 0x68672071u, 0x9a5fbaefu}}
, .sourceIx = ty_u
, .targetIx = ty_b
, .cost = 67 /* milli weight units */
}
,[TX_LOCK_DISTANCE] =
{ .tag = JET
, .jet = tx_lock_distance
, .cmr = {{0xecaf8885u, 0x06cad00au, 0xc971146bu, 0x4a89f5aau, 0xbabdf583u, 0x2e2cafd9u, 0xfc9a817du, 0x00b185b8u}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 72 /* milli weight units */
}
,[TX_LOCK_DURATION] =
{ .tag = JET
, .jet = tx_lock_duration
, .cmr = {{0xa199b26du, 0xf4494288u, 0xc5b533bdu, 0x39081846u, 0x681d2be9u, 0x8195fafeu, 0x807c7072u, 0x72320571u}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 63 /* milli weight units */
}
,[TX_LOCK_HEIGHT] =
{ .tag = JET
, .jet = tx_lock_height
, .cmr = {{0x56df87acu, 0x8a857ca0u, 0x6f874066u, 0xe41b0541u, 0x636b68c0u, 0x68dad09fu, 0xa9723ac7u, 0x68376584u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 71 /* milli weight units */
}
,[TX_LOCK_TIME] =
{ .tag = JET
, .jet = tx_lock_time
, .cmr = {{0xb8da7911u, 0x8d5b4366u, 0x4f51a135u, 0x58f8437au, 0x75ec886fu, 0x113f5559u, 0x60d6e28du, 0x2b614835u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 61 /* milli weight units */
}
,[VERIFY] =
{ .tag = JET
, .jet = verify
, .cmr = {{0x020e8401u, 0x3030ec69u, 0xd9a93fecu, 0x7110e727u, 0xead51288u, 0x5fa3c572u, 0xd8cfc347u, 0x2ca5c8e8u}}
, .sourceIx = ty_b
, .targetIx = ty_u
, .cost = 45 /* milli weight units */
}
,[VERSION] =
{ .tag = JET
, .jet = version
, .cmr = {{0x8fdf01a1u, 0x856ca95du, 0xc14d138du, 0x4b7fd084u, 0x3ea1119eu, 0x5f81cf4du, 0x43c80a1fu, 0xef888314u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 176 /* milli weight units */
}
,[XOR_16] =
{ .tag = JET
, .jet = xor_16
, .cmr = {{0xa6101440u, 0x5ba14a9bu, 0xd47d3f8fu, 0x38731976u, 0x5d34f07eu, 0xe28258e1u, 0x63a8ac1fu, 0x037487d2u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[XOR_32] =
{ .tag = JET
, .jet = xor_32
, .cmr = {{0x146d0172u, 0x5176eb83u, 0x200a70ccu, 0x4b793ce9u, 0x525cfe28u, 0x9944d4bdu, 0xf2f1c29fu, 0x890a86f9u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[XOR_64] =
{ .tag = JET
, .jet = xor_64
, .cmr = {{0x7c8981c7u, 0x6feb1488u, 0xe3861806u, 0xe8233639u, 0x5256b5cbu, 0xa445abf4u, 0x8fec540du, 0xd3f94380u}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[XOR_8] =
{ .tag = JET
, .jet = xor_8
, .cmr = {{0x4e790651u, 0x60c45368u, 0xa0f6a760u, 0xd31d9eebu, 0x0b92b332u, 0x74147237u, 0x1057ad04u, 0x7902d3dau}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
,[XOR_XOR_16] =
{ .tag = JET
, .jet = xor_xor_16
, .cmr = {{0x5b1cd287u, 0x52729029u, 0x6eba6dffu, 0xc564536du, 0x4f7a0412u, 0x12af8c27u, 0x1cb5b162u, 0xc20b871du}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[XOR_XOR_32] =
{ .tag = JET
, .jet = xor_xor_32
, .cmr = {{0x4f96b4f5u, 0x655dd3c7u, 0x59fe0a4cu, 0x38d10794u, 0x79bec4edu, 0x992529ffu, 0x1a075924u, 0xbb1c63c1u}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 133 /* milli weight units */
}
,[XOR_XOR_64] =
{ .tag = JET
, .jet = xor_xor_64
, .cmr = {{0x350087bfu, 0xdc119d8cu, 0x8577e9a2u, 0xf5239e28u, 0xfecc430fu, 0x4c2d41c0u, 0x187d263fu, 0x7966796cu}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 133 /* milli weight units */
}
,[XOR_XOR_8] =
{ .tag = JET
, .jet = xor_xor_8
, .cmr = {{0xdc4a3581u, 0xeef9f3a4u, 0x0ed12facu, 0x10915cc6u, 0x604320c0u, 0xdec94f19u, 0xe5851127u, 0xf94f2d36u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 133 /* milli weight units */
}
