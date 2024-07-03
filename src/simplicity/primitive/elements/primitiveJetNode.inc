/* This file has been automatically generated. */
[ADD_16] =
{ .tag = JET
, .jet = add_16
, .cmr = {{0x90e5c302u, 0xc2a102f7u, 0x6cc20bcdu, 0xddc0622bu, 0xf3b8a544u, 0x6ab68d1bu, 0x2a03395eu, 0x6fae9250u}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw16
, .cost = 226 /* milli weight units */
}
,[ADD_32] =
{ .tag = JET
, .jet = add_32
, .cmr = {{0x6d7830d6u, 0x5e69f27du, 0x551c4bb3u, 0x718da935u, 0x222faec4u, 0xaf7f49e9u, 0x5e9833edu, 0x2f84c106u}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw32
, .cost = 183 /* milli weight units */
}
,[ADD_64] =
{ .tag = JET
, .jet = add_64
, .cmr = {{0x9eeebea8u, 0x47388e14u, 0xc7c9e7cau, 0x147c7071u, 0x4de144ebu, 0xab398a53u, 0xf4f58a34u, 0x930cc45cu}}
, .sourceIx = ty_w128
, .targetIx = ty_pbw64
, .cost = 221 /* milli weight units */
}
,[ADD_8] =
{ .tag = JET
, .jet = add_8
, .cmr = {{0x3759b040u, 0x6aa2c4e1u, 0x152621e0u, 0x11e4efdbu, 0x555c6ab6u, 0xd91ae9ebu, 0xf1d6315bu, 0x4382a6c4u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw8
, .cost = 150 /* milli weight units */
}
,[ALL_16] =
{ .tag = JET
, .jet = all_16
, .cmr = {{0x3e7e953du, 0x28a6dc5eu, 0xd7dfbd4cu, 0x63f2e080u, 0x47c71bb9u, 0xc437e8c7u, 0x1ee0147au, 0x60f78beeu}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 110 /* milli weight units */
}
,[ALL_32] =
{ .tag = JET
, .jet = all_32
, .cmr = {{0x5dd08516u, 0x26036cb6u, 0xa42aa952u, 0x93dbb8f3u, 0x6efe5e0eu, 0xa57a3108u, 0x27fa6d79u, 0x2f46e0c1u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 136 /* milli weight units */
}
,[ALL_64] =
{ .tag = JET
, .jet = all_64
, .cmr = {{0xbad02fd1u, 0x58908a1bu, 0xe068725eu, 0xb05276deu, 0xfa411207u, 0xd0c8a91bu, 0xbe6fa57du, 0x2cda29dfu}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 165 /* milli weight units */
}
,[ALL_8] =
{ .tag = JET
, .jet = all_8
, .cmr = {{0xdc098854u, 0xdd06ae1eu, 0x6e3e73a4u, 0xae94d0b2u, 0xacce5cb3u, 0xecc12e8cu, 0xb8167f7bu, 0x6eaa4069u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 113 /* milli weight units */
}
,[AND_1] =
{ .tag = JET
, .jet = and_1
, .cmr = {{0x2dc2dbccu, 0x69c12c78u, 0x30df1170u, 0xd9e93a35u, 0xd8284cc8u, 0x15916aebu, 0x3b1b95efu, 0xdaa92c26u}}
, .sourceIx = ty_w2
, .targetIx = ty_b
, .cost = 159 /* milli weight units */
}
,[AND_16] =
{ .tag = JET
, .jet = and_16
, .cmr = {{0x4f42c688u, 0xcc3ceb76u, 0x1f662a0bu, 0x8e77b196u, 0x42dab540u, 0x7d9a873cu, 0xd9c18609u, 0x977ebd91u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 195 /* milli weight units */
}
,[AND_32] =
{ .tag = JET
, .jet = and_32
, .cmr = {{0x1680cfd2u, 0x643ad389u, 0x6bfb45e9u, 0x6fc62dc2u, 0xbb0cc0acu, 0x486fa833u, 0x30a8890cu, 0x09ee969bu}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 175 /* milli weight units */
}
,[AND_64] =
{ .tag = JET
, .jet = and_64
, .cmr = {{0xa2dd3d49u, 0xf12cd442u, 0xcea7c832u, 0x3868be3cu, 0xe6e9af67u, 0x6f725110u, 0xf3ce494eu, 0xdd6a5a4au}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 221 /* milli weight units */
}
,[AND_8] =
{ .tag = JET
, .jet = and_8
, .cmr = {{0x27554178u, 0x198658f5u, 0xbfb5b041u, 0x30898742u, 0xbf82db60u, 0x39dcbb17u, 0x266dfe03u, 0x0cc12075u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 159 /* milli weight units */
}
,[ANNEX_HASH] =
{ .tag = JET
, .jet = annex_hash
, .cmr = {{0xca1beda0u, 0x4f1fe8cbu, 0xb08cd69fu, 0x3959d442u, 0xfe5ab015u, 0xc6923e17u, 0x1d8d0686u, 0xef31488fu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256mw256
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 3065 /* milli weight units */
}
,[ASSET_AMOUNT_HASH] =
{ .tag = JET
, .jet = asset_amount_hash
, .cmr = {{0x4ff7e73cu, 0xe7fbbfa1u, 0xc577e6feu, 0x1dab70b8u, 0xf10bb4dfu, 0x319c0f6du, 0x67994f6fu, 0xdb224258u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256pspbw256w256spbw256w64
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 3177 /* milli weight units */
}
,[BIP_0340_VERIFY] =
{ .tag = JET
, .jet = bip_0340_verify
, .cmr = {{0x3a196ec1u, 0x9d8f3fccu, 0x67b0ad8fu, 0x611e762du, 0xc1189a72u, 0x2faa745bu, 0x694d292cu, 0x47373f53u}}
, .sourceIx = ty_w1Ki
, .targetIx = ty_u
, .cost = 49671 /* milli weight units */
}
,[BUILD_TAPBRANCH] =
{ .tag = JET
, .jet = build_tapbranch
, .cmr = {{0xd4b31312u, 0x786cb33bu, 0x43b062d4u, 0x8e0be039u, 0xc7de2b8du, 0x67ce9eeau, 0x5f5225f1u, 0x97ef7774u}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 4804 /* milli weight units */
}
,[BUILD_TAPLEAF_SIMPLICITY] =
{ .tag = JET
, .jet = build_tapleaf_simplicity
, .cmr = {{0x136f16e4u, 0x4ae55b7eu, 0x6330d656u, 0xa282cbe5u, 0xaf966e74u, 0x1f576c9du, 0x0acd7749u, 0x467fd505u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 3670 /* milli weight units */
}
,[CALCULATE_ASSET] =
{ .tag = JET
, .jet = calculate_asset
, .cmr = {{0x2eaae24du, 0xccce3c94u, 0x4beb8e38u, 0xac6a52eau, 0x434420fbu, 0x56a9a9b4u, 0xfb841583u, 0x48087421u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 1516 /* milli weight units */
}
,[CALCULATE_CONFIDENTIAL_TOKEN] =
{ .tag = JET
, .jet = calculate_confidential_token
, .cmr = {{0x3c5bf08au, 0xba5aa33eu, 0xba87efb0u, 0x99bdf1c4u, 0x64e7722au, 0xece1a221u, 0x3dc8eb25u, 0x54f0b56bu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 1727 /* milli weight units */
}
,[CALCULATE_EXPLICIT_TOKEN] =
{ .tag = JET
, .jet = calculate_explicit_token
, .cmr = {{0xbef44e2eu, 0x52ccbfbau, 0xc88fd4d0u, 0xbdad51a4u, 0x69b484c7u, 0x585b7825u, 0x8ad4a79bu, 0xc9e4803bu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 1610 /* milli weight units */
}
,[CALCULATE_ISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = calculate_issuance_entropy
, .cmr = {{0xca162c8au, 0xab8f94ddu, 0xe208dd87u, 0x1306b4ccu, 0x917ef2d8u, 0x1b8df75fu, 0xb23a916eu, 0xb3be197eu}}
, .sourceIx = ty_ppw256w32w256
, .targetIx = ty_w256
, .cost = 3453 /* milli weight units */
}
,[CH_1] =
{ .tag = JET
, .jet = ch_1
, .cmr = {{0xc2323612u, 0x4da01f3du, 0x8eb742c2u, 0xed47953fu, 0x66c8b084u, 0xd95a10c6u, 0x0cae69bau, 0x9842ae96u}}
, .sourceIx = ty_pbw2
, .targetIx = ty_b
, .cost = 240 /* milli weight units */
}
,[CH_16] =
{ .tag = JET
, .jet = ch_16
, .cmr = {{0xdccde6a9u, 0x545875c5u, 0xcb46e72cu, 0x7b04ceebu, 0x920c203du, 0x1c042aecu, 0x91241dbeu, 0xca23f435u}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 245 /* milli weight units */
}
,[CH_32] =
{ .tag = JET
, .jet = ch_32
, .cmr = {{0x8c0a87eeu, 0x8e1dfca3u, 0x4bdff421u, 0x2ba1af75u, 0x44d2de6fu, 0x4acb7618u, 0x08231a5fu, 0x57788e62u}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 238 /* milli weight units */
}
,[CH_64] =
{ .tag = JET
, .jet = ch_64
, .cmr = {{0x5d5ae57du, 0x7647f01eu, 0xc3fd797eu, 0xd89d62beu, 0x5fe585fbu, 0xb9fdb6c3u, 0x208b2c08u, 0x579b9e2cu}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 274 /* milli weight units */
}
,[CH_8] =
{ .tag = JET
, .jet = ch_8
, .cmr = {{0xdfc578f2u, 0x5cb31402u, 0xe22a810eu, 0x98950ae1u, 0x7b190896u, 0x364cdee8u, 0xeea300cfu, 0x79d87801u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 240 /* milli weight units */
}
,[CHECK_LOCK_DISTANCE] =
{ .tag = JET
, .jet = check_lock_distance
, .cmr = {{0xc510cd9au, 0xf3ead171u, 0xe189f9e1u, 0x0c95463du, 0x331b1673u, 0x941de384u, 0xe846ab71u, 0x57538ee6u}}
, .sourceIx = ty_w16
, .targetIx = ty_u
, .cost = 198 /* milli weight units */
}
,[CHECK_LOCK_DURATION] =
{ .tag = JET
, .jet = check_lock_duration
, .cmr = {{0x4a64700cu, 0x730c6351u, 0x94cced20u, 0x471b0a69u, 0xc6dea271u, 0xb04a41aau, 0x8c76437bu, 0x74628ddbu}}
, .sourceIx = ty_w16
, .targetIx = ty_u
, .cost = 201 /* milli weight units */
}
,[CHECK_LOCK_HEIGHT] =
{ .tag = JET
, .jet = check_lock_height
, .cmr = {{0x00dd5316u, 0x8f951773u, 0x818c1ea6u, 0x9797ed00u, 0xcccd3762u, 0xd2edb6d9u, 0x5feb7670u, 0x9805d49fu}}
, .sourceIx = ty_w32
, .targetIx = ty_u
, .cost = 239 /* milli weight units */
}
,[CHECK_LOCK_TIME] =
{ .tag = JET
, .jet = check_lock_time
, .cmr = {{0xdea6df2au, 0x1980028fu, 0x423b6a49u, 0x042e1ee5u, 0x361760e9u, 0x42f0ea68u, 0xf9bf9dcau, 0xab57de53u}}
, .sourceIx = ty_w32
, .targetIx = ty_u
, .cost = 232 /* milli weight units */
}
,[CHECK_SIG_VERIFY] =
{ .tag = JET
, .jet = check_sig_verify
, .cmr = {{0xa516dd5cu, 0x9cabd041u, 0x120ea368u, 0xab4ccd92u, 0x31255ef5u, 0x79968558u, 0xc1aa6a21u, 0x2f168329u}}
, .sourceIx = ty_ppw256w512w512
, .targetIx = ty_u
, .cost = 50000 /* milli weight units */
}
,[COMPLEMENT_1] =
{ .tag = JET
, .jet = complement_1
, .cmr = {{0x7e714813u, 0x2e289282u, 0x3fcf2a26u, 0xc6220beeu, 0x039ff6c5u, 0xd7c1b4e4u, 0xca213ad8u, 0x37ab4774u}}
, .sourceIx = ty_b
, .targetIx = ty_b
, .cost = 139 /* milli weight units */
}
,[COMPLEMENT_16] =
{ .tag = JET
, .jet = complement_16
, .cmr = {{0x7f16d124u, 0x15998768u, 0x347f43a9u, 0xb91c8987u, 0x591dfec1u, 0xcf7850b4u, 0x23fea33au, 0x3726f463u}}
, .sourceIx = ty_w16
, .targetIx = ty_w16
, .cost = 146 /* milli weight units */
}
,[COMPLEMENT_32] =
{ .tag = JET
, .jet = complement_32
, .cmr = {{0xe65a4f75u, 0x5411b480u, 0xb80585fdu, 0xc02ee24cu, 0xbbd9502au, 0x48a7347au, 0x710294e7u, 0x82acffbau}}
, .sourceIx = ty_w32
, .targetIx = ty_w32
, .cost = 161 /* milli weight units */
}
,[COMPLEMENT_64] =
{ .tag = JET
, .jet = complement_64
, .cmr = {{0xd5c65713u, 0x8a6cf553u, 0x22c36e6fu, 0x3c4a0f9fu, 0xb63988a1u, 0x120d6eebu, 0x03fc427cu, 0xad971869u}}
, .sourceIx = ty_w64
, .targetIx = ty_w64
, .cost = 174 /* milli weight units */
}
,[COMPLEMENT_8] =
{ .tag = JET
, .jet = complement_8
, .cmr = {{0x1f5c6ab4u, 0x1d406badu, 0xfc9d5a2cu, 0x76bef7e3u, 0x287aabeeu, 0x19d0850fu, 0x09389846u, 0xeabf458eu}}
, .sourceIx = ty_w8
, .targetIx = ty_w8
, .cost = 139 /* milli weight units */
}
,[CURRENT_AMOUNT] =
{ .tag = JET
, .jet = current_amount
, .cmr = {{0x7631944bu, 0x936d0b7fu, 0xa92a868du, 0xd76e4d47u, 0x2936cf42u, 0x5cd86e5bu, 0x90936fbdu, 0x8d54e202u}}
, .sourceIx = ty_u
, .targetIx = ty_pspbw256w256spbw256w64
, .cost = 400 /* milli weight units */
}
,[CURRENT_ANNEX_HASH] =
{ .tag = JET
, .jet = current_annex_hash
, .cmr = {{0x45ca8294u, 0xef4d6120u, 0xe9ef59ebu, 0xeb8c51d2u, 0xc4e816f5u, 0x2d148f64u, 0x250eb8a3u, 0xaa050e18u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 137 /* milli weight units */
}
,[CURRENT_ASSET] =
{ .tag = JET
, .jet = current_asset
, .cmr = {{0x38f14f83u, 0xc6a0474cu, 0x3bc22cabu, 0x540faf66u, 0xbb06d67eu, 0xa12c0048u, 0xf475980du, 0x5c2b7c5eu}}
, .sourceIx = ty_u
, .targetIx = ty_spbw256w256
, .cost = 320 /* milli weight units */
}
,[CURRENT_INDEX] =
{ .tag = JET
, .jet = current_index
, .cmr = {{0x755022edu, 0xc3fab4bcu, 0x656eedc4u, 0x617ea37du, 0x132b2c46u, 0x1740a62du, 0xcad472eau, 0x23de629eu}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 137 /* milli weight units */
}
,[CURRENT_ISSUANCE_ASSET_AMOUNT] =
{ .tag = JET
, .jet = current_issuance_asset_amount
, .cmr = {{0xeac74d4cu, 0x7de43514u, 0x164fe5aeu, 0x76016045u, 0xa68358cfu, 0x1c74241bu, 0x152ed063u, 0xac9f5e29u}}
, .sourceIx = ty_u
, .targetIx = ty_mspbw256w64
, .cost = 317 /* milli weight units */
}
,[CURRENT_ISSUANCE_ASSET_PROOF] =
{ .tag = JET
, .jet = current_issuance_asset_proof
, .cmr = {{0x362dfa80u, 0xda8410c5u, 0xf5066647u, 0xab642f0du, 0x6b7286acu, 0x2608b954u, 0xc3a15cdfu, 0x0f55555eu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 301 /* milli weight units */
}
,[CURRENT_ISSUANCE_TOKEN_AMOUNT] =
{ .tag = JET
, .jet = current_issuance_token_amount
, .cmr = {{0x859241c0u, 0x4b8f0dc7u, 0x3072aed7u, 0x838067fau, 0x70a4ca52u, 0x16f39713u, 0xf12f5fc5u, 0xa4aead7du}}
, .sourceIx = ty_u
, .targetIx = ty_mspbw256w64
, .cost = 326 /* milli weight units */
}
,[CURRENT_ISSUANCE_TOKEN_PROOF] =
{ .tag = JET
, .jet = current_issuance_token_proof
, .cmr = {{0x1b7ea16fu, 0x032f37dcu, 0x2ae103e6u, 0x962c5a90u, 0x42af295bu, 0x4a703a3cu, 0x842e6295u, 0x15ad24cbu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 288 /* milli weight units */
}
,[CURRENT_NEW_ISSUANCE_CONTRACT] =
{ .tag = JET
, .jet = current_new_issuance_contract
, .cmr = {{0x0baa8735u, 0xa3029084u, 0x857cc974u, 0x9bbc7f19u, 0x851bc78fu, 0xbecdce1fu, 0x0dd6757bu, 0x7b8f3f30u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 293 /* milli weight units */
}
,[CURRENT_PEGIN] =
{ .tag = JET
, .jet = current_pegin
, .cmr = {{0x9807ac5eu, 0xb07ba24fu, 0xb021b74au, 0xe6874f3bu, 0xc9b393c6u, 0x6c4f5d22u, 0xf05546e2u, 0xea08d760u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 303 /* milli weight units */
}
,[CURRENT_PREV_OUTPOINT] =
{ .tag = JET
, .jet = current_prev_outpoint
, .cmr = {{0x0877b36fu, 0x656c2489u, 0x13254415u, 0x92df56e2u, 0xbbecf24du, 0x0acd0b78u, 0xfc9438b7u, 0x773a9eb4u}}
, .sourceIx = ty_u
, .targetIx = ty_pw256w32
, .cost = 312 /* milli weight units */
}
,[CURRENT_REISSUANCE_BLINDING] =
{ .tag = JET
, .jet = current_reissuance_blinding
, .cmr = {{0xc8d3e808u, 0x87505aa7u, 0xf583ac6bu, 0xe47182ecu, 0xbc685cc3u, 0xc4a6acaau, 0x8e2c1329u, 0xe35d2930u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 148 /* milli weight units */
}
,[CURRENT_REISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = current_reissuance_entropy
, .cmr = {{0x4f241095u, 0x401ceea8u, 0x312d2f42u, 0xbeae8d88u, 0x0acfe189u, 0x33630d7bu, 0x8216c537u, 0x623e2af7u}}
, .sourceIx = ty_u
, .targetIx = ty_mw256
, .cost = 139 /* milli weight units */
}
,[CURRENT_SCRIPT_HASH] =
{ .tag = JET
, .jet = current_script_hash
, .cmr = {{0xcd5ea7fbu, 0x0910f76eu, 0x76c6ea68u, 0xd0e2cad1u, 0x34cbb642u, 0x823bc43cu, 0x0423852fu, 0x37b7e25au}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 305 /* milli weight units */
}
,[CURRENT_SCRIPT_SIG_HASH] =
{ .tag = JET
, .jet = current_script_sig_hash
, .cmr = {{0x17ad01cau, 0xe293427bu, 0xe2505af2u, 0xfe4c3e65u, 0x125fc3ddu, 0xe27a1143u, 0x788fa136u, 0x0f1c3751u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 298 /* milli weight units */
}
,[CURRENT_SEQUENCE] =
{ .tag = JET
, .jet = current_sequence
, .cmr = {{0x79ce41eeu, 0x05c97335u, 0xdc73515cu, 0x2934c91cu, 0x2e2dca6eu, 0x73c335eau, 0x4f43e0fau, 0x88de00f6u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 138 /* milli weight units */
}
,[DECOMPRESS] =
{ .tag = JET
, .jet = decompress
, .cmr = {{0xa43c3926u, 0x7facd1e2u, 0xb6d42c76u, 0x15ad3f28u, 0x68637572u, 0xf46e1879u, 0x4e3475b9u, 0xb2eaef84u}}
, .sourceIx = ty_pbw256
, .targetIx = ty_mw512
, .cost = 10956 /* milli weight units */
}
,[DECREMENT_16] =
{ .tag = JET
, .jet = decrement_16
, .cmr = {{0x196b2dc6u, 0x32e6c5d0u, 0x94ff9d34u, 0xa2092b80u, 0x5e4b94d0u, 0x36ba4826u, 0xacefed60u, 0x3a489dc7u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw16
, .cost = 116 /* milli weight units */
}
,[DECREMENT_32] =
{ .tag = JET
, .jet = decrement_32
, .cmr = {{0x29b31592u, 0x66e9f608u, 0x80884f6eu, 0xb2816f19u, 0xa207291cu, 0x829fd139u, 0xfb0d78a3u, 0x9e08d0c5u}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw32
, .cost = 159 /* milli weight units */
}
,[DECREMENT_64] =
{ .tag = JET
, .jet = decrement_64
, .cmr = {{0x67175a67u, 0x6dc1780au, 0x20faf5e5u, 0xaad582ecu, 0x797baea5u, 0x5f2905ecu, 0xad2aaa1au, 0xe76be943u}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw64
, .cost = 160 /* milli weight units */
}
,[DECREMENT_8] =
{ .tag = JET
, .jet = decrement_8
, .cmr = {{0x2b5911e6u, 0x67e696f9u, 0xcd03e9dfu, 0x7d400a55u, 0x45e7e974u, 0x4afbf92eu, 0x0ba87f6cu, 0x7cc44287u}}
, .sourceIx = ty_w8
, .targetIx = ty_pbw8
, .cost = 195 /* milli weight units */
}
,[DIV_MOD_128_64] =
{ .tag = JET
, .jet = div_mod_128_64
, .cmr = {{0x1ee3e60fu, 0x5c9e4f0du, 0x3ec9ebeau, 0x3698eca8u, 0xbd32ac16u, 0x7e69b296u, 0xab9c1836u, 0xb6101d04u}}
, .sourceIx = ty_pw128w64
, .targetIx = ty_w128
, .cost = 220 /* milli weight units */
}
,[DIV_MOD_16] =
{ .tag = JET
, .jet = div_mod_16
, .cmr = {{0x1585d1bfu, 0xe952f71bu, 0x1cfebbefu, 0x292ced56u, 0x60915723u, 0x05182720u, 0x625a1ac0u, 0x0881a489u}}
, .sourceIx = ty_w32
, .targetIx = ty_w32
, .cost = 223 /* milli weight units */
}
,[DIV_MOD_32] =
{ .tag = JET
, .jet = div_mod_32
, .cmr = {{0xbab7bc9au, 0x9f644edcu, 0xba73e330u, 0xc1a50543u, 0x67f5fb86u, 0x78c1236au, 0xb6e7f4d7u, 0x1860e002u}}
, .sourceIx = ty_w64
, .targetIx = ty_w64
, .cost = 198 /* milli weight units */
}
,[DIV_MOD_64] =
{ .tag = JET
, .jet = div_mod_64
, .cmr = {{0x8db4664du, 0x99e8c878u, 0xef31ebf1u, 0xaca6a876u, 0x4b58495du, 0xa0ecc032u, 0xb3c9b489u, 0xaaa0ff90u}}
, .sourceIx = ty_w128
, .targetIx = ty_w128
, .cost = 220 /* milli weight units */
}
,[DIV_MOD_8] =
{ .tag = JET
, .jet = div_mod_8
, .cmr = {{0x25f3694bu, 0x752e4df1u, 0xb0cc8c51u, 0xbf9917efu, 0x6e11c52eu, 0xa777353eu, 0x9507e819u, 0xa8066295u}}
, .sourceIx = ty_w16
, .targetIx = ty_w16
, .cost = 141 /* milli weight units */
}
,[DIVIDE_16] =
{ .tag = JET
, .jet = divide_16
, .cmr = {{0x2dc3e9a9u, 0xc61dc88du, 0xd744f16bu, 0xe1aed4b7u, 0x2ab47949u, 0x0e414226u, 0x58b97219u, 0xdf49957cu}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 188 /* milli weight units */
}
,[DIVIDE_32] =
{ .tag = JET
, .jet = divide_32
, .cmr = {{0xf6dcf4bdu, 0x8d9b5effu, 0x751e9b01u, 0x47a98e0fu, 0xc4c8872cu, 0x1ab782d1u, 0xebec6383u, 0xa09b780au}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 225 /* milli weight units */
}
,[DIVIDE_64] =
{ .tag = JET
, .jet = divide_64
, .cmr = {{0x8a94518bu, 0x9b76179au, 0x9d5c1e31u, 0x6e690062u, 0x7f5b6e3eu, 0xcc668fe2u, 0xd0c5d562u, 0x38e33ea3u}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 202 /* milli weight units */
}
,[DIVIDE_8] =
{ .tag = JET
, .jet = divide_8
, .cmr = {{0xd716000cu, 0xe7e57278u, 0x84a6d797u, 0x6a32c0f6u, 0xbdb881d0u, 0x0fe8dbb2u, 0x8dea3701u, 0x03769e2du}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 125 /* milli weight units */
}
,[DIVIDES_16] =
{ .tag = JET
, .jet = divides_16
, .cmr = {{0x8f4184a5u, 0x82674e00u, 0x3b37401bu, 0x13c9b8c3u, 0x7c683b88u, 0xdf633a22u, 0x719a23e1u, 0x94bda6f3u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 173 /* milli weight units */
}
,[DIVIDES_32] =
{ .tag = JET
, .jet = divides_32
, .cmr = {{0xe89ecdc3u, 0x7cd10466u, 0xb00f0137u, 0xe20b09b9u, 0xc5948d07u, 0x312d053fu, 0xed63c491u, 0xbb5c4c6au}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 175 /* milli weight units */
}
,[DIVIDES_64] =
{ .tag = JET
, .jet = divides_64
, .cmr = {{0xb43198d5u, 0x74419057u, 0xe76bc069u, 0xd7d3e2cbu, 0x04f7072bu, 0x80696d3du, 0xb92c8a72u, 0xc78a5cfcu}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 246 /* milli weight units */
}
,[DIVIDES_8] =
{ .tag = JET
, .jet = divides_8
, .cmr = {{0x3fc3b9b4u, 0x968e1674u, 0xda9ec457u, 0xb1ca8a66u, 0x29a37b4bu, 0xefdcd7ccu, 0x55886080u, 0xaef68af8u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 142 /* milli weight units */
}
,[EQ_1] =
{ .tag = JET
, .jet = eq_1
, .cmr = {{0x4249c5bdu, 0xec540a06u, 0x957dcdabu, 0x045a445eu, 0xb91891c0u, 0x6c3f8f96u, 0xc888e9ddu, 0xd2fbaa28u}}
, .sourceIx = ty_w2
, .targetIx = ty_b
, .cost = 120 /* milli weight units */
}
,[EQ_16] =
{ .tag = JET
, .jet = eq_16
, .cmr = {{0xab31a797u, 0x4acbf72au, 0xb2f21bf5u, 0x3fec346au, 0x28e6e65eu, 0x4c05e3e7u, 0x843e1473u, 0xb1fd3ff9u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 174 /* milli weight units */
}
,[EQ_256] =
{ .tag = JET
, .jet = eq_256
, .cmr = {{0xf7df29edu, 0x2d007822u, 0x7e719b7du, 0x1337dbeau, 0x3a710f58u, 0x4a4b07f0u, 0xf2654a44u, 0x6554f2beu}}
, .sourceIx = ty_w512
, .targetIx = ty_b
, .cost = 431 /* milli weight units */
}
,[EQ_32] =
{ .tag = JET
, .jet = eq_32
, .cmr = {{0x76791f0du, 0xddab9dc7u, 0x7a14a68cu, 0xc67787c9u, 0x84493faeu, 0xbbdbb6d6u, 0xd493352eu, 0x114720d5u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 233 /* milli weight units */
}
,[EQ_64] =
{ .tag = JET
, .jet = eq_64
, .cmr = {{0x011b5f4cu, 0xb31f34bau, 0x158a6822u, 0x3b34445eu, 0x93f3dc18u, 0x91b53390u, 0x04923dcfu, 0xabe034c1u}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 202 /* milli weight units */
}
,[EQ_8] =
{ .tag = JET
, .jet = eq_8
, .cmr = {{0x0f8b1fdeu, 0x1949bebdu, 0x47d2554au, 0x4807fd8du, 0xcaef8730u, 0x1838d60eu, 0x84c73814u, 0x42da7eceu}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 120 /* milli weight units */
}
,[FE_ADD] =
{ .tag = JET
, .jet = fe_add
, .cmr = {{0xa5e921d4u, 0xd2959af7u, 0x833df930u, 0x83689857u, 0x32ab0f33u, 0xbad8aa34u, 0x5b39f303u, 0x032be7aeu}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 908 /* milli weight units */
}
,[FE_INVERT] =
{ .tag = JET
, .jet = fe_invert
, .cmr = {{0x21f42956u, 0x9d78e09fu, 0xb29013efu, 0x8a16c755u, 0x0edc4e19u, 0x0525715au, 0xbfb0c19bu, 0x21cfd9c2u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 3375 /* milli weight units */
}
,[FE_IS_ODD] =
{ .tag = JET
, .jet = fe_is_odd
, .cmr = {{0x21d35d0au, 0x657f5defu, 0xacde6da3u, 0xfdb48d67u, 0x56f30690u, 0xb40270f0u, 0x1017e7e3u, 0x48d7585du}}
, .sourceIx = ty_w256
, .targetIx = ty_b
, .cost = 544 /* milli weight units */
}
,[FE_IS_ZERO] =
{ .tag = JET
, .jet = fe_is_zero
, .cmr = {{0xf5716282u, 0xba0d26bdu, 0x0671cdfeu, 0x1f118f45u, 0xbae79d10u, 0x9a6d9f39u, 0x7a4c4554u, 0x6f62af00u}}
, .sourceIx = ty_w256
, .targetIx = ty_b
, .cost = 521 /* milli weight units */
}
,[FE_MULTIPLY] =
{ .tag = JET
, .jet = fe_multiply
, .cmr = {{0xc176969cu, 0x337fbc6bu, 0x5ac8ed3eu, 0xa28ab3fdu, 0x94782064u, 0x3195d73bu, 0x862018f7u, 0x08487d23u}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 975 /* milli weight units */
}
,[FE_MULTIPLY_BETA] =
{ .tag = JET
, .jet = fe_multiply_beta
, .cmr = {{0xc0fc7666u, 0x8d99d407u, 0x3f399344u, 0x3a68980bu, 0xa96e9760u, 0x1ed1a919u, 0xc4a23305u, 0x7b66fe23u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 824 /* milli weight units */
}
,[FE_NEGATE] =
{ .tag = JET
, .jet = fe_negate
, .cmr = {{0xd6ef8fc2u, 0x275ddf70u, 0x58b5e499u, 0xf10dd284u, 0x66f57b72u, 0x53a54407u, 0x798a4772u, 0x592184b9u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 846 /* milli weight units */
}
,[FE_NORMALIZE] =
{ .tag = JET
, .jet = fe_normalize
, .cmr = {{0xf498bcdfu, 0xf3506788u, 0x1bd96ee1u, 0xc91f4367u, 0x1e79186eu, 0x700ec4dau, 0x2dc0296au, 0x2dea91c7u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 813 /* milli weight units */
}
,[FE_SQUARE] =
{ .tag = JET
, .jet = fe_square
, .cmr = {{0x168a11b1u, 0x9c0fb97fu, 0x1099f863u, 0xa4c8e2f8u, 0x12425fbdu, 0x3d01bdedu, 0x3f460cb3u, 0x59bfdd89u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 829 /* milli weight units */
}
,[FE_SQUARE_ROOT] =
{ .tag = JET
, .jet = fe_square_root
, .cmr = {{0x3b46cde3u, 0x0674b777u, 0x16f2c8f6u, 0x14adbd16u, 0x61985d82u, 0xc55304d5u, 0x6e53ef5cu, 0x74c83e83u}}
, .sourceIx = ty_w256
, .targetIx = ty_mw256
, .cost = 10698 /* milli weight units */
}
,[FULL_ADD_16] =
{ .tag = JET
, .jet = full_add_16
, .cmr = {{0xf454a632u, 0xfd1928cdu, 0x6f070df6u, 0x8014288eu, 0x97b3e582u, 0xe7f03e98u, 0xed3234b6u, 0x282d0294u}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw16
, .cost = 193 /* milli weight units */
}
,[FULL_ADD_32] =
{ .tag = JET
, .jet = full_add_32
, .cmr = {{0x9606b9e6u, 0x541e0356u, 0xed7608d5u, 0xbc6f9d4eu, 0xf68e0a3du, 0x235168d9u, 0xe75cae66u, 0x52dd0634u}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw32
, .cost = 197 /* milli weight units */
}
,[FULL_ADD_64] =
{ .tag = JET
, .jet = full_add_64
, .cmr = {{0xf0f79532u, 0x001c02afu, 0xac650a62u, 0x801932afu, 0xc2c1b286u, 0xa31fef7au, 0xe08a47eau, 0x1e71387du}}
, .sourceIx = ty_pbw128
, .targetIx = ty_pbw64
, .cost = 225 /* milli weight units */
}
,[FULL_ADD_8] =
{ .tag = JET
, .jet = full_add_8
, .cmr = {{0xcdd080fdu, 0x8612e7d1u, 0x4ada3491u, 0x64a6d5afu, 0x6054d673u, 0x77e17665u, 0xc4722040u, 0x28bc2125u}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw8
, .cost = 190 /* milli weight units */
}
,[FULL_DECREMENT_16] =
{ .tag = JET
, .jet = full_decrement_16
, .cmr = {{0xa7d1b9a6u, 0x09dcd367u, 0x66a167a3u, 0x7aa0e649u, 0xfbdd75f6u, 0x4691a9fbu, 0x6bf1663du, 0x329282a8u}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw16
, .cost = 107 /* milli weight units */
}
,[FULL_DECREMENT_32] =
{ .tag = JET
, .jet = full_decrement_32
, .cmr = {{0xcbcfd7cau, 0x7372b2b1u, 0x80008e51u, 0x589880d3u, 0xb5399bd9u, 0xa8ddb9bcu, 0xda6132c2u, 0x2c777e0fu}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw32
, .cost = 153 /* milli weight units */
}
,[FULL_DECREMENT_64] =
{ .tag = JET
, .jet = full_decrement_64
, .cmr = {{0x42df92d2u, 0xe7f42e57u, 0x9bd4c430u, 0x8cd2db6eu, 0x76774695u, 0xd6a56950u, 0xc5cf9203u, 0x002d41aau}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw64
, .cost = 151 /* milli weight units */
}
,[FULL_DECREMENT_8] =
{ .tag = JET
, .jet = full_decrement_8
, .cmr = {{0xff58dd01u, 0x62bce9fbu, 0x73ed015bu, 0x7e5d3d1du, 0xc11b505cu, 0x932d490cu, 0xaadc1b5du, 0x893d1fadu}}
, .sourceIx = ty_pbw8
, .targetIx = ty_pbw8
, .cost = 218 /* milli weight units */
}
,[FULL_INCREMENT_16] =
{ .tag = JET
, .jet = full_increment_16
, .cmr = {{0x5453608eu, 0xeff967afu, 0xef4ae583u, 0x1aa7a9fcu, 0x75c2ba57u, 0xe1ac412au, 0xb5464d4du, 0xe93af4f9u}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw16
, .cost = 108 /* milli weight units */
}
,[FULL_INCREMENT_32] =
{ .tag = JET
, .jet = full_increment_32
, .cmr = {{0x36323321u, 0x58f90ba4u, 0xdf623f08u, 0x6808d1d3u, 0x39f36d9au, 0x6f922723u, 0x3416f234u, 0xcdd25d98u}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw32
, .cost = 171 /* milli weight units */
}
,[FULL_INCREMENT_64] =
{ .tag = JET
, .jet = full_increment_64
, .cmr = {{0x0637fcc5u, 0x52f62a8au, 0x08c6d070u, 0x667ed80eu, 0x47ba707cu, 0x120c4d65u, 0x6604a343u, 0x3bfc40a6u}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw64
, .cost = 161 /* milli weight units */
}
,[FULL_INCREMENT_8] =
{ .tag = JET
, .jet = full_increment_8
, .cmr = {{0x291524e1u, 0x70d523fdu, 0x35c2577bu, 0x8ea3f447u, 0x8ec63206u, 0xc98fb5ccu, 0xcf77c209u, 0xbebd29efu}}
, .sourceIx = ty_pbw8
, .targetIx = ty_pbw8
, .cost = 204 /* milli weight units */
}
,[FULL_LEFT_SHIFT_16_1] =
{ .tag = JET
, .jet = full_left_shift_16_1
, .cmr = {{0x740e2381u, 0x1b3e62d4u, 0x91510fc9u, 0xedc4cb0au, 0x0eecfadfu, 0xd21bb27fu, 0x33e220b1u, 0xd87d14d7u}}
, .sourceIx = ty_pw16b
, .targetIx = ty_pbw16
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_16_2] =
{ .tag = JET
, .jet = full_left_shift_16_2
, .cmr = {{0xc26e8ac3u, 0xff9cc518u, 0x719d4d7fu, 0xd149d802u, 0xf23f0b02u, 0x4999ed5du, 0xaf369210u, 0xacbe3345u}}
, .sourceIx = ty_pw16w2
, .targetIx = ty_pw2w16
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_16_4] =
{ .tag = JET
, .jet = full_left_shift_16_4
, .cmr = {{0x5e570cbeu, 0x4c7ca94bu, 0xe0fc7b3eu, 0xe579bdd7u, 0x8426f0b7u, 0x67f48517u, 0x17bbfeaeu, 0xde91fe30u}}
, .sourceIx = ty_pw16w4
, .targetIx = ty_pw4w16
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_16_8] =
{ .tag = JET
, .jet = full_left_shift_16_8
, .cmr = {{0x65adc553u, 0x48383b28u, 0xe8797f81u, 0xa9282d91u, 0x1b3f8fa6u, 0x13927251u, 0xd88e0c38u, 0xb029b705u}}
, .sourceIx = ty_pw16w8
, .targetIx = ty_pw8w16
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_32_1] =
{ .tag = JET
, .jet = full_left_shift_32_1
, .cmr = {{0x72e0104eu, 0xfaf1dee4u, 0x1198ec3bu, 0x790373f6u, 0x48f13f5eu, 0xe06552fbu, 0x020bafb5u, 0x8497c25cu}}
, .sourceIx = ty_pw32b
, .targetIx = ty_pbw32
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_32_16] =
{ .tag = JET
, .jet = full_left_shift_32_16
, .cmr = {{0xb9fb2169u, 0x908d9144u, 0xcc73e68fu, 0x753536f4u, 0x3cb2b74cu, 0xb62c6408u, 0x810670deu, 0x84ab09bdu}}
, .sourceIx = ty_pw32w16
, .targetIx = ty_pw16w32
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_32_2] =
{ .tag = JET
, .jet = full_left_shift_32_2
, .cmr = {{0x11efdb81u, 0xb0c4dedau, 0x4d4f9847u, 0x5d7878efu, 0xa338694fu, 0xa0fd613eu, 0x1293225au, 0x4f462f7cu}}
, .sourceIx = ty_pw32w2
, .targetIx = ty_pw2w32
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_32_4] =
{ .tag = JET
, .jet = full_left_shift_32_4
, .cmr = {{0x77e399d7u, 0xd83f7d11u, 0x44991dafu, 0xa3cc9811u, 0xc1632c29u, 0xe493a8afu, 0x98e98fbcu, 0x1d635fb4u}}
, .sourceIx = ty_pw32w4
, .targetIx = ty_pw4w32
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_32_8] =
{ .tag = JET
, .jet = full_left_shift_32_8
, .cmr = {{0xba664cb1u, 0xc42eda17u, 0x9191ebc2u, 0xa110396du, 0xae58f906u, 0xa64106b3u, 0x0667790au, 0xc2f2382du}}
, .sourceIx = ty_pw32w8
, .targetIx = ty_pw8w32
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_64_1] =
{ .tag = JET
, .jet = full_left_shift_64_1
, .cmr = {{0x79d38fe0u, 0x75839b22u, 0x7cffd92au, 0x8cdb5c8cu, 0x3522bcb4u, 0xd1e03beeu, 0xb6db6ab6u, 0x4ed4721fu}}
, .sourceIx = ty_pw64b
, .targetIx = ty_pbw64
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_64_16] =
{ .tag = JET
, .jet = full_left_shift_64_16
, .cmr = {{0x21435662u, 0x45f5a1b9u, 0xdfeb0c75u, 0x878e21dbu, 0xe13804c2u, 0x6935ee47u, 0xcac9ad82u, 0x2d6dedb2u}}
, .sourceIx = ty_pw64w16
, .targetIx = ty_pw16w64
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_64_2] =
{ .tag = JET
, .jet = full_left_shift_64_2
, .cmr = {{0x9c921649u, 0x15af0b15u, 0x4e1df564u, 0xd4dc9be9u, 0x80b39883u, 0x5c9988bbu, 0xb108d0cdu, 0x8145b330u}}
, .sourceIx = ty_pw64w2
, .targetIx = ty_pw2w64
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_64_32] =
{ .tag = JET
, .jet = full_left_shift_64_32
, .cmr = {{0xd0d016e9u, 0xc78cd112u, 0xb4dd91a8u, 0x359f805cu, 0x68415b85u, 0x7a799b00u, 0x394954dcu, 0xd290acbcu}}
, .sourceIx = ty_pw64w32
, .targetIx = ty_pw32w64
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_64_4] =
{ .tag = JET
, .jet = full_left_shift_64_4
, .cmr = {{0x0f1f7d37u, 0x4e82868du, 0x71e7e7c0u, 0x3221b150u, 0x594b6304u, 0x45b1b163u, 0x56cf3545u, 0xbd939263u}}
, .sourceIx = ty_pw64w4
, .targetIx = ty_pw4w64
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_64_8] =
{ .tag = JET
, .jet = full_left_shift_64_8
, .cmr = {{0xad7b4438u, 0xb73f6f9eu, 0x42f64c70u, 0x530475eeu, 0x08936e47u, 0x63e5b73eu, 0xa4bc8383u, 0xa2b963d5u}}
, .sourceIx = ty_pw64w8
, .targetIx = ty_pw8w64
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_8_1] =
{ .tag = JET
, .jet = full_left_shift_8_1
, .cmr = {{0x2113681au, 0x11624e60u, 0x6030c470u, 0xd68f6061u, 0x232f71cfu, 0xabc50571u, 0x92c6c8bdu, 0x1d73b7e1u}}
, .sourceIx = ty_pw8b
, .targetIx = ty_pbw8
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_8_2] =
{ .tag = JET
, .jet = full_left_shift_8_2
, .cmr = {{0x368368c9u, 0x4b040e81u, 0xb948d737u, 0xc193c042u, 0x83ec80a2u, 0x8fd3a021u, 0xb0b8c1abu, 0xcf5edcd3u}}
, .sourceIx = ty_pw8w2
, .targetIx = ty_pw2w8
, .cost = 150 /* milli weight units */
}
,[FULL_LEFT_SHIFT_8_4] =
{ .tag = JET
, .jet = full_left_shift_8_4
, .cmr = {{0x8f854d58u, 0xf968b4beu, 0x3b2021fbu, 0x22142dd3u, 0xe68aa819u, 0x7b5475b7u, 0x050b02e1u, 0xe5caee47u}}
, .sourceIx = ty_pw8w4
, .targetIx = ty_pw4w8
, .cost = 150 /* milli weight units */
}
,[FULL_MULTIPLY_16] =
{ .tag = JET
, .jet = full_multiply_16
, .cmr = {{0x32cf7f50u, 0x894ea2c4u, 0x61a05466u, 0xbbfa1e4eu, 0x1b049957u, 0x523f6493u, 0x7a8b5427u, 0x3dd31b37u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 208 /* milli weight units */
}
,[FULL_MULTIPLY_32] =
{ .tag = JET
, .jet = full_multiply_32
, .cmr = {{0xdea1afc6u, 0xfd546c75u, 0xe0b2d8e4u, 0x18f26179u, 0xd6dbe905u, 0x8b079aa9u, 0xab80eaa6u, 0xc05f39cbu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 213 /* milli weight units */
}
,[FULL_MULTIPLY_64] =
{ .tag = JET
, .jet = full_multiply_64
, .cmr = {{0x813d74d6u, 0xc3064cf7u, 0xc5db2ddau, 0x964ed0e2u, 0xd5a2491bu, 0x89432921u, 0x9237cb1au, 0x91ee0934u}}
, .sourceIx = ty_w256
, .targetIx = ty_w128
, .cost = 209 /* milli weight units */
}
,[FULL_MULTIPLY_8] =
{ .tag = JET
, .jet = full_multiply_8
, .cmr = {{0xf7f39d95u, 0xdab57308u, 0x52e9cc7eu, 0x74c0743bu, 0x8fb3f754u, 0x87120ba3u, 0x26ff600au, 0xd8b1f3e6u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 190 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_16_1] =
{ .tag = JET
, .jet = full_right_shift_16_1
, .cmr = {{0xb8074423u, 0xe6748a6au, 0xa54ec574u, 0x1feef25au, 0x262fdecbu, 0xfce39124u, 0xe610238au, 0x3b0a23fcu}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pw16b
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_16_2] =
{ .tag = JET
, .jet = full_right_shift_16_2
, .cmr = {{0x3fcf985eu, 0xe0c72ca4u, 0x1ddf6c89u, 0xd0f0f69du, 0x5065876eu, 0x3b6020ecu, 0xc9bf059eu, 0x8f9719c6u}}
, .sourceIx = ty_pw2w16
, .targetIx = ty_pw16w2
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_16_4] =
{ .tag = JET
, .jet = full_right_shift_16_4
, .cmr = {{0xa30c7c29u, 0xd0eeac29u, 0x5258b2b6u, 0x1d0b5413u, 0x46f407c0u, 0x848d448eu, 0x13e9774cu, 0x1c969679u}}
, .sourceIx = ty_pw4w16
, .targetIx = ty_pw16w4
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_16_8] =
{ .tag = JET
, .jet = full_right_shift_16_8
, .cmr = {{0x5b8808cau, 0xda5587b3u, 0x6d1a6fadu, 0x66ae4da0u, 0x8d412364u, 0x4c0bdd59u, 0x772a70aau, 0x7432e715u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_pw16w8
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_32_1] =
{ .tag = JET
, .jet = full_right_shift_32_1
, .cmr = {{0x32afd0efu, 0x94df51b7u, 0xd35c00e5u, 0x61a8390cu, 0x5cf50f93u, 0x0b30d786u, 0x8804b580u, 0x49375840u}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pw32b
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_32_16] =
{ .tag = JET
, .jet = full_right_shift_32_16
, .cmr = {{0x44d179a8u, 0x90f7812fu, 0x151331b5u, 0x5fc07eb4u, 0xe4d7814eu, 0xb683da28u, 0x8f8fe7cdu, 0x55b43906u}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_pw32w16
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_32_2] =
{ .tag = JET
, .jet = full_right_shift_32_2
, .cmr = {{0x33c661dfu, 0x3a32cae5u, 0x5b52a5f2u, 0x632154ccu, 0x85b65913u, 0x87bc2b34u, 0x8330c870u, 0xa6f6706fu}}
, .sourceIx = ty_pw2w32
, .targetIx = ty_pw32w2
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_32_4] =
{ .tag = JET
, .jet = full_right_shift_32_4
, .cmr = {{0xe4bebf16u, 0x935f67beu, 0x7d8c86bcu, 0x588adbcfu, 0x8e597539u, 0x257fddabu, 0x9fb04372u, 0xc77012d3u}}
, .sourceIx = ty_pw4w32
, .targetIx = ty_pw32w4
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_32_8] =
{ .tag = JET
, .jet = full_right_shift_32_8
, .cmr = {{0xabcffb08u, 0x4a239642u, 0x16d56273u, 0x305c0c8bu, 0x03bdabdau, 0xd69ff7e9u, 0x42f0d2cfu, 0x080febccu}}
, .sourceIx = ty_pw8w32
, .targetIx = ty_pw32w8
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_64_1] =
{ .tag = JET
, .jet = full_right_shift_64_1
, .cmr = {{0x37688260u, 0xc53af06bu, 0x856d9022u, 0xca5d87f8u, 0xa687ee53u, 0xfaca1866u, 0xec842a7cu, 0x890a4b70u}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pw64b
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_64_16] =
{ .tag = JET
, .jet = full_right_shift_64_16
, .cmr = {{0x417bfb71u, 0x5a20b10du, 0x4881f5c3u, 0x496c63efu, 0xee4ab500u, 0x3dfd0a16u, 0xb85f94f8u, 0xe5b0667cu}}
, .sourceIx = ty_pw16w64
, .targetIx = ty_pw64w16
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_64_2] =
{ .tag = JET
, .jet = full_right_shift_64_2
, .cmr = {{0xceca2567u, 0xb91a63e9u, 0xca44035eu, 0xb59e2f22u, 0xd81e37e1u, 0x96595a74u, 0x8cea4a46u, 0x84a215b0u}}
, .sourceIx = ty_pw2w64
, .targetIx = ty_pw64w2
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_64_32] =
{ .tag = JET
, .jet = full_right_shift_64_32
, .cmr = {{0x03969937u, 0x84023d47u, 0xe8514b45u, 0x9298198du, 0x33bd71e6u, 0xf756d08eu, 0xdf462a8fu, 0x62a21b80u}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_pw64w32
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_64_4] =
{ .tag = JET
, .jet = full_right_shift_64_4
, .cmr = {{0xdee4dad6u, 0x7a5ddcc3u, 0x5da1a790u, 0x63ca975fu, 0x8134c8eau, 0xc56a9f55u, 0x5d2b0e13u, 0xda10994du}}
, .sourceIx = ty_pw4w64
, .targetIx = ty_pw64w4
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_64_8] =
{ .tag = JET
, .jet = full_right_shift_64_8
, .cmr = {{0x9cd77803u, 0xfc389c94u, 0xfff286dau, 0x0b374b89u, 0xfeeb3daau, 0x38ce67cau, 0xb0220dabu, 0xeefe23a2u}}
, .sourceIx = ty_pw8w64
, .targetIx = ty_pw64w8
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_8_1] =
{ .tag = JET
, .jet = full_right_shift_8_1
, .cmr = {{0xee23fff0u, 0x7de53cc3u, 0x7109a47fu, 0x9fde3c74u, 0x447ae831u, 0xcee9ac4du, 0xb790cde8u, 0xb15323b2u}}
, .sourceIx = ty_pbw8
, .targetIx = ty_pw8b
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_8_2] =
{ .tag = JET
, .jet = full_right_shift_8_2
, .cmr = {{0x25e1dea1u, 0x08c5f89cu, 0xce5b3d5bu, 0x0e0792beu, 0x37901a5au, 0x65def904u, 0xdd51710au, 0x355ab55fu}}
, .sourceIx = ty_pw2w8
, .targetIx = ty_pw8w2
, .cost = 150 /* milli weight units */
}
,[FULL_RIGHT_SHIFT_8_4] =
{ .tag = JET
, .jet = full_right_shift_8_4
, .cmr = {{0xd7f0a83cu, 0x4104543eu, 0xc75b5ee7u, 0x5bf5f791u, 0x5d65fa50u, 0xc2095de2u, 0xa35670a5u, 0x05be129au}}
, .sourceIx = ty_pw4w8
, .targetIx = ty_pw8w4
, .cost = 150 /* milli weight units */
}
,[FULL_SUBTRACT_16] =
{ .tag = JET
, .jet = full_subtract_16
, .cmr = {{0x95ea5e54u, 0xc5603f2fu, 0x78acf6b8u, 0xa87a63b3u, 0xacc7b65fu, 0x2b87b690u, 0x4b9830fau, 0x91212c8cu}}
, .sourceIx = ty_pbw32
, .targetIx = ty_pbw16
, .cost = 201 /* milli weight units */
}
,[FULL_SUBTRACT_32] =
{ .tag = JET
, .jet = full_subtract_32
, .cmr = {{0x32963526u, 0xfc6089f5u, 0xec7da584u, 0xfbee3237u, 0x631c9b12u, 0x81f6f446u, 0xd99c9b50u, 0xc80c76dbu}}
, .sourceIx = ty_pbw64
, .targetIx = ty_pbw32
, .cost = 170 /* milli weight units */
}
,[FULL_SUBTRACT_64] =
{ .tag = JET
, .jet = full_subtract_64
, .cmr = {{0x15d48a43u, 0x2479b451u, 0xa6e2c18fu, 0x43fb0dfcu, 0x9aeb6fceu, 0x04035027u, 0xb033aa99u, 0xfb143447u}}
, .sourceIx = ty_pbw128
, .targetIx = ty_pbw64
, .cost = 231 /* milli weight units */
}
,[FULL_SUBTRACT_8] =
{ .tag = JET
, .jet = full_subtract_8
, .cmr = {{0x2bd4f0b3u, 0xa0a758acu, 0x39f1581bu, 0x2c34d7f4u, 0x14db4d8eu, 0x1bc119d7u, 0xf8929135u, 0x480e9affu}}
, .sourceIx = ty_pbw16
, .targetIx = ty_pbw8
, .cost = 141 /* milli weight units */
}
,[GE_IS_ON_CURVE] =
{ .tag = JET
, .jet = ge_is_on_curve
, .cmr = {{0x0572aef3u, 0x6300508cu, 0x96eda4a4u, 0xfec8579du, 0x8d8a43bdu, 0x540cb6ddu, 0xecc82a49u, 0xe668f7deu}}
, .sourceIx = ty_w512
, .targetIx = ty_b
, .cost = 763 /* milli weight units */
}
,[GE_NEGATE] =
{ .tag = JET
, .jet = ge_negate
, .cmr = {{0x90f33d91u, 0x0f858f9bu, 0x3b840ddbu, 0xc03d8a39u, 0xaf810214u, 0x853bad3cu, 0x905f1829u, 0x6fdfcb58u}}
, .sourceIx = ty_w512
, .targetIx = ty_w512
, .cost = 1278 /* milli weight units */
}
,[GEJ_ADD] =
{ .tag = JET
, .jet = gej_add
, .cmr = {{0x00871c07u, 0x66286a50u, 0x0acea05fu, 0x7a1fd98cu, 0x3e5246c1u, 0x946771e4u, 0x738e7582u, 0x091cca0du}}
, .sourceIx = ty_ppw512w256pw512w256
, .targetIx = ty_pw512w256
, .cost = 3292 /* milli weight units */
}
,[GEJ_DOUBLE] =
{ .tag = JET
, .jet = gej_double
, .cmr = {{0x5fc480c5u, 0x05b67dddu, 0xb9ce84b0u, 0xa8ee5a7eu, 0x4ef0e936u, 0x59d44521u, 0xe6a664acu, 0x5d6556f8u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_pw512w256
, .cost = 2103 /* milli weight units */
}
,[GEJ_EQUIV] =
{ .tag = JET
, .jet = gej_equiv
, .cmr = {{0xe87f98d9u, 0x1d9ebdecu, 0x167aba00u, 0xf8e8fc6du, 0xab8079c7u, 0x6b4d9c3du, 0x88f1f84cu, 0x8e6cd274u}}
, .sourceIx = ty_ppw512w256pw512w256
, .targetIx = ty_b
, .cost = 1270 /* milli weight units */
}
,[GEJ_GE_ADD] =
{ .tag = JET
, .jet = gej_ge_add
, .cmr = {{0xa24d049fu, 0xf1e4cf37u, 0x84c1b7d6u, 0xd1ba09fdu, 0x17fecfebu, 0x5580eab5u, 0xf11e8f8eu, 0xb9d9adefu}}
, .sourceIx = ty_ppw512w256w512
, .targetIx = ty_pw512w256
, .cost = 2890 /* milli weight units */
}
,[GEJ_GE_ADD_EX] =
{ .tag = JET
, .jet = gej_ge_add_ex
, .cmr = {{0x1e0e26d0u, 0xb29ae63du, 0x41e6767eu, 0x016e7e24u, 0x86e4f5d8u, 0xdc2cf665u, 0x02220316u, 0x40f1733au}}
, .sourceIx = ty_ppw512w256w512
, .targetIx = ty_pw256pw512w256
, .cost = 3114 /* milli weight units */
}
,[GEJ_GE_EQUIV] =
{ .tag = JET
, .jet = gej_ge_equiv
, .cmr = {{0x3b51dacdu, 0x29ff5cd3u, 0xc320455fu, 0xc3fa1ae9u, 0x612129aau, 0x8c8e2374u, 0x60c3ca2au, 0xd54e8f58u}}
, .sourceIx = ty_ppw512w256w512
, .targetIx = ty_b
, .cost = 1270 /* milli weight units */
}
,[GEJ_INFINITY] =
{ .tag = JET
, .jet = gej_infinity
, .cmr = {{0x88d4642cu, 0xfc2b52d0u, 0x90ce6e89u, 0x5c20da2eu, 0xfb0df6feu, 0x84f22722u, 0xbc46111cu, 0xc6be5cdau}}
, .sourceIx = ty_u
, .targetIx = ty_pw512w256
, .cost = 971 /* milli weight units */
}
,[GEJ_IS_INFINITY] =
{ .tag = JET
, .jet = gej_is_infinity
, .cmr = {{0x80f528e5u, 0xd85672dcu, 0x8d9c264fu, 0x67c7b727u, 0x00faad89u, 0x972a7e1du, 0x27d049c9u, 0x474b6cd9u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
, .cost = 923 /* milli weight units */
}
,[GEJ_IS_ON_CURVE] =
{ .tag = JET
, .jet = gej_is_on_curve
, .cmr = {{0x70ce4ffcu, 0xe2497cc6u, 0x2f170c57u, 0x14ff2cfeu, 0xce90b4cbu, 0x89a6a22fu, 0xac26b1b5u, 0xc66faa10u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
, .cost = 1106 /* milli weight units */
}
,[GEJ_NEGATE] =
{ .tag = JET
, .jet = gej_negate
, .cmr = {{0xad53f179u, 0x3fe07b8du, 0x672d9f7bu, 0x0741e9edu, 0x61557effu, 0x5b7296c5u, 0x68e09b3du, 0x19cf7124u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_pw512w256
, .cost = 1823 /* milli weight units */
}
,[GEJ_NORMALIZE] =
{ .tag = JET
, .jet = gej_normalize
, .cmr = {{0x0333df98u, 0xa8060c93u, 0x15c5fdb8u, 0x3ebffe34u, 0x07bf9c33u, 0x6bf4bb92u, 0x2df58588u, 0x7e1acdc7u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_mw512
, .cost = 4337 /* milli weight units */
}
,[GEJ_RESCALE] =
{ .tag = JET
, .jet = gej_rescale
, .cmr = {{0xf00ad18fu, 0xb4928cfau, 0xd02c5b9du, 0x8b6fd4b0u, 0x5d7cb549u, 0xee65984du, 0x022a6df9u, 0x8712b6d9u}}
, .sourceIx = ty_ppw512w256w256
, .targetIx = ty_pw512w256
, .cost = 2315 /* milli weight units */
}
,[GEJ_X_EQUIV] =
{ .tag = JET
, .jet = gej_x_equiv
, .cmr = {{0xe31c0f2cu, 0x5d08139bu, 0x4feb0985u, 0x2c06b6aau, 0x00b1d13eu, 0x62babd99u, 0x828212dcu, 0xff82217cu}}
, .sourceIx = ty_pw256pw512w256
, .targetIx = ty_b
, .cost = 1270 /* milli weight units */
}
,[GEJ_Y_IS_ODD] =
{ .tag = JET
, .jet = gej_y_is_odd
, .cmr = {{0xe34c867du, 0xe16b2f65u, 0x6109a738u, 0x72b0b5bau, 0x55ca3c2du, 0xbea9c2c6u, 0xe4cb19adu, 0x18c06f56u}}
, .sourceIx = ty_pw512w256
, .targetIx = ty_b
, .cost = 3665 /* milli weight units */
}
,[GENERATE] =
{ .tag = JET
, .jet = generate
, .cmr = {{0xa3c55befu, 0x32a350d9u, 0x0d5c3dacu, 0x24767a03u, 0x867faf7au, 0x73277703u, 0x895a27cbu, 0x6b44252du}}
, .sourceIx = ty_w256
, .targetIx = ty_pw512w256
, .cost = 51706 /* milli weight units */
}
,[GENESIS_BLOCK_HASH] =
{ .tag = JET
, .jet = genesis_block_hash
, .cmr = {{0x336ff73du, 0x002f3754u, 0x9c481fd4u, 0xaaf15a58u, 0x60779df2u, 0x83344871u, 0x41f409b4u, 0xb29efb65u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 395 /* milli weight units */
}
,[HASH_TO_CURVE] =
{ .tag = JET
, .jet = hash_to_curve
, .cmr = {{0x4dc3eb6au, 0x6fbe374bu, 0xa7696472u, 0x63a695a4u, 0x5d092113u, 0x8a17f003u, 0xc4abb758u, 0xd838b133u}}
, .sourceIx = ty_w256
, .targetIx = ty_w512
, .cost = 10956 /* milli weight units */
}
,[HIGH_1] =
{ .tag = JET
, .jet = high_1
, .cmr = {{0x97a143f0u, 0x4cb603f6u, 0x5f84a80du, 0x31c3364fu, 0x8fda2297u, 0x3a9ae695u, 0xa58189c3u, 0x1463a8bfu}}
, .sourceIx = ty_u
, .targetIx = ty_b
, .cost = 169 /* milli weight units */
}
,[HIGH_16] =
{ .tag = JET
, .jet = high_16
, .cmr = {{0x6210ac71u, 0x36586c73u, 0xa09c9421u, 0xa40e308cu, 0x4491eaceu, 0x9b5b3695u, 0xd61f4c81u, 0x96a69dc8u}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 159 /* milli weight units */
}
,[HIGH_32] =
{ .tag = JET
, .jet = high_32
, .cmr = {{0x719424b1u, 0xacd35b13u, 0x73580690u, 0xa7ec0b8fu, 0xb486145cu, 0x9cde728du, 0xa7984693u, 0xe95fc7c0u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 121 /* milli weight units */
}
,[HIGH_64] =
{ .tag = JET
, .jet = high_64
, .cmr = {{0x8c5d4409u, 0x34dfdcf2u, 0x75a21cf0u, 0x87ac127du, 0xa75715b5u, 0xdac9c693u, 0xc2afd7c7u, 0x18dc0ffbu}}
, .sourceIx = ty_u
, .targetIx = ty_w64
, .cost = 110 /* milli weight units */
}
,[HIGH_8] =
{ .tag = JET
, .jet = high_8
, .cmr = {{0x3a5ce00eu, 0x15e31808u, 0x51c20021u, 0x1f1c82dau, 0xa33ec876u, 0x38248a4bu, 0xf113407cu, 0x6b16ac4fu}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 169 /* milli weight units */
}
,[INCREMENT_16] =
{ .tag = JET
, .jet = increment_16
, .cmr = {{0x80f6cbbcu, 0x09b78ceau, 0x76c81390u, 0xd3ed989bu, 0x70e43916u, 0x1effaf9au, 0x62c64b1bu, 0x959cd030u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw16
, .cost = 129 /* milli weight units */
}
,[INCREMENT_32] =
{ .tag = JET
, .jet = increment_32
, .cmr = {{0x5a963ca4u, 0xada6619au, 0x805346e8u, 0x099503e4u, 0x7825be5cu, 0xf3c9a89bu, 0xfdbe2f19u, 0x1c32a2e0u}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw32
, .cost = 195 /* milli weight units */
}
,[INCREMENT_64] =
{ .tag = JET
, .jet = increment_64
, .cmr = {{0x86575236u, 0x83c2a05cu, 0x0e0998cdu, 0xa7b94e8bu, 0x0365ee83u, 0x22a14c5au, 0x3722b515u, 0xbb681f74u}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw64
, .cost = 187 /* milli weight units */
}
,[INCREMENT_8] =
{ .tag = JET
, .jet = increment_8
, .cmr = {{0xd1db8a9eu, 0xced17e21u, 0x996526bcu, 0x73be8e57u, 0x98688da3u, 0xc2ef8b8du, 0x5ba255d1u, 0x1ed8183eu}}
, .sourceIx = ty_w8
, .targetIx = ty_pbw8
, .cost = 155 /* milli weight units */
}
,[INPUT_AMOUNT] =
{ .tag = JET
, .jet = input_amount
, .cmr = {{0xbe740f91u, 0xe4d7b4b7u, 0xe62cd14au, 0x61cc00a2u, 0x4c3a1fb7u, 0x6c62f77bu, 0x9c1f92a2u, 0x77f55ff0u}}
, .sourceIx = ty_w32
, .targetIx = ty_mpspbw256w256spbw256w64
, .cost = 359 /* milli weight units */
}
,[INPUT_AMOUNTS_HASH] =
{ .tag = JET
, .jet = input_amounts_hash
, .cmr = {{0x5a06d0b9u, 0xf11a19fdu, 0x32e83e9du, 0x28111bd2u, 0x5f46528bu, 0x65404504u, 0xc4c6e68eu, 0x645bb04eu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 280 /* milli weight units */
}
,[INPUT_ANNEX_HASH] =
{ .tag = JET
, .jet = input_annex_hash
, .cmr = {{0x21769e4fu, 0x92825d7au, 0x82155e10u, 0x2e10605au, 0x8285530fu, 0xfdf75baau, 0x2a8cded3u, 0x628db316u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 122 /* milli weight units */
}
,[INPUT_ANNEXES_HASH] =
{ .tag = JET
, .jet = input_annexes_hash
, .cmr = {{0x260dc71du, 0x414eb859u, 0xc4a2cb33u, 0xca7406cfu, 0x067bc3c2u, 0x1c339903u, 0x5febafd4u, 0x0e9029c9u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 290 /* milli weight units */
}
,[INPUT_ASSET] =
{ .tag = JET
, .jet = input_asset
, .cmr = {{0x6072d81bu, 0x12015ab2u, 0x97efa1e8u, 0xa7713804u, 0x26ef0a12u, 0xf90d61e1u, 0xd419d082u, 0xe67b7565u}}
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w256
, .cost = 220 /* milli weight units */
}
,[INPUT_HASH] =
{ .tag = JET
, .jet = input_hash
, .cmr = {{0xb5d0d777u, 0x851e89d1u, 0x41d3cda1u, 0xb0f251e9u, 0xc31011d1u, 0xb01c2939u, 0x77119662u, 0xc349959eu}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 289 /* milli weight units */
}
,[INPUT_OUTPOINTS_HASH] =
{ .tag = JET
, .jet = input_outpoints_hash
, .cmr = {{0xdad26093u, 0x0c5f4d23u, 0x8d83565au, 0x6757e147u, 0x0030cb29u, 0xe0fd1e18u, 0xfc46edf3u, 0x1e650557u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 408 /* milli weight units */
}
,[INPUT_PEGIN] =
{ .tag = JET
, .jet = input_pegin
, .cmr = {{0x98f0575au, 0x0a978d26u, 0x626b79c8u, 0x424b4a5du, 0x16d94244u, 0xca606c8au, 0x63bee7e4u, 0xb0509122u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 235 /* milli weight units */
}
,[INPUT_PREV_OUTPOINT] =
{ .tag = JET
, .jet = input_prev_outpoint
, .cmr = {{0x7ad26d34u, 0x37c5aebau, 0x3b3d6b54u, 0x128d4d5eu, 0x9b99e9edu, 0x50fe7e07u, 0x674cc734u, 0x8055d895u}}
, .sourceIx = ty_w32
, .targetIx = ty_mpw256w32
, .cost = 326 /* milli weight units */
}
,[INPUT_SCRIPT_HASH] =
{ .tag = JET
, .jet = input_script_hash
, .cmr = {{0xa004c23cu, 0x28e3c938u, 0x9c2a7de1u, 0xf5091364u, 0x3a7ec259u, 0x77a31bd9u, 0x12e148d6u, 0x7b82b6dau}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 285 /* milli weight units */
}
,[INPUT_SCRIPT_SIG_HASH] =
{ .tag = JET
, .jet = input_script_sig_hash
, .cmr = {{0x25a59e2au, 0xed6be14cu, 0xc0b08f91u, 0xf81ce371u, 0xe396fe38u, 0xd719c33du, 0x38502866u, 0x8ae2eb87u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 231 /* milli weight units */
}
,[INPUT_SCRIPT_SIGS_HASH] =
{ .tag = JET
, .jet = input_script_sigs_hash
, .cmr = {{0xc47dc33eu, 0x1f780263u, 0x4928f1f5u, 0xd638558bu, 0x8f417eb2u, 0xbff69f54u, 0x2e8ceb98u, 0xbe1f02cdu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 283 /* milli weight units */
}
,[INPUT_SCRIPTS_HASH] =
{ .tag = JET
, .jet = input_scripts_hash
, .cmr = {{0xcfa056e1u, 0x249e8eb1u, 0xcdb7fee1u, 0x2383efa6u, 0x62028e7au, 0xdfcefa4fu, 0x8aa519f6u, 0x51cab9beu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 280 /* milli weight units */
}
,[INPUT_SEQUENCE] =
{ .tag = JET
, .jet = input_sequence
, .cmr = {{0x9f7a6694u, 0xe5991343u, 0x57c5ee0bu, 0x1ee6d0aeu, 0x5f954d5cu, 0xd1b10e09u, 0x20197a33u, 0xec877a4cu}}
, .sourceIx = ty_w32
, .targetIx = ty_mw32
, .cost = 144 /* milli weight units */
}
,[INPUT_SEQUENCES_HASH] =
{ .tag = JET
, .jet = input_sequences_hash
, .cmr = {{0x4b8b17e2u, 0x5e918156u, 0xd5625586u, 0x019aa0f7u, 0x6b79a53au, 0x24495de3u, 0xe39c48bbu, 0x03722edau}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 292 /* milli weight units */
}
,[INPUT_UTXO_HASH] =
{ .tag = JET
, .jet = input_utxo_hash
, .cmr = {{0xd6453aeeu, 0xb2b18b4cu, 0x1bb02b33u, 0x51ce5135u, 0x45cb7f10u, 0x62f2a3fau, 0xc680d0bbu, 0xcac63e86u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 409 /* milli weight units */
}
,[INPUT_UTXOS_HASH] =
{ .tag = JET
, .jet = input_utxos_hash
, .cmr = {{0xde24825fu, 0xdb9d56dau, 0x3638bd48u, 0x0005c3dbu, 0x574fdf11u, 0xc15303b2u, 0x42e29bdbu, 0xc51df389u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 409 /* milli weight units */
}
,[INPUTS_HASH] =
{ .tag = JET
, .jet = inputs_hash
, .cmr = {{0x5678275eu, 0xde8721f1u, 0xabda5cb4u, 0x60b30238u, 0x11d23e47u, 0xcc1f11c1u, 0xf4458035u, 0xcdc3d7ecu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 289 /* milli weight units */
}
,[INTERNAL_KEY] =
{ .tag = JET
, .jet = internal_key
, .cmr = {{0x6e048732u, 0x5df1ac05u, 0xd2d7decbu, 0xee3fc1f5u, 0xd63df047u, 0xf69c22b4u, 0xd93bc47cu, 0xbab44941u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 272 /* milli weight units */
}
,[IS_ONE_16] =
{ .tag = JET
, .jet = is_one_16
, .cmr = {{0x877cd001u, 0xd5e7b74eu, 0xdd1a4a5cu, 0x965641d4u, 0xfb53682du, 0x7fefae50u, 0xb5141218u, 0xc04be5afu}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 117 /* milli weight units */
}
,[IS_ONE_32] =
{ .tag = JET
, .jet = is_one_32
, .cmr = {{0x83354e97u, 0xd614600au, 0x49894ec2u, 0xc9d1980fu, 0x9c4c928cu, 0x1561eecau, 0xc99c1681u, 0x9c2b0791u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 136 /* milli weight units */
}
,[IS_ONE_64] =
{ .tag = JET
, .jet = is_one_64
, .cmr = {{0xb355f602u, 0xec76c4c4u, 0xce707720u, 0xfd543432u, 0x22a7c8cfu, 0xca439451u, 0xf23f9854u, 0x395078bau}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 163 /* milli weight units */
}
,[IS_ONE_8] =
{ .tag = JET
, .jet = is_one_8
, .cmr = {{0xf2459cf3u, 0x5b972029u, 0xfbb22e82u, 0x191ace11u, 0x732b1e08u, 0x346e21cfu, 0x0d305b41u, 0xfae87990u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 160 /* milli weight units */
}
,[IS_ZERO_16] =
{ .tag = JET
, .jet = is_zero_16
, .cmr = {{0x6ed03325u, 0x6fe645b5u, 0xec3f5950u, 0x8c60192au, 0xc8763008u, 0x915c8115u, 0xe929330cu, 0x0fcd4838u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 143 /* milli weight units */
}
,[IS_ZERO_32] =
{ .tag = JET
, .jet = is_zero_32
, .cmr = {{0x1af358a0u, 0x6be93ac6u, 0xf37cbb7du, 0x254d7bf9u, 0xd7187738u, 0xbaf1f25du, 0x0b67c9ffu, 0xe00f6a62u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 135 /* milli weight units */
}
,[IS_ZERO_64] =
{ .tag = JET
, .jet = is_zero_64
, .cmr = {{0xc1100cfcu, 0x16203ca4u, 0x44f16082u, 0x645b724du, 0x3ecd23dfu, 0x5d0ccf91u, 0xf35c5d9bu, 0x5a02a2f2u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 136 /* milli weight units */
}
,[IS_ZERO_8] =
{ .tag = JET
, .jet = is_zero_8
, .cmr = {{0x4d58680du, 0x8e1e8618u, 0xc43ce525u, 0xf78661a3u, 0x01486758u, 0x61a612d1u, 0xbfcfe3bbu, 0x5fa4ca95u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 163 /* milli weight units */
}
,[ISSUANCE] =
{ .tag = JET
, .jet = issuance
, .cmr = {{0x1dd033d3u, 0x2cd8e890u, 0x2f5ecb18u, 0x3385ec2bu, 0x0c27da38u, 0xae8e7b59u, 0x3f68f9b1u, 0xa4e62051u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmb
, .cost = 116 /* milli weight units */
}
,[ISSUANCE_ASSET] =
{ .tag = JET
, .jet = issuance_asset
, .cmr = {{0x7a3699d0u, 0x71030b58u, 0xd9f41ae1u, 0x1c637bacu, 0x977849f6u, 0x9a0487b1u, 0x9d2336d1u, 0xa7c6b705u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 241 /* milli weight units */
}
,[ISSUANCE_ASSET_AMOUNT] =
{ .tag = JET
, .jet = issuance_asset_amount
, .cmr = {{0x75bd9955u, 0x9c022dbfu, 0x5d5cf951u, 0xcb33ea37u, 0x05058bf8u, 0x1fbc74d5u, 0x9bbfba9eu, 0x37a1be0du}}
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
, .cost = 261 /* milli weight units */
}
,[ISSUANCE_ASSET_AMOUNTS_HASH] =
{ .tag = JET
, .jet = issuance_asset_amounts_hash
, .cmr = {{0x8c090d1au, 0x32b32b27u, 0x1fa376a3u, 0xba303616u, 0x8c0f62f9u, 0xa446ace2u, 0x9b3545c9u, 0xe51f3e47u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 276 /* milli weight units */
}
,[ISSUANCE_ASSET_PROOF] =
{ .tag = JET
, .jet = issuance_asset_proof
, .cmr = {{0xc0482071u, 0x1dc25ab0u, 0x61da6de8u, 0x32788d6du, 0xbfb54cfeu, 0xeafddb7eu, 0x1eae6085u, 0x0a766ee9u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 229 /* milli weight units */
}
,[ISSUANCE_BLINDING_ENTROPY_HASH] =
{ .tag = JET
, .jet = issuance_blinding_entropy_hash
, .cmr = {{0x3c429fa6u, 0x28e12ccfu, 0x9f167a07u, 0xe26f70afu, 0x36cb3459u, 0x964dbc14u, 0x2b524d40u, 0x9db1699bu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 278 /* milli weight units */
}
,[ISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = issuance_entropy
, .cmr = {{0x61f31455u, 0xd9982801u, 0x25df98e5u, 0x983d72f5u, 0xfbfdd65cu, 0x6369a0e7u, 0x8d07702fu, 0x28e2ff5eu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 437 /* milli weight units */
}
,[ISSUANCE_HASH] =
{ .tag = JET
, .jet = issuance_hash
, .cmr = {{0x3a7c8ea2u, 0xde579879u, 0x275bf1beu, 0xa7be5279u, 0xe703a36du, 0xc5f4e488u, 0x53a3af9bu, 0x0c501b66u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 281 /* milli weight units */
}
,[ISSUANCE_RANGE_PROOFS_HASH] =
{ .tag = JET
, .jet = issuance_range_proofs_hash
, .cmr = {{0xe05a29d1u, 0x7161105eu, 0x3b5221f4u, 0xebae702bu, 0x0c4c72b6u, 0xcb70dfdeu, 0xe2dc607bu, 0xa8a8cf72u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 280 /* milli weight units */
}
,[ISSUANCE_TOKEN] =
{ .tag = JET
, .jet = issuance_token
, .cmr = {{0x0c7e9b99u, 0xf9ec40f6u, 0x7020f83eu, 0x7367db45u, 0x88038ecdu, 0x1b3124b9u, 0x5be98267u, 0xd5f348c8u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 253 /* milli weight units */
}
,[ISSUANCE_TOKEN_AMOUNT] =
{ .tag = JET
, .jet = issuance_token_amount
, .cmr = {{0x9554ccd2u, 0x417ed6b3u, 0x75b17883u, 0xf7e98557u, 0xe448d804u, 0xccec8dc6u, 0xa3a38c60u, 0xf2f4097au}}
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w64
, .cost = 240 /* milli weight units */
}
,[ISSUANCE_TOKEN_AMOUNTS_HASH] =
{ .tag = JET
, .jet = issuance_token_amounts_hash
, .cmr = {{0x195e7666u, 0x1a78bc69u, 0x1ef0139eu, 0x1f366a96u, 0x6f75584au, 0xb7768dc7u, 0x8fffabdeu, 0x155601f6u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 289 /* milli weight units */
}
,[ISSUANCE_TOKEN_PROOF] =
{ .tag = JET
, .jet = issuance_token_proof
, .cmr = {{0x9bd45c77u, 0x4d41d208u, 0x968d9adeu, 0x7d280debu, 0x05c2699au, 0xb2b870ebu, 0xe6f44ac3u, 0xb52ec8feu}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 233 /* milli weight units */
}
,[ISSUANCES_HASH] =
{ .tag = JET
, .jet = issuances_hash
, .cmr = {{0x9ab9fd03u, 0xff1c6958u, 0x6174bc26u, 0xa88764f0u, 0xdf9cc7ddu, 0x6e61f3dcu, 0x3e426660u, 0xf0912230u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 281 /* milli weight units */
}
,[LBTC_ASSET] =
{ .tag = JET
, .jet = lbtc_asset
, .cmr = {{0x495dd0a1u, 0xcb39ee84u, 0xff45e1dfu, 0x3db4b69du, 0xe27c37c3u, 0x6d69b312u, 0x976c43f5u, 0x0e5d941au}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 3065 /* milli weight units */
}
,[LE_16] =
{ .tag = JET
, .jet = le_16
, .cmr = {{0xd617feeau, 0xfd6ffc23u, 0xfeffbe70u, 0x12ce3a03u, 0x02d4d111u, 0x665822b3u, 0x04b79adbu, 0xcc9a16d7u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 166 /* milli weight units */
}
,[LE_32] =
{ .tag = JET
, .jet = le_32
, .cmr = {{0x45745c5bu, 0xc7f8978fu, 0x85b1b14du, 0x494af21au, 0x8a51ccd8u, 0x7f3fede9u, 0x59749591u, 0x32aef9ceu}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 216 /* milli weight units */
}
,[LE_64] =
{ .tag = JET
, .jet = le_64
, .cmr = {{0x3a8f0870u, 0x900af71du, 0x4242fe26u, 0xad4dfbedu, 0x92f30bb7u, 0x9b72737du, 0xbcab9ac5u, 0xc070abe5u}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 173 /* milli weight units */
}
,[LE_8] =
{ .tag = JET
, .jet = le_8
, .cmr = {{0x5ecc9b33u, 0x25446749u, 0xafa40965u, 0xea21e011u, 0x18fb8c1au, 0xdcdc1121u, 0x9793cb2au, 0xfc4a7e8cu}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 143 /* milli weight units */
}
,[LEFT_EXTEND_16_32] =
{ .tag = JET
, .jet = left_extend_16_32
, .cmr = {{0x8c990435u, 0xb135de74u, 0x57c2690du, 0x2dc8744au, 0x506641b8u, 0x81f41e5cu, 0x17027765u, 0xc352ddcbu}}
, .sourceIx = ty_w16
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_EXTEND_16_64] =
{ .tag = JET
, .jet = left_extend_16_64
, .cmr = {{0x9b9ff9ccu, 0x27139319u, 0xb224b7b2u, 0xb816c913u, 0xa568bfd0u, 0x0be1f383u, 0xc026bcffu, 0xe9bfe712u}}
, .sourceIx = ty_w16
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_EXTEND_1_16] =
{ .tag = JET
, .jet = left_extend_1_16
, .cmr = {{0xb8ff8dc1u, 0xa04ca716u, 0x4917f4c4u, 0x50688c83u, 0xdd416cefu, 0x7b0fabddu, 0x1692fae6u, 0xbff7b4a6u}}
, .sourceIx = ty_b
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFT_EXTEND_1_32] =
{ .tag = JET
, .jet = left_extend_1_32
, .cmr = {{0x2253a452u, 0xb99902abu, 0xcf15496du, 0xf19d3112u, 0xa1cef59bu, 0x9adcee20u, 0x6c0d8dceu, 0xa628d073u}}
, .sourceIx = ty_b
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_EXTEND_1_64] =
{ .tag = JET
, .jet = left_extend_1_64
, .cmr = {{0xc8599c85u, 0x75edb7c2u, 0x60402ef2u, 0xf26dd491u, 0xcb5e4d38u, 0x18ff2e95u, 0x85c8d3e7u, 0x812db5aau}}
, .sourceIx = ty_b
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_EXTEND_1_8] =
{ .tag = JET
, .jet = left_extend_1_8
, .cmr = {{0xcfe02200u, 0x5f6bad4bu, 0x25b51e9eu, 0xbe929424u, 0x373ff197u, 0xceca62b9u, 0xe069ab08u, 0xda9f38f2u}}
, .sourceIx = ty_b
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[LEFT_EXTEND_32_64] =
{ .tag = JET
, .jet = left_extend_32_64
, .cmr = {{0x3f668404u, 0x7edafb76u, 0xf11fbf59u, 0x5499c5abu, 0xa9c4ba55u, 0xcab587cdu, 0xfebad457u, 0xb55bf5bbu}}
, .sourceIx = ty_w32
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_EXTEND_8_16] =
{ .tag = JET
, .jet = left_extend_8_16
, .cmr = {{0xdbd55f41u, 0x70153853u, 0xbad0e084u, 0xf9e1a7e7u, 0x5a7a0dc9u, 0xd8920775u, 0x575b0d48u, 0xe507af2fu}}
, .sourceIx = ty_w8
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFT_EXTEND_8_32] =
{ .tag = JET
, .jet = left_extend_8_32
, .cmr = {{0x5b5b4567u, 0x6a7503eeu, 0xd0855738u, 0x69dbc580u, 0x0b35029du, 0x140290acu, 0x20891489u, 0xbd2aa7d5u}}
, .sourceIx = ty_w8
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_EXTEND_8_64] =
{ .tag = JET
, .jet = left_extend_8_64
, .cmr = {{0x7b9ea148u, 0xa30f2af4u, 0xd4001d4fu, 0x25b0bf4fu, 0xdd67c7d0u, 0xf134d7efu, 0x3f678f72u, 0x19002bcfu}}
, .sourceIx = ty_w8
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_HIGH_16_32] =
{ .tag = JET
, .jet = left_pad_high_16_32
, .cmr = {{0xe8c2d85au, 0x7b7b2a8eu, 0xbb5b0f21u, 0x2fc8450du, 0xc1d3a468u, 0x22fb21e8u, 0x6e3fee02u, 0x0af9738fu}}
, .sourceIx = ty_w16
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_HIGH_16_64] =
{ .tag = JET
, .jet = left_pad_high_16_64
, .cmr = {{0x613b85d2u, 0xa751b3e5u, 0x1fbc59a1u, 0xdedd1fc7u, 0x93365e40u, 0x71dc1e01u, 0x4108d892u, 0x0d41d470u}}
, .sourceIx = ty_w16
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_HIGH_1_16] =
{ .tag = JET
, .jet = left_pad_high_1_16
, .cmr = {{0xe82b00efu, 0xd7dcc34eu, 0x96e8f3e5u, 0x1ead12d3u, 0x845f6c77u, 0x85e4438bu, 0x05457d95u, 0x326e59e3u}}
, .sourceIx = ty_b
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_HIGH_1_32] =
{ .tag = JET
, .jet = left_pad_high_1_32
, .cmr = {{0x88585b8cu, 0x4592d5d0u, 0x83dff68eu, 0xb5c230d0u, 0x6c37995au, 0x6fede22cu, 0x26e661a7u, 0x516e5bf4u}}
, .sourceIx = ty_b
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_HIGH_1_64] =
{ .tag = JET
, .jet = left_pad_high_1_64
, .cmr = {{0xc27e3d02u, 0x94922058u, 0x890d5c8bu, 0x676c1daeu, 0xfdde6531u, 0xe8ae6d79u, 0x37539272u, 0x3ead9c03u}}
, .sourceIx = ty_b
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_HIGH_1_8] =
{ .tag = JET
, .jet = left_pad_high_1_8
, .cmr = {{0x143e1239u, 0x2b8f2e73u, 0x5371fed0u, 0xb4b6d623u, 0xffa4f660u, 0xe5390c00u, 0xe567cf21u, 0xa1c92078u}}
, .sourceIx = ty_b
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_HIGH_32_64] =
{ .tag = JET
, .jet = left_pad_high_32_64
, .cmr = {{0xf4847c67u, 0x5667b3c6u, 0xa890fd5au, 0x6adb0927u, 0x557ee80cu, 0xd6e65af9u, 0xb1b47295u, 0x72cd8661u}}
, .sourceIx = ty_w32
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_HIGH_8_16] =
{ .tag = JET
, .jet = left_pad_high_8_16
, .cmr = {{0x7618058au, 0x4e08eb52u, 0x43dad205u, 0xcc7e8d25u, 0x47380da0u, 0x5ec5411eu, 0xfc372baau, 0x2bb12da6u}}
, .sourceIx = ty_w8
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_HIGH_8_32] =
{ .tag = JET
, .jet = left_pad_high_8_32
, .cmr = {{0x3dfed5c0u, 0xa9b26b8fu, 0x4a8eabd6u, 0xfbed87beu, 0x450de795u, 0xf541953eu, 0xec16a6d5u, 0xaa825a56u}}
, .sourceIx = ty_w8
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_HIGH_8_64] =
{ .tag = JET
, .jet = left_pad_high_8_64
, .cmr = {{0xce7c407eu, 0x4b561721u, 0xd66c1bb0u, 0xd17ee841u, 0xb4d504b4u, 0xc4c07200u, 0x2237140bu, 0x8909769fu}}
, .sourceIx = ty_w8
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_LOW_16_32] =
{ .tag = JET
, .jet = left_pad_low_16_32
, .cmr = {{0xa28c7924u, 0xa47b46ecu, 0x73bcff6eu, 0x1328d439u, 0xaa903acfu, 0x103e9aa8u, 0x0b65ba76u, 0xd2a08e75u}}
, .sourceIx = ty_w16
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_LOW_16_64] =
{ .tag = JET
, .jet = left_pad_low_16_64
, .cmr = {{0xb6258acdu, 0xa2110ed9u, 0x8c17bca8u, 0x2712e3eau, 0x60866f7du, 0x4004c83eu, 0x8ae524b7u, 0xba44008bu}}
, .sourceIx = ty_w16
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_LOW_1_16] =
{ .tag = JET
, .jet = left_pad_low_1_16
, .cmr = {{0x1e1f6cc4u, 0x24648375u, 0x49b97d30u, 0x7e28a9c2u, 0x3680914cu, 0xd86d65c3u, 0x04679312u, 0x7b54fe82u}}
, .sourceIx = ty_b
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_LOW_1_32] =
{ .tag = JET
, .jet = left_pad_low_1_32
, .cmr = {{0xc338a195u, 0x5e99820du, 0x0ed31a5au, 0xfedd1358u, 0xc1744402u, 0x3e3f2b47u, 0x33d9f68cu, 0xb7b40cd9u}}
, .sourceIx = ty_b
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_LOW_1_64] =
{ .tag = JET
, .jet = left_pad_low_1_64
, .cmr = {{0x689ed569u, 0xc201521eu, 0xc1954f0du, 0xc7d2128eu, 0x465a5204u, 0x99190549u, 0x858de9edu, 0x231a5d69u}}
, .sourceIx = ty_b
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_LOW_1_8] =
{ .tag = JET
, .jet = left_pad_low_1_8
, .cmr = {{0x5b519053u, 0xfd2bb758u, 0x473af8e3u, 0x910baef3u, 0x3cc801c0u, 0xb1420aafu, 0x814a7e72u, 0x54ea78f0u}}
, .sourceIx = ty_b
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_LOW_32_64] =
{ .tag = JET
, .jet = left_pad_low_32_64
, .cmr = {{0xac00a34fu, 0xb6a58e57u, 0xad223950u, 0x0e657137u, 0x5dfda0ceu, 0xa1175fe9u, 0x9d875cd8u, 0x718105e9u}}
, .sourceIx = ty_w32
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_LOW_8_16] =
{ .tag = JET
, .jet = left_pad_low_8_16
, .cmr = {{0xb6f6334cu, 0xc660e306u, 0x9f7e1437u, 0xa1943f61u, 0x0fc5a5abu, 0x8aa5105bu, 0xfcecd3dau, 0x0c59633cu}}
, .sourceIx = ty_w8
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_LOW_8_32] =
{ .tag = JET
, .jet = left_pad_low_8_32
, .cmr = {{0x8aee9f42u, 0xda9b842eu, 0x41189596u, 0x594756bau, 0xd9bab295u, 0x3deae668u, 0x56b9cb60u, 0x1d7ac548u}}
, .sourceIx = ty_w8
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_PAD_LOW_8_64] =
{ .tag = JET
, .jet = left_pad_low_8_64
, .cmr = {{0x611d64ceu, 0x94f882fdu, 0xa24c97adu, 0xd1905421u, 0x2f46b3b9u, 0x8ef2ae22u, 0x79364539u, 0xb93e2b8bu}}
, .sourceIx = ty_w8
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_ROTATE_16] =
{ .tag = JET
, .jet = left_rotate_16
, .cmr = {{0x25e2d4ecu, 0xc03f8765u, 0x5e965b35u, 0x7d6fd0c2u, 0xea36d112u, 0x068c9633u, 0x39de467eu, 0x5c8e7d8eu}}
, .sourceIx = ty_pw4w16
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFT_ROTATE_32] =
{ .tag = JET
, .jet = left_rotate_32
, .cmr = {{0x2d4189b3u, 0x12e8cedau, 0xaa3853a4u, 0x5a12986eu, 0xe262fb60u, 0x5f0d592du, 0xcbb9618fu, 0xe67a250bu}}
, .sourceIx = ty_pw8w32
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_ROTATE_64] =
{ .tag = JET
, .jet = left_rotate_64
, .cmr = {{0xb8e68e0au, 0xd682b967u, 0xf24c0984u, 0xf7d5f809u, 0xa28597a0u, 0x434618c8u, 0x949fa808u, 0xe3be7614u}}
, .sourceIx = ty_pw8w64
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_ROTATE_8] =
{ .tag = JET
, .jet = left_rotate_8
, .cmr = {{0x956a653au, 0xe0b8f8c3u, 0xf29fd8f3u, 0x3119168fu, 0xcbe64f5du, 0x765fa9ffu, 0x6b8e3b0du, 0x961a1629u}}
, .sourceIx = ty_pw4w8
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[LEFT_SHIFT_16] =
{ .tag = JET
, .jet = left_shift_16
, .cmr = {{0x9bbce29eu, 0x695be2e4u, 0x830c7a93u, 0xa0d2151bu, 0x664fc272u, 0x06eed7e5u, 0x0fcef602u, 0xd345ce0du}}
, .sourceIx = ty_pw4w16
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFT_SHIFT_32] =
{ .tag = JET
, .jet = left_shift_32
, .cmr = {{0xf9c4bf07u, 0xd3e72e85u, 0xb1d455f7u, 0x34cf1b11u, 0xbea58e25u, 0x3b854a1au, 0x097bab1eu, 0xc2c62e1fu}}
, .sourceIx = ty_pw8w32
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_SHIFT_64] =
{ .tag = JET
, .jet = left_shift_64
, .cmr = {{0x8cfa741au, 0xa41d828au, 0x41083bb7u, 0xcbdd1f4eu, 0xda5dccacu, 0x529b247du, 0x188495b4u, 0x9bb38c2bu}}
, .sourceIx = ty_pw8w64
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_SHIFT_8] =
{ .tag = JET
, .jet = left_shift_8
, .cmr = {{0x95663e07u, 0x7cadca31u, 0xb9596b09u, 0x706cdb4fu, 0xa703870fu, 0x792a4635u, 0x852b5e24u, 0x69e6fdbau}}
, .sourceIx = ty_pw4w8
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[LEFT_SHIFT_WITH_16] =
{ .tag = JET
, .jet = left_shift_with_16
, .cmr = {{0x6214c456u, 0x25d704ceu, 0xc987b796u, 0x676f1566u, 0x1a6bf5dcu, 0x0f6a51cbu, 0x865a0e71u, 0xd66fbf95u}}
, .sourceIx = ty_pbpw4w16
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFT_SHIFT_WITH_32] =
{ .tag = JET
, .jet = left_shift_with_32
, .cmr = {{0x1b452fc7u, 0xab5c7147u, 0x454af4d5u, 0x595481ffu, 0xac42dea1u, 0x06032b3bu, 0x9f375bedu, 0xcda6f4d6u}}
, .sourceIx = ty_pbpw8w32
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFT_SHIFT_WITH_64] =
{ .tag = JET
, .jet = left_shift_with_64
, .cmr = {{0xc38b02abu, 0xcff514d9u, 0x6191a7feu, 0xfba1ac16u, 0xe9c150a1u, 0x8ce1c5bcu, 0xf09d6755u, 0xe0369905u}}
, .sourceIx = ty_pbpw8w64
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[LEFT_SHIFT_WITH_8] =
{ .tag = JET
, .jet = left_shift_with_8
, .cmr = {{0x217ad6dcu, 0x1292aa42u, 0xdbd84dbdu, 0x971c118fu, 0x02a9740au, 0x7cb5661eu, 0x90d42dd5u, 0xca8ca4d9u}}
, .sourceIx = ty_pbpw4w8
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_16_1] =
{ .tag = JET
, .jet = leftmost_16_1
, .cmr = {{0x3ea89e43u, 0x2077940du, 0x0bbf9ed2u, 0xcf16ba63u, 0x1110e7abu, 0x9f19eef3u, 0xea925a69u, 0x9f60c60cu}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_16_2] =
{ .tag = JET
, .jet = leftmost_16_2
, .cmr = {{0x5ce2bd7au, 0xc35a7c33u, 0x73c3dd60u, 0x7f48e5d4u, 0xc7aaa6c6u, 0x9fc4930eu, 0xca14049fu, 0x5d39ffabu}}
, .sourceIx = ty_w16
, .targetIx = ty_w2
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_16_4] =
{ .tag = JET
, .jet = leftmost_16_4
, .cmr = {{0x1012a139u, 0x3ed0f91du, 0x75ad5912u, 0x2853893au, 0x7f25cd35u, 0xc8036c7fu, 0xa195682cu, 0xa1458c4au}}
, .sourceIx = ty_w16
, .targetIx = ty_w4
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_16_8] =
{ .tag = JET
, .jet = leftmost_16_8
, .cmr = {{0xccd31e9eu, 0xb1a1bbdeu, 0x555c0f73u, 0x1af2d3d4u, 0xff5388fau, 0x1461826au, 0xa9c89342u, 0x42ac753fu}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_32_1] =
{ .tag = JET
, .jet = leftmost_32_1
, .cmr = {{0xb714ad74u, 0xae045af7u, 0x5680778au, 0x032761a4u, 0xc726d7b6u, 0xd977bc93u, 0xa4125654u, 0x3cae8d3du}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_32_16] =
{ .tag = JET
, .jet = leftmost_32_16
, .cmr = {{0x1b20634fu, 0xb43eb83au, 0x968c3c81u, 0xc0087c63u, 0xd5d4f8cau, 0xcdbd3e0eu, 0x9f9a3d75u, 0x91c3ef62u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_32_2] =
{ .tag = JET
, .jet = leftmost_32_2
, .cmr = {{0x752dda08u, 0xe40faea0u, 0xf6c4ee3du, 0x344b7c4eu, 0xa11b971du, 0xcec55592u, 0xb822ee56u, 0x271ca5dfu}}
, .sourceIx = ty_w32
, .targetIx = ty_w2
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_32_4] =
{ .tag = JET
, .jet = leftmost_32_4
, .cmr = {{0x44e9f779u, 0xa029ecfcu, 0x9762b8b6u, 0xcbaf0922u, 0xd935fea5u, 0x150a546au, 0x5fc1fdb8u, 0xb9534134u}}
, .sourceIx = ty_w32
, .targetIx = ty_w4
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_32_8] =
{ .tag = JET
, .jet = leftmost_32_8
, .cmr = {{0x54801eb5u, 0xe778cf6cu, 0xda95ccf5u, 0x70286d81u, 0x6d3a1ff1u, 0xdd39db5au, 0xb6136f0eu, 0xc3b72dc6u}}
, .sourceIx = ty_w32
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_64_1] =
{ .tag = JET
, .jet = leftmost_64_1
, .cmr = {{0xb316af24u, 0xc86b3961u, 0x3d4fd1b3u, 0x926a8413u, 0x0eb7ab12u, 0xfdef6233u, 0x17ab48f7u, 0x7cb62145u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_64_16] =
{ .tag = JET
, .jet = leftmost_64_16
, .cmr = {{0x8cf85481u, 0xe0f00838u, 0xb5239bbfu, 0xad1382f0u, 0x7bd03c12u, 0x1d5d8aafu, 0xa6d98341u, 0x6de45c32u}}
, .sourceIx = ty_w64
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_64_2] =
{ .tag = JET
, .jet = leftmost_64_2
, .cmr = {{0xda40c89bu, 0x15c9e86bu, 0x028ce9ecu, 0x07b7f699u, 0x5a5ddda4u, 0x850a91afu, 0x8c60e02bu, 0xf991fb0cu}}
, .sourceIx = ty_w64
, .targetIx = ty_w2
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_64_32] =
{ .tag = JET
, .jet = leftmost_64_32
, .cmr = {{0x95f46db9u, 0xd906f050u, 0x53455e95u, 0x34eb9b08u, 0xb09e38bcu, 0x0fc698a1u, 0x6f4b2a62u, 0x710759d1u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_64_4] =
{ .tag = JET
, .jet = leftmost_64_4
, .cmr = {{0xf501f905u, 0xfb8baba1u, 0xa7e8a6bfu, 0x68d3ae6au, 0x0add9195u, 0x1b56629du, 0x59f42873u, 0x9e7e41a2u}}
, .sourceIx = ty_w64
, .targetIx = ty_w4
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_64_8] =
{ .tag = JET
, .jet = leftmost_64_8
, .cmr = {{0xb37f0ba2u, 0xfcbd4ae3u, 0x316a4fe4u, 0xf58aa1a5u, 0x41740cdeu, 0x60ed87f3u, 0x3862a2ffu, 0xecad442fu}}
, .sourceIx = ty_w64
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_8_1] =
{ .tag = JET
, .jet = leftmost_8_1
, .cmr = {{0x5fdcfa9bu, 0x9a4b65c7u, 0x207471e5u, 0x33928d6au, 0x24f4b6ffu, 0x9b345ef7u, 0x61b1480au, 0x8a05e3d7u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_8_2] =
{ .tag = JET
, .jet = leftmost_8_2
, .cmr = {{0x624221e9u, 0xf8a91691u, 0x26c73347u, 0x9648c73bu, 0x68c6b8ebu, 0xbb60c72au, 0xf1e6fc65u, 0xe7d30723u}}
, .sourceIx = ty_w8
, .targetIx = ty_w2
, .cost = 150 /* milli weight units */
}
,[LEFTMOST_8_4] =
{ .tag = JET
, .jet = leftmost_8_4
, .cmr = {{0x1a4843c4u, 0x08e1d46cu, 0x9c938946u, 0x34495f8au, 0xd6a680e3u, 0x2dd6f25bu, 0xa19dbc60u, 0xa60d1897u}}
, .sourceIx = ty_w8
, .targetIx = ty_w4
, .cost = 150 /* milli weight units */
}
,[LINEAR_COMBINATION_1] =
{ .tag = JET
, .jet = linear_combination_1
, .cmr = {{0x00bef144u, 0xda3f5163u, 0x318c01ebu, 0x66cc681fu, 0x29ccb987u, 0xea2a88d0u, 0x83345a1cu, 0xaa082ce3u}}
, .sourceIx = ty_ppw256pw512w256w256
, .targetIx = ty_pw512w256
, .cost = 86722 /* milli weight units */
}
,[LINEAR_VERIFY_1] =
{ .tag = JET
, .jet = linear_verify_1
, .cmr = {{0x0c9fae64u, 0xa64cd63cu, 0xa85beba7u, 0x5c9f2c6eu, 0x85343b74u, 0xf28634eau, 0x85f70fc3u, 0x41ccaff3u}}
, .sourceIx = ty_pppw256w512w256w512
, .targetIx = ty_u
, .cost = 43063 /* milli weight units */
}
,[LOCK_TIME] =
{ .tag = JET
, .jet = lock_time
, .cmr = {{0xee87a025u, 0xd7338a3cu, 0x8f251be4u, 0x19efb7eeu, 0x7177cb73u, 0x8f42e8c0u, 0x03fc4658u, 0xcc0e5b8bu}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 132 /* milli weight units */
}
,[LOW_1] =
{ .tag = JET
, .jet = low_1
, .cmr = {{0xdb4a424au, 0x20aeefa4u, 0xe742d51du, 0x84929218u, 0xcbf73472u, 0x6176dc4fu, 0xf9f8bf13u, 0xde10ca2bu}}
, .sourceIx = ty_u
, .targetIx = ty_b
, .cost = 173 /* milli weight units */
}
,[LOW_16] =
{ .tag = JET
, .jet = low_16
, .cmr = {{0xa114e958u, 0x0de07d8bu, 0x077eb889u, 0x98755a0au, 0x62bfe085u, 0xfb23404cu, 0xd1e87868u, 0xcd56d5bdu}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 172 /* milli weight units */
}
,[LOW_32] =
{ .tag = JET
, .jet = low_32
, .cmr = {{0xa717610eu, 0x8c577125u, 0x5140d620u, 0x7fff3bddu, 0x3464acffu, 0x5998e129u, 0xaf8b9f4cu, 0x0e21b23du}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 170 /* milli weight units */
}
,[LOW_64] =
{ .tag = JET
, .jet = low_64
, .cmr = {{0x9a6f4a0au, 0xd2fb72c5u, 0x79424c72u, 0xe17daae6u, 0x2b366695u, 0xcd1a2685u, 0xfb0ab02eu, 0x4c2cc0f5u}}
, .sourceIx = ty_u
, .targetIx = ty_w64
, .cost = 162 /* milli weight units */
}
,[LOW_8] =
{ .tag = JET
, .jet = low_8
, .cmr = {{0x69c9b9cau, 0xb9f44cffu, 0xaedf1c84u, 0x3146bcc0u, 0xb03b0f0cu, 0x134866afu, 0xd23a614fu, 0x01a70a24u}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 173 /* milli weight units */
}
,[LT_16] =
{ .tag = JET
, .jet = lt_16
, .cmr = {{0x4f465a49u, 0xa963acceu, 0x93f6b6f8u, 0x23eb9472u, 0xb4cc21f6u, 0xe58b7657u, 0x0508babdu, 0xf44a8c97u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 188 /* milli weight units */
}
,[LT_32] =
{ .tag = JET
, .jet = lt_32
, .cmr = {{0xd3421dfcu, 0x84671cd7u, 0x445082a9u, 0x86df1628u, 0xedcacbf4u, 0x29a3c809u, 0xd2365497u, 0xe1170bfdu}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 215 /* milli weight units */
}
,[LT_64] =
{ .tag = JET
, .jet = lt_64
, .cmr = {{0x7c67aa89u, 0x93fcda59u, 0x30f79db2u, 0x008aa6d7u, 0xbe5f3bedu, 0x5aca5e03u, 0x2dcccf0bu, 0xe84f62d1u}}
, .sourceIx = ty_w128
, .targetIx = ty_b
, .cost = 195 /* milli weight units */
}
,[LT_8] =
{ .tag = JET
, .jet = lt_8
, .cmr = {{0x98763f78u, 0x21690954u, 0xcf508102u, 0x09df6e15u, 0x570316bbu, 0xa89ffa9au, 0xe556a915u, 0xf37b640bu}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 130 /* milli weight units */
}
,[MAJ_1] =
{ .tag = JET
, .jet = maj_1
, .cmr = {{0xae8b912eu, 0x3ad47f68u, 0x8bbb46c8u, 0xcb6d5333u, 0x69f5109au, 0x2730471eu, 0xab6efe98u, 0xe9ea5e78u}}
, .sourceIx = ty_pbw2
, .targetIx = ty_b
, .cost = 241 /* milli weight units */
}
,[MAJ_16] =
{ .tag = JET
, .jet = maj_16
, .cmr = {{0xf5a41da0u, 0x377fe688u, 0xac2fcdf3u, 0x5b6b7a47u, 0x2e78ea69u, 0xfd2b17f7u, 0x56342baau, 0x1f8b9fddu}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 273 /* milli weight units */
}
,[MAJ_32] =
{ .tag = JET
, .jet = maj_32
, .cmr = {{0xf1d93b04u, 0x6b0285f6u, 0xe520467fu, 0x265f6a6au, 0xe3491f16u, 0x78c8a826u, 0xa0099b9cu, 0xd41599d4u}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 289 /* milli weight units */
}
,[MAJ_64] =
{ .tag = JET
, .jet = maj_64
, .cmr = {{0x5e996c51u, 0x51d7aceeu, 0x4a7d9e22u, 0x95ef8f2cu, 0x75548884u, 0x4bfde25du, 0x5acdfea2u, 0x9844435au}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 293 /* milli weight units */
}
,[MAJ_8] =
{ .tag = JET
, .jet = maj_8
, .cmr = {{0xab6c4c41u, 0xab67ebf7u, 0xea60870cu, 0x9b2d9310u, 0x01742961u, 0x8d2ab902u, 0x68b5c5c2u, 0xb5377f3bu}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 241 /* milli weight units */
}
,[MAX_16] =
{ .tag = JET
, .jet = max_16
, .cmr = {{0xcddd8169u, 0x5522971bu, 0x529eb0bbu, 0x53818fe2u, 0x2858ac6bu, 0x037c3810u, 0xec268b53u, 0xb817a38du}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 164 /* milli weight units */
}
,[MAX_32] =
{ .tag = JET
, .jet = max_32
, .cmr = {{0xd916f34bu, 0xd785b938u, 0x08b67c62u, 0x284f94aau, 0x5df47919u, 0x59b49b85u, 0x82b0582bu, 0x82853883u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 162 /* milli weight units */
}
,[MAX_64] =
{ .tag = JET
, .jet = max_64
, .cmr = {{0x99ef5abfu, 0xf78700bdu, 0x93d1c977u, 0xfd686f31u, 0x210fd1ceu, 0x1d094d23u, 0x048c026cu, 0x19fc984au}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 193 /* milli weight units */
}
,[MAX_8] =
{ .tag = JET
, .jet = max_8
, .cmr = {{0x3acbf773u, 0x3fd8ef4fu, 0x51967aa2u, 0x45558b28u, 0x374d54c6u, 0x32a9f46au, 0xab6b2b1eu, 0xc2d5139au}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 142 /* milli weight units */
}
,[MEDIAN_16] =
{ .tag = JET
, .jet = median_16
, .cmr = {{0xd6463e89u, 0xdfe2c334u, 0xb01f9097u, 0xb01a75c4u, 0x75fb0f0fu, 0x167cb6b7u, 0x4976f197u, 0xbd4c76e1u}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 270 /* milli weight units */
}
,[MEDIAN_32] =
{ .tag = JET
, .jet = median_32
, .cmr = {{0x01dca1edu, 0xe5b29d88u, 0x480bc4dcu, 0x43be4e04u, 0xf2d209eeu, 0x32f6cf3eu, 0xc7050da1u, 0x07359063u}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 256 /* milli weight units */
}
,[MEDIAN_64] =
{ .tag = JET
, .jet = median_64
, .cmr = {{0x707a6fa8u, 0xc15495a2u, 0xc4822263u, 0xddcea5e0u, 0xf0e850a9u, 0x4b1cf4ecu, 0xc0652fafu, 0xeef130e9u}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 336 /* milli weight units */
}
,[MEDIAN_8] =
{ .tag = JET
, .jet = median_8
, .cmr = {{0x26bfcb7bu, 0xabcf26c9u, 0x7a841675u, 0x45746276u, 0x59279af8u, 0x09554882u, 0x400ef874u, 0xdf1c1a31u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 256 /* milli weight units */
}
,[MIN_16] =
{ .tag = JET
, .jet = min_16
, .cmr = {{0x63bbc0e5u, 0xdb1ce080u, 0x97d3f5bcu, 0xc5be1d72u, 0x090bab4au, 0x87c10c80u, 0x0549ca84u, 0xefbfe5e3u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 164 /* milli weight units */
}
,[MIN_32] =
{ .tag = JET
, .jet = min_32
, .cmr = {{0xaf4d6184u, 0x2f479032u, 0x5c614556u, 0xc7776eeau, 0x457513cau, 0x422f305bu, 0x463f8f7du, 0x8bda0c3cu}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 181 /* milli weight units */
}
,[MIN_64] =
{ .tag = JET
, .jet = min_64
, .cmr = {{0xf0a3170fu, 0xb3065090u, 0x71b21432u, 0x309c0086u, 0x5d8fb675u, 0x2de6ec41u, 0x0abb6ce3u, 0x5b4ffa9cu}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[MIN_8] =
{ .tag = JET
, .jet = min_8
, .cmr = {{0x8aa71d09u, 0x3e838ad3u, 0x6aa6fe16u, 0xfd1dde9fu, 0xb5772ac4u, 0x5d6bb8e4u, 0x2c8883a2u, 0xa9f100e2u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 135 /* milli weight units */
}
,[MODULO_16] =
{ .tag = JET
, .jet = modulo_16
, .cmr = {{0x0ea89859u, 0x79209d31u, 0x94c55912u, 0xf21a6577u, 0xda30c517u, 0xe008f851u, 0xc352085bu, 0xb067a0f1u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 188 /* milli weight units */
}
,[MODULO_32] =
{ .tag = JET
, .jet = modulo_32
, .cmr = {{0x223fb583u, 0x2b9559cau, 0x8651726au, 0xb7956e58u, 0xe53a402du, 0xf9603486u, 0x181807a2u, 0xfcaed487u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 207 /* milli weight units */
}
,[MODULO_64] =
{ .tag = JET
, .jet = modulo_64
, .cmr = {{0x8259a2e3u, 0xb0789c9du, 0x31eabc49u, 0x39d31bc5u, 0x254c5665u, 0xc412052cu, 0x12d72ecdu, 0xfbed5225u}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 191 /* milli weight units */
}
,[MODULO_8] =
{ .tag = JET
, .jet = modulo_8
, .cmr = {{0xf8fd7c21u, 0xc15ebc5au, 0x04b3d3bcu, 0x0ad647e2u, 0x1d89f800u, 0x8ddddffeu, 0xbb003e35u, 0x52bdb570u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 158 /* milli weight units */
}
,[MULTIPLY_16] =
{ .tag = JET
, .jet = multiply_16
, .cmr = {{0xd66b0ad2u, 0x1cdbe601u, 0x4f2619f4u, 0x40d935f6u, 0x42e97c59u, 0x4e3b441fu, 0x01980eeau, 0x08c48591u}}
, .sourceIx = ty_w32
, .targetIx = ty_w32
, .cost = 154 /* milli weight units */
}
,[MULTIPLY_32] =
{ .tag = JET
, .jet = multiply_32
, .cmr = {{0xc67f65afu, 0xae79108cu, 0xe5f724f4u, 0x01817aa1u, 0xb4a7608au, 0x4e18ee74u, 0x826b37f7u, 0x949c77d6u}}
, .sourceIx = ty_w64
, .targetIx = ty_w64
, .cost = 165 /* milli weight units */
}
,[MULTIPLY_64] =
{ .tag = JET
, .jet = multiply_64
, .cmr = {{0x16ac08feu, 0xc9d96652u, 0x7f80c39cu, 0x64a4fc10u, 0x82b150bdu, 0xbb05f7f6u, 0xc4b9a00eu, 0xbd894dbau}}
, .sourceIx = ty_w128
, .targetIx = ty_w128
, .cost = 185 /* milli weight units */
}
,[MULTIPLY_8] =
{ .tag = JET
, .jet = multiply_8
, .cmr = {{0xcec3d5c3u, 0x2dee352eu, 0x754f141cu, 0x02ef2b60u, 0xf86e27d2u, 0xcbe27326u, 0x060dec9eu, 0x7bcc206bu}}
, .sourceIx = ty_w16
, .targetIx = ty_w16
, .cost = 126 /* milli weight units */
}
,[NEGATE_16] =
{ .tag = JET
, .jet = negate_16
, .cmr = {{0x81f3ef08u, 0x2b199d2eu, 0x474535fbu, 0x84282f21u, 0x111c1a04u, 0x97a91695u, 0xe72c4d51u, 0xaf1cb057u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw16
, .cost = 121 /* milli weight units */
}
,[NEGATE_32] =
{ .tag = JET
, .jet = negate_32
, .cmr = {{0xba173bdeu, 0xf24e637fu, 0x4a5a0c6fu, 0xed4bbc22u, 0xc7d08bccu, 0x20fdca61u, 0x70363d25u, 0x26955836u}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw32
, .cost = 185 /* milli weight units */
}
,[NEGATE_64] =
{ .tag = JET
, .jet = negate_64
, .cmr = {{0xe713272du, 0x6d9a6d69u, 0x6c46889du, 0xfb270475u, 0xe9238d17u, 0x72abf916u, 0x5b093c79u, 0x98ee8070u}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw64
, .cost = 162 /* milli weight units */
}
,[NEGATE_8] =
{ .tag = JET
, .jet = negate_8
, .cmr = {{0x8be87139u, 0x3e18c063u, 0x69161fb1u, 0xc0ad2b92u, 0x0622974eu, 0x3fdfca90u, 0x567e6da4u, 0x29fd9842u}}
, .sourceIx = ty_w8
, .targetIx = ty_pbw8
, .cost = 152 /* milli weight units */
}
,[NEW_ISSUANCE_CONTRACT] =
{ .tag = JET
, .jet = new_issuance_contract
, .cmr = {{0x59e2a74cu, 0x997a07aau, 0xfd5c280eu, 0x4649e7afu, 0x2b3cc4dcu, 0x9b72a81cu, 0x722548ffu, 0x8c1313bfu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 214 /* milli weight units */
}
,[NONCE_HASH] =
{ .tag = JET
, .jet = nonce_hash
, .cmr = {{0xca4a66d7u, 0xf8e982a9u, 0xee042504u, 0x0d2b0d1du, 0x3dc6207fu, 0x93856458u, 0xe24e7a26u, 0xe95c56f8u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256mspbw256w256
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 2727 /* milli weight units */
}
,[NUM_INPUTS] =
{ .tag = JET
, .jet = num_inputs
, .cmr = {{0xd7b46628u, 0x7ef4e59cu, 0x02be3389u, 0xeafb4347u, 0xb7d1a2a1u, 0x5c144918u, 0xb7ad3443u, 0xb14fae03u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 139 /* milli weight units */
}
,[NUM_OUTPUTS] =
{ .tag = JET
, .jet = num_outputs
, .cmr = {{0x67df4debu, 0x3ff0c26au, 0xe3123047u, 0xcc734ae3u, 0xb61ffcefu, 0x511fcf42u, 0x813c3f48u, 0x1920ee48u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 134 /* milli weight units */
}
,[ONE_16] =
{ .tag = JET
, .jet = one_16
, .cmr = {{0x7629792bu, 0xa1a44114u, 0xe59e64b5u, 0x1d187af6u, 0xd965d966u, 0x20dca262u, 0x7507b7d3u, 0x88d9353cu}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 126 /* milli weight units */
}
,[ONE_32] =
{ .tag = JET
, .jet = one_32
, .cmr = {{0x0ba004ceu, 0xa250fe95u, 0x3ac74e6eu, 0xcd3620e8u, 0x02841fdau, 0x795208deu, 0xc66d626eu, 0x06aa29b2u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 122 /* milli weight units */
}
,[ONE_64] =
{ .tag = JET
, .jet = one_64
, .cmr = {{0xba3478c1u, 0x08740a83u, 0xf0ca0eaeu, 0x86c31b4au, 0xfac830dfu, 0x093467ccu, 0x08ea1c04u, 0x15efef6du}}
, .sourceIx = ty_u
, .targetIx = ty_w64
, .cost = 123 /* milli weight units */
}
,[ONE_8] =
{ .tag = JET
, .jet = one_8
, .cmr = {{0x15ca77a4u, 0xb7022568u, 0x37f90ff7u, 0x8ca7740au, 0x40fece71u, 0x91301d00u, 0xe517d8d3u, 0x4f46c250u}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 127 /* milli weight units */
}
,[OR_1] =
{ .tag = JET
, .jet = or_1
, .cmr = {{0x93522230u, 0x1700987du, 0xe12cb426u, 0x17218153u, 0xfd7ccd63u, 0x174a1749u, 0xfc880c39u, 0xe3e7239cu}}
, .sourceIx = ty_w2
, .targetIx = ty_b
, .cost = 147 /* milli weight units */
}
,[OR_16] =
{ .tag = JET
, .jet = or_16
, .cmr = {{0xdfead0bau, 0x93e49155u, 0xc40cb372u, 0xca5ef617u, 0x9741c61fu, 0x2b3cc279u, 0x7ef162c8u, 0xd2fc1f9au}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 204 /* milli weight units */
}
,[OR_32] =
{ .tag = JET
, .jet = or_32
, .cmr = {{0x67ac6945u, 0xcdc006d2u, 0x5e5bbe6cu, 0x4fe81ca1u, 0x6741ffabu, 0x3d23960eu, 0xeb49850fu, 0x92732cbbu}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 197 /* milli weight units */
}
,[OR_64] =
{ .tag = JET
, .jet = or_64
, .cmr = {{0x1eb952e4u, 0x6116e271u, 0xdc489e67u, 0x22a90185u, 0xebf5fb77u, 0x5b778160u, 0x6dbf5e89u, 0xccd7c250u}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 214 /* milli weight units */
}
,[OR_8] =
{ .tag = JET
, .jet = or_8
, .cmr = {{0x378f7abeu, 0x8b081fafu, 0x5b3a2578u, 0xef1979feu, 0x80bccb07u, 0x91156a49u, 0x3f8a3f6eu, 0x0bb2fc84u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 147 /* milli weight units */
}
,[OUTPOINT_HASH] =
{ .tag = JET
, .jet = outpoint_hash
, .cmr = {{0xe31d339du, 0x86e6d76bu, 0xadc3d6d6u, 0xcf1be706u, 0x53e03442u, 0x73449cecu, 0xf521d366u, 0x2bd8fc2bu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256pmw256pw256w32
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 5256 /* milli weight units */
}
,[OUTPUT_AMOUNT] =
{ .tag = JET
, .jet = output_amount
, .cmr = {{0x52db68c6u, 0xc7be32bfu, 0xaa426970u, 0xeb4197ceu, 0x1ce3f453u, 0x0e1a2cffu, 0x8e17db47u, 0x229207b3u}}
, .sourceIx = ty_w32
, .targetIx = ty_mpspbw256w256spbw256w64
, .cost = 709 /* milli weight units */
}
,[OUTPUT_AMOUNTS_HASH] =
{ .tag = JET
, .jet = output_amounts_hash
, .cmr = {{0xbccbee78u, 0x1ee297fau, 0xbfbe38c0u, 0x079ad374u, 0x258c0b1eu, 0xbe223457u, 0x099a284au, 0x1b4338a2u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 404 /* milli weight units */
}
,[OUTPUT_ASSET] =
{ .tag = JET
, .jet = output_asset
, .cmr = {{0xca89b5c4u, 0x5a9a247du, 0x39086cdfu, 0xbe2ba1dfu, 0x025e37dbu, 0x9b6a2abbu, 0x74d97066u, 0xa69bf3a0u}}
, .sourceIx = ty_w32
, .targetIx = ty_mspbw256w256
, .cost = 621 /* milli weight units */
}
,[OUTPUT_HASH] =
{ .tag = JET
, .jet = output_hash
, .cmr = {{0x7875cc33u, 0x2cf1b49cu, 0xdcf11e70u, 0x18dc8119u, 0x3ee4b19eu, 0xa142fc0au, 0xe7dbddb3u, 0x36e2fbfau}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 296 /* milli weight units */
}
,[OUTPUT_IS_FEE] =
{ .tag = JET
, .jet = output_is_fee
, .cmr = {{0xf70eb068u, 0xd200b7bcu, 0x5aaaaba1u, 0x2928e819u, 0x2b2948cdu, 0xe7e8f314u, 0x1c6b4311u, 0x38e5de3cu}}
, .sourceIx = ty_w32
, .targetIx = ty_mb
, .cost = 270 /* milli weight units */
}
,[OUTPUT_NONCE] =
{ .tag = JET
, .jet = output_nonce
, .cmr = {{0xedab1241u, 0xd297f274u, 0x7ad378a8u, 0x1a56143du, 0x741bc4eeu, 0x4c30b32fu, 0x8bc1aeb5u, 0x2cc4814cu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmspbw256w256
, .cost = 396 /* milli weight units */
}
,[OUTPUT_NONCES_HASH] =
{ .tag = JET
, .jet = output_nonces_hash
, .cmr = {{0xf07fe7e9u, 0x7396865du, 0x50c1ac94u, 0x77ad9f95u, 0x062f11edu, 0x01c97de7u, 0xfa4affa0u, 0x8cd10531u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 387 /* milli weight units */
}
,[OUTPUT_NULL_DATUM] =
{ .tag = JET
, .jet = output_null_datum
, .cmr = {{0x964c4deeu, 0x8fe4a866u, 0xcc3ea494u, 0x7884814cu, 0xccd60269u, 0x2e378ba0u, 0xe935fa03u, 0xf95e3de1u}}
, .sourceIx = ty_w64
, .targetIx = ty_mmspw2w256sbw4
, .cost = 249 /* milli weight units */
}
,[OUTPUT_RANGE_PROOF] =
{ .tag = JET
, .jet = output_range_proof
, .cmr = {{0xa00418e4u, 0xabc4bed5u, 0x373fc222u, 0xce1f960bu, 0x6435eaa8u, 0xf14fe66cu, 0xa42c52ddu, 0x9ae226b8u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 452 /* milli weight units */
}
,[OUTPUT_RANGE_PROOFS_HASH] =
{ .tag = JET
, .jet = output_range_proofs_hash
, .cmr = {{0xebe626e2u, 0x854e7000u, 0x75eadeeeu, 0xad5fe0bdu, 0xd69c1b0fu, 0xadf108d3u, 0x68c1293fu, 0x86585fb1u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 397 /* milli weight units */
}
,[OUTPUT_SCRIPT_HASH] =
{ .tag = JET
, .jet = output_script_hash
, .cmr = {{0xecf673e5u, 0xfcaf7b7eu, 0x6e37b628u, 0x095e5a9eu, 0xf981e6c4u, 0xc339ebdfu, 0x3eb1e6bfu, 0x4505f534u}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 437 /* milli weight units */
}
,[OUTPUT_SCRIPTS_HASH] =
{ .tag = JET
, .jet = output_scripts_hash
, .cmr = {{0xc0489e87u, 0x8cd89ca5u, 0x109a5316u, 0x7a61a845u, 0x4ed6dc2au, 0xcef9191au, 0xd53bbfb3u, 0xb0ea72dfu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 416 /* milli weight units */
}
,[OUTPUT_SURJECTION_PROOF] =
{ .tag = JET
, .jet = output_surjection_proof
, .cmr = {{0x1de8addbu, 0xf8b697c2u, 0xb3d192bdu, 0xe2c2c55fu, 0x5e6709c5u, 0xbd8631e3u, 0x8d8378ddu, 0x3dce49ccu}}
, .sourceIx = ty_w32
, .targetIx = ty_mw256
, .cost = 453 /* milli weight units */
}
,[OUTPUT_SURJECTION_PROOFS_HASH] =
{ .tag = JET
, .jet = output_surjection_proofs_hash
, .cmr = {{0x743eb2d9u, 0x8e2c69c4u, 0x03aba3c3u, 0x3dcb8351u, 0xde8224c9u, 0xe04da507u, 0x1c8dfd7au, 0x935070acu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 419 /* milli weight units */
}
,[OUTPUTS_HASH] =
{ .tag = JET
, .jet = outputs_hash
, .cmr = {{0x12af1e5cu, 0x32da7512u, 0xfcd43259u, 0xd1bc8472u, 0xa915ce21u, 0xc6d306e4u, 0x85f1dbbcu, 0x07a1cfdbu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 296 /* milli weight units */
}
,[PARSE_LOCK] =
{ .tag = JET
, .jet = parse_lock
, .cmr = {{0x4571ca04u, 0x52577cfau, 0xf8a85f5eu, 0x329d602cu, 0x8dcad127u, 0x6a974e2cu, 0x75d2ec04u, 0x657bc425u}}
, .sourceIx = ty_w32
, .targetIx = ty_sw32w32
, .cost = 177 /* milli weight units */
}
,[PARSE_SEQUENCE] =
{ .tag = JET
, .jet = parse_sequence
, .cmr = {{0x55c90366u, 0x0c8c92b1u, 0x429f63e2u, 0x7471acd5u, 0x9c3a26aau, 0x7a59221du, 0x7a6d52b6u, 0x2ebaf94au}}
, .sourceIx = ty_w32
, .targetIx = ty_msw16w16
, .cost = 261 /* milli weight units */
}
,[POINT_VERIFY_1] =
{ .tag = JET
, .jet = point_verify_1
, .cmr = {{0xb6009cecu, 0x8be8b14au, 0x1d313299u, 0xd66761d6u, 0x59adfff8u, 0x232899abu, 0x7db4097fu, 0x52c7d0beu}}
, .sourceIx = ty_pppw256pbw256w256pbw256
, .targetIx = ty_u
, .cost = 50604 /* milli weight units */
}
,[REISSUANCE_BLINDING] =
{ .tag = JET
, .jet = reissuance_blinding
, .cmr = {{0x0b9a0aafu, 0xedb102a1u, 0x64061419u, 0xa789ea84u, 0x326cd589u, 0xf17c0ea0u, 0x192dd637u, 0x2ecb5ebfu}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 153 /* milli weight units */
}
,[REISSUANCE_ENTROPY] =
{ .tag = JET
, .jet = reissuance_entropy
, .cmr = {{0xce84f983u, 0xa3bd3394u, 0x3d4dcb44u, 0x861c4a69u, 0xa2a5e8a5u, 0x22b5d5ebu, 0xf2515f51u, 0x1ac6a9b2u}}
, .sourceIx = ty_w32
, .targetIx = ty_mmw256
, .cost = 126 /* milli weight units */
}
,[RIGHT_EXTEND_16_32] =
{ .tag = JET
, .jet = right_extend_16_32
, .cmr = {{0x36423c16u, 0xd48d6c7cu, 0x91ed4416u, 0x11be3072u, 0xdfa5dd38u, 0xe4d27da8u, 0xdaed2978u, 0x8fc95208u}}
, .sourceIx = ty_w16
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_EXTEND_16_64] =
{ .tag = JET
, .jet = right_extend_16_64
, .cmr = {{0x4b8a47b9u, 0x067073a1u, 0xfb68300fu, 0xacd6c506u, 0x9890abdbu, 0x7eaacb62u, 0x2ad7309au, 0x87f4d34du}}
, .sourceIx = ty_w16
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_EXTEND_32_64] =
{ .tag = JET
, .jet = right_extend_32_64
, .cmr = {{0xdd6af1c8u, 0x01d26c0bu, 0x2edf83ceu, 0x67b172dfu, 0x6757d07fu, 0xb7c85468u, 0x6f42e576u, 0x8adcc9e7u}}
, .sourceIx = ty_w32
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_EXTEND_8_16] =
{ .tag = JET
, .jet = right_extend_8_16
, .cmr = {{0x1de201a8u, 0x6470a02bu, 0x2dfe48c6u, 0x6afe0673u, 0x5b475e88u, 0xd325cbf1u, 0x6042a910u, 0x24d2bed9u}}
, .sourceIx = ty_w8
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[RIGHT_EXTEND_8_32] =
{ .tag = JET
, .jet = right_extend_8_32
, .cmr = {{0x7e9c5cb3u, 0x5419ab06u, 0xe1220023u, 0x102be46au, 0xb6d96995u, 0xc423c6b1u, 0x4b9a6602u, 0x8aec5d75u}}
, .sourceIx = ty_w8
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_EXTEND_8_64] =
{ .tag = JET
, .jet = right_extend_8_64
, .cmr = {{0x49d246c2u, 0xa61cd39du, 0x7820dcd7u, 0x5eee847bu, 0xf057c01au, 0x63a3acbcu, 0xc9463e44u, 0xbc1e0b6cu}}
, .sourceIx = ty_w8
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_HIGH_16_32] =
{ .tag = JET
, .jet = right_pad_high_16_32
, .cmr = {{0xfe901fb4u, 0xf6ebdc4eu, 0xa2961998u, 0x9922b80fu, 0xa9ce2412u, 0x87fa5408u, 0x64362cccu, 0xe9f54b3bu}}
, .sourceIx = ty_w16
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_HIGH_16_64] =
{ .tag = JET
, .jet = right_pad_high_16_64
, .cmr = {{0xda90add3u, 0x1067ccfdu, 0xbee4cbfbu, 0x21de8e6au, 0xa4f93e00u, 0x2200711fu, 0x9984af6fu, 0xc01e2700u}}
, .sourceIx = ty_w16
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_HIGH_1_16] =
{ .tag = JET
, .jet = right_pad_high_1_16
, .cmr = {{0xe4cf116cu, 0x0880f73fu, 0x9952f700u, 0x81788498u, 0xe5084cbbu, 0x72cf841bu, 0xcd9167a6u, 0xeea264dcu}}
, .sourceIx = ty_b
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_HIGH_1_32] =
{ .tag = JET
, .jet = right_pad_high_1_32
, .cmr = {{0x1276036bu, 0xb94cfd92u, 0x0ab73164u, 0x3b76b119u, 0x72dd2654u, 0x3853444eu, 0x18d7f63fu, 0xcac091a3u}}
, .sourceIx = ty_b
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_HIGH_1_64] =
{ .tag = JET
, .jet = right_pad_high_1_64
, .cmr = {{0x38c99980u, 0xb1a99810u, 0x5111c56bu, 0xf8246509u, 0x65a509c4u, 0x7e1c76d9u, 0x00750a1fu, 0xee45c964u}}
, .sourceIx = ty_b
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_HIGH_1_8] =
{ .tag = JET
, .jet = right_pad_high_1_8
, .cmr = {{0xca72ceedu, 0x2d98dccdu, 0x81aa21f0u, 0xba21d1a0u, 0x87b6f252u, 0x07c24a58u, 0x0ada7e60u, 0x5f7982dfu}}
, .sourceIx = ty_b
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_HIGH_32_64] =
{ .tag = JET
, .jet = right_pad_high_32_64
, .cmr = {{0x17eb5911u, 0xf8549576u, 0x68eef463u, 0xb0cbae72u, 0x08529134u, 0xef5e56cdu, 0x33fbbc29u, 0xc28bbe92u}}
, .sourceIx = ty_w32
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_HIGH_8_16] =
{ .tag = JET
, .jet = right_pad_high_8_16
, .cmr = {{0xd26f0cc5u, 0xb261eb83u, 0x0e02df12u, 0xcc574425u, 0x9b4a43d9u, 0x75bd2e3du, 0x7c782811u, 0x761ff1d1u}}
, .sourceIx = ty_w8
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_HIGH_8_32] =
{ .tag = JET
, .jet = right_pad_high_8_32
, .cmr = {{0xbd2e5c92u, 0x60bf6f32u, 0x4d2b1f40u, 0xcbb12240u, 0x2f30d52fu, 0x6434e39fu, 0x8a09b839u, 0x7bc32e94u}}
, .sourceIx = ty_w8
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_HIGH_8_64] =
{ .tag = JET
, .jet = right_pad_high_8_64
, .cmr = {{0x941bf442u, 0xdbcf4f20u, 0x04a4b18bu, 0xeeb2adacu, 0x9f209feau, 0x4c4bd48cu, 0xede8dafau, 0xcf8843b7u}}
, .sourceIx = ty_w8
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_LOW_16_32] =
{ .tag = JET
, .jet = right_pad_low_16_32
, .cmr = {{0xbb387c29u, 0x2d59d713u, 0xad76f6ceu, 0xd5b596cfu, 0xd8385892u, 0x4f725f7du, 0x116b2807u, 0x5821925au}}
, .sourceIx = ty_w16
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_LOW_16_64] =
{ .tag = JET
, .jet = right_pad_low_16_64
, .cmr = {{0x0232326eu, 0xe1b206adu, 0x26349b55u, 0x3d7f2462u, 0x287320d6u, 0x30e42932u, 0x0740cbd3u, 0xeb4ef9beu}}
, .sourceIx = ty_w16
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_LOW_1_16] =
{ .tag = JET
, .jet = right_pad_low_1_16
, .cmr = {{0xd913f602u, 0xb35958d5u, 0x2abb20b0u, 0x2ce68961u, 0x6ffa66e0u, 0x2d73867du, 0x29181e11u, 0x93c9d243u}}
, .sourceIx = ty_b
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_LOW_1_32] =
{ .tag = JET
, .jet = right_pad_low_1_32
, .cmr = {{0x6b4033d9u, 0xfc6c876bu, 0x2e75d582u, 0xbb9b3c04u, 0xfa29dfb2u, 0x2c9e1a48u, 0x8e837c2fu, 0x39aa6160u}}
, .sourceIx = ty_b
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_LOW_1_64] =
{ .tag = JET
, .jet = right_pad_low_1_64
, .cmr = {{0x4e2b20ddu, 0x9d91857au, 0x49c820d0u, 0x6f435dd3u, 0xca791f17u, 0x7eeaf34au, 0xec36c454u, 0x19d16965u}}
, .sourceIx = ty_b
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_LOW_1_8] =
{ .tag = JET
, .jet = right_pad_low_1_8
, .cmr = {{0x24eee451u, 0xb26ba39du, 0x6bcc588bu, 0x720faf22u, 0x32767912u, 0xf67db329u, 0x060d90b7u, 0x1417b6c3u}}
, .sourceIx = ty_b
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_LOW_32_64] =
{ .tag = JET
, .jet = right_pad_low_32_64
, .cmr = {{0x52fb8bbcu, 0xef903231u, 0xa5b76791u, 0xe4652b38u, 0xbed8977fu, 0x5dab1795u, 0x55998db2u, 0x4d1d7c98u}}
, .sourceIx = ty_w32
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_LOW_8_16] =
{ .tag = JET
, .jet = right_pad_low_8_16
, .cmr = {{0x1719b279u, 0x74e84380u, 0x50882530u, 0xa1a42ed7u, 0xab3ca28du, 0x254adc37u, 0xfe5666fdu, 0x2f70b4e4u}}
, .sourceIx = ty_w8
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_LOW_8_32] =
{ .tag = JET
, .jet = right_pad_low_8_32
, .cmr = {{0xee2a8230u, 0xf283dc08u, 0x3b8e1944u, 0x8ba32497u, 0xe9318b4eu, 0x9e1bd4ebu, 0xe1bec524u, 0x476ab86du}}
, .sourceIx = ty_w8
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_PAD_LOW_8_64] =
{ .tag = JET
, .jet = right_pad_low_8_64
, .cmr = {{0x97da90d8u, 0x428e6b94u, 0xe6c13514u, 0x60dc0112u, 0x3e479c4au, 0xafbbd14cu, 0x78ad2fadu, 0x0a895ef3u}}
, .sourceIx = ty_w8
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_ROTATE_16] =
{ .tag = JET
, .jet = right_rotate_16
, .cmr = {{0xee7d1c1fu, 0x3d82da56u, 0x81dd8b50u, 0x69d537d8u, 0x9f2293aau, 0x605332ceu, 0x10c1c422u, 0x4a53ceeau}}
, .sourceIx = ty_pw4w16
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[RIGHT_ROTATE_32] =
{ .tag = JET
, .jet = right_rotate_32
, .cmr = {{0x892a28dbu, 0x324cd93cu, 0xf7f69c30u, 0x72a7b222u, 0xb88c818eu, 0xe0e5a1b8u, 0x97e50c58u, 0x1f2a2962u}}
, .sourceIx = ty_pw8w32
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_ROTATE_64] =
{ .tag = JET
, .jet = right_rotate_64
, .cmr = {{0x64314ff1u, 0x9040a376u, 0xf9fcf02eu, 0x7574149cu, 0x123f99c3u, 0x9071cd37u, 0x851f8f8cu, 0xdf0eed42u}}
, .sourceIx = ty_pw8w64
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_ROTATE_8] =
{ .tag = JET
, .jet = right_rotate_8
, .cmr = {{0x1581e0cau, 0x09f13684u, 0xfe3135c1u, 0xc6b6f9c4u, 0x89d7dd1eu, 0xf0a5f770u, 0x83bb0ed0u, 0x0b4df28fu}}
, .sourceIx = ty_pw4w8
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[RIGHT_SHIFT_16] =
{ .tag = JET
, .jet = right_shift_16
, .cmr = {{0x5b4ec462u, 0xd4e2ed89u, 0xffe3fd40u, 0x5932c797u, 0x80286120u, 0x3ecb61d5u, 0xb59a73b0u, 0xfbfc4e84u}}
, .sourceIx = ty_pw4w16
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[RIGHT_SHIFT_32] =
{ .tag = JET
, .jet = right_shift_32
, .cmr = {{0xb2861a48u, 0xb2054176u, 0x91b6347fu, 0xe75ebea5u, 0x4560cf81u, 0x3814ac31u, 0x639170dbu, 0x92b947d6u}}
, .sourceIx = ty_pw8w32
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_SHIFT_64] =
{ .tag = JET
, .jet = right_shift_64
, .cmr = {{0xd33942bfu, 0x18618a10u, 0x4a570754u, 0x7f78ab72u, 0x941f4ee8u, 0x13216c0cu, 0xe520f356u, 0x60fdbf81u}}
, .sourceIx = ty_pw8w64
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_SHIFT_8] =
{ .tag = JET
, .jet = right_shift_8
, .cmr = {{0x737912aeu, 0x323250c0u, 0x4e516e39u, 0x66ce947eu, 0x65326f47u, 0x468ac931u, 0xc163c3b0u, 0x2de41245u}}
, .sourceIx = ty_pw4w8
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[RIGHT_SHIFT_WITH_16] =
{ .tag = JET
, .jet = right_shift_with_16
, .cmr = {{0x1e181c33u, 0x1693594cu, 0x6e0e8fdeu, 0xb40a81a3u, 0xaf8f56b7u, 0xa560de64u, 0x41303f65u, 0xf4fc937cu}}
, .sourceIx = ty_pbpw4w16
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[RIGHT_SHIFT_WITH_32] =
{ .tag = JET
, .jet = right_shift_with_32
, .cmr = {{0x69dbe190u, 0xd72d77d0u, 0xd0dcf325u, 0xde965922u, 0x14581f11u, 0xe9edca93u, 0xe2f92848u, 0x2b5e77a7u}}
, .sourceIx = ty_pbpw8w32
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHT_SHIFT_WITH_64] =
{ .tag = JET
, .jet = right_shift_with_64
, .cmr = {{0x2d0ab883u, 0x0469280eu, 0x2a28993cu, 0x5a05f56bu, 0x91a8aeb0u, 0x34ccebe0u, 0x9c50f13eu, 0xa78ddafcu}}
, .sourceIx = ty_pbpw8w64
, .targetIx = ty_w64
, .cost = 150 /* milli weight units */
}
,[RIGHT_SHIFT_WITH_8] =
{ .tag = JET
, .jet = right_shift_with_8
, .cmr = {{0x1bdbdc8du, 0x8b749ba3u, 0xda757558u, 0x7d999300u, 0x72603f27u, 0x5f7bd2f3u, 0x24a34951u, 0xd4461b21u}}
, .sourceIx = ty_pbpw4w8
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_16_1] =
{ .tag = JET
, .jet = rightmost_16_1
, .cmr = {{0xe129a8aeu, 0x880f51cau, 0x2a94db44u, 0xedeca1c3u, 0xa766b73eu, 0x98970b11u, 0x98ade216u, 0xae69cd2du}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_16_2] =
{ .tag = JET
, .jet = rightmost_16_2
, .cmr = {{0x8d0f68dau, 0xdf546c5eu, 0xd36f3470u, 0x5802b0ceu, 0x839a63e5u, 0x74497785u, 0x243008abu, 0x427e456bu}}
, .sourceIx = ty_w16
, .targetIx = ty_w2
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_16_4] =
{ .tag = JET
, .jet = rightmost_16_4
, .cmr = {{0xb0d41395u, 0x41ecab2cu, 0x16fc1a87u, 0x989bdd04u, 0x5322efb1u, 0xe70bc1f7u, 0xb04d43b2u, 0x8bb349ffu}}
, .sourceIx = ty_w16
, .targetIx = ty_w4
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_16_8] =
{ .tag = JET
, .jet = rightmost_16_8
, .cmr = {{0x0f03fa0fu, 0xa6ceb55du, 0xf99b20d9u, 0xefcf3710u, 0xa708a284u, 0xa95c334cu, 0x1da3cbfeu, 0x02fb9467u}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_32_1] =
{ .tag = JET
, .jet = rightmost_32_1
, .cmr = {{0x8f5e5263u, 0xbb8ef800u, 0xc99d0c23u, 0xfcbaa319u, 0x8a6abdf0u, 0x08581e8cu, 0x891052b4u, 0x0ca7f7a4u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_32_16] =
{ .tag = JET
, .jet = rightmost_32_16
, .cmr = {{0xb9a23e1bu, 0xf7c68143u, 0x513074c9u, 0x39bd73c9u, 0xbf8eb5aau, 0xce8415ffu, 0x01022fcau, 0x65b3a342u}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_32_2] =
{ .tag = JET
, .jet = rightmost_32_2
, .cmr = {{0xabf3238du, 0x3cbf0bf3u, 0x5a83961fu, 0xb9f904b5u, 0x6d3a9e0eu, 0x35c89df8u, 0x72c9c938u, 0xd344a54au}}
, .sourceIx = ty_w32
, .targetIx = ty_w2
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_32_4] =
{ .tag = JET
, .jet = rightmost_32_4
, .cmr = {{0xf7eed2ecu, 0x805906feu, 0xb3ac27f2u, 0xdee53b58u, 0xc3b13e40u, 0xe2bc3e8bu, 0x10632ed9u, 0xc0e7ca5fu}}
, .sourceIx = ty_w32
, .targetIx = ty_w4
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_32_8] =
{ .tag = JET
, .jet = rightmost_32_8
, .cmr = {{0xf3e439edu, 0x9883c6a6u, 0xb9072053u, 0x2eb4e043u, 0xe89a35f0u, 0xb5295fd5u, 0x02a0b0b2u, 0x436bd213u}}
, .sourceIx = ty_w32
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_64_1] =
{ .tag = JET
, .jet = rightmost_64_1
, .cmr = {{0xc96be3e3u, 0x3548258eu, 0x30717b30u, 0x817e440fu, 0x0af4b189u, 0x0edfcf7fu, 0xdcb39cb9u, 0xefff471du}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_64_16] =
{ .tag = JET
, .jet = rightmost_64_16
, .cmr = {{0x5d555f83u, 0xe48087dbu, 0x0c415dadu, 0x17f081d4u, 0xf6b760e9u, 0x95f272bbu, 0xb6e4cb42u, 0xd0f50325u}}
, .sourceIx = ty_w64
, .targetIx = ty_w16
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_64_2] =
{ .tag = JET
, .jet = rightmost_64_2
, .cmr = {{0xa9cb1343u, 0xdbd522b9u, 0x1b6482e4u, 0xbae62b0eu, 0x5f829868u, 0x7e642333u, 0x5c6df506u, 0xdc425b90u}}
, .sourceIx = ty_w64
, .targetIx = ty_w2
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_64_32] =
{ .tag = JET
, .jet = rightmost_64_32
, .cmr = {{0x4733b192u, 0x59800964u, 0x99b7877cu, 0x04e001bau, 0xd3325b2eu, 0xcab348e5u, 0xadd720d0u, 0x7b1b4a3au}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_64_4] =
{ .tag = JET
, .jet = rightmost_64_4
, .cmr = {{0x89daf7beu, 0x2cde58f0u, 0x4e8dee58u, 0xa4391091u, 0x2c096e95u, 0xe146c19bu, 0x00f54fe8u, 0x74700740u}}
, .sourceIx = ty_w64
, .targetIx = ty_w4
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_64_8] =
{ .tag = JET
, .jet = rightmost_64_8
, .cmr = {{0x1dfb2befu, 0x4cae4507u, 0x922708e5u, 0xa5709949u, 0x3fbe2115u, 0x98eec0bfu, 0xe0e77b3du, 0x41ec89abu}}
, .sourceIx = ty_w64
, .targetIx = ty_w8
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_8_1] =
{ .tag = JET
, .jet = rightmost_8_1
, .cmr = {{0xceabd5cau, 0x9fd9162fu, 0x995e3735u, 0x77047aa4u, 0xba71f807u, 0xc711f60bu, 0x08eb6a1cu, 0xfc381c9cu}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_8_2] =
{ .tag = JET
, .jet = rightmost_8_2
, .cmr = {{0x39b2f037u, 0xb6a08186u, 0x115065f3u, 0x85057af3u, 0xde3b9f0au, 0x9bda6833u, 0x71462259u, 0x413028ecu}}
, .sourceIx = ty_w8
, .targetIx = ty_w2
, .cost = 150 /* milli weight units */
}
,[RIGHTMOST_8_4] =
{ .tag = JET
, .jet = rightmost_8_4
, .cmr = {{0xa7a94949u, 0x0d1a00deu, 0xfe5f6151u, 0x2923850fu, 0x51e347c0u, 0x6a8d76a0u, 0xcdab87eeu, 0xe29a5defu}}
, .sourceIx = ty_w8
, .targetIx = ty_w4
, .cost = 150 /* milli weight units */
}
,[SCALAR_ADD] =
{ .tag = JET
, .jet = scalar_add
, .cmr = {{0x4ee9a96cu, 0xef496cf4u, 0xa8fc4e8au, 0x8bc0d159u, 0xca5ffb87u, 0x53643a8au, 0xdf638ae8u, 0x9bbbb345u}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 962 /* milli weight units */
}
,[SCALAR_INVERT] =
{ .tag = JET
, .jet = scalar_invert
, .cmr = {{0x12b855e5u, 0xebaa7f8bu, 0xb44fee26u, 0x16a051adu, 0x00499f9du, 0xf2a2adf7u, 0x9973e9dbu, 0x8185759cu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 4025 /* milli weight units */
}
,[SCALAR_IS_ZERO] =
{ .tag = JET
, .jet = scalar_is_zero
, .cmr = {{0x4d252803u, 0x457b83b8u, 0x5b987f04u, 0x8733fbeeu, 0xdeaa8d25u, 0x9d320507u, 0x450019c6u, 0x22034f26u}}
, .sourceIx = ty_w256
, .targetIx = ty_b
, .cost = 569 /* milli weight units */
}
,[SCALAR_MULTIPLY] =
{ .tag = JET
, .jet = scalar_multiply
, .cmr = {{0x8756f2dcu, 0x310cdeb6u, 0x4045c44cu, 0x2366e14bu, 0xc1fafa17u, 0x159f2d7bu, 0x489bd945u, 0x3ee37ea0u}}
, .sourceIx = ty_w512
, .targetIx = ty_w256
, .cost = 1230 /* milli weight units */
}
,[SCALAR_MULTIPLY_LAMBDA] =
{ .tag = JET
, .jet = scalar_multiply_lambda
, .cmr = {{0x2b31d39eu, 0xc4ff3723u, 0x1a1b3ebeu, 0x759d41e0u, 0xf5ce3449u, 0x2d4bd3c2u, 0x0988c3f2u, 0xf7c53edcu}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 984 /* milli weight units */
}
,[SCALAR_NEGATE] =
{ .tag = JET
, .jet = scalar_negate
, .cmr = {{0xfc2ed187u, 0x50a22181u, 0xaf5b8141u, 0x969273cau, 0xaf72cc11u, 0x31e1082cu, 0xf008f5cau, 0x0909c216u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 851 /* milli weight units */
}
,[SCALAR_NORMALIZE] =
{ .tag = JET
, .jet = scalar_normalize
, .cmr = {{0x797cffa8u, 0x0859cab7u, 0xcdbf3b9du, 0xe6e0a8b7u, 0x91484eaau, 0xbacbdfbau, 0xeb01e238u, 0x95e96199u}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 808 /* milli weight units */
}
,[SCALAR_SQUARE] =
{ .tag = JET
, .jet = scalar_square
, .cmr = {{0x77b43c60u, 0x38ad80b4u, 0x6d3a76e2u, 0x12b3a8c0u, 0xd2f06307u, 0xbc456e40u, 0xb5d6f4a3u, 0xa50e264du}}
, .sourceIx = ty_w256
, .targetIx = ty_w256
, .cost = 947 /* milli weight units */
}
,[SCALE] =
{ .tag = JET
, .jet = scale
, .cmr = {{0x574ce760u, 0x24a5f011u, 0xa2d0bcebu, 0xb0f81a15u, 0xe0f9d06bu, 0x34f20994u, 0x33cb114fu, 0x53468d4fu}}
, .sourceIx = ty_pw256pw512w256
, .targetIx = ty_pw512w256
, .cost = 75377 /* milli weight units */
}
,[SCRIPT_CMR] =
{ .tag = JET
, .jet = script_cmr
, .cmr = {{0xb8ad3723u, 0x7699301fu, 0xb33e6928u, 0xa4101f93u, 0x169ad1f4u, 0x128b9e1eu, 0x86bdbb6cu, 0xdc274c38u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 281 /* milli weight units */
}
,[SHA_256_BLOCK] =
{ .tag = JET
, .jet = sha_256_block
, .cmr = {{0x94a36a40u, 0x83309e0bu, 0x86de77d0u, 0xfb48d9d3u, 0x31e2d2f1u, 0x67740b60u, 0x6e60574au, 0xf438cd86u}}
, .sourceIx = ty_pw256w512
, .targetIx = ty_w256
, .cost = 986 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_1] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_1
, .cmr = {{0x8a1d2570u, 0x87b32ccdu, 0xc3320037u, 0x4e6e95c8u, 0x75a05e54u, 0x8122323fu, 0x6b7ab9c0u, 0x7eb9b6eeu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w8
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 1600 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_128] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_128
, .cmr = {{0xe7772cb9u, 0xc0ec421au, 0xb8a789d4u, 0x5cd64661u, 0xf433dd7du, 0x3d2c94dcu, 0x1f1c4f3au, 0xf8c780abu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w1Ki
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 3921 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_16] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_16
, .cmr = {{0xf0f4cf99u, 0xad58a038u, 0x5e16b87du, 0xbf3271c4u, 0x7524defdu, 0x78f11bbcu, 0x7471fe4du, 0xa94aebadu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w128
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 2275 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_2] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_2
, .cmr = {{0x7998c7c2u, 0xbd814b0cu, 0x0f403f58u, 0xc576ea56u, 0x407d25eeu, 0x229fae62u, 0x5bcab0c6u, 0x20a2a29cu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w16
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 3772 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_256] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_256
, .cmr = {{0xa8749961u, 0xb31afe2fu, 0xb553b70bu, 0x4cea787du, 0xca472584u, 0x54d583dcu, 0x45a0780du, 0x5e2a2a50u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w2Ki
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 6211 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_32] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_32
, .cmr = {{0xf22068b7u, 0x76a3787fu, 0x9d52ec2au, 0x9591951fu, 0x8a73f009u, 0x60091235u, 0x8a2a1e15u, 0x864e80b2u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w256
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 4599 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_4] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_4
, .cmr = {{0x40e66decu, 0xa132f5aeu, 0x0c54937bu, 0x95ccaca1u, 0x1267a4adu, 0xca702887u, 0xb6e408edu, 0x761530bcu}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w32
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 3515 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_512] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_512
, .cmr = {{0x5a96ee66u, 0x8b52f63fu, 0x7bdbaae3u, 0xcc38e393u, 0xef24b3a9u, 0x67856f2cu, 0xd89d83bau, 0x4ccbda8du}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w4Ki
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 10936 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_64] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_64
, .cmr = {{0x36ede6b6u, 0x8ab6e4dbu, 0x31efc7a7u, 0xeae7ec3fu, 0x7ceead93u, 0x91103b8du, 0xcb406091u, 0x57fb8702u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w512
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 3111 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_8] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_8
, .cmr = {{0xac1ff0fbu, 0x0cf71d71u, 0x13db42aau, 0x1ddb8955u, 0x96e645d7u, 0x63b8df5eu, 0x8725f514u, 0x4c399588u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256w64
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 1625 /* milli weight units */
}
,[SHA_256_CTX_8_ADD_BUFFER_511] =
{ .tag = JET
, .jet = sha_256_ctx_8_add_buffer_511
, .cmr = {{0x6901ac0eu, 0x30fd59ceu, 0xc879d169u, 0x3b267959u, 0x35690784u, 0x4b577edcu, 0x3ce0e3f7u, 0x14a8ef31u}}
, .sourceIx = ty_pppmw256pmw128pmw64pmw32pmw16mw8pw64w256pmw2Kipmw1Kipmw512pmw256pmw128pmw64pmw32pmw16mw8
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 14290 /* milli weight units */
}
,[SHA_256_CTX_8_FINALIZE] =
{ .tag = JET
, .jet = sha_256_ctx_8_finalize
, .cmr = {{0x84615954u, 0x007ed823u, 0xd60546d7u, 0x5b04b909u, 0xbc909206u, 0x371473dau, 0xc70e1268u, 0x047708cbu}}
, .sourceIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .targetIx = ty_w256
, .cost = 2111 /* milli weight units */
}
,[SHA_256_CTX_8_INIT] =
{ .tag = JET
, .jet = sha_256_ctx_8_init
, .cmr = {{0x6adda7d7u, 0x339f7dceu, 0x4d62ff82u, 0x2816da8du, 0xf56af624u, 0x3fa073a2u, 0x5c4c7cb5u, 0x7e0112b3u}}
, .sourceIx = ty_u
, .targetIx = ty_ppmw256pmw128pmw64pmw32pmw16mw8pw64w256
, .cost = 184 /* milli weight units */
}
,[SHA_256_IV] =
{ .tag = JET
, .jet = sha_256_iv
, .cmr = {{0x6a18e6e7u, 0x64af800du, 0xc6faeb07u, 0x54bf0b17u, 0x329f9828u, 0x1d13f515u, 0x7700fa6au, 0x1d6d5d42u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 129 /* milli weight units */
}
,[SIG_ALL_HASH] =
{ .tag = JET
, .jet = sig_all_hash
, .cmr = {{0x0dc3f10bu, 0xbbbf9aa4u, 0x91bb8814u, 0x631d3b6du, 0x4195f82cu, 0x9773bbcbu, 0x2da3ef0cu, 0xf0cd94d2u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 265 /* milli weight units */
}
,[SOME_1] =
{ .tag = JET
, .jet = some_1
, .cmr = {{0x0b9cb7b4u, 0x7deb4f9du, 0x95d5c020u, 0x001fd009u, 0xa2f10ce5u, 0xd918d818u, 0x1e259315u, 0xfe8eac53u}}
, .sourceIx = ty_b
, .targetIx = ty_b
, .cost = 104 /* milli weight units */
}
,[SOME_16] =
{ .tag = JET
, .jet = some_16
, .cmr = {{0x30d814ffu, 0xb49278b4u, 0x25007b9du, 0xe279f76fu, 0x4a6da4c0u, 0x34634abbu, 0x87110ecbu, 0xea2ce429u}}
, .sourceIx = ty_w16
, .targetIx = ty_b
, .cost = 129 /* milli weight units */
}
,[SOME_32] =
{ .tag = JET
, .jet = some_32
, .cmr = {{0x69279190u, 0x3be7d9e4u, 0xc54772bau, 0x88a48615u, 0x46361218u, 0xdd8a26ceu, 0xed699bcfu, 0x77c09909u}}
, .sourceIx = ty_w32
, .targetIx = ty_b
, .cost = 183 /* milli weight units */
}
,[SOME_64] =
{ .tag = JET
, .jet = some_64
, .cmr = {{0xfa9b0160u, 0xc72715ffu, 0xfd1d94dau, 0x19978828u, 0x09b462bbu, 0x144acecbu, 0x43054468u, 0xe63786b5u}}
, .sourceIx = ty_w64
, .targetIx = ty_b
, .cost = 139 /* milli weight units */
}
,[SOME_8] =
{ .tag = JET
, .jet = some_8
, .cmr = {{0x0bd7ab43u, 0x80c8f45au, 0xca7cac97u, 0x2886ceefu, 0x23ba8421u, 0x0c5c4d96u, 0x9b1f59b1u, 0x832c1d36u}}
, .sourceIx = ty_w8
, .targetIx = ty_b
, .cost = 104 /* milli weight units */
}
,[SUBTRACT_16] =
{ .tag = JET
, .jet = subtract_16
, .cmr = {{0x0cd3ab73u, 0xe5ce2a44u, 0xf2d1c332u, 0xa1ed5aefu, 0x5bcb604fu, 0x721b15b8u, 0x010dd54fu, 0x40c6aca7u}}
, .sourceIx = ty_w32
, .targetIx = ty_pbw16
, .cost = 237 /* milli weight units */
}
,[SUBTRACT_32] =
{ .tag = JET
, .jet = subtract_32
, .cmr = {{0xe0de6876u, 0x259d5a00u, 0x4b3016d3u, 0x5815db41u, 0xbcecdbfau, 0x18d37d99u, 0x204e4957u, 0xad2c4d0eu}}
, .sourceIx = ty_w64
, .targetIx = ty_pbw32
, .cost = 186 /* milli weight units */
}
,[SUBTRACT_64] =
{ .tag = JET
, .jet = subtract_64
, .cmr = {{0xffe673eeu, 0x8edc729au, 0x47eced3au, 0x677f85b1u, 0xdae714a5u, 0x100c4949u, 0x73abcb32u, 0x59a3c756u}}
, .sourceIx = ty_w128
, .targetIx = ty_pbw64
, .cost = 315 /* milli weight units */
}
,[SUBTRACT_8] =
{ .tag = JET
, .jet = subtract_8
, .cmr = {{0xbda59813u, 0x96478eb3u, 0x6f8592a7u, 0x509fa487u, 0x7c50b2bfu, 0x9165e5b7u, 0x9635bf8bu, 0xcb84d442u}}
, .sourceIx = ty_w16
, .targetIx = ty_pbw8
, .cost = 149 /* milli weight units */
}
,[SWU] =
{ .tag = JET
, .jet = swu
, .cmr = {{0x69459b6du, 0xd10a63dfu, 0x37dedf18u, 0x6cb4d208u, 0xd8c03961u, 0x1cecdd09u, 0xcfe07ac9u, 0x1d01422fu}}
, .sourceIx = ty_w256
, .targetIx = ty_w512
, .cost = 10956 /* milli weight units */
}
,[TAP_ENV_HASH] =
{ .tag = JET
, .jet = tap_env_hash
, .cmr = {{0x59e04eeeu, 0x36883dd5u, 0xe7c2695du, 0x7c9938c0u, 0x6d983fbau, 0x88dc2a04u, 0x843ab80bu, 0x68f199ecu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 301 /* milli weight units */
}
,[TAPLEAF_HASH] =
{ .tag = JET
, .jet = tapleaf_hash
, .cmr = {{0xea815658u, 0xff9a2716u, 0x420d4591u, 0x5d66070bu, 0xe4116c1cu, 0x707e2694u, 0xd3665845u, 0x20c22469u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 279 /* milli weight units */
}
,[TAPLEAF_VERSION] =
{ .tag = JET
, .jet = tapleaf_version
, .cmr = {{0x303ef4deu, 0x618e7f08u, 0x67794828u, 0x2dd42d57u, 0xd644c41cu, 0x18c11c13u, 0x0a1be5a6u, 0xe254e3e9u}}
, .sourceIx = ty_u
, .targetIx = ty_w8
, .cost = 141 /* milli weight units */
}
,[TAPPATH] =
{ .tag = JET
, .jet = tappath
, .cmr = {{0x5fd71c6fu, 0xf67ba426u, 0x3c8256feu, 0xcee1e2ecu, 0x1dcf45a8u, 0xb3845062u, 0x70151780u, 0xaacf1c32u}}
, .sourceIx = ty_w8
, .targetIx = ty_mw256
, .cost = 143 /* milli weight units */
}
,[TAPPATH_HASH] =
{ .tag = JET
, .jet = tappath_hash
, .cmr = {{0x62af75f4u, 0xf37c0ff2u, 0x7537e054u, 0x3a134802u, 0x66a5ad12u, 0xce53df1fu, 0xbac111eau, 0xa93d277cu}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 282 /* milli weight units */
}
,[TOTAL_FEE] =
{ .tag = JET
, .jet = total_fee
, .cmr = {{0xcc69d24cu, 0x5dd852cdu, 0xefcaa74du, 0x3140467fu, 0xbe8d08a7u, 0x709422eeu, 0xc28ed632u, 0xb28aba63u}}
, .sourceIx = ty_w256
, .targetIx = ty_w64
, .cost = 397 /* milli weight units */
}
,[TRANSACTION_ID] =
{ .tag = JET
, .jet = transaction_id
, .cmr = {{0xab4bf478u, 0x2d358cd3u, 0x1f22e066u, 0x64167078u, 0x457c76e3u, 0xfa8e421cu, 0x7929de11u, 0x310b07d9u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 281 /* milli weight units */
}
,[TX_HASH] =
{ .tag = JET
, .jet = tx_hash
, .cmr = {{0xb7e0a2dcu, 0x5ca11ce5u, 0x82a7aa29u, 0x9a51b23eu, 0x66efe623u, 0x602a7b7du, 0x434eec51u, 0xaf245a07u}}
, .sourceIx = ty_u
, .targetIx = ty_w256
, .cost = 290 /* milli weight units */
}
,[TX_IS_FINAL] =
{ .tag = JET
, .jet = tx_is_final
, .cmr = {{0xeb8e83d1u, 0xe02c3ce7u, 0xaf2d28f0u, 0xcec04314u, 0x80dc2f38u, 0x85c9913au, 0x50727e43u, 0xd0bdaf88u}}
, .sourceIx = ty_u
, .targetIx = ty_b
, .cost = 128 /* milli weight units */
}
,[TX_LOCK_DISTANCE] =
{ .tag = JET
, .jet = tx_lock_distance
, .cmr = {{0xa37893c9u, 0x7c9b950eu, 0x0f7f1045u, 0xc8d8473au, 0xc8336aaeu, 0xe9ea1fadu, 0x6b2a4061u, 0x729149c6u}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 133 /* milli weight units */
}
,[TX_LOCK_DURATION] =
{ .tag = JET
, .jet = tx_lock_duration
, .cmr = {{0x4d6987ddu, 0x45f78d5eu, 0x43f93851u, 0x64a0bd08u, 0x80752ab8u, 0x11b38bd2u, 0x97da0016u, 0x1526a9cau}}
, .sourceIx = ty_u
, .targetIx = ty_w16
, .cost = 146 /* milli weight units */
}
,[TX_LOCK_HEIGHT] =
{ .tag = JET
, .jet = tx_lock_height
, .cmr = {{0x16ab830fu, 0xace51fe4u, 0xe18089ecu, 0xa1b55234u, 0x36aa45efu, 0x84132182u, 0xc7cc6583u, 0x6fd1342cu}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 132 /* milli weight units */
}
,[TX_LOCK_TIME] =
{ .tag = JET
, .jet = tx_lock_time
, .cmr = {{0xaf112fc8u, 0xeed3c33bu, 0xc7b5ea04u, 0xccab8699u, 0x1953f2a2u, 0xaaf3d87du, 0x6c2c4314u, 0x3d426f56u}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 136 /* milli weight units */
}
,[VERIFY] =
{ .tag = JET
, .jet = verify
, .cmr = {{0xf11c9481u, 0xe71863a2u, 0x4453c3e2u, 0x13046499u, 0xa03a9a0fu, 0x993be3c4u, 0x8e9d1f40u, 0x5d97947cu}}
, .sourceIx = ty_b
, .targetIx = ty_u
, .cost = 144 /* milli weight units */
}
,[VERSION] =
{ .tag = JET
, .jet = version
, .cmr = {{0x22215300u, 0x9f0863dau, 0x5cec8ffau, 0xa4a017d8u, 0xe4ff2566u, 0xfa9c03e7u, 0x431a0902u, 0xd56a24dcu}}
, .sourceIx = ty_u
, .targetIx = ty_w32
, .cost = 188 /* milli weight units */
}
,[XOR_1] =
{ .tag = JET
, .jet = xor_1
, .cmr = {{0x77b714e6u, 0x89c9d6a4u, 0x8fd1add8u, 0x6522823du, 0xebc70df6u, 0xa7fe4bf2u, 0xb85de549u, 0xe0cd0a05u}}
, .sourceIx = ty_w2
, .targetIx = ty_b
, .cost = 135 /* milli weight units */
}
,[XOR_16] =
{ .tag = JET
, .jet = xor_16
, .cmr = {{0xca363551u, 0x35a86a11u, 0x686c01aau, 0x35f25b97u, 0xfaeedabfu, 0xdec8df08u, 0xd2c0f665u, 0x0833f93fu}}
, .sourceIx = ty_w32
, .targetIx = ty_w16
, .cost = 188 /* milli weight units */
}
,[XOR_32] =
{ .tag = JET
, .jet = xor_32
, .cmr = {{0xffe2c8eeu, 0x96d55797u, 0x81c43662u, 0x88d95071u, 0x85e461ccu, 0xc40a45bbu, 0xcc559489u, 0xd3c69612u}}
, .sourceIx = ty_w64
, .targetIx = ty_w32
, .cost = 204 /* milli weight units */
}
,[XOR_64] =
{ .tag = JET
, .jet = xor_64
, .cmr = {{0x5b3bb7b1u, 0x8c7098f4u, 0xe5cd1497u, 0x22ac7309u, 0xce66a3e2u, 0x19c61b33u, 0x3f313358u, 0x3a7b572du}}
, .sourceIx = ty_w128
, .targetIx = ty_w64
, .cost = 207 /* milli weight units */
}
,[XOR_8] =
{ .tag = JET
, .jet = xor_8
, .cmr = {{0xff3e5262u, 0x02ff89cfu, 0xf7bbe70fu, 0xdbf9f97du, 0x23c12f6eu, 0x2bb8bbe8u, 0x304ac70fu, 0x61c1cf2cu}}
, .sourceIx = ty_w16
, .targetIx = ty_w8
, .cost = 135 /* milli weight units */
}
,[XOR_XOR_1] =
{ .tag = JET
, .jet = xor_xor_1
, .cmr = {{0x2252a986u, 0x08d20bd4u, 0x11317a20u, 0x15c15698u, 0x70a62c95u, 0x3a6165fbu, 0xe977b40du, 0x6ccea495u}}
, .sourceIx = ty_pbw2
, .targetIx = ty_b
, .cost = 258 /* milli weight units */
}
,[XOR_XOR_16] =
{ .tag = JET
, .jet = xor_xor_16
, .cmr = {{0xa1f2d633u, 0xbf9889a0u, 0x8a42512au, 0x7893a679u, 0x9dc47aa8u, 0x29ff8f57u, 0x7c5bc975u, 0x66c4d3feu}}
, .sourceIx = ty_pw16w32
, .targetIx = ty_w16
, .cost = 235 /* milli weight units */
}
,[XOR_XOR_32] =
{ .tag = JET
, .jet = xor_xor_32
, .cmr = {{0x0d5ff581u, 0x23ba0daeu, 0x3b3240a6u, 0x31052af2u, 0xe87b52b6u, 0x37a2cbd3u, 0x37d22593u, 0x70628741u}}
, .sourceIx = ty_pw32w64
, .targetIx = ty_w32
, .cost = 251 /* milli weight units */
}
,[XOR_XOR_64] =
{ .tag = JET
, .jet = xor_xor_64
, .cmr = {{0x783f49a1u, 0x9d4f4aaeu, 0x4d3c1d6cu, 0xcf83156du, 0xc55d0b5cu, 0x08cf5923u, 0x36584cb1u, 0x3167c6cau}}
, .sourceIx = ty_pw64w128
, .targetIx = ty_w64
, .cost = 285 /* milli weight units */
}
,[XOR_XOR_8] =
{ .tag = JET
, .jet = xor_xor_8
, .cmr = {{0x83a980ccu, 0x61068524u, 0x88105d3cu, 0xee10f351u, 0x13b8c9f7u, 0x4664e7ceu, 0x6d4ec091u, 0x2bc29bc7u}}
, .sourceIx = ty_pw8w16
, .targetIx = ty_w8
, .cost = 258 /* milli weight units */
}
