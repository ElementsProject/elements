// Copyright (c) 2012-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "rpc/server.h"
#include "rpc/client.h"

#include "base58.h"
#include "netbase.h"

#include "test/test_bitcoin.h"

#include <boost/algorithm/string.hpp>
#include <boost/assign/list_of.hpp>
#include <boost/test/unit_test.hpp>

#include <univalue.h>

UniValue CallRPC(std::string args)
{
    std::vector<std::string> vArgs;
    boost::split(vArgs, args, boost::is_any_of(" \t"));
    std::string strMethod = vArgs[0];
    vArgs.erase(vArgs.begin());
    JSONRPCRequest request;
    request.strMethod = strMethod;
    request.params = RPCConvertValues(strMethod, vArgs);
    request.fHelp = false;
    BOOST_CHECK(tableRPC[strMethod]);
    rpcfn_type method = tableRPC[strMethod]->actor;
    try {
        UniValue result = (*method)(request);
        return result;
    }
    catch (const UniValue& objError) {
        throw std::runtime_error(find_value(objError, "message").get_str());
    }
}


BOOST_FIXTURE_TEST_SUITE(rpc_tests, TestingSetup)

BOOST_AUTO_TEST_CASE(rpc_rawparams)
{
    // Test raw transaction API argument handling
    UniValue r;

    BOOST_CHECK_THROW(CallRPC("getrawtransaction"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("getrawtransaction not_hex"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("getrawtransaction a3b807410df0b60fcb9736768df5823938b2f838694939ba45f3c0a1bff150ed not_int"), std::runtime_error);

    BOOST_CHECK_THROW(CallRPC("createrawtransaction"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("createrawtransaction null null"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("createrawtransaction not_array"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("createrawtransaction [] []"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("createrawtransaction {} {}"), std::runtime_error);
    BOOST_CHECK_NO_THROW(CallRPC("createrawtransaction [] {}"));
    BOOST_CHECK_THROW(CallRPC("createrawtransaction [] {} extra"), std::runtime_error);

    BOOST_CHECK_THROW(CallRPC("decoderawtransaction"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("decoderawtransaction null"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("decoderawtransaction DEADBEEF"), std::runtime_error);
    std::string rawtx = "01000000000132313029282726252423222120191817161514131211100908070605040302010000000000feffffff010121667c3dcc51290904a6a9eae27337e6ff5602d0deb5ca501f77be96de63f60901000000000000000000036a01de69000000";
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("decoderawtransaction ")+rawtx));
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "size").get_int(), 99);
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "version").get_int(), 1);
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "locktime").get_int(), 105);
    BOOST_CHECK_THROW(r = CallRPC(std::string("decoderawtransaction ")+rawtx+" extra"), std::runtime_error);

    BOOST_CHECK_THROW(CallRPC("signrawtransaction"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("signrawtransaction null"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("signrawtransaction ff00"), std::runtime_error);
    BOOST_CHECK_NO_THROW(CallRPC(std::string("signrawtransaction ")+rawtx));
    BOOST_CHECK_NO_THROW(CallRPC(std::string("signrawtransaction ")+rawtx+" null null NONE|ANYONECANPAY"));
    BOOST_CHECK_NO_THROW(CallRPC(std::string("signrawtransaction ")+rawtx+" [] [] NONE|ANYONECANPAY"));
    BOOST_CHECK_THROW(CallRPC(std::string("signrawtransaction ")+rawtx+" null null badenum"), std::runtime_error);

    // Only check failure cases for sendrawtransaction, there's no network to send to...
    BOOST_CHECK_THROW(CallRPC("sendrawtransaction"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("sendrawtransaction null"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("sendrawtransaction DEADBEEF"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC(std::string("sendrawtransaction ")+rawtx+" extra"), std::runtime_error);

    // Check a more advanced rawtx case with blinds and witness data (elements specific)
    std::string rawtx2 = "0200000001013dbc5d47f9275524ed705eddf72a53fef4adcc6f72862307bbd53f767285babd0000000000ffffffff040a2a8f37f85eacbe4435f078d03536bda4903a746ce6e42cb7faad7c782366c37408c268a0afce0f59f70d022e105d607fa0a4c6f65110e73ccd9640ebdd1272e4cf02955a2594eec93612be0012f572a8b0462b1d30d222042a08e342eaa3bec724de1976a91480b13c111909db1f7acfaffb9bcdb1fda579d08588ac0a27d954a5459ab030f832a32e96d0bc8c7aec911dca1460b1395ace8bf5bc667008b20395fc3202f78253102cc7c5206fafd2560bee394f36883249e32765402dd60276b93cc268ffbbe61f3a159127a5bfbb41b72cad63352000e42e55383c8b1fd11976a91474ce2e414059470ddfc7b5e21370e1d00e7bc9d988ac0121667c3dcc51290904a6a9eae27337e6ff5602d0deb5ca501f77be96de63f60901000000000000000000036a01de0121667c3dcc51290904a6a9eae27337e6ff5602d0deb5ca501f77be96de63f609010000000000989680000000000000000000430100016c8d770ce2bfba6b762b4394eff906ef161069eecd547c8c657985c3d2485f85c69ff9f0ba30ae987a2f5a84a95a96185393a8a9db4762484b10214a15c7d940fd2d0e602c00000000000000016f0c18bc2c107e145ed45bf1d8b7c472b154d793a29df614a925fd5625a91fed6af77ac202b1b71a85995c93130a8a316af237834d35d2eff90d02da59134e5de7c38ace2f5d7f60a6a25340d9bd4f1ea15cc629869038027a9a09dbbafa331d85670df92781c988b1ef10b67f56e0fb968b4546959c2e1e61993c2ab55e45e509d5f243dbaab91e1d08d11ad6e6b0c8c3bab337fa84e07fa80794e302c33cfe2b464646fdcd60f11c8a47528c7962618820d9f135cdb2cf6855c6a15aebab128c44b86d9fa0e97594af9d5965f80cd819f983e8557869a145870b22ce921091ec5bd40983b234d2deb7f24355b4f9dc6ced58f8e301fc55551565feb19287e66a5df9c5c811f5475d782bee65e4da026f767a9d0820f16c24f9eca3d2a507389fb14a6476fb03641c3a1c256d3e4abaa44fb26daf017ccaad5c48f9afb7192e42595a99e94c3be7e54bcaf27e24c8376473a8f1e56727bd2d0277d4b919a8717fa64e0ceb332efecaae10efd17bc51e91a70baefbda21384aa2766ba752bb51399e50c7787b807cd5c7fff24e82f475d157f71f4ceb865ad89a782a6192bb0f056023729ed83119512f3dd5b9176e4044ba159007beadf32b1cbf5b5c5a9c925e6a7555e18ed8266b204b68c07e8e84554b0e809dcd683b011b2f561a2d7aca966322565aa0c1551ea72e0d9a11b69de9a60cb65b04705bad4915c6e7eba96fa697efcf975c14e2f2737099739c9724de01ca5a67c596b02fa14ebcfca6dfec4d0e200ddfa8e447412323ca3692cc4b88d5d49896c82c63295a3a5d958485f5ec5745ff609f2dcaf6469806cbd2479eabcaa93019bd7abf7da5db540976991db78fde76d159492cdff9d5ee4d9a7cf8f43c7017b26fc6b6de26816517ec0b29c4bdf56b5945306db025170b4ed589bc17bb069943397ad707986dc46f43ca2b1c90277a3c03ebc6775f6374271cf8a6606e14bddb200cd03296341c5072fb39e29b1dca4a1b5685ca9fbfbf918b259a79fc5061a758219156ffea253f046baef21cdc79be037f398f08fb0dcad33f5ea1fbbcd236422d6199738a838322b2684e5d3344fac185034c7653577002edde48fd8bacd79db70fa7b3faf0c060d308768b782c005dbf865a55bd4fbdb3c9f4d29cb2cf5da6253ad9d5ece5adadb95c4f354a2f818a4d2dc99e02ba2a2ef0c70a995579f606666b1f105e736f15fc83f791939d1d4a3806d5541e83564647831df83c79436189b1d63e44b210dadecd4f645a3002f83e928149cf21c73b711b17a1375d7c2c41e94801e80e55765302c2c764c6496b024a07277c41d84653c52659267f62311c9fbb4e087e72082115b8f21230f5c6f801393f112263ff6de101928695715a1caabb4af540c739b7252615a475b75b4e9d73e9b012a897c917c0fb2fa578cb51af2ccd492a0246c0264a0c10d003f8b738feaa2827e1a10bffcac3f0d17e4a11f4c8ac7ad0a6281e79d0a418af0b9bbe1039d2e59b47eb6ab3d9a91f00dbebda40e8f3b3e5b5ec2bbf5f65178844705a2aeff0e723bdbec91a829e4060d6c4ba2c7891b5c84d31b10fb281d2f7488869428820254470ab8f4a4f5be97e3c47ddab99607a618be9a177a217ac794773874b426c02cc8702d4850ec3b4c6d4d0c31e2853813fa42cec6645e743e1971fc68b4e47a568e431e22c7226bba99d65b4550939deaa9ab618e8c25cfa34c21aabc1b4be0a50b685f1d25cc5df3090da131a74ee5108c65778c173572c1ba483cd460bc012c8d3db9aef167776c3090a3cfe3624f07cf2dda869743fd5a6143f87b55618c80eaad35aee5c7f5497e037038de5c93521a1ea60e76c9e435e88eb72c9046f1d8ae2338e7c6826793a2c22741ac8d19ebbce55d3792dbcd88ef64f177e2280be47b35256c7a50c9de8c5ba72385bed43aaec1a65d4b27bb850f78888625645216592a2c65c5e2f97042e1b399a6e9de452676a3fbbf6c5eaf6a08b733f2f4c28d4be6f93c0b02615faa089bd3d8c5f0db540b740aae54bc629b8d34588bda43cfe89c737aa0c08990b10f9054745ef9a5b756029e885af52b8dcdad07d1d4bc431cfb9f194f270d7bb4b66db7f0d8ca603cd2241a8a88d4623f1664544d05515875af3ddb125f141477f65504fa960c8dd63adfbc31a719a316c097097f114ea9c695c0ed72d2387ba4ea7fbaba8c5de546a0d0cffce153901310a0557acadc920a7032cf924e551559aecfce02f0de1f06c2ee2a85f612c3b95ad020ea26a88e2b42ea40dc1ed1f6e893145465981fd136163531284b62c21d858127bb13d5435e610ff00787cabe5c8822c9f4ab88661d32bfc6c2042a53a385b0832aa2b17f50303fc09ce77011c1437673a2b505491322796e95c2efdc40daf8cca242b75bf27fc19d09a2045d27608c2e0313244b74bde6bc411070bec4fec0267739e97f8a9c38e569e204b4d6cfc2f1c21d2efb2d20ec8806eb6a4bb1187a3f69d2993c621a1e5c986ba8fbaa4310363eaeabb085ab8404d8cd0e17ac9438d34f2e33d563487920bd0356d5313625b124cdb774f521e7b6776dad15f5511d60882a21cff1e604ae0dc25a3e58bc038884af68dce99375b3664c43b44c0ccdb65663fdaadc52a7f6190e6bf70c3023e0912e7154c782770fdeb73d614f944b7aa4fba7acee9a514299974523f55c38e3e94b5dfacbd6ebd107881378a5c81cfa19c2875024d0feed0efa12e347d25a040e3bfb620e8d3c0de2c8f249fa242fbc37decb154aad67ba8c03854ffd93a5b2e8a92a0fb934c8634f2f28788a2b56174f99b8e2c9b2626ec3a828a17ce408d600cbfb7b9913b9b33546a65c1eb5b31a0609c3915dc68547233f79f37f65c63e96a91be5045b97944156d77cf716c93e967c7e6d2b29b65081408a4d632027659f5e1fc944875821f9dafc6ad03deceb3227abdd3bdbb5ef0a67f3375406dbdca8d56b26bb0953607830748b178a4dfd0a0c1c1e50d80fe546309ff1facc47e21c3ba7956c531049aac0971bbdfbf08e6a5d8aa89b810b6db441eb24aafc5dafcd5f4e9f927ca965d1408db2607f5d932c7cf0bf12e2e2a397b6c2f9e821525ba2a0be92d8c18216a4ec6257e0c797f655c487cf520f838343c882f763e7ed457783b144330243d8a2cea784d28a43bd8e5c3a77fdaec4f32e44c179190c8324aebd68b422027a59ed501a41a638bd07843d80c96972d9378acf1e87002377b3ffc5d82e85e06a02d318a5c62eca9d744880b132d591e2af0118452041f851a6fcdbee2bec7e7a3a7921659171b2e8aae2af4b81f5cd4ebc1fe42a5034a79c8b805a51d93e8c053fd8fdc9b2940f5ea434e89cd82cca63d722cd3de0a3d879210162bd336ebac191c4e3f4612169f6e353e1181693ba83b57c553620e88ad12a5427bb01dcd287238b0b49acac2068360142ac1073525e8deac7e4065664d8c76d9aecc94adfb07c2d0363bc9bdb4906c2ab8a85717df225f217dca18ca72910a58b1f6f9be5bfc0d1b0b2dc1fdd705821e395ac2da06308ddb8fd5e824bc1fe4a0fe76f3999d1028a0367638878652c02cd61834c122a248532babbd41adf6dbeaf05686f655f44ab540bf6ca78b2d646cd46c947f6b55d60d8ec96ecf7e671877a664e73711504d288f8d285cd1eb982feffb364c833dbeca3c57dff2120d9903557837b2897238b5269cfd25aaecef0444d1a32fc5e9f9b85886c6a1b75a939ba645aa23c778d77027b4148a76e8fdb1a12ba265d0e5ca1acca724c91455c46900d3362537aaefc6e0d34a89d0a09831e0457f62a40f9795bfd886c29bbd140bc3dacd2f0da2dbccc4f4a4f5f1ab7c7d85a92280ade2bd5ad4b5ab1458fa6ef2fdc66beb70a7a1334c84d078e5ae799eb755f97a3ee0e361299acd28fcc9cebfaf86f2cf0d9480fa2e5b5830e94df05466165970d07e6f19ff7f8bd069574c8cc19bc4073f57df5ef5cee2fb80a5df6bad010683fa288ca9737c20d80e7585b9b2e30e93afdf3182614037d323e77d6ca91b5cd3b39f82ba9fc81b2176c33b76ce4bfd58987e7807db46c232832303ba34599d6a0b71c9b3ff0cd9696bc19e4ffd21d5afbd4f98bb6b3cb6585ff0e8f6bc313ddcefb0e54f088cd1d6ef02a1a2b84b45beb6d6b439011b4c8db2395395602fccbe0d8e57851ece3855736fc251bbc5068e1f515800caf804646b8d61f496804f6d8b24e79fc4ab775b58a6a2907d674893f183e9c6acb4a2244ff5ffb37f7343dc3dcdbed9b0892a5cfebac74da7b224b24636b6f7a72f9067ad56b76eafc7add0b57493c6d70ba148b055b331e38b5b9b509f2c2e0c92cee82043189ba3a987d3804d896478a341e5453be25868cf2b403d736c4e6a86f4f8ca47eddc2830a5ecd47516ffda50d5efbe6b83c65f74c065e55854314149949bdfb8f476f1ce43e85720c2ed16be60b68b614820438c248a6eade0d070d591464ec0be7adb403decaad1f5ca64f4fcc084b82bc85e35fb7f62305168f01e23090e1a08e9f27e68739b97a9038e77287af0762ca5110e54345ff28fed6df0d30d701f2f11b01d7c7ac1726c7b065b43ab48931dd6ad2f3d7daa4b9ea17fec6d9dc1094585ea64ab61f36584da480465f340605cda88095d8eca27aa1c0f910adbb551fdefaabee636eb5dc5c458dcf371bc61341aec73f438bc70b81f881ca4004ab70b932e6b1572a6622e55848b499783621f00f60856d252cc8d85cbe89a97bb4c03a76513860914ef766748c810caa4a3ea6df6b4c1878a40b822d5e806f6ce285d170d1d797d9a5c46b3a52898c9dc83e720efbc81b5beaed82da200d72b77782d86eb6054ce2ce9a8b92b6522a90bd83b5d071ab110a03df53ae44185bca738c5d8bb621c4c00eccc9dd57d332d4787ca73b0d8122c0a3c7e81c708476bff174b734acc43a6c2dacc0b5fa69e4b20713b28477a12c88b13b6840c5de997f6779fadfb072ba295a8665d52101b5ae5a14cfd78913a00924c1dfaa8bb73b79b877221b381d15dc02e883086802a963cb00ee53ed246155286881857b790779a8f823d649a58d8eadf653cf2a5dd03b1f86164591a1ed71fbad130258143010001bd1504b715e5c76a61a6a7bf3c33df202d74a99c4d752dc4d8da37ee12479a64c61621261aad42b1451b6056e1fad40625330ff434126c175704712486121034fd0c0a601f0000000000000001770ea866172e8d40a5ec75be01fe745fe8af2204fe50370c19d943c2e806987a82cda62aab3db7f5166c41a65094843a6a4f9bf185f6f9c39dd5203a8e7820f59884d688790a3dfd208459487be405b1ab310332bc1a62559664eff47126afb7d9a6006ea825bf06dbb7b28b8aff1ec81200d8d7420bf1daf81bc004442b3fae2b4f3b0048354d15b916877943ac862c46688e745d4af459f7caff0cb14753d7a3f993ba74abbc53c7ce25d50f099db363cb21463dd202f00154c83d5d4c8552613853c7991e6f477cb4a7c85c92d51a20040d5c86efdc02d0a9916e301fbb2d598b8ce5486e0928c811ea79daa67a11fed57b2a5159f8966f8a3564e4078921930a49f9bd5be5a4b32f2dba7b16075507f0ebf5e4e47afa4e54881a4e3700c91d5aa44d95fa6b8a167f1c5d90ae927044985b18b8efa095420aa689889b504371558605a4ec42f86bb43700e8b7ebcae5f613107cfc28fd80dfef9bd4240d925449b64189a615d708af55cd334a51c43b7564c342187595b594789d99d09872bb7ed53207d29f02d0d17b27e8a9a68639341d2aad8edec2dd2d58d091e960250d8252e709f887f5e355e840fe7f84243d55166cfbfb2f475b33e0f853bca789909877cadb5aa305564691755c1b2f00d38844ec75e112dfb4aefe94f21e3732cbccdf63030850e2719d2fcf2170736f98485cdc3f49006f41a17259cd5f94840bc50ad335829157de38b7abefe00bfeff06b3059baa2df8715f7336bf118ae7c10e64e4bfaae047275c0493f241a9c6734d971d54eb544039ca748801c004c44b2d24d507352dd229730a206c60a0aceb028639690944f3d99b4b31dae85bfc853ccf78510c24eb85baae0dad2afe092c00448656a3b9410fd13472c407a3d2d699e226463dc035b9217bd7a67181df76c7eba5f769212e6b9cf01fb056203422e1f92ec75591d34daf2c63d8730e1bf2db00a9f335262e57841e75bcce714b155926ffc4d97d4cb0a3c339f13f5220737e741abacc6027402c5b8a4083cb4667a11abc2c889fb6aa67971fcd6e544f49de560fb39a883405deded3693e5ca97741ef11f139dab38944d99f22a59c5cc8fc8f6182216bd0e00e0de57a3d7924ddf6c3fdc32c8b973f38de485f6a81efbf9a0efa569e267da5d7d118e8c776e2521dc355112bdfdafa6f67dbdb0c1fa454c067789e4458aa7c27fb96e03d12cdf1a6eb6c4dbdb7ffa5987170e38b4b393857853a700a0426aaf577d75a08921da9ba3bb8406c5b763e2fb841af25abd2b7d9d0d91d09ccae2bb98b7ffaf041e056aaad22c8ac87ab4458cc3cbd9b3b7c96afaca3641e1c5647c58b888ddbc6b1f5dcf47d4d98f966210ac14505d9ef45b344d70c0317b254390e4de091b1d0119246a145c64e53eea42310f1587c101cc48a8bbab0f4e569198ed020e25dd8b6e3ba1ae91558518a09fee2897c2917280b5f55678fa5bce141f9743fb82be4c4ab561e74ee0c13b0d35ca4d69110c2b81146652450e185277823e3aef3ae53c2a795cfc73f65d2bebea6f221830aa95d9492b4bdd69d2657e82dddaa28aae2cc7b2ec78778b43f7f1fda91246e8935d1baad16ea90ddf6008caa809ccd46d09df6dc86b49530891301f6d3ec0d994a8bb206423062e204dcc6372f57d740bdcca6dcc1144223cf827ee95a27aa32147d001ac4b40ced09ec8ae0041e52f51b2d591da7baebad889ee058a8cc4a07e34de321b65485307771487eb5de6dd75004042452799686eba9cb54d88f4b91f0b77198b27cff96c00761e527e0a9c11f780105987d02623590e09c45690cd9e8a787caa0f14cff54b17918c3cab79327afd275821a084e4e7a169717560932f8cdc5351b4895c3e7c83e2e167bb01bfc898bb70558ddd91c736f634b9217d67be66a93635097e64e0fe3eb8d9007305e2f6ca99b587dbe00bd780725857bfb36796068bb57f01df7ba010920816a4215d999e9b9acfc7437d2c7f2f563c4618574f3279ccf80dd6c23cd313064e7f75c3ddb0efbd5f948893bfc1d24e937a000f90ccf8ceaf57461345d9a00f61e7de0ccd5cc00fa9c03a0764ca22d3486bd07105340ac4d26666fcb930520a733647c215bd326a00f08450e7efff68e95ef34695d20c08c113b9c9040125d668fd07093742b292749b534dbe84155002c02ca887989d8900f8e7eca1dc9363f5722162c62382f41eb2ed91c0e7375901f803951f1504b5bbcecc6388e756f3dd038a303d9f1a7212f9c60e3dbfa7b06e64a3564ff4296f15730c0eb6028429c3bf5d1e3b8f46ab649db9fb457d22e470ca7c7793e53fce7c07a3cd71b49cbad32900f94f076cdf1c039d9d50625f5b883e33c6e5320d5d061a490b8ababfe6f1277f2bfd77f658b497b7217dcbc4e3dfecb4b08d99343e87313eb27f102a1bcb74be5790f89721bfce7b42661fbf84ffcd29be6b45be448f66f816215914cabce764023f5cd5ba27fd574155b2e8ee4171c1511fe48ab3eca9f7c5115ee4017632b38b078678cd7ec139022b3abbea5ae2178872c3ca9708c99af29ce1502dadd3ef273576a798155f06bf0dd877b1462848539a351658f18d8ccf845822594d1965c1c3a825aed86f0683f63b20d1df46c0490852c73b775917bc63015f4df4669c39edc50b69d1910d152004afbeaaa3e9d8980ddd96c5e81c83e9770086b1942ae9cc2488eb99a7280210ec559533640ed0a59b397f53909edfcf81ccbf46d164c3dad7fe786eab68701b1a88a87670cbfe98b8dfbe808290cb737184f8a35bcfa6a27d236edad1855ac67450b79eb2973802eb10737bbe3953f3b26d0d70ac95c30954d222bbfa27d31bd083d27f45edbdc560f557e57a71e59554f2efc38d41bb2730f794d514c03398374ef73de279934f0fb6399946cbdcc61003ec29f9e82352bba0985ed9e29dbc18fc24e0a01fd8045dcbece21de4bb52af36830d933b0e222a35ada06cfef4308a42d8d9d4c84d7dc439b3f51eacb71412a20c77a5b8a8cb72ad73f4f51eaa842d3ca6111a484eb1cec8a1e480ec8cd1ad6d0607cd62b37bde02d8ea8bf3fb62fe30b945e0f566217a096a32662154b8f39d58c5c4166991d1086a831727ff86cb405ebeae0ead1848611441e1dfcf1fe17ceff7b808ebb5f9fcb7da734e6f742e276fde75f7249869f882aba7d85a9b795b1ba7726b69b0a2b375b97d2889e4d7e5fbf7659f046593448ad1aae569254b2c5b54b02df1d285124ee818cf63a54db498d61ffb7b0d8897e48933effa2bfa43284b06718eac8977589462621981818d60f54eeb16d4e0c123e8915a76f7d5a82beb90378b1c8ebe353414a94d969e16737a5d1fe7a66b175d949a62dc8416336e9233604db1656bc35d4d2fe98809f5111c7ad73aabbfd690d165088133fa7ca217d98d345afa8cb7745719a5ed89450b76f731ca6bdb7daa3559161441ad7b07406cc15c114171b685380e16b138f4b94907f3c77c4f463f520921828fbf83b92fa0d28795caa7819daa9e6e13884db30868dfb355211ab6e934d3a9ccda3453790bfc83bb652a18d777a056cad0078d815d92714871a27ceb1801a8ebd4555b5570130bf531300000000";
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("decoderawtransaction ")+rawtx2));
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "size").get_int(), 6743);
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "version").get_int(), 2);
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "locktime").get_int(), 0);
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "vin").get_array().size(), 1);
    BOOST_CHECK_EQUAL(find_value(find_value(r.get_obj(), "vin").get_array()[0].get_obj(), "txid").get_str(), "bdba8572763fd5bb072386726fccadf4fe532af7dd5e70ed245527f9475dbc3d");
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "vout").get_array().size(), 4);
}

BOOST_AUTO_TEST_CASE(rpc_togglenetwork)
{
    UniValue r;

    r = CallRPC("getnetworkinfo");
    bool netState = find_value(r.get_obj(), "networkactive").get_bool();
    BOOST_CHECK_EQUAL(netState, true);

    BOOST_CHECK_NO_THROW(CallRPC("setnetworkactive false"));
    r = CallRPC("getnetworkinfo");
    int numConnection = find_value(r.get_obj(), "connections").get_int();
    BOOST_CHECK_EQUAL(numConnection, 0);

    netState = find_value(r.get_obj(), "networkactive").get_bool();
    BOOST_CHECK_EQUAL(netState, false);

    BOOST_CHECK_NO_THROW(CallRPC("setnetworkactive true"));
    r = CallRPC("getnetworkinfo");
    netState = find_value(r.get_obj(), "networkactive").get_bool();
    BOOST_CHECK_EQUAL(netState, true);
}

BOOST_AUTO_TEST_CASE(rpc_rawsign)
{
    UniValue r;
    // input is a 1-of-2 multisig (so is output):
    std::string prevout =
      "[{\"txid\":\"b4cc287e58f87cdae59417329f710f3ecd75a4ee1d2872b7248f50977c8493f3\","
      "\"vout\":1,\"scriptPubKey\":\"a914b10c9df5f7edf436c697f02f1efdba4cf399615187\","
      "\"redeemScript\":\"512103debedc17b3df2badbcdd86d5feb4562b86fe182e5998abd8bcd4f122c6155b1b21027e940bb73ab8732bfdf7f9216ecefca5b94d6df834e77e108f68e66f126044c052ae\","
      "\"nValue\":11}]";
    r = CallRPC(std::string("createrawtransaction ")+prevout+" "+
      "{\"3HqAe9LtNBjnsfM4CyYaWTnvCaUYT7v4oZ\":11}");
    std::string notsigned = r.get_str();
    std::string privkey1 = "\"KzsXybp9jX64P5ekX1KUxRQ79Jht9uzW7LorgwE65i5rWACL6LQe\"";
    std::string privkey2 = "\"Kyhdf5LuKTRx4ge69ybABsiUAWjVRK4XGxAKk2FQLp2HjGMy87Z4\"";
    r = CallRPC(std::string("signrawtransaction ")+notsigned+" "+prevout+" "+"[]");
    BOOST_CHECK(find_value(r.get_obj(), "complete").get_bool() == false);
    r = CallRPC(std::string("signrawtransaction ")+notsigned+" "+prevout+" "+"["+privkey1+","+privkey2+"]");
    BOOST_CHECK(find_value(r.get_obj(), "complete").get_bool() == true);
}

BOOST_AUTO_TEST_CASE(rpc_createraw_op_return)
{
    BOOST_CHECK_NO_THROW(CallRPC("createrawtransaction [{\"txid\":\"a3b807410df0b60fcb9736768df5823938b2f838694939ba45f3c0a1bff150ed\",\"vout\":0,\"nValue\":0}] {\"data\":\"68656c6c6f776f726c64\"}"));

    // Allow more than one data transaction output
    BOOST_CHECK_NO_THROW(CallRPC("createrawtransaction [{\"txid\":\"a3b807410df0b60fcb9736768df5823938b2f838694939ba45f3c0a1bff150ed\",\"vout\":0,\"nValue\":0}] {\"data\":\"68656c6c6f776f726c64\",\"data\":\"68656c6c6f776f726c64\"}"));

    // Key not "data" (bad address)
    BOOST_CHECK_THROW(CallRPC("createrawtransaction [{\"txid\":\"a3b807410df0b60fcb9736768df5823938b2f838694939ba45f3c0a1bff150ed\",\"vout\":0,\"nValue\":0}] {\"somedata\":\"68656c6c6f776f726c64\"}"), std::runtime_error);

    // Bad hex encoding of data output
    BOOST_CHECK_THROW(CallRPC("createrawtransaction [{\"txid\":\"a3b807410df0b60fcb9736768df5823938b2f838694939ba45f3c0a1bff150ed\",\"vout\":0,\"nValue\":0}] {\"data\":\"12345\"}"), std::runtime_error);
    BOOST_CHECK_THROW(CallRPC("createrawtransaction [{\"txid\":\"a3b807410df0b60fcb9736768df5823938b2f838694939ba45f3c0a1bff150ed\",\"vout\":0,\"nValue\":0}] {\"data\":\"12345g\"}"), std::runtime_error);

    // Data 81 bytes long
    BOOST_CHECK_NO_THROW(CallRPC("createrawtransaction [{\"txid\":\"a3b807410df0b60fcb9736768df5823938b2f838694939ba45f3c0a1bff150ed\",\"vout\":0,\"nValue\":0}] {\"data\":\"010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081\"}"));
}

BOOST_AUTO_TEST_CASE(rpc_format_monetary_values)
{
    BOOST_CHECK(ValueFromAmount(0LL).write() == "0.00000000");
    BOOST_CHECK(ValueFromAmount(1LL).write() == "0.00000001");
    BOOST_CHECK(ValueFromAmount(17622195LL).write() == "0.17622195");
    BOOST_CHECK(ValueFromAmount(50000000LL).write() == "0.50000000");
    BOOST_CHECK(ValueFromAmount(89898989LL).write() == "0.89898989");
    BOOST_CHECK(ValueFromAmount(100000000LL).write() == "1.00000000");
    BOOST_CHECK(ValueFromAmount(2099999999999990LL).write() == "20999999.99999990");
    BOOST_CHECK(ValueFromAmount(2099999999999999LL).write() == "20999999.99999999");

    BOOST_CHECK_EQUAL(ValueFromAmount(0).write(), "0.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount((COIN/10000)*123456789).write(), "12345.67890000");
    BOOST_CHECK_EQUAL(ValueFromAmount(-COIN).write(), "-1.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(-COIN/10).write(), "-0.10000000");

    BOOST_CHECK_EQUAL(ValueFromAmount(COIN*100000000).write(), "100000000.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN*10000000).write(), "10000000.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN*1000000).write(), "1000000.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN*100000).write(), "100000.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN*10000).write(), "10000.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN*1000).write(), "1000.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN*100).write(), "100.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN*10).write(), "10.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN).write(), "1.00000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN/10).write(), "0.10000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN/100).write(), "0.01000000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN/1000).write(), "0.00100000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN/10000).write(), "0.00010000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN/100000).write(), "0.00001000");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN/1000000).write(), "0.00000100");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN/10000000).write(), "0.00000010");
    BOOST_CHECK_EQUAL(ValueFromAmount(COIN/100000000).write(), "0.00000001");
}

static UniValue ValueFromString(const std::string &str)
{
    UniValue value;
    BOOST_CHECK(value.setNumStr(str));
    return value;
}

BOOST_AUTO_TEST_CASE(rpc_parse_monetary_values)
{
    BOOST_CHECK_THROW(AmountFromValue(ValueFromString("-0.00000001")), UniValue);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0")), 0LL);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.00000000")), 0LL);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.00000001")), 1LL);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.17622195")), 17622195LL);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.5")), 50000000LL);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.50000000")), 50000000LL);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.89898989")), 89898989LL);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("1.00000000")), 100000000LL);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("20999999.9999999")), 2099999999999990LL);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("20999999.99999999")), 2099999999999999LL);

    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("1e-8")), COIN/100000000);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.1e-7")), COIN/100000000);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.01e-6")), COIN/100000000);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.0000000000000000000000000000000000000000000000000000000000000000000000000001e+68")), COIN/100000000);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("10000000000000000000000000000000000000000000000000000000000000000e-64")), COIN);
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000e64")), COIN);

    BOOST_CHECK_THROW(AmountFromValue(ValueFromString("1e-9")), UniValue); //should fail
    BOOST_CHECK_THROW(AmountFromValue(ValueFromString("0.000000019")), UniValue); //should fail
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.00000001000000")), 1LL); //should pass, cut trailing 0
    BOOST_CHECK_THROW(AmountFromValue(ValueFromString("19e-9")), UniValue); //should fail
    BOOST_CHECK_EQUAL(AmountFromValue(ValueFromString("0.19e-6")), 19); //should pass, leading 0 is present

    BOOST_CHECK_THROW(AmountFromValue(ValueFromString("92233720368.54775808")), UniValue); //overflow error
    BOOST_CHECK_THROW(AmountFromValue(ValueFromString("1e+11")), UniValue); //overflow error
    BOOST_CHECK_THROW(AmountFromValue(ValueFromString("1e11")), UniValue); //overflow error signless
    BOOST_CHECK_THROW(AmountFromValue(ValueFromString("93e+9")), UniValue); //overflow error
}

BOOST_AUTO_TEST_CASE(json_parse_errors)
{
    // Valid
    BOOST_CHECK_EQUAL(ParseNonRFCJSONValue("1.0").get_real(), 1.0);
    // Valid, with leading or trailing whitespace
    BOOST_CHECK_EQUAL(ParseNonRFCJSONValue(" 1.0").get_real(), 1.0);
    BOOST_CHECK_EQUAL(ParseNonRFCJSONValue("1.0 ").get_real(), 1.0);

    BOOST_CHECK_THROW(AmountFromValue(ParseNonRFCJSONValue(".19e-6")), std::runtime_error); //should fail, missing leading 0, therefore invalid JSON
    BOOST_CHECK_EQUAL(AmountFromValue(ParseNonRFCJSONValue("0.00000000000000000000000000000000000001e+30 ")), 1);
    // Invalid, initial garbage
    BOOST_CHECK_THROW(ParseNonRFCJSONValue("[1.0"), std::runtime_error);
    BOOST_CHECK_THROW(ParseNonRFCJSONValue("a1.0"), std::runtime_error);
    // Invalid, trailing garbage
    BOOST_CHECK_THROW(ParseNonRFCJSONValue("1.0sds"), std::runtime_error);
    BOOST_CHECK_THROW(ParseNonRFCJSONValue("1.0]"), std::runtime_error);
    // BTC addresses should fail parsing
    BOOST_CHECK_THROW(ParseNonRFCJSONValue("175tWpb8K1S7NmH4Zx6rewF9WQrcZv245W"), std::runtime_error);
    BOOST_CHECK_THROW(ParseNonRFCJSONValue("3J98t1WpEZ73CNmQviecrnyiWrnqRhWNL"), std::runtime_error);
}

BOOST_AUTO_TEST_CASE(rpc_ban)
{
    BOOST_CHECK_NO_THROW(CallRPC(std::string("clearbanned")));

    UniValue r;
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("setban 127.0.0.0 add")));
    BOOST_CHECK_THROW(r = CallRPC(std::string("setban 127.0.0.0:8334")), std::runtime_error); //portnumber for setban not allowed
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("listbanned")));
    UniValue ar = r.get_array();
    UniValue o1 = ar[0].get_obj();
    UniValue adr = find_value(o1, "address");
    BOOST_CHECK_EQUAL(adr.get_str(), "127.0.0.0/32");
    BOOST_CHECK_NO_THROW(CallRPC(std::string("setban 127.0.0.0 remove")));
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("listbanned")));
    ar = r.get_array();
    BOOST_CHECK_EQUAL(ar.size(), 0);

    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("setban 127.0.0.0/24 add 1607731200 true")));
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("listbanned")));
    ar = r.get_array();
    o1 = ar[0].get_obj();
    adr = find_value(o1, "address");
    UniValue banned_until = find_value(o1, "banned_until");
    BOOST_CHECK_EQUAL(adr.get_str(), "127.0.0.0/24");
    BOOST_CHECK_EQUAL(banned_until.get_int64(), 1607731200); // absolute time check

    BOOST_CHECK_NO_THROW(CallRPC(std::string("clearbanned")));

    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("setban 127.0.0.0/24 add 200")));
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("listbanned")));
    ar = r.get_array();
    o1 = ar[0].get_obj();
    adr = find_value(o1, "address");
    banned_until = find_value(o1, "banned_until");
    BOOST_CHECK_EQUAL(adr.get_str(), "127.0.0.0/24");
    int64_t now = GetTime();
    BOOST_CHECK(banned_until.get_int64() > now);
    BOOST_CHECK(banned_until.get_int64()-now <= 200);

    // must throw an exception because 127.0.0.1 is in already banned suubnet range
    BOOST_CHECK_THROW(r = CallRPC(std::string("setban 127.0.0.1 add")), std::runtime_error);

    BOOST_CHECK_NO_THROW(CallRPC(std::string("setban 127.0.0.0/24 remove")));
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("listbanned")));
    ar = r.get_array();
    BOOST_CHECK_EQUAL(ar.size(), 0);

    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("setban 127.0.0.0/255.255.0.0 add")));
    BOOST_CHECK_THROW(r = CallRPC(std::string("setban 127.0.1.1 add")), std::runtime_error);

    BOOST_CHECK_NO_THROW(CallRPC(std::string("clearbanned")));
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("listbanned")));
    ar = r.get_array();
    BOOST_CHECK_EQUAL(ar.size(), 0);


    BOOST_CHECK_THROW(r = CallRPC(std::string("setban test add")), std::runtime_error); //invalid IP

    //IPv6 tests
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("setban FE80:0000:0000:0000:0202:B3FF:FE1E:8329 add")));
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("listbanned")));
    ar = r.get_array();
    o1 = ar[0].get_obj();
    adr = find_value(o1, "address");
    BOOST_CHECK_EQUAL(adr.get_str(), "fe80::202:b3ff:fe1e:8329/128");

    BOOST_CHECK_NO_THROW(CallRPC(std::string("clearbanned")));
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("setban 2001:db8::/ffff:fffc:0:0:0:0:0:0 add")));
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("listbanned")));
    ar = r.get_array();
    o1 = ar[0].get_obj();
    adr = find_value(o1, "address");
    BOOST_CHECK_EQUAL(adr.get_str(), "2001:db8::/30");

    BOOST_CHECK_NO_THROW(CallRPC(std::string("clearbanned")));
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("setban 2001:4d48:ac57:400:cacf:e9ff:fe1d:9c63/128 add")));
    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("listbanned")));
    ar = r.get_array();
    o1 = ar[0].get_obj();
    adr = find_value(o1, "address");
    BOOST_CHECK_EQUAL(adr.get_str(), "2001:4d48:ac57:400:cacf:e9ff:fe1d:9c63/128");
}
/*
BOOST_AUTO_TEST_CASE(rpc_convert_values_generatetoaddress)
{
    UniValue result;

    BOOST_CHECK_NO_THROW(result = RPCConvertValues("generatetoaddress", boost::assign::list_of("101")("mkESjLZW66TmHhiFX8MCaBjrhZ543PPh9a")));
    BOOST_CHECK_EQUAL(result[0].get_int(), 101);
    BOOST_CHECK_EQUAL(result[1].get_str(), "mkESjLZW66TmHhiFX8MCaBjrhZ543PPh9a");

    BOOST_CHECK_NO_THROW(result = RPCConvertValues("generatetoaddress", boost::assign::list_of("101")("mhMbmE2tE9xzJYCV9aNC8jKWN31vtGrguU")));
    BOOST_CHECK_EQUAL(result[0].get_int(), 101);
    BOOST_CHECK_EQUAL(result[1].get_str(), "mhMbmE2tE9xzJYCV9aNC8jKWN31vtGrguU");

    BOOST_CHECK_NO_THROW(result = RPCConvertValues("generatetoaddress", boost::assign::list_of("1")("mkESjLZW66TmHhiFX8MCaBjrhZ543PPh9a")("9")));
    BOOST_CHECK_EQUAL(result[0].get_int(), 1);
    BOOST_CHECK_EQUAL(result[1].get_str(), "mkESjLZW66TmHhiFX8MCaBjrhZ543PPh9a");
    BOOST_CHECK_EQUAL(result[2].get_int(), 9);

    BOOST_CHECK_NO_THROW(result = RPCConvertValues("generatetoaddress", boost::assign::list_of("1")("mhMbmE2tE9xzJYCV9aNC8jKWN31vtGrguU")("9")));
    BOOST_CHECK_EQUAL(result[0].get_int(), 1);
    BOOST_CHECK_EQUAL(result[1].get_str(), "mhMbmE2tE9xzJYCV9aNC8jKWN31vtGrguU");
    BOOST_CHECK_EQUAL(result[2].get_int(), 9);
}
*/
BOOST_AUTO_TEST_SUITE_END()
