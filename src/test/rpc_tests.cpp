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

    // Check a more advanced rawtx case with blinds and witness data (ocean specific)
    std::string rawtx2 = "020000000101d591f7259fded69811c82a4100055148c070add33fa3d7e6fe48eb0cc3a0bb471300000000feffffff030ba0ac82e2ef758f2162fa741cd0f719028e530690bf42e2fe61b252f9a10e3c9308ba1325167710a3aef9b68f60397bc28610bd5f7cdd9c2893206cd85efbbd4972022313a4a559d45615027d501524495c6df99dd25ce7b763400b23b34319c8cd521976a914147845e13196bb2994d981277c8be8740af71b0888ac0b38b5af7598350a4c539079ac3276ba89f2d11ff6299e740e85977daef5557d0409466d97966b7db2bb8f7bc77bddcacaa20b2c014e3c03cc3a7c205c802b0277d3030eaf54cac9a1aced68ab0ba57605ad73974f1950f44d2b44c81cd1b57f9303551976a9145d00f031bcb6ea91f0b094b3add79d01f964612588ac01230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000000009718000000000000000000004301000184d953c6a1daa32febe274772e908764a61e02e207a4adf75092394fdaa32fe0a96c01fc837b35a379fed927baef8b80d5a9439a591b19234e2f0b9a73cdcce9fd0c0a601f000000000000000133208b0edf417bdc4b07edd0914b6d057bccca355536cec721f50211234d4c83c89b5c9da1c2497fb5b443c59a71a8b9b0c2134eb34f74be863af973a3fa5205086c208da851cd1070d9ed1e2a3d7854c074de4a25628a291d27dbf07cae1d761a3e24044d29d1b6891dd58b36d5b1f0f4d709fbc84618529ef2e96c5824bb6766d3cfdd7787f77d9a636a23aea8c8e15b4f855424d02b31e1442115d55e6c7387c99a46b131cee2fdad1dfdc29a27a109e728068cdc977d2e25b53d1ebbd4aecdd513b815a998d394988eca5d2f2dd3ccb0ecedcce6b3987bbb5b5889c8d48fede605dc4eb3630574373f897b54e58abd58f0f67bed2a29427bf78928b04be307a96a45af21f9f37515344a9e8052b33067c2cdd03d3dba60b88f901a2b823f83e2bedaf007b4190007116b2bfb47a886d3d852ccb8ddd838a37bea04304e9ad3fe176b0669f6213eba9d22549d81febfda82a011b7d25b7adf54656e72fc057ea9d3d07ef44c36c1b8908be63b8da85b033f55b51da3273152ec6604fa0ebd818768bb8fec080611e0b4626203257d7a72025e93014618231c96d430bcb59d27d12f8b0bd1b6213e07b7bb1a52b9ca56c001921a24980d0e191134aa87c49b52865c5afac20a3bf3df2ca5bd899842ca04786a403d4a19d37d6946f7e2f504969a4e5470973b96701ea4141816f7326453e0ba7e55a9384ba822cf3c5719f553dfa0184bc03cfc64227dc8aebd6dfd8ead916fca9856306f501b45af23cc87d4fed85350303b0c48450ea44e1de813c9ca495e9a7b9405f1cd303084bba97f5ccc32a5e77c496557a57126c524d8d813a23c53658bffb8212056009763837223f546a7846f43a604ae0ad3d11dec91f3e7441aa9c47fc801743bba0cfc75bbb344cd92c132aa5573306a3a6d9357df6bb3816e20ca78d319abf80298de7565205c1b0183399c5d75c8ff2c239f9fc2ca90bd244bd6cdbc17da2648b107d3e490a97c4a6cc6450ffa7ec0a801e67961306bfdee6b6887ceb26a9e8275b34c87d809815f774a52a82a28a4ce5f8c6dbbbb9ffd24c3da93c3a2b091f938af6053d36bce4ebbea82048af132034154a4dc0ddfd5758fb1e1ca2e914ef305b1a04748ebaff0ef897c8ddc1734ad3079ea266d2de1035b7993196e7e962fbe9287df14da9aed4d9897c6798868a67a4e79683a25b2c3ce938bfd56e72f4d9498ac0819d13a77573f76cbbafcea2c57d39058946bba370dbfb8b09fb825358d032a5d291271a3bb45ea822a06a0f03aa3a78f1c70771bfc364e5081e14016f10b60fa0d0f686390e483b1cba81dfc7c53dc6adab89621a636273aabaf3d029ef6bbe678549024bf3c6fa2041e8a88fd223af48e8e69328f33c6a39ef200a90959897249a75eb1af37339547d769c0af53cfee90d14f83ce52209a8afdf9ce92fd573f37f28de3ebefc6526134f0ea59bb3ff58fa1d95b36d23447ae527446d8f56e0bf09468d510edab595ef7bf0f22cc74333ba9cbe38f304e693f14e8f8a934abff2d84bc7777b92bf02ebe616d8e057137fb5dea30088794536c7c7959aa54ea6b85c99e178a2f174fe7b707bcd5620bd6e5e537ab5e195269818528458c56059e081b35e6f2c80f4c31e0993ccdc5acf123c8d88c6071897168fac1d9044918e0d17fa4ccf9445aafd6bbe7adc4310c7cb10b65578c171f617ecea3d6a0a2a6da1099402e7d34576412a44df7ad60cca300491ca1e3439b65a59d3c0e9b2340eb29b25ad8a7063424dc4ebd8c6994213cf9489b1fcbd514a88bd801a54cacb1f26414ae0420f5ed788bd3e4382ea5ce3b46ea6583ee4a5beb31a9322d4d402871d0db4eff9e2e75403f4d325caaef63518645ffe1ef7e8ac73e055e7b64db4f2efdc0158e3d5ec08d3ea415fd65fa396f873c318f1933d242137553aebe6088c858e7baa8ebf33582d8b293d665c417e6425f1841903901ff7af295baf64872df39465cf0a4a0ed755a353316c7727142df0f78915ae336f134ea8b2ece84c2100f652a0e38043804f6e45f8e3c76f7b815b3cdbb5481d2cc01b4be17ccad95cbf9a1142b43498a8289793bd4e71765b59666c2b762296a9c4a7dfb16555713095c383ee64c8cd95085c35f999b77d4e5c87cf1f8457306176224a9b342bc289627d6b9953e472f594e9b1fe286659571b0ce1fc0d6f71d39494415dd2ff21976808084bede3c60c7bef6dc2fc1f1c8fe3a4955944edd444b49db31b4c1d932b50566aa0fafbc7fc183e41e67270681bc38417bbfad1d1cc0bb0a3f05bd9b0be41a9c6119010d90a766ceb2b28df5c034cd5e0ef10ef763ecbf205e43276ab7730d8537f13ffe380aff0552663cdc02060128848f2bfea6e30f4c8cc96b5ae6ab08afa6ec3439b780336dea8994274a9a3330cb01a3e54088bfbdfd4134cf8551fefe2cb332f08dfba0c098e9bf529e6635edad6ce272b2b268a690b212d95acb2041fb711a48725216fb91fe12ebb3720e48945f3187b96867772d8e36911b7b579e2ad59b6939c48b36693a51b70e96cc577c13b6155f8191510b183a1e9e4abcfcc1e6cba1b200bedb2a0a5d2e0dc61fe29c2aa02e7de658538ec0e8fdb5f9954310933ed1f234640216a9721d7746cb10c47929c109799b724f7fb94d9dd146f42e5dbd252a7bb48f97ac7af30b5d7393d1ecb6c0d60068346cb5340eaf67cbcbf4db057352ee5afc573c40b095b18269cb796927a67601835360f7c625cb46899d255ec3425e0e34e1ed098719ca7341a4ca87ee36daf0999f371707d041daca6039a1bee1bb21d6e02c17dcd6fad7424b4159f52464c92990c2baca5e4dc5967359218d15ce0ca7a203ee328a6e54f9cb89cf2dd5a7612441090c5df91bf6e3bb806e46920f0d6ee0617bd85f9bd09a957c63c43f3cb10df052ece5ddd07d83c90e4f2a78247defec586c3af4af6c6edcbc8f5497a95428ec320d582ffd2a96b3a00aaa460986e1f2808bdae9c8de93ace89025f495c37fa3c2f7d3026d9a9b813a558b94d6e5d580fe1a2b3529a759dd65f81f02e4f30c8371271d7ee59d1a0570e933381c26770a83e7aefbcddb963c024c4ef6f8fd09723851978fd9925ad81b2b4c39f31278989fa9f973f86fdb9a00ea9f4b3e98d30a27612566747bbd5f924ec0c838123f6536ce1689c8636443a92096cabc7dbb0f2065a5cf1d4a3219b9c6b685fb10d3785c6fa469cfcc6e97a825e0b7a85dd97a3617865abe823d6c096dc61fcccedef0fba73ecd7fa725d3c64ab2f00da04e80ef22c87500f06917f3a87f2b2898b448f5a663a5d0705e1a5d7f8e57f37bdbfa008e47df5ead1aebb4097186902d85654678dc564aeb23e250a72d7354ba40e14788db4ac217d0fab5bb3f1b609df8d3802e2a1857b1339e114e3889bf16c8710228c92790b9e301aa225dfcd62ea5c2279be9550af6a2dc1860adeef9ab424d703afcbd90d930f7dedaa765783159ddce03fd9330edeb6fbf39622e80c5bd4daaefb3387b74d35c6d02e14d6344a6ddfcd716530f75bb9503d37fb54e5237eb83e33f1d76650d45cb8aea33dc72cf7d5fc5d3e91b7ef53fa7badcab7e47023181677c6e721197430100019500f90b308316402b8bdb6e7059684cd4456d5b97b6867642545d6c124a6135da514c72045e675fc2f7a592d9da29dfe221d65ad6ce1d39d5efb6f6c1aa5d69fd2d0e602c00000000000000012e63386a0f0d72de7dab42e60f8d077837b86773ffc62eaa1e10158b7b4cdad4c68f4426c4b6a33659dc5c4f0ccc0e8b4831bb2cf5889feba458d7d9b0aecc95da8eb33c3366e3c3fff80cef436ab0b3ca9806f6acf700a4233119ea661db6a90a9b3509d2c3c6f083ada521c3d48b3e2406e473d85c9de5101005ba5a8b07dabc3657b9d47d92c049c3ddf85bf39c59df39d79728ee99799989bbb86c98bce11799f68243dd4a947b510fea0be52ab5b79176a44b5186ec22481e8a9d15fb730aeb29a68f0e3f2e1616f9a03312c65c66cdc03a37095d7e8f6eca40e95c3702e30b578510e3190cccd511a5670e56cc7f76c5be9ae9a4065614e89b8f8a76d999e1be8ffd3b4f3aab58cb6deec120506880f704dda2c0cd3dfa437b17289850fb857dbc399cf01361e1e683edfe9fe056e868d7758a996900a42b4aa985573b135fef949722254088656b9af2664cb707632407bc400af64d7ce937cde30bbe1f6012f92b7a76852c174ea159fc270b6119215e7fa315fbaeb8ce1fbcd3d385498295816c65938bb4dbcc25a7a6c55d7292b1a508cf4709d574c2e771a65a02ea74509004239a95ef67470b6e33a37338875bc210611c4174ec3e694e8654967266fb3d4f95eb6d54678aff5ed862c522ef45e3d0068b2d2da00dfa0e3ea668fc3d899810aefcabb4c6acf839e4f284841a2bd473d22291ab7b6fb9c99adb545bc7658794402d866f5bc414d60ae23b6dd297c38d86c88fd2c09b8ae0a6c3c3621785f11727477d9d2f83915231c84cf9de7c6c6d4dee4a1ee246e6184a3b9b5755db2a615d7ef3f4f6d13b1bf0bd70843b12748cf9fc4f06631368d2eead8deedc336a4ce02f0b222a179a1adda25e08a3c0b2d55d86b949b00dd2114c8d681bcae510b7513bbc7d77b19b4138650e253bee180e2d208a9596ed5ac1c10f0aeab771cb7b0e4539ba65c78730904dac974ec5bb43b19f961e57c2095781c6bd3d505f352175c679857a698c1ed5cd2b9812af7b75947b01695bacb106e062d077fff22f92656387ae5c02c980f83929e6b793f9c93c26e47b91bf10d73be2f344ff1bf4245cd3a5bb017222ea1081289e3a993adedaa7641957a29468f036b88aaf0aec22d948aeff5c4f53020220dfd146e211290476164635754508058c75d9229a688a0a0aea5f49f3ad0c72b6d7de2ae4fcfbe1fff15823b4643f11c188290de334bae6b22ab4a6bfd509f8cd989040bf5830e60259f34b97ee46d07e03025f8b6ecd49053c2881f1764c283c4cdbdda8c6f6177655eb7a2fbb506e33005a973a105fbefdbbcd0221f297b872b7213bb87cdce54690bdca0fef540b9df631a885a4f3905b2c635ca49a26c7d393a56de440765dbe48f85a7439582af0e6ff301f2a025413db9190e0cb41ebb0481f5dfc3c6468f55f95dedb43f366cf48af19ab6d4d0fe1511bb77992cfa119a990dec26ee6a95d465eb4da1e79e82e737f936b670a0c86196d02fd659014b3b1b3900f005f0818c5fb128a75671dbb436b998b1178ccca389555dec01a0d21fb599f608820887cbf7cc5f0cb3d58469091341794f0c68d040003621acfa2c7a3afff3ea9577f41d5ead8825eeb8808d6bd2c6b051ccb8f6a945475ca727f95d0ff52ba56e923e30b50f129d60083d6492c4233cb724b56b5cdd2d5764aaaa849bc046c8cc6dff65f8b74262f9248978cee12bb5f2505543235baf71aa0f501099e587a89815848b6f32e449c2cb7d8ef636a8fa08030172f1300f9f951dce8f8446c8f6d6e25aba12c95b9eb9bacbb4b49973e13785c53515949dae502860e681efef83e742edc0e9c594cf0c365a9825d32c8d434a4110393d3d44751f51f6b5f75782a419c19f3fa2c7d2ca5f11674da5ed10e45abfdd1f5f9a54361e4087071196834895922a1d974c7c4bb9898cf493704be17c086087ec6097cd30c02f6affeee3a0c946f58a61175ca3542b8852587d1dc86a1822f92214caf538519387da469166454532e8c1fcffbad4536078b53bdae5b81f2c00ca442530cb51bdee3f5363568a0b651c1459cb6c0e240c1dafe8f7da245427e3a126d544b343fc21bfff350a3267189e8808b5de5f386138efc0bc66413ac5fe32e13ad27cab2b8cdc2b7e2e19af39a6e0dbe4df4789161881080a53efecf1a1d40768b9edd9f07df9dc09d13592011fb19f1b1076bb3c1b1844e8423fbf48b0cf47fbcc9583d333edd2a559d1db72a2ce9a594fac9bced219c91b7453b0c2d2271760ed3d3cca940b1b383a7ee78165892b8f247eab95e0da506fae1e26815c651c30fdd0c14db08b9f41b0abe06aa5e167b2abc24399753f73a0246a66039cc5da16b1c3e4267ca093995e2521f600b39e150bc2a029212c3bf7e1528fe40893d196973d7e4e03ee754266d0766c44443f2da3199a9ffef4c598731353e710a16396078b89b6fe263e0dee52719cd38797ce263ce00ed7f8bd975171a9bf4adf5b841f9562c56defc15bf7abecbac2f5105ff7374d652f112733e296da779626d69db3ee4968776b97d431820dee2459408580f5eb515b7b12cf6174cec356288b3802a8af80bd8392dbe10159acf5502ec21c252dca61d598fe52703af4e3db32f9bdbde268451749a2a323574464066e82a24a191255802afea5803ebdaa52fc00d21e22a1a75bff7936e6a78de2eeea2fc2e9244fba601d4238bd1d920ba7437db789acfb0226fd97723d7ba4d502a6440d558c61f62690eb168429ee6f44fa0d014aeb52e177bff8159c532b68674fc8f279d61eaad6387dd317ce25ca02ca6095efa6a1615d6c29d132c67a26ee98a7e5157557530b2a5b9341cf8f83bc0a80c79b5a7a44aff0cebe1bfd100450004aa8ccc31fe2578f7ba3ff38de8d4d9b2cea03136f62fe9120b4b06ba290e80fa27ba39c5c95087998d4e80e436c7d9557302241ec99d5617b6f433e73323bd40c22cc20ec1464c843175abd5d056f6eb282b58ff8ab3938ec625835b66567bad93537146588231c31cb2420c8f3f4af7195395e3590e38cd2d8299a14f0c0a5e1118c0b70c86a5adc60846737d58d9605339a17d5ec700d480359a198101b9893c7b0de04d8043d09e61a8a667b45b4872f58a38d76bc8cee7cd598422a22924e6ebb5527a61524f76ab87027d2329544839ed320d8385e62d0868efd0b25e243b66ba0739227dc88b6dc84eaa37d7b1e0f342338f6562f920c821d9eeae2f3621bc4873f29e18bfb052ae9ed5b5cc05149d6d143afa00b9320dcdab8e7c5492a3d03435fe136a7f938e737662c6aada2427054bd8ce83f9c78785a9ca7003c38dd507c281c5947d31d82480e4f676279a62eb729846d234c21398a309349b91f6b95b9576adf47e9cf0a2696c456bd8167217951f83e1181244d58ac74a3c657ae1e8291521382d7ccbdc0ad84dab67d694ea7a811a733c57cd6d8d774da71d996f2db7ac6665a2d532cbdd36c07b439fb5c9502e0ec12d7a882af1a598261312fc91a351a64faea8c9399375506e0d3ce9b6805b7c2935566e9b886b9a40e2d0878f25bcbb2fffa52c14fb759051098f6037ae8b5e45979f84d3136eace071823fe827208dd82e7c94a4952296998c2d43cdb9d392aa9da6df55d4d3d364c5889d8c007858731df7102670101211574fe16bb9d7dda234175043ad31ec86fcb42735eed139943c8cffa592c47e074ea7625646fb35d9bf2c8ec79aa472b11ed551769170936423c6c0c6d686a737ec4568be08e718ef91b0df8fc197b241d22ecc9c1246aedab8d07bbcbcda7258f703c63336f34811b86a8a2d2a8e75ccbb2db336c905df51218c542b05b6dd53a55eee287a9c6fec8edd7f77a7597d3c6201fd5f1d72a7cf5eafaa56d4eea9bb59065b98d8761675844bed56b61d2ac2e95f1c737ed8c487066524cbcfb48e3a6d90eedff04c837135b231a1e8afc714e8ecaa25699e4308968a73924f21aa911fdf8e6ea3d912382bf1acb221b20b24578c9ac66d9e01cab9a75db0169814052261408b87ef94709d656bca2fd67bd3d9f813c7969d89a760473fba47a110e23bb6b62f8b2ba5d72df92c5640da00669cab7a9a92d69ed76566e8fa7183634abe25ffe62e1e8414480f847c3df9137e6535e46fa6e07af5e0ee8e22203b36793232d4a4bff3d8a0e2aa411c0c9fd1d32a4cf77281a664fbdf6f36c8712362a841afd0a5f432118e4ff6017369fd4b5252c663c2f9ec2fab4085551779cd1693630bcac744247216c71fcbf1b2ef74cf36e200d838bbc2188cd90895c168d4baaf1278728c8b959ab250d58504af5f1f30777529d6f44c17ddb5df640367aee115bc77aa0d63ae8ff82771fc35450f17e00ae2a96b623af9df80825f1d1610159e791fa3491ff872d4266feeace014dec77307f272f2a9d6d0e345b8947415d18aa697568840928bd576087ceb94d3070853c8abedc94a069d5654180301e1000f43977bd21eee5f0bd557d9bf5701bd7821f06cb510c271437c5cc68529587a3359be7fab0c2492984f9c01d5226096f020e586cacbdeb10fcaee578fc2dc91d34ae6680f553a78c4025a3885bae674460f2ff9e40cc3de6cc29c03d605a5cc33bdd82b673c2149bfdf4d0c861f8c19fc4ba540693516435d53e3e9eec2fcdfdfd4f7af0ad97af66b3294234e4b27ad3f3c83abe11f81f6abd102259d329a732df2047e54c8cf2924d4acbe7adcb49ceb2093fec928d5247a15b29f60011b1bfaa287f13a338827015b5f35f62dc64f9e12f6aa402de67ce1647628228e09a302ff9b0c8184501b5632be947374ed984de3ad0c7ef4a2bb69cd9c746edbc9e8144c5ead0c92a15c3da2fbf1b755e70c076ee80fa88d9dfa6a7027ad2c5213c88fe57415c7652ba003846d076134426665239e9b7b2d9367b27225b7a19ff99c20dbaa3f833e874b7edcfbb54a0097fcdcc41451ec718a29dd4f1e44b4200b6734dc9514090e119d57106577ef3431d8ab0e8c7253cb02e204232eec3370d806e99808b5d9a2e0986bfc34ec94a9107cc3799d238a29c235a869b7014226bdd6d7a476380dea0ed3107da8ba7af5842e675ff7a39fe1bd54b80000";

    BOOST_CHECK_NO_THROW(r = CallRPC(std::string("decoderawtransaction ")+rawtx2));
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "size").get_int(), 6695);
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "version").get_int(), 2);
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "locktime").get_int(), 0);
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "vin").get_array().size(), 1);
    BOOST_CHECK_EQUAL(find_value(find_value(r.get_obj(), "vin").get_array()[0].get_obj(), "txid").get_str(), "47bba0c30ceb48fee6d7a33fd3ad70c048510500412ac81198d6de9f25f791d5");
    BOOST_CHECK_EQUAL(find_value(r.get_obj(), "vout").get_array().size(), 3);
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
