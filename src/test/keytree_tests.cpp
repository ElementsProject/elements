// Copyright (c) 2015 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "util.h"
#include <stdio.h>

#include <boost/test/unit_test.hpp>

#include "core_io.h"
#include "thresholdtree.h"
#include "keytree.h"
#include "key.h"
#include "keystore.h"
#include "script/script.h"
#include "script/sign.h"
#include "script/standard.h"

BOOST_AUTO_TEST_SUITE(keytree_tests)

struct SimpleTree {
    std::vector<SimpleTree> children;
    int leaf;
    int threshold;

    inline int Children() const { return children.size(); }
    inline int Threshold() const { return threshold; }
    inline bool IsLeaf() const { return children.size() == 0; }
    inline SimpleTree* Child(int pos) { return &children[pos]; }
};

struct TestAccumulator {
    std::vector<int> x;
    void Push(SimpleTree* v) {
        x.push_back(v->leaf);
    }
    void Pop(SimpleTree* v) {
        BOOST_CHECK(x.size() >= 1);
        BOOST_CHECK_EQUAL(x.back(), v->leaf);
        x.pop_back();
    }

    void Test(int a, int b, int c, int d) {
        BOOST_CHECK_EQUAL(x.size(), 4);
        BOOST_CHECK_EQUAL(x[0], a);
        BOOST_CHECK_EQUAL(x[1], b);
        BOOST_CHECK_EQUAL(x[2], c);
        BOOST_CHECK_EQUAL(x[3], d);
    }
};

BOOST_AUTO_TEST_CASE(thresholdtree_test)
{
    SimpleTree root;
    root.threshold = 2;
    root.children.resize(3);
    root.children[0].threshold = 2;
    root.children[0].children.resize(3);
    root.children[0].children[0].leaf = 11;
    root.children[0].children[1].leaf = 12;
    root.children[0].children[2].leaf = 13;
    root.children[1].threshold = 2;
    root.children[1].children.resize(3);
    root.children[1].children[0].leaf = 21;
    root.children[1].children[1].leaf = 22;
    root.children[1].children[2].leaf = 23;
    root.children[2].threshold = 2;
    root.children[2].children.resize(3);
    root.children[2].children[0].leaf = 31;
    root.children[2].children[1].leaf = 32;
    root.children[2].children[2].leaf = 33;

    ThresholdTreeIterator<SimpleTree, TestAccumulator> iter(&root);
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 12, 21, 22); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 12, 21, 23); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 12, 22, 23); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 13, 21, 22); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 13, 21, 23); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 13, 22, 23); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(12, 13, 21, 22); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(12, 13, 21, 23); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(12, 13, 22, 23); iter.Increment();

    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 12, 31, 32); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 12, 31, 33); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 12, 32, 33); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 13, 31, 32); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 13, 31, 33); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(11, 13, 32, 33); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(12, 13, 31, 32); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(12, 13, 31, 33); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(12, 13, 32, 33); iter.Increment();

    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(21, 22, 31, 32); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(21, 22, 31, 33); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(21, 22, 32, 33); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(21, 23, 31, 32); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(21, 23, 31, 33); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(21, 23, 32, 33); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(22, 23, 31, 32); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(22, 23, 31, 33); iter.Increment();
    BOOST_CHECK(iter.Valid()); iter.GetAccumulator()->Test(22, 23, 32, 33); iter.Increment();

    BOOST_CHECK(!iter.Valid());

    int64_t count = CountCombinations(&root);
    BOOST_CHECK_EQUAL(count, 27);
}

CKey SecKeyNum(uint32_t x) {
    unsigned char data[32] = {0};
    data[31] = x & 0xFF;
    data[30] = (x >> 8) & 0xFF;
    data[29] = (x >> 16) & 0xFF;
    data[28] = (x >> 24) & 0xFF;
    CKey key;
    key.Set(&data[0], &data[32], true);
    return key;
}

CPubKey KeyNum(uint32_t x) {
    CKey key = SecKeyNum(x);
    return key.GetPubKey();
}

uint256 KeyNumHash(uint32_t i) {
    CPubKey x = KeyNum(i);
    assert(x.size() == 33);
    uint256 ret;
    CSHA256().Write(x.begin(), 33).Finalize(ret.begin());
    return ret;
}

uint256 CombineTwoHashes(const uint256& x, const uint256& y) {
    uint256 ret;
    CSHA256().Write(x.begin(), 32).Write(y.begin(), 32).Finalize(ret.begin());
    return ret;
}

uint256 CombineOneHash(const uint256& x) {
    uint256 ret;
    static const unsigned char one[1] = {1};
    CSHA256().Write(x.begin(), 32).Write(one, 1).Finalize(ret.begin());
    return ret;
}

struct SetKeyTreeFilter : public KeyTreeFilter
{
    std::set<CPubKey> valid;

    bool operator()(const CPubKey& key) {
        return valid.count(key);
    }

    SetKeyTreeFilter() {}

    SetKeyTreeFilter(const CPubKey& key) {
        valid.insert(key);
    }
};

BOOST_AUTO_TEST_CASE(keytree_test0)
{
    /*            1
     */

    static const std::string formatted =
        "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
    KeyTree tree;
    BOOST_CHECK(ParseKeyTree(formatted, tree));
    BOOST_CHECK_EQUAL(FormatKeyTree(tree), formatted);
    BOOST_CHECK_EQUAL(tree.levels, 0);

    KeyTreeNode root;
    root.leaf = KeyNum(1);
    uint64_t count;
    uint256 rootA = GetMerkleRoot(&root, &count);
    BOOST_CHECK_EQUAL(count, 1);
    BOOST_CHECK(rootA == tree.hash);
    BOOST_CHECK(tree.root == root);

    uint256 rootB = KeyNumHash(1);
    BOOST_CHECK(rootA == rootB);

    uint256 rootC;
    uint64_t countC;
    uint64_t positionC;
    std::vector<uint256> branch;
    std::vector<CPubKey> pubkeys;
    SetKeyTreeFilter filterkey(KeyNum(1));
    BOOST_CHECK(GetMerkleBranch(&root, &filterkey, &rootC, &countC, &positionC, &branch, &pubkeys));
    BOOST_CHECK(rootA == rootC);
    BOOST_CHECK_EQUAL(count, countC);
    BOOST_CHECK_EQUAL(positionC, 0);
    BOOST_CHECK_EQUAL(branch.size(), 0);
    BOOST_CHECK_EQUAL(pubkeys.size(), 1);
    BOOST_CHECK(pubkeys[0] == KeyNum(1));

    SetKeyTreeFilter filterkeynone;
    BOOST_CHECK(GetMerkleBranch(&root, &filterkeynone, &rootC, &countC, &positionC, &branch) == false);

    CMutableTransaction mtxFrom;
    mtxFrom.vout.resize(1);
    mtxFrom.vout[0].scriptPubKey = GetScriptForTree(tree);
    CTransaction txFrom(mtxFrom);
    CMutableTransaction mtxTo;
    mtxTo.vin.resize(1);
    mtxTo.vin[0].prevout.hash = txFrom.GetHash();
    mtxTo.vin[0].prevout.n = 0;
    CBasicKeyStore keystore;
    keystore.AddKeyTree(tree);
    keystore.AddKey(SecKeyNum(1));
    BOOST_CHECK(SignSignature(keystore, txFrom, mtxTo, 0));
    BOOST_CHECK_EQUAL(mtxTo.vin[0].scriptSig.ToString(),
        "6438800535962d52309f384d257e30bdeeaf895d49f80dfa73787426997324c77adb3d"
        "94c052c0cf7e52783d7f8346255e5f4bac42f8e13eeb4f587175b93c1e01 0279be667"
        "ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798");
}

BOOST_AUTO_TEST_CASE(keytree_test1)
{
    /*            1-of
     *         /   |  \
     *      /      |     \
     *     1       2      4
     */

    static const std::string formatted =
        "OR(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,"
        "02c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5,02e"
        "493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd13)";
    KeyTree tree;
    BOOST_CHECK(ParseKeyTree(formatted, tree));
    BOOST_CHECK_EQUAL(FormatKeyTree(tree), formatted);
    BOOST_CHECK_EQUAL(tree.levels, 2);

    KeyTreeNode root;
    root.threshold = 1;
    root.children.resize(3);
    for (int i = 0; i < 3; i++) {
        root.children[i].leaf = KeyNum(1 << i);
    }
    uint64_t count;
    uint256 rootA = GetMerkleRoot(&root, &count);
    BOOST_CHECK_EQUAL(count, 3);
    BOOST_CHECK(rootA == tree.hash);
    BOOST_CHECK(tree.root == root);

    uint256 hashes0[12] = {
        KeyNumHash(1), KeyNumHash(2), KeyNumHash(4)
    };
    uint256 hashes1[6] = {
        CombineTwoHashes(hashes0[0], hashes0[1]), CombineOneHash(hashes0[2]),
    };
    uint256 rootB = CombineTwoHashes(hashes1[0], hashes1[1]);
    BOOST_CHECK(rootA == rootB);

    uint256 rootC;
    uint64_t countC;
    uint64_t positionC;
    std::vector<uint256> branch;
    std::vector<CPubKey> pubkeys;
    SetKeyTreeFilter filterkey4(KeyNum(4));
    BOOST_CHECK(GetMerkleBranch(&root, &filterkey4, &rootC, &countC, &positionC, &branch, &pubkeys));
    BOOST_CHECK(rootA == rootC);
    BOOST_CHECK_EQUAL(count, countC);
    BOOST_CHECK_EQUAL(positionC, 2);
    BOOST_CHECK_EQUAL(branch.size(), 2);
    BOOST_CHECK(branch[0] == uint256());
    BOOST_CHECK(branch[1] == hashes1[0]);
    BOOST_CHECK_EQUAL(pubkeys.size(), 1);
    BOOST_CHECK(pubkeys[0] == KeyNum(4));

    SetKeyTreeFilter filterkeynone;
    BOOST_CHECK(GetMerkleBranch(&root, &filterkeynone, &rootC, &countC, &positionC, &branch) == false);

    CMutableTransaction mtxFrom;
    mtxFrom.vout.resize(1);
    mtxFrom.vout[0].scriptPubKey = GetScriptForTree(tree);
    CTransaction txFrom(mtxFrom);
    CMutableTransaction mtxTo;
    mtxTo.vin.resize(1);
    mtxTo.vin[0].prevout.hash = txFrom.GetHash();
    mtxTo.vin[0].prevout.n = 0;
    CBasicKeyStore keystore;
    keystore.AddKeyTree(tree);
    keystore.AddKey(SecKeyNum(1));
    BOOST_CHECK(SignSignature(keystore, txFrom, mtxTo, 0));
    BOOST_CHECK_EQUAL(mtxTo.vin[0].scriptSig.ToString(),
        "4ea7e71ddab23f1e9991bfe7579dd777cf68699a6c4809d69ab197f1a4709ced177ec2"
        "bf9864b147c85faab20783830be9fb9507ee5649cc14f13314e098d1b001 0279be667"
        "ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798 ed057686095e"
        "5e9df917f11adf776e27199f80c34bdf106d76d91d8ec6c41cde 1 b1c9938f01121e1"
        "59887ac2c8d393a22e4476ff8212de13fe1939de2a236f0a7 1");
}

BOOST_AUTO_TEST_CASE(keytree_test2)
{
    /*            2-of
     *         /   |  \
     *      /      |     \
     *    1-of   1-of   1-of
     *    /  \   /  \   /  \
     *    1  2  4   8  16  32
     */
    static const std::string formatted =
        "THRESHOLD(2,OR(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f28"
        "15b16f81798,02c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b9"
        "5c709ee5),OR(02e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94a"
        "be8c4cd13,022f01e5e15cca351daff3843fb70f3c2f0a1bdd05e5af888a67784ef3e1"
        "0a2a01),OR(03e60fce93b59e9ec53011aabc21c23e97b2a31369b87a5ae9c44ee89e2"
        "a6dec0a,03d30199d74fb5a22d47b6e054e2f378cedacffcb89904a61d75d0dbd40714"
        "3e65))";
    KeyTree tree;
    BOOST_CHECK(ParseKeyTree(formatted, tree));
    BOOST_CHECK_EQUAL(FormatKeyTree(tree), formatted);
    BOOST_CHECK_EQUAL(tree.levels, 4);

    KeyTreeNode root;
    root.threshold = 2;
    root.children.resize(3);
    for (int i = 0; i < 3; i++) {
        root.children[i].threshold = 1;
        root.children[i].children.resize(2);
        for (int j = 0; j < 2; j++) {
            root.children[i].children[j].leaf = KeyNum(1 << (2*i + j));
        }
    }
    uint64_t count;
    uint256 rootA = GetMerkleRoot(&root, &count);
    BOOST_CHECK_EQUAL(count, 12);
    BOOST_CHECK(rootA == tree.hash);
    BOOST_CHECK(tree.root == root);

    uint256 hashes0[12] = {
        KeyNumHash(5), KeyNumHash(9), KeyNumHash(6), KeyNumHash(10),
        KeyNumHash(17), KeyNumHash(33), KeyNumHash(18), KeyNumHash(34),
        KeyNumHash(20), KeyNumHash(36), KeyNumHash(24), KeyNumHash(40)
    };
    uint256 hashes1[6] = {
        CombineTwoHashes(hashes0[0], hashes0[1]), CombineTwoHashes(hashes0[2], hashes0[3]),
        CombineTwoHashes(hashes0[4], hashes0[5]), CombineTwoHashes(hashes0[6], hashes0[7]),
        CombineTwoHashes(hashes0[8], hashes0[9]), CombineTwoHashes(hashes0[10], hashes0[11])
    };
    uint256 hashes2[3] = {
        CombineTwoHashes(hashes1[0], hashes1[1]), CombineTwoHashes(hashes1[2], hashes1[3]),
        CombineTwoHashes(hashes1[4], hashes1[5])
    };
    uint256 hashes3[2] = {
        CombineTwoHashes(hashes2[0], hashes2[1]), CombineOneHash(hashes2[2])
    };
    uint256 rootB = CombineTwoHashes(hashes3[0], hashes3[1]);
    BOOST_CHECK(rootA == rootB);

    SetKeyTreeFilter filterkey;
    filterkey.valid.insert(KeyNum(16));
    filterkey.valid.insert(KeyNum(8));
    filterkey.valid.insert(KeyNum(32));
    uint256 rootC;
    uint64_t countC;
    uint64_t positionC;
    std::vector<uint256> branch;
    std::vector<CPubKey> pubkeys;
    BOOST_CHECK(GetMerkleBranch(&root, &filterkey, &rootC, &countC, &positionC, &branch, &pubkeys));
    BOOST_CHECK(rootA == rootC);
    BOOST_CHECK(count == countC);
    BOOST_CHECK(positionC == 10);
    BOOST_CHECK(branch.size() == 4);
    BOOST_CHECK(branch[0] == hashes0[11]);
    BOOST_CHECK(branch[1] == hashes1[4]);
    BOOST_CHECK(branch[2] == uint256());
    BOOST_CHECK(branch[3] == hashes3[0]);
    BOOST_CHECK(pubkeys.size() == 2);
    BOOST_CHECK(pubkeys[0] == KeyNum(8));
    BOOST_CHECK(pubkeys[1] == KeyNum(16));

    CScript redeemScript = GetScriptForTree(tree);
    CScriptID p2sh(redeemScript);
    CMutableTransaction mtxFrom;
    mtxFrom.vout.resize(1);
    mtxFrom.vout[0].scriptPubKey = GetScriptForDestination(p2sh);
    CTransaction txFrom(mtxFrom);
    CMutableTransaction mtxTo;
    mtxTo.vin.resize(1);
    mtxTo.vin[0].prevout.hash = txFrom.GetHash();
    mtxTo.vin[0].prevout.n = 0;
    CBasicKeyStore keystore1;
    keystore1.AddKeyTree(tree);
    keystore1.AddCScript(redeemScript);
    keystore1.AddKey(SecKeyNum(4));
    keystore1.AddKey(SecKeyNum(8));
    BOOST_CHECK(!SignSignature(keystore1, txFrom, mtxTo, 0));
    CBasicKeyStore keystore2;
    keystore2.AddKeyTree(tree);
    keystore2.AddCScript(redeemScript);
    keystore2.AddKey(SecKeyNum(16));
    BOOST_CHECK(!SignSignature(keystore2, txFrom, mtxTo, 0));
    BOOST_CHECK(SignSignature(keystore1, txFrom, mtxTo, 0));
    BOOST_CHECK_EQUAL(mtxTo.vin[0].scriptSig.ToString(),
        "24199b18f2148c9521c7ec97f49c5241a3ec47d2a08257f9671683aaee1a8a3bc8c2ff"
        "3b9cc77c97ed863565e939494e61623d2537b9458303c340c7a7689c6701 024ce119c"
        "96e2fa357200b559b2f7dd5a5f02d5290aff74b03f3e471b273211c97 bd2a91465655"
        "067eadb86cf4f660671e63566c71a5328adfbcde342c17d5e450 0 1 1 6e7468b3b7a"
        "82215ee3a373a658ce4bc6ad11c53fa9c896f3239650442c1f0a3 1 5417114a2fc7e0"
        "f1cd82684c9b0ca852ceb600562a6adeb18cc795c2efdd9c63 1 5879a87c637c687ea"
        "87c637c687ea87c637c687ea87c637c687ea820927db000c4bfec1a1f6c07cb13b36f9"
        "593300885b5d816f64c269245c02724f588ac");
}

BOOST_AUTO_TEST_CASE(keytree_test3)
{
    /*            2-of
     *         /   |  \
     *      /      |     \
     *     1     1-of   2-of
     *           /  \   /  \
     *          2    4  8  16
     */
    static const std::string formatted =
        "THRESHOLD(2,0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b"
        "16f81798,OR(02c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b9"
        "5c709ee5,02e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c"
        "4cd13),AND(022f01e5e15cca351daff3843fb70f3c2f0a1bdd05e5af888a67784ef3e"
        "10a2a01,03e60fce93b59e9ec53011aabc21c23e97b2a31369b87a5ae9c44ee89e2a6d"
        "ec0a))";
    KeyTree tree;
    BOOST_CHECK(ParseKeyTree(formatted, tree));
    BOOST_CHECK_EQUAL(FormatKeyTree(tree), formatted);
    BOOST_CHECK_EQUAL(tree.levels, 3);

    KeyTreeNode root;
    root.threshold = 2;
    root.children.resize(3);
    root.children[0].leaf = KeyNum(1);
    root.children[1].threshold = 1;
    root.children[1].children.resize(2);
    root.children[1].children[0].leaf = KeyNum(2);
    root.children[1].children[1].leaf = KeyNum(4);
    root.children[2].threshold = 2;
    root.children[2].children.resize(2);
    root.children[2].children[0].leaf = KeyNum(8);
    root.children[2].children[1].leaf = KeyNum(16);
    uint64_t count;
    uint256 rootA = GetMerkleRoot(&root, &count);
    BOOST_CHECK_EQUAL(count, 5);
    BOOST_CHECK(rootA == tree.hash);
    BOOST_CHECK(tree.root == root);

    uint256 hashes0[5] = {
        KeyNumHash(3), KeyNumHash(5), KeyNumHash(25), KeyNumHash(26),
        KeyNumHash(28)
    };
    uint256 hashes1[3] = {
        CombineTwoHashes(hashes0[0], hashes0[1]), CombineTwoHashes(hashes0[2], hashes0[3]),
        CombineOneHash(hashes0[4]),
    };
    uint256 hashes2[2] = {
        CombineTwoHashes(hashes1[0], hashes1[1]), CombineOneHash(hashes1[2])
    };
    uint256 rootB = CombineTwoHashes(hashes2[0], hashes2[1]);
    BOOST_CHECK(rootA == rootB);

    SetKeyTreeFilter filterkey;
    filterkey.valid.insert(KeyNum(2));
    filterkey.valid.insert(KeyNum(4));
    filterkey.valid.insert(KeyNum(8));
    filterkey.valid.insert(KeyNum(16));
    uint256 rootC;
    uint64_t countC;
    uint64_t positionC;
    std::vector<uint256> branch;
    std::vector<CPubKey> pubkeys;
    BOOST_CHECK(GetMerkleBranch(&root, &filterkey, &rootC, &countC, &positionC, &branch, &pubkeys));
    BOOST_CHECK(rootA == rootC);
    BOOST_CHECK(count == countC);
    BOOST_CHECK(positionC == 3);
    BOOST_CHECK(branch.size() == 3);
    BOOST_CHECK(branch[0] == hashes0[2]);
    BOOST_CHECK(branch[1] == hashes1[0]);
    BOOST_CHECK(branch[2] == hashes2[1]);
    BOOST_CHECK(pubkeys.size() == 3);
    BOOST_CHECK(pubkeys[0] == KeyNum(2));
    BOOST_CHECK(pubkeys[1] == KeyNum(8));
    BOOST_CHECK(pubkeys[2] == KeyNum(16));
}

BOOST_AUTO_TEST_CASE(keytree_test4)
{
    /*            3-of
     *         /   |  \
     *      /      |     \
     *     1      2-of    8
     *           /    \
     *          2      4
     */

    static const std::string formatted =
        "AND(0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
        ",AND(02c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee"
        "5,02e493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd13),"
        "022f01e5e15cca351daff3843fb70f3c2f0a1bdd05e5af888a67784ef3e10a2a01)";
    KeyTree tree;
    BOOST_CHECK(ParseKeyTree(formatted, tree));
    BOOST_CHECK_EQUAL(FormatKeyTree(tree), formatted);
    BOOST_CHECK_EQUAL(tree.levels, 0);

    KeyTreeNode root;
    root.threshold = 3;
    root.children.resize(3);
    root.children[0].leaf = KeyNum(1);
    root.children[1].threshold = 2;
    root.children[1].children.resize(2);
    root.children[1].children[0].leaf = KeyNum(2);
    root.children[1].children[1].leaf = KeyNum(4);
    root.children[2].leaf = KeyNum(8);

    uint64_t count;
    uint256 rootA = GetMerkleRoot(&root, &count);
    BOOST_CHECK_EQUAL(count, 1);
    BOOST_CHECK(rootA == tree.hash);
    BOOST_CHECK(tree.root == root);

    uint256 rootB = KeyNumHash(15);
    BOOST_CHECK(rootA == rootB);

    uint256 rootC;
    uint64_t countC;
    uint64_t positionC;
    std::vector<uint256> branch;
    std::vector<CPubKey> pubkeys;
    SetKeyTreeFilter filterkey;
    filterkey.valid.insert(KeyNum(1));
    filterkey.valid.insert(KeyNum(2));
    filterkey.valid.insert(KeyNum(8));
    filterkey.valid.insert(KeyNum(4));
    BOOST_CHECK(GetMerkleBranch(&root, &filterkey, &rootC, &countC, &positionC, &branch, &pubkeys));
    BOOST_CHECK(rootA == rootC);
    BOOST_CHECK_EQUAL(count, countC);
    BOOST_CHECK_EQUAL(positionC, 0);
    BOOST_CHECK_EQUAL(branch.size(), 0);
    BOOST_CHECK_EQUAL(pubkeys.size(), 4);
    BOOST_CHECK(pubkeys[0] == KeyNum(1));
    BOOST_CHECK(pubkeys[1] == KeyNum(2));
    BOOST_CHECK(pubkeys[2] == KeyNum(4));
    BOOST_CHECK(pubkeys[3] == KeyNum(8));

    SetKeyTreeFilter filterkeynone;
    BOOST_CHECK(GetMerkleBranch(&root, &filterkeynone, &rootC, &countC, &positionC, &branch) == false);

    CMutableTransaction mtxFrom;
    mtxFrom.vout.resize(1);
    mtxFrom.vout[0].scriptPubKey = GetScriptForTree(tree);
    CTransaction txFrom(mtxFrom);
    CMutableTransaction mtxTo;
    mtxTo.vin.resize(1);
    mtxTo.vin[0].prevout.hash = txFrom.GetHash();
    mtxTo.vin[0].prevout.n = 0;

    CBasicKeyStore keystore1;
    keystore1.AddKeyTree(tree);
    keystore1.AddKey(SecKeyNum(1));
    CBasicKeyStore keystore2;
    keystore2.AddKeyTree(tree);
    keystore2.AddKey(SecKeyNum(2));
    CBasicKeyStore keystore3;
    keystore3.AddKeyTree(tree);
    keystore3.AddKey(SecKeyNum(4));
    CBasicKeyStore keystore4;
    keystore4.AddKeyTree(tree);
    keystore4.AddKey(SecKeyNum(8));
    BOOST_CHECK(!SignSignature(keystore1, txFrom, mtxTo, 0));
    BOOST_CHECK(!SignSignature(keystore2, txFrom, mtxTo, 0));
    BOOST_CHECK(!SignSignature(keystore3, txFrom, mtxTo, 0));
    BOOST_CHECK(!SignSignature(keystore4, txFrom, mtxTo, 0));
    BOOST_CHECK(!SignSignature(keystore2, txFrom, mtxTo, 0));
    BOOST_CHECK(!SignSignature(keystore1, txFrom, mtxTo, 0));
    BOOST_CHECK(SignSignature(keystore3, txFrom, mtxTo, 0));
    BOOST_CHECK_EQUAL(mtxTo.vin[0].scriptSig.ToString(),
        "e3cefe369d7d75472ef307ab9a4a13ddc9b2eac7304c93a47ac715d701f0347d89cdbd"
        "c19f173cc8143091c9206f5648691f5dffa8a3570ec10ae101a9b48d7f01 02d7924d4"
        "f7d43ea965a465ae3095ff41131e5946f3c85f79e44adbcf8e27e080e");
}

BOOST_AUTO_TEST_SUITE_END()
