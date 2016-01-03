// Copyright (c) 2015 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_KEYTREE_H
#define BITCOIN_KEYTREE_H

#include "thresholdtree.h"
#include "pubkey.h"

/* A node in a threshold tree of public keys.
 * Such a tree represents a set of valid combinations of public keys in a compact way.
 *
 * For example:
 *           thr=2
 *         /   |      \
 *      /      |           \
 *   leafA  thr=1          thr=2
 *           /  \         /     \
 *       leafB leafC   leafD   leafE
 *
 * Corresponds to the combinations (A,B), (A,C), (A,D,E), (B,D,E), (C,D,E).
 */
struct KeyTreeNode {
    //! The public key this node requires signing with (only used in leaf node, which have threshold == 0).
    CPubKey leaf;

    //! The child nodes of this node (only used when this is an inner node, which have threshold > 0).
    std::vector<KeyTreeNode> children;

    //! The number of child nodes that need to be satisfied before this node is considered satisfied.
    uint32_t threshold;

    ADD_SERIALIZE_METHODS;

    KeyTreeNode() : threshold(0) {}

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion)
    {
        READWRITE(VARINT(threshold));
        if (threshold) {
            READWRITE(children);
        } else {
            READWRITE(leaf);
        }
    }

    friend bool operator==(const KeyTreeNode &a, const KeyTreeNode &b) {
        if (a.threshold != b.threshold) return false;
        if (a.threshold) {
            return (a.children == b.children);
        } else {
            return (a.leaf == b.leaf);
        }
    }

};

/* Wrapper around an entire key tree, with precomputed Merkle root and level count. */
struct KeyTree {
    uint256 hash;
    int levels;
    KeyTreeNode root;

    ADD_SERIALIZE_METHODS;

    KeyTree() : levels(0) {}

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion)
    {
        READWRITE(hash);
        READWRITE(VARINT(levels));
        READWRITE(root);
    }
};

struct KeyTreeFilter {
    virtual bool operator()(const CPubKey& pubkey) = 0;
    virtual ~KeyTreeFilter() {}
};


uint64_t GetCombinations(const KeyTreeNode* tree);
uint256 GetMerkleRoot(const KeyTreeNode* tree, uint64_t* count);
bool GetMerkleBranch(const KeyTreeNode* tree, KeyTreeFilter* filter, uint256* root, uint64_t* count, uint64_t* matchpos, std::vector<uint256>* branch, std::vector<CPubKey>* pubkeys = NULL);
uint256 GetMerkleRootFromBranch(const uint256& leaf, std::vector<uint256>& branch, uint64_t position);
bool HasMatch(const KeyTreeNode* tree, KeyTreeFilter* filter);
std::set<CPubKey> GetAllLeaves(const KeyTreeNode* tree);

#endif
