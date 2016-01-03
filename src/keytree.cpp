// Copyright (c) 2015 Pieter Wuille
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <vector>

#include "hash.h"
#include "keytree.h"
#include "pubkey.h"
#include "crypto/sha256.h"

#include <secp256k1.h>

extern secp256k1_context_t* secp256k1_bitcoin_verify_context;

namespace {

/* This implements a constant-space merkle root/branch calculator, limited to 2^63 leaves. */
template<typename LeafSource>
void MerkleComputation(LeafSource& source, uint256* proot, std::vector<uint256>* pbranch) {
    if (pbranch) pbranch->clear();
    if (!source.Valid()) {
        if (proot) *proot = uint256();
        return;
    }
    // count is the number of leaves processed so far.
    uint64_t count = 0;
    // inner is an array of eagerly computed subtree hashes, indexed by tree
    // level (0 being the leaves).
    // For example, when count is 25 (11001 in binary), inner[4] is the hash of
    // the first 16 leaves, inner[3] of the next 8 leaves, and inner[0] equal to
    // the last leaf. The other inner entries are undefined.
    uint256 inner[64];
    // Which position in inner is a hash that depends on the matching leaf.
    int matchlevel = -1;
    // First process all leaves into 'inner' values.
    while (source.Valid()) {
        uint256 h = source.Get();
        // If there has been no match before, check whether the current leaf is.
        bool matchh = (matchlevel == -1) && source.Match();
        count++;
        source.Increment();
        int level;
        // For each of the lower bits in count that are 0, do 1 step. Each
        // corresponds to an inner value that existed before processing the
        // current leaf, and each needs a hash to combine it.
        for (level = 0; !(count & (((uint64_t)1) << level)); level++) {
            if (pbranch) {
                if (matchh) {
                    pbranch->push_back(inner[level]);
                } else if (matchlevel == level) {
                    pbranch->push_back(h);
                    matchh = true;
                }
            }
            CSHA256().Write(inner[level].begin(), 32).Write(h.begin(), 32).Finalize(h.begin());
        }
        // Store the resulting hash at inner position level.
        inner[level] = h;
        if (matchh) {
            matchlevel = level;
        }
    }
    // Do a final 'sweep' over the rightmost branch of the tree to process
    // odd levels, and reduce everything to a single top value.
    // Level is the level (counted from the bottom) up to which we've sweeped.
    int level = 0;
    // As long as bit number level in count is zero, skip it. It means there
    // is nothing left at this level.
    while (!(count & (((uint64_t)1) << level))) {
        level++;
    }
    uint256 h = inner[level];
    bool matchh = matchlevel == level;
    static const unsigned char one[1] = {1};
    while (count != (((uint64_t)1) << level)) {
        // If we reach this point, h is an inner value that is not the top.
        // We combine it with 1 (special rule for odd levels) to produce a higher level one.
        if (pbranch && matchh) {
            pbranch->push_back(uint256());
        }
        CSHA256().Write(h.begin(), 32).Write(one, 1).Finalize(h.begin());
        // Increment count to the value it would have if two entries at this
        // level had existed.
        count += (((uint64_t)1) << level);
        level++;
        // And propagate the result upwards accordingly.
        while (!(count & (((uint64_t)1) << level))) {
            if (pbranch) {
                if (matchh) {
                    pbranch->push_back(inner[level]);
                } else if (matchlevel == level) {
                    pbranch->push_back(h);
                    matchh = true;
                }
            }
            CSHA256().Write(inner[level].begin(), 32).Write(h.begin(), 32).Finalize(h.begin());
            level++;
        }
    }
    // Return result.
    if (proot) *proot = h;
}

// Lazily constructed wrapper around KeyTreeNode, suitable for use with ThresholdTreeIterator,
// with cached parsed pubkeys.
struct InnerKeyTree {
    const KeyTreeNode* node;
    bool processed;
    bool cached_pubkey;
    bool cached_match;
    bool match;
    secp256k1_pubkey_t pubkey;
    std::vector<InnerKeyTree> children;

    InnerKeyTree() : node(NULL), processed(true), cached_pubkey(true), cached_match(true), match(false) {}
    InnerKeyTree(const KeyTreeNode* node_) : node(node_), processed(false), cached_pubkey(false), cached_match(false), match(false) {}

    void Process() {
        if (processed) return;
        processed = true;
        children.resize(node->children.size());
        for (size_t i = 0; i < children.size(); i++) {
            children[i] = InnerKeyTree(&node->children[i]);
        }
    }

    bool IsLeaf() const { return node->threshold == 0; }
    uint32_t Threshold() const { return node->threshold; }
    uint32_t Children() { return node->children.size(); }
    InnerKeyTree* Child(int pos) { Process(); return &children[pos]; }

    const secp256k1_pubkey_t* GetParsedPubKey() {
        if (!cached_pubkey) {
            assert(secp256k1_ec_pubkey_parse(secp256k1_bitcoin_verify_context, &pubkey, node->leaf.begin(), node->leaf.size()));
            cached_pubkey = true;
        }
        return &pubkey;
    }

    const CPubKey* GetPubKey() {
        return &node->leaf;
    }

    bool Matches(KeyTreeFilter& filter) {
        if (!cached_match) {
            match = filter(node->leaf);
            cached_match = true;
        }
        return match;
    }
};

// An accumulator for ThresholdTreeIterator taking leaf InnerKeyTree*'s, and supporting the computation of hashes of the combined solution pubkey sets.
struct CombinedKeyHashingAccumulator {
    std::vector<InnerKeyTree*> leaves;
    uint32_t first_non_match_before;
    KeyTreeFilter* filter;

    CombinedKeyHashingAccumulator(KeyTreeFilter* filter_ = NULL) : first_non_match_before(0), filter(filter_) {}

    void Push(InnerKeyTree* x) {
        leaves.push_back(x);
        if ((!first_non_match_before) && filter && !x->Matches(*filter)) {
            first_non_match_before = leaves.size();
        }
    }

    void Pop(InnerKeyTree* x) {
        (void)x;
        if (first_non_match_before == leaves.size()) {
            first_non_match_before = 0;
        }
        leaves.pop_back();
    }

    uint256 ComputeHash() const {
        uint256 ret;
        if (leaves.size() == 1) {
            // When there is just a single key, do not parse and reserialize.
            const CPubKey* pubkey = leaves[0]->GetPubKey();
            CSHA256().Write(pubkey->begin(), pubkey->size()).Finalize(ret.begin());
        } else {
            unsigned char pubkey[33];
            int pubkeylen = 33;
            std::vector<const secp256k1_pubkey_t*> keys;
            keys.resize(leaves.size());
            for (size_t i = 0; i < leaves.size(); i++) {
                keys[i] = leaves[i]->GetParsedPubKey();
            }
            secp256k1_pubkey_t key;
            assert(secp256k1_ec_pubkey_combine(secp256k1_bitcoin_verify_context, &key, keys.size(), &keys[0]));
            secp256k1_ec_pubkey_serialize(secp256k1_bitcoin_verify_context, pubkey, &pubkeylen, &key, 1);
            CSHA256().Write(pubkey, 33).Finalize(ret.begin());
        }
        return ret;
    }

    bool Matches() {
        return (filter != NULL && first_non_match_before == 0);
    }

    std::vector<CPubKey> GetMatch() const {
        std::vector<CPubKey> pubkeys;
        pubkeys.reserve(leaves.size());
        for (std::vector<InnerKeyTree*>::const_iterator it = leaves.begin(); it != leaves.end(); it++) {
            pubkeys.push_back((*it)->node->leaf);
        }
        return pubkeys;
    }
};

// Wrapper around a ThresholdTreeIterator for InnerKeyTrees, producing hashes of the combined pubkeys of the solution sets.
struct InnerKeyTreeIteratorLeafSource {
    InnerKeyTree root;
    ThresholdTreeIterator<InnerKeyTree, CombinedKeyHashingAccumulator> iter;
    uint64_t count;
    uint64_t matchpos;
    bool hadmatch;
    std::vector<CPubKey>* match;

    InnerKeyTreeIteratorLeafSource(const KeyTreeNode *tree, KeyTreeFilter* filter, std::vector<CPubKey>* matchout) : root(tree), iter(&root, filter), count(0), matchpos(0), hadmatch(false), match(matchout) {}

    bool Valid() const {
        return iter.Valid();
    }

    uint256 Get() const {
        return iter.GetAccumulator()->ComputeHash();
    }

    inline bool Match() {
        if (iter.GetAccumulator()->Matches()) {
            matchpos = count;
            hadmatch = true;
            if (match) {
                *match = iter.GetAccumulator()->GetMatch();
            }
            return true;
        }
        return false;
    }

    void Increment() {
        iter.Increment();
        ++count;
    }

    bool HadMatch() const { return hadmatch; }
    uint64_t GetCount() const { return count; }
    uint64_t GetMatchPosition() const { return matchpos; }
};

}

uint64_t GetCombinations(const KeyTreeNode* tree) {
    InnerKeyTree innertree(tree);
    return CountCombinations(&innertree);
}

uint256 GetMerkleRoot(const KeyTreeNode* tree, uint64_t* count) {
    uint256 root;
    InnerKeyTreeIteratorLeafSource source(tree, NULL, NULL);
    MerkleComputation(source, &root, NULL);
    if (count) *count = source.count;
    return root;
}

bool GetMerkleBranch(const KeyTreeNode* tree, KeyTreeFilter* filter, uint256* root, uint64_t* count, uint64_t* matchpos, std::vector<uint256>* branch, std::vector<CPubKey>* pubkeys) {
    InnerKeyTreeIteratorLeafSource source(tree, filter, pubkeys);
    MerkleComputation(source, root, branch);
    if (!source.HadMatch()) return false;
    if (count) *count = source.GetCount();
    if (matchpos) *matchpos = source.GetMatchPosition();
    return true;
}

uint256 GetMerkleRootFromBranch(const uint256& leaf, std::vector<uint256>& branch, uint64_t position) {
    uint256 res = leaf;
    for (std::vector<uint256>::const_iterator it = branch.begin(); it != branch.end(); it++) {
        if (position & 1) {
            CSHA256().Write(it->begin(), 32).Write(res.begin(), 32).Finalize(res.begin());
        } else if (*it != uint256()) {
            CSHA256().Write(res.begin(), 32).Write(it->begin(), 32).Finalize(res.begin());
        } else {
            static const unsigned char one[1] = {1};
            CSHA256().Write(res.begin(), 32).Write(one, 1).Finalize(res.begin());
        }
        position >>= 1;
    }
    if (position) {
        return uint256();
    }
    return res;
}

bool HasMatch(const KeyTreeNode* node, KeyTreeFilter* filter) {
    if (node->threshold == 0) {
        return (*filter)(node->leaf);
    }
    uint32_t matches = 0;
    for (std::vector<KeyTreeNode>::const_iterator it = node->children.begin(); it != node->children.end(); ++it) {
        if (HasMatch(&(*it), filter)) {
            matches++;
            if (matches == node->threshold) {
                return true;
            }
        }
    }
    return false;
}

static void GetAllLeavesRecurse(const KeyTreeNode* tree, std::set<CPubKey>& ret) {
    if (tree->threshold == 0) {
        ret.insert(tree->leaf);
    } else {
        for (std::vector<KeyTreeNode>::const_iterator it = tree->children.begin(); it != tree->children.end(); ++it) {
            GetAllLeavesRecurse(&*it, ret);
        }
    }
}

std::set<CPubKey> GetAllLeaves(const KeyTreeNode* tree) {
    std::set<CPubKey> ret;
    GetAllLeavesRecurse(tree, ret);
    return ret;
}
