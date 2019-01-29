// Copyright (c) 2016-2019 The Elements developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <primitives/txwitness.h>

#include <hash.h>

static inline
void MerkleHash_Sha256Midstate(uint256& parent, const uint256& left, const uint256& right) {
    CSHA256().Write(left.begin(), 32).Write(right.begin(), 32).Midstate(parent.begin(), NULL, NULL);
}

uint256 ComputeFastMerkleRoot(const std::vector<uint256>& hashes) {
    uint256 result_hash = uint256();
    if (hashes.size() == 0) return result_hash;

    // inner is an array of eagerly computed subtree hashes, indexed by tree
    // level (0 being the leaves).
    // For example, when count is 25 (11001 in binary), inner[4] is the hash of
    // the first 16 leaves, inner[3] of the next 8 leaves, and inner[0] equal to
    // the last leaf. The other inner entries are undefined.
    //
    // First process all leaves into 'inner' values.
    uint256 inner[32];
    uint32_t count = 0;
    while (count < hashes.size()) {
        uint256 temp_hash = hashes[count];
        count++;
        // For each of the lower bits in count that are 0, do 1 step. Each
        // corresponds to an inner value that existed before processing the
        // current leaf, and each needs a hash to combine it.
        int level;
        for (level = 0; !(count & (((uint32_t)1) << level)); level++) {
            MerkleHash_Sha256Midstate(temp_hash, inner[level], temp_hash);
        }
        // Store the resulting hash at inner position level.
        inner[level] = temp_hash;
    }

    // Do a final 'sweep' over the rightmost branch of the tree to process
    // odd levels, and reduce everything to a single top value.
    // Level is the level (counted from the bottom) up to which we've sweeped.
    //
    // As long as bit number level in count is zero, skip it. It means there
    // is nothing left at this level.
    int level = 0;
    while (!(count & (((uint32_t)1) << level))) {
        level++;
    }
    result_hash = inner[level];

    while (count != (((uint32_t)1) << level)) {
        // If we reach this point, hash is an inner value that is not the top.
        // We combine it with itself (Bitcoin's special rule for odd levels in
        // the tree) to produce a higher level one.

        // Increment count to the value it would have if two entries at this
        // level had existed and propagate the result upwards accordingly.
        count += (((uint32_t)1) << level);
        level++;
        while (!(count & (((uint32_t)1) << level))) {
            MerkleHash_Sha256Midstate(result_hash, inner[level], result_hash);
            level++;
        }
    }
    // Return result.
    return result_hash;
}
