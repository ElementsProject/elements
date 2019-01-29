// Copyright (c) 2016-2019 The Elements developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PRIMITIVES_TXWITNESS_H
#define BITCOIN_PRIMITIVES_TXWITNESS_H

#include <uint256.h>


/*
 * Compute the Merkle root of the transactions in a block using mid-state only.
 * Note that the merkle root calculated with this method is not the same as the
 * one computed by ComputeMerkleRoot.
 */
uint256 ComputeFastMerkleRoot(const std::vector<uint256>& hashes);


#endif //BITCOIN_PRIMITIVES_TXWITNESS_H
