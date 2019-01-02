//
// Created by michael on 12/12/18.
//

#include "CTxWitness.h"

#include <hash.h>
#include "consensus/merkle.h"


/**
 * The input witness consists of four elements, three of which are
 * optional. The optional elements have to do with asset issuance
 * and peg-in transactions, nor present most of the time.
 *
 */
uint256 CTxInWitness::GetHash() const
{
    std::vector<uint256> leaves;
    leaves.push_back(SerializeHash(vchIssuanceAmountRangeproof, SER_GETHASH, 0));
    leaves.push_back(SerializeHash(vchInflationKeysRangeproof, SER_GETHASH, 0));
    leaves.push_back(SerializeHash(scriptWitness.stack, SER_GETHASH, 0));
    leaves.push_back(SerializeHash(m_pegin_witness.stack, SER_GETHASH, 0));
    return ComputeFastMerkleRoot(leaves);
}

/**
 * The output witness consists of two elements: the surjection proof and
 * the range proof.
 *
 *     S : asset surjection proof
 *     R : value range proof
 *
 *           .
 *          / \
 *         S   R
 */
uint256 CTxOutWitness::GetHash() const
{
    std::vector<uint256> leaves;
    leaves.push_back(SerializeHash(vchSurjectionproof, SER_GETHASH, 0));
    leaves.push_back(SerializeHash(vchRangeproof, SER_GETHASH, 0));
    return ComputeFastMerkleRoot(leaves);
}
