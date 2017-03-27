#include "issuance.h"

#include "primitives/transaction.h"
#include "amount.h"

void GenerateAssetEntropy(uint256& entropy, const COutPoint& prevout, const uint256& contracthash)
{
    // E : entropy
    // I : prevout
    // C : contract
    // E = H( H(I) || H(C) )
    std::vector<uint256> leaves;
    leaves.reserve(2);
    leaves.push_back(SerializeHash(prevout, SER_GETHASH, 0));
    leaves.push_back(contracthash);
    entropy = ComputeFastMerkleRoot(leaves);
}

void CalculateAsset(CAsset& asset, const uint256& entropy)
{
    static const uint256 kZero = uint256S("0x0000000000000000000000000000000000000000000000000000000000000000");
    // H_a : asset tag
    // E   : entropy
    // H_a = H( E || 0 )
    std::vector<uint256> leaves;
    leaves.reserve(2);
    leaves.push_back(entropy);
    leaves.push_back(kZero);
    asset = CAsset(ComputeFastMerkleRoot(leaves));
}

void CalculateReissuanceToken(CAsset& reissuanceToken, const uint256& entropy, bool fConfidential)
{
    static const uint256 kOne = uint256S("0x0000000000000000000000000000000000000000000000000000000000000001");
    static const uint256 kTwo = uint256S("0x0000000000000000000000000000000000000000000000000000000000000002");
    // H_a : asset reissuance tag
    // E   : entropy
    // if not fConfidential:
    //     H_a = H( E || 1 )
    // else
    //     H_a = H( E || 2 )
    std::vector<uint256> leaves;
    leaves.reserve(2);
    leaves.push_back(entropy);
    leaves.push_back(fConfidential? kTwo: kOne);
    reissuanceToken = CAsset(ComputeFastMerkleRoot(leaves));
}


