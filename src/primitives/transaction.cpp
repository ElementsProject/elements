// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "consensus/merkle.h"
#include "primitives/transaction.h"

#include "hash.h"
#include "tinyformat.h"
#include "utilstrencodings.h"

const uint256 CAssetIssuance::UNBLINDED_REISSUANCE_NONCE(uint256S("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"));

void CConfidentialAsset::SetToAsset(const CAsset& asset)
{
    vchCommitment.clear();
    vchCommitment.reserve(nExplicitSize);
    vchCommitment.push_back(1);
    vchCommitment.insert(vchCommitment.end(), asset.begin(), asset.end());
}

void CConfidentialValue::SetToAmount(const CAmount amount)
{
    vchCommitment.resize(nExplicitSize);
    vchCommitment[0] = 1;
    WriteBE64(&vchCommitment[1], amount);
}

CTxOut::CTxOut(const CConfidentialAsset& nAssetIn, const CConfidentialValue& nValueIn, CScript scriptPubKeyIn)
{
    nAsset = nAssetIn;
    nValue = nValueIn;
    scriptPubKey = scriptPubKeyIn;
}

std::string CTxOut::ToString() const
{
    std::string strAsset;
    if (nAsset.IsExplicit())
        strAsset = strprintf("nAsset=%s, ", nAsset.GetAsset().GetHex());
    if (nAsset.IsCommitment())
        strAsset = std::string("nAsset=CONFIDENTIAL, ");
    return strprintf("CTxOut(%snValue=%s, scriptPubKey=%s)", strAsset, (nValue.IsExplicit() ? strprintf("%d.%08d", nValue.GetAmount() / COIN, nValue.GetAmount() % COIN) : std::string("CONFIDENTIAL")), HexStr(scriptPubKey).substr(0, 30));
}

std::string COutPoint::ToString() const
{
    return strprintf("COutPoint(%s, %u)", hash.ToString().substr(0,10), n);
}

std::string CAssetIssuance::ToString() const
{
    std::string str;
    str += "CAssetIssuance(";
    str += assetBlindingNonce.ToString();
    str += ", ";
    str += assetEntropy.ToString();
    if (!nAmount.IsNull())
        str += strprintf(", amount=%s", (nAmount.IsExplicit() ? strprintf("%d.%08d", nAmount.GetAmount() / COIN, nAmount.GetAmount() % COIN) : std::string("CONFIDENTIAL")));
    if (!nInflationKeys.IsNull())
        str += strprintf(", inflationkeys=%s", (nInflationKeys.IsExplicit() ? strprintf("%d.%08d", nInflationKeys.GetAmount() / COIN, nInflationKeys.GetAmount() % COIN) : std::string("CONFIDENTIAL")));
    str += ")";
    return str;
}

bool CAssetIssuance::IsReissuance() const
{
    return !assetBlindingNonce.IsNull();
}

bool CAssetIssuance::IsUnblindedReissuance() const
{
    return IsReissuance() && assetBlindingNonce == UNBLINDED_REISSUANCE_NONCE;
}

CTxIn::CTxIn(COutPoint prevoutIn, CScript scriptSigIn, uint32_t nSequenceIn)
{
    prevout = prevoutIn;
    scriptSig = scriptSigIn;
    nSequence = nSequenceIn;
}

CTxIn::CTxIn(uint256 hashPrevTx, uint32_t nOut, CScript scriptSigIn, uint32_t nSequenceIn)
{
    prevout = COutPoint(hashPrevTx, nOut);
    scriptSig = scriptSigIn;
    nSequence = nSequenceIn;
}

std::string CTxIn::ToString() const
{
    std::string str;
    str += "CTxIn(";
    str += prevout.ToString();
    if (prevout.IsNull())
        str += strprintf(", coinbase %s", HexStr(scriptSig));
    else
        str += strprintf(", scriptSig=%s", HexStr(scriptSig).substr(0, 24));
    if (nSequence != SEQUENCE_FINAL)
        str += strprintf(", nSequence=%u", nSequence);
    if (!assetIssuance.IsNull())
        str += strprintf(", %s", assetIssuance.ToString());
    str += ")";
    return str;
}

CMutableTransaction::CMutableTransaction() : nVersion(CTransaction::CURRENT_VERSION), vin(), vout(), wit(), nLockTime(0) {}
CMutableTransaction::CMutableTransaction(const CTransaction& tx) : nVersion(tx.nVersion), vin(tx.vin), vout(tx.vout), wit(tx.wit), nLockTime(tx.nLockTime) {}

/**
 * The input witness consists of four ocean, three of which are
 * optional. The optional ocean have to do with asset issuance
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
 * The output witness consists of two ocean: the surjection proof and
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


uint256 CMutableTransaction::GetHash() const
{
    return SerializeHash(*this, SER_GETHASH, SERIALIZE_TRANSACTION_NO_WITNESS);
}

uint256 CTransaction::ComputeHash() const
{
    return SerializeHash(*this, SER_GETHASH, SERIALIZE_TRANSACTION_NO_WITNESS);
}

uint256 CTransaction::GetHashWithWitness() const
{
    if (!HasWitness()) {
        return GetHash();
    }
    return SerializeHash(*this, SER_GETHASH, 0);
}

uint256 CTransaction::ComputeWitnessHash() const
{
    std::vector<uint256> leaves;
    leaves.reserve(std::max(vin.size(), vout.size()));
    /* Inputs */
    for (size_t i = 0; i < vin.size(); ++i)
        leaves.push_back(((wit.vtxinwit.size() <= i || vin[i].prevout.IsNull())? CTxInWitness(): wit.vtxinwit[i]).GetHash());
    uint256 hashIn = ComputeFastMerkleRoot(leaves);
    leaves.clear();
    /* Outputs */
    for (size_t i = 0; i < vout.size(); ++i)
        leaves.push_back((wit.vtxoutwit.size() <= i? CTxOutWitness(): wit.vtxoutwit[i]).GetHash());
    uint256 hashOut = ComputeFastMerkleRoot(leaves);
    leaves.clear();
    /* Combined */
    leaves.push_back(hashIn);
    leaves.push_back(hashOut);
    return ComputeFastMerkleRoot(leaves);
}

bool CTransaction::HasValidFee() const
{
    CAmountMap totalFee;
    for (unsigned int i = 0; i < vout.size(); i++) {
        CAmount fee = 0;
        if (vout[i].IsFee()) {
            fee = vout[i].nValue.GetAmount();
            if (fee == 0 || !MoneyRange(fee))
                return false;
            totalFee[vout[i].nAsset.GetAsset()] += fee;
        }
    }
    return MoneyRange(totalFee);
}

CAmountMap CTransaction::GetFee() const
{
    CAmountMap fee;
    unsigned int numFees = 0;
    for (unsigned int i = 0; i < vout.size(); i++) {
        if (vout[i].IsFee()) {
            fee[vout[i].nAsset.GetAsset()] += vout[i].nValue.GetAmount();
            numFees++;
        }
    }
    if(numFees == 0) fee[vout[0].nAsset.GetAsset()] = 0;
    return fee;
}

/* For backward compatibility, the hash is initialized to 0. TODO: remove the need for this default constructor entirely. */
CTransaction::CTransaction() : nVersion(CTransaction::CURRENT_VERSION), vin(), vout(), wit(), nLockTime(0), hash() {}
CTransaction::CTransaction(const CMutableTransaction &tx) : nVersion(tx.nVersion), vin(tx.vin), vout(tx.vout), wit(tx.wit), nLockTime(tx.nLockTime), hash(ComputeHash()) {}
CTransaction::CTransaction(CMutableTransaction &&tx) : nVersion(tx.nVersion), vin(std::move(tx.vin)), vout(std::move(tx.vout)), wit(tx.wit), nLockTime(tx.nLockTime), hash(ComputeHash()) {}

double CTransaction::ComputePriority(double dPriorityInputs, unsigned int nTxSize) const
{
    nTxSize = CalculateModifiedSize(nTxSize);
    if (nTxSize == 0) return 0.0;

    return dPriorityInputs / nTxSize;
}

unsigned int CTransaction::CalculateModifiedSize(unsigned int nTxSize) const
{
    // In order to avoid disincentivizing cleaning up the UTXO set we don't count
    // the constant overhead for each txin and up to 110 bytes of scriptSig (which
    // is enough to cover a compressed pubkey p2sh redemption) for priority.
    // Providing any more cleanup incentive than making additional inputs free would
    // risk encouraging people to create junk outputs to redeem later.
    if (nTxSize == 0)
        nTxSize = (GetTransactionWeight(*this) + WITNESS_SCALE_FACTOR - 1) / WITNESS_SCALE_FACTOR;
    for (std::vector<CTxIn>::const_iterator it(vin.begin()); it != vin.end(); ++it)
    {
        unsigned int offset = 41U + std::min(110U, (unsigned int)it->scriptSig.size());
        if (nTxSize > offset)
            nTxSize -= offset;
    }
    return nTxSize;
}

unsigned int CTransaction::GetTotalSize() const
{
    return ::GetSerializeSize(*this, SER_NETWORK, PROTOCOL_VERSION);
}

std::string CTransaction::ToString() const
{
    CAmount fee = 0;
    for (unsigned int i = 0; i < vout.size(); i++)
        if (vout[i].IsFee())
            fee += vout[i].nValue.GetAmount();

    std::string str;
    str += strprintf("CTransaction(hash=%s, ver=%d, fee=%d.%08d, vin.size=%u, vout.size=%u, nLockTime=%u)\n",
        GetHash().ToString().substr(0,10),
        nVersion,
        fee / COIN, fee % COIN,
        vin.size(),
        vout.size(),
        nLockTime);
    for (unsigned int i = 0; i < vin.size(); i++)
        str += "    " + vin[i].ToString() + "\n";
    for (unsigned int i = 0; i < wit.vtxinwit.size(); i++)
        str += "    " + wit.vtxinwit[i].scriptWitness.ToString() + "\n";
    for (unsigned int i = 0; i < vout.size(); i++)
        str += "    " + vout[i].ToString() + "\n";
    return str;
}

int64_t GetTransactionWeight(const CTransaction& tx)
{
    return ::GetSerializeSize(tx, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS) * (WITNESS_SCALE_FACTOR -1) + ::GetSerializeSize(tx, SER_NETWORK, PROTOCOL_VERSION);
}
