// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <primitives/transaction.h>

#include <hash.h>
#include <tinyformat.h>
#include <util/strencodings.h>

#include <assert.h>

bool g_con_elementsmode = false;

const int32_t CTransaction::CURRENT_VERSION = 2;

std::string COutPoint::ToString() const
{
    return strprintf("COutPoint(%s, %u)", hash.ToString().substr(0,10), n);
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

CMutableTransaction::CMutableTransaction() : nVersion(CTransaction::CURRENT_VERSION), nLockTime(0) {}
CMutableTransaction::CMutableTransaction(const CTransaction& tx) :
        vin(tx.vin), vout(tx.vout), nVersion(tx.nVersion), nLockTime(tx.nLockTime), witness(tx.witness) {}

uint256 CMutableTransaction::GetHash() const
{
    return SerializeHash(*this, SER_GETHASH, SERIALIZE_TRANSACTION_NO_WITNESS);
}

uint256 CTransaction::ComputeHash() const
{
    return SerializeHash(*this, SER_GETHASH, SERIALIZE_TRANSACTION_NO_WITNESS);
}

uint256 CTransaction::ComputeWitnessHash() const
{
    if (!HasWitness()) {
        return hash;
    }
    return SerializeHash(*this, SER_GETHASH, 0);
}

// ELEMENTS ONLY
uint256 CTransaction::GetWitnessOnlyHash() const
{
    assert(g_con_elementsmode);

    std::vector<uint256> leaves;
    leaves.reserve(std::max(vin.size(), vout.size()));
    /* Inputs */
    for (size_t i = 0; i < vin.size(); ++i) {
        // Input has no witness OR is null input(coinbase)
        const CTxInWitness& txinwit = (witness.vtxinwit.size() <= i || vin[i].prevout.IsNull()) ? CTxInWitness() : witness.vtxinwit[i];
        leaves.push_back(txinwit.GetHash());
    }
    uint256 hashIn = ComputeFastMerkleRoot(leaves);
    leaves.clear();
    /* Outputs */
    for (size_t i = 0; i < vout.size(); ++i) {
        const CTxOutWitness& txoutwit = witness.vtxoutwit.size() <= i ? CTxOutWitness() : witness.vtxoutwit[i];
        leaves.push_back(txoutwit.GetHash());
    }
    uint256 hashOut = ComputeFastMerkleRoot(leaves);
    leaves.clear();
    /* Combined */
    leaves.push_back(hashIn);
    leaves.push_back(hashOut);
    return ComputeFastMerkleRoot(leaves);
}

CTransaction::CTransaction(const CMutableTransaction& tx) :
        vin(tx.vin), vout(tx.vout), nVersion(tx.nVersion), nLockTime(tx.nLockTime), witness(tx.witness), hash{ComputeHash()}, m_witness_hash{ComputeWitnessHash()} {}
CTransaction::CTransaction(CMutableTransaction&& tx) :
        vin(std::move(tx.vin)), vout(std::move(tx.vout)), nVersion(tx.nVersion), nLockTime(tx.nLockTime), witness(std::move(tx.witness)),hash{ComputeHash()}, m_witness_hash{ComputeWitnessHash()} {}

CAmountMap CTransaction::GetValueOutMap() const {

    CAmountMap values;
    for (const auto& tx_out : vout) {
        if (tx_out.nValue.IsExplicit() && tx_out.nAsset.IsExplicit()) {
            CAmountMap m;
            m[tx_out.nAsset.GetAsset()] = tx_out.nValue.GetAmount();
            if (!MoneyRange(tx_out.nValue.GetAmount()) || !MoneyRange(values[tx_out.nAsset.GetAsset()] + tx_out.nValue.GetAmount()))
                throw std::runtime_error(std::string(__func__) + ": value out of range");
            values += m;
        }
    }
    assert(MoneyRange(values));
    return values;
}

unsigned int CTransaction::GetTotalSize() const
{
    return ::GetSerializeSize(*this, PROTOCOL_VERSION);
}

std::string CTransaction::ToString() const
{
    std::string str;
    str += strprintf("CTransaction(hash=%s, ver=%d, vin.size=%u, vout.size=%u, nLockTime=%u)\n",
        GetHash().ToString().substr(0,10),
        nVersion,
        vin.size(),
        vout.size(),
        nLockTime);
    for (const auto& tx_in : vin)
        str += "    " + tx_in.ToString() + "\n";
    for (const auto& tx_in : witness.vtxinwit)
        str += "    " + tx_in.scriptWitness.ToString() + "\n";
    for (const auto& tx_out : vout)
        str += "    " + tx_out.ToString() + "\n";
    return str;
}
