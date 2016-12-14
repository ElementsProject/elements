// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "primitives/transaction.h"

#include "hash.h"
#include "tinyformat.h"
#include "utilstrencodings.h"

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
    str += ")";
    return str;
}

void CTxOutAsset::SetNull()
{
    vchAssetTag.resize(1);
    vchAssetTag[0] = 0xff;
    vchSurjectionproof.clear();
}

bool CTxOutAsset::GetAssetID(uint256& assetID) const
{
    if (!IsAssetID() && !IsAssetGeneration())
        return false;
    std::copy(std::next(vchAssetTag.begin()), vchAssetTag.end(), assetID.begin());
    return true;
}

void CTxOutAsset::SetToAssetID(const uint256& assetID)
{
    vchAssetTag.reserve(nAssetTagSize);
    vchAssetTag.push_back(1);
    vchAssetTag.insert(vchAssetTag.end(), assetID.begin(), assetID.end());
    vchSurjectionproof.clear();
}

CTxOutValue::CTxOutValue(CAmount nAmountIn)
{
    vchCommitment.resize(nExplicitSize);
    SetToAmount(nAmountIn);
}

void CTxOutValue::SetNull()
{
    vchCommitment.resize(1);
    vchCommitment[0] = 0xff;
}

bool CTxOutValue::IsValid() const
{
    switch(vchCommitment[0]) {
        case 0:
        case 1:
            if (vchCommitment.size() != nExplicitSize)
                return false;
            return true;
        // Alpha used 2 and 3 for value commitments
        case 2:
        case 3:
            return false;
        case 8:
        case 9:
            if (vchCommitment.size() != nCommittedSize)
                return false;
            return true;
        default:
            return false;
    }
}

CAmount CTxOutValue::GetAmount() const
{
    assert(IsAmount());
    return ReadBE64(&vchCommitment[1]);
}

void CTxOutValue::SetToBitcoinAmount(const CAmount nAmount) {
    SetToAmount(nAmount);
    vchCommitment[0] = 0;
}

void CTxOutValue::SetToAmount(const CAmount nAmount) {
    vchCommitment.resize(nExplicitSize);
    vchCommitment[0] = 1;
    WriteBE64(&vchCommitment[1], nAmount);
}

CTxOut::CTxOut(const CTxOutAsset& nAssetIn, const CTxOutValue& nValueIn, CScript scriptPubKeyIn)
{
    nAsset = nAssetIn;
    nValue = nValueIn;
    scriptPubKey = scriptPubKeyIn;
}

std::string CTxOut::ToString() const
{
    uint256 assetID;
    std::string strAsset;
    if ((nAsset.IsAssetID() || nAsset.IsAssetGeneration()) && nAsset.GetAssetID(assetID))
        strAsset = strprintf("nAsset=%s, ", assetID.ToString());
    if (nAsset.IsAssetCommitment())
        strAsset = std::string("nAsset=UNKNOWN, ");
    return strprintf("CTxOut(%snValue=%s, scriptPubKey=%s)", strAsset, (nValue.IsAmount() ? strprintf("%d.%08d", nValue.GetAmount() / COIN, nValue.GetAmount() % COIN) : std::string("UNKNOWN")), HexStr(scriptPubKey).substr(0, 30));
}

CMutableTransaction::CMutableTransaction() : nVersion(CTransaction::CURRENT_VERSION), nLockTime(0) {}
CMutableTransaction::CMutableTransaction(const CTransaction& tx) : nVersion(tx.nVersion), vin(tx.vin), vout(tx.vout), wit(tx.wit), nLockTime(tx.nLockTime) {}

uint256 CMutableTransaction::GetHash() const
{
    return SerializeHash(*this, SER_GETHASH, SERIALIZE_TRANSACTION_NO_WITNESS);
}

void CTransaction::UpdateHash() const
{
    *const_cast<uint256*>(&hash) = SerializeHash(*this, SER_GETHASH, SERIALIZE_TRANSACTION_NO_WITNESS);
}

uint256 CTransaction::GetWitnessHash() const
{
    return SerializeHash(*this, SER_GETHASH, 0);
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
            uint256 assetid;
            vout[i].nAsset.GetAssetID(assetid);
            totalFee[assetid] += fee;
        }
    }
    return MoneyRange(totalFee);
}

CAmountMap CTransaction::GetFee() const
{
    CAmountMap fee;
    for (unsigned int i = 0; i < vout.size(); i++)
        if (vout[i].IsFee()) {
            uint256 assetid;
            vout[i].nAsset.GetAssetID(assetid);
            fee[assetid] += vout[i].nValue.GetAmount();
        }
    return fee;
}

CTransaction::CTransaction() : nVersion(CTransaction::CURRENT_VERSION), vin(), vout(), nLockTime(0) { }

CTransaction::CTransaction(const CMutableTransaction &tx) : nVersion(tx.nVersion), vin(tx.vin), vout(tx.vout), wit(tx.wit), nLockTime(tx.nLockTime) {
    UpdateHash();
}

CTransaction& CTransaction::operator=(const CTransaction &tx) {
    *const_cast<int*>(&nVersion) = tx.nVersion;
    *const_cast<std::vector<CTxIn>*>(&vin) = tx.vin;
    *const_cast<std::vector<CTxOut>*>(&vout) = tx.vout;
    *const_cast<CTxWitness*>(&wit) = tx.wit;
    *const_cast<unsigned int*>(&nLockTime) = tx.nLockTime;
    *const_cast<uint256*>(&hash) = tx.hash;
    return *this;
}

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
