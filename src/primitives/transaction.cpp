// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "primitives/transaction.h"

#include "hash.h"
#include "tinyformat.h"
#include "utilstrencodings.h"

CTxOutValue::CTxOutValue()
{
    vchCommitment.resize(nCommitmentSize);
    memset(&vchCommitment[0], 0xff, nCommitmentSize);
}

CTxOutValue::CTxOutValue(CAmount nAmountIn)
{
    vchCommitment.resize(nCommitmentSize);
    SetToAmount(nAmountIn);
}

CTxOutValue::CTxOutValue(const std::vector<unsigned char>& vchValueCommitmentIn, const std::vector<unsigned char>& vchRangeproofIn)
: vchCommitment(vchValueCommitmentIn), vchRangeproof(vchRangeproofIn)
{
    assert(vchCommitment.size() == nCommitmentSize);
    assert(vchCommitment[0] == 2 || vchCommitment[0] == 3);
}

bool CTxOutValue::IsValid() const
{
    switch (vchCommitment[0])
    {
        case 0:
        {
            // Ensure all but the last sizeof(CAmount) bytes are zero
            for (size_t i = vchCommitment.size() - sizeof(CAmount); --i > 0; )
                if (vchCommitment[i])
                    return false;
            return true;
        }
        case 2:
        case 3:
            // FIXME: Additional checks?
            return true;
        default:
            return false;
    }
}

bool CTxOutValue::IsNull() const
{
    return vchCommitment[0] == 0xff;
}

bool CTxOutValue::IsAmount() const
{
    return !vchCommitment[0];
}

void CTxOutValue::SetToAmount(CAmount nAmount)
{
    assert(vchCommitment.size() > sizeof(nAmount) + 1);
    memset(&vchCommitment[0], 0, vchCommitment.size() - sizeof(nAmount));
    for (size_t i = 0; i < sizeof(nAmount); ++i)
        vchCommitment[vchCommitment.size() - (i + 1)] = ((nAmount >> (i * 8)) & 0xff);
}

CAmount CTxOutValue::GetAmount() const
{
    assert(IsAmount());
    CAmount nAmount = 0;
    for (size_t i = 0; i < sizeof(nAmount); ++i)
        nAmount |= CAmount(vchCommitment[vchCommitment.size() - (i + 1)]) << (i * 8);
    return nAmount;
}

bool operator==(const CTxOutValue& a, const CTxOutValue& b)
{
    return a.vchRangeproof == b.vchRangeproof &&
           a.vchCommitment == b.vchCommitment &&
           a.vchNonceCommitment == b.vchNonceCommitment;
}

bool operator!=(const CTxOutValue& a, const CTxOutValue& b) {
    return !(a == b);
}

bool operator<(const CAmountMap& a, const CAmountMap& b)
{
    for(std::map<CAssetID, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it) {
        if (a.count(it->first) == 0 || a.find(it->first)->second < it->second)
            return true;
    }
    return false;
}

CAmountMap& operator+=(CAmountMap& a, const CAmountMap& b)
{
    for(std::map<CAssetID, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it)
        a[it->first] += it->second;
    return a;
}

CAmountMap& operator-=(CAmountMap& a, const CAmountMap& b)
{
    for(std::map<CAssetID, CAmount>::const_iterator it = b.begin(); it != b.end(); ++it) {
        if (a.count(it->first) > 0)
            a[it->first] -= it->second;
        else
            throw std::runtime_error(strprintf("%s : asset %s is not contained in this map", __func__, it->first.ToString()));
    }
    return a;
}

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
        str += strprintf(", scriptSig=%s", scriptSig.ToString().substr(0,24));
    if (~nSequence)
        str += strprintf(", nSequence=%u", nSequence);
    str += ")";
    return str;
}

CTxOut::CTxOut(const CTxOutValue& valueIn, CScript scriptPubKeyIn, CAssetID assetIDIn) 
    : nValue(valueIn), assetID(assetIDIn), scriptPubKey(scriptPubKeyIn)
{
}

std::string CTxOut::ToString() const
{
    return strprintf("CTxOut(nValue=%s, assetID=%s, scriptPubKey=%s)", (nValue.IsAmount() ? strprintf("%d.%08d", nValue.GetAmount() / COIN, nValue.GetAmount() % COIN) : std::string("UNKNOWN")), assetID.ToString(), scriptPubKey.ToString().substr(0,30));
}

CMutableTransaction::CMutableTransaction() : nVersion(CTransaction::CURRENT_VERSION), vTxFees(std::vector<CAmount>()), nLockTime(0) {}
CMutableTransaction::CMutableTransaction(const CTransaction& tx) : nVersion(tx.nVersion), vin(tx.vin), vTxFees(tx.vTxFees), vout(tx.vout), nLockTime(tx.nLockTime) {}

uint256 CMutableTransaction::GetHash() const
{
    if (IsCoinBase()) {
        return SerializeHash(*this, SER_GETHASH, PROTOCOL_VERSION);
    } else {
        return SerializeHash(*this, SER_GETHASH, PROTOCOL_VERSION | SERIALIZE_VERSION_MASK_NO_WITNESS);
    }
}

void CTransaction::UpdateHash() const
{
    bool maybeBitcoinTx = true;
    for (unsigned int i = 0; i < vout.size(); i++)
        if (!vout[i].nValue.IsAmount())
            maybeBitcoinTx = false;
    if (maybeBitcoinTx)
        *const_cast<uint256*>(&hashBitcoin) = SerializeHash(*this, SER_GETHASH, PROTOCOL_VERSION | SERIALIZE_VERSION_MASK_BITCOIN_TX);

    if (IsCoinBase()) {
        *const_cast<uint256*>(&hash) = SerializeHash(*this, SER_GETHASH, PROTOCOL_VERSION);
    } else {
        *const_cast<uint256*>(&hash) = SerializeHash(*this, SER_GETHASH, PROTOCOL_VERSION | SERIALIZE_VERSION_MASK_NO_WITNESS);
    }
    *const_cast<uint256*>(&hashWitness) = SerializeHash(*this, SER_GETHASH, PROTOCOL_VERSION | SERIALIZE_VERSION_MASK_ONLY_WITNESS);
    // Update full hash combining the normalized txid with the hash of the witness
    CHash256 hasher;
    hasher.Write((unsigned char*)&hash, hash.size());
    hasher.Write((unsigned char*)&hashWitness, hashWitness.size());
    hasher.Finalize((unsigned char*)&hashFull);
}

CTransaction::CTransaction() : hash(0), hashFull(0), nVersion(CTransaction::CURRENT_VERSION), vin(), vTxFees(std::vector<CAmount>()), vout(), nLockTime(0) { }

CTransaction::CTransaction(const CMutableTransaction &tx) : nVersion(tx.nVersion), vin(tx.vin), vTxFees(tx.vTxFees), vout(tx.vout), nLockTime(tx.nLockTime) {
    UpdateHash();
}

CTransaction& CTransaction::operator=(const CTransaction &tx) {
    *const_cast<int*>(&nVersion) = tx.nVersion;
    *const_cast<std::vector<CAmount>*>(&vTxFees) = tx.vTxFees;
    *const_cast<std::vector<CTxIn>*>(&vin) = tx.vin;
    *const_cast<std::vector<CTxOut>*>(&vout) = tx.vout;
    *const_cast<unsigned int*>(&nLockTime) = tx.nLockTime;
    *const_cast<uint256*>(&hash) = tx.hash;
    *const_cast<uint256*>(&hashFull) = tx.hashFull;
    return *this;
}

double CTransaction::ComputePriority(double dPriorityInputs, unsigned int nTxSize) const
{
    nTxSize = CalculateModifiedSize(nTxSize);
    if (nTxSize == 0) return 0.0;

    return dPriorityInputs / nTxSize;
}

CAmountMap CTransaction::GetTxRewardMap() const
{
    assert(vTxFees.size() <= vout.size());
    CAmountMap mTxReward;
    for (unsigned i = 0; i < vTxFees.size(); ++i)
        mTxReward[vout[i].assetID] += vTxFees[i];
    return mTxReward;
}

bool CTransaction::GetFee(const CAssetID& assetID) const
{
    const CAmountMap mTxReward = GetTxRewardMap();
    return mTxReward.find(assetID)->second;
}

unsigned int CTransaction::CalculateModifiedSize(unsigned int nTxSize) const
{
    // In order to avoid disincentivizing cleaning up the UTXO set we don't count
    // the constant overhead for each txin and up to 110 bytes of scriptSig (which
    // is enough to cover a compressed pubkey p2sh redemption) for priority.
    // Providing any more cleanup incentive than making additional inputs free would
    // risk encouraging people to create junk outputs to redeem later.
    if (nTxSize == 0)
        nTxSize = ::GetSerializeSize(*this, SER_NETWORK, PROTOCOL_VERSION);
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
    std::string str;
    str += strprintf("CTransaction(hash=%s, ver=%d, vin.size=%u, vout.size=%u, nLockTime=%u, vTxFees.size=%u)\n",
        GetHash().ToString().substr(0,10),
        nVersion,
        vin.size(),
        vout.size(),
        nLockTime, vTxFees.size());
    for (unsigned int i = 0; i < vin.size(); i++)
        str += "    " + vin[i].ToString() + "\n";
    for (unsigned int i = 0; i < vout.size(); i++)
        str += "    " + vout[i].ToString() + "\n";
    return str;
}
