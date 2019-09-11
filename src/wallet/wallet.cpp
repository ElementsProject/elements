// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "wallet/wallet.h"

#include "checkpoints.h"
#include "chain.h"
#include "wallet/coincontrol.h"
#include "consensus/consensus.h"
#include "consensus/validation.h"
#include "crypto/hmac_sha256.h"
#include "key.h"
#include "keystore.h"
#include "validation.h"
#include "issuance.h"
#include "net.h"
#include "policy/policy.h"
#include "primitives/block.h"
#include "primitives/transaction.h"
#include "script/script.h"
#include "script/sign.h"
#include "timedata.h"
#include "txmempool.h"
#include "util.h"
#include "ui_interface.h"
#include "utilmoneystr.h"
#include "script/ismine.h"

#include <assert.h>

#include <boost/algorithm/string/replace.hpp>
#include <boost/filesystem.hpp>
#include <boost/thread.hpp>

#include <secp256k1.h>

using namespace std;

CWallet* pwalletMain = NULL;

/** Transaction fee set by the user */
CFeeRate payTxFee(DEFAULT_TRANSACTION_FEE);
unsigned int nTxConfirmTarget = DEFAULT_TX_CONFIRM_TARGET;
bool bSpendZeroConfChange = DEFAULT_SPEND_ZEROCONF_CHANGE;
bool fSendFreeTransactions = DEFAULT_SEND_FREE_TRANSACTIONS;

const char * DEFAULT_WALLET_DAT = "wallet.dat";
const uint32_t BIP32_HARDENED_KEY_LIMIT = 0x80000000;

/**
 * Fees smaller than this (in satoshi) are considered zero fee (for transaction creation)
 * Override with -mintxfee
 */
CFeeRate CWallet::minTxFee = CFeeRate(DEFAULT_TRANSACTION_MINFEE);
/**
 * If fee estimation does not have enough data to provide estimates, use this fee instead.
 * Has no effect if not using fee estimation
 * Override with -fallbackfee
 */
CFeeRate CWallet::fallbackFee = CFeeRate(DEFAULT_FALLBACK_FEE);

const uint256 CMerkleTx::ABANDON_HASH(uint256S("0000000000000000000000000000000000000000000000000000000000000001"));

/** @defgroup mapWallet
 *
 * @{
 */

struct CompareValueOnly
{
    bool operator()(const pair<CAmount, pair<const CWalletTx*, unsigned int> >& t1,
                    const pair<CAmount, pair<const CWalletTx*, unsigned int> >& t2) const
    {
        return t1.first < t2.first;
    }
};

std::string COutput::ToString() const
{
    return strprintf("COutput(%s, %d, %d) [%s]", tx->GetHash().ToString(), i, nDepth, FormatMoney(tx->GetOutputValueOut(i)));
}

const CWalletTx* CWallet::GetWalletTx(const uint256& hash) const
{
    LOCK(cs_wallet);
    std::map<uint256, CWalletTx>::const_iterator it = mapWallet.find(hash);
    if (it == mapWallet.end())
        return NULL;
    return &(it->second);
}

CPubKey CWallet::GenerateNewKey(bool bEncryption)
{
    AssertLockHeld(cs_wallet); // mapKeyMetadata
    bool fCompressed = CanSupportFeature(FEATURE_COMPRPUBKEY); // default to compressed public keys if we want 0.6.0 wallets

    CKey secret;

    // Create new metadata
    int64_t nCreationTime = GetTime();
    CKeyMetadata metadata(nCreationTime);

    // use HD key derivation if HD was enabled during wallet creation
    if (IsHDEnabled()) {
        if(bEncryption){
            DeriveNewEncryptionChildKey(metadata, secret);
        } else {
            DeriveNewChildKey(metadata, secret);
        }
    } else {
        secret.MakeNewKey(fCompressed);
    }

    // Compressed public keys were introduced in version 0.6.0
    if (fCompressed)
        SetMinVersion(FEATURE_COMPRPUBKEY);

    CPubKey pubKeyPreTweak = secret.GetPubKey();
    metadata.derivedPubKey = pubKeyPreTweak;

    if (Params().EmbedContract() &! bEncryption) {
        // use the active block contract hash to generate keys - if this is not available use the local contract
        uint256 contract = chainActive.Tip() ? chainActive.Tip()->hashContract : GetContractHash(); // for BIP-175
        if (!contract.IsNull() && !Params().ContractInTx())
        {
            pubKeyPreTweak.AddTweakToPubKey((unsigned char*)contract.begin()); //tweak pubkey for reverse testing
            secret.AddTweakToPrivKey((unsigned char*)contract.begin()); //do actual tweaking of private key
        }
    }

    CPubKey pubkey = secret.GetPubKey();
    assert(secret.VerifyPubKey(pubkey));

    if (Params().EmbedContract() &! bEncryption)
        assert(pubKeyPreTweak == pubkey);

    mapKeyMetadata[pubkey.GetID()] = metadata;
    UpdateTimeFirstKey(nCreationTime);

    if (!AddKeyPubKey(secret, pubkey))
        throw std::runtime_error(std::string(__func__) + ": AddKey failed");
    return pubkey;
}


void CWallet::DeriveNewChildKey(CKeyMetadata& metadata, CKey& secret, unsigned int nExternalChain)
{
    // for now we use a fixed keypath scheme of m/0'/0'/k
    CKey key;                      //master key seed (256bit)
    CExtKey masterKey;             //hd master key
    CExtKey accountKey;            //key at m/0'
    CExtKey externalChainChildKey; //key at m/0'/0'
    CExtKey childKey;              //key at m/0'/0'/<n>'

    // try to get the master key
    if (!GetKey(hdChain.masterKeyID, key))
        throw std::runtime_error(std::string(__func__) + ": Master key not found");

    masterKey.SetMaster(key.begin(), key.size());

    // derive m/0'
    // use hardened derivation (child keys >= 0x80000000 are hardened after bip32)
    masterKey.Derive(accountKey, BIP32_HARDENED_KEY_LIMIT);

    // derive m/0'/0'
    accountKey.Derive(externalChainChildKey, BIP32_HARDENED_KEY_LIMIT + nExternalChain);

    // derive child key at next index, skip keys already known to the wallet
    do {
        // always derive hardened keys
        // childIndex | BIP32_HARDENED_KEY_LIMIT = derive childIndex in hardened child-index-range
        // example: 1 | BIP32_HARDENED_KEY_LIMIT == 0x80000001 == 2147483649
        externalChainChildKey.Derive(childKey, hdChain.nExternalChainCounter | BIP32_HARDENED_KEY_LIMIT);
        metadata.hdKeypath = "m/0'/0'/" + std::to_string(hdChain.nExternalChainCounter) + "'";
        metadata.hdMasterKeyID = hdChain.masterKeyID;
        // increment childkey index
        hdChain.nExternalChainCounter++;
    } while (HaveKey(childKey.key.GetPubKey().GetID()));
    secret = childKey.key;

    // update the chain model in the database
    if (!CWalletDB(strWalletFile).WriteHDChain(hdChain))
        throw std::runtime_error(std::string(__func__) + ": Writing HD chain model failed");
}

bool CWallet::AddKeyPubKey(const CKey& secret, const CPubKey &pubkey)
{
    AssertLockHeld(cs_wallet); // mapKeyMetadata
    if (!CCryptoKeyStore::AddKeyPubKey(secret, pubkey))
        return false;

    // check if we need to remove from watch-only
    CScript script;
    script = GetScriptForDestination(pubkey.GetID());
    if (HaveWatchOnly(script))
        RemoveWatchOnly(script);
    script = GetScriptForRawPubKey(pubkey);
    if (HaveWatchOnly(script))
        RemoveWatchOnly(script);

    if (!fFileBacked)
        return true;
    if (!IsCrypted()) {
        return CWalletDB(strWalletFile).WriteKey(pubkey,
                                                 secret.GetPrivKey(),
                                                 mapKeyMetadata[pubkey.GetID()]);
    }
    return true;
}

bool CWallet::AddCryptedKey(const CPubKey &vchPubKey,
                            const vector<unsigned char> &vchCryptedSecret)
{
    if (!CCryptoKeyStore::AddCryptedKey(vchPubKey, vchCryptedSecret))
        return false;
    if (!fFileBacked)
        return true;
    {
        LOCK(cs_wallet);
        if (pwalletdbEncryption)
            return pwalletdbEncryption->WriteCryptedKey(vchPubKey,
                                                        vchCryptedSecret,
                                                        mapKeyMetadata[vchPubKey.GetID()]);
        else
            return CWalletDB(strWalletFile).WriteCryptedKey(vchPubKey,
                                                            vchCryptedSecret,
                                                            mapKeyMetadata[vchPubKey.GetID()]);
    }
    return false;
}

bool CWallet::LoadKeyMetadata(const CTxDestination& keyID, const CKeyMetadata &meta)
{
    AssertLockHeld(cs_wallet); // mapKeyMetadata
    UpdateTimeFirstKey(meta.nCreateTime);
    mapKeyMetadata[keyID] = meta;
    return true;
}

bool CWallet::LoadCryptedKey(const CPubKey &vchPubKey, const std::vector<unsigned char> &vchCryptedSecret)
{
    return CCryptoKeyStore::AddCryptedKey(vchPubKey, vchCryptedSecret);
}

void CWallet::UpdateTimeFirstKey(int64_t nCreateTime)
{
    AssertLockHeld(cs_wallet);
    if (nCreateTime <= 1) {
        // Cannot determine birthday information, so set the wallet birthday to
        // the beginning of time.
        nTimeFirstKey = 1;
    } else if (!nTimeFirstKey || nCreateTime < nTimeFirstKey) {
        nTimeFirstKey = nCreateTime;
    }
}

bool CWallet::AddCScript(const CScript& redeemScript)
{
    if (!CCryptoKeyStore::AddCScript(redeemScript))
        return false;
    if (!fFileBacked)
        return true;
    return CWalletDB(strWalletFile).WriteCScript(Hash160(redeemScript), redeemScript);
}

bool CWallet::LoadCScript(const CScript& redeemScript)
{
    /* A sanity check was added in pull #3843 to avoid adding redeemScripts
     * that never can be redeemed. However, old wallets may still contain
     * these. Do not add them to the wallet and warn. */
    if (redeemScript.size() > MAX_SCRIPT_ELEMENT_SIZE)
    {
        std::string strAddr = CBitcoinAddress(CScriptID(redeemScript)).ToString();
        LogPrintf("%s: Warning: This wallet contains a redeemScript of size %i which exceeds maximum size %i thus can never be redeemed. Do not use address %s.\n",
            __func__, redeemScript.size(), MAX_SCRIPT_ELEMENT_SIZE, strAddr);
        return true;
    }

    return CCryptoKeyStore::AddCScript(redeemScript);
}

bool CWallet::AddWatchOnly(const CScript& dest)
{
    if (!CCryptoKeyStore::AddWatchOnly(dest))
        return false;
    const CKeyMetadata& meta = mapKeyMetadata[CScriptID(dest)];
    UpdateTimeFirstKey(meta.nCreateTime);
    NotifyWatchonlyChanged(true);
    if (!fFileBacked)
        return true;
    return CWalletDB(strWalletFile).WriteWatchOnly(dest, meta);
}

bool CWallet::AddWatchOnly(const CScript& dest, int64_t nCreateTime)
{
    mapKeyMetadata[CScriptID(dest)].nCreateTime = nCreateTime;
    return AddWatchOnly(dest);
}

bool CWallet::RemoveWatchOnly(const CScript &dest)
{
    AssertLockHeld(cs_wallet);
    if (!CCryptoKeyStore::RemoveWatchOnly(dest))
        return false;
    if (!HaveWatchOnly())
        NotifyWatchonlyChanged(false);
    if (fFileBacked)
        if (!CWalletDB(strWalletFile).EraseWatchOnly(dest))
            return false;

    return true;
}

bool CWallet::LoadWatchOnly(const CScript &dest)
{
    return CCryptoKeyStore::AddWatchOnly(dest);
}

bool CWallet::Unlock(const SecureString& strWalletPassphrase)
{
    CCrypter crypter;
    CKeyingMaterial vMasterKey;

    {
        LOCK(cs_wallet);
        BOOST_FOREACH(const MasterKeyMap::value_type& pMasterKey, mapMasterKeys)
        {
            if(!crypter.SetKeyFromPassphrase(strWalletPassphrase, pMasterKey.second.vchSalt, pMasterKey.second.nDeriveIterations, pMasterKey.second.nDerivationMethod))
                return false;
            if (!crypter.Decrypt(pMasterKey.second.vchCryptedKey, vMasterKey))
                continue; // try another master key
            if (CCryptoKeyStore::Unlock(vMasterKey))
                return true;
        }
    }
    return false;
}

bool CWallet::ChangeWalletPassphrase(const SecureString& strOldWalletPassphrase, const SecureString& strNewWalletPassphrase)
{
    bool fWasLocked = IsLocked();

    {
        LOCK(cs_wallet);
        Lock();

        CCrypter crypter;
        CKeyingMaterial vMasterKey;
        BOOST_FOREACH(MasterKeyMap::value_type& pMasterKey, mapMasterKeys)
        {
            if(!crypter.SetKeyFromPassphrase(strOldWalletPassphrase, pMasterKey.second.vchSalt, pMasterKey.second.nDeriveIterations, pMasterKey.second.nDerivationMethod))
                return false;
            if (!crypter.Decrypt(pMasterKey.second.vchCryptedKey, vMasterKey))
                return false;
            if (CCryptoKeyStore::Unlock(vMasterKey))
            {
                int64_t nStartTime = GetTimeMillis();
                crypter.SetKeyFromPassphrase(strNewWalletPassphrase, pMasterKey.second.vchSalt, pMasterKey.second.nDeriveIterations, pMasterKey.second.nDerivationMethod);
                pMasterKey.second.nDeriveIterations = pMasterKey.second.nDeriveIterations * (100 / ((double)(GetTimeMillis() - nStartTime)));

                nStartTime = GetTimeMillis();
                crypter.SetKeyFromPassphrase(strNewWalletPassphrase, pMasterKey.second.vchSalt, pMasterKey.second.nDeriveIterations, pMasterKey.second.nDerivationMethod);
                pMasterKey.second.nDeriveIterations = (pMasterKey.second.nDeriveIterations + pMasterKey.second.nDeriveIterations * 100 / ((double)(GetTimeMillis() - nStartTime))) / 2;

                if (pMasterKey.second.nDeriveIterations < 25000)
                    pMasterKey.second.nDeriveIterations = 25000;

                LogPrintf("Wallet passphrase changed to an nDeriveIterations of %i\n", pMasterKey.second.nDeriveIterations);

                if (!crypter.SetKeyFromPassphrase(strNewWalletPassphrase, pMasterKey.second.vchSalt, pMasterKey.second.nDeriveIterations, pMasterKey.second.nDerivationMethod))
                    return false;
                if (!crypter.Encrypt(vMasterKey, pMasterKey.second.vchCryptedKey))
                    return false;
                CWalletDB(strWalletFile).WriteMasterKey(pMasterKey.first, pMasterKey.second);
                if (fWasLocked)
                    Lock();
                return true;
            }
        }
    }

    return false;
}

void CWallet::SetBestChain(const CBlockLocator& loc)
{
    CWalletDB walletdb(strWalletFile);
    walletdb.WriteBestBlock(loc);
}

bool CWallet::SetMinVersion(enum WalletFeature nVersion, CWalletDB* pwalletdbIn, bool fExplicit)
{
    LOCK(cs_wallet); // nWalletVersion
    if (nWalletVersion >= nVersion)
        return true;

    // when doing an explicit upgrade, if we pass the max version permitted, upgrade all the way
    if (fExplicit && nVersion > nWalletMaxVersion)
            nVersion = FEATURE_LATEST;

    nWalletVersion = nVersion;

    if (nVersion > nWalletMaxVersion)
        nWalletMaxVersion = nVersion;

    if (fFileBacked)
    {
        CWalletDB* pwalletdb = pwalletdbIn ? pwalletdbIn : new CWalletDB(strWalletFile);
        if (nWalletVersion > 40000)
            pwalletdb->WriteMinVersion(nWalletVersion);
        if (!pwalletdbIn)
            delete pwalletdb;
    }

    return true;
}

bool CWallet::SetMaxVersion(int nVersion)
{
    LOCK(cs_wallet); // nWalletVersion, nWalletMaxVersion
    // cannot downgrade below current version
    if (nWalletVersion > nVersion)
        return false;

    nWalletMaxVersion = nVersion;

    return true;
}

set<uint256> CWallet::GetConflicts(const uint256& txid) const
{
    set<uint256> result;
    AssertLockHeld(cs_wallet);

    std::map<uint256, CWalletTx>::const_iterator it = mapWallet.find(txid);
    if (it == mapWallet.end())
        return result;
    const CWalletTx& wtx = it->second;

    std::pair<TxSpends::const_iterator, TxSpends::const_iterator> range;

    BOOST_FOREACH(const CTxIn& txin, wtx.tx->vin)
    {
        if (mapTxSpends.count(txin.prevout) <= 1)
            continue;  // No conflict if zero or one spends
        range = mapTxSpends.equal_range(txin.prevout);
        for (TxSpends::const_iterator _it = range.first; _it != range.second; ++_it)
            result.insert(_it->second);
    }
    return result;
}

bool CWallet::HasWalletSpend(const uint256& txid) const
{
    AssertLockHeld(cs_wallet);
    auto iter = mapTxSpends.lower_bound(COutPoint(txid, 0));
    return (iter != mapTxSpends.end() && iter->first.hash == txid);
}

void CWallet::Flush(bool shutdown)
{
    bitdb.Flush(shutdown);
}

bool CWallet::Verify()
{
    if (GetBoolArg("-disablewallet", DEFAULT_DISABLE_WALLET))
        return true;

    LogPrintf("Using BerkeleyDB version %s\n", DbEnv::version(0, 0, 0));
    std::string walletFile = GetArg("-wallet", DEFAULT_WALLET_DAT);

    LogPrintf("Using wallet %s\n", walletFile);
    uiInterface.InitMessage(_("Verifying wallet..."));

    // Wallet file must be a plain filename without a directory
    if (walletFile != boost::filesystem::basename(walletFile) + boost::filesystem::extension(walletFile))
        return InitError(strprintf(_("Wallet %s resides outside data directory %s"), walletFile, GetDataDir().string()));

    if (!bitdb.Open(GetDataDir()))
    {
        // try moving the database env out of the way
        boost::filesystem::path pathDatabase = GetDataDir() / "database";
        boost::filesystem::path pathDatabaseBak = GetDataDir() / strprintf("database.%d.bak", GetTime());
        try {
            boost::filesystem::rename(pathDatabase, pathDatabaseBak);
            LogPrintf("Moved old %s to %s. Retrying.\n", pathDatabase.string(), pathDatabaseBak.string());
        } catch (const boost::filesystem::filesystem_error&) {
            // failure is ok (well, not really, but it's not worse than what we started with)
        }

        // try again
        if (!bitdb.Open(GetDataDir())) {
            // if it still fails, it probably means we can't even create the database env
            return InitError(strprintf(_("Error initializing wallet database environment %s!"), GetDataDir()));
        }
    }

    if (GetBoolArg("-salvagewallet", false))
    {
        // Recover readable keypairs:
        if (!CWalletDB::Recover(bitdb, walletFile, true))
            return false;
    }

    if (boost::filesystem::exists(GetDataDir() / walletFile))
    {
        CDBEnv::VerifyResult r = bitdb.Verify(walletFile, CWalletDB::Recover);
        if (r == CDBEnv::RECOVER_OK)
        {
            InitWarning(strprintf(_("Warning: Wallet file corrupt, data salvaged!"
                                         " Original %s saved as %s in %s; if"
                                         " your balance or transactions are incorrect you should"
                                         " restore from a backup."),
                walletFile, "wallet.{timestamp}.bak", GetDataDir()));
        }
        if (r == CDBEnv::RECOVER_FAIL)
            return InitError(strprintf(_("%s corrupt, salvage failed"), walletFile));
    }

    return true;
}

void CWallet::SyncMetaData(pair<TxSpends::iterator, TxSpends::iterator> range)
{
    // We want all the wallet transactions in range to have the same metadata as
    // the oldest (smallest nOrderPos).
    // So: find smallest nOrderPos:

    int nMinOrderPos = std::numeric_limits<int>::max();
    const CWalletTx* copyFrom = NULL;
    for (TxSpends::iterator it = range.first; it != range.second; ++it)
    {
        const uint256& hash = it->second;
        int n = mapWallet[hash].nOrderPos;
        if (n < nMinOrderPos)
        {
            nMinOrderPos = n;
            copyFrom = &mapWallet[hash];
        }
    }
    // Now copy data from copyFrom to rest:
    for (TxSpends::iterator it = range.first; it != range.second; ++it)
    {
        const uint256& hash = it->second;
        CWalletTx* copyTo = &mapWallet[hash];
        if (copyFrom == copyTo) continue;
        if (!copyFrom->IsEquivalentTo(*copyTo)) continue;
        copyTo->mapValue = copyFrom->mapValue;
        copyTo->vOrderForm = copyFrom->vOrderForm;
        // fTimeReceivedIsTxTime not copied on purpose
        // nTimeReceived not copied on purpose
        copyTo->nTimeSmart = copyFrom->nTimeSmart;
        copyTo->fFromMe = copyFrom->fFromMe;
        copyTo->strFromAccount = copyFrom->strFromAccount;
        // nOrderPos not copied on purpose
        // cached members not copied on purpose
    }
}

/**
 * Outpoint is spent if any non-conflicted transaction
 * spends it:
 */
bool CWallet::IsSpent(const uint256& hash, unsigned int n) const
{
    const COutPoint outpoint(hash, n);
    pair<TxSpends::const_iterator, TxSpends::const_iterator> range;
    range = mapTxSpends.equal_range(outpoint);

    for (TxSpends::const_iterator it = range.first; it != range.second; ++it)
    {
        const uint256& wtxid = it->second;
        std::map<uint256, CWalletTx>::const_iterator mit = mapWallet.find(wtxid);
        if (mit != mapWallet.end()) {
            int depth = mit->second.GetDepthInMainChain();
            if (depth > 0  || (depth == 0 && !mit->second.isAbandoned()))
                return true; // Spent
        }
    }
    return false;
}

void CWallet::AddToSpends(const COutPoint& outpoint, const uint256& wtxid)
{
    mapTxSpends.insert(make_pair(outpoint, wtxid));

    pair<TxSpends::iterator, TxSpends::iterator> range;
    range = mapTxSpends.equal_range(outpoint);
    SyncMetaData(range);
}


void CWallet::AddToSpends(const uint256& wtxid)
{
    assert(mapWallet.count(wtxid));
    CWalletTx& thisTx = mapWallet[wtxid];
    if (thisTx.IsCoinBase()) // Coinbases don't spend anything!
        return;

    BOOST_FOREACH(const CTxIn& txin, thisTx.tx->vin)
        AddToSpends(txin.prevout, wtxid);
}

bool CWallet::EncryptWallet(const SecureString& strWalletPassphrase)
{
    if (IsCrypted())
        return false;

    CKeyingMaterial vMasterKey;

    vMasterKey.resize(WALLET_CRYPTO_KEY_SIZE);
    GetStrongRandBytes(&vMasterKey[0], WALLET_CRYPTO_KEY_SIZE);

    CMasterKey kMasterKey;

    kMasterKey.vchSalt.resize(WALLET_CRYPTO_SALT_SIZE);
    GetStrongRandBytes(&kMasterKey.vchSalt[0], WALLET_CRYPTO_SALT_SIZE);

    CCrypter crypter;
    int64_t nStartTime = GetTimeMillis();
    crypter.SetKeyFromPassphrase(strWalletPassphrase, kMasterKey.vchSalt, 25000, kMasterKey.nDerivationMethod);
    kMasterKey.nDeriveIterations = 2500000 / ((double)(GetTimeMillis() - nStartTime));

    nStartTime = GetTimeMillis();
    crypter.SetKeyFromPassphrase(strWalletPassphrase, kMasterKey.vchSalt, kMasterKey.nDeriveIterations, kMasterKey.nDerivationMethod);
    kMasterKey.nDeriveIterations = (kMasterKey.nDeriveIterations + kMasterKey.nDeriveIterations * 100 / ((double)(GetTimeMillis() - nStartTime))) / 2;

    if (kMasterKey.nDeriveIterations < 25000)
        kMasterKey.nDeriveIterations = 25000;

    LogPrintf("Encrypting Wallet with an nDeriveIterations of %i\n", kMasterKey.nDeriveIterations);

    if (!crypter.SetKeyFromPassphrase(strWalletPassphrase, kMasterKey.vchSalt, kMasterKey.nDeriveIterations, kMasterKey.nDerivationMethod))
        return false;
    if (!crypter.Encrypt(vMasterKey, kMasterKey.vchCryptedKey))
        return false;

    {
        LOCK(cs_wallet);
        mapMasterKeys[++nMasterKeyMaxID] = kMasterKey;
        if (fFileBacked)
        {
            assert(!pwalletdbEncryption);
            pwalletdbEncryption = new CWalletDB(strWalletFile);
            if (!pwalletdbEncryption->TxnBegin()) {
                delete pwalletdbEncryption;
                pwalletdbEncryption = NULL;
                return false;
            }
            pwalletdbEncryption->WriteMasterKey(nMasterKeyMaxID, kMasterKey);
        }

        if (!EncryptKeys(vMasterKey))
        {
            if (fFileBacked) {
                pwalletdbEncryption->TxnAbort();
                delete pwalletdbEncryption;
            }
            // We now probably have half of our keys encrypted in memory, and half not...
            // die and let the user reload the unencrypted wallet.
            assert(false);
        }

        // Encryption was introduced in version 0.4.0
        SetMinVersion(FEATURE_WALLETCRYPT, pwalletdbEncryption, true);

        if (fFileBacked)
        {
            if (!pwalletdbEncryption->TxnCommit()) {
                delete pwalletdbEncryption;
                // We now have keys encrypted in memory, but not on disk...
                // die to avoid confusion and let the user reload the unencrypted wallet.
                assert(false);
            }

            delete pwalletdbEncryption;
            pwalletdbEncryption = NULL;
        }

        Lock();
        Unlock(strWalletPassphrase);

        // if we are using HD, replace the HD master key (seed) with a new one
        if (IsHDEnabled()) {
            CKey key;
            CPubKey masterPubKey = GenerateNewHDMasterKey();
            if (!SetHDMasterKey(masterPubKey))
                return false;
        }

        NewKeyPool();
        Lock();

        // Need to completely rewrite the wallet file; if we don't, bdb might keep
        // bits of the unencrypted private key in slack space in the database file.
        CDB::Rewrite(strWalletFile);

    }
    NotifyStatusChanged(this);

    return true;
}

DBErrors CWallet::ReorderTransactions()
{
    LOCK(cs_wallet);
    CWalletDB walletdb(strWalletFile);

    // Old wallets didn't have any defined order for transactions
    // Probably a bad idea to change the output of this

    // First: get all CWalletTx and CAccountingEntry into a sorted-by-time multimap.
    typedef pair<CWalletTx*, CAccountingEntry*> TxPair;
    typedef multimap<int64_t, TxPair > TxItems;
    TxItems txByTime;

    for (map<uint256, CWalletTx>::iterator it = mapWallet.begin(); it != mapWallet.end(); ++it)
    {
        CWalletTx* wtx = &((*it).second);
        txByTime.insert(make_pair(wtx->nTimeReceived, TxPair(wtx, (CAccountingEntry*)0)));
    }
    list<CAccountingEntry> acentries;
    walletdb.ListAccountCreditDebit("", acentries);
    BOOST_FOREACH(CAccountingEntry& entry, acentries)
    {
        txByTime.insert(make_pair(entry.nTime, TxPair((CWalletTx*)0, &entry)));
    }

    nOrderPosNext = 0;
    std::vector<int64_t> nOrderPosOffsets;
    for (TxItems::iterator it = txByTime.begin(); it != txByTime.end(); ++it)
    {
        CWalletTx *const pwtx = (*it).second.first;
        CAccountingEntry *const pacentry = (*it).second.second;
        int64_t& nOrderPos = (pwtx != 0) ? pwtx->nOrderPos : pacentry->nOrderPos;

        if (nOrderPos == -1)
        {
            nOrderPos = nOrderPosNext++;
            nOrderPosOffsets.push_back(nOrderPos);

            if (pwtx)
            {
                if (!walletdb.WriteTx(*pwtx))
                    return DB_LOAD_FAIL;
            }
            else
                if (!walletdb.WriteAccountingEntry(pacentry->nEntryNo, *pacentry))
                    return DB_LOAD_FAIL;
        }
        else
        {
            int64_t nOrderPosOff = 0;
            BOOST_FOREACH(const int64_t& nOffsetStart, nOrderPosOffsets)
            {
                if (nOrderPos >= nOffsetStart)
                    ++nOrderPosOff;
            }
            nOrderPos += nOrderPosOff;
            nOrderPosNext = std::max(nOrderPosNext, nOrderPos + 1);

            if (!nOrderPosOff)
                continue;

            // Since we're changing the order, write it back
            if (pwtx)
            {
                if (!walletdb.WriteTx(*pwtx))
                    return DB_LOAD_FAIL;
            }
            else
                if (!walletdb.WriteAccountingEntry(pacentry->nEntryNo, *pacentry))
                    return DB_LOAD_FAIL;
        }
    }
    walletdb.WriteOrderPosNext(nOrderPosNext);

    return DB_LOAD_OK;
}

int64_t CWallet::IncOrderPosNext(CWalletDB *pwalletdb)
{
    AssertLockHeld(cs_wallet); // nOrderPosNext
    int64_t nRet = nOrderPosNext++;
    if (pwalletdb) {
        pwalletdb->WriteOrderPosNext(nOrderPosNext);
    } else {
        CWalletDB(strWalletFile).WriteOrderPosNext(nOrderPosNext);
    }
    return nRet;
}

bool CWallet::AccountMove(std::string strFrom, std::string strTo, CAmount nAmount, std::string strComment)
{
    CWalletDB walletdb(strWalletFile);
    if (!walletdb.TxnBegin())
        return false;

    int64_t nNow = GetAdjustedTime();

    // Debit
    CAccountingEntry debit;
    debit.nOrderPos = IncOrderPosNext(&walletdb);
    debit.strAccount = strFrom;
    debit.nCreditDebit = -nAmount;
    debit.nTime = nNow;
    debit.strOtherAccount = strTo;
    debit.strComment = strComment;
    AddAccountingEntry(debit, &walletdb);

    // Credit
    CAccountingEntry credit;
    credit.nOrderPos = IncOrderPosNext(&walletdb);
    credit.strAccount = strTo;
    credit.nCreditDebit = nAmount;
    credit.nTime = nNow;
    credit.strOtherAccount = strFrom;
    credit.strComment = strComment;
    AddAccountingEntry(credit, &walletdb);

    if (!walletdb.TxnCommit())
        return false;

    return true;
}

bool CWallet::GetAccountPubkey(CPubKey &pubKey, std::string strAccount, bool bForceNew)
{
    CWalletDB walletdb(strWalletFile);

    CAccount account;
    walletdb.ReadAccount(strAccount, account);

    if (!bForceNew) {
        if (!account.vchPubKey.IsValid())
            bForceNew = true;
        else {
            // Check if the current key has been used
            CScript scriptPubKey = GetScriptForDestination(account.vchPubKey.GetID());
            for (map<uint256, CWalletTx>::iterator it = mapWallet.begin();
                 it != mapWallet.end() && account.vchPubKey.IsValid();
                 ++it)
                BOOST_FOREACH(const CTxOut& txout, (*it).second.tx->vout)
                    if (txout.scriptPubKey == scriptPubKey) {
                        bForceNew = true;
                        break;
                    }
        }
    }

    // Generate a new key
    if (bForceNew) {
        if (!GetKeyFromPool(account.vchPubKey))
            return false;

        SetAddressBook(account.vchPubKey.GetID(), strAccount, "receive");
        walletdb.WriteAccount(strAccount, account);
    }

    pubKey = account.vchPubKey;

    return true;
}

void CWallet::MarkDirty()
{
    {
        LOCK(cs_wallet);
        BOOST_FOREACH(PAIRTYPE(const uint256, CWalletTx)& item, mapWallet)
            item.second.MarkDirty();
    }
}

bool CWallet::MarkReplaced(const uint256& originalHash, const uint256& newHash)
{
    LOCK(cs_wallet);

    auto mi = mapWallet.find(originalHash);

    // There is a bug if MarkReplaced is not called on an existing wallet transaction.
    assert(mi != mapWallet.end());

    CWalletTx& wtx = (*mi).second;

    // Ensure for now that we're not overwriting data
    assert(wtx.mapValue.count("replaced_by_txid") == 0);

    wtx.mapValue["replaced_by_txid"] = newHash.ToString();

    CWalletDB walletdb(strWalletFile, "r+");

    bool success = true;
    if (!walletdb.WriteTx(wtx)) {
        LogPrintf("%s: Updating walletdb tx %s failed", __func__, wtx.GetHash().ToString());
        success = false;
    }

    NotifyTransactionChanged(this, originalHash, CT_UPDATED);

    return success;
}

bool CWallet::AddToWallet(const CWalletTx& wtxIn, bool fFlushOnClose)
{
    LOCK(cs_wallet);

    CWalletDB walletdb(strWalletFile, "r+", fFlushOnClose);

    uint256 hash = wtxIn.GetHash();

    // Inserts only if not already there, returns tx inserted or tx found
    pair<map<uint256, CWalletTx>::iterator, bool> ret = mapWallet.insert(make_pair(hash, wtxIn));
    CWalletTx& wtx = (*ret.first).second;
    wtx.BindWallet(this);
    bool fInsertedNew = ret.second;
    if (fInsertedNew)
    {
        wtx.nTimeReceived = GetAdjustedTime();
        wtx.nOrderPos = IncOrderPosNext(&walletdb);
        wtxOrdered.insert(make_pair(wtx.nOrderPos, TxPair(&wtx, (CAccountingEntry*)0)));

        wtx.nTimeSmart = wtx.nTimeReceived;
        if (!wtxIn.hashUnset())
        {
            if (mapBlockIndex.count(wtxIn.hashBlock))
            {
                int64_t latestNow = wtx.nTimeReceived;
                int64_t latestEntry = 0;
                {
                    // Tolerate times up to the last timestamp in the wallet not more than 5 minutes into the future
                    int64_t latestTolerated = latestNow + 300;
                    const TxItems & txOrdered = wtxOrdered;
                    for (TxItems::const_reverse_iterator it = txOrdered.rbegin(); it != txOrdered.rend(); ++it)
                    {
                        CWalletTx *const pwtx = (*it).second.first;
                        if (pwtx == &wtx)
                            continue;
                        CAccountingEntry *const pacentry = (*it).second.second;
                        int64_t nSmartTime;
                        if (pwtx)
                        {
                            nSmartTime = pwtx->nTimeSmart;
                            if (!nSmartTime)
                                nSmartTime = pwtx->nTimeReceived;
                        }
                        else
                            nSmartTime = pacentry->nTime;
                        if (nSmartTime <= latestTolerated)
                        {
                            latestEntry = nSmartTime;
                            if (nSmartTime > latestNow)
                                latestNow = nSmartTime;
                            break;
                        }
                    }
                }

                int64_t blocktime = mapBlockIndex[wtxIn.hashBlock]->GetBlockTime();
                wtx.nTimeSmart = std::max(latestEntry, std::min(blocktime, latestNow));
            }
            else
                LogPrintf("AddToWallet(): found %s in block %s not in index\n",
                         wtxIn.GetHash().ToString(),
                         wtxIn.hashBlock.ToString());
        }
        AddToSpends(hash);
    }

    bool fUpdated = false;
    if (!fInsertedNew)
    {
        // Merge
        if (!wtxIn.hashUnset() && wtxIn.hashBlock != wtx.hashBlock)
        {
            wtx.hashBlock = wtxIn.hashBlock;
            fUpdated = true;
        }
        // If no longer abandoned, update
        if (wtxIn.hashBlock.IsNull() && wtx.isAbandoned())
        {
            wtx.hashBlock = wtxIn.hashBlock;
            fUpdated = true;
        }
        if (wtxIn.nIndex != -1 && (wtxIn.nIndex != wtx.nIndex))
        {
            wtx.nIndex = wtxIn.nIndex;
            fUpdated = true;
        }
        if (wtxIn.fFromMe && wtxIn.fFromMe != wtx.fFromMe)
        {
            wtx.fFromMe = wtxIn.fFromMe;
            fUpdated = true;
        }
    }

    //// debug print
    LogPrintf("AddToWallet %s  %s%s\n", wtxIn.GetHash().ToString(), (fInsertedNew ? "new" : ""), (fUpdated ? "update" : ""));

    // Write to disk
    if (fInsertedNew || fUpdated)
        if (!walletdb.WriteTx(wtx))
            return false;

    // Break debit/credit balance caches:
    wtx.MarkDirty();

    // Notify UI of new or updated transaction
    NotifyTransactionChanged(this, hash, fInsertedNew ? CT_NEW : CT_UPDATED);

    // notify an external script when a wallet transaction comes in or is updated
    std::string strCmd = GetArg("-walletnotify", "");

    if ( !strCmd.empty())
    {
        boost::replace_all(strCmd, "%s", wtxIn.GetHash().GetHex());
        boost::thread t(runCommand, strCmd); // thread runs free
    }

    return true;
}

bool CWallet::LoadToWallet(const CWalletTx& wtxIn)
{
    uint256 hash = wtxIn.GetHash();

    mapWallet[hash] = wtxIn;
    CWalletTx& wtx = mapWallet[hash];
    wtx.BindWallet(this);
    wtxOrdered.insert(make_pair(wtx.nOrderPos, TxPair(&wtx, (CAccountingEntry*)0)));
    AddToSpends(hash);
    BOOST_FOREACH(const CTxIn& txin, wtx.tx->vin) {
        if (mapWallet.count(txin.prevout.hash)) {
            CWalletTx& prevtx = mapWallet[txin.prevout.hash];
            if (prevtx.nIndex == -1 && !prevtx.hashUnset()) {
                MarkConflicted(prevtx.hashBlock, wtx.GetHash());
            }
        }
    }

    return true;
}

/**
 * Add a transaction to the wallet, or update it.  pIndex and posInBlock should
 * be set when the transaction was known to be included in a block.  When
 * posInBlock = SYNC_TRANSACTION_NOT_IN_BLOCK (-1) , then wallet state is not
 * updated in AddToWallet, but notifications happen and cached balances are
 * marked dirty.
 * If fUpdate is true, existing transactions will be updated.
 * TODO: One exception to this is that the abandoned state is cleared under the
 * assumption that any further notification of a transaction that was considered
 * abandoned is an indication that it is not safe to be considered abandoned.
 * Abandoned state should probably be more carefuly tracked via different
 * posInBlock signals or by checking mempool presence when necessary.
 */
bool CWallet::AddToWalletIfInvolvingMe(const CTransaction& tx, const CBlockIndex* pIndex, int posInBlock, bool fUpdate)
{
    {
        AssertLockHeld(cs_wallet);

        if (posInBlock != -1) {
            BOOST_FOREACH(const CTxIn& txin, tx.vin) {
                std::pair<TxSpends::const_iterator, TxSpends::const_iterator> range = mapTxSpends.equal_range(txin.prevout);
                while (range.first != range.second) {
                    if (range.first->second != tx.GetHash()) {
                        LogPrintf("Transaction %s (in block %s) conflicts with wallet transaction %s (both spend %s:%i)\n", tx.GetHash().ToString(), pIndex->GetBlockHash().ToString(), range.first->second.ToString(), range.first->first.hash.ToString(), range.first->first.n);
                        MarkConflicted(pIndex->GetBlockHash(), range.first->second);
                    }
                    range.first++;
                }
            }
        }

        bool fExisted = mapWallet.count(tx.GetHash()) != 0;
        if (fExisted && !fUpdate) return false;
        if (fExisted || IsMine(tx) || IsFromMe(tx))
        {
            CWalletTx wtx(this, MakeTransactionRef(tx));

            // Get merkle branch if transaction was found in a block
            if (posInBlock != -1)
                wtx.SetMerkleBranch(pIndex, posInBlock);

            return AddToWallet(wtx, false);
        }
    }
    return false;
}

bool CWallet::AbandonTransaction(const uint256& hashTx)
{
    LOCK2(cs_main, cs_wallet);

    CWalletDB walletdb(strWalletFile, "r+");

    std::set<uint256> todo;
    std::set<uint256> done;

    // Can't mark abandoned if confirmed or in mempool
    assert(mapWallet.count(hashTx));
    CWalletTx& origtx = mapWallet[hashTx];
    if (origtx.GetDepthInMainChain() > 0 || origtx.InMempool()) {
        return false;
    }

    todo.insert(hashTx);

    while (!todo.empty()) {
        uint256 now = *todo.begin();
        todo.erase(now);
        done.insert(now);
        assert(mapWallet.count(now));
        CWalletTx& wtx = mapWallet[now];
        int currentconfirm = wtx.GetDepthInMainChain();
        // If the orig tx was not in block, none of its spends can be
        assert(currentconfirm <= 0);
        // if (currentconfirm < 0) {Tx and spends are already conflicted, no need to abandon}
        if (currentconfirm == 0 && !wtx.isAbandoned()) {
            // If the orig tx was not in block/mempool, none of its spends can be in mempool
            assert(!wtx.InMempool());
            wtx.nIndex = -1;
            wtx.setAbandoned();
            wtx.MarkDirty();
            walletdb.WriteTx(wtx);
            NotifyTransactionChanged(this, wtx.GetHash(), CT_UPDATED);
            // Iterate over all its outputs, and mark transactions in the wallet that spend them abandoned too
            TxSpends::const_iterator iter = mapTxSpends.lower_bound(COutPoint(hashTx, 0));
            while (iter != mapTxSpends.end() && iter->first.hash == now) {
                if (!done.count(iter->second)) {
                    todo.insert(iter->second);
                }
                iter++;
            }
            // If a transaction changes 'conflicted' state, that changes the balance
            // available of the outputs it spends. So force those to be recomputed
            BOOST_FOREACH(const CTxIn& txin, wtx.tx->vin)
            {
                if (mapWallet.count(txin.prevout.hash))
                    mapWallet[txin.prevout.hash].MarkDirty();
            }
        }
    }

    return true;
}

void CWallet::MarkConflicted(const uint256& hashBlock, const uint256& hashTx)
{
    LOCK2(cs_main, cs_wallet);

    int conflictconfirms = 0;
    if (mapBlockIndex.count(hashBlock)) {
        CBlockIndex* pindex = mapBlockIndex[hashBlock];
        if (chainActive.Contains(pindex)) {
            conflictconfirms = -(chainActive.Height() - pindex->nHeight + 1);
        }
    }
    // If number of conflict confirms cannot be determined, this means
    // that the block is still unknown or not yet part of the main chain,
    // for example when loading the wallet during a reindex. Do nothing in that
    // case.
    if (conflictconfirms >= 0)
        return;

    // Do not flush the wallet here for performance reasons
    CWalletDB walletdb(strWalletFile, "r+", false);

    std::set<uint256> todo;
    std::set<uint256> done;

    todo.insert(hashTx);

    while (!todo.empty()) {
        uint256 now = *todo.begin();
        todo.erase(now);
        done.insert(now);
        assert(mapWallet.count(now));
        CWalletTx& wtx = mapWallet[now];
        int currentconfirm = wtx.GetDepthInMainChain();
        if (conflictconfirms < currentconfirm) {
            // Block is 'more conflicted' than current confirm; update.
            // Mark transaction as conflicted with this block.
            wtx.nIndex = -1;
            wtx.hashBlock = hashBlock;
            wtx.MarkDirty();
            walletdb.WriteTx(wtx);
            // Iterate over all its outputs, and mark transactions in the wallet that spend them conflicted too
            TxSpends::const_iterator iter = mapTxSpends.lower_bound(COutPoint(now, 0));
            while (iter != mapTxSpends.end() && iter->first.hash == now) {
                 if (!done.count(iter->second)) {
                     todo.insert(iter->second);
                 }
                 iter++;
            }
            // If a transaction changes 'conflicted' state, that changes the balance
            // available of the outputs it spends. So force those to be recomputed
            BOOST_FOREACH(const CTxIn& txin, wtx.tx->vin)
            {
                if (mapWallet.count(txin.prevout.hash))
                    mapWallet[txin.prevout.hash].MarkDirty();
            }
        }
    }
}

void CWallet::SyncTransaction(const CTransaction& tx, const CBlockIndex *pindex, int posInBlock)
{
    LOCK2(cs_main, cs_wallet);

    if (!AddToWalletIfInvolvingMe(tx, pindex, posInBlock, true))
        return; // Not one of ours

    // If a transaction changes 'conflicted' state, that changes the balance
    // available of the outputs it spends. So force those to be
    // recomputed, also:
    BOOST_FOREACH(const CTxIn& txin, tx.vin)
    {
        if (mapWallet.count(txin.prevout.hash))
            mapWallet[txin.prevout.hash].MarkDirty();
    }
}


isminetype CWallet::IsMine(const CTxIn &txin) const
{
    {
        LOCK(cs_wallet);
        map<uint256, CWalletTx>::const_iterator mi = mapWallet.find(txin.prevout.hash);
        if (mi != mapWallet.end())
        {
            const CWalletTx& prev = (*mi).second;
            if (txin.prevout.n < prev.tx->vout.size())
                return IsMine(prev.tx->vout[txin.prevout.n]);
        }
    }
    return ISMINE_NO;
}

// Note that this function doesn't distinguish between a 0-valued input,
// and a not-"is mine" (according to the filter) input.
CAmountMap CWallet::GetDebit(const CTxIn &txin, const isminefilter& filter) const
{
    {
        LOCK(cs_wallet);
        std::map<uint256, CWalletTx>::const_iterator mi = mapWallet.find(txin.prevout.hash);
        if (mi != mapWallet.end())
        {
            const CWalletTx& prev = (*mi).second;
            if (txin.prevout.n < prev.tx->vout.size()) {
                if (IsMine(prev.tx->vout[txin.prevout.n]) & filter) {
                    CAmountMap map;
                    map[prev.GetOutputAsset(txin.prevout.n)] = std::max<CAmount>(0, prev.GetOutputValueOut(txin.prevout.n));
                    return map;
                }
            }
        }
    }
    return CAmountMap();
}

isminetype CWallet::IsMine(const CTxOut& txout) const
{
    return ::IsMine(*this, txout.scriptPubKey);
}

bool CWallet::IsChange(const CTxOut& txout) const
{
    // TODO: fix handling of 'change' outputs. The assumption is that any
    // payment to a script that is ours, but is not in the address book
    // is change. That assumption is likely to break when we implement multisignature
    // wallets that return change back into a multi-signature-protected address;
    // a better way of identifying which outputs are 'the send' and which are
    // 'the change' will need to be implemented (maybe extend CWalletTx to remember
    // which output, if any, was change).
    if (::IsMine(*this, txout.scriptPubKey))
    {
        CTxDestination address;
        if (!ExtractDestination(txout.scriptPubKey, address))
            return true;

        LOCK(cs_wallet);
        if (!mapAddressBook.count(address))
            return true;
    }
    return false;
}

bool CWallet::IsMine(const CTransaction& tx) const
{
    BOOST_FOREACH(const CTxOut& txout, tx.vout)
        if (IsMine(txout))
            return true;
    return false;
}

bool CWallet::IsFromMe(const CTransaction& tx) const
{
    return (GetDebit(tx, ISMINE_ALL) > CAmountMap());
}

CAmountMap CWallet::GetDebit(const CTransaction& tx, const isminefilter& filter) const
{
    CAmountMap nDebit;
    BOOST_FOREACH(const CTxIn& txin, tx.vin)
    {
        nDebit += GetDebit(txin, filter);
        if (!MoneyRange(nDebit))
            throw std::runtime_error(std::string(__func__) + ": value out of range");
    }
    return nDebit;
}

bool CWallet::IsAllFromMe(const CTransaction& tx, const isminefilter& filter) const
{
    LOCK(cs_wallet);

    BOOST_FOREACH(const CTxIn& txin, tx.vin)
    {
        auto mi = mapWallet.find(txin.prevout.hash);
        if (mi == mapWallet.end())
            return false; // any unknown inputs can't be from us

        const CWalletTx& prev = (*mi).second;

        if (txin.prevout.n >= prev.tx->vout.size())
            return false; // invalid input!

        if (!(IsMine(prev.tx->vout[txin.prevout.n]) & filter))
            return false;
    }
    return true;
}

CAmountMap CWallet::GetCredit(const CWalletTx& tx, const isminefilter& filter) const
{
    CAmountMap nCredit;
    for (unsigned int i = 0; i < tx.tx->vout.size(); i++)
    {
        nCredit += tx.GetCredit(i, filter);
        if (!MoneyRange(nCredit))
            throw std::runtime_error(std::string(__func__) + ": value out of range");
    }
    return nCredit;
}

CAmountMap CWallet::GetChange(const CWalletTx& tx) const
{
    CAmountMap nChange;
    for (unsigned int i = 0; i < tx.tx->vout.size(); i++)
    {
        nChange += tx.GetChange(i);
        if (!MoneyRange(nChange))
            throw std::runtime_error(std::string(__func__) + ": value out of range");
    }
    return nChange;
}

CPubKey CWallet::GenerateNewHDMasterKey()
{
    CKey key;
    key.MakeNewKey(true);

    int64_t nCreationTime = GetTime();
    CKeyMetadata metadata(nCreationTime);

    // calculate the pubkey
    CPubKey pubkey = key.GetPubKey();
    assert(key.VerifyPubKey(pubkey));

    // set the hd keypath to "m" -> Master, refers the masterkeyid to itself
    metadata.hdKeypath     = "m";
    metadata.hdMasterKeyID = pubkey.GetID();

    {
        LOCK(cs_wallet);

        // mem store the metadata
        mapKeyMetadata[pubkey.GetID()] = metadata;

        // write the key&metadata to the database
        if (!AddKeyPubKey(key, pubkey))
            throw std::runtime_error(std::string(__func__) + ": AddKeyPubKey failed");
    }

    return pubkey;
}

bool CWallet::SetHDMasterKey(const CPubKey& pubkey)
{
    LOCK(cs_wallet);

    // ensure this wallet.dat can only be opened by clients supporting HD
    SetMinVersion(FEATURE_HD);

    // store the keyid (hash160) together with
    // the child index counter in the database
    // as a hdchain object
    CHDChain newHdChain;
    newHdChain.masterKeyID = pubkey.GetID();
    SetHDChain(newHdChain, false);

    return true;
}

bool CWallet::SetHDChain(const CHDChain& chain, bool memonly)
{
    LOCK(cs_wallet);
    if (!memonly && !CWalletDB(strWalletFile).WriteHDChain(chain))
        throw runtime_error(std::string(__func__) + ": writing chain failed");

    hdChain = chain;
    return true;
}

bool CWallet::IsHDEnabled()
{
    return !hdChain.masterKeyID.IsNull();
}

int64_t CWalletTx::GetTxTime() const
{
    int64_t n = nTimeSmart;
    return n ? n : nTimeReceived;
}

int CWalletTx::GetRequestCount() const
{
    // Returns -1 if it wasn't being tracked
    int nRequests = -1;
    {
        LOCK(pwallet->cs_wallet);
        if (IsCoinBase())
        {
            // Generated block
            if (!hashUnset())
            {
                map<uint256, int>::const_iterator mi = pwallet->mapRequestCount.find(hashBlock);
                if (mi != pwallet->mapRequestCount.end())
                    nRequests = (*mi).second;
            }
        }
        else
        {
            // Did anyone request this transaction?
            map<uint256, int>::const_iterator mi = pwallet->mapRequestCount.find(GetHash());
            if (mi != pwallet->mapRequestCount.end())
            {
                nRequests = (*mi).second;

                // How about the block it's in?
                if (nRequests == 0 && !hashUnset())
                {
                    map<uint256, int>::const_iterator _mi = pwallet->mapRequestCount.find(hashBlock);
                    if (_mi != pwallet->mapRequestCount.end())
                        nRequests = (*_mi).second;
                    else
                        nRequests = 1; // If it's in someone else's block it must have got out
                }
            }
        }
    }
    return nRequests;
}

void CWalletTx::GetAmounts(list<COutputEntry>& listReceived,
                           list<COutputEntry>& listSent, CAmount& nFee, string& strSentAccount, const isminefilter& filter) const
{
    nFee = 0;
    listReceived.clear();
    listSent.clear();
    strSentAccount = strFromAccount;

    // Compute fee:
    CAmountMap nDebit = GetDebit(filter);
    if (nDebit > CAmountMap()) // debit>0 means we signed/sent this transaction
    {
        nFee = tx->GetFee().begin()->second;
    }

    CTxDestination addressUnaccounted = CNoDestination();
    int voutUnaccounted = -1;
    CAmountMap nValueUnaccounted = nDebit;
    nValueUnaccounted[tx->GetFee().begin()->first] -= nFee;
    int nUnaccountedOutputs = 0;

    // Sent/received.
    for (unsigned int i = 0; i < tx->vout.size(); ++i)
    {
        const CTxOut& txout = tx->vout[i];
        CAmount nValueOut = GetOutputValueOut(i);
        CAsset asset = GetOutputAsset(i);

        if (nValueOut >= 0) {
            nValueUnaccounted[asset] -= nValueOut;
        }
        isminetype fIsMine = nValueOut >= 0 ? pwallet->IsMine(txout) : ISMINE_NO;
        // Only need to handle txouts if AT LEAST one of these is true:
        //   1) they debit from us (sent)
        //   2) the output is to us (received)
        if (nDebit > CAmountMap())
        {
            // Don't report 'change' txouts
            if (pwallet->IsChange(txout))
                continue;
        }
        else if (!(fIsMine & filter))
            continue;

        // In either case, we need to get the destination address
        CTxDestination address;

        if (!ExtractDestination(txout.scriptPubKey, address) && !txout.scriptPubKey.IsUnspendable())
        {
            LogPrintf("CWalletTx::GetAmounts: Unknown transaction type found, txid %s\n",
                 this->GetHash().ToString());
            address = CNoDestination();
        }

        if (nDebit > CAmountMap() && nValueOut < 0) {
            // This is an output we'd add to listSent, but we don't know its value.
            // Instead just remember its details so we can reconstruct it or
            // correct for it afterwards.
            addressUnaccounted = address;
            voutUnaccounted = i;
            nUnaccountedOutputs++;
            continue;
        }

        COutputEntry output = {address, nValueOut, asset, (int)i, GetOutputBlindingPubKey(i), GetOutputBlindingFactor(i), GetOutputAssetBlindingFactor(i)};

        // If we are debited by the transaction, add the output as a "sent" entry
        if (nDebit > CAmountMap() && !txout.IsFee())
            listSent.push_back(output);

        // If we are receiving the output, add it as a "received" entry
        if (fIsMine & filter)
            listReceived.push_back(output);
    }

    // This should not happen if transaction was created via CreateTransaction
    if (nValueUnaccounted != CAmountMap() && nDebit > CAmountMap()) {
        if (nValueUnaccounted > CAmountMap() && nUnaccountedOutputs == 1) {
            // There is exactly one sent output with unknown value. Reconstruct it.
            CAsset unaccountedAsset;
            for (const auto &entry : nValueUnaccounted) {
                if (entry.second > 0)
                    unaccountedAsset = entry.first;
            }
            COutputEntry unaccounted = {addressUnaccounted, nValueUnaccounted[unaccountedAsset], unaccountedAsset, voutUnaccounted, CPubKey(), uint256(), uint256()};
            listSent.push_back(unaccounted);
        } else {
            // It's not simple. Create synthetic unknown output entries for each asset.
            for (const auto &entry : nValueUnaccounted) {
                if (entry.second > 0) {
                    COutputEntry unaccounted = {CNoDestination(), entry.second, entry.first, -1, CPubKey(), uint256(), uint256()};
                    listSent.push_back(unaccounted);
                }
            }
        }
    }
}

void CWalletTx::GetAccountAmounts(const string& strAccount, CAmount& nReceived,
                                  CAmount& nSent, CAmount& nFee, const isminefilter& filter) const
{
    nReceived = nSent = nFee = 0;

    CAmount allFee;
    string strSentAccount;
    list<COutputEntry> listReceived;
    list<COutputEntry> listSent;
    GetAmounts(listReceived, listSent, allFee, strSentAccount, filter);

    if (strAccount == strSentAccount)
    {
        BOOST_FOREACH(const COutputEntry& s, listSent)
            nSent += s.amount;
        nFee = allFee;
    }
    {
        LOCK(pwallet->cs_wallet);
        BOOST_FOREACH(const COutputEntry& r, listReceived)
        {
            if (pwallet->mapAddressBook.count(r.destination))
            {
                map<CTxDestination, CAddressBookData>::const_iterator mi = pwallet->mapAddressBook.find(r.destination);
                if (mi != pwallet->mapAddressBook.end() && (*mi).second.name == strAccount)
                    nReceived += r.amount;
            }
            else if (strAccount.empty())
            {
                nReceived += r.amount;
            }
        }
    }
}

/**
 * Scan the block chain (starting in pindexStart) for transactions
 * from or to us. If fUpdate is true, found transactions that already
 * exist in the wallet will be updated.
 *
 * Returns pointer to the first block in the last contiguous range that was
 * successfully scanned.
 *
 */
CBlockIndex* CWallet::ScanForWalletTransactions(CBlockIndex* pindexStart, bool fUpdate)
{
    CBlockIndex* ret = nullptr;
    int64_t nNow = GetTime();
    const CChainParams& chainParams = Params();

    CBlockIndex* pindex = pindexStart;
    {
        LOCK2(cs_main, cs_wallet);

        // no need to read and scan block, if block was created before
        // our wallet birthday (as adjusted for block time variability)
        while (pindex && nTimeFirstKey && (pindex->GetBlockTime() < (nTimeFirstKey - 7200)))
            pindex = chainActive.Next(pindex);

        ShowProgress(_("Rescanning..."), 0); // show rescan progress in GUI as dialog or on splashscreen, if -rescan on startup
        double dProgressStart = GuessVerificationProgress(chainParams.TxData(), pindex);
        double dProgressTip = GuessVerificationProgress(chainParams.TxData(), chainActive.Tip());
        while (pindex)
        {
            if (pindex->nHeight % 100 == 0 && dProgressTip - dProgressStart > 0.0)
                ShowProgress(_("Rescanning..."), std::max(1, std::min(99, (int)((GuessVerificationProgress(chainParams.TxData(), pindex) - dProgressStart) / (dProgressTip - dProgressStart) * 100))));

            CBlock block;
            if (ReadBlockFromDisk(block, pindex, Params().GetConsensus())) {
                for (size_t posInBlock = 0; posInBlock < block.vtx.size(); ++posInBlock) {
                    if(fRecordInflation){
                        UpdateAssetMap(*block.vtx[posInBlock]);
                        UpdateFreezeHistory(*block.vtx[posInBlock],pindex->nHeight);
                    }
                    AddToWalletIfInvolvingMe(*block.vtx[posInBlock], pindex, posInBlock, fUpdate);
                }
                if (!ret) {
                    ret = pindex;
                }
            } else {
                ret = nullptr;
            }
            pindex = chainActive.Next(pindex);
            if (GetTime() >= nNow + 60) {
                nNow = GetTime();
                LogPrintf("Still rescanning. At block %d. Progress=%f\n", pindex->nHeight, GuessVerificationProgress(chainParams.TxData(), pindex));
            }
        }
        ShowProgress(_("Rescanning..."), 100); // hide progress dialog in GUI
    }
    return ret;
}

void CWallet::ReacceptWalletTransactions()
{
    // If transactions aren't being broadcasted, don't let them into local mempool either
    if (!fBroadcastTransactions)
        return;
    LOCK2(cs_main, cs_wallet);
    std::map<int64_t, CWalletTx*> mapSorted;

    // Sort pending wallet transactions based on their initial wallet insertion order
    BOOST_FOREACH(PAIRTYPE(const uint256, CWalletTx)& item, mapWallet)
    {
        const uint256& wtxid = item.first;
        CWalletTx& wtx = item.second;
        assert(wtx.GetHash() == wtxid);

        int nDepth = wtx.GetDepthInMainChain();

        if (!wtx.IsCoinBase() && (nDepth == 0 && !wtx.isAbandoned())) {
            mapSorted.insert(std::make_pair(wtx.nOrderPos, &wtx));
        }
    }

    // Try to add wallet transactions to memory pool
    BOOST_FOREACH(PAIRTYPE(const int64_t, CWalletTx*)& item, mapSorted)
    {
        CWalletTx& wtx = *(item.second);

        LOCK(mempool.cs);
        CValidationState state;
        wtx.AcceptToMemoryPool(maxTxFee, state);
    }
}

bool CWalletTx::RelayWalletTransaction(CConnman* connman)
{
    assert(pwallet->GetBroadcastTransactions());
    if (!IsCoinBase() && !isAbandoned() && GetDepthInMainChain() == 0)
    {
        CValidationState state;
        /* GetDepthInMainChain already catches known conflicts. */
        if (InMempool() || AcceptToMemoryPool(maxTxFee, state)) {
            LogPrintf("Relaying wtx %s\n", GetHash().ToString());
            if (connman) {
                CInv inv(MSG_TX, GetHash());
                connman->ForEachNode([&inv](CNode* pnode)
                {
                    pnode->PushInventory(inv);
                });
                return true;
            }
        }
    }
    return false;
}

set<uint256> CWalletTx::GetConflicts() const
{
    set<uint256> result;
    if (pwallet != NULL)
    {
        uint256 myHash = GetHash();
        result = pwallet->GetConflicts(myHash);
        result.erase(myHash);
    }
    return result;
}

CAmountMap CWalletTx::GetDebit(const isminefilter& filter) const
{
    if (tx->vin.empty())
        return CAmountMap();

    CAmountMap debit;
    if(filter & ISMINE_SPENDABLE)
    {
        if (fDebitCached)
            debit += nDebitCached;
        else
        {
            nDebitCached = pwallet->GetDebit(*this, ISMINE_SPENDABLE);
            fDebitCached = true;
            debit += nDebitCached;
        }
    }
    if(filter & ISMINE_WATCH_ONLY)
    {
        if(fWatchDebitCached)
            debit += nWatchDebitCached;
        else
        {
            nWatchDebitCached = pwallet->GetDebit(*this, ISMINE_WATCH_ONLY);
            fWatchDebitCached = true;
            debit += nWatchDebitCached;
        }
    }
    return debit;
}

CAmountMap CWalletTx::GetCredit(unsigned int nTxOut, const isminefilter& filter) const
{
    CAmountMap amount;
    if (pwallet->IsMine(tx->vout[nTxOut]) & filter)
        amount[GetOutputAsset(nTxOut)] = GetOutputValueOut(nTxOut);
    // Can be -1 if someone sent us a transaction using a wrong scanning key:
    if (amount[CAsset()] == -1)
        return CAmountMap();
    if (!MoneyRange(amount))
        throw std::runtime_error("CWallet::GetCredit(): value out of range");
    return amount;
}

CAmountMap CWalletTx::GetCredit(const isminefilter& filter) const
{
    // Must wait until coinbase is safely deep enough in the chain before valuing it
    if (IsCoinBase() && GetBlocksToMaturity() > 0)
        return CAmountMap();

    CAmountMap credit;
    if (filter & ISMINE_SPENDABLE)
    {
        // GetBalance can assume transactions in mapWallet won't change
        if (fCreditCached)
            credit += nCreditCached;
        else
        {
            nCreditCached = pwallet->GetCredit(*this, ISMINE_SPENDABLE);
            fCreditCached = true;
            credit += nCreditCached;
        }
    }
    if (filter & ISMINE_WATCH_ONLY)
    {
        if (fWatchCreditCached)
            credit += nWatchCreditCached;
        else
        {
            nWatchCreditCached = pwallet->GetCredit(*this, ISMINE_WATCH_ONLY);
            fWatchCreditCached = true;
            credit += nWatchCreditCached;
        }
    }
    return credit;
}

CAmountMap CWalletTx::GetImmatureCredit(bool fUseCache) const
{
    if (IsCoinBase() && GetBlocksToMaturity() > 0 && IsInMainChain())
    {
        if (fUseCache && fImmatureCreditCached)
            return nImmatureCreditCached;
        nImmatureCreditCached = pwallet->GetCredit(*this, ISMINE_SPENDABLE);
        fImmatureCreditCached = true;
        return nImmatureCreditCached;
    }

    return CAmountMap();
}

CAmountMap CWalletTx::GetAvailableCredit(bool fUseCache) const
{
    if (pwallet == 0)
        return CAmountMap();

    // Must wait until coinbase is safely deep enough in the chain before valuing it
    if (IsCoinBase() && GetBlocksToMaturity() > 0)
        return CAmountMap();

    if (fUseCache && fAvailableCreditCached)
        return nAvailableCreditCached;

    CAmountMap nCredit;
    uint256 hashTx = GetHash();
    for (unsigned int i = 0; i < tx->vout.size(); i++)
    {
        if (!pwallet->IsSpent(hashTx, i))
        {
            nCredit += GetCredit(i, ISMINE_SPENDABLE);
            if (!MoneyRange(nCredit))
                throw std::runtime_error("CWalletTx::GetAvailableCredit() : value out of range");
        }
    }

    nAvailableCreditCached = nCredit;
    fAvailableCreditCached = true;
    return nCredit;
}

CAmountMap CWalletTx::GetImmatureWatchOnlyCredit(const bool& fUseCache) const
{
    if (IsCoinBase() && GetBlocksToMaturity() > 0 && IsInMainChain())
    {
        if (fUseCache && fImmatureWatchCreditCached)
            return nImmatureWatchCreditCached;
        nImmatureWatchCreditCached = pwallet->GetCredit(*this, ISMINE_WATCH_ONLY);
        fImmatureWatchCreditCached = true;
        return nImmatureWatchCreditCached;
    }

    return CAmountMap();
}

CAmountMap CWalletTx::GetAvailableWatchOnlyCredit(const bool& fUseCache) const
{
    if (pwallet == 0)
        return CAmountMap();

    // Must wait until coinbase is safely deep enough in the chain before valuing it
    if (IsCoinBase() && GetBlocksToMaturity() > 0)
        return CAmountMap();

    if (fUseCache && fAvailableWatchCreditCached)
        return nAvailableWatchCreditCached;

    CAmountMap nCredit;
    for (unsigned int i = 0; i < tx->vout.size(); i++)
    {
        if (!pwallet->IsSpent(GetHash(), i))
        {
            nCredit += GetCredit(i, ISMINE_WATCH_ONLY);
            if (!MoneyRange(nCredit))
                throw std::runtime_error("CWalletTx::GetAvailableCredit() : value out of range");
        }
    }

    nAvailableWatchCreditCached = nCredit;
    fAvailableWatchCreditCached = true;
    return nCredit;
}

CAmountMap CWalletTx::GetChange(unsigned int nTxOut) const
{
    CAmountMap amount;
    if (pwallet->IsChange(tx->vout[nTxOut]))
        amount[GetOutputAsset(nTxOut)] = GetOutputValueOut(nTxOut);
    if (!MoneyRange(amount))
        throw std::runtime_error("CWallet::GetChange(): value out of range");
    return amount;
}

CAmountMap CWalletTx::GetChange() const
{
    if (fChangeCached)
        return nChangeCached;
    nChangeCached = pwallet->GetChange(*this);
    fChangeCached = true;
    return nChangeCached;
}

bool CWalletTx::InMempool() const
{
    LOCK(mempool.cs);
    if (mempool.exists(GetHash())) {
        return true;
    }
    return false;
}

bool CWalletTx::IsTrusted() const
{
    // Quick answer in most cases
    if (!CheckFinalTx(*this))
        return false;
    int nDepth = GetDepthInMainChain();
    if (nDepth >= 1)
        return true;
    if (nDepth < 0)
        return false;
    if (!bSpendZeroConfChange || !IsFromMe(ISMINE_ALL)) // using wtx's cached debit
        return false;

    // Don't trust unconfirmed transactions from us unless they are in the mempool.
    if (!InMempool())
        return false;

    // Trusted if all inputs are from us and are in the mempool:
    BOOST_FOREACH(const CTxIn& txin, tx->vin)
    {
        // Transactions not sent by us: not trusted
        const CWalletTx* parent = pwallet->GetWalletTx(txin.prevout.hash);
        if (parent == NULL)
            return false;
        const CTxOut& parentOut = parent->tx->vout[txin.prevout.n];
        if (pwallet->IsMine(parentOut) != ISMINE_SPENDABLE)
            return false;
    }
    return true;
}

bool CWalletTx::IsEquivalentTo(const CWalletTx& _tx) const
{
        CMutableTransaction tx1 = *this->tx;
        CMutableTransaction tx2 = *_tx.tx;
        for (unsigned int i = 0; i < tx1.vin.size(); i++) tx1.vin[i].scriptSig = CScript();
        for (unsigned int i = 0; i < tx2.vin.size(); i++) tx2.vin[i].scriptSig = CScript();
        return CTransaction(tx1) == CTransaction(tx2);
}

void CWalletTx::SetBlindingData(unsigned int mapIndex, CAmount amountIn, CPubKey pubkeyIn, uint256 blindingfactorIn, const CAsset& assetIn, uint256 assetBlindingFactorIn) const
{
    if (mapValue["blindingdata"].size() < (mapIndex + 1) * 138) {
        mapValue["blindingdata"].resize((tx->vout.size() + GetNumIssuances(*tx)) * 138);
    }

    unsigned char* it = (unsigned char*)(&mapValue["blindingdata"][0]) + 138 * mapIndex;

    *it = 1;
    memcpy(&*(it + 1), &amountIn, 8);
    memcpy(&*(it + 9), blindingfactorIn.begin(), 32);
    memcpy(&*(it + 41), assetBlindingFactorIn.begin(), 32);
    memcpy(&*(it + 73), assetIn.begin(), 32);
    if (pubkeyIn.IsValid() && pubkeyIn.size() == 33) {
        memcpy(&*(it + 105), pubkeyIn.begin(), 33);
    } else {
        memset(&*(it + 105), 0, 33);
    }

}

void CWalletTx::GetBlindingData(const unsigned int mapIndex, const std::vector<unsigned char>& vchRangeproof, const CConfidentialValue& confValue, const CConfidentialAsset& confAsset, const CConfidentialNonce nonce, const CScript& scriptPubKey, CAmount* pamountOut, CPubKey* ppubkeyOut, uint256* pblindingfactorOut, CAsset* pAssetOut, uint256* passetBlindingFactorOut) const
{
    // Blinding data is cached in a serialized record mapWallet["blindingdata"].
    // It contains a concatenation byte vectors, 74 bytes per txout or pseudo-input.
    // Each consists of:
    // * 1 byte boolean marker (has the output been computed)?
    // * 8 bytes amount (-1 if unknown)
    // * 32 bytes blinding factor
    // * 32 bytes asset blinding factor
    // * 32 bytes asset
    // * 33 bytes blinding pubkey (ECDH pubkey of the destination)
    // This is really ugly, and should use CDataStream serialization instead.

    if (mapValue["blindingdata"].size() < (mapIndex + 1) * 138) {
        mapValue["blindingdata"].resize((tx->vout.size() + GetNumIssuances(*tx)) * 138);
    }

    unsigned char* it = (unsigned char*)(&mapValue["blindingdata"][0]) + 138 * mapIndex;

    CAmount amount = -1;
    CPubKey pubkey;
    uint256 blindingfactor;
    CAsset asset;
    uint256 assetBlindingFactor;

    if (*it == 1) {
        memcpy(&amount, &*(it + 1), 8);
        memcpy(blindingfactor.begin(), &*(it + 9), 32);
        memcpy(assetBlindingFactor.begin(), &*(it + 41), 32);
        memcpy(asset.begin(), &*(it + 73), 32);
        pubkey.Set(it + 105, it + 138);
    } else {
        pwallet->ComputeBlindingData(confValue, confAsset, nonce, scriptPubKey, vchRangeproof, amount, pubkey, blindingfactor,
            asset, assetBlindingFactor);
        *it = 1;
        memcpy(&*(it + 1), &amount, 8);
        memcpy(&*(it + 9), blindingfactor.begin(), 32);
        memcpy(&*(it + 41), assetBlindingFactor.begin(), 32);
        memcpy(&*(it + 73), asset.begin(), 32);
        if (pubkey.IsValid() && pubkey.size() == 33) {
            memcpy(&*(it + 105), pubkey.begin(), 33);
        } else {
            memset(&*(it + 105), 0, 33);
        }
    }

    if (pamountOut) *pamountOut = amount;
    if (ppubkeyOut) *ppubkeyOut = pubkey;
    if (pblindingfactorOut) *pblindingfactorOut = blindingfactor;
    if (passetBlindingFactorOut) *passetBlindingFactorOut = assetBlindingFactor;
    if (pAssetOut) *pAssetOut = asset;
}

CAmount CWalletTx::GetOutputValueOut(unsigned int nOut) const {
    assert(nOut < tx->vout.size());
    const CTxOut& out = tx->vout[nOut];
    const CTxWitness& wit = tx->wit;
    CAmount ret;
    GetBlindingData(nOut, wit.vtxoutwit.size() <= nOut ? std::vector<unsigned char>() : wit.vtxoutwit[nOut].vchRangeproof, out.nValue, out.nAsset, out.nNonce, out.scriptPubKey, &ret, NULL, NULL, NULL, NULL);
    return ret;
}

uint256 CWalletTx::GetOutputBlindingFactor(unsigned int nOut) const {
    assert(nOut < tx->vout.size());
    const CTxOut& out = tx->vout[nOut];
    const CTxWitness& wit = tx->wit;
    uint256 ret;
    GetBlindingData(nOut, wit.vtxoutwit.size() <= nOut ? std::vector<unsigned char>() : wit.vtxoutwit[nOut].vchRangeproof, out.nValue, out.nAsset, out.nNonce, out.scriptPubKey, NULL, NULL, &ret, NULL, NULL);
    return ret;
}

uint256 CWalletTx::GetOutputAssetBlindingFactor(unsigned int nOut) const {
    assert(nOut < tx->vout.size());
    const CTxOut& out = tx->vout[nOut];
    const CTxWitness& wit = tx->wit;
    uint256 ret;
    GetBlindingData(nOut, wit.vtxoutwit.size() <= nOut ? std::vector<unsigned char>() : wit.vtxoutwit[nOut].vchRangeproof, out.nValue, out.nAsset, out.nNonce, out.scriptPubKey, NULL, NULL, NULL, NULL, &ret);
    return ret;
}

CAsset CWalletTx::GetOutputAsset(unsigned int nOut) const {
    assert(nOut < tx->vout.size());
    const CTxOut& out = tx->vout[nOut];
    const CTxWitness& wit = tx->wit;
    CAsset ret;
    GetBlindingData(nOut, wit.vtxoutwit.size() <= nOut ? std::vector<unsigned char>() : wit.vtxoutwit[nOut].vchRangeproof, out.nValue, out.nAsset, out.nNonce, out.scriptPubKey, NULL, NULL, NULL, &ret, NULL);
    return ret;
}

CPubKey CWalletTx::GetOutputBlindingPubKey(unsigned int nOut) const {
    assert(nOut < tx->vout.size());
    const CTxOut& out = tx->vout[nOut];
    const CTxWitness& wit = tx->wit;
    CPubKey ret;
    GetBlindingData(nOut, wit.vtxoutwit.size() <= nOut ? std::vector<unsigned char>() : wit.vtxoutwit[nOut].vchRangeproof, out.nValue, out.nAsset, out.nNonce, out.scriptPubKey, NULL, &ret, NULL, NULL, NULL);
    return ret;
}

uint256 CWalletTx::GetIssuanceBlindingFactor(unsigned int vinIndex, bool fIssuanceToken) const {
    assert(vinIndex < tx->vin.size());
    CAsset asset;
    const CAssetIssuance& issuance = tx->vin[vinIndex].assetIssuance;
    const CTxWitness& wit = tx->wit;
    if ((issuance.nAmount.IsNull() && !fIssuanceToken) || (issuance.nInflationKeys.IsNull() && fIssuanceToken)) {
        return uint256();
    }
    const std::vector<unsigned char>& rangeproof = wit.vtxinwit.size() <= vinIndex ? std::vector<unsigned char>() : (fIssuanceToken ? wit.vtxinwit[vinIndex].vchInflationKeysRangeproof : wit.vtxinwit[vinIndex].vchIssuanceAmountRangeproof);
    unsigned int mapValueInd = GetPseudoInputOffset(vinIndex, fIssuanceToken)+tx->vout.size();
  if (!issuance.IsReissuance()) {
        uint256 entropy;
        GenerateAssetEntropy(entropy, tx->vin[vinIndex].prevout, issuance.assetEntropy);
        if (fIssuanceToken) {
            CalculateReissuanceToken(asset, entropy, issuance.nInflationKeys.IsCommitment());
        } else {
            CalculateAsset(asset, entropy);
        }
  }
    else {
        if (fIssuanceToken) {
            // Re-issuances don't emit issuance tokens
            return uint256();
        }
        CalculateAsset(asset, issuance.assetEntropy);
    }

    uint256 ret;
    CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(tx->vin[vinIndex].prevout.hash.begin(), tx->vin[vinIndex].prevout.hash.end()) << tx->vin[vinIndex].prevout.n);
    GetBlindingData(mapValueInd, rangeproof, fIssuanceToken ? issuance.nInflationKeys : issuance.nAmount, CConfidentialAsset(asset), CConfidentialNonce(), blindingScript, NULL, NULL, &ret, NULL, NULL);
    return ret;
}

CAmount CWalletTx::GetIssuanceAmount(unsigned int vinIndex, bool fIssuanceToken) const {
    assert(vinIndex < tx->vin.size());
    CAsset asset;
    CAsset token;
    const CAssetIssuance& issuance = tx->vin[vinIndex].assetIssuance;
    const CTxWitness& wit = tx->wit;
    if ((issuance.nAmount.IsNull() && !fIssuanceToken) || (issuance.nInflationKeys.IsNull() && fIssuanceToken)) {
        return 0;
    }
    unsigned int mapValueInd = GetPseudoInputOffset(vinIndex, fIssuanceToken)+tx->vout.size();
    const std::vector<unsigned char>& rangeproof = wit.vtxinwit.size() <= vinIndex ? std::vector<unsigned char>() : (fIssuanceToken ? wit.vtxinwit[vinIndex].vchInflationKeysRangeproof : wit.vtxinwit[vinIndex].vchIssuanceAmountRangeproof);
    if (!issuance.IsReissuance()) {
        uint256 entropy;
        GenerateAssetEntropy(entropy, tx->vin[vinIndex].prevout, issuance.assetEntropy);
        CalculateReissuanceToken(token, entropy, issuance.nAmount.IsCommitment());
        CalculateAsset(asset, entropy);
    }
    else {
        if (fIssuanceToken) {
            // Re-issuances don't emit issuance tokens
            return -1;
        }
        CalculateAsset(asset, issuance.assetEntropy);
    }

    CAmount ret;
    CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(tx->vin[vinIndex].prevout.hash.begin(), tx->vin[vinIndex].prevout.hash.end()) << tx->vin[vinIndex].prevout.n);
    GetBlindingData(mapValueInd, rangeproof, fIssuanceToken ? issuance.nInflationKeys : issuance.nAmount, CConfidentialAsset((fIssuanceToken ? token : asset)), CConfidentialNonce(), blindingScript, &ret, NULL, NULL, NULL, NULL);
    return ret;
}

std::vector<uint256> CWallet::ResendWalletTransactionsBefore(int64_t nTime, CConnman* connman)
{
    std::vector<uint256> result;

    LOCK(cs_wallet);
    // Sort them in chronological order
    multimap<unsigned int, CWalletTx*> mapSorted;
    BOOST_FOREACH(PAIRTYPE(const uint256, CWalletTx)& item, mapWallet)
    {
        CWalletTx& wtx = item.second;
        // Don't rebroadcast if newer than nTime:
        if (wtx.nTimeReceived > nTime)
            continue;
        mapSorted.insert(make_pair(wtx.nTimeReceived, &wtx));
    }
    BOOST_FOREACH(PAIRTYPE(const unsigned int, CWalletTx*)& item, mapSorted)
    {
        CWalletTx& wtx = *item.second;
        if (wtx.RelayWalletTransaction(connman))
            result.push_back(wtx.GetHash());
    }
    return result;
}

void CWallet::ResendWalletTransactions(int64_t nBestBlockTime, CConnman* connman)
{
    // Do this infrequently and randomly to avoid giving away
    // that these are our transactions.
    if (GetTime() < nNextResend || !fBroadcastTransactions)
        return;
    bool fFirst = (nNextResend == 0);
    nNextResend = GetTime() + GetRand(30 * 60);
    if (fFirst)
        return;

    // Only do it if there's been a new block since last time
    if (nBestBlockTime < nLastResend)
        return;
    nLastResend = GetTime();

    // Rebroadcast unconfirmed txes older than 5 minutes before the last
    // block was found:
    std::vector<uint256> relayed = ResendWalletTransactionsBefore(nBestBlockTime-5*60, connman);
    if (!relayed.empty())
        LogPrintf("%s: rebroadcast %u unconfirmed transactions\n", __func__, relayed.size());
}

/** @} */ // end of mapWallet




/** @defgroup Actions
 *
 * @{
 */


CAmountMap CWallet::GetBalance() const
{
    CAmountMap nTotal;
    {
        LOCK2(cs_main, cs_wallet);
        for (map<uint256, CWalletTx>::const_iterator it = mapWallet.begin(); it != mapWallet.end(); ++it)
        {
            const CWalletTx* pcoin = &(*it).second;
            if (pcoin->IsTrusted())
                nTotal += pcoin->GetAvailableCredit();
        }
    }

    return nTotal;
}

CAmountMap CWallet::GetUnconfirmedBalance() const
{
    CAmountMap nTotal;
    {
        LOCK2(cs_main, cs_wallet);
        for (map<uint256, CWalletTx>::const_iterator it = mapWallet.begin(); it != mapWallet.end(); ++it)
        {
            const CWalletTx* pcoin = &(*it).second;
            if (!pcoin->IsTrusted() && pcoin->GetDepthInMainChain() == 0 && pcoin->InMempool())
                nTotal += pcoin->GetAvailableCredit();
        }
    }
    return nTotal;
}

CAmountMap CWallet::GetImmatureBalance() const
{
    CAmountMap nTotal;
    {
        LOCK2(cs_main, cs_wallet);
        for (map<uint256, CWalletTx>::const_iterator it = mapWallet.begin(); it != mapWallet.end(); ++it)
        {
            const CWalletTx* pcoin = &(*it).second;
            nTotal += pcoin->GetImmatureCredit();
        }
    }
    return nTotal;
}

CAmountMap CWallet::GetWatchOnlyBalance() const
{
    CAmountMap nTotal;
    {
        LOCK2(cs_main, cs_wallet);
        for (map<uint256, CWalletTx>::const_iterator it = mapWallet.begin(); it != mapWallet.end(); ++it)
        {
            const CWalletTx* pcoin = &(*it).second;
            if (pcoin->IsTrusted())
                nTotal += pcoin->GetAvailableWatchOnlyCredit();
        }
    }

    return nTotal;
}

CAmountMap CWallet::GetUnconfirmedWatchOnlyBalance() const
{
    CAmountMap nTotal;
    {
        LOCK2(cs_main, cs_wallet);
        for (map<uint256, CWalletTx>::const_iterator it = mapWallet.begin(); it != mapWallet.end(); ++it)
        {
            const CWalletTx* pcoin = &(*it).second;
            if (!pcoin->IsTrusted() && pcoin->GetDepthInMainChain() == 0 && pcoin->InMempool())
                nTotal += pcoin->GetAvailableWatchOnlyCredit();
        }
    }
    return nTotal;
}

CAmountMap CWallet::GetImmatureWatchOnlyBalance() const
{
    CAmountMap nTotal;
    {
        LOCK2(cs_main, cs_wallet);
        for (map<uint256, CWalletTx>::const_iterator it = mapWallet.begin(); it != mapWallet.end(); ++it)
        {
            const CWalletTx* pcoin = &(*it).second;
            nTotal += pcoin->GetImmatureWatchOnlyCredit();
        }
    }
    return nTotal;
}

void CWallet::AvailableCoins(vector<COutput>& vCoins, bool fOnlyConfirmed, const CCoinControl *coinControl, bool fIncludeZeroValue) const
{
    vCoins.clear();

    {
        LOCK2(cs_main, cs_wallet);
        for (map<uint256, CWalletTx>::const_iterator it = mapWallet.begin(); it != mapWallet.end(); ++it)
        {
            const uint256& wtxid = it->first;
            const CWalletTx* pcoin = &(*it).second;

            if (!CheckFinalTx(*pcoin))
                continue;

            if (fOnlyConfirmed && !pcoin->IsTrusted())
                continue;

            if (pcoin->IsCoinBase() && pcoin->GetBlocksToMaturity() > 0)
                continue;

            int nDepth = pcoin->GetDepthInMainChain();
            if (nDepth < 0)
                continue;

            // We should not consider coins which aren't at least in our mempool
            // It's possible for these to be conflicted via ancestors which we may never be able to detect
            if (nDepth == 0 && !pcoin->InMempool())
                continue;

            // We should not consider coins from transactions that are replacing
            // other transactions.
            //
            // Example: There is a transaction A which is replaced by bumpfee
            // transaction B. In this case, we want to prevent creation of
            // a transaction B' which spends an output of B.
            //
            // Reason: If transaction A were initially confirmed, transactions B
            // and B' would no longer be valid, so the user would have to create
            // a new transaction C to replace B'. However, in the case of a
            // one-block reorg, transactions B' and C might BOTH be accepted,
            // when the user only wanted one of them. Specifically, there could
            // be a 1-block reorg away from the chain where transactions A and C
            // were accepted to another chain where B, B', and C were all
            // accepted.
            if (nDepth == 0 && fOnlyConfirmed && pcoin->mapValue.count("replaces_txid")) {
                continue;
            }

            // Similarly, we should not consider coins from transactions that
            // have been replaced. In the example above, we would want to prevent
            // creation of a transaction A' spending an output of A, because if
            // transaction B were initially confirmed, conflicting with A and
            // A', we wouldn't want to the user to create a transaction D
            // intending to replace A', but potentially resulting in a scenario
            // where A, A', and D could all be accepted (instead of just B and
            // D, or just A and A' like the user would want).
            if (nDepth == 0 && fOnlyConfirmed && pcoin->mapValue.count("replaced_by_txid")) {
                continue;
            }

            for (unsigned int i = 0; i < pcoin->tx->vout.size(); i++) {
                isminetype mine = IsMine(pcoin->tx->vout[i]);
                if (!(IsSpent(wtxid, i)) && mine != ISMINE_NO &&
                    !IsLockedCoin((*it).first, i) && (pcoin->GetOutputValueOut(i) > 0 || fIncludeZeroValue) &&
                    (!coinControl || !coinControl->HasSelected() || coinControl->fAllowOtherInputs || coinControl->IsSelected(COutPoint((*it).first, i))))
                        vCoins.push_back(COutput(pcoin, i, nDepth,
                                                 ((mine & ISMINE_SPENDABLE) != ISMINE_NO) ||
                                                  (coinControl && coinControl->fAllowWatchOnly && (mine & ISMINE_WATCH_SOLVABLE) != ISMINE_NO),
                                                 (mine & (ISMINE_SPENDABLE | ISMINE_WATCH_SOLVABLE)) != ISMINE_NO));
            }
        }
    }
}

static void ApproximateBestSubset(vector<pair<CAmount, pair<const CWalletTx*,unsigned int> > >vValue, const CAmount& nTotalLower, const CAmount& nTargetValue,
                                  vector<char>& vfBest, CAmount& nBest, int iterations = 1000)
{
    vector<char> vfIncluded;

    vfBest.assign(vValue.size(), true);
    nBest = nTotalLower;

    FastRandomContext insecure_rand;

    for (int nRep = 0; nRep < iterations && nBest != nTargetValue; nRep++)
    {
        vfIncluded.assign(vValue.size(), false);
        CAmount nTotal = 0;
        bool fReachedTarget = false;
        for (int nPass = 0; nPass < 2 && !fReachedTarget; nPass++)
        {
            for (unsigned int i = 0; i < vValue.size(); i++)
            {
                //The solver here uses a randomized algorithm,
                //the randomness serves no real security purpose but is just
                //needed to prevent degenerate behavior and it is important
                //that the rng is fast. We do not use a constant random sequence,
                //because there may be some privacy improvement by making
                //the selection random.
                if (nPass == 0 ? insecure_rand.rand32()&1 : !vfIncluded[i])
                {
                    nTotal += vValue[i].first;
                    vfIncluded[i] = true;
                    if (nTotal >= nTargetValue)
                    {
                        fReachedTarget = true;
                        if (nTotal < nBest)
                        {
                            nBest = nTotal;
                            vfBest = vfIncluded;
                        }
                        nTotal -= vValue[i].first;
                        vfIncluded[i] = false;
                    }
                }
            }
        }
    }
}

typedef std::pair<CAmount, std::pair<const CWalletTx*,unsigned int> > SelectCoin;

bool CWallet::SelectCoinsMinConf(const CAmountMap& mapTargetValue, const int nConfMine, const int nConfTheirs, const uint64_t nMaxAncestors, vector<COutput> vCoins,
                                 set<pair<const CWalletTx*,unsigned int> >& setCoinsRet, CAmountMap& mapValueRet, const CAsset& feeAsset) const
{
    setCoinsRet.clear();
    mapValueRet = CAmountMap();
    CAmountMap mapTotalLower;
    std::map<CAsset, std::vector<SelectCoin> > mapVValue;

    // List of values less than target
    std::map<CAsset, SelectCoin > mapCoinLowestLarger;
    // For all positive assets
    std::set<CAsset> setAssetsToMatch;
    for(std::map<CAsset, CAmount>::const_iterator it = mapTargetValue.begin(); it != mapTargetValue.end(); it++) {
        if (it->second <= 0)
            continue;
        setAssetsToMatch.insert(it->first);
        mapCoinLowestLarger[it->first] = SelectCoin();
        mapCoinLowestLarger[it->first].first = std::numeric_limits<CAmount>::max();
        mapCoinLowestLarger[it->first].second.first = NULL;
        mapTotalLower[it->first] = 0;
        mapVValue[it->first] = std::vector<SelectCoin>();
    }

    random_shuffle(vCoins.begin(), vCoins.end(), GetRandInt);

    // TODO Remove dust rule, remove need for this
    CAmountMap mapTargetValuePlusMinChange = mapTargetValue;
    mapTargetValuePlusMinChange[feeAsset] += MIN_CHANGE;

    BOOST_FOREACH(const COutput &output, vCoins)
    {
        if (!output.fSpendable)
            continue;

        const CWalletTx *pcoin = output.tx;

        if (output.nDepth < (pcoin->IsFromMe(ISMINE_ALL) ? nConfMine : nConfTheirs))
            continue;

        if (!mempool.TransactionWithinChainLimit(pcoin->GetHash(), nMaxAncestors))
            continue;

        int i = output.i;
        CAmount n = pcoin->GetOutputValueOut(i);
        CAsset asset = pcoin->GetOutputAsset(i);

        if (mapTargetValue.count(asset) && mapTargetValue.at(asset) <= 0)
            continue;

        SelectCoin coin = make_pair(n,make_pair(pcoin, i));

        // We've already exactly matched this asset
        if (setAssetsToMatch.count(asset) == 0) {
            continue;
        }
        else if (n == mapTargetValue.at(asset))
        {
            setCoinsRet.insert(coin.second);
            mapValueRet[asset] += coin.first;
            setAssetsToMatch.erase(asset);
        }
        // No minimum output for non-bitcoin assets
        else if (n < mapTargetValuePlusMinChange.at(asset))
        {
            mapVValue[asset].push_back(coin);
            mapTotalLower[asset] += n;
        }
        else if (n < mapCoinLowestLarger.at(asset).first)
        {
            mapCoinLowestLarger[asset] = coin;
        }
    }

    // Exact match using all coins lower than value
    for (std::set<CAsset>::iterator it = setAssetsToMatch.begin(); it != setAssetsToMatch.end(); ) {
        CAsset asset = *it;
        if (mapTotalLower.at(asset) == mapTargetValue.at(asset))
        {
            for (unsigned int i = 0; i < mapVValue[asset].size(); ++i)
            {
                setCoinsRet.insert(mapVValue[asset][i].second);
                mapValueRet[asset] += mapVValue[asset][i].first;
            }
            it = setAssetsToMatch.erase(it);
        }
        else
            ++it;
    }

    // For any particular asset, if sum of small isn't enough, take smallest larger
    for (std::set<CAsset>::iterator it = setAssetsToMatch.begin(); it != setAssetsToMatch.end(); ) {
        CAsset asset = *it;
        if (mapTotalLower.at(asset) < mapTargetValue.at(asset))
        {
            if (mapCoinLowestLarger.at(asset).second.first == NULL)
                return false;
            setCoinsRet.insert(mapCoinLowestLarger[asset].second);
            mapValueRet[asset] += mapCoinLowestLarger[asset].first;
            it = setAssetsToMatch.erase(it);
        }
        else
            ++it;
    }

    // For the assets we haven't yet solved for, we throw each into the stochastic approx section
    for (std::set<CAsset>::iterator it = setAssetsToMatch.begin(); it != setAssetsToMatch.end(); ) {
        CAsset asset = *it;
        std::vector<SelectCoin> vValue = mapVValue[asset];
        // Solve subset sum by stochastic approximation
        std::sort(vValue.begin(), vValue.end(), CompareValueOnly());
        std::reverse(vValue.begin(), vValue.end());
        vector<char> vfBest;
        CAmount vBest;

        ApproximateBestSubset(vValue, mapTotalLower.at(asset), mapTargetValue.at(asset), vfBest, vBest);
        if (vBest != mapTargetValue.at(asset) && mapTotalLower.at(asset) >= mapTargetValuePlusMinChange.at(asset))
                ApproximateBestSubset(vValue, mapTotalLower.at(asset), mapTargetValuePlusMinChange.at(asset), vfBest, vBest);

        // If we have a bigger coin and (either the stochastic approximation didn't find a good solution,
        //                                   or the next bigger coin is closer), return the bigger coin
        if (mapCoinLowestLarger[asset].second.first &&
                ((vBest != mapTargetValue.at(asset) && vBest < mapTargetValuePlusMinChange.at(asset)) || mapCoinLowestLarger.at(asset).first <= vBest))
        {
                setCoinsRet.insert(mapCoinLowestLarger[asset].second);
                mapValueRet[asset] += mapCoinLowestLarger[asset].first;
        }
        else {
                for (unsigned int i = 0; i < vValue.size(); i++)
                if (vfBest[i])
                {
                        setCoinsRet.insert(vValue[i].second);
                        mapValueRet[asset] += vValue[i].first;
                }

                LogPrint("selectcoins", "SelectCoins() best subset: ");
                for (unsigned int i = 0; i < vValue.size(); i++)
                if (vfBest[i])
                        LogPrint("selectcoins", "%s ", FormatMoney(vValue[i].first));
                LogPrint("selectcoins", "total %s\n", FormatMoney(vBest));
        }
        it = setAssetsToMatch.erase(it);
    }

    assert(setAssetsToMatch.empty());
    return true;
}

bool CWallet::SelectCoins(const vector<COutput>& vAvailableCoins, const CAmountMap& mapTargetValue, set<pair<const CWalletTx*,unsigned int> >& setCoinsRet, CAmountMap& mapValueRet, const CCoinControl* coinControl, const CAsset& feeAsset) const
{
    vector<COutput> vCoins(vAvailableCoins);

    // coin control -> return all selected outputs (we want all selected to go into the transaction for sure)
    if (coinControl && coinControl->HasSelected() && !coinControl->fAllowOtherInputs)
    {
        BOOST_FOREACH(const COutput& out, vCoins)
        {
            if (!out.fSpendable)
                continue;
            mapValueRet[out.tx->GetOutputAsset(out.i)] += out.tx->GetOutputValueOut(out.i);
            setCoinsRet.insert(make_pair(out.tx, out.i));
        }
        return (mapValueRet >= mapTargetValue);
    }

    // calculate value from preset inputs and store them
    set<pair<const CWalletTx*, uint32_t> > setPresetCoins;
    CAmountMap mapValueFromPresetInputs;

    std::vector<COutPoint> vPresetInputs;
    if (coinControl)
        coinControl->ListSelected(vPresetInputs);
    BOOST_FOREACH(const COutPoint& outpoint, vPresetInputs)
    {
        map<uint256, CWalletTx>::const_iterator it = mapWallet.find(outpoint.hash);
        if (it != mapWallet.end())
        {
            const CWalletTx* pcoin = &it->second;
            // Clearly invalid input, fail
            if (pcoin->tx->vout.size() <= outpoint.n)
                return false;

            //Reject non-whitelisted
            if(fRequireWhitelistCheck){
                const CScript& script = pcoin->tx->vout[outpoint.n].scriptPubKey;
                CTxDestination dest;

                if(ExtractDestination(script, dest)){
                    CKeyID keyId = boost::get<CKeyID>(dest);
                    if(!addressWhitelist->is_whitelisted(keyId)) continue;
                }
            }

            mapValueFromPresetInputs[pcoin->GetOutputAsset(outpoint.n)] += pcoin->GetOutputValueOut(outpoint.n);
            setPresetCoins.insert(make_pair(pcoin, outpoint.n));


        } else
            return false; // TODO: Allow non-wallet inputs
    }

    // remove preset inputs from vCoins
    for (vector<COutput>::iterator it = vCoins.begin(); it != vCoins.end() && coinControl && coinControl->HasSelected();)
    {
        if (setPresetCoins.count(make_pair(it->tx, it->i)))
            it = vCoins.erase(it);
        else
            ++it;
    }

    size_t nMaxChainLength = std::min(GetArg("-limitancestorcount", DEFAULT_ANCESTOR_LIMIT), GetArg("-limitdescendantcount", DEFAULT_DESCENDANT_LIMIT));
    bool fRejectLongChains = GetBoolArg("-walletrejectlongchains", DEFAULT_WALLET_REJECT_LONG_CHAINS);
    CAmountMap mapTargetMinusPreset = mapTargetValue;
    mapTargetMinusPreset -= mapValueFromPresetInputs;

    bool res = mapTargetValue <= mapValueFromPresetInputs ||
        SelectCoinsMinConf(mapTargetMinusPreset, 1, 6, 0, vCoins, setCoinsRet, mapValueRet, feeAsset) ||
        SelectCoinsMinConf(mapTargetMinusPreset, 1, 1, 0, vCoins, setCoinsRet, mapValueRet, feeAsset) ||
        (bSpendZeroConfChange && SelectCoinsMinConf(mapTargetMinusPreset, 0, 1, 2, vCoins, setCoinsRet, mapValueRet, feeAsset)) ||
        (bSpendZeroConfChange && SelectCoinsMinConf(mapTargetMinusPreset, 0, 1, std::min((size_t)4, nMaxChainLength/3), vCoins, setCoinsRet, mapValueRet, feeAsset)) ||
        (bSpendZeroConfChange && SelectCoinsMinConf(mapTargetMinusPreset, 0, 1, nMaxChainLength/2, vCoins, setCoinsRet, mapValueRet, feeAsset)) ||
        (bSpendZeroConfChange && SelectCoinsMinConf(mapTargetMinusPreset, 0, 1, nMaxChainLength, vCoins, setCoinsRet, mapValueRet, feeAsset)) ||
        (bSpendZeroConfChange && !fRejectLongChains && SelectCoinsMinConf(mapTargetMinusPreset, 0, 1, std::numeric_limits<uint64_t>::max(), vCoins, setCoinsRet, mapValueRet, feeAsset));

    // because SelectCoinsMinConf clears the setCoinsRet, we now add the possible inputs to the coinset
    setCoinsRet.insert(setPresetCoins.begin(), setPresetCoins.end());

    // add preset inputs to the total value selected
    mapValueRet += mapValueFromPresetInputs;

    return res;
}

bool CWallet::FundTransaction(CMutableTransaction& tx, CAmount& nFeeRet, bool overrideEstimatedFeeRate, const CFeeRate& specificFeeRate, int& nChangePosInOut, std::string& strFailReason, bool includeWatching, bool lockUnspents, const std::set<int>& setSubtractFeeFromOutputs, bool keepReserveKey, const CTxDestination& destChange)
{
    vector<CRecipient> vecSend;
    std::vector<std::vector<CReserveKey>> vChangeKeys;
    std::vector<CReserveKey> vChangeKey;
    // Avoid copying CReserveKeys which causes badness
    vChangeKey.reserve((tx.vin.size()+tx.vout.size())*2);
    std::set<CAsset> setAssets;

    CAsset feeAsset;

    // Turn the txout set into a CRecipient vector
    for (size_t idx = 0; idx < tx.vout.size(); idx++)
    {
        const CTxOut& txOut = tx.vout[idx];
        if (!txOut.nValue.IsExplicit() || !txOut.nAsset.IsExplicit()) {
            strFailReason = _("Pre-funded amounts must be non-blinded");
            return false;
        }
        // Fee outputs should not be added to avoid overpayment of fees
        if (txOut.IsFee()) {
            feeAsset = txOut.nAsset.GetAsset();
            continue;
        }
        CRecipient recipient = {txOut.scriptPubKey, txOut.nValue.GetAmount(), txOut.nAsset.GetAsset(), CPubKey(txOut.nNonce.vchCommitment), false};
        vecSend.push_back(recipient);

        if (setAssets.count(txOut.nAsset.GetAsset()) == 0) {
            vChangeKey.push_back(CReserveKey(this));
            setAssets.insert(txOut.nAsset.GetAsset());
        }
    }

    // Also add reserve keys for inputs, since those could create more change
    // Any excess will never be reserved, so this should be safe.
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        vChangeKey.push_back(CReserveKey(this));
    }

    // Always add policyAsset, as fees via policyAsset may create change
    if (setAssets.count(policyAsset) == 0) {
        vChangeKey.push_back(CReserveKey(this));
    }
    vChangeKeys.push_back(vChangeKey);

    CCoinControl coinControl;
    coinControl.destChange = destChange;
    coinControl.fAllowOtherInputs = true;
    coinControl.fAllowWatchOnly = includeWatching;
    coinControl.fOverrideFeeRate = overrideEstimatedFeeRate;
    coinControl.nFeeRate = specificFeeRate;

    BOOST_FOREACH(const CTxIn& txin, tx.vin)
        coinControl.Select(txin.prevout);

    CWalletTx wtx;

    std::vector<CWalletTx> createResult = CreateTransaction(vecSend, wtx, vChangeKeys, nFeeRet, nChangePosInOut, strFailReason, &coinControl, false, NULL, true, NULL, NULL, NULL, feeAsset, true);

    if (!(createResult.size() > 0))
        return false;

    // Wipe outputs and output witness and re-add one by one
    tx.vout.clear();
    tx.wit.vtxoutwit.clear();
    for (unsigned int i = 0; i < wtx.tx->vout.size(); i++) {
        const CTxOut& out = wtx.tx->vout[i];
        tx.vout.push_back(out);
        if (wtx.tx->wit.vtxoutwit.size() <= i) {
            continue;
        }
        // We want to re-add previously existing outwitnesses
        // even though we don't create any new ones
        const CTxOutWitness& outwit = wtx.tx->wit.vtxoutwit[i];
        tx.wit.vtxoutwit.push_back(outwit);
    }

    // Add new txins (keeping original txin scriptSig/order)
    BOOST_FOREACH(const CTxIn& txin, wtx.tx->vin)
    {
        if (!coinControl.IsSelected(txin.prevout))
        {
            tx.vin.push_back(txin);

            if (lockUnspents)
            {
              LOCK2(cs_main, cs_wallet);
              LockCoin(txin.prevout);
            }
        }
    }

    // optionally keep the change output key
    if (keepReserveKey) {
        for (auto& changekey : vChangeKeys[0]) {
            changekey.KeepKey();
        }
    }
    return true;
}

std::vector<CWalletTx> CWallet::CreateTransaction(vector<CRecipient>& vecSend, CWalletTx& wtxNew,
    std::vector<std::vector<CReserveKey>>& vChangeKeys, CAmount& nFeeRet, int& nChangePosInOut,
    std::string& strFailReason, const CCoinControl* coinControl, bool sign, std::vector<CAmount> *outAmounts,
    bool fBlindIssuances, const uint256* issuanceEntropy, const CAsset* reissuanceAsset,
    const CAsset* reissuanceToken, CAsset feeAsset, bool fIgnoreBlindFail, bool fSplitTransactions,
    std::vector<COutput> vInputPool, bool fFindFeeAsset, std::map<CAsset, std::vector<COutput>>* mAvailableInputs)
{
    // original unchanged recipient vector
    const vector<CRecipient> vecSendOriginal = vecSend;

    // TODO re-enable to support multiple assets in a logical fashion, since the number of possible
    // change positions are number of assets being spent.
    if (nChangePosInOut != -1) {
        strFailReason = _("change position argument has been disabled");
        return std::vector<CWalletTx>();
    }

    CAmountMap mapValue;
    int nChangePosRequest = nChangePosInOut;
    unsigned int nSubtractFeeFromAmount = 0;
    for (const auto& recipient : vecSend)
    {
        // Skip over issuance outputs, no need to select those coins
        if (recipient.asset == CAsset(uint256S("1")) || recipient.asset == CAsset(uint256S("2"))) {
            // In issuance/reissuance cases pay fees in policyAsset
            feeAsset = policyAsset;
            continue;
        }

        // TODO - should also do this for the case where bytes are appended to OP_RETURN?
        // Just like issuance/re-issuance, when destroying assets pay policyAsset fees
        if (recipient.scriptPubKey == CScript(OP_RETURN) ||
            recipient.scriptPubKey == CScript(OP_REGISTERADDRESS) ||
            recipient.scriptPubKey == CScript(OP_DEREGISTERADDRESS))
            feeAsset =  policyAsset;

        if (mapValue[recipient.asset] < 0 || recipient.nAmount < 0 || recipient.asset.IsNull())
        {
            strFailReason = _("Transaction amounts must not be negative");
            return std::vector<CWalletTx>();
        }
        mapValue[recipient.asset] += recipient.nAmount;

        if (recipient.fSubtractFeeFromAmount)
        {
            // When subtracting fee from amount choose the first recipient's asset
            // as the fee asset. Since only one asset fee is allowed there should
            // not be more than one recipient to subtract fees from but there is
            // a check later on that raises an exception if something it happens
            if (feeAsset.IsNull() && nSubtractFeeFromAmount == 0)
            {
                feeAsset = recipient.asset;
            }
            nSubtractFeeFromAmount++;
        }
    }

    if (vecSend.empty())
    {
        strFailReason = _("Transaction must have at least one recipient");
        return std::vector<CWalletTx>();
    }

    // If the asset fee is still not set it means that there is no issuance/reissuance
    // and that fees are subtracted from the senders wallet not from a recipient. The
    // first asset is chosen. This only applies in the sendmany case, as in the when
    // using sendtoaddress a single asset is send and fees are received from it
    if (feeAsset.IsNull())
    {
        CAsset newFeeAsset = vecSend[0].asset;
        if (vecSend.size() > 1) {
            CAmountMap balanceMap;
            if (vInputPool.size() > 0) {
                for (auto const& out: vInputPool) {
                    balanceMap[out.tx->GetOutputAsset(out.i)] += out.tx->GetOutputValueOut(out.i);
                }
            } else {
                balanceMap = pwalletMain->GetBalance();
            }
            int newFeeRecipient = 0;
            for (unsigned int i = 1; i < vecSend.size(); ++i) {
                if (balanceMap[vecSend[i].asset] > balanceMap[newFeeAsset]) {
                    newFeeAsset = vecSend[i].asset;
                    newFeeRecipient = i;
                }
            }

            // I don't understand the purpose of this
            // maybe in case a recipient is dust, which only the last can be?
            // maybe SendAnyMoney should handle that
            CRecipient lastRecipient = vecSend.back();
            if (lastRecipient.asset != newFeeAsset) {
                CAmount lastBalance = balanceMap[lastRecipient.asset];
                CAmount usedLastBalance = mapValue[lastRecipient.asset];
                CAmount unusedLastBalance = lastBalance - usedLastBalance;

                mapValue[lastRecipient.asset] = lastBalance;
                mapValue[newFeeAsset] -= unusedLastBalance;

                vecSend[newFeeRecipient].nAmount = mapValue[newFeeAsset];
                vecSend[vecSend.size() - 1].nAmount = mapValue[lastRecipient.asset];

                if (!PreventDustForNewOutput(mapValue, vecSend, newFeeRecipient)) {
                    strFailReason = _("Output with the same asset as the fee could not find another asset which could be deducted from to make it not dust.");
                    return std::vector<CWalletTx>();
                }
            }
        }
        feeAsset = newFeeAsset;
    }

    wtxNew.fTimeReceivedIsTxTime = true;
    wtxNew.BindWallet(this);
    CMutableTransaction txNew;

    // Discourage fee sniping.
    //
    // For a large miner the value of the transactions in the best block and
    // the mempool can exceed the cost of deliberately attempting to mine two
    // blocks to orphan the current best block. By setting nLockTime such that
    // only the next block can include the transaction, we discourage this
    // practice as the height restricted and limited blocksize gives miners
    // considering fee sniping fewer options for pulling off this attack.
    //
    // A simple way to think about this is from the wallet's point of view we
    // always want the blockchain to move forward. By setting nLockTime this
    // way we're basically making the statement that we only want this
    // transaction to appear in the next block; we don't want to potentially
    // encourage reorgs by allowing transactions to appear at lower heights
    // than the next block in forks of the best chain.
    //
    // Of course, the subsidy is high enough, and transaction volume low
    // enough, that fee sniping isn't a problem yet, but by implementing a fix
    // now we ensure code won't be written that makes assumptions about
    // nLockTime that preclude a fix later.
    txNew.nLockTime = chainActive.Height();

    // Secondly occasionally randomly pick a nLockTime even further back, so
    // that transactions that are delayed after signing for whatever reason,
    // e.g. high-latency mix networks and some CoinJoin implementations, have
    // better privacy.
    if (GetRandInt(10) == 0)
        txNew.nLockTime = std::max(0, (int)txNew.nLockTime - GetRandInt(100));

    assert(txNew.nLockTime <= (unsigned int)chainActive.Height());
    assert(txNew.nLockTime < LOCKTIME_THRESHOLD);

    {
        set<pair<const CWalletTx*,unsigned int> > setCoins;
        // We need to store an unblinded and unsigned version of the transaction
        // in case of !sign
        CMutableTransaction txUnblindedAndUnsigned;
        // Store amounts for storage in mapValue
        std::vector<CAmount> vAmounts;

        std::vector<uint256> input_blinds;
        std::vector<uint256> input_asset_blinds;
        std::vector<CAsset> input_assets;
        std::vector<CAmount> input_amounts;
        std::vector<uint256> output_blinds;
        std::vector<CPubKey> output_pubkeys;
        std::vector<uint256> output_asset_blinds;
        std::vector<CAsset> output_assets;

        std::vector<COutput> vAvailableCoins;
        LOCK2(cs_main, cs_wallet);
        {
            if (vInputPool.size() > 0)
                vAvailableCoins = vInputPool;
            else
                AvailableCoins(vAvailableCoins, true, coinControl);
    	    nFeeRet = 1;
            if (IsPolicy(feeAsset))
                nFeeRet = 0;
            // Start with tiny non-zero or zero fee for issuance entropy and loop until there is enough fee
            while (true)
            {
                nChangePosInOut = nChangePosRequest;
                output_pubkeys.clear();
                int numToBlind = 0;
                int changeToBlind = 0;
                int numInputsBlinded = 0;
                // Needed in case of one blinded output that is change and no blind inputs
                int onlyChangePos = -1;
                // Only used to strip blinding if its the only blind output in certain situations
                int onlyRecipientBlindIndex = -1;

                vAmounts.clear();

                txNew.vin.clear();
                txNew.vout.clear();
                txNew.wit.SetNull();
                wtxNew.fFromMe = true;
                bool fFirst = true;

                CAmountMap mapValueToSelect = mapValue;
                if (nSubtractFeeFromAmount == 0)
                    mapValueToSelect[feeAsset] += nFeeRet;
                double dPriority = 0;
                // vouts to the payees
                for (const auto& recipient : vecSend)
                {
                    CTxOut txout(recipient.asset, recipient.nAmount, recipient.scriptPubKey);
                    txout.nNonce.vchCommitment = std::vector<unsigned char>(recipient.confidentiality_key.begin(), recipient.confidentiality_key.end());

                    if (recipient.fSubtractFeeFromAmount)
                    {
                        if (recipient.asset != feeAsset) {
                            strFailReason = strprintf(_("Wallet does not support more than one type of fee at a time, therefore can not subtract fee from address amount, which is of a different asset id. fee asset: %s recipient asset: %s"), feeAsset.GetHex(), recipient.asset.GetHex());
                            return std::vector<CWalletTx>();
                        }
                        txout.nValue = recipient.nAmount - (nFeeRet / nSubtractFeeFromAmount); // Subtract fee equally from each selected recipient

                        if (fFirst) // first receiver pays the remainder not divisible by output count
                        {
                            fFirst = false;
                            txout.nValue = recipient.nAmount - (nFeeRet / nSubtractFeeFromAmount) - (nFeeRet % nSubtractFeeFromAmount);
                        }
                    }

                    if (recipient.asset == feeAsset && txout.IsDust(::minRelayTxFee))
                    {
                        if (recipient.fSubtractFeeFromAmount && nFeeRet > 0)
                        {
                            if (txout.nValue.GetAmount() < 0)
                                strFailReason = _("The transaction amount is too small to pay the fee");
                            else
                                strFailReason = _("The transaction amount is too small to send after the fee has been deducted");
                        } else {
                            strFailReason = _("Transaction amount too small");
                        }
                        return std::vector<CWalletTx>();
                    }
                    txNew.vout.push_back(txout);
                    output_pubkeys.push_back(recipient.confidentiality_key);
                    if (recipient.confidentiality_key.IsFullyValid()) {
                        numToBlind++;
                        onlyRecipientBlindIndex = txNew.vout.size()-1;
                    }
                }

                // Choose coins to use
                CAmountMap mapValueIn;
                setCoins.clear();
                if (!SelectCoins(vAvailableCoins, mapValueToSelect, setCoins, mapValueIn, coinControl, feeAsset))
                {
                    // Attempt to seek other assets to cover the fee
                    // Edge case for sendanytoaddress
                    if (fFindFeeAsset && nSubtractFeeFromAmount == 0) {
                        std::set<CAsset> balanceSet;
                        for (const auto& itRecipients : vecSend) {
                            balanceSet.insert(itRecipients.asset);
                        }
                        CAmount amountHave = 0;
                        CAmountMap validAmounts;
                        if (vInputPool.size() > 0) {
                            for (const auto& receivedCoin : vAvailableCoins) {
                                amountHave += receivedCoin.tx->GetOutputValueOut(receivedCoin.i);
                            }
                        } else {
                            for (const auto& out : vAvailableCoins) {
                                if (!out.fSpendable)
                                    continue;
                                if (balanceSet.find(out.tx->GetOutputAsset(out.i)) != balanceSet.end())
                                    amountHave += out.tx->GetOutputValueOut(out.i);
                                else
                                    validAmounts[out.tx->GetOutputAsset(out.i)] += out.tx->GetOutputValueOut(out.i);
                            }
                        }
                        CAmount amountNeeded = 0;
                        for (const auto& itNeeded : mapValueToSelect) {
                            amountNeeded += itNeeded.second;
                        }
                        CAmount amountMissing = amountNeeded - amountHave;
                        if (amountMissing > 0) {
                            CAmountMap balanceMap = pwalletMain->GetBalance();
                            // Fee in send any is based on the largest balance.
                            // If its bigger than the largest balance then this transaction is invalid.
                            if (balanceMap[feeAsset] < nFeeRet) {
                                strFailReason = _("Required fee is larger than the owned non-policy asset with the biggest balance.");
                                return std::vector<CWalletTx>();
                            }
                            bool alternativeFound = false;
                            if (mAvailableInputs && mAvailableInputs->size() > 0) {
                                CAmountMap tempAvailableBalances = GetBalanceFromOutputs(*mAvailableInputs);
                                for (const auto& freeBalances : tempAvailableBalances) {
                                    if (freeBalances.second >= amountMissing) {
                                        std::vector<COutput>* extraAvailableCoins = new std::vector<COutput>();
                                        if (DistributeFeeToNewBalance(mapValue, feeAsset, vecSend, vChangeKeys[0], freeBalances.first, amountMissing, extraAvailableCoins, mAvailableInputs)) {
                                            vAvailableCoins.insert(vAvailableCoins.end(), (*extraAvailableCoins).begin(), (*extraAvailableCoins).end());
                                            alternativeFound = true;
                                            break;
                                        } else {
                                            strFailReason = _("Output with the same asset as the fee could not find another asset which could be deducted from to make it not dust in split transactions.");
                                            return std::vector<CWalletTx>();
                                        }
                                    }
                                }
                            } else {
                                for (const auto& it : validAmounts) {
                                    if (!IsPolicy(it.first)) {
                                        CAmount outputValue = it.second;
                                        if (outputValue >= amountMissing) {
                                            if (DistributeFeeToNewBalance(mapValue, feeAsset, vecSend, vChangeKeys[0], it.first, outputValue)) {
                                                alternativeFound = true;
                                                break;
                                            } else {
                                                strFailReason = _("Output with the same asset as the fee could not find another asset which could be deducted from to make it not dust.");
                                                return std::vector<CWalletTx>();
                                            }
                                        }
                                    }
                                }
                            }
                            if (!alternativeFound) {
                                strFailReason = _("Could not find another asset with sufficient balance to cover the fees. ");
                                return std::vector<CWalletTx>();
                            }
                            vChangeKeys[0].emplace_back(pwalletMain);
                            continue;
                        } else {
                            strFailReason = _("Selecting coins error. Amount needed was not larger than the amount owned.");
                            return std::vector<CWalletTx>();
                        }
                    } else {
                        strFailReason = _("Insufficient funds");
                        return std::vector<CWalletTx>();
                    }
                }
                BOOST_FOREACH(PAIRTYPE(const CWalletTx*, unsigned int) pcoin, setCoins)
                {
                    CAmount nCredit = pcoin.first->GetOutputValueOut(pcoin.second);
                    //The coin age after the next block (depth+1) is used instead of the current,
                    //reflecting an assumption the user would accept a bit more delay for
                    //a chance at a free transaction.
                    //But mempool inputs might still be in the mempool, so their age stays 0
                    int age = pcoin.first->GetDepthInMainChain();
                    assert(age >= 0);
                    if (age != 0)
                        age += 1;
                    dPriority += (double)nCredit * age;
                }

                const CAmountMap mapChange = mapValueIn - mapValueToSelect;
                assert(!hasNegativeValue(mapChange));
                unsigned int changeCounter = 0;
                for(std::map<CAsset, CAmount>::const_iterator it = mapChange.begin(); it != mapChange.end(); ++it) {
                    if (it->second > 0)
                    {
                        // Fill a vout to ourself
                        // TODO: pass in scriptChange instead of reservekey so
                        // change transaction isn't always pay-to-bitcoin-address
                        CScript scriptChange;

                        // coin control: send change to custom address
                        if (coinControl && !((coinControl->destChange).which() == ((CTxDestination)CNoDestination()).which()))
                            scriptChange = GetScriptForDestination(coinControl->destChange);

                        // no coin control: send change to newly generated address
                        else
                        {
                            // Note: We use a new key here to keep it from being obvious which side is the change.
                            //  The drawback is that by not reusing a previous key, the change may be lost if a
                            //  backup is restored, if the backup doesn't have the new private key for the change.
                            //  If we reused the old key, it would be possible to add code to look for and
                            //  rediscover unknown transactions that were written with keys of ours to recover
                            //  post-backup change.

                            // Reserve a new key pair from key pool
                            CPubKey vchPubKey;
                            bool ret;
                            ret = vChangeKeys[0][changeCounter].GetReservedKey(vchPubKey);
                            if (!ret)
                            {
                                strFailReason = _("Keypool ran out, please call keypoolrefill first");
                                return std::vector<CWalletTx>();
                            }

                                scriptChange = GetScriptForDestination(vchPubKey.GetID());
                        }

                        CTxOut newTxOut(it->first, it->second, scriptChange);

                        // We do not move dust-change to fees, because the sender would end up paying more than requested.
                        // This would be against the purpose of the all-inclusive feature.
                        // So instead we raise the change and deduct from the recipient.
                        if (nSubtractFeeFromAmount > 0 && newTxOut.IsDust(::minRelayTxFee) && it->first == feeAsset)
                        {
                            CAmount nDust = newTxOut.GetDustThreshold(::minRelayTxFee) - newTxOut.nValue.GetAmount();
                            newTxOut.nValue = newTxOut.nValue.GetAmount() + nDust; // raise change until no more dust
                            for (unsigned int i = 0; i < vecSend.size(); i++) // subtract from first recipient
                            {
                                if (vecSend[i].fSubtractFeeFromAmount)
                                {
                                    txNew.vout[i].nValue = txNew.vout[i].nValue.GetAmount() - nDust;
                                    if (txNew.vout[i].IsDust(dustRelayFee))
                                    {
                                        strFailReason = _("The transaction amount is too small to send after the fee has been deducted");
                                        return std::vector<CWalletTx>();
                                    }
                                    break;
                                }
                            }
                        }

                        // Never create dust outputs; if we would, just
                        // add the dust to the fee.
                        if (newTxOut.IsDust(dustRelayFee) && it->first == feeAsset)
                        {
                            nChangePosInOut = -1;
                            nFeeRet += it->second;
                            vChangeKeys[0][changeCounter].ReturnKey();
                        }
                        else
                        {
                            if (nChangePosInOut == -1)
                            {
                                // Insert change txn at random position:
                                nChangePosInOut = GetRandInt(txNew.vout.size()+1);
                            }
                            else if ((unsigned int)nChangePosInOut > txNew.vout.size())
                            {
                                strFailReason = _("Change index out of range");
                                return std::vector<CWalletTx>();
                            }

                            vector<CTxOut>::iterator position = txNew.vout.begin()+nChangePosInOut;
                            CPubKey pubkey = !GetDisableCt() ? GetBlindingPubKey(scriptChange) : CPubKey();
                            newTxOut.nNonce.vchCommitment = std::vector<unsigned char>(pubkey.begin(), pubkey.end());
                            txNew.vout.insert(position, newTxOut);
                            output_pubkeys.insert(output_pubkeys.begin() + nChangePosInOut, pubkey);
                            if (pubkey.IsFullyValid()) {
                                numToBlind++;
                                changeToBlind++;
                            }
                            onlyChangePos = nChangePosInOut;
                            // reset nChangePosInOut for next asset
                            nChangePosInOut = -1;
                        }
                    }
                    else {
                        vChangeKeys[0][changeCounter].ReturnKey();
                    }
                    changeCounter++;
                }

                // Add fee output
                if (nFeeRet > 0) {
                    CTxOut fee(feeAsset, nFeeRet, CScript());
                    assert(fee.IsFee());
                    txNew.vout.push_back(fee);
                    output_pubkeys.push_back(CPubKey());
                }

                // Set token input if reissuing
                int reissuanceIndex = -1;
                uint256 tokenBlinding;

                // Fill vin
                //
                // Note how the sequence number is set to non-maxint so that
                // the nLockTime set above actually works.
                for (const auto& coin : setCoins) {
                    txNew.vin.push_back(CTxIn(coin.first->GetHash(),coin.second,CScript(), std::numeric_limits<unsigned int>::max() - 1));
                    if (reissuanceToken &&
                        coin.first->GetOutputAsset(coin.second) == *reissuanceToken) {
                        reissuanceIndex = txNew.vin.size()-1;
                        tokenBlinding = coin.first->GetOutputAssetBlindingFactor(coin.second);

                        if (tokenBlinding.IsNull()) // issuance was unblinded
                        {
                            tokenBlinding = CAssetIssuance::UNBLINDED_REISSUANCE_NONCE;
                        }
                    }
                }


                // Construct issuances if they exist
                std::vector<CKey> vassetKeys;
                std::vector<CKey> vtokenKeys;
                assert(txNew.vin.size() > 0);
                int assetIndex = -1;
                int tokenIndex = -1;
                for (unsigned int i = 0; i < txNew.vout.size(); i++) {
                    if (txNew.vout[i].nAsset.IsExplicit() && txNew.vout[i].nAsset.GetAsset()  == CAsset(uint256S("1"))) {
                        assetIndex = i;
                    } else if (txNew.vout[i].nAsset.IsExplicit() && txNew.vout[i].nAsset.GetAsset() == CAsset(uint256S("2"))) {
                        tokenIndex = i;
                    }
                }
                // Initial issuance only for now, always uses vin[0]
                if ((!reissuanceAsset || reissuanceAsset->IsNull()) && (!reissuanceToken || reissuanceToken->IsNull()) && (assetIndex != -1 || tokenIndex != -1)) {
                    uint256 entropy;
                    CAsset asset;
                    CAsset token;
                    // TODO take optional contract hash
                    GenerateAssetEntropy(entropy, txNew.vin[0].prevout, uint256());
                    CalculateAsset(asset, entropy);
                    CalculateReissuanceToken(token, entropy, fBlindIssuances);
                    CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(txNew.vin[0].prevout.hash.begin(), txNew.vin[0].prevout.hash.end()) << txNew.vin[0].prevout.n);
                    // We're making asset outputs, fill out asset type and issuance input
                    if (assetIndex != -1) {
                        txNew.vin[0].assetIssuance.nAmount = txNew.vout[assetIndex].nValue;

                        txNew.vout[assetIndex].nAsset = asset;
                        if (fBlindIssuances) {
                            vassetKeys.push_back(GetBlindingKey(&blindingScript));
                            numToBlind++;
                        }
                    }
                    // We're making reissuance token outputs
                    if (tokenIndex != -1) {
                        txNew.vin[0].assetIssuance.nInflationKeys = txNew.vout[tokenIndex].nValue;
                        txNew.vout[tokenIndex].nAsset = token;
                        if (fBlindIssuances) {
                            vtokenKeys.push_back(GetBlindingKey(&blindingScript));
                            numToBlind++;

                            // If we're blinding a token issuance and no assets, we must make
                            // the asset issuance a blinded commitment to 0
                            if (assetIndex == -1) {
                                txNew.vin[0].assetIssuance.nAmount = 0;
                                vassetKeys.push_back(GetBlindingKey(&blindingScript));
                                numToBlind++;
                            }
                        }
                    }
                // Asset being reissued with explicitly named asset/token
                } else if (assetIndex != -1) {
                    assert(reissuanceIndex != -1);
                    assert(reissuanceAsset);
                    assert(issuanceEntropy);
                    // Fill in output with issuance
                    txNew.vout[assetIndex].nAsset = *reissuanceAsset;

                    // Fill in issuance
                    // Blinding revealing underlying asset
                    txNew.vin[reissuanceIndex].assetIssuance.assetBlindingNonce = tokenBlinding;
                    txNew.vin[reissuanceIndex].assetIssuance.assetEntropy = *issuanceEntropy;
                    txNew.vin[reissuanceIndex].assetIssuance.nAmount = txNew.vout[assetIndex].nValue;

                    // If blinded token derivation, blind the issuance
                    CAsset tempToken;
                    CalculateReissuanceToken(tempToken, *issuanceEntropy, true);
                    if (tempToken == *reissuanceToken) {
                        CScript blindingScript(CScript() << OP_RETURN << std::vector<unsigned char>(txNew.vin[reissuanceIndex].prevout.hash.begin(), txNew.vin[reissuanceIndex].prevout.hash.end()) << txNew.vin[reissuanceIndex].prevout.n);
                        vassetKeys.resize(reissuanceIndex);
                        vassetKeys.push_back(GetBlindingKey(&blindingScript));
                        numToBlind++;
                    }
                }

                LogPrintf("Created transaction (before blinding): %s", CTransaction(txNew).ToString());

                // Create blinded outputs
                input_blinds.clear();
                input_asset_blinds.clear();
                input_assets.clear();
                output_blinds.clear();
                input_amounts.clear();
                output_asset_blinds.clear();
                output_assets.clear();
                BOOST_FOREACH(const PAIRTYPE(const CWalletTx*,unsigned int)& coin, setCoins) {
                    uint256 blind = coin.first->GetOutputBlindingFactor(coin.second);
                    input_blinds.push_back(blind);
                    uint256 asset_blind = coin.first->GetOutputAssetBlindingFactor(coin.second);
                    input_asset_blinds.push_back(asset_blind);
                    CAsset asset = coin.first->GetOutputAsset(coin.second);
                    input_assets.push_back(asset);
                    CAmount amount = coin.first->GetOutputValueOut(coin.second);
                    input_amounts.push_back(amount);
                    if (coin.first->tx->vout[coin.second].nValue.IsCommitment() || coin.first->tx->vout[coin.second].nAsset.IsCommitment()) {
                        numInputsBlinded++;
                    }
                }
                if(outAmounts)
                    outAmounts->clear();
                for (size_t nOut = 0; nOut < txNew.vout.size(); nOut++) {
                    output_blinds.push_back(uint256());
                    output_asset_blinds.push_back(uint256());
                    if (outAmounts)
                        outAmounts->push_back(txNew.vout[nOut].nValue.GetAmount());
                    vAmounts.push_back(txNew.vout[nOut].nValue.GetAmount());
                    output_assets.push_back(txNew.vout[nOut].nAsset.GetAsset());
                }

                // There are a few edge-cases of blinding we need to take care of
                //
                // First, if there are blinded inputs but not outputs to blind
                // We need this to go through, even though no privacy is gained.
                if (numInputsBlinded > 0 &&  numToBlind == 0) {
                    // We need to make sure to dupe an asset that is in input set
                    // TODO Have blinding do some extremely minimal rangeproof
                    CTxOut newTxOut(output_assets.back(), 0, CScript() << OP_RETURN);
                    txNew.vout.push_back(newTxOut);
                    output_pubkeys.push_back(GetBlindingPubKey(newTxOut.scriptPubKey));
                    output_blinds.push_back(uint256());
                    output_asset_blinds.push_back(uint256());
                    output_assets.push_back(output_assets.back());
                    vAmounts.push_back(0);
                    numToBlind++;

                    // No blinded inputs, but 1 blinded output
                } else if (numInputsBlinded == 0 && numToBlind == 1) {
                    if (changeToBlind == 1) {
                        // Only 1 blinded change, unblinded the change
                        // TODO Split up change instead if possible
                        if (fIgnoreBlindFail) {
                            numToBlind--;
                            changeToBlind--;
                            txNew.vout[onlyChangePos].nNonce.SetNull();
                            output_pubkeys[onlyChangePos] = CPubKey();
                            output_blinds[onlyChangePos] = uint256();
                            output_asset_blinds[onlyChangePos] = uint256();
                        } else {
                            strFailReason = _("Change output could not be blinded as there are no blinded inputs and no other blinded outputs.");
                            return std::vector<CWalletTx>();
                        }
                    } else {
                        // 1 blinded destination
                        // TODO Attempt to get a blinded input, OR add unblinded coin to make blinded change
                        assert(onlyRecipientBlindIndex != -1);
                        if (fIgnoreBlindFail) {
                            numToBlind--;
                            txNew.vout[onlyRecipientBlindIndex].nNonce.SetNull();
                            output_pubkeys[onlyRecipientBlindIndex] = CPubKey();
                            output_blinds[onlyRecipientBlindIndex] = uint256();
                            output_asset_blinds[onlyRecipientBlindIndex] = uint256();
                        } else {
                            strFailReason = _("Transaction output could not be blinded as there are no blinded inputs and no other blinded outputs.");
                            return std::vector<CWalletTx>();
                        }
                    }
                }
                // All other combinations should work.

                // Keep a backup of transaction in case re-blinding necessary
                txUnblindedAndUnsigned = txNew;
                int ret = BlindTransaction(input_blinds, input_asset_blinds, input_assets, input_amounts, output_blinds, output_asset_blinds,  output_pubkeys, vassetKeys, vtokenKeys, txNew);
                assert(ret != -1);
                if (ret != numToBlind) {
                    strFailReason = _("Unable to blind the transaction properly. This should not happen.");
                    return std::vector<CWalletTx>();
                }

                // Fill in dummy signatures for fee calculation.
                if (!DummySignTx(txNew, setCoins)) {
                    strFailReason = _("Signing transaction failed");
                    return std::vector<CWalletTx>();
                }

                unsigned int nBytes = GetVirtualTransactionSize(txNew);

                CTransaction txNewConst(txNew);
                dPriority = txNewConst.ComputePriority(dPriority, nBytes);

                assert(vAmounts.size() == output_pubkeys.size());
                assert(output_pubkeys.size() == output_blinds.size());
                assert(output_blinds.size() == output_asset_blinds.size());
                assert(output_asset_blinds.size() == output_assets.size());

                // Remove scriptSigs to eliminate the fee calculation dummy signatures
                for (auto& vin : txNew.vin) {
                    vin.scriptSig = CScript();
                }

                // Remove blinding as well if we're not actually signing
                if (!sign) {
                    txNew = txUnblindedAndUnsigned;
                }

                // Allow to override the default confirmation target over the CoinControl instance
                int currentConfirmationTarget = nTxConfirmTarget;
                if (coinControl && coinControl->nConfirmTarget > 0)
                    currentConfirmationTarget = coinControl->nConfirmTarget;

                // Can we complete this as a free transaction?
                if (fSendFreeTransactions && nBytes <= MAX_FREE_TRANSACTION_CREATE_SIZE)
                {
                    // Not enough fee: enough priority?
                    double dPriorityNeeded = mempool.estimateSmartPriority(currentConfirmationTarget);
                    // Require at least hard-coded AllowFree.
                    if (dPriority >= dPriorityNeeded && AllowFree(dPriority))
                        break;
                }

                CAmount nFeeNeeded;

                if(!IsPolicy(feeAsset)){
                    nFeeNeeded = GetMinimumFee(nBytes, currentConfirmationTarget, mempool);
                    if (coinControl && nFeeNeeded > 0 && coinControl->nMinimumTotalFee > nFeeNeeded) {
                        nFeeNeeded = coinControl->nMinimumTotalFee;
                    }
                    if (coinControl && coinControl->fOverrideFeeRate)
                        nFeeNeeded = coinControl->nFeeRate.GetFee(nBytes);

                    // If we made it here and we aren't even able to meet the relay fee on the next pass, give up
                    // because we must be at the maximum allowed fee, if this is not a policy Tx
                    if ((nFeeNeeded < ::minRelayTxFee.GetFee(nBytes))) {
                        if (!IsAllPolicy(txUnblindedAndUnsigned)) {
                            strFailReason = _("Transaction too large for fee policy");
                            return std::vector<CWalletTx>();
                        }
                    }
                } else {
                    nFeeNeeded = 0;
                }

                if(fixedTxFee > 0 && !IsPolicy(feeAsset)) nFeeNeeded = fixedTxFee;

                if (nFeeRet >= nFeeNeeded) {
                    /* TODO Push actual blinding outside of loop and reactivate this logic
                    // Reduce fee to only the needed amount if we have change
                    // output to increase.  This prevents potential overpayment
                    // in fees if the coins selected to meet nFeeNeeded result
                    // in a transaction that requires less fee than the prior
                    // iteration.
                    // TODO: The case where nSubtractFeeFromAmount > 0 remains
                    // to be addressed because it requires returning the fee to
                    // the payees and not the change output.
                    // TODO: The case where there is no change output remains
                    // to be addressed so we avoid creating too small an output.
                    if (nFeeRet > nFeeNeeded && nChangePosInOut != -1 && nSubtractFeeFromAmount == 0) {
                        CAmount extraFeePaid = nFeeRet - nFeeNeeded;
                        vector<CTxOut>::iterator change_position = txNew.vout.begin()+nChangePosInOut;
                        change_position->nValue = CConfidentialValue(change_position->nValue.GetAmount() + extraFeePaid);
                        nFeeRet -= extraFeePaid;
                    } */

                    break; // Done, enough fee included.
                }
                /* TODO Push actual blinding outside of loop and reactivate this logic
                // Try to reduce change to include necessary fee
                if (nChangePosInOut != -1 && nSubtractFeeFromAmount == 0) {
                    CAmount additionalFeeNeeded = nFeeNeeded - nFeeRet;
                    vector<CTxOut>::iterator change_position = txNew.vout.begin()+nChangePosInOut;
                    // Only reduce change if remaining amount is still a large enough output.
                    if (change_position->nValue.GetAmount() >= MIN_FINAL_CHANGE + additionalFeeNeeded) {
                        change_position->nValue = CConfidentialValue(change_position->nValue.GetAmount() - additionalFeeNeeded);
                        nFeeRet += additionalFeeNeeded;
                        break; // Done, able to increase fee from change
                    }
                }*/

                // Include more fee and try again.
                nFeeRet = nFeeNeeded;
                continue;
            }
        }

        //add contract hash to transaction if option selected
        if (Params().ContractInTx()) {
            uint256 contract = chainActive.Tip() ? chainActive.Tip()->hashContract : GetContractHash();
            CScript scriptPubKey;
            scriptPubKey << OP_RETURN;
            scriptPubKey << std::vector<unsigned char>(contract.begin(), contract.end());
            CTxOut txoutcontract(feeAsset,0,scriptPubKey);
            txNew.vout.push_back(txoutcontract);
        }

        // TODO Do actual blinding/caching here to allow for amount adjustments until end
        if (sign)
        {
            CTransaction txNewConst(txNew);
            int nIn = 0;
            for (const auto& coin : setCoins)
            {
                const CScript& scriptPubKey = coin.first->tx->vout[coin.second].scriptPubKey;
                SignatureData sigdata;

                if (!ProduceSignature(TransactionSignatureCreator(this, &txNewConst, nIn, coin.first->tx->vout[coin.second].nValue, SIGHASH_ALL), scriptPubKey, sigdata))
                {
                    strFailReason = _("Signing transaction failed");
                    return std::vector<CWalletTx>();
                } else {
                    UpdateTransaction(txNew, nIn, sigdata);
                }

                nIn++;
            }
        } else {
            // Revert to pre-blinded transaction
            txNew = txUnblindedAndUnsigned;
        }

        // Embed the constructed transaction data in wtxNew.
        wtxNew.SetTx(MakeTransactionRef(std::move(txNew)));

        if (sign) {
            for (unsigned int i = 0; i< vAmounts.size(); i++) {
                assert(!output_assets[i].IsNull());
                wtxNew.SetBlindingData(i, vAmounts[i], output_pubkeys[i], output_blinds[i], output_assets[i], output_asset_blinds[i]);
            }
        }

        // Limit size
        if (GetTransactionWeight(wtxNew) >= MAX_STANDARD_TX_WEIGHT)
        {
            if (fSplitTransactions) {
                // First create a map of assets and recipients
                // and a set of the required assets
                std::set<CAsset> assetSet;
                std::map<CAsset, std::vector<CRecipient>> recipientMap;
                unsigned int nRecipients = 0;
                for (const auto& recipient : vecSendOriginal) {
                    if (recipientMap.find(recipient.asset) != recipientMap.end())
                        recipientMap[recipient.asset].push_back(recipient);
                    else {
                        std::vector<CRecipient> initVec;
                        initVec.push_back(recipient);
                        recipientMap[recipient.asset] = initVec;
                    }
                    assetSet.insert(recipient.asset);
                    nRecipients += 1;
                }
                if (assetSet.size() == 1) {
                    strFailReason = _("Transaction too large and could not be split as only a single asset is transacted");
                    return std::vector<CWalletTx>();
                }

                // Then create an output map of the assets that will be used
                // and a map of outputs that can be shared between split txs
                std::map<CAsset, std::vector<COutput>> usedOutputAssetMap;   // used outputs
                std::map<const CWalletTx* const, COutput> availableOutputMap;   // available outputs
                for (const auto& coin : vAvailableCoins) {
                    const CAsset &asset = coin.tx->GetOutputAsset(coin.i);
                    if (assetSet.find(asset) == assetSet.end()) {
                        availableOutputMap[coin.tx] = coin;
                    } else {
                        if (usedOutputAssetMap.find(asset) != usedOutputAssetMap.end())
                            usedOutputAssetMap[asset].push_back(coin);
                        else {
                            std::vector<COutput> initVec;
                            initVec.push_back(coin);
                            usedOutputAssetMap[asset] = initVec;
                        }
                    }
                }

                // Fill mAvailableInputs with the outputs of the unused assets
                typedef std::function<bool(COutput, COutput)> OutputComparison;
                if (mAvailableInputs && mAvailableInputs->size() == 0) {
                    OutputComparison outputDescendingComparison =
                        [](COutput left, COutput right) {
                            return left.tx->GetOutputValueOut(left.i) > right.tx->GetOutputValueOut(right.i);
                        };
                    for (const auto& remaining : availableOutputMap) {
                        if (mAvailableInputs->find(remaining.second.tx->GetOutputAsset(remaining.second.i)) != mAvailableInputs->end()) {
                            mAvailableInputs->at(remaining.second.tx->GetOutputAsset(remaining.second.i)).push_back(remaining.second);
                        } else {
                            std::vector<COutput> initVec;
                            initVec.push_back(remaining.second);
                            mAvailableInputs->insert({remaining.second.tx->GetOutputAsset(remaining.second.i), initVec});
                        }
                    }
                    std::map<CAsset, std::vector<COutput>> unsortedMap = *mAvailableInputs;
                    for (const auto& toSort : unsortedMap) {
                        std::vector<COutput> sortedAssetInputs = toSort.second;
                        std::sort(sortedAssetInputs.begin(), sortedAssetInputs.end(), outputDescendingComparison);
                        mAvailableInputs->at(toSort.first) = sortedAssetInputs;
                    }
                }

                // Split recipients and inputs (per asset) in (approximately) half
                std::vector<CRecipient> leftRecipients;
                std::vector<CRecipient> rightRecipients;
                std::vector<COutput> leftInputs;
                std::vector<COutput> rightInputs;
                unsigned int nRecipientsUsed = 0;
                bool fCenterReached = false;
                for (const auto& itAsset : assetSet) {
                    std::vector<CRecipient> curVecRecipients = recipientMap[itAsset];
                    std::vector<COutput> curVecInputs = usedOutputAssetMap[itAsset];
                    if (!fCenterReached) {
                        leftRecipients.insert(leftRecipients.end(), curVecRecipients.begin(), curVecRecipients.end());
                        leftInputs.insert(leftInputs.end(), curVecInputs.begin(), curVecInputs.end());
                        nRecipientsUsed += curVecRecipients.size();
                        if (nRecipientsUsed >= ceil(nRecipients / 2)) {
                            fCenterReached = true;
                        }
                    } else {
                        rightRecipients.insert(rightRecipients.end(), curVecRecipients.begin(), curVecRecipients.end());
                        rightInputs.insert(rightInputs.end(), curVecInputs.begin(), curVecInputs.end());
                    }
                }

                // sort recipients in descending order
                typedef std::function<bool(CRecipient, CRecipient)> RecipientComparison;
                RecipientComparison recipientComparisonFunction =
                    [](CRecipient left, CRecipient right) {
                        return left.nAmount < right.nAmount;
                    };
                sort(leftRecipients.begin(), leftRecipients.end(), recipientComparisonFunction);
                sort(rightRecipients.begin(), rightRecipients.end(), recipientComparisonFunction);

                // Unreserve and reserve change keys
                for (unsigned int i = 0; i < vChangeKeys[0].size(); ++i) {
                    vChangeKeys[0][i].ReturnKey();
                }
                std::vector<std::vector<CReserveKey>> vChangeKeysLeft;
                std::vector<std::vector<CReserveKey>> vChangeKeysRight;
                std::vector<CReserveKey> vChangeLeft;
                std::vector<CReserveKey> vChangeRight;
                vChangeLeft.reserve(leftRecipients.size() + 1);
                for (unsigned int j = 0; j < leftRecipients.size() + 1; ++j) {
                    vChangeLeft.emplace_back(pwalletMain);
                }
                vChangeKeysLeft.push_back(vChangeLeft);

                vChangeRight.reserve(rightRecipients.size() + 1);
                for (unsigned int j = 0; j < rightRecipients.size() + 1; ++j) {
                    vChangeRight.emplace_back(pwalletMain);
                }
                vChangeKeysRight.push_back(vChangeRight);

                // Create and send the transaction
                CAmount feeLeft;
                CAmount feeRight;
                CWalletTx dummyLeft, dummyRight;
                int dummyPosLeft = -1;
                int dummyPosRight = -1;
                std::vector<CWalletTx> leftRes = CreateTransaction(leftRecipients, dummyLeft, vChangeKeysLeft,
                    feeLeft, dummyPosLeft, strFailReason, coinControl, true, NULL, true, NULL, NULL, NULL,
                    CAsset(), fIgnoreBlindFail, fSplitTransactions, leftInputs, fFindFeeAsset, mAvailableInputs);
                std::vector<CWalletTx> rightRes = CreateTransaction(rightRecipients, dummyRight, vChangeKeysRight,
                    feeRight, dummyPosRight, strFailReason, coinControl, true, NULL, true, NULL, NULL, NULL,
                    CAsset(), fIgnoreBlindFail, fSplitTransactions, rightInputs, fFindFeeAsset, mAvailableInputs);
                if (leftRes.size() > 0 && rightRes.size() > 0) {
                    leftRes.insert( leftRes.end(), rightRes.begin(), rightRes.end() );
                    nFeeRet = feeLeft + feeRight;
                    vChangeKeys = vChangeKeysLeft;
                    vChangeKeys.insert(vChangeKeys.begin(), vChangeKeysRight.begin(), vChangeKeysRight.end());
                    return leftRes;
                } else {
                    return std::vector<CWalletTx>();
                }
            } else {
                strFailReason = _("Transaction too large");
                return std::vector<CWalletTx>();
            }
        }

    }

    if (GetBoolArg("-walletrejectlongchains", DEFAULT_WALLET_REJECT_LONG_CHAINS)) {
        // Lastly, ensure this tx will pass the mempool's chain limits
        LockPoints lp;
        std::set<std::pair<uint256, COutPoint> > setPeginsSpent;
        CTxMemPoolEntry entry(wtxNew.tx, 0, CAsset(), 0, 0, 0, 0, false, 0, lp, setPeginsSpent);
        CTxMemPool::setEntries setAncestors;
        size_t nLimitAncestors = GetArg("-limitancestorcount", DEFAULT_ANCESTOR_LIMIT);
        size_t nLimitAncestorSize = GetArg("-limitancestorsize", DEFAULT_ANCESTOR_SIZE_LIMIT)*1000;
        size_t nLimitDescendants = GetArg("-limitdescendantcount", DEFAULT_DESCENDANT_LIMIT);
        size_t nLimitDescendantSize = GetArg("-limitdescendantsize", DEFAULT_DESCENDANT_SIZE_LIMIT)*1000;
        std::string errString;
        if (!mempool.CalculateMemPoolAncestors(entry, setAncestors, nLimitAncestors, nLimitAncestorSize, nLimitDescendants, nLimitDescendantSize, errString)) {
            strFailReason = _("Transaction has too long of a mempool chain");
            return std::vector<CWalletTx>();
        }
    }
    std::vector<CWalletTx> finalVec;
    finalVec.push_back(wtxNew);
    return finalVec;
}

CAmountMap CWallet::GetBalanceFromOutputs(std::map<CAsset, std::vector<COutput>> outputMap)
{
    CAmountMap tempAvailableBalances;
    for (const auto& freeInputList : outputMap) {
        std::vector<COutput> freeOutputs = freeInputList.second;
        CAmount tempAssetAmount = 0;
        for (unsigned int i = 0; i < freeOutputs.size(); ++i) {
            tempAssetAmount += freeOutputs[i].tx->GetOutputValueOut(freeOutputs[i].i);
        }
        tempAvailableBalances[freeInputList.first] = tempAssetAmount;
    }
    return tempAvailableBalances;
}

bool CWallet::PreventDustForNewOutput(CAmountMap& mapValue, std::vector<CRecipient>& vecSend, unsigned int feeRecipientId)
{
    CRecipient feeAssetRecipient = vecSend[feeRecipientId];
    CTxOut dummyOutput = CTxOut(feeAssetRecipient.asset, feeAssetRecipient.nAmount, feeAssetRecipient.scriptPubKey);
    if (dummyOutput.IsDust(::minRelayTxFee)) {
        CAmount nDust = dummyOutput.GetDustThreshold(::minRelayTxFee) - dummyOutput.nValue.GetAmount();
        if (nDust > 0) {
            vecSend[feeRecipientId].nAmount += nDust;
            mapValue[vecSend[feeRecipientId].asset] += nDust; // raise change until no more dust
            for (unsigned int i = 0; i < vecSend.size(); i++) { // subtract from a recipient who has enough
                if (i != feeRecipientId) {
                    CTxOut dummyOutputForRefill = CTxOut(vecSend[i].asset, vecSend[i].nAmount, vecSend[i].scriptPubKey);
                    if (!dummyOutputForRefill.IsDust(::minRelayTxFee) &&
                        dummyOutputForRefill.GetDustThreshold(::minRelayTxFee) <= (dummyOutputForRefill.nValue.GetAmount() - nDust)) {
                        vecSend[i].nAmount -= nDust;
                        mapValue[vecSend[i].asset] -= nDust;
                        return true;
                    }
                }
            }
            return false;
        }
    }
    return true;
}

bool CWallet::DistributeFeeToNewBalance(CAmountMap& mapValue, CAsset feeAsset, std::vector<CRecipient>& vecSend,
    std::vector<CReserveKey>& vChangeKey, CAsset newAsset, CAmount newAssetValue, std::vector<COutput>* vAvailableCoins,
    std::map<CAsset, std::vector<COutput>>* mAvailableInputs)
{
    if (mAvailableInputs && vAvailableCoins && mAvailableInputs->size() > 0) {
        if (mAvailableInputs->find(newAsset) == mAvailableInputs->end())
            return false;
        auto &freeInputVector = mAvailableInputs->at(newAsset);
        CAmount amountFound = 0;
        int inputsUsed = 0;
        bool amountSatisfied = false;
        for (unsigned int i = 0; i < freeInputVector.size(); ++i) {
            amountFound += freeInputVector[i].tx->GetOutputValueOut(freeInputVector[i].i);
            ++inputsUsed;
            vAvailableCoins->push_back(freeInputVector[i]);
            if (amountFound >= newAssetValue) {
                amountSatisfied = true;
                break;
            }
        }

        freeInputVector.erase(freeInputVector.begin(), freeInputVector.begin() + inputsUsed);

        if (inputsUsed == 0 || !amountSatisfied)
            return false;

        if (mapValue[feeAsset] > amountFound) {
            mapValue[feeAsset] -= amountFound;
            mapValue[newAsset] = amountFound;
        } else {
            mapValue[newAsset] = mapValue[feeAsset];
            mapValue[feeAsset] = 0;
        }
    } else {
        if (mapValue[feeAsset] > newAssetValue) {
            mapValue[feeAsset] -= newAssetValue;
            mapValue[newAsset] = newAssetValue;
        } else {
            mapValue[newAsset] = mapValue[feeAsset];
            mapValue[feeAsset] = 0;
        }
    }

    bool feeRecipientErased = false;
    unsigned int feeRecipientId = 0;
    for (unsigned int j = 0; j < vecSend.size(); ++j) {
        if (vecSend[j].asset == feeAsset) {
            feeRecipientId = j;
            vecSend.push_back({vecSend[j].scriptPubKey, mapValue[newAsset], newAsset, vecSend[j].confidentiality_key, vecSend[j].fSubtractFeeFromAmount});
            if (mapValue[feeAsset] == 0) {
                vecSend.erase(vecSend.begin() + j);
                feeRecipientErased = true;
            } else {
                vecSend[j].nAmount = mapValue[feeAsset];
            }
            break;
        }
    }

    if (!feeRecipientErased) {
        if (!PreventDustForNewOutput(mapValue, vecSend, feeRecipientId))
            return false;
    } else {
        vChangeKey[feeRecipientId].ReturnKey();
        vChangeKey.erase(vChangeKey.begin() + feeRecipientId);
    }

    return true;
}

/**
 * Call after CreateTransaction unless you want to abort
 */
bool CWallet::CommitTransaction(CWalletTx& wtxNew, std::vector<CReserveKey>& reservekey, CConnman* connman, CValidationState& state)
{
    {
        LOCK2(cs_main, cs_wallet);
        LogPrintf("CommitTransaction:\n%s", wtxNew.tx->ToString());
        {
            // Take key pair from key pool so it won't be used again
            for (auto&& key : reservekey)
                key.KeepKey();

            // Add tx to wallet, because if it has change it's also ours,
            // otherwise just for transaction history.
            AddToWallet(wtxNew);

            // Notify that old coins are spent
            BOOST_FOREACH(const CTxIn& txin, wtxNew.tx->vin)
            {
                CWalletTx &coin = mapWallet[txin.prevout.hash];
                coin.BindWallet(this);
                NotifyTransactionChanged(this, coin.GetHash(), CT_UPDATED);
            }
        }

        // Track how many getdata requests our transaction gets
        mapRequestCount[wtxNew.GetHash()] = 0;

        if (fBroadcastTransactions)
        {
            // Broadcast
            if (!wtxNew.AcceptToMemoryPool(maxTxFee, state)) {
                LogPrintf("CommitTransaction(): Transaction cannot be broadcast immediately, %s\n", state.GetRejectReason());
                // TODO: if we expect the failure to be long term or permanent, instead delete wtx from the wallet and return failure.
            } else {
                wtxNew.RelayWalletTransaction(connman);
            }
        }
    }
    return true;
}

void CWallet::ListAccountCreditDebit(const std::string& strAccount, std::list<CAccountingEntry>& entries) {
    CWalletDB walletdb(strWalletFile);
    return walletdb.ListAccountCreditDebit(strAccount, entries);
}

bool CWallet::AddAccountingEntry(const CAccountingEntry& acentry)
{
    CWalletDB walletdb(strWalletFile);

    return AddAccountingEntry(acentry, &walletdb);
}

bool CWallet::AddAccountingEntry(const CAccountingEntry& acentry, CWalletDB *pwalletdb)
{
    if (!pwalletdb->WriteAccountingEntry_Backend(acentry))
        return false;

    laccentries.push_back(acentry);
    CAccountingEntry & entry = laccentries.back();
    wtxOrdered.insert(make_pair(entry.nOrderPos, TxPair((CWalletTx*)0, &entry)));

    return true;
}

CAmount CWallet::GetRequiredFee(unsigned int nTxBytes)
{
    return std::max(minTxFee.GetFee(nTxBytes), ::minRelayTxFee.GetFee(nTxBytes));
}

CAmount CWallet::GetMinimumFee(unsigned int nTxBytes, unsigned int nConfirmTarget, const CTxMemPool& pool)
{
    // payTxFee is the user-set global for desired feerate
    return GetMinimumFee(nTxBytes, nConfirmTarget, pool, payTxFee.GetFee(nTxBytes));
}

CAmount CWallet::GetMinimumFee(unsigned int nTxBytes, unsigned int nConfirmTarget, const CTxMemPool& pool, CAmount targetFee)
{
    CAmount nFeeNeeded = targetFee;
    // User didn't set: use -txconfirmtarget to estimate...
    if (nFeeNeeded == 0) {
        int estimateFoundTarget = nConfirmTarget;
        nFeeNeeded = pool.estimateSmartFee(nConfirmTarget, &estimateFoundTarget).GetFee(nTxBytes);
        // ... unless we don't have enough mempool data for estimatefee, then use fallbackFee
        if (nFeeNeeded == 0)
            nFeeNeeded = fallbackFee.GetFee(nTxBytes);
    }
    // prevent user from paying a fee below minRelayTxFee or minTxFee
    nFeeNeeded = std::max(nFeeNeeded, GetRequiredFee(nTxBytes));
    // But always obey the maximum
    if (nFeeNeeded > maxTxFee)
        nFeeNeeded = maxTxFee;
    return nFeeNeeded;
}




DBErrors CWallet::LoadWallet(bool& fFirstRunRet)
{
    if (!fFileBacked)
        return DB_LOAD_OK;
    fFirstRunRet = false;
    DBErrors nLoadWalletRet = CWalletDB(strWalletFile,"cr+").LoadWallet(this);
    if (nLoadWalletRet == DB_NEED_REWRITE)
    {
        if (CDB::Rewrite(strWalletFile, "\x04pool"))
        {
            LOCK(cs_wallet);
            setKeyPool.clear();
            // Note: can't top-up keypool here, because wallet is locked.
            // User will be prompted to unlock wallet the next operation
            // that requires a new key.
        }
    }

    if (nLoadWalletRet != DB_LOAD_OK)
        return nLoadWalletRet;
    fFirstRunRet = !vchDefaultKey.IsValid();

    uiInterface.LoadWallet(this);

    return DB_LOAD_OK;
}

DBErrors CWallet::ZapSelectTx(vector<uint256>& vHashIn, vector<uint256>& vHashOut)
{
    if (!fFileBacked)
        return DB_LOAD_OK;
    DBErrors nZapSelectTxRet = CWalletDB(strWalletFile,"cr+").ZapSelectTx(this, vHashIn, vHashOut);
    if (nZapSelectTxRet == DB_NEED_REWRITE)
    {
        if (CDB::Rewrite(strWalletFile, "\x04pool"))
        {
            LOCK(cs_wallet);
            setKeyPool.clear();
            // Note: can't top-up keypool here, because wallet is locked.
            // User will be prompted to unlock wallet the next operation
            // that requires a new key.
        }
    }

    if (nZapSelectTxRet != DB_LOAD_OK)
        return nZapSelectTxRet;

    MarkDirty();

    return DB_LOAD_OK;

}

DBErrors CWallet::ZapWalletTx(std::vector<CWalletTx>& vWtx)
{
    if (!fFileBacked)
        return DB_LOAD_OK;
    DBErrors nZapWalletTxRet = CWalletDB(strWalletFile,"cr+").ZapWalletTx(this, vWtx);
    if (nZapWalletTxRet == DB_NEED_REWRITE)
    {
        if (CDB::Rewrite(strWalletFile, "\x04pool"))
        {
            LOCK(cs_wallet);
            setKeyPool.clear();
            // Note: can't top-up keypool here, because wallet is locked.
            // User will be prompted to unlock wallet the next operation
            // that requires a new key.
        }
    }

    if (nZapWalletTxRet != DB_LOAD_OK)
        return nZapWalletTxRet;

    return DB_LOAD_OK;
}


bool CWallet::SetAddressBook(const CTxDestination& address, const string& strName, const string& strPurpose)
{
    bool fUpdated = false;
    {
        LOCK(cs_wallet); // mapAddressBook
        std::map<CTxDestination, CAddressBookData>::iterator mi = mapAddressBook.find(address);
        fUpdated = mi != mapAddressBook.end();
        mapAddressBook[address].name = strName;
        if (!strPurpose.empty()) /* update purpose only if requested */
            mapAddressBook[address].purpose = strPurpose;
    }
    NotifyAddressBookChanged(this, address, strName, ::IsMine(*this, address) != ISMINE_NO,
                             strPurpose, (fUpdated ? CT_UPDATED : CT_NEW) );
    if (!fFileBacked)
        return false;
    if (!strPurpose.empty() && !CWalletDB(strWalletFile).WritePurpose(CBitcoinAddress(address).ToString(), strPurpose))
        return false;
    return CWalletDB(strWalletFile).WriteName(CBitcoinAddress(address).ToString(), strName);
}

bool CWallet::DelAddressBook(const CTxDestination& address)
{
    {
        LOCK(cs_wallet); // mapAddressBook

        if(fFileBacked)
        {
            // Delete destdata tuples associated with address
            std::string strAddress = CBitcoinAddress(address).ToString();
            BOOST_FOREACH(const PAIRTYPE(string, string) &item, mapAddressBook[address].destdata)
            {
                CWalletDB(strWalletFile).EraseDestData(strAddress, item.first);
            }
        }
        mapAddressBook.erase(address);
    }

    NotifyAddressBookChanged(this, address, "", ::IsMine(*this, address) != ISMINE_NO, "", CT_DELETED);

    if (!fFileBacked)
        return false;
    CWalletDB(strWalletFile).ErasePurpose(CBitcoinAddress(address).ToString());
    return CWalletDB(strWalletFile).EraseName(CBitcoinAddress(address).ToString());
}

bool CWallet::SetDefaultKey(const CPubKey &vchPubKey)
{
    if (fFileBacked)
    {
        if (!CWalletDB(strWalletFile).WriteDefaultKey(vchPubKey))
            return false;
    }
    vchDefaultKey = vchPubKey;
    return true;
}

/**
 * Mark old keypool keys as used,
 * and generate all new keys
 */
bool CWallet::NewKeyPool()
{
    {
        LOCK(cs_wallet);
        CWalletDB walletdb(strWalletFile);
        BOOST_FOREACH(int64_t nIndex, setKeyPool)
            walletdb.ErasePool(nIndex);
        setKeyPool.clear();

        if (IsLocked())
            return false;

        int64_t nKeys = max(GetArg("-keypool", DEFAULT_KEYPOOL_SIZE), (int64_t)0);
        for (int i = 0; i < nKeys; i++)
        {
            int64_t nIndex = i+1;
            walletdb.WritePool(nIndex, CKeyPool(GenerateNewKey()));
            setKeyPool.insert(nIndex);
        }
        LogPrintf("CWallet::NewKeyPool wrote %d new keys\n", nKeys);
    }
    return true;
}

bool CWallet::TopUpKeyPool(unsigned int kpSize)
{
    {
        LOCK(cs_wallet);

        if (IsLocked())
            return false;

        CWalletDB walletdb(strWalletFile);

        // Top up key pool
        unsigned int nTargetSize;
        if (kpSize > 0)
            nTargetSize = kpSize;
        else
            nTargetSize = max(GetArg("-keypool", DEFAULT_KEYPOOL_SIZE), (int64_t) 0);

        while (setKeyPool.size() < (nTargetSize + 1))
        {
            int64_t nEnd = 1;
            if (!setKeyPool.empty())
                nEnd = *(--setKeyPool.end()) + 1;
            if (!walletdb.WritePool(nEnd, CKeyPool(GenerateNewKey())))
                throw runtime_error(std::string(__func__) + ": writing generated key failed");
            setKeyPool.insert(nEnd);
            LogPrintf("keypool added key %d, size=%u\n", nEnd, setKeyPool.size());
        }
    }
    return true;
}

void CWallet::ReserveKeyFromKeyPool(int64_t& nIndex, CKeyPool& keypool)
{
    nIndex = -1;
    keypool.vchPubKey = CPubKey();
    {
        LOCK(cs_wallet);

        if (!IsLocked())
            TopUpKeyPool();

        // Get the oldest key
        if(setKeyPool.empty())
            return;

        CWalletDB walletdb(strWalletFile);

        nIndex = *(setKeyPool.begin());
        setKeyPool.erase(setKeyPool.begin());
        if (!walletdb.ReadPool(nIndex, keypool))
            throw runtime_error(std::string(__func__) + ": read failed");
        if (!HaveKey(keypool.vchPubKey.GetID()))
            throw runtime_error(std::string(__func__) + ": unknown key in key pool");
        assert(keypool.vchPubKey.IsValid());
        LogPrintf("keypool reserve %d\n", nIndex);
    }
}

void CWallet::KeepKey(int64_t nIndex)
{
    // Remove from key pool
    if (fFileBacked)
    {
        CWalletDB walletdb(strWalletFile);
        walletdb.ErasePool(nIndex);
    }
    LogPrintf("keypool keep %d\n", nIndex);
}

void CWallet::ReturnKey(int64_t nIndex)
{
    // Return to key pool
    {
        LOCK(cs_wallet);
        setKeyPool.insert(nIndex);
    }
    LogPrintf("keypool return %d\n", nIndex);
}

bool CWallet::GetKeyFromPool(CPubKey& result)
{
    int64_t nIndex = 0;
    CKeyPool keypool;
    {
        LOCK(cs_wallet);
        ReserveKeyFromKeyPool(nIndex, keypool);
        if (nIndex == -1)
        {
            if (IsLocked()) return false;
            result = GenerateNewKey();
            return true;
        }
        KeepKey(nIndex);
        result = keypool.vchPubKey;
    }
    return true;
}

int64_t CWallet::GetOldestKeyPoolTime()
{
    LOCK(cs_wallet);

    // if the keypool is empty, return <NOW>
    if (setKeyPool.empty())
        return GetTime();

    // load oldest key from keypool, get time and return
    CKeyPool keypool;
    CWalletDB walletdb(strWalletFile);
    int64_t nIndex = *(setKeyPool.begin());
    if (!walletdb.ReadPool(nIndex, keypool))
        throw runtime_error(std::string(__func__) + ": read oldest key in keypool failed");
    assert(keypool.vchPubKey.IsValid());
    return keypool.nTime;
}

std::map<CTxDestination, CAmount> CWallet::GetAddressBalances()
{
    map<CTxDestination, CAmount> balances;

    {
        LOCK(cs_wallet);
        BOOST_FOREACH(PAIRTYPE(uint256, CWalletTx) walletEntry, mapWallet)
        {
            CWalletTx *pcoin = &walletEntry.second;

            if (!pcoin->IsTrusted())
                continue;

            if (pcoin->IsCoinBase() && pcoin->GetBlocksToMaturity() > 0)
                continue;

            int nDepth = pcoin->GetDepthInMainChain();
            if (nDepth < (pcoin->IsFromMe(ISMINE_ALL) ? 0 : 1))
                continue;

            for (unsigned int i = 0; i < pcoin->tx->vout.size(); i++)
            {
                CTxDestination addr;
                if (!IsMine(pcoin->tx->vout[i]))
                    continue;
                if(!ExtractDestination(pcoin->tx->vout[i].scriptPubKey, addr))
                    continue;

                CAmount n = IsSpent(walletEntry.first, i) ? 0 : pcoin->GetOutputValueOut(i);

                if (!balances.count(addr))
                    balances[addr] = 0;
                balances[addr] += n;
            }
        }
    }

    return balances;
}

set< set<CTxDestination> > CWallet::GetAddressGroupings()
{
    AssertLockHeld(cs_wallet); // mapWallet
    set< set<CTxDestination> > groupings;
    set<CTxDestination> grouping;

    BOOST_FOREACH(PAIRTYPE(uint256, CWalletTx) walletEntry, mapWallet)
    {
        CWalletTx *pcoin = &walletEntry.second;

        if (pcoin->tx->vin.size() > 0)
        {
            bool any_mine = false;
            // group all input addresses with each other
            BOOST_FOREACH(CTxIn txin, pcoin->tx->vin)
            {
                CTxDestination address;
                if(!IsMine(txin)) /* If this input isn't mine, ignore it */
                    continue;
                if(!ExtractDestination(mapWallet[txin.prevout.hash].tx->vout[txin.prevout.n].scriptPubKey, address))
                    continue;
                grouping.insert(address);
                any_mine = true;
            }

            // group change with input addresses
            if (any_mine)
            {
               BOOST_FOREACH(CTxOut txout, pcoin->tx->vout)
                   if (IsChange(txout))
                   {
                       CTxDestination txoutAddr;
                       if(!ExtractDestination(txout.scriptPubKey, txoutAddr))
                           continue;
                       grouping.insert(txoutAddr);
                   }
            }
            if (grouping.size() > 0)
            {
                groupings.insert(grouping);
                grouping.clear();
            }
        }

        // group lone addrs by themselves
        for (unsigned int i = 0; i < pcoin->tx->vout.size(); i++)
            if (IsMine(pcoin->tx->vout[i]))
            {
                CTxDestination address;
                if(!ExtractDestination(pcoin->tx->vout[i].scriptPubKey, address))
                    continue;
                grouping.insert(address);
                groupings.insert(grouping);
                grouping.clear();
            }
    }

    set< set<CTxDestination>* > uniqueGroupings; // a set of pointers to groups of addresses
    map< CTxDestination, set<CTxDestination>* > setmap;  // map addresses to the unique group containing it
    BOOST_FOREACH(set<CTxDestination> _grouping, groupings)
    {
        // make a set of all the groups hit by this new group
        set< set<CTxDestination>* > hits;
        map< CTxDestination, set<CTxDestination>* >::iterator it;
        BOOST_FOREACH(CTxDestination address, _grouping)
            if ((it = setmap.find(address)) != setmap.end())
                hits.insert((*it).second);

        // merge all hit groups into a new single group and delete old groups
        set<CTxDestination>* merged = new set<CTxDestination>(_grouping);
        BOOST_FOREACH(set<CTxDestination>* hit, hits)
        {
            merged->insert(hit->begin(), hit->end());
            uniqueGroupings.erase(hit);
            delete hit;
        }
        uniqueGroupings.insert(merged);

        // update setmap
        BOOST_FOREACH(CTxDestination element, *merged)
            setmap[element] = merged;
    }

    set< set<CTxDestination> > ret;
    BOOST_FOREACH(set<CTxDestination>* uniqueGrouping, uniqueGroupings)
    {
        ret.insert(*uniqueGrouping);
        delete uniqueGrouping;
    }

    return ret;
}

CAmount CWallet::GetAccountBalance(const std::string& strAccount, int nMinDepth, const isminefilter& filter)
{
    CWalletDB walletdb(strWalletFile);
    return GetAccountBalance(walletdb, strAccount, nMinDepth, filter);
}

CAmount CWallet::GetAccountBalance(CWalletDB& walletdb, const std::string& strAccount, int nMinDepth, const isminefilter& filter)
{
    CAmount nBalance = 0;

    // Tally wallet transactions
    for (map<uint256, CWalletTx>::iterator it = mapWallet.begin(); it != mapWallet.end(); ++it)
    {
        const CWalletTx& wtx = (*it).second;
        if (!CheckFinalTx(wtx) || wtx.GetBlocksToMaturity() > 0 || wtx.GetDepthInMainChain() < 0)
            continue;

        CAmount nReceived, nSent, nFee;
        wtx.GetAccountAmounts(strAccount, nReceived, nSent, nFee, filter);

        if (nReceived != 0 && wtx.GetDepthInMainChain() >= nMinDepth)
            nBalance += nReceived;
        nBalance -= nSent + nFee;
    }

    // Tally internal accounting entries
    nBalance += walletdb.GetAccountCreditDebit(strAccount);

    return nBalance;
}

std::set<CTxDestination> CWallet::GetAccountAddresses(const std::string& strAccount) const
{
    LOCK(cs_wallet);
    set<CTxDestination> result;
    BOOST_FOREACH(const PAIRTYPE(CTxDestination, CAddressBookData)& item, mapAddressBook)
    {
        const CTxDestination& address = item.first;
        const string& strName = item.second.name;
        if (strName == strAccount)
            result.insert(address);
    }
    return result;
}

bool CReserveKey::GetReservedKey(CPubKey& pubkey)
{
    if (nIndex == -1)
    {
        CKeyPool keypool;
        pwallet->ReserveKeyFromKeyPool(nIndex, keypool);
        if (nIndex != -1)
            vchPubKey = keypool.vchPubKey;
        else {
            return false;
        }
    }
    assert(vchPubKey.IsValid());
    pubkey = vchPubKey;
    return true;
}

void CReserveKey::KeepKey()
{
    if (nIndex != -1)
        pwallet->KeepKey(nIndex);
    nIndex = -1;
    vchPubKey = CPubKey();
}

void CReserveKey::ReturnKey()
{
    if (nIndex != -1)
        pwallet->ReturnKey(nIndex);
    nIndex = -1;
    vchPubKey = CPubKey();
}

void CWallet::GetAllReserveKeys(set<CKeyID>& setAddress) const
{
    setAddress.clear();

    CWalletDB walletdb(strWalletFile);

    LOCK2(cs_main, cs_wallet);
    BOOST_FOREACH(const int64_t& id, setKeyPool)
    {
        CKeyPool keypool;
        if (!walletdb.ReadPool(id, keypool))
            throw runtime_error(std::string(__func__) + ": read failed");
        assert(keypool.vchPubKey.IsValid());
        CKeyID keyID = keypool.vchPubKey.GetID();
        if (!HaveKey(keyID))
            throw runtime_error(std::string(__func__) + ": unknown key in key pool");
        setAddress.insert(keyID);
    }
}

void CWallet::UpdatedTransaction(const uint256 &hashTx)
{
    {
        LOCK(cs_wallet);
        // Only notify UI if this transaction is in this wallet
        map<uint256, CWalletTx>::const_iterator mi = mapWallet.find(hashTx);
        if (mi != mapWallet.end())
            NotifyTransactionChanged(this, hashTx, CT_UPDATED);
    }
}

void CWallet::GetScriptForMining(boost::shared_ptr<CReserveScript> &script)
{
    boost::shared_ptr<CReserveKey> rKey(new CReserveKey(this));
    CPubKey pubkey;
    if (!rKey->GetReservedKey(pubkey))
        return;

    script = rKey;
    script->reserveScript = CScript() << ToByteVector(pubkey) << OP_CHECKSIG;
}

void CWallet::LockCoin(const COutPoint& output)
{
    AssertLockHeld(cs_wallet); // setLockedCoins
    setLockedCoins.insert(output);
}

void CWallet::UnlockCoin(const COutPoint& output)
{
    AssertLockHeld(cs_wallet); // setLockedCoins
    setLockedCoins.erase(output);
}

void CWallet::UnlockAllCoins()
{
    AssertLockHeld(cs_wallet); // setLockedCoins
    setLockedCoins.clear();
}

bool CWallet::IsLockedCoin(uint256 hash, unsigned int n) const
{
    AssertLockHeld(cs_wallet); // setLockedCoins
    COutPoint outpt(hash, n);

    return (setLockedCoins.count(outpt) > 0);
}

void CWallet::ListLockedCoins(std::vector<COutPoint>& vOutpts)
{
    AssertLockHeld(cs_wallet); // setLockedCoins
    for (std::set<COutPoint>::iterator it = setLockedCoins.begin();
         it != setLockedCoins.end(); it++) {
        COutPoint outpt = (*it);
        vOutpts.push_back(outpt);
    }
}

/** @} */ // end of Actions

class CAffectedKeysVisitor : public boost::static_visitor<void> {
private:
    const CKeyStore &keystore;
    std::vector<CKeyID> &vKeys;

public:
    CAffectedKeysVisitor(const CKeyStore &keystoreIn, std::vector<CKeyID> &vKeysIn) : keystore(keystoreIn), vKeys(vKeysIn) {}

    void Process(const CScript &script) {
        txnouttype type;
        std::vector<CTxDestination> vDest;
        int nRequired;
        if (ExtractDestinations(script, type, vDest, nRequired)) {
            BOOST_FOREACH(const CTxDestination &dest, vDest)
                boost::apply_visitor(*this, dest);
        }
    }

    void operator()(const CKeyID &keyId) {
        if (keystore.HaveKey(keyId))
            vKeys.push_back(keyId);
    }

    void operator()(const CScriptID &scriptId) {
        CScript script;
        if (keystore.GetCScript(scriptId, script))
            Process(script);
    }

    void operator()(const CNoDestination &none) {}
};

void CWallet::GetKeyBirthTimes(std::map<CTxDestination, int64_t> &mapKeyBirth) const {
    AssertLockHeld(cs_wallet); // mapKeyMetadata
    mapKeyBirth.clear();

    // get birth times for keys with metadata
    for (const auto& entry : mapKeyMetadata) {
        if (entry.second.nCreateTime) {
            mapKeyBirth[entry.first] = entry.second.nCreateTime;
        }
    }

    // map in which we'll infer heights of other keys
    CBlockIndex *pindexMax = chainActive[std::max(0, chainActive.Height() - 144)]; // the tip can be reorganized; use a 144-block safety margin
    std::map<CKeyID, CBlockIndex*> mapKeyFirstBlock;
    std::set<CKeyID> setKeys;
    GetKeys(setKeys);
    BOOST_FOREACH(const CKeyID &keyid, setKeys) {
        if (mapKeyBirth.count(keyid) == 0)
            mapKeyFirstBlock[keyid] = pindexMax;
    }
    setKeys.clear();

    // if there are no such keys, we're done
    if (mapKeyFirstBlock.empty())
        return;

    // find first block that affects those keys, if there are any left
    std::vector<CKeyID> vAffected;
    for (std::map<uint256, CWalletTx>::const_iterator it = mapWallet.begin(); it != mapWallet.end(); it++) {
        // iterate over all wallet transactions...
        const CWalletTx &wtx = (*it).second;
        BlockMap::const_iterator blit = mapBlockIndex.find(wtx.hashBlock);
        if (blit != mapBlockIndex.end() && chainActive.Contains(blit->second)) {
            // ... which are already in a block
            int nHeight = blit->second->nHeight;
            BOOST_FOREACH(const CTxOut &txout, wtx.tx->vout) {
                // iterate over all their outputs
                CAffectedKeysVisitor(*this, vAffected).Process(txout.scriptPubKey);
                BOOST_FOREACH(const CKeyID &keyid, vAffected) {
                    // ... and all their affected keys
                    std::map<CKeyID, CBlockIndex*>::iterator rit = mapKeyFirstBlock.find(keyid);
                    if (rit != mapKeyFirstBlock.end() && nHeight < rit->second->nHeight)
                        rit->second = blit->second;
                }
                vAffected.clear();
            }
        }
    }

    // Extract block timestamps for those keys
    for (std::map<CKeyID, CBlockIndex*>::const_iterator it = mapKeyFirstBlock.begin(); it != mapKeyFirstBlock.end(); it++)
        mapKeyBirth[it->first] = it->second->GetBlockTime() - 7200; // block times can be 2h off
}

bool CWallet::AddDestData(const CTxDestination &dest, const std::string &key, const std::string &value)
{
    if (dest.which() == ((CTxDestination)CNoDestination()).which())
        return false;

    mapAddressBook[dest].destdata.insert(std::make_pair(key, value));
    if (!fFileBacked)
        return true;
    return CWalletDB(strWalletFile).WriteDestData(CBitcoinAddress(dest).ToString(), key, value);
}

bool CWallet::EraseDestData(const CTxDestination &dest, const std::string &key)
{
    if (!mapAddressBook[dest].destdata.erase(key))
        return false;
    if (!fFileBacked)
        return true;
    return CWalletDB(strWalletFile).EraseDestData(CBitcoinAddress(dest).ToString(), key);
}

bool CWallet::LoadDestData(const CTxDestination &dest, const std::string &key, const std::string &value)
{
    mapAddressBook[dest].destdata.insert(std::make_pair(key, value));
    return true;
}

bool CWallet::GetDestData(const CTxDestination &dest, const std::string &key, std::string *value) const
{
    std::map<CTxDestination, CAddressBookData>::const_iterator i = mapAddressBook.find(dest);
    if(i != mapAddressBook.end())
    {
        CAddressBookData::StringMap::const_iterator j = i->second.destdata.find(key);
        if(j != i->second.destdata.end())
        {
            if(value)
                *value = j->second;
            return true;
        }
    }
    return false;
}

std::string CWallet::GetWalletHelpString(bool showDebug)
{
    std::string strUsage = HelpMessageGroup(_("Wallet options:"));
    strUsage += HelpMessageOpt("-disablewallet", _("Do not load the wallet and disable wallet RPC calls"));
    strUsage += HelpMessageOpt("-disablect", _("Disable usage of confidential transactions and addresses"));
    strUsage += HelpMessageOpt("-keypool=<n>", strprintf(_("Set key pool size to <n> (default: %u)"), DEFAULT_KEYPOOL_SIZE));
    strUsage += HelpMessageOpt("-fallbackfee=<amt>", strprintf(_("A fee rate (in %s/kB) that will be used when fee estimation has insufficient data (default: %s)"),
                                                               CURRENCY_UNIT, FormatMoney(DEFAULT_FALLBACK_FEE)));
    strUsage += HelpMessageOpt("-mintxfee=<amt>", strprintf(_("Fees (in %s/kB) smaller than this are considered zero fee for transaction creation (default: %s)"),
                                                            CURRENCY_UNIT, FormatMoney(DEFAULT_TRANSACTION_MINFEE)));
    strUsage += HelpMessageOpt("-paytxfee=<amt>", strprintf(_("Fee (in %s/kB) to add to transactions you send (default: %s)"),
                                                            CURRENCY_UNIT, FormatMoney(payTxFee.GetFeePerK())));
    strUsage += HelpMessageOpt("-rescan", _("Rescan the block chain for missing wallet transactions on startup"));
    strUsage += HelpMessageOpt("-salvagewallet", _("Attempt to recover private keys from a corrupt wallet on startup"));
    if (showDebug)
        strUsage += HelpMessageOpt("-sendfreetransactions", strprintf(_("Send transactions as zero-fee transactions if possible (default: %u)"), DEFAULT_SEND_FREE_TRANSACTIONS));
    strUsage += HelpMessageOpt("-spendzeroconfchange", strprintf(_("Spend unconfirmed change when sending transactions (default: %u)"), DEFAULT_SPEND_ZEROCONF_CHANGE));
    strUsage += HelpMessageOpt("-txconfirmtarget=<n>", strprintf(_("If paytxfee is not set, include enough fee so transactions begin confirmation on average within n blocks (default: %u)"), DEFAULT_TX_CONFIRM_TARGET));
    strUsage += HelpMessageOpt("-usehd", _("Use hierarchical deterministic key generation (HD) after BIP32. Only has effect during wallet creation/first start") + " " + strprintf(_("(default: %u)"), DEFAULT_USE_HD_WALLET));
    strUsage += HelpMessageOpt("-upgradewallet", _("Upgrade wallet to latest format on startup"));
    strUsage += HelpMessageOpt("-wallet=<file>", _("Specify wallet file (within data directory)") + " " + strprintf(_("(default: %s)"), DEFAULT_WALLET_DAT));
    strUsage += HelpMessageOpt("-walletbroadcast", _("Make the wallet broadcast transactions") + " " + strprintf(_("(default: %u)"), DEFAULT_WALLETBROADCAST));
    strUsage += HelpMessageOpt("-walletnotify=<cmd>", _("Execute command when a wallet transaction changes (%s in cmd is replaced by TxID)"));
    strUsage += HelpMessageOpt("-zapwallettxes=<mode>", _("Delete all wallet transactions and only recover those parts of the blockchain through -rescan on startup") +
                               " " + _("(1 = keep tx meta data e.g. account owner and payment request information, 2 = drop tx meta data)"));

    if (showDebug)
    {
        strUsage += HelpMessageGroup(_("Wallet debugging/testing options:"));

        strUsage += HelpMessageOpt("-dblogsize=<n>", strprintf("Flush wallet database activity from memory to disk log every <n> megabytes (default: %u)", DEFAULT_WALLET_DBLOGSIZE));
        strUsage += HelpMessageOpt("-flushwallet", strprintf("Run a thread to flush wallet periodically (default: %u)", DEFAULT_FLUSHWALLET));
        strUsage += HelpMessageOpt("-privdb", strprintf("Sets the DB_PRIVATE flag in the wallet db environment (default: %u)", DEFAULT_WALLET_PRIVDB));
        strUsage += HelpMessageOpt("-walletrejectlongchains", strprintf(_("Wallet will not create transactions that violate mempool chain limits (default: %u)"), DEFAULT_WALLET_REJECT_LONG_CHAINS));
    }

    return strUsage;
}

CWallet* CWallet::CreateWalletFromFile(const std::string walletFile)
{
    // needed to restore wallet transaction meta data after -zapwallettxes
    std::vector<CWalletTx> vWtx;

    if (GetBoolArg("-zapwallettxes", false)) {
        uiInterface.InitMessage(_("Zapping all transactions from wallet..."));

        CWallet *tempWallet = new CWallet(walletFile);
        DBErrors nZapWalletRet = tempWallet->ZapWalletTx(vWtx);
        if (nZapWalletRet != DB_LOAD_OK) {
            InitError(strprintf(_("Error loading %s: Wallet corrupted"), walletFile));
            return NULL;
        }

        delete tempWallet;
        tempWallet = NULL;
    }

    uiInterface.InitMessage(_("Loading wallet..."));

    int64_t nStart = GetTimeMillis();
    bool fFirstRun = true;
    CWallet *walletInstance = new CWallet(walletFile);
    DBErrors nLoadWalletRet = walletInstance->LoadWallet(fFirstRun);
    if (nLoadWalletRet != DB_LOAD_OK)
    {
        if (nLoadWalletRet == DB_CORRUPT) {
            InitError(strprintf(_("Error loading %s: Wallet corrupted"), walletFile));
            return NULL;
        }
        else if (nLoadWalletRet == DB_NONCRITICAL_ERROR)
        {
            InitWarning(strprintf(_("Error reading %s! All keys read correctly, but transaction data"
                                         " or address book entries might be missing or incorrect."),
                walletFile));
        }
        else if (nLoadWalletRet == DB_TOO_NEW) {
            InitError(strprintf(_("Error loading %s: Wallet requires newer version of %s"), walletFile, _(PACKAGE_NAME)));
            return NULL;
        }
        else if (nLoadWalletRet == DB_NEED_REWRITE)
        {
            InitError(strprintf(_("Wallet needed to be rewritten: restart %s to complete"), _(PACKAGE_NAME)));
            return NULL;
        }
        else {
            InitError(strprintf(_("Error loading %s"), walletFile));
            return NULL;
        }
    }

    if (GetBoolArg("-upgradewallet", fFirstRun))
    {
        int nMaxVersion = GetArg("-upgradewallet", 0);
        if (nMaxVersion == 0) // the -upgradewallet without argument case
        {
            LogPrintf("Performing wallet upgrade to %i\n", FEATURE_LATEST);
            nMaxVersion = CLIENT_VERSION;
            walletInstance->SetMinVersion(FEATURE_LATEST); // permanently upgrade the wallet immediately
        }
        else
            LogPrintf("Allowing wallet upgrade up to %i\n", nMaxVersion);
        if (nMaxVersion < walletInstance->GetVersion())
        {
            InitError(_("Cannot downgrade wallet"));
            return NULL;
        }
        walletInstance->SetMaxVersion(nMaxVersion);
    }

    if (fFirstRun)
    {
        // Create new keyUser and set as default key
        if (GetBoolArg("-usehd", DEFAULT_USE_HD_WALLET) && !walletInstance->IsHDEnabled()) {
            // generate a new master key
            CPubKey masterPubKey = walletInstance->GenerateNewHDMasterKey();
            if (!walletInstance->SetHDMasterKey(masterPubKey))
                throw std::runtime_error(std::string(__func__) + ": Storing master key failed");
        }

        CPubKey newDefaultKey;
        if (walletInstance->GetKeyFromPool(newDefaultKey)) {
            walletInstance->SetDefaultKey(newDefaultKey);
            if (!walletInstance->SetAddressBook(walletInstance->vchDefaultKey.GetID(), "", "receive")) {
                InitError(_("Cannot write default address") += "\n");
                return NULL;
            }
        }

        walletInstance->SetBestChain(chainActive.GetLocator());
    }
    else if (IsArgSet("-usehd")) {
        bool useHD = GetBoolArg("-usehd", DEFAULT_USE_HD_WALLET);
        if (walletInstance->IsHDEnabled() && !useHD) {
            InitError(strprintf(_("Error loading %s: You can't disable HD on a already existing HD wallet"), walletFile));
            return NULL;
        }
        if (!walletInstance->IsHDEnabled() && useHD) {
            InitError(strprintf(_("Error loading %s: You can't enable HD on a already existing non-HD wallet"), walletFile));
            return NULL;
        }
    }

    LogPrintf(" wallet      %15dms\n", GetTimeMillis() - nStart);

    RegisterValidationInterface(walletInstance);

    CBlockIndex *pindexRescan = chainActive.Tip();
    if (GetBoolArg("-rescan", false)){
        pindexRescan = chainActive.Genesis();
    }
    else
    {
        CWalletDB walletdb(walletFile);
        CBlockLocator locator;
        if (walletdb.ReadBestBlock(locator))
            pindexRescan = FindForkInGlobalIndex(chainActive, locator);
        else
            pindexRescan = chainActive.Genesis();
    }
    if (chainActive.Tip() && chainActive.Tip() != pindexRescan)
    {
        //We can't rescan beyond non-pruned blocks, stop and throw an error
        //this might happen if a user uses a old wallet within a pruned node
        // or if he ran -disablewallet for a longer time, then decided to re-enable
        if (fPruneMode)
        {
            CBlockIndex *block = chainActive.Tip();
            while (block && block->pprev && (block->pprev->nStatus & BLOCK_HAVE_DATA) && block->pprev->nTx > 0 && pindexRescan != block)
                block = block->pprev;

            if (pindexRescan != block) {
                InitError(_("Prune: last wallet synchronisation goes beyond pruned data. You need to -reindex (download the whole blockchain again in case of pruned node)"));
                return NULL;
            }
        }

        uiInterface.InitMessage(_("Rescanning..."));
        LogPrintf("Rescanning last %i blocks (from block %i)...\n", chainActive.Height() - pindexRescan->nHeight, pindexRescan->nHeight);
        nStart = GetTimeMillis();
        walletInstance->ScanForWalletTransactions(pindexRescan, true);
        LogPrintf(" rescan      %15dms\n", GetTimeMillis() - nStart);
        walletInstance->SetBestChain(chainActive.GetLocator());
        CWalletDB::IncrementUpdateCounter();

        // Restore wallet transaction metadata after -zapwallettxes=1
        if (GetBoolArg("-zapwallettxes", false) && GetArg("-zapwallettxes", "1") != "2")
        {
            CWalletDB walletdb(walletFile);

            BOOST_FOREACH(const CWalletTx& wtxOld, vWtx)
            {
                uint256 hash = wtxOld.GetHash();
                std::map<uint256, CWalletTx>::iterator mi = walletInstance->mapWallet.find(hash);
                if (mi != walletInstance->mapWallet.end())
                {
                    const CWalletTx* copyFrom = &wtxOld;
                    CWalletTx* copyTo = &mi->second;
                    copyTo->mapValue = copyFrom->mapValue;
                    copyTo->vOrderForm = copyFrom->vOrderForm;
                    copyTo->nTimeReceived = copyFrom->nTimeReceived;
                    copyTo->nTimeSmart = copyFrom->nTimeSmart;
                    copyTo->fFromMe = copyFrom->fFromMe;
                    copyTo->strFromAccount = copyFrom->strFromAccount;
                    copyTo->nOrderPos = copyFrom->nOrderPos;
                    walletdb.WriteTx(*copyTo);
                }
            }
        }
    }
    walletInstance->SetBroadcastTransactions(GetBoolArg("-walletbroadcast", DEFAULT_WALLETBROADCAST));
    walletInstance->SetDisableCt(GetBoolArg("-disablect", DEFAULT_DISABLE_CT));

    {
        LOCK(walletInstance->cs_wallet);
        LogPrintf("setKeyPool.size() = %u\n",      walletInstance->GetKeyPoolSize());
        LogPrintf("mapWallet.size() = %u\n",       walletInstance->mapWallet.size());
        LogPrintf("mapAddressBook.size() = %u\n",  walletInstance->mapAddressBook.size());
    }

    return walletInstance;
}

bool CWallet::InitLoadWallet()
{
    if (GetBoolArg("-disablewallet", DEFAULT_DISABLE_WALLET)) {
        pwalletMain = NULL;
        LogPrintf("Wallet disabled!\n");
        return true;
    }

    std::string walletFile = GetArg("-wallet", DEFAULT_WALLET_DAT);

    CWallet * const pwallet = CreateWalletFromFile(walletFile);
    if (!pwallet) {
        return false;
    }
    pwalletMain = pwallet;

    return true;
}

std::atomic<bool> CWallet::fFlushThreadRunning(false);

void CWallet::postInitProcess(boost::thread_group& threadGroup)
{
    // Add wallet transactions that aren't already in a block to mempool
    // Do this here as mempool requires genesis block to be loaded
    ReacceptWalletTransactions();

    // Run a thread to flush wallet periodically
    if (!CWallet::fFlushThreadRunning.exchange(true)) {
        threadGroup.create_thread(ThreadFlushWalletDB);
    }
}

bool CWallet::ParameterInteraction()
{
    if (GetBoolArg("-disablewallet", DEFAULT_DISABLE_WALLET))
        return true;

    if (GetBoolArg("-blocksonly", DEFAULT_BLOCKSONLY) && SoftSetBoolArg("-walletbroadcast", false)) {
        LogPrintf("%s: parameter interaction: -blocksonly=1 -> setting -walletbroadcast=0\n", __func__);
    }

    if (GetBoolArg("-salvagewallet", false) && SoftSetBoolArg("-rescan", true)) {
        // Rewrite just private keys: rescan to find transactions
        LogPrintf("%s: parameter interaction: -salvagewallet=1 -> setting -rescan=1\n", __func__);
    }

    // -zapwallettx implies a rescan
    if (GetBoolArg("-zapwallettxes", false) && SoftSetBoolArg("-rescan", true)) {
        LogPrintf("%s: parameter interaction: -zapwallettxes=<mode> -> setting -rescan=1\n", __func__);
    }

    if (GetBoolArg("-sysperms", false))
        return InitError("-sysperms is not allowed in combination with enabled wallet functionality");
    if (GetArg("-prune", 0) && GetBoolArg("-rescan", false))
        return InitError(_("Rescans are not possible in pruned mode. You will need to use -reindex which will download the whole blockchain again."));

    if (::minRelayTxFee.GetFeePerK() > HIGH_TX_FEE_PER_KB)
        InitWarning(AmountHighWarn("-minrelaytxfee") + " " +
                    _("The wallet will avoid paying less than the minimum relay fee."));

    if (IsArgSet("-mintxfee"))
    {
        CAmount n = 0;
        if (!ParseMoney(GetArg("-mintxfee", ""), n) || 0 == n)
            return InitError(AmountErrMsg("mintxfee", GetArg("-mintxfee", "")));
        if (n > HIGH_TX_FEE_PER_KB)
            InitWarning(AmountHighWarn("-mintxfee") + " " +
                        _("This is the minimum transaction fee you pay on every transaction."));
        CWallet::minTxFee = CFeeRate(n);
    }
    if (IsArgSet("-fallbackfee"))
    {
        CAmount nFeePerK = 0;
        if (!ParseMoney(GetArg("-fallbackfee", ""), nFeePerK))
            return InitError(strprintf(_("Invalid amount for -fallbackfee=<amount>: '%s'"), GetArg("-fallbackfee", "")));
        if (nFeePerK > HIGH_TX_FEE_PER_KB)
            InitWarning(AmountHighWarn("-fallbackfee") + " " +
                        _("This is the transaction fee you may pay when fee estimates are not available."));
        CWallet::fallbackFee = CFeeRate(nFeePerK);
    }
    if (IsArgSet("-paytxfee"))
    {
        CAmount nFeePerK = 0;
        if (!ParseMoney(GetArg("-paytxfee", ""), nFeePerK))
            return InitError(AmountErrMsg("paytxfee", GetArg("-paytxfee", "")));
        if (nFeePerK > HIGH_TX_FEE_PER_KB)
            InitWarning(AmountHighWarn("-paytxfee") + " " +
                        _("This is the transaction fee you will pay if you send a transaction."));

        payTxFee = CFeeRate(nFeePerK, 1000);
        if (payTxFee < ::minRelayTxFee)
        {
            return InitError(strprintf(_("Invalid amount for -paytxfee=<amount>: '%s' (must be at least %s)"),
                                       GetArg("-paytxfee", ""), ::minRelayTxFee.ToString()));
        }
    }
    if (IsArgSet("-maxtxfee"))
    {
        CAmount nMaxFee = 0;
        if (!ParseMoney(GetArg("-maxtxfee", ""), nMaxFee))
            return InitError(AmountErrMsg("maxtxfee", GetArg("-maxtxfee", "")));
        if (nMaxFee > HIGH_MAX_TX_FEE)
            InitWarning(_("-maxtxfee is set very high! Fees this large could be paid on a single transaction."));
        maxTxFee = nMaxFee;
        if (CFeeRate(maxTxFee, 1000) < ::minRelayTxFee)
        {
            return InitError(strprintf(_("Invalid amount for -maxtxfee=<amount>: '%s' (must be at least the minrelay fee of %s to prevent stuck transactions)"),
                                       GetArg("-maxtxfee", ""), ::minRelayTxFee.ToString()));
        }
    }
    nTxConfirmTarget = GetArg("-txconfirmtarget", DEFAULT_TX_CONFIRM_TARGET);
    bSpendZeroConfChange = GetBoolArg("-spendzeroconfchange", DEFAULT_SPEND_ZEROCONF_CHANGE);
    fSendFreeTransactions = GetBoolArg("-sendfreetransactions", DEFAULT_SEND_FREE_TRANSACTIONS);

    if (fSendFreeTransactions && GetArg("-limitfreerelay", DEFAULT_LIMITFREERELAY) <= 0)
        return InitError("Creation of free transactions with their relay disabled is not supported.");

    return true;
}

bool CWallet::BackupWallet(const std::string& strDest)
{
    if (!fFileBacked)
        return false;
    while (true)
    {
        {
            LOCK(bitdb.cs_db);
            if (!bitdb.mapFileUseCount.count(strWalletFile) || bitdb.mapFileUseCount[strWalletFile] == 0)
            {
                // Flush log data to the dat file
                bitdb.CloseDb(strWalletFile);
                bitdb.CheckpointLSN(strWalletFile);
                bitdb.mapFileUseCount.erase(strWalletFile);

                // Copy wallet file
                boost::filesystem::path pathSrc = GetDataDir() / strWalletFile;
                boost::filesystem::path pathDest(strDest);
                if (boost::filesystem::is_directory(pathDest))
                    pathDest /= strWalletFile;

                try {
#if BOOST_VERSION >= 104000
                    boost::filesystem::copy_file(pathSrc, pathDest, boost::filesystem::copy_option::overwrite_if_exists);
#else
                    boost::filesystem::copy_file(pathSrc, pathDest);
#endif
                    LogPrintf("copied %s to %s\n", strWalletFile, pathDest.string());
                    return true;
                } catch (const boost::filesystem::filesystem_error& e) {
                    LogPrintf("error copying %s to %s - %s\n", strWalletFile, pathDest.string(), e.what());
                    return false;
                }
            }
        }
        MilliSleep(100);
    }
    return false;
}

CKeyPool::CKeyPool()
{
    nTime = GetTime();
}

CKeyPool::CKeyPool(const CPubKey& vchPubKeyIn)
{
    nTime = GetTime();
    vchPubKey = vchPubKeyIn;
}

CWalletKey::CWalletKey(int64_t nExpires)
{
    nTimeCreated = (nExpires ? GetTime() : 0);
    nTimeExpires = nExpires;
}

void CMerkleTx::SetMerkleBranch(const CBlockIndex* pindex, int posInBlock)
{
    // Update the tx's hashBlock
    hashBlock = pindex->GetBlockHash();

    // set the position of the transaction in the block
    nIndex = posInBlock;
}

int CMerkleTx::GetDepthInMainChain(const CBlockIndex* &pindexRet) const
{
    if (hashUnset())
        return 0;

    AssertLockHeld(cs_main);

    // Find the block it claims to be in
    BlockMap::iterator mi = mapBlockIndex.find(hashBlock);
    if (mi == mapBlockIndex.end())
        return 0;
    CBlockIndex* pindex = (*mi).second;
    if (!pindex || !chainActive.Contains(pindex))
        return 0;

    pindexRet = pindex;
    return ((nIndex == -1) ? (-1) : 1) * (chainActive.Height() - pindex->nHeight + 1);
}

int CMerkleTx::GetBlocksToMaturity() const
{
    if (!IsCoinBase())
        return 0;
    return max(0, (COINBASE_MATURITY+1) - GetDepthInMainChain());
}


bool CMerkleTx::AcceptToMemoryPool(const CAmount& nAbsurdFee, CValidationState& state)
{
    return ::AcceptToMemoryPool(mempool, state, tx, true, NULL, NULL, false, nAbsurdFee);
}

CKey CWallet::GetBlindingKey(const CScript* script) const
{
    CKey key;

    if (script != NULL) {
        std::map<CScriptID, uint256>::const_iterator it = mapSpecificBlindingKeys.find(CScriptID(*script));
        if (it != mapSpecificBlindingKeys.end()) {
            key.Set(it->second.begin(), it->second.end(), true);
            if (key.IsValid()) {
                return key;
            }
        }
    }

    if (script != NULL && !blinding_derivation_key.IsNull()) {
        unsigned char vch[32];
        CHMAC_SHA256(blinding_derivation_key.begin(), blinding_derivation_key.size()).Write(&((*script)[0]), script->size()).Finalize(vch);
        key.Set(&vch[0], &vch[32], true);
        if (key.IsValid()) {
            return key;
        }
    }

    return CKey();
}

CPubKey CWallet::GetBlindingPubKey(const CScript& script) const
{
    CKey key = GetBlindingKey(&script);
    if (key.IsValid()) {
        return key.GetPubKey();
    }

    return CPubKey();
}

unsigned int CWalletTx::GetPseudoInputOffset(const unsigned int index, const bool fIssuanceToken) const
{
    // There is no mapValue space for null issuances
    assert(fIssuanceToken ? !tx->vin[index].assetIssuance.nInflationKeys.IsNull() : !tx->vin[index].assetIssuance.nAmount.IsNull());
    unsigned int mapValueLoc = 0;
    for (unsigned int i = 0; i < tx->vin.size()*2; i++) {
        if (index == i/2 && (fIssuanceToken ? 1 : 0) == i % 2) {
            break;
        }
        if (!tx->vin[i/2].assetIssuance.IsNull()) {
            if ((i % 2 == 0 && !tx->vin[i/2].assetIssuance.nAmount.IsNull()) ||
                    (i % 2 == 1 && !tx->vin[i/2].assetIssuance.nInflationKeys.IsNull())) {
                mapValueLoc++;
            }
        }
    }
    return mapValueLoc;
}

bool CWallet::LoadSpecificBlindingKey(const CScriptID& scriptid, const uint256& key)
{
    AssertLockHeld(cs_wallet); // mapSpecificBlindingKeys
    mapSpecificBlindingKeys[scriptid] = key;
    return true;
}

bool CWallet::AddSpecificBlindingKey(const CScriptID& scriptid, const uint256& key)
{
    AssertLockHeld(cs_wallet); // mapSpecificBlindingKeys
    if (!LoadSpecificBlindingKey(scriptid, key))
        return false;

    if (!fFileBacked)
        return true;
    return CWalletDB(strWalletFile).WriteSpecificBlindingKey(scriptid, key);
}

void CWallet::ComputeBlindingData(const CConfidentialValue& confValue, const CConfidentialAsset& confAsset, const CConfidentialNonce& nonce, const CScript& scriptPubKey, const std::vector<unsigned char>& vchRangeproof, CAmount& amount, CPubKey& pubkey, uint256& blindingfactor, CAsset& asset, uint256& assetBlindingFactor) const
{
    if (confValue.IsExplicit() && confAsset.IsExplicit()) {
        amount = confValue.GetAmount();
        asset = confAsset.GetAsset();
        pubkey = CPubKey();
        blindingfactor.SetNull();
        assetBlindingFactor.SetNull();
        return;
    }

    CKey blinding_key;
    if ((blinding_key = GetBlindingKey(&scriptPubKey)).IsValid()) {
        // For outputs using derived blinding.
        if (UnblindConfidentialPair(blinding_key, confValue, confAsset, nonce, scriptPubKey, vchRangeproof, amount, blindingfactor,
                asset, assetBlindingFactor)) {
            pubkey = blinding_key.GetPubKey();
            return;
        }
    }

    amount = -1;
    pubkey = CPubKey();
    blindingfactor.SetNull();
    asset.SetNull();
    assetBlindingFactor.SetNull();
}

void CWalletTx::WipeUnknownBlindingData() const
{
    for (unsigned int n = 0; n < tx->vout.size(); n++) {
        if (GetOutputValueOut(n) == -1) {
            mapValue["blindingdata"][138 * n] = 0;
        }
    }
    for (unsigned int n = 0; n < tx->vin.size(); n++) {
        if (!tx->vin[n].assetIssuance.nAmount.IsNull()) {
            if (GetIssuanceAmount(n, false) == -1) {
                mapValue["blindingdata"][138 * (tx->vout.size() + GetPseudoInputOffset(n, false))] = 0;
            }
        }
        if (!tx->vin[n].assetIssuance.nInflationKeys.IsNull()) {
            if (GetIssuanceAmount(n, true) == -1) {
                mapValue["blindingdata"][138 * (tx->vout.size() + GetPseudoInputOffset(n, true))] = 0;
            }
        }
    }
}

std::map<uint256, std::pair<CAsset, CAsset> > CWallet::GetReissuanceTokenTypes() const
{
    std::map<uint256, std::pair<CAsset, CAsset> > tokenMap;
    {
        LOCK2(cs_main, cs_wallet);
        for (map<uint256, CWalletTx>::const_iterator it = mapWallet.begin(); it != mapWallet.end(); ++it)
        {
            const CWalletTx* pcoin = &(*it).second;
            CAsset asset;
            CAsset token;
            uint256 entropy;
            for (unsigned int vinIndex = 0; vinIndex < pcoin->tx->vin.size(); vinIndex++) {
                const CAssetIssuance& issuance = pcoin->tx->vin[vinIndex].assetIssuance;
                if (issuance.IsNull()) {
                    continue;
                }
                // Only looking at initial issuances
                if (!issuance.IsReissuance()) {
                    GenerateAssetEntropy(entropy, pcoin->tx->vin[vinIndex].prevout, issuance.assetEntropy);
                    CalculateAsset(asset, entropy);
                    // TODO handle the case with null nAmount (not decided yet)
                    CalculateReissuanceToken(token, entropy, issuance.nAmount.IsCommitment());
                    tokenMap[entropy] = std::make_pair(token, asset);
                }
            }
        }
    }
    return tokenMap;
}

void CWallet::SetKYCPubKeyIfMine(const CBitcoinAddress& addr, const CPubKey& pubKey){
    isminetype mine = ::IsMine(*this, addr.Get());
    if (mine != ISMINE_NO && addr.IsBlinded() && addr.GetBlindingKey()
        != GetBlindingPubKey(GetScriptForDestination(addr.Get()))) {
        // Note: this will fail to return ismine for deprecated static blinded addresses.
        mine = ISMINE_NO;
    }
    if((mine & ISMINE_SPENDABLE) ? true : false) {
        SetKYCPubKey(pubKey);
    }
}
