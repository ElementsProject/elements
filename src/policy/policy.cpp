// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// NOTE: This file is intended to be customised by the end user,
//       and includes only local node policy logic

#include "policy/policy.h"
#include "validation.h"
#include "issuance.h"

using namespace std;

CAsset policyAsset;
CAsset freezelistAsset;
CAsset burnlistAsset;
CAsset whitelistAsset;
CAsset challengeAsset;
CAsset permissionAsset;
CAsset issuanceAsset;

/**
     * Check transaction inputs to mitigate two
     * potential denial-of-service attacks:
     *
     * 1. scriptSigs with extra data stuffed into them,
     *    not consumed by scriptPubKey (or P2SH script)
     * 2. P2SH scripts with a crazy number of expensive
     *    CHECKSIG/CHECKMULTISIG operations
     *
     * Why bother? To avoid denial-of-service attacks; an attacker
     * can submit a standard HASH... OP_EQUAL transaction,
     * which will get accepted into blocks. The redemption
     * script can be anything; an attacker could use a very
     * expensive-to-check-upon-redemption script like:
     *   DUP CHECKSIG DROP ... repeated 100 times... OP_1
     */

bool IsStandard(const CScript& scriptPubKey, txnouttype& whichType)
{
    std::vector<std::vector<unsigned char> > vSolutions;
    if (!Solver(scriptPubKey, whichType, vSolutions))
        return false;
    if (whichType == TX_MULTISIG)
    {
        unsigned char m = vSolutions.front()[0];
        unsigned char n = vSolutions.back()[0];
        // Support up to x-of-3 multisig txns as standard
        if (n < 1 || n > 3)
            return false;
        if (m < 1 || m > n)
            return false;
    } else if (whichType == TX_LOCKED_MULTISIG) {
        unsigned char m = (*(vSolutions.begin() + 1))[0];
        unsigned char n = vSolutions.back()[0];
        // Support up to x-of-3 multisig txns as standard
        if (n < 1 || n > 3)
            return false;
        if (m < 1 || m > n)
            return false;
    } else if (whichType == TX_NULL_DATA &&
               (!fAcceptDatacarrier || scriptPubKey.size() > nMaxDatacarrierBytes))
          return false;
    else if ( (whichType == TX_REGISTERADDRESS || whichType == TX_DEREGISTERADDRESS) &&
               (!fAcceptRegisteraddress || scriptPubKey.size() > nMaxRegisteraddressBytes))
          return false;
    else if (whichType == TX_TRUE)
        return false;
    return whichType != TX_NONSTANDARD;
}

bool IsStandardTx(const CTransaction& tx, std::string& reason)
{
    if (tx.nVersion > CTransaction::MAX_STANDARD_VERSION || tx.nVersion < 1) {
        reason = "version";
        return false;
    }
    // Extremely large transactions with lots of inputs can cost the network
    // almost as much to process as they cost the sender in fees, because
    // computing signature hashes is O(ninputs*txsize). Limiting transactions
    // to MAX_STANDARD_TX_WEIGHT mitigates CPU exhaustion attacks.
    unsigned int sz = GetTransactionWeight(tx);
    if (sz >= MAX_STANDARD_TX_WEIGHT) {
        reason = "tx-size";
        return false;
    }
    for (CTxIn const &txin : tx.vin)
    {
        if (!txin.scriptSig.IsPushOnly()) {
            reason = "scriptsig-not-pushonly";
            return false;
        }
    }
    txnouttype whichType;
    for (CTxOut const &txout : tx.vout) {
        if (!::IsStandard(txout.scriptPubKey, whichType) && !txout.IsFee()) {
            reason = "scriptpubkey";
            return false;
        }
        if ((whichType == TX_MULTISIG || whichType == TX_LOCKED_MULTISIG) && (!fIsBareMultisigStd)) {
            reason = "bare-multisig";
            return false;
        } else if (txout.nAsset.IsExplicit() && txout.IsDust(dustRelayFee)) {
            reason = "dust";
            return false;
        }
    }
    return true;
}

bool IsSpam(const CTransaction &tx) {
    txnouttype whichType;
    vector<vector<uint8_t>> vSolutions;
    vector<tuple<uint160, CAsset>> addr_asset;
    int num_op_return = 0;
    for (CTxOut const &txout : tx.vout) {
        if (!Solver(txout.scriptPubKey, whichType, vSolutions) || whichType == TX_NULL_DATA) num_op_return++;
        if (num_op_return > 1) return true;
      if (whichType == TX_PUBKEYHASH || whichType == TX_SCRIPTHASH) {
          tuple<uint160, CAsset> aa_pair(uint160(vSolutions[0]), txout.nAsset.GetAsset());
          if (find(addr_asset.begin(), addr_asset.end(), aa_pair) != addr_asset.end()) return true;
          addr_asset.push_back(aa_pair);
      }
  }
  return false;
}

bool IsAllBurn(const CTransaction &tx) {
  txnouttype whichType;
  vector<vector<uint8_t>> vSolutions;
  for (CTxOut const &txout : tx.vout)
    if (!Solver(txout.scriptPubKey, whichType, vSolutions) ||
        whichType != TX_NULL_DATA)
      return false;
  return true;
}

bool IsAnyBurn(const CTransaction &tx) {
  txnouttype whichType;
  vector<vector<uint8_t>> vSolutions;
  for (CTxOut const &txout : tx.vout) {
    if(Solver(txout.scriptPubKey, whichType, vSolutions)) {
      if ((whichType == TX_NULL_DATA || whichType == TX_REGISTERADDRESS || whichType == TX_DEREGISTERADDRESS) && txout.nValue.GetAmount() != 0) return true;
    } else {
      return true;
    }
  }
  return false;
}

// @fn IsPolicy.
// @brief determines if any outputs of a transaction are policy assets.
// @param[in] class that contains the transaction.
// @retrun true == successful process.
// @retrun false == failed process.
bool IsPolicy(CTransaction const &tx) {
    for (CTxOut const &txout : tx.vout)
        if (IsPolicy(txout.nAsset.GetAsset()))
            return true;
    return false;
}

// @fn IsAllPolicy.
// @brief determines if all outputs of a transaction are policy assets.
// @param[in] class that contains the transaction.
// @retrun true == successful process.
// @retrun false == failed process.
bool IsAllPolicy(CTransaction const &tx) {
    for (CTxOut const &txout : tx.vout)
        if (!IsPolicy(txout.nAsset.GetAsset()))
            return false;
    return true;
}

bool IsWhitelistAssetOnly(vector<CTxOut> const &vout){
  for (CTxOut const &txout : vout)
    if (!IsWhitelistAsset(txout))
      return false;
  return true;
}

bool IsWhitelistAssetOnly(CTransaction const &tx){
  return IsWhitelistAssetOnly(tx.vout);
}

bool IsWhitelistAsset(CTxOut const &out){
  return IsWhitelistAsset(out.nAsset.GetAsset());
}

bool IsWhitelistAsset(CAsset const &asset){
  return (asset == whitelistAsset);
}

bool IsPermissionAsset(CAsset const &asset){
  return (asset == permissionAsset);
}

bool IsPolicy(const CAsset& asset){
    if (asset == freezelistAsset ||
        asset == burnlistAsset ||
        asset == whitelistAsset ||
        asset == challengeAsset ||
        asset == permissionAsset ||
        asset == issuanceAsset)
        return true;
    return false;
}

bool IsContractInTx(CTransaction const &tx) {
  txnouttype whichType;
  uint256 contract = chainActive.Tip() ? chainActive.Tip()->hashContract : GetContractHash();

  for (CTxOut const &txout : tx.vout) {
    opcodetype opcode;
    std::vector<unsigned char> bytes;
    vector<vector<uint8_t>> vSolutions;
    if (!Solver(txout.scriptPubKey, whichType, vSolutions))
      return false;
    if(whichType == TX_NULL_DATA) {
      CScript::const_iterator pc = txout.scriptPubKey.begin();
      if (!txout.scriptPubKey.GetOp(++pc, opcode, bytes)) continue;
      if(bytes.size() == 32) {
        uint256 data(bytes);
        if(data == contract) return true;
      }
    }
  }
  return false;
}

// @fn IsWhitelisted
// @brief determines that all outputs of a transaction are P2PKH,
//        all output addresses must be in the whitelist database.
// @param[in] class that contains the transaction.
// @brief Processing.
//        Skip whitelist check if issuance transaction.
//        Skip whitelist check if output is TX_FEE.
//        Skip whitelist check if output is OP_RETURN.
//        Search in whitelist for the presence of each output address,
//        return false if not found.
// @retrun true == successful process.
// @retrun false == failed process.
bool IsWhitelisted(CTransaction const &tx) {
    txnouttype whichType;

    uint160 frzInt;
    frzInt.SetHex("0x0000000000000000000000000000000000000000");
    for (CTxOut const &txout : tx.vout) {
        vector<vector<uint8_t>> vSolutions;
        if (!Solver(txout.scriptPubKey, whichType, vSolutions))
            return false;
        // skip whitelist check if issuance transaction
        // skip whitelist check if output is TX_FEE
        // skip whitelist check if output is OP_RETURN
    // skip whitelist check if output is OP_REGISTERADDRESS or OP_DEREGISTERADDRESS
        if (!tx.vin[0].assetIssuance.IsNull() || whichType == TX_FEE ||
        whichType == TX_NULL_DATA || whichType == TX_REGISTERADDRESS || whichType == TX_DEREGISTERADDRESS )
            continue;
        // return false if not P2PKH or P2SH
        if (whichType == TX_PUBKEYHASH) {
            CKeyID keyId;
            keyId = CKeyID(uint160(vSolutions[0]));
            // Search in whitelist for the presence of each output address.
            // If one is not found, return false.
    if (!addressWhitelist->is_whitelisted(keyId) && uint160(vSolutions[0]) != frzInt)
                return false;
        } else if (whichType == TX_SCRIPTHASH) {
            CScriptID keyId;
            keyId = CScriptID(uint160(vSolutions[0]));
            // Search in whitelist for the presence of each output address.
            // If one is not found, return false.
            if (!addressWhitelist->is_whitelisted(keyId) && uint160(vSolutions[0]) != frzInt)
                return false;
        } else {
            return false;
        }
    }
    return true;
}
// @fn IsRedemption.
// @brief check if the transaction is tagged as a redemption transaction.
// @param[in] class that contains the transaction.
// @retrun true == successful process.
// @retrun false == failed process.
bool IsRedemption(CTransaction const &tx) {
  txnouttype whichType;
  vector<vector<uint8_t>> vSolutions;
  for (uint32_t itr = 0; itr < tx.vout.size(); ++itr) {
    if (Solver(tx.vout[itr].scriptPubKey, whichType, vSolutions)) {
      if (whichType == TX_FEE || whichType == TX_REGISTERADDRESS || whichType == TX_DEREGISTERADDRESS)
        continue;
      //set freeze-flag key
      uint160 frzInt;
      frzInt.SetHex("0x0000000000000000000000000000000000000000");
      if (whichType == TX_PUBKEYHASH && uint160(vSolutions[0]) == frzInt) {
        return true;
      }
    } else
      return false;
  }
  return false;
}

bool IsRedemptionListed(CTransaction const &tx) {
  CKeyID keyId;
  txnouttype whichType;
  for (CTxOut const &txout : tx.vout) {
    vector<vector<uint8_t>> vSolutions;
    if (!Solver(txout.scriptPubKey, whichType, vSolutions))
      return false;
    // skip op_return
    if (whichType == TX_NULL_DATA) continue;
    // return false if not P2PKH
    if (whichType == TX_PUBKEYHASH) {
      CKeyID keyId;
      keyId = CKeyID(uint160(vSolutions[0]));
      // Search in whitelist for the presence of each output address.
      // If one is not found, return false.
      if(uint160(vSolutions[0]).IsNull()) continue;
      if (!addressFreezelist.find(keyId)) return false;
    } else {
      return false;
    }
  }
  return true;
}

bool IsFreezelisted(CTransaction const &tx, CCoinsViewCache const &mapInputs) {
  if (tx.IsCoinBase())
    return false; // Coinbases don't use vin normally
  //function that determines if any input pubkeys are on the freezelist
  for (uint32_t itr = 0; itr < tx.vin.size(); ++itr) {
    CTxOut const &prev = mapInputs.GetOutputFor(tx.vin[itr]);
    vector<vector<uint8_t>> vSolutions;
    txnouttype whichType;
    CScript const &prevScript = prev.scriptPubKey;
    if (!Solver(prevScript, whichType, vSolutions))
      return false;
    if (whichType == TX_PUBKEYHASH) {
      CKeyID keyId = CKeyID(uint160(vSolutions[0]));
      // search in freezelist for the presence of keyid
      if (!addressFreezelist.find(keyId)) return false;
    } else if (whichType == TX_FEE || whichType == TX_REGISTERADDRESS || whichType == TX_DEREGISTERADDRESS) {
      continue;
     } else {
      return false;
    }
  }
  return true;
}

bool IsBurnlisted(const CTransaction& tx, const CCoinsViewCache& mapInputs)
{
    //are input pubkeys are on the burn list
    if(tx.vin.size() != 1) return false;
    const CTxOut& prev = mapInputs.GetOutputFor(tx.vin[0]);
    std::vector<std::vector<unsigned char> > vSolutions;
    txnouttype whichType;
    const CScript& prevScript = prev.scriptPubKey;
    if (!Solver(prevScript, whichType, vSolutions))
        return false;
    if (whichType == TX_PUBKEYHASH) {
        CKeyID keyId;
        keyId = CKeyID(uint160(vSolutions[0]));
        // search in freezelist for the presence of keyid
        if (addressBurnlist.find(keyId)) return true;
    }
  return false;
}

bool UpdateFreezeList(const CTransaction& tx, const CCoinsViewCache& mapInputs)
{
    if (tx.IsCoinBase())
      return false; // Coinbases don't use vin normally
    // check inputs for encoded address data
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxOut& prev = mapInputs.GetOutputFor(tx.vin[i]);
        std::vector<std::vector<unsigned char> > vSolutions;
        txnouttype whichType;
        const CScript& prevScript = prev.scriptPubKey;
        if (!Solver(prevScript, whichType, vSolutions))
          continue;
        // extract address from second multisig public key and remove from freezelist
        // encoding: 33 byte public key: address is encoded in the last 20 bytes (i.e. byte 14 to 33)
        if (whichType == TX_MULTISIG && vSolutions.size() == 4)
        {
            CKeyID keyId;
            std::vector<unsigned char> ex_addr;
            std::vector<unsigned char>::const_iterator first = vSolutions[2].begin() + 13;
            std::vector<unsigned char>::const_iterator last = vSolutions[2].begin() + 33;
            std::vector<unsigned char> extracted_addr(first, last);
            keyId = CKeyID(uint160(extracted_addr));
            addressFreezelist.remove(keyId);
            LogPrintf("POLICY: removed address from freeze-list "+CBitcoinAddress(keyId).ToString()+"\n");
        }
    }
    //check outputs for encoded address data
    for (unsigned int i = 0; i < tx.vout.size(); i++) {
        const CTxOut& txout = tx.vout[i];
        std::vector<std::vector<unsigned char> > vSolutions;
        txnouttype whichType;
        if (!Solver(txout.scriptPubKey, whichType, vSolutions))
          continue;
        // extract address from second multisig public key and add to the freezelist
        // encoding: 33 byte public key: address is encoded in the last 20 bytes (i.e. byte 14 to 33)
        if (whichType == TX_MULTISIG && vSolutions.size() == 4)
        {
            CKeyID keyId;
            std::vector<unsigned char> ex_addr;
            std::vector<unsigned char>::const_iterator first = vSolutions[2].begin() + 13;
            std::vector<unsigned char>::const_iterator last = vSolutions[2].begin() + 33;
            std::vector<unsigned char> extracted_addr(first,last);
            keyId = CKeyID(uint160(extracted_addr));
            addressFreezelist.add_sorted(keyId);
            LogPrintf("POLICY: added address to freeze-list "+CBitcoinAddress(keyId).ToString()+"\n");
        }
    }
    return true;
}

bool UpdateBurnList(const CTransaction& tx, const CCoinsViewCache& mapInputs)
{
    if (tx.IsCoinBase())
      return false; // Coinbases don't use vin normally
    // check inputs for encoded address data
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxOut& prev = mapInputs.GetOutputFor(tx.vin[i]);
        std::vector<std::vector<unsigned char> > vSolutions;
        txnouttype whichType;
        const CScript& prevScript = prev.scriptPubKey;
        if (!Solver(prevScript, whichType, vSolutions))
          continue;
        // extract address from second multisig public key and remove from freezelist
        // encoding: 33 byte public key: address is encoded in the last 20 bytes (i.e. byte 14 to 33)
        if (whichType == TX_MULTISIG && vSolutions.size() == 4)
        {
            CKeyID keyId;
            std::vector<unsigned char> ex_addr;
            std::vector<unsigned char>::const_iterator first = vSolutions[2].begin() + 13;
            std::vector<unsigned char>::const_iterator last = vSolutions[2].begin() + 33;
            std::vector<unsigned char> extracted_addr(first,last);
            keyId = CKeyID(uint160(extracted_addr));
            addressBurnlist.remove(keyId);
            LogPrintf("POLICY: removed address from burn-list "+CBitcoinAddress(keyId).ToString()+"\n");
        }
    }
    //check outputs for encoded address data
    for (unsigned int i = 0; i < tx.vout.size(); i++) {
        const CTxOut& txout = tx.vout[i];
        std::vector<std::vector<unsigned char> > vSolutions;
        txnouttype whichType;
        if (!Solver(txout.scriptPubKey, whichType, vSolutions))
          continue;
        // extract address from second multisig public key and add to the freezelist
        // encoding: 33 byte public key: address is encoded in the last 20 bytes (i.e. byte 14 to 33)
        if (whichType == TX_MULTISIG && vSolutions.size() == 4)
        {
            CKeyID keyId;
            std::vector<unsigned char> ex_addr;
            std::vector<unsigned char>::const_iterator first = vSolutions[2].begin() + 13;
            std::vector<unsigned char>::const_iterator last = vSolutions[2].begin() + 33;
            std::vector<unsigned char> extracted_addr(first,last);
            keyId = CKeyID(uint160(extracted_addr));
            addressBurnlist.add_sorted(keyId);
            LogPrintf("POLICY: added address to burn-list "+CBitcoinAddress(keyId).ToString()+"\n");
        }
    }
    return true;
}

bool IsValidIssuance(const CTransaction &tx, const CCoinsViewCache &view, std::string &reason)
{
    const CAssetIssuance &issuance = tx.vin[0].assetIssuance;
    if (!issuance.IsNull() && !issuance.IsReissuance()) {
        const CTxOut &prev = view.GetOutputFor(tx.vin[0]);
        if (prev.nAsset.GetAsset() != issuanceAsset) {
            reason = "non-issuance-asset";
            return false;
        }
        if (fRequireWhitelistCheck) {
            txnouttype whichType;
            vector<vector<uint8_t>> vSolutions;
            bool fWhitelisted = false;
            if (Solver(tx.vout[0].scriptPubKey, whichType, vSolutions) && whichType == TX_PUBKEYHASH) {
                CKeyID keyId;
                keyId = CKeyID(uint160(vSolutions[0]));
                fWhitelisted = addressWhitelist->is_whitelisted(keyId);
            }
            if (!fWhitelisted) {
                reason = "non-whitelisted-address";
                return false;
            }
        }
    }
    return true;
}

bool GetRequest(const CTxOut &out, uint256 hash, uint32_t nConfirmedHeight, CRequest &request)
{
    vector<vector<unsigned char>> vSolutions;
    txnouttype whichType;
    if (Solver(out.scriptPubKey, whichType, vSolutions) && whichType == TX_LOCKED_MULTISIG) {
        request = CRequest::FromSolutions(vSolutions, nConfirmedHeight);
        return true;
    }
    return false;
}

bool IsValidRequest(const CRequest &request, uint32_t nHeight)
{
    return request.nEndBlockHeight > nHeight;
}

bool UpdateRequestList(const CTransaction& tx, uint32_t nHeight)
{
    if (tx.IsCoinBase() || tx.vout.size() != 1)
        return false;
    // confirmed height will be the next height
    return requestList.LoadRequest(tx.vout[0], tx.GetHash(), nHeight, nHeight + 1);
}

bool GetRequestBid(const vector<CTxOut> &outs, uint256 hash, uint32_t nConfirmedHeight, CBid &bid)
{
    txnouttype whichType;
    vector<vector<unsigned char>> vSolutions;
    for (const auto &out : outs) {
        if (out.nAsset.IsExplicit() && !IsPolicy(out.nAsset.GetAsset())
        && Solver(out.scriptPubKey, whichType, vSolutions) && whichType == TX_LOCKED_MULTISIG) {
            bid = CBid::FromSolutions(vSolutions, out.nValue.GetAmount(), nConfirmedHeight);
            bid.SetBidHash(hash);
            return true;
        }
    }
    return false;
}

bool IsValidRequestBid(const CRequest &request, const CBid &bid)
{
    // amount less than current auction price
    if (bid.nStakePrice < request.GetAuctionPrice(bid.nConfirmedBlockHeight))
        return false;
    // stake lock expires before request end
    if (request.nEndBlockHeight > bid.nLockBlockHeight)
        return false;
    // auction finished
    if (request.nStartBlockHeight <= bid.nConfirmedBlockHeight)
        return false;

    return true;
}

bool UpdateRequestBidList(const CTransaction& tx, uint32_t nHeight)
{
    if (tx.IsCoinBase() || tx.vout.size() == 1)
        return false;
    return requestList.LoadBid(tx.vout, tx.GetHash(), nHeight + 1);
}

bool UpdateAssetMap(const CTransaction& tx)
{
    if(!tx.vin[0].assetIssuance.IsNull()){
        if(!tx.vin[0].assetIssuance.IsReissuance()) {
            IssuanceData newIssuance;

            uint256 entropy;
            GenerateAssetEntropy(entropy, tx.vin[0].prevout, tx.vin[0].assetIssuance.assetEntropy);
            newIssuance.entropy = entropy;

            CAsset asset;
            CalculateAsset(asset, entropy);
            CAsset token;
            CalculateReissuanceToken(token, entropy, false);
            newIssuance.token = token.id;
            newIssuance.asset = asset;

            assetEntropyMap.push_back(newIssuance);
        }
    }
  return true;
}

void UpdateFreezeHistory(const CTransaction& tx, uint32_t bheight)
{
    //is the transaction a redemption transaction
    txnouttype whichType;
    bool isfrz = false;
    for (uint32_t itr = 0; itr < tx.vout.size(); ++itr) {
        vector<vector<uint8_t>> vSolutions;
        if (Solver(tx.vout[itr].scriptPubKey, whichType, vSolutions)) {
            if (whichType == TX_PUBKEYHASH && uint160(vSolutions[0]).IsNull()) isfrz = true;
        }
    }
    //if a redemption/freeze transaction then add outputs to the history list
    uint256 txhash = tx.GetHash();
    if(isfrz) {
        FreezeHist histEntry;
        for (uint32_t itr = 0; itr < tx.vout.size(); ++itr) {
            vector<vector<uint8_t>> vSolutions;
            if (Solver(tx.vout[itr].scriptPubKey, whichType, vSolutions)) {
                if (whichType == TX_PUBKEYHASH && !uint160(vSolutions[0]).IsNull()) {
                    histEntry.txid = txhash;
                    histEntry.vout = itr;
                    histEntry.asset = tx.vout[itr].nAsset.GetAsset();
                    histEntry.freezeheight = bheight;
                    histEntry.spendheight = 0;
                    histEntry.value = tx.vout[itr].nValue.GetAmount();

                    if(std::find(freezeHistList.begin(), freezeHistList.end(), histEntry)==freezeHistList.end()) {
                        freezeHistList.push_back(histEntry);
                    }
                }
            }
        }
    // else check if any inputs txids are already on the history list
    }
    //loop over tx inputs
    for (uint32_t itr = 0; itr < tx.vin.size(); ++itr) {
    //for each input, check if the outpoint is in the history list
        for (uint32_t itr2 = 0; itr2 < freezeHistList.size(); ++itr2) {
            if(tx.vin[itr].prevout.n == freezeHistList[itr2].vout && tx.vin[itr].prevout.hash == freezeHistList[itr2].txid) {
                //if not burn, add spend-height
                if(!IsAnyBurn(tx)) {
                    freezeHistList[itr2].spendheight = bheight;
                }
            }
        }
    }
}

bool LoadFreezeList(CCoinsView *view)
{
    std::unique_ptr<CCoinsViewCursor> pcursor(view->Cursor());
    CHashWriter ss(SER_GETHASH, PROTOCOL_VERSION);
    uint256 hashBlock = pcursor->GetBestBlock();
    {
        LOCK(cs_main);
    }
    ss << hashBlock;
    //main loop over coins (transactions with > 0 unspent outputs
    while (pcursor->Valid()) {
        boost::this_thread::interruption_point();
        uint256 key;
        CCoins coins;
        if (pcursor->GetKey(key) && pcursor->GetValue(coins)) {
            ss << key;
            //loop over all vouts within a single transaction
            for (unsigned int i=0; i<coins.vout.size(); i++) {
                const CTxOut &out = coins.vout[i];
                //null vouts are spent
                if (!out.IsNull()) {
                    ss << VARINT(i+1);
                    ss << out;
                if (out.nAsset.GetAsset() == freezelistAsset) {
                    std::vector<std::vector<unsigned char> > vSolutions;
                    txnouttype whichType;
                    if (!Solver(out.scriptPubKey, whichType, vSolutions))
                      continue;

                    // extract address from second multisig public key and add to the freezelist
                    // encoding: 33 byte public key: address is encoded in the last 20 bytes (i.e. byte 14 to 33)
                    if (whichType == TX_MULTISIG && vSolutions.size() == 4)
                    {
                        CKeyID keyId;
                        std::vector<unsigned char> ex_addr;
                        std::vector<unsigned char>::const_iterator first = vSolutions[2].begin() + 13;
                        std::vector<unsigned char>::const_iterator last = vSolutions[2].begin() + 33;
                        std::vector<unsigned char> extracted_addr(first,last);
                        keyId = CKeyID(uint160(extracted_addr));
                        addressFreezelist.add_sorted(keyId);
                        LogPrintf("POLICY: added address to freeze-list "+CBitcoinAddress(keyId).ToString()+"\n");
                    }
                }
            }
            }
        ss << VARINT(0);
    } else {
      return error("%s: unable to read value", __func__);
    }
    pcursor->Next();
    }
    return true;
}

bool LoadBurnList(CCoinsView *view)
{
    std::unique_ptr<CCoinsViewCursor> pcursor(view->Cursor());
    CHashWriter ss(SER_GETHASH, PROTOCOL_VERSION);
    uint256 hashBlock = pcursor->GetBestBlock();
    {
        LOCK(cs_main);
    }
    ss << hashBlock;
    //main loop over coins (transactions with > 0 unspent outputs
    while (pcursor->Valid()) {
        boost::this_thread::interruption_point();
        uint256 key;
        CCoins coins;
        if (pcursor->GetKey(key) && pcursor->GetValue(coins)) {
            ss << key;

            //loop over all vouts within a single transaction
            for (unsigned int i=0; i<coins.vout.size(); i++) {
                const CTxOut &out = coins.vout[i];
                //null vouts are spent
                if (!out.IsNull()) {
                    ss << VARINT(i+1);
                    ss << out;
                    if (out.nAsset.GetAsset() == burnlistAsset) {
                        std::vector<std::vector<unsigned char> > vSolutions;
                        txnouttype whichType;
                        if (!Solver(out.scriptPubKey, whichType, vSolutions)) continue;
                        // extract address from second multisig public key and add to the freezelist
                        // encoding: 33 byte public key: address is encoded in the last 20 bytes (i.e. byte 14 to 33)
                        if (whichType == TX_MULTISIG && vSolutions.size() == 4)
                        {
                            CKeyID keyId;
                            std::vector<unsigned char> ex_addr;
                            std::vector<unsigned char>::const_iterator first = vSolutions[2].begin() + 13;
                            std::vector<unsigned char>::const_iterator last = vSolutions[2].begin() + 33;
                            std::vector<unsigned char> extracted_addr(first,last);
                            keyId = CKeyID(uint160(extracted_addr));
                            addressBurnlist.add_sorted(keyId);
                            LogPrintf("POLICY: added address to burn-list "+CBitcoinAddress(keyId).ToString()+"\n");
                        }
                    }
                }
            }
        ss << VARINT(0);
    } else {
      return error("%s: unable to read value", __func__);
    }
    pcursor->Next();
    }
    return true;
}

bool AreInputsStandard(const CTransaction& tx, const CCoinsViewCache& mapInputs)
{
    if (tx.IsCoinBase())
        return true; // Coinbases don't use vin normally
    for (unsigned int i = 0; i < tx.vin.size(); i++)
    {
        if (tx.vin[i].m_is_pegin) {
            // This deals with p2sh in general only
            continue;
        }
        const CTxOut& prev = mapInputs.GetOutputFor(tx.vin[i]);
        // Biggest 'standard' txin is a 15-of-15 P2SH multisig with compressed
        // keys. (remember the 520 byte limit on redeemScript size) That works
        // out to a (15*(33+1))+3=513 byte redeemScript, 513+1+15*(73+1)+3=1627
        // bytes of scriptSig, which we round off to 1650 bytes for some minor
        // future-proofing. That's also enough to spend a 20-of-20
        // CHECKMULTISIG scriptPubKey, though such a scriptPubKey is not
        // considered standard)
        if (tx.vin[i].scriptSig.size() > 1650)
            return false;
        std::vector<std::vector<unsigned char> > vSolutions;
        txnouttype whichType;
        // get the scriptPubKey corresponding to this input:
        const CScript& prevScript = prev.scriptPubKey;
        if (!Solver(prevScript, whichType, vSolutions))
            return false;
        if (whichType == TX_SCRIPTHASH)
        {
            std::vector<std::vector<unsigned char> > stack;
            // convert the scriptSig into a stack, so we can inspect the redeemScript
            if (!EvalScript(stack, tx.vin[i].scriptSig, SCRIPT_VERIFY_NONE, BaseSignatureChecker(), SIGVERSION_BASE))
                return false;
            if (stack.empty())
                return false;
            CScript subscript(stack.back().begin(), stack.back().end());
            if (subscript.GetSigOpCount(true) > MAX_P2SH_SIGOPS) {
                return false;
            }
        }
    }
    return true;
}

bool IsWitnessStandard(const CTransaction& tx, const CCoinsViewCache& mapInputs)
{
    if (tx.IsCoinBase())
        return true; // Coinbases are skipped
    for (unsigned int i = 0; i < tx.vin.size(); i++)
    {
        // We don't care if witness for this input is empty, since it must not be bloated.
        // If the script is invalid without witness, it would be caught sooner or later during validation.
        if (tx.wit.vtxinwit.size() <= i || tx.wit.vtxinwit[i].scriptWitness.IsNull())
            continue;
        const CTxOut &prev = tx.vin[i].m_is_pegin ? GetPeginOutputFromWitness(tx.wit.vtxinwit[i].m_pegin_witness) :  mapInputs.GetOutputFor(tx.vin[i]);
        // get the scriptPubKey corresponding to this input:
        CScript prevScript = prev.scriptPubKey;
        if (prevScript.IsPayToScriptHash()) {
            std::vector <std::vector<unsigned char> > stack;
            // If the scriptPubKey is P2SH, we try to extract the redeemScript casually by converting the scriptSig
            // into a stack. We do not check IsPushOnly nor compare the hash as these will be done later anyway.
            // If the check fails at this stage, we know that this txid must be a bad one.
            if (!EvalScript(stack, tx.vin[i].scriptSig, SCRIPT_VERIFY_NONE, BaseSignatureChecker(), SIGVERSION_BASE))
                return false;
            if (stack.empty())
                return false;
            prevScript = CScript(stack.back().begin(), stack.back().end());
        }
        int witnessversion = 0;
        std::vector<unsigned char> witnessprogram;
        // Non-witness program must not be associated with any witness
        if (!prevScript.IsWitnessProgram(witnessversion, witnessprogram))
            return false;
        // Check P2WSH standard limits
        if (witnessversion == 0 && witnessprogram.size() == 32) {
            if (tx.wit.vtxinwit[i].scriptWitness.stack.back().size() > MAX_STANDARD_P2WSH_SCRIPT_SIZE)
                return false;
            size_t sizeWitnessStack = tx.wit.vtxinwit[i].scriptWitness.stack.size() - 1;
            if (sizeWitnessStack > MAX_STANDARD_P2WSH_STACK_ITEMS)
                return false;
            for (unsigned int j = 0; j < sizeWitnessStack; j++) {
                if (tx.wit.vtxinwit[i].scriptWitness.stack[j].size() > MAX_STANDARD_P2WSH_STACK_ITEM_SIZE)
                    return false;
            }
        }
    }
    return true;
}

CFeeRate incrementalRelayFee = CFeeRate(DEFAULT_INCREMENTAL_RELAY_FEE);
CFeeRate dustRelayFee = CFeeRate(DUST_RELAY_TX_FEE);
unsigned int nBytesPerSigOp = DEFAULT_BYTES_PER_SIGOP;

int64_t GetVirtualTransactionSize(int64_t nWeight, int64_t nSigOpCost)
{
    return (std::max(nWeight, nSigOpCost * nBytesPerSigOp) + WITNESS_SCALE_FACTOR - 1) / WITNESS_SCALE_FACTOR;
}

int64_t GetVirtualTransactionSize(const CTransaction& tx, int64_t nSigOpCost)
{
    return GetVirtualTransactionSize(GetTransactionWeight(tx), nSigOpCost);
}
