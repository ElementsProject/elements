// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chain.h"
#include "whitelist.h"
#include "validation.h"
#ifdef ENABLE_WALLET
#endif
#include "ecies_hex.h"
#include "policy/policy.h"
#include "rpc/server.h"
#include "random.h"
#include <fstream>
#include <iostream>

CWhiteList::CWhiteList(){
  _asset=whitelistAsset;
  //The written code behaviour expects nMultisigSize to be of length 1 at the moment. If it is changed in the future the code needs to be adjusted accordingly.
  assert(nMultisigSize == 1);
}

CWhiteList::~CWhiteList(){;}

void CWhiteList::init_defaults(){
  if (fRequireWhitelistCheck || fScanWhitelist) {
    const CChainParams& chainparams = Params();
    if (chainparams.GetConsensus().mandatory_coinbase_destination != CScript()){
      CTxDestination man_con_dest;
      if(ExtractDestination(chainparams.GetConsensus().mandatory_coinbase_destination, man_con_dest)){
	if(!is_whitelisted(man_con_dest)){
	    try{
	      add_destination(man_con_dest); 
	    } catch (std::invalid_argument e){
	      LogPrintf(std::string("Error adding coinbase destination to whitelist: ") + std::string(e.what()) + "\n");
	    }
	}
	}
      }
    }
}

bool CWhiteList::Load(CCoinsView *view)
{
    CCoinsViewCache coins(view);
    std::unique_ptr<CCoinsViewCursor> pcursor(coins.Cursor());
    LOCK(cs_main);

      //main loop over coins (transactions with > 0 unspent outputs
    while (pcursor->Valid()) {
      boost::this_thread::interruption_point();
      uint256 key;
      CCoins coins;
      if (!(pcursor->GetKey(key) && pcursor->GetValue(coins))) 
        return error("%s: unable to read value", __func__);
             
      //loop over all vouts within a single transaction
      for (unsigned int i=0; i<coins.vout.size(); i++) {
        const CTxOut &out = coins.vout[i];
        //null vouts are spent
        if (!out.IsNull() && (out.nAsset.GetAsset() == _asset)) {
          std::vector<std::vector<unsigned char> > vSolutions;
          txnouttype whichType;
        
          if (!Solver(out.scriptPubKey, whichType, vSolutions)) 
            continue;
              
          // extract address from second multisig public key and add to the freezelist
          // encoding: 33 byte public key: address is encoded in the last 20 bytes (i.e. byte 14 to 33)
          if (whichType == TX_MULTISIG && vSolutions.size() == 4){
            std::vector<unsigned char> vKycPub(vSolutions[2].begin(), vSolutions[2].begin() + 33);
            //The last bytes of the KYC public key are
            //in reverse to prevent spending, 
            std::reverse(vKycPub.begin() + 3, vKycPub.end());
            CPubKey kycPubKey(vKycPub.begin(), vKycPub.end());
            if (!kycPubKey.IsFullyValid()) {
              //  LogPrintf("POLICY: not adding invalid KYC pub key"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
            } else {
              //LogPrintf("POLICY: added unassigned KYC pub key "+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
              COutPoint outPoint(key, i);
              add_unassigned_kyc(kycPubKey, outPoint);
            }
          } else if ((whichType == TX_REGISTERADDRESS || 
                      whichType == TX_DEREGISTERADDRESS)
                      &! fReindex &! fReindexChainState ) {
            ParseRegisterAddressOutput(out, whichType == TX_DEREGISTERADDRESS);
          }
        }
      }
      pcursor->Next();
    }

  sync_whitelist_wallet();

  return true;
}

//Modifies a vector of the kyc public keys whose private keys were not found in the wallet.
void CWhiteList::sync_whitelist_wallet(std::vector<CPubKey>& keysNotFound){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);  
  #ifndef ENABLE_WALLET
    return false;
  #endif
  LOCK2(cs_main, pwalletMain->cs_wallet);
  EnsureWalletIsUnlocked();
  keysNotFound.clear();
  int nTries = 0;
  int nKeys = _kycUnassignedSet.size();
  int nTriesMax = MAX_KYCPUBKEY_GAP + nKeys;
  bool bKeyFound = true;
  for(auto key : _kycUnassignedSet){
    bKeyFound=true;
    CKeyID kycKey=key.GetID();
    CKey privKey;
    while(!pwalletMain->GetKey(kycKey, privKey)){
      pwalletMain->GenerateNewKey(true);
      if(++nTries > nTriesMax){
        keysNotFound.push_back(key);
        bKeyFound=false;
        break;
      }
    }
    //Reset the gap if a key was found.
    if(bKeyFound) nTries=std::min(nTries, nKeys);
  }
}

void CWhiteList::sync_whitelist_wallet(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);  
  std::vector<CPubKey> keysNotFound;
  sync_whitelist_wallet(keysNotFound);
}
  

void CWhiteList::add_destination(const CTxDestination& dest){
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);  
    if (dest.which() == ((CTxDestination)CNoDestination()).which()){
        throw std::invalid_argument(std::string(std::string(__func__) + 
        ": invalid destination"));
    }   
    add_sorted(dest);
}

void CWhiteList::add_derived(const CBitcoinAddress& address, const CPubKey& pubKey, 
        const std::unique_ptr<CPubKey>& kycPubKey){
    add_derived(address, pubKey);
}

void CWhiteList::add_derived(const CBitcoinAddress& address, const CPubKey& pubKey){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if (!pubKey.IsFullyValid()) 
    throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid public key"));

    //Will throw an error if address is not a valid derived address.
  CTxDestination keyId;
  keyId = address.Get();
  
  if (keyId.which() == ((CTxDestination)CNoDestination()).which())
      throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid key id"));

  if(!Params().ContractInTx() && !Consensus::CheckValidTweakedAddress(keyId, pubKey))
     throw std::invalid_argument(std::string(std::string(__func__) + 
      ": address does not derive from public key when tweaked with contract hash"));

 //insert new address into sorted CWhiteList vector
  add_sorted(keyId);
}

void CWhiteList::add_derived(const std::string& sAddress, const std::string& sPubKey, 
        const std::string& sKYCPubKey){
    add_derived(sAddress, sPubKey);
}

void CWhiteList::add_derived(const std::string& sAddress, const std::string& sPubKey){
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    CBitcoinAddress address;
  if (!address.SetString(sAddress))
    throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid Bitcoin address: ") + sAddress);
  
  std::vector<unsigned char> pubKeyData(ParseHex(sPubKey));
  CPubKey pubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());

  std::unique_ptr<CPubKey> kycPubKey(new CPubKey());
  add_derived(address, pubKey);
}

void CWhiteList::add_multisig_whitelist(const CBitcoinAddress& address, const std::vector<CPubKey>& pubKeys, 
        const std::unique_ptr<CPubKey>& kycPubKey, const uint8_t nMultisig){
    add_multisig_whitelist(address, pubKeys, nMultisig);
}

void CWhiteList::add_multisig_whitelist(const CBitcoinAddress& address, const std::vector<CPubKey>& pubKeys, 
  const uint8_t nMultisig){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);

  for(unsigned int i = 0; i < pubKeys.size(); ++i) {
    if (!pubKeys[i].IsFullyValid()) 
      throw std::invalid_argument(std::string(std::string(__func__) + 
        ": invalid public key"));
  }
  
  //Will throw an error if address is not a valid derived address.
  CTxDestination keyId;
  keyId = address.Get();
  if (keyId.which() == ((CTxDestination)CNoDestination()).which())
      throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid key id"));
   
  if(!Params().ContractInTx() && !Consensus::CheckValidTweakedAddress(keyId, pubKeys, nMultisig))
     throw std::invalid_argument(std::string(std::string(__func__) + 
      ": address does not derive from public keys when tweaked with contract hash"));

  //insert new address into sorted CWhiteList vector
  add_sorted(keyId);
}

void CWhiteList::add_multisig_whitelist(const std::string& addressIn, const UniValue& keys, 
        const std::string& sKYCAddress, const uint8_t nMultisig){
    add_multisig_whitelist(addressIn, keys, nMultisig);
}

void CWhiteList::add_multisig_whitelist(const std::string& sAddress, const UniValue& sPubKeys, 
  const uint8_t nMultisig){

  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CBitcoinAddress address;
  if (!address.SetString(sAddress))
    throw std::invalid_argument(std::string(std::string(__func__) + 
    ": invalid Bitcoin address: ") + sAddress);

  std::vector<CPubKey> pubKeyVec;
  for (unsigned int i = 0; i < sPubKeys.size(); ++i){
    std::string parseStr = sPubKeys[i].get_str();
    std::vector<unsigned char> pubKeyData(ParseHex(parseStr.c_str()));
    CPubKey pubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());
    pubKeyVec.push_back(pubKey);
   }

   add_multisig_whitelist(address, pubKeyVec, nMultisig);
}

bool CWhiteList::RegisterAddress(const CTransaction& tx, const CBlockIndex* pindex){
  #ifdef ENABLE_WALLET
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CCoinsViewCache mapInputs(pcoinsTip);
  mapInputs.SetBestBlock(pindex->GetBlockHash());
  return RegisterAddress(tx, mapInputs);
  #else //#ifdef ENABLE_WALLET
    LogPrintf("POLICY: wallet not enabled - unable to process registeraddress transaction.\n");
    return false;
  #endif //#ifdef ENABLE_WALLET
}

bool CWhiteList::RegisterAddress(const CTransaction& tx, const CCoinsViewCache& mapInputs){
  #ifdef ENABLE_WALLET
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if(!mapInputs.HaveInputs(tx)) 
    return false; // No inputs for tx in cache

  if (tx.IsCoinBase())
    return false; // Coinbases don't use vin normally

  return RegisterAddress(tx.vout);

  #else //#ifdef ENABLE_WALLET
    LogPrintf("POLICY: wallet not enabled - unable to process registeraddress transaction.\n");
      return false;
  #endif //#ifdef ENABLE_WALLET
}

bool CWhiteList::RegisterAddress(const std::vector<CTxOut>& vout){
  #ifdef ENABLE_WALLET
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);

  LOCK2(cs_main, pwalletMain->cs_wallet);
  EnsureWalletIsUnlocked();

  //Check if this is a TX_REGISTERADDRESS or TX_DEREGISTERADDRESS. If so, read the data into a byte vector.
  txnouttype whichType;

  // For each TXOUT, if a TX_REGISTERADDRESS, read the data
  BOOST_FOREACH (const CTxOut& txout, vout) {
    std::vector<std::vector<unsigned char> > vSolutions;
    if (!Solver(txout.scriptPubKey, whichType, vSolutions)) return false;
    if(whichType == TX_REGISTERADDRESS || whichType == TX_DEREGISTERADDRESS) {
      return ParseRegisterAddressOutput(txout, whichType == TX_DEREGISTERADDRESS);
    }
  }
  return false;
  #else //#ifdef ENABLE_WALLET
    LogPrintf("POLICY: wallet not enabled - unable to process registeraddress transaction.\n");
      return false;
  #endif //#ifdef ENABLE_WALLET
}

bool CWhiteList::ParseRegisterAddressOutput(const CTxOut& txout, bool fBlacklist){
  #ifdef ENABLE_WALLET
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);

 if (!IsWhitelistAsset(txout)) return false;

  opcodetype opcode;
  std::vector<unsigned char> bytes;
  CScript::const_iterator pc = txout.scriptPubKey.begin();
  if (!txout.scriptPubKey.GetOp(++pc, opcode, bytes)) return false;

  //Confirm data read from the TX_REGISTERADDRESS
  unsigned int minDataSize=CPubKey::COMPRESSED_PUBLIC_KEY_SIZE+addrSize;
  if(bytes.size()<minDataSize) return false;

  CPubKey inputPubKey;
  std::set<CPubKey> inputPubKeys;

  //Read the message data
  std::vector<unsigned char> data(bytes.begin(), bytes.end());
  return RegisterDecryptedAddresses(data, fBlacklist);

  #else //#ifdef ENABLE_WALLET
    LogPrintf("POLICY: wallet not enabled - unable to process registeraddress transaction.\n");
      return false;
  #endif //#ifdef ENABLE_WALLET
}



bool CWhiteList::RegisterDecryptedAddresses(const std::vector<unsigned char>& data, 
    const bool bBlacklist){
  //Interpret the data
  //First 20 bytes: keyID 
  std::vector<unsigned char>::const_iterator itData2 = data.begin();
  std::vector<unsigned char>::const_iterator itData1 = itData2;

  std::vector<unsigned char>::const_iterator pend = data.end();

  bool bEnd=false;
  bool bSuccess=false;

  while(!bEnd){
    bool isMultisig = IsRegisterAddressMulti(itData1, pend);

    //REGISTERADDRESS for pubkeys
    if(isMultisig == false){
      bool fEnd = false;
      int pairsAdded = 0;
      while(!fEnd){
        std::vector<unsigned char>::const_iterator itStart = itData1;
        for(unsigned int i=0; i<addrSize; ++i){
          if(itData2++ == pend) {
            bEnd = true;
            fEnd = true;
            break;
          }
        }
        if(!fEnd){
          CBitcoinAddress addrNew;
          std::vector<unsigned char> addrChars(itData1,itData2);
          CTxDestination addr = CKeyID(uint160(addrChars));
          itData1 = itData2;
          for(unsigned int i=0; i<CPubKey::COMPRESSED_PUBLIC_KEY_SIZE; ++i){
            if(itData2++ == pend){
              bEnd = true;
              fEnd = true;
              break;
            }
          }
            try{
                CPubKey pubKeyNew = CPubKey(itData1,itData2);
                itData1=itData2;
                if(bBlacklist){
                    remove(addr);
                } else {
                    if(!pubKeyNew.IsFullyValid())
                    {
                        itData1 = itStart;
                        itData2 = itStart;
                        if(pairsAdded == 0)
                        bEnd = true;
                        break;
                    }
                    add_derived(CBitcoinAddress(addr), pubKeyNew);
                }
                ++pairsAdded;
            } catch (std::invalid_argument e){
              LogPrintf(std::string(e.what()) + "\n");
              return bSuccess;
            } 
            bSuccess = true;
        }
      }
    }
    //REGISTERADDRESS for MULTISIG
    else{

      itData2 += nMultisigSize;

      uint8_t mMultisig = 0;
      std::vector<unsigned char> mMultisigChars(itData1,itData2);

      mMultisig = mMultisigChars[0];

      itData1 = itData2;

      itData2 += nMultisigSize;

      uint8_t nMultisig = 0;
      std::vector<unsigned char> nMultisigChars(itData1,itData2);

      nMultisig = nMultisigChars[0];

      itData1 = itData2;

      itData2 += addrSize;

      CBitcoinAddress addrMultiNew;
      std::vector<unsigned char> addrTestChars(itData1,itData2);
      addrMultiNew.Set(CScriptID(uint160(addrTestChars)));

      std::vector<CPubKey> vPubKeys;

      itData1=itData2;

      unsigned int pubkeyNr = static_cast<unsigned int>(nMultisig);

      for (unsigned int j=0; j < pubkeyNr; ++j){

        if(bEnd == true)
          break;

        for(unsigned int i=0; i<CPubKey::COMPRESSED_PUBLIC_KEY_SIZE; ++i){
          if(itData2++ == pend){
            bEnd = true;
            break;
          }
        }
        if(!bEnd){
          CPubKey pubKeyNew = CPubKey(itData1,itData2);
          if(!pubKeyNew.IsFullyValid()){
            itData2=itData1;
            break;
          }
          itData1=itData2;
          vPubKeys.push_back(pubKeyNew);
        }
      }
      if(bBlacklist){
        remove(addrMultiNew.Get());
      } else {
            try{
            add_multisig_whitelist(addrMultiNew, vPubKeys, mMultisig);
            } catch (std::invalid_argument e){
            LogPrintf(std::string(e.what()) + "\n");
            return bSuccess;
        }
      }

      bSuccess = true;
    }
  }
  return bSuccess;
}


bool CWhiteList::IsRegisterAddressMulti(const std::vector<unsigned char>::const_iterator start, const std::vector<unsigned char>::const_iterator vend){

  std::vector<unsigned char>::const_iterator point1 = start;
  std::vector<unsigned char>::const_iterator point2 = start;

  for(unsigned int i=0; i<nMultisigSize; ++i){
    if(point2++ == vend) {
      return false;
    }
  }

  uint8_t mMultisig = *start;

  if(mMultisig > MAX_P2SH_SIGOPS || mMultisig == 0)
    return false;

  point1 = point2;

  for(unsigned int i=0; i<nMultisigSize; ++i){
    if(point2++ == vend) {
      return false;
    }
  }

  uint8_t nMultisig = *point1;

  if(nMultisig > MAX_P2SH_SIGOPS || nMultisig == 0)
    return false;

  point1 = point2;

  for(unsigned int i=0; i<addrSize; ++i){
    if(point2++ == vend) {
      return false;
    }
  }

  CBitcoinAddress addrTestNew;
  std::vector<unsigned char> addrTestChars(point1,point2);
  addrTestNew.Set(CScriptID(uint160(addrTestChars)));

  if(!addrTestNew.IsValid())
    return false;

  point1=point2;

  for(unsigned int i=0; i<CPubKey::COMPRESSED_PUBLIC_KEY_SIZE; ++i){
    if(point2++ == vend){
      return false;
    }
  }

  CPubKey pubKeyNew = CPubKey(point1,point2);
  if(!pubKeyNew.IsFullyValid())
    return false;

  return true;
}

//Update from transaction
bool CWhiteList::Update(const CTransaction& tx, const CCoinsViewCache& mapInputs)
{
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    if (tx.IsCoinBase())
      return false; // Coinbases don't use vin normally

    // check inputs for encoded address data
    // The first dummy key in the multisig is the (scrambled) kyc public key.
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxOut& prev = mapInputs.GetOutputFor(tx.vin[i]);
        if(prev.nAsset.GetAsset() != whitelistAsset)
          return false;
        std::vector<std::vector<unsigned char> > vSolutions;
        txnouttype whichType;

        const CScript& prevScript = prev.scriptPubKey;
        if (!Solver(prevScript, whichType, vSolutions)) continue;

        // extract address from second multisig public key and remove from whitelist
        // bytes 0-32: KYC public key assigned by the server, bytes reversed
        
        if (whichType == TX_MULTISIG && vSolutions.size() == 4)
        {
            std::vector<unsigned char> vKycPub(vSolutions[2].begin(), vSolutions[2].begin() + 33);
            //The last bytes of the KYC public key are
            //in reverse to prevent spending, 
            std::reverse(vKycPub.begin()+3, vKycPub.end());
            CPubKey kycPubKey(vKycPub.begin(), vKycPub.end());
            
            if (!kycPubKey.IsFullyValid()) {
              LogPrintf("POLICY: not removing invalid KYC pub key"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
            }

            if(remove_unassigned_kyc(kycPubKey))
                LogPrintf("POLICY: removed KYC pubkey "+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
        }
    }

    //check outputs for encoded address data
    for (unsigned int i = 0; i < tx.vout.size(); i++) {
        const CTxOut& txout = tx.vout[i];

        std::vector<std::vector<unsigned char> > vSolutions;
        txnouttype whichType;

        if (!Solver(txout.scriptPubKey, whichType, vSolutions)) continue;

        // extract address from second multisig public key and add it to the whitelist
        // bytes 0-32: KYC public key assigned by the server, bytes reversed
        if (whichType == TX_MULTISIG && vSolutions.size() == 4)
        {
            std::vector<unsigned char> vKycPub(vSolutions[2].begin(), vSolutions[2].begin() + 33);
            //The last bytes of the KYC public key are
            //in reverse to prevent spending, 
            std::reverse(vKycPub.begin() + 3, vKycPub.end());
            CPubKey kycPubKey(vKycPub.begin(), vKycPub.end());
            if (!kycPubKey.IsFullyValid()) {
                LogPrintf("POLICY: not adding invalid KYC pub key"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
            } else {
                COutPoint outPoint(tx.GetHash(), i);
                add_unassigned_kyc(kycPubKey, outPoint);    
                LogPrintf("POLICY: added KYC pub key "+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
            }
        }
    }
    return true;
}

bool CWhiteList::get_unassigned_kyc(CPubKey& pubKey){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if(!peek_unassigned_kyc(pubKey)) return false;
  remove_unassigned_kyc(pubKey);
  return true;
}

bool CWhiteList::peek_unassigned_kyc(CPubKey& pubKey){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    std::set<CPubKey>::size_type size = _kycUnassignedSet.size();
  if (size == 0) return false;
  auto it = _kycUnassignedSet.begin();
  std::advance(it,GetRand(size-1));
  pubKey= *it;
  return true;
}

bool CWhiteList::is_unassigned_kyc(const CPubKey& kycPubKey){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  auto it = _kycUnassignedSet.find(kycPubKey);
  if (it == _kycUnassignedSet.end()) return false;
  return true;
}

void CWhiteList::add_unassigned_kyc(const CPubKey& kycPubKey, const COutPoint& outPoint){
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    CKeyID kycKey=kycPubKey.GetID();    
    _kycPubkeyOutPointMap[kycKey]=outPoint;
    _kycUnassignedSet.insert(kycPubKey);
}

bool CWhiteList::remove_unassigned_kyc(const CPubKey& id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return _kycUnassignedSet.erase(id);
}


void CWhiteList::dump_unassigned_kyc(std::ofstream& fStream){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  // add the base58check encoded tweaked public key and untweaked pubkey hex
  for(auto it = _kycUnassignedSet.begin(); it != _kycUnassignedSet.end(); ++it) {
        const CPubKey &pubKey = *it;
        const CKeyID keyid = pubKey.GetID();
        const CBitcoinAddress address(keyid);
        std::string strAddr = address.ToString();
        fStream << strAddr;
        fStream << " ";
        fStream << std::string(HexStr(pubKey.begin(), pubKey.end()));
        fStream << " ";
        isminetype mine = pwalletMain ? IsMine(*pwalletMain, keyid) : ISMINE_NO;
        if (mine != ISMINE_NO && address.IsBlinded() && address.GetBlindingKey() 
            != pwalletMain->GetBlindingPubKey(GetScriptForDestination(keyid))) {
            // Note: this will fail to return ismine for deprecated static blinded addresses.
            mine = ISMINE_NO;
        }
        bool bMine =  (mine & ISMINE_SPENDABLE) ? true : false;
        fStream << bMine;
        fStream << std::endl;
    }
}

void CWhiteList::clear(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CPolicyList::clear();
}

bool CWhiteList::is_whitelisted(const CTxDestination keyId){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return find(keyId);
}

void CWhiteList::add_my_pending(const CTxDestination id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  _myPending.insert(id);
}

void CWhiteList::remove_my_pending(const CTxDestination id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  _myPending.erase(id);
}

bool CWhiteList::is_my_pending(const CTxDestination id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return (_myPending.find(id) != _myPending.end());
} 

unsigned int CWhiteList::n_my_pending(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return _myPending.size();
}

bool CWhiteList::get_kycpubkey_outpoint(const CKeyID& keyId, COutPoint& outPoint){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  auto it = _kycPubkeyOutPointMap.find(keyId);
  if (it == _kycPubkeyOutPointMap.end()) return false;
  outPoint = it->second;
  return true;
}

bool CWhiteList::get_kycpubkey_outpoint(const CPubKey& pubKey, COutPoint& outPoint){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if(!pubKey.IsFullyValid())
    return false;
  return get_kycpubkey_outpoint(pubKey.GetID(), outPoint);
}



