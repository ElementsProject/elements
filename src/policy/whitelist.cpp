// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "whitelist.h"
#include "validation.h"
#ifdef ENABLE_WALLET
#include "wallet/wallet.h"
#endif
#include "ecies_hex.h"
#include "policy/policy.h"

CWhiteList::CWhiteList(){
  _asset=whitelistAsset;
}
CWhiteList::~CWhiteList(){;}

bool CWhiteList::Load(CCoinsView *view)
{
    std::unique_ptr<CCoinsViewCursor> pcursor(view->Cursor());
    LOCK(cs_main);

    //main loop over coins (transactions with > 0 unspent outputs
    while (pcursor->Valid()) {
        boost::this_thread::interruption_point();
        uint256 key;
        CCoins coins;
        if (pcursor->GetKey(key) && pcursor->GetValue(coins)) {
            //loop over all vouts within a single transaction
            for (unsigned int i=0; i<coins.vout.size(); i++) {
                const CTxOut &out = coins.vout[i];
                //null vouts are spent
                if (!out.IsNull()) {
                   if(out.nAsset.GetAsset() == _asset) {
                    std::vector<std::vector<unsigned char> > vSolutions;
                    txnouttype whichType;

                    if (!Solver(out.scriptPubKey, whichType, vSolutions)) continue;

                    // extract address from second multisig public key and add to the freezelist
                    // encoding: 33 byte public key: address is encoded in the last 20 bytes (i.e. byte 14 to 33)
                    if (whichType == TX_MULTISIG && vSolutions.size() == 4){
                      std::vector<unsigned char> vKycPub(vSolutions[2].begin(), vSolutions[2].begin() + 33);
                      //The last bytes of the KYC public key are
                      //in reverse to prevent spending, 
                      std::reverse(vKycPub.begin() + 3, vKycPub.end());
                      CPubKey kycPubKey(vKycPub.begin(), vKycPub.end());
                      if (!kycPubKey.IsFullyValid()) {
                        LogPrintf("POLICY: not adding invalid KYC pub key to whitelist"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
                        return false;
                      }

                      CKeyID id=kycPubKey.GetID();
                      COutPoint outPoint(key, i);
                      if(find_kyc_blacklisted(id)){
                        LogPrintf("POLICY: moved KYC pub key from blacklist to whitelist"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
                        whitelist_kyc(id, &outPoint);
                      } else if(find_kyc_whitelisted(id)){
                        return false;
                      } else {
                        LogPrintf("POLICY: registered new unassigned KYC pub key"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
                        whitelist_kyc(id, &outPoint);
                        add_unassigned_kyc(kycPubKey);
                      }
                      return true;
                    }
                }
              }
            }
      } else {
        return error("%s: unable to read value", __func__);
      }
    pcursor->Next();
    }
  return true;
}



void CWhiteList::add_derived(const CBitcoinAddress& address, const CPubKey& pubKey){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CWhiteList::add_derived(address, pubKey, nullptr);
}

void CWhiteList::add_derived(const CBitcoinAddress& address,  const CPubKey& pubKey, 
  const CPubKey* kycPubKey){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if (!pubKey.IsFullyValid()) 
    throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid public key"));

    //Will throw an error if address is not a valid derived address.
  CKeyID keyId;
  if (!address.GetKeyID(keyId))
      throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid key id"));

  if(!Consensus::CheckValidTweakedAddress(keyId, pubKey))
     throw std::invalid_argument(std::string(std::string(__func__) + 
      ": address does not derive from public key when tweaked with contract hash"));


  CPubKey newKYCPubKey;
  CKeyID kycKeyID;
  if(kycPubKey != nullptr){
    if (!kycPubKey->IsFullyValid()) 
      throw std::invalid_argument(std::string(std::string(__func__) + 
        ": invalid KYC public key"));

    newKYCPubKey=CPubKey(kycPubKey->begin(), kycPubKey->end());
    kycKeyID=newKYCPubKey.GetID();
  } 


  //insert new address into sorted CWhiteList vector
  add_sorted(&keyId);

  _kycMap[keyId]=kycKeyID;
  _kycPubkeyMap[kycKeyID]=newKYCPubKey;

  //Used for decryption
  CPubKey tweakedPubKey(pubKey);
   uint256 contract = chainActive.Tip() ? chainActive.Tip()->hashContract : GetContractHash();
  if (!contract.IsNull())
    tweakedPubKey.AddTweakToPubKey((unsigned char*)contract.begin());
  _tweakedPubKeyMap[keyId]=tweakedPubKey;
}

void CWhiteList::add_derived(const std::string& addressIn, const std::string& key){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  add_derived(addressIn, key, std::string(""));
}

void CWhiteList::add_derived(const std::string& sAddress, const std::string& sPubKey, 
  const std::string& sKYCPubKey){
   boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    CBitcoinAddress address;
  if (!address.SetString(sAddress))
    throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid Bitcoin address: ") + sAddress);
  
  std::vector<unsigned char> pubKeyData(ParseHex(sPubKey));
  CPubKey pubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());

  CPubKey* kycPubKey = nullptr;
  if(sKYCPubKey.size() > 0){
    std::vector<unsigned char> kycPubKeyData(ParseHex(sKYCPubKey));
    kycPubKey = new CPubKey(kycPubKeyData.begin(), kycPubKeyData.end());
  }

  add_derived(address, pubKey, kycPubKey);
  delete kycPubKey;
}

#ifdef ENABLE_WALLET
bool CWhiteList::RegisterAddress(const CTransaction& tx, const CBlockIndex* pindex){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CCoinsViewCache mapInputs(pcoinsTip);
  mapInputs.SetBestBlock(pindex->GetBlockHash());
  return RegisterAddress(tx, mapInputs);
}
#endif //#ifdef ENABLE_WALLET

bool CWhiteList::RegisterAddress(const CTransaction& tx, const CCoinsViewCache& mapInputs){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  #ifdef ENABLE_WALLET
  if(!mapInputs.HaveInputs(tx)) 
    return false; // No inputs for tx in cache

  if (tx.IsCoinBase())
    return false; // Coinbases don't use vin normally

  //Check if this is a TX_REGISTERADDRESS. If so, read the data into a byte vector.
  opcodetype opcode;
  std::vector<unsigned char> bytes;

  // For each TXOUT, if a TX_REGISTERADDRESS, read the data
  BOOST_FOREACH (const CTxOut& txout, tx.vout) {
    std::vector<std::vector<unsigned char> > vSolutions;
    txnouttype whichType;
    if (!Solver(txout.scriptPubKey, whichType, vSolutions)) return false;
    if(whichType == TX_REGISTERADDRESS) {
      CScript::const_iterator pc = txout.scriptPubKey.begin();
      if (!txout.scriptPubKey.GetOp(++pc, opcode, bytes)) return false;
      break;
    }
  }

  unsigned int pubKeySize=33;
  unsigned int addrSize=20;
  unsigned int minPayloadSize=2;

  //Confirm data read from the TX_REGISTERADDRESS
  unsigned int minDataSize=pubKeySize+addrSize+minPayloadSize;
  if(bytes.size()<minDataSize) return false;


  // Are the first 33 bytes a currently whitelisted KYC public key? 
  // If so, this is an initial onboarding transaction, and those 33 bytes are the server KYC public key.
  // And the following bytes are:
  // 33 bytes: client onboarding public key.

  bool bOnboard=false;
  CPubKey kycPubKey;
  CPubKey userOnboardPubKey;
  CKeyID kycKey, keyId, onboardKeyID;
  CKey userOnboardPrivKey;
  CPubKey inputPubKey;
  std::set<CPubKey> inputPubKeys;

  unsigned int minOnboardDataSize=2*pubKeySize+minPayloadSize;
  std::vector<unsigned char>::const_iterator it1=bytes.begin();
  std::vector<unsigned char>::const_iterator it2=it1+pubKeySize;

  if(bytes.size()>=minOnboardDataSize){
    kycPubKey = CPubKey(it1, it2);
    it1=it2;
    it2+=pubKeySize;
    userOnboardPubKey = CPubKey(it1, it2);
    it1=it2;

    if(kycPubKey.IsFullyValid()){
      if(userOnboardPubKey.IsFullyValid()){
        kycKey=kycPubKey.GetID();
        bOnboard = find_kyc(kycKey);
      }
    }
  } else {
    bOnboard=false;
  }

  CPubKey decryptPubKey; //Default key

  if(bOnboard){
    //Onboarding must be done using the whitelist asset 
    if(!IsWhitelistAssetOnly(tx)) return false;
    // Check if reading from the client node
    if(pwalletMain->GetKey(userOnboardPubKey.GetID(), userOnboardPrivKey)){  
      // kycPubKey assigned to me by the whitelisting node
      pwalletMain->SetKYCPubKey(kycPubKey);
      _onboardMap[userOnboardPubKey.GetID()]=kycPubKey;
    }
    inputPubKeys.insert(userOnboardPubKey);
    inputPubKey = userOnboardPubKey;
    decryptPubKey = inputPubKey;
  } else {
    it1=bytes.begin(); //Reset iterator
    kycPubKey=pwalletMain->GetKYCPubKey();  //For the non-whitelisting nodes
    kycKey=kycPubKey.GetID();
    //Get input keyids
    //Lookup the ID public keys of the input addresses.
    //The set is used to ensure that there is only one kycKey involved.
    BOOST_FOREACH(const CTxIn& prevIn, tx.vin) {
      const CTxOut& prev = mapInputs.GetOutputFor(prevIn);
      CTxDestination dest;
      if(!ExtractDestination(prev.scriptPubKey, dest))
       continue;
    
      // For debugging - translate into bitcoin address
      CBitcoinAddress addr(dest);
      addr.GetKeyID(keyId);
      std::string sAddr = addr.ToString();
      // search in whitelist for the presence of keyid
      // add the associated kycKey to the set of kyc keys
      if(LookupKYCKey(keyId, kycKey)){
        if(find_kyc(kycKey)){ //Is user whitelisted?
          if(LookupTweakedPubKey(keyId, inputPubKey))
            inputPubKeys.insert(inputPubKey);
        }
      }
    }
  }

  if(inputPubKeys.size()!=1) return false;

  //Read the encrypted message data
  it2=bytes.end();
  std::vector<unsigned char> encryptedData(it1, it2);
  //Get the private key that is paired with kycKey
  CBitcoinAddress kycAddr(kycKey);
  std::string sKYCAddr = kycAddr.ToString();

  // Get the KYC private key from the wallet.
  CKey decryptPrivKey;
  if(!pwalletMain->GetKey(kycKey, decryptPrivKey)){  
    //Non-whitelisting node
    if(!pwalletMain->GetKey(inputPubKey.GetID(), decryptPrivKey)) return false;  
    decryptPubKey=kycPubKey;
  }  

  bool bSuccess=false;

  //Decrypt
  CECIES_hex decryptor;
  std::vector<unsigned char> data;
  data.resize(encryptedData.size());
  if(!decryptor.Decrypt(data, encryptedData, decryptPrivKey, decryptPubKey)){
    return false;   
  }
  //Interpret the data
  //First 20 bytes: keyID 
  std::vector<unsigned char>::const_iterator itData2 = data.begin();
  std::vector<unsigned char>::const_iterator itData1 = itData2;

  std::vector<unsigned char>::const_iterator pend = data.end();
  std::vector<unsigned char> vKeyID, vPubKey;

  bool bEnd=false;
  while(!bEnd){
    for(unsigned int i=0; i<addrSize; ++i){
      if(itData2++ == pend) {
        bEnd=true;
        break;
      }
    }
    if(!bEnd){
      CBitcoinAddress addrNew;
      std::vector<unsigned char> addrChars(itData1,itData2);
      std::string addrCharsStr(addrChars.begin(), addrChars.end());
      addrNew.Set(CKeyID(uint160(addrChars)));  
      itData1=itData2;
      for(unsigned int i=0; i<pubKeySize; ++i){
        if(itData2++ == pend){
          bEnd=true;
          break;
        }
      }
      std::string addrStr=addrNew.ToString();
      if(!bEnd){
        std::vector<unsigned char> pubKeyData(itData1, itData2);
        itData1=itData2;
        CPubKey pubKeyNew = CPubKey(pubKeyData.begin(),pubKeyData.end());
        try{
          add_derived(addrNew, pubKeyNew, &kycPubKey);
        } catch (std::invalid_argument e){
          LogPrintf(std::string(e.what()) + "\n");
          continue;
        } 
        bSuccess=true;
      }
    }
  }
  return bSuccess;
  #else //#ifdef ENABLE_WALLET
    LogPrintf("POLICY: wallet not enabled - unable to process registeraddress transaction.\n");
      return false;
  #endif //#ifdef ENABLE_WALLET
}

bool CWhiteList::LookupKYCKey(const CKeyID& address, CKeyID& kycKeyFound){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  auto search = _kycMap.find(address);
  if(search != _kycMap.end()){
    kycKeyFound = search->second;
    return true;
  }
  return false;
}

bool CWhiteList::LookupKYCKey(const CKeyID& keyId, CPubKey& kycPubkeyFound){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CKeyID kycKeyID;
  if(LookupKYCKey(keyId, kycKeyID)){
    auto search = _kycPubkeyMap.find(kycKeyID);
    if(search != _kycPubkeyMap.end()){
      kycPubkeyFound = search->second;
      return true;
    }
  }
  return false;
}

bool CWhiteList::LookupTweakedPubKey(const CKeyID& address, CPubKey& pubKeyFound){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  auto search = _tweakedPubKeyMap.find(address);
  if(search != _tweakedPubKeyMap.end()){
    pubKeyFound = search->second;
    return true;
  }
  return false;
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
              LogPrintf("POLICY: not blacklisting invalid KYC pub key"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
              return false;
            }

            CKeyID id=kycPubKey.GetID();
            blacklist_kyc(id);

            LogPrintf("POLICY: moved KYC pubkey from whitelist to blacklist"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
            return true;
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
              LogPrintf("POLICY: not adding invalid KYC pub key to whitelist"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
              return false;
            }

            CKeyID id=kycPubKey.GetID();
            if(find_kyc_blacklisted(id)){
              LogPrintf("POLICY: moved KYC pub key from blacklist to whitelist"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
              COutPoint outPoint(tx.GetHash(), i);
              whitelist_kyc(id, &outPoint);
            } else if(find_kyc_whitelisted(id)){
              return false;
            } else {
              LogPrintf("POLICY: registered new unassigned KYC pub key"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
              COutPoint outPoint(tx.GetHash(), i);
              whitelist_kyc(id, &outPoint);
              add_unassigned_kyc(kycPubKey);
            }
            return true;
        }
    }
    return false;
}

//hashTx = tx->GetHash();){

void CWhiteList::blacklist_kyc(const CKeyID& keyId){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  set_kyc_status(keyId, CWhiteList::status::black);
  _kycPubkeyOutPointMap.erase(_kycPubkeyOutPointMap.find(keyId));
}

void CWhiteList::whitelist_kyc(const CKeyID& keyId, const COutPoint* outPoint){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  set_kyc_status(keyId, CWhiteList::status::white);
  if(outPoint)
    _kycPubkeyOutPointMap[keyId]=*outPoint;
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

bool CWhiteList::set_kyc_status(const CKeyID& keyId, const CWhiteList::status& status){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  _kycStatusMap[keyId]=status;
  return true;
}

bool CWhiteList::find_kyc_status(const CKeyID& keyId, const CWhiteList::status& status){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  auto it = _kycStatusMap.find(keyId);
  if (it == _kycStatusMap.end()) return false;
  return (it->second == status);
}

bool CWhiteList::find_kyc(const CKeyID& keyId){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return _kycStatusMap.find(keyId) != _kycStatusMap.end();
}

bool CWhiteList::find_kyc_whitelisted(const CKeyID& keyId){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return find_kyc_status(keyId, CWhiteList::status::white);
}

bool CWhiteList::find_kyc_blacklisted(const CKeyID& keyId){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return find_kyc_status(keyId, CWhiteList::status::black);
}

bool CWhiteList::get_unassigned_kyc(CPubKey& pubKey){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if(peek_unassigned_kyc(pubKey)){
    _kycUnassignedQueue.pop();
    return true;
  }
  return false;
}

bool CWhiteList::peek_unassigned_kyc(CPubKey& pubKey){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if (_kycUnassignedQueue.empty()) return false;
  pubKey = _kycUnassignedQueue.front();
  return true;
}

void CWhiteList::add_unassigned_kyc(const CPubKey& id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  _kycUnassignedQueue.push(id);
}

void CWhiteList::clear(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  _kycMap.clear();
  _tweakedPubKeyMap.clear();
  _kycStatusMap.clear();
  CPolicyList::clear();
}

bool CWhiteList::is_whitelisted(const CKeyID& keyId){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if(!find(&keyId)) return false;
  if(_kycMap[keyId] == CKeyID()) return true;
  if(!find_kyc_whitelisted(_kycMap[keyId])) return false;
  return true;
}

void CWhiteList::add_my_pending(const CKeyID& id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  _myPending.insert(id);
}

void CWhiteList::remove_my_pending(const CKeyID& id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  _myPending.erase(id);
}

bool CWhiteList::is_my_pending(const CKeyID& id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return (_myPending.find(id) != _myPending.end());
} 

unsigned int CWhiteList::n_my_pending(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return _myPending.size();
}

bool CWhiteList::kycFromUserOnboard(const CPubKey& userOnboard, CPubKey& kyc){
  if(_onboardMap.find(userOnboard.GetID()) == _onboardMap.end()) return false;
  kyc=_onboardMap[userOnboard.GetID()];
  return true;
}

