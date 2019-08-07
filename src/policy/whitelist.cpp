// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "chain.h"
#include "whitelist.h"
#include "validation.h"
#ifdef ENABLE_WALLET
#include "wallet/wallet.h"
#endif
#include "ecies_hex.h"
#include "policy/policy.h"
#include "rpc/server.h"

CWhiteList::CWhiteList(){
  _asset=whitelistAsset;
  //The written code behaviour expects nMultisigSize to be of length 1 at the moment. If it is changed in the future the code needs to be adjusted accordingly.
  assert(nMultisigSize == 1);
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
                      }

                      CKeyID id=kycPubKey.GetID();
                      COutPoint outPoint(key, i);
                      if(find_kyc_blacklisted(id)){
                        LogPrintf("POLICY: moved KYC pub key from blacklist to whitelist"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
                        whitelist_kyc(id, &outPoint);
                      } else if(find_kyc_whitelisted(id)){
                        continue;
                      } else {
                        LogPrintf("POLICY: registered new unassigned KYC pub key"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
                        whitelist_kyc(id, &outPoint);
                        add_unassigned_kyc(kycPubKey);
                      }
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

void CWhiteList::add_destination(const CTxDestination& dest){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);  
  if (dest.which() == ((CTxDestination)CNoDestination()).which())
    throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid destination"));
  CKeyID kycKeyID;
  _kycPubkeyMap[kycKeyID]=CPubKey();  
  _kycMap[dest]=kycKeyID;
   add_sorted(dest);
}

void CWhiteList::add_derived(const CBitcoinAddress& address, const CPubKey& pubKey){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CWhiteList::add_derived(address, pubKey, nullptr);
}

void CWhiteList::add_derived(const CBitcoinAddress& address,  const CPubKey& pubKey, 
  const std::unique_ptr<CPubKey>& kycPubKey){
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

  if(!Consensus::CheckValidTweakedAddress(keyId, pubKey))
     throw std::invalid_argument(std::string(std::string(__func__) + 
      ": address does not derive from public key when tweaked with contract hash"));

  CKeyID kycKeyID;

  //Update kyc pub key maps one is supplied
  if(kycPubKey){
    if (!kycPubKey->IsFullyValid()) 
      throw std::invalid_argument(std::string(std::string(__func__) + 
        ": invalid KYC public key"));

    kycKeyID=kycPubKey->GetID();

    //If the kycpubkey is not in the whitelist, blacklist or the unassigned list then 
    //it must have been blacklisted (the KYC pub key registration transaction hase been
    //remvoved from the UTXO set and the blockchain has not been rescanned).
    if(!find_kyc(kycKeyID) &! is_unassigned_kyc(kycKeyID)){
      blacklist_kyc(kycKeyID);
    }

    _kycPubkeyMap[kycKeyID]= *kycPubKey;
  } else {
    _kycPubkeyMap[kycKeyID]=CPubKey();
  }

  _kycMap[keyId]=kycKeyID;


  CPubKey tweakedPubKey(pubKey);
   uint256 contract = chainActive.Tip() ? chainActive.Tip()->hashContract : GetContractHash();
  if (!contract.IsNull())
    tweakedPubKey.AddTweakToPubKey((unsigned char*)contract.begin());
    _tweakedPubKeyMap[boost::get<CKeyID>(keyId)]=tweakedPubKey;


 //insert new address into sorted CWhiteList vector
  add_sorted(keyId);
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

  std::unique_ptr<CPubKey> kycPubKey(new CPubKey());
  if(sKYCPubKey.size() > 0){
    std::vector<unsigned char> kycPubKeyData(ParseHex(sKYCPubKey));
    kycPubKey->Set(kycPubKeyData.begin(), kycPubKeyData.end());
  } else {
    kycPubKey=nullptr;
  }
  
  add_derived(address, pubKey, kycPubKey);
}


void CWhiteList::add_multisig_whitelist(const CBitcoinAddress& address, const std::vector<CPubKey>& pubKeys, const uint8_t nMultisig){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CWhiteList::add_multisig_whitelist(address, pubKeys, nullptr, nMultisig);
}

void CWhiteList::add_multisig_whitelist(const CBitcoinAddress& address, const std::vector<CPubKey>& pubKeys, 
  const std::unique_ptr<CPubKey>& kycPubKey, const uint8_t nMultisig){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);

  for(int i = 0; i < pubKeys.size(); ++i) {
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
   
  CKeyID kycKeyId;
  if(kycPubKey){
    if (!kycPubKey->IsFullyValid())
      throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid public key (kyc pub key)"));
    kycKeyId=kycPubKey->GetID();
  }

  if(!Consensus::CheckValidTweakedAddress(keyId, pubKeys, nMultisig))
     throw std::invalid_argument(std::string(std::string(__func__) + 
      ": address does not derive from public keys when tweaked with contract hash"));

  //insert new address into sorted CWhiteList vector
  add_sorted(keyId);
  
  //Add to the ID map
  _kycMap[keyId]=kycKeyId;
}

void CWhiteList::add_multisig_whitelist(const std::string& addressIn, const UniValue& keys, const uint8_t nMultisig){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  add_multisig_whitelist(addressIn, keys, std::string(""), nMultisig);
}

void CWhiteList::add_multisig_whitelist(const std::string& sAddress, const UniValue& sPubKeys, 
  const std::string& sKYCPubKey, const uint8_t nMultisig){

  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CBitcoinAddress address;
  if (!address.SetString(sAddress))
    throw std::invalid_argument(std::string(std::string(__func__) + 
    ": invalid Bitcoin address: ") + sAddress);

  std::vector<CPubKey> pubKeyVec;
  for (int i = 0; i < sPubKeys.size(); ++i){
    std::string parseStr = sPubKeys[i].get_str();
    std::vector<unsigned char> pubKeyData(ParseHex(parseStr.c_str()));
    CPubKey pubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());
    pubKeyVec.push_back(pubKey);
  }

  std::unique_ptr<CPubKey> kycPubKey(new CPubKey());
  if(sKYCPubKey.size() == 0) {
    kycPubKey = nullptr;
  } else {
    std::vector<unsigned char> kycPubKeyData(ParseHex(sKYCPubKey));
    kycPubKey->Set(kycPubKeyData.begin(), kycPubKeyData.end());
    if (!kycPubKey->IsFullyValid())
      throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid public key (kyc pub key): ") + sKYCPubKey);
  }
  add_multisig_whitelist(address, pubKeyVec, kycPubKey, nMultisig);
}

bool CWhiteList::RegisterAddress(const CTransaction& tx, const CBlockIndex* pindex){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CCoinsViewCache mapInputs(pcoinsTip);
  mapInputs.SetBestBlock(pindex->GetBlockHash());
  return RegisterAddress(tx, mapInputs);
}

bool CWhiteList::RegisterAddress(const CTransaction& tx, const CCoinsViewCache& mapInputs){
  #ifdef ENABLE_WALLET
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if(!mapInputs.HaveInputs(tx)) 
    return false; // No inputs for tx in cache

  if (tx.IsCoinBase())
    return false; // Coinbases don't use vin normally

  LOCK2(cs_main, pwalletMain->cs_wallet);
  EnsureWalletIsUnlocked();

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

  //Confirm data read from the TX_REGISTERADDRESS
  unsigned int minDataSize=CPubKey::COMPRESSED_PUBLIC_KEY_SIZE+addrSize+minPayloadSize;
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

  unsigned int minOnboardDataSize=2*CPubKey::COMPRESSED_PUBLIC_KEY_SIZE+minPayloadSize;
  std::vector<unsigned char>::const_iterator it1=bytes.begin();
  std::vector<unsigned char>::const_iterator it2=it1+CPubKey::COMPRESSED_PUBLIC_KEY_SIZE;

  if(bytes.size()>=minOnboardDataSize){
    kycPubKey = CPubKey(it1, it2);
    it1=it2;
    it2+=CPubKey::COMPRESSED_PUBLIC_KEY_SIZE;
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

    //The user onboard pubkey is one of the unassigned KYC pubkeys - so 
    //this will have been derived already in add_unassigned_kycpubkey,
    //even if the node has been restarted
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
      if(LookupKYCKey(keyId, kycKey, kycPubKey)){
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
  std::unique_ptr<CBitcoinAddress> kycAddr(new CBitcoinAddress(kycKey));

  // Get the KYC private key from the wallet.
  // If not found, generate new keys up to nMaxGap.
  // This will allow the nsigning nodes to generate the necessary keys
  // nMaxUnassigned is the maximum number of unassigned keys
  CKey decryptPrivKey;
  if(!pwalletMain->GetKey(inputPubKey.GetID(), decryptPrivKey)){
    //Whitelisting node?
            // For debugging - translate into bitcoin address
      CBitcoinAddress addr(kycKey);
      std::string sAddr = addr.ToString();
    if(!pwalletMain->GetKey(kycKey, decryptPrivKey))
      return false;
  }  else {
    decryptPubKey=kycPubKey;
  }

  //Decrypt
  CECIES_hex decryptor;
  std::vector<unsigned char> data;
  data.resize(encryptedData.size());
  if(!decryptor.Decrypt(data, encryptedData, decryptPrivKey, decryptPubKey)){
    return false;   
  }

  std::unique_ptr<CPubKey> kycPubKeyPtr(new CPubKey(kycPubKey.begin(), kycPubKey.end()));
  return RegisterDecryptedAddresses(data, kycPubKeyPtr);

  #else //#ifdef ENABLE_WALLET
    LogPrintf("POLICY: wallet not enabled - unable to process registeraddress transaction.\n");
      return false;
  #endif //#ifdef ENABLE_WALLET
  return true;
}



bool CWhiteList::RegisterDecryptedAddresses(const std::vector<unsigned char>& data, const std::unique_ptr<CPubKey>& kycPubKey){
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
          addrNew.Set(CKeyID(uint160(addrChars)));  
          itData1 = itData2;
          for(unsigned int i=0; i<CPubKey::COMPRESSED_PUBLIC_KEY_SIZE; ++i){
            if(itData2++ == pend){
              bEnd = true;
              fEnd = true;
              break;
            }
          }
          std::string addrStr=addrNew.ToString();
          if(!fEnd){
            CPubKey pubKeyNew = CPubKey(itData1,itData2);
            itData1=itData2;
            if(!pubKeyNew.IsFullyValid())
            {
              itData1 = itStart;
              itData2 = itStart;
              if(pairsAdded == 0)
                bEnd = true;
              break;
            }
            try{
              add_derived(addrNew, pubKeyNew, kycPubKey);
               ++pairsAdded;
            } catch (std::invalid_argument e){
              LogPrintf(std::string(e.what()) + "\n");
              return bSuccess;
            } 
            bSuccess = true;
          }
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

      try{
        add_multisig_whitelist(addrMultiNew, vPubKeys, kycPubKey, mMultisig);
      } catch (std::invalid_argument e){
        LogPrintf(std::string(e.what()) + "\n");
        return bSuccess;
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

bool CWhiteList::LookupKYCKey(const CTxDestination address, CKeyID& kycKeyFound){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  auto search = _kycMap.find(address);
  if(search != _kycMap.end()){
    kycKeyFound = search->second;
    return true;
  }
  return false;
}

bool CWhiteList::LookupKYCKey(const CKeyID& keyId, CPubKey& kycPubKeyFound){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CKeyID kycKeyID;
  return LookupKYCKey(keyId, kycKeyID, kycPubKeyFound);
}

bool CWhiteList::LookupKYCKey(const CKeyID& keyId, CKeyID& kycKeyIdFound, CPubKey& kycPubKeyFound){
  CKeyID kycKeyId;
  if(LookupKYCKey(keyId, kycKeyId)){
    auto search = _kycPubkeyMap.find(kycKeyId);
    if(search != _kycPubkeyMap.end()){
      kycPubKeyFound = search->second;
      kycKeyIdFound = kycKeyId;
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
              LogPrintf("POLICY: not blacklisting invalid KYC pub key"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
            }

            CKeyID id=kycPubKey.GetID();
            blacklist_kyc(id);

            LogPrintf("POLICY: moved KYC pubkey from whitelist to blacklist"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
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
            }

            CKeyID id=kycPubKey.GetID();
            if(find_kyc_blacklisted(id)){
              LogPrintf("POLICY: moved KYC pub key from blacklist to whitelist"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
              COutPoint outPoint(tx.GetHash(), i);
              whitelist_kyc(id, &outPoint);
            } else if(find_kyc_whitelisted(id)){
              continue;
            } else {
              LogPrintf("POLICY: registered new unassigned KYC pub key"+HexStr(kycPubKey.begin(), kycPubKey.end())+"\n");
              COutPoint outPoint(tx.GetHash(), i);
              whitelist_kyc(id, &outPoint);
              add_unassigned_kyc(kycPubKey);
            }
        }
    }
    return true;
}


void CWhiteList::blacklist_kyc(const CKeyID& keyId){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  set_kyc_status(keyId, CWhiteList::status::black);
  _kycPubkeyOutPointMap.erase(keyId);
}

void CWhiteList::whitelist_kyc(const CKeyID& keyId, const COutPoint* outPoint){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  set_kyc_status(keyId, CWhiteList::status::white);
  if(outPoint)
    _kycPubkeyOutPointMap[keyId]=*outPoint;
  _kycUnassignedSet.erase(keyId);
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
    //Move from "unassigned" to whitelisted in this node.
    //Other nodes will be notified via the user onboard transaction.
    CKeyID id = pubKey.GetID();
    whitelist_kyc(id);
    _kycUnassignedQueue.pop();
    _kycUnassignedSet.erase(id);
    return true;
  }
  return false;
}

bool CWhiteList::peek_unassigned_kyc(CPubKey& pubKey){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  while (!_kycUnassignedQueue.empty()){
      pubKey = _kycUnassignedQueue.front();
      auto it = _kycUnassignedSet.find(pubKey.GetID());
      if(it == _kycUnassignedSet.end()){
        _kycUnassignedQueue.pop();
      } else {
        return true;
      }
  }
  return false;
}

bool CWhiteList::is_unassigned_kyc(const CKeyID& kycKeyID){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  auto it = _kycUnassignedSet.find(kycKeyID);
  if (it == _kycUnassignedSet.end()) return false;
  return true;
}

void CWhiteList::add_unassigned_kyc(const CPubKey& id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  //If this is the whitelisting node, the private key should be in the wallet.
  //Generate new keys up to the limit until found.
  //If not found, return and error.
  CKeyID kycKey=id.GetID();
  #ifdef ENABLE_WALLET
    if(fRequireWhitelistCheck){
    LOCK2(cs_main, pwalletMain->cs_wallet);
    EnsureWalletIsUnlocked();
    CKey privKey;
    int nTries=0;
    while(!pwalletMain->GetKey(kycKey, privKey)){
      CPubKey newPubKey = pwalletMain->GenerateNewKey();
      if(++nTries > MAX_UNASSIGNED_KYCPUBKEYS){
         LogPrintf("ERROR: kyc privkey not in whitelisting node wallet"+HexStr(id.begin(), id.end())+"\n");
        break;
        }
      }
    }
    #endif //ENABLE_WALLET  
 
  _kycUnassignedSet.insert(kycKey);
  _kycUnassignedQueue.push(id);
}

void CWhiteList::clear(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  _kycMap.clear();
  _tweakedPubKeyMap.clear();
  _kycStatusMap.clear();
  CPolicyList::clear();
}

bool CWhiteList::is_whitelisted(const CTxDestination keyId){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if(!find(keyId)) return false;
  if(_kycMap[keyId] == CKeyID()) return true;
  if(!find_kyc_whitelisted(_kycMap[keyId])) return false;
  return true;
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

bool CWhiteList::kycFromUserOnboard(const CPubKey& userOnboard, CPubKey& kyc){
  if(_onboardMap.find(userOnboard.GetID()) == _onboardMap.end()) return false;
  kyc=_onboardMap[userOnboard.GetID()];
  return true;
}

