// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "whitelist.h"
#include "validation.h"
#include "wallet/wallet.h"
#include "ecies.h"

CWhiteList::CWhiteList(){;}
CWhiteList::~CWhiteList(){;}

void CWhiteList::add_derived(const CBitcoinAddress& address, const CPubKey& pubKey){
  CWhiteList::add_derived(address, pubKey, nullptr);
}

void CWhiteList::add_derived(const CBitcoinAddress& address,  const CPubKey& pubKey, 
  const CBitcoinAddress* kycAddress){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if (!pubKey.IsFullyValid())
    throw std::system_error(
          std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY, std::system_category())
          ,std::string(std::string(__func__) +  ": invalid public key"));

    //Will throw an error if address is not a valid derived address.
  CKeyID keyId;
  if (!address.GetKeyID(keyId))
    throw std::system_error(
          std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY, std::system_category()),
          std::string(__func__) + ": invalid key id");

  CKeyID kycKeyId;
  if(kycAddress){
    if (!kycAddress->GetKeyID(kycKeyId))
      throw std::system_error(
			    std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY,std::system_category()),
            std::string(__func__) + ": invalid key id (kyc address)");
  }

  try{
    if(!Consensus::CheckValidTweakedAddress(keyId, pubKey)) return;
  } catch (std::system_error e) {
    throw e;
  } 
  //insert new address into sorted CWhiteList vector
  add_sorted(&keyId);

  //Add to the ID map
  _kycMap[keyId]=kycKeyId;
  //Used for decryption
  CPubKey tweakedPubKey(pubKey);
   uint256 contract = chainActive.Tip() ? chainActive.Tip()->hashContract : GetContractHash();
  if (!contract.IsNull())
    tweakedPubKey.AddTweakToPubKey((unsigned char*)contract.begin());
    _tweakedPubKeyMap[keyId]=tweakedPubKey;
}

void CWhiteList::add_derived(const std::string& addressIn, const std::string& key){
  add_derived(addressIn, key, std::string(""));
}

void CWhiteList::add_derived(const std::string& sAddress, const std::string& sPubKey, 
  const std::string& sKYCAddress){
   boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    CBitcoinAddress address;
  if (!address.SetString(sAddress))
    throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid Bitcoin address: ") + sAddress);
  
  std::vector<unsigned char> pubKeyData(ParseHex(sPubKey));
  CPubKey pubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());

  CBitcoinAddress* kycAddress;
  if(sKYCAddress.size() == 0) {
    kycAddress = nullptr;
  } else {
    kycAddress = new CBitcoinAddress();
     if (!kycAddress->SetString(sKYCAddress))
     throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid Bitcoin address (kyc key): ") + sKYCAddress);
  }
  add_derived(address, pubKey, kycAddress);
  delete kycAddress;
}

bool CWhiteList::RegisterAddress(const CTransaction& tx, const CCoinsViewCache& mapInputs){
  //Check if this is a ID registration (whitetoken) transaction
  // Get input addresses an lookup associated idpubkeys
  if (tx.IsCoinBase())
    return false; // Coinbases don't use vin normally

  //Check if this is a TX_REGISTERADDRESS. If so, read the data into a byte vector.
  opcodetype opcode;
  std::vector<unsigned char> bytes;

  BOOST_FOREACH (const CTxOut& txout, tx.vout) {
    std::vector<std::vector<unsigned char> > vSolutions;
    txnouttype whichType;
    //Is the output solvable?
    if (!Solver(txout.scriptPubKey, whichType, vSolutions)) return false;
    //Is it a TX_REGISTERADDRESS?
    if(whichType == TX_REGISTERADDRESS) {
      CScript::const_iterator pc = txout.scriptPubKey.begin();
      //Can the bytes be read?
      if (!txout.scriptPubKey.GetOp(++pc, opcode, bytes)) return false;
      break;
    }
  }

  //Confirm data read from the TX_REGISTERADDRESS
  if(bytes.size()==0) return false;

  //Get input keyids
  //Lookup the ID public keys of the input addresses.
  //The set is used to ensure that there is only one kycKey involved.
  std::vector<CPubKey> inputPubKeys;
  CKeyID kycKey, keyId;
  
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
      CPubKey pubKey;
      if(LookupTweakedPubKey(keyId, pubKey))
      inputPubKeys.push_back(pubKey);
    }
  }

  //Inputs need to all be owned by the same entity
  if(inputPubKeys.size()!=1) return false;

  //The first AES_BLOCKSIZE bytes of the message are the initialization vector
  //used to decrypt the rest of the message
  unsigned int pubKeySize=33;
  unsigned int addrSize=20;
  std::vector<unsigned char>::const_iterator it=bytes.begin();
//  std::vector<unsigned char> fromPubKey(it, it+=pubKeySize);
  std::vector<unsigned char> initVec(it, it+=AES_BLOCKSIZE);
  std::vector<unsigned char> encryptedData(it, bytes.end());

  //Get the private key that is paired with kycKey
  CBitcoinAddress kycAddr(kycKey);
  std::string sKYCAddr = kycAddr.ToString();

  // Get the KYC private key from the wallet.
  // This ultimately checks that the kyc key associated with the transaction input address 
  // is already associated with a valid kyc key.
  bool bWLNode=false;
  CKey decryptPrivKey;
  if(!pwalletMain->GetKey(kycKey, decryptPrivKey)){  
    bWLNode=false;
  } else{
    bWLNode=true;
  }
  

  //Decrypt the data
  //One of the input public keys together with the KYC private key 
  //will compute the shared secret used to encrypt the data

  bool bSuccess=false;

  for(std::vector<CPubKey>::const_iterator it = inputPubKeys.begin();
    it != inputPubKeys.end();
    ++it)
  {
    if((*it).size() != pubKeySize) continue;

    //Get the decryption keys
    CPubKey decryptPubKey;
    if(bWLNode){
      decryptPubKey=(*it);
    } else {
      if(!pwalletMain->GetKey((*it).GetID(), decryptPrivKey)) continue;  
      decryptPubKey=pwalletMain->GetKYCPubKey();
    }

    //Decrypt
    CECIES decryptor(decryptPrivKey, decryptPubKey, initVec);
    std::vector<unsigned char> data;
    data.resize(encryptedData.size());
    decryptor.Decrypt(data, encryptedData);
    
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
        addrNew.Set(CKeyID(uint160(addrChars)));  
        itData1=itData2;
        for(unsigned int i=0; i<pubKeySize; ++i){
          if(itData2++ == pend){
            bEnd=true;
            break;
          }
        }
        if(!bEnd){
          std::vector<unsigned char> pubKeyData(itData1, itData2);
          itData1=itData2;
          CPubKey pubKeyNew = CPubKey(pubKeyData.begin(),pubKeyData.end());
          CBitcoinAddress* addr = new CBitcoinAddress(kycKey);
          //Convert to string for debugging
          std::string sAddr=addr->ToString();
          std::string sAddrNew=addrNew.ToString();
          try{
            add_derived(addrNew, pubKeyNew, addr);
          } catch (std::system_error e){
            if(e.code().value() != CPolicyList::Errc::INVALID_ADDRESS_OR_KEY) throw e;
          }
          delete addr;
          bSuccess=true;
        }
      }
    }
  }
  
  return bSuccess;
}

bool CWhiteList::LookupKYCKey(const CKeyID& address, CKeyID& kycKeyFound){
  auto search = _kycMap.find(address);
  if(search != _kycMap.end()){
    kycKeyFound = search->second;
    return true;
  }
  return false;
}

bool CWhiteList::LookupTweakedPubKey(const CKeyID& address, CPubKey& pubKeyFound){
  auto search = _tweakedPubKeyMap.find(address);
  if(search != _tweakedPubKeyMap.end()){
    pubKeyFound = search->second;
    return true;
  }
  return false;
}

