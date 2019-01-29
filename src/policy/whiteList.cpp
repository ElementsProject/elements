// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "whiteList.h"
#include "validation.h"
#include "wallet/wallet.h"
#include "ecies.h"

CWhiteList::CWhiteList(){;}
CWhiteList::~CWhiteList(){;}

void CWhiteList::add_derived(CBitcoinAddress address, CPubKey pubKey){
  CWhiteList::add_derived(address, pubKey, CKeyID());
}

void CWhiteList::add_derived(CBitcoinAddress address, CPubKey pubKey, CKeyID kycKey){
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
  try{
    if(!Consensus::CheckValidTweakedAddress(keyId, pubKey)) return;
  } catch (std::system_error e) {
    throw e;
  } 
  //insert new address into sorted CWhiteList vector 
  add_sorted(&keyId);

  //Add to the ID map
  _kycMap[keyId]=kycKey;
}

void CWhiteList::add_derived(std::string addressIn, std::string key){
  add_derived(addressIn, key, std::string(""));
}

void CWhiteList::add_derived(std::string sAddress, std::string sPubKey, std::string sKYCKey){
   boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    CBitcoinAddress address;
  if (!address.SetString(sAddress))
    throw std::invalid_argument(std::string(std::string(__func__) + 
      ": invalid Bitcoin address: ") + sAddress);
  
  std::vector<unsigned char> pubKeyData(ParseHex(sPubKey));
  CPubKey pubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());

  CKeyID kycKey;
  if(sKYCKey.size()>0){ //TODO - size?
    std::vector<unsigned char> kycKeyData(ParseHex(sKYCKey));
    kycKey = uint160(kycKeyData);
  } 

  add_derived(address, pubKey, kycKey);
}

bool CWhiteList::RegisterAddress(const CTransaction& tx){
  //Check if this is a ID registration (whitetoken) transaction
    unsigned int pubKeySize=33;
    unsigned int initVecSize=32;


  // Get input addresses an lookup associated idpubkeys
  if (tx.IsCoinBase())
    return false; // Coinbases don't use vin normally

  //Get input addresses
  std::vector<CPubKey> inputPubKeys;

  for (unsigned int i = 0; i < tx.vin.size(); i++) {
    CScript scriptSig = tx.vin[i].scriptSig;
    inputPubKeys.push_back(CPubKey(scriptSig.end()-pubKeySize, scriptSig.end()));
  }

  if(inputPubKeys.size()==0) return false;
  
  //Lookup the ID public keys of the input addresses
  std::set<CKeyID> kycKeys;
  CKeyID kycKey;
  CPubKey inputPubKey;

  for(std::vector<CPubKey>::const_iterator it = inputPubKeys.begin();
      it != inputPubKeys.end();
      ++it){
    //All input addresses must be owned by someone whitelisted
    CKeyID keyID = CKeyID(uint160(Hash160((*it).begin(), (*it).end())));
    if(!LookupKYCKey(keyID, kycKey)) return false;
    kycKeys.insert(kycKey);
  }

  //There must be exactly 1 kyc key (all input addresses owned by 1 person)
  if(kycKeys.size() != 1) return false;
  
  //Get the message bytes
  opcodetype opcode;
  std::vector<unsigned char> bytes;

  //Get the data from the registeraddress script
  for (unsigned int i = 0; i < tx.vout.size(); i++) {
    const CTxOut& txout = tx.vout[i];
    std::vector<std::vector<unsigned char> > vSolutions;
    txnouttype whichType;

    if (!Solver(txout.scriptPubKey, whichType, vSolutions)) continue;

    if(whichType == TX_REGISTERADDRESS){
      CScript::const_iterator pc = txout.scriptPubKey.begin();
      if (!txout.scriptPubKey.GetOp(++pc, opcode, bytes)) return true;
      break;
    }
  }

  //The first 32 bytes of the message are the initialization vector
  //used to decrypt the rest of the message
  std::vector<unsigned char> initVec(bytes.begin(), bytes.begin()+initVecSize);
  std::vector<unsigned char> encryptedData(bytes.begin()+initVecSize, bytes.end());

  //Get the private key that is paired with kycKey
  CKey kycPrivKey;
  pwalletMain->GetKey(kycKey, kycPrivKey); 
  
  //Decrypt the data
  //One of the input public keys together with the KYC private key 
  //will compute the shared secret used to encrypt the data

  bool bSuccess=false;

  for(std::vector<CPubKey>::const_iterator it = inputPubKeys.begin();
    it != inputPubKeys.end();
    ++it)
  {
    bool bEnd=false;

    CECIES decryptor(kycPrivKey, *it, initVec);
    std::vector<unsigned char> data;
    decryptor.Decrypt(data, encryptedData);
    
    //Interpret the data
    //First 20 bytes: keyID 
    std::vector<unsigned char>::const_iterator itData1 = data.begin();
    std::vector<unsigned char>::const_iterator itData2 = data.begin();
    std::vector<unsigned char>::const_iterator pend = data.end();
    std::vector<unsigned char> vKeyID, vPubKey;

    for(unsigned int i=0; i<pubKeySize; i++){
      if(itData2++ == pend) {
        bEnd=true;
        break;
      }
    }

    if(bEnd) break;

    CBitcoinAddress addrNew;
    addrNew.Set(CKeyID(uint160(std::vector<unsigned char>(itData1,itData2))));

    itData1=itData2;
    for(unsigned int i=0; i<pubKeySize; i++){
      if(itData2++ == pend){
      bEnd=true;
       break;
     }
    }
      
    if(bEnd) break;

    CPubKey pubKeyNew = CPubKey(itData1,itData2);
      try{
        //This will succeeed if the decrypted addresses are valid.
       add_derived(addrNew, pubKeyNew, kycKey);
       bSuccess=true;
      } catch (std::invalid_argument e){
       bSuccess=false; // Do nothing
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

