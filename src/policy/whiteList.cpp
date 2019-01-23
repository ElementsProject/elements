// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "whiteList.hpp"
#include "validation.h"

CWhiteList::CWhiteList(){;}
CWhiteList::~CWhiteList(){;}

void CWhiteList::add_derived(CBitcoinAddress address, CPubKey pubKey){
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
}

void CWhiteList::add_derived(std::string addressIn, std::string key){
   boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    CBitcoinAddress address;
  if (!address.SetString(addressIn))
    throw std::system_error(
          std::error_code(CPolicyList::Errc::INVALID_ADDRESS_OR_KEY, 
              std::system_category()), 
          std::string(std::string(__func__) + ": invalid Bitcoin address: ") + addressIn);
  

  std::vector<unsigned char> pubKeyData(ParseHex(key));
  CPubKey pubKey = CPubKey(pubKeyData.begin(), pubKeyData.end());

  add_derived(address, pubKey);
}



