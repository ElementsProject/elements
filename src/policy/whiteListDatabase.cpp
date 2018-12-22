// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "whiteListDatabase.hpp"
#include "whiteList.hpp"

whiteListDatabase::whiteListDatabase(){;}
whiteListDatabase::~whiteListDatabase(){;}


//Read the keys from the database into the policy list.
void whiteListDatabase::read(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  begin();
  for(const bsoncxx::document::view doc : (*_cursor)){
    readAddressesKeys(&doc);
  }
}

void whiteListDatabase::readAddressesKeys(const bsoncxx::v_noabi::document::view* doc){
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    bsoncxx::document::element addEl=(*doc)["addresses"];
    bsoncxx::document::element keyEl=(*doc)["keys"]; 
    
    //Return if one or both arrays are empty/invalid.
    if(!addEl || !keyEl) return;

    bsoncxx::array::view subarr_add{addEl.get_array().value};
    bsoncxx::array::view subarr_key{keyEl.get_array().value};
    
  //Add all the keys in the subarrays to the policy list
    CWhiteList* wl = (CWhiteList*)_plist;

    auto it_add=subarr_add.begin();
    auto it_key=subarr_key.begin();
    while(it_add != subarr_add.end() &&
        it_key != subarr_key.end()){
		wl->add_derived(
        it_add->get_utf8().value.to_string(),
        it_key->get_utf8().value.to_string()
      );     
      it_add++;
      it_key++;
    }
}