// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "whiteListDatabase.hpp"
#include "whiteList.hpp"

whiteListDatabase::whiteListDatabase(){;}
whiteListDatabase::~whiteListDatabase(){;}


//Synchronise the local whitelist with the database.
void whiteListDatabase::synchronise(){
  //No mutex lock - filling the temporary list is thread safe.
  //begin() and CWhiteList::swap() have their own mutex locks.
  begin();
  auto doc = _cursor->begin();
  //std::cout << bsoncxx::to_json(*doc) << "\n";
  //Read keys into a temporary whitelist.
  CWhiteList* wlTemp = new CWhiteList();
  for(const bsoncxx::document::view doc : (*_cursor)){
    readAddressesKeys(&doc, wlTemp);
  }
  //Swap contexts of new list into old
  _plist->swap(wlTemp);
  delete wlTemp;
}

//Read addresses and keys into the live whitelist.
void whiteListDatabase::readAddressesKeys(const bsoncxx::v_noabi::document::view* doc){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  CWhiteList* wl = (CWhiteList*)_plist;
  readAddressesKeys(doc, wl);
}

//Read addresses and keys into a whitelist.
//This function is not thread safe so should only be used 
//with a temporary whitelist owned by the function. 
//E.g. see whiteListDatabase::synchronise()
void whiteListDatabase::readAddressesKeys(const bsoncxx::v_noabi::document::view* doc,
                                          CWhiteList* wl){
    bsoncxx::document::element addEl=(*doc)["addresses"];
    bsoncxx::document::element keyEl=(*doc)["keys"]; 
    
    //Return if one or both arrays are empty/invalid.
    if(!addEl || !keyEl) return;

    bsoncxx::array::view subarr_add{addEl.get_array().value};
    bsoncxx::array::view subarr_key{keyEl.get_array().value};
    
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