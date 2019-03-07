// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "policylist.h"


CPolicyList::CPolicyList(){;}
CPolicyList::~CPolicyList(){;}

void CPolicyList::delete_address(std::string addressIn){
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  }

bool CPolicyList::find(const CKeyID* id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);  
  return(base::find(*id) != end());
}

void CPolicyList::clear(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return base::clear();
}

//Erase ocean, and return the next valid iterator.
CPolicyList::baseIter CPolicyList::remove(CKeyID* id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  baseIter it = base::find(*id);
  if(it == this->end()) return it;
  return base::erase(it);
}

//CKeyID CPolicyList::at(base::size_type pos) {
//  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
//  return base::at(pos);
//}

CPolicyList::base::size_type CPolicyList::size(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return base::size();
}

//Add to the sorted list
void CPolicyList::add_sorted(CKeyID* id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  base::insert(*id);
}

//Swap the contents of this list for another list.
void CPolicyList::swap(CPolicyList* l_new){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  base::swap(*l_new);
}

//Update from transaction
bool CPolicyList::Update(const CTransaction& tx, const CCoinsViewCache& mapInputs)
{
    if (tx.IsCoinBase())
      return false; // Coinbases don't use vin normally

    // check inputs for encoded address data
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxOut& prev = mapInputs.GetOutputFor(tx.vin[i]);

        std::vector<std::vector<unsigned char> > vSolutions;
        txnouttype whichType;

        const CScript& prevScript = prev.scriptPubKey;
        if (!Solver(prevScript, whichType, vSolutions)) continue;

        // extract address from second multisig public key and remove from freezelist
        // encoding: 33 byte public key: address is encoded in the last 20 bytes (i.e. byte 14 to 33)
        if (whichType == TX_MULTISIG && vSolutions.size() == 4)
        {
            CKeyID keyId;
            std::vector<unsigned char> ex_addr;
            std::vector<unsigned char>::const_iterator first = vSolutions[2].begin() + 13;
            std::vector<unsigned char>::const_iterator last = vSolutions[2].begin() + 32;
            std::vector<unsigned char> extracted_addr(first,last);

            keyId = CKeyID(uint160(extracted_addr));

            remove(&keyId);
        }
    }

    //check outputs for encoded address data
    for (unsigned int i = 0; i < tx.vout.size(); i++) {
        const CTxOut& txout = tx.vout[i];

        std::vector<std::vector<unsigned char> > vSolutions;
        txnouttype whichType;

        if (!Solver(txout.scriptPubKey, whichType, vSolutions)) continue;

        // extract address from second multisig public key and add to the freezelist
        // encoding: 33 byte public key: address is encoded in the last 20 bytes (i.e. byte 14 to 33)
        if (whichType == TX_MULTISIG && vSolutions.size() == 4)
        {
            CKeyID keyId;
            std::vector<unsigned char> ex_addr;
            std::vector<unsigned char>::const_iterator first = vSolutions[2].begin() + 13;
            std::vector<unsigned char>::const_iterator last = vSolutions[2].begin() + 32;
            std::vector<unsigned char> extracted_addr(first,last);

            keyId = CKeyID(uint160(extracted_addr));

            add_sorted(&keyId);
        }
    }
    return true;
}
