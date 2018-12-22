// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "policyList.hpp"


CPolicyList::CPolicyList(){;}
CPolicyList::~CPolicyList(){;}

void CPolicyList::delete_address(std::string addressIn){
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  }

bool CPolicyList::find(CKeyID* id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return std::binary_search(begin(),end(),*id);
}

void CPolicyList::clear(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return std::vector<CKeyID>::clear();
}

void CPolicyList::remove(CKeyID* id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  erase(std::remove(begin(),end(),*id),end());
}

CKeyID CPolicyList::at(std::vector<CKeyID>::size_type pos) {
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return std::vector<CKeyID>::at(pos);
}

std::vector<CKeyID>::size_type CPolicyList::size(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return std::vector<CKeyID>::size();
}

//Add to the sorted list
void CPolicyList::add_sorted(CKeyID* id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if(!find(id)) {
    std::vector<CKeyID>::iterator it = std::lower_bound(begin(),end(),*id);
    insert(it,*id);
  }
}