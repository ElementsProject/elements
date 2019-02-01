// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "policyList.h"


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
  return base::clear();
}

//Erase ocean, and return the next valid iterator.
CPolicyList::baseIter CPolicyList::remove(CKeyID* id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return erase(std::remove(begin(),end(),*id),end());
}

CKeyID CPolicyList::at(base::size_type pos) {
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return base::at(pos);
}

CPolicyList::base::size_type CPolicyList::size(){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return base::size();
}

//Add to the sorted list
void CPolicyList::add_sorted(CKeyID* id){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  if(!find(id)) {
    baseIter it = std::lower_bound(begin(),end(),*id);
    insert(it,*id);
  }
}

//Swap the contents of this list for another list.
void CPolicyList::swap(CPolicyList* l_new){
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  base::swap(*l_new);
}

