// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//A thread-safe policy address list e.g. whitelist, freezelist, burnlist.

#pragma once

#include "pubkey.h"
#include "base58.h"
#include "utilstrencodings.h"
#include "util.h"
#include <string>
#include <vector>
#include <boost/thread/recursive_mutex.hpp>
#include <boost/thread/mutex.hpp>

class CPolicyList : private std::vector<CKeyID>
{
  using base = std::vector<CKeyID>;
  using baseIter = base::iterator;

 public:
  CPolicyList();
  virtual ~CPolicyList();
  void lock(){_mtx.lock();}
  void unlock(){_mtx.unlock();}
  bool find(CKeyID* id);
  virtual void clear();
  baseIter remove(CKeyID* id);
  virtual CKeyID at(base::size_type pos);
  virtual base::size_type size();
  void delete_address(std::string addressIn);

  //This will be made prive int CWhitelist.
  virtual void add_sorted(CKeyID* keyId);
  void swap(CPolicyList* l_new);

 enum Errc{
    INVALID_ADDRESS_OR_KEY,
    INVALID_KEY_DERIVATION
  };

 protected:
	boost::recursive_mutex _mtx;
};
