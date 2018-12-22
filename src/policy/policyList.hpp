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
 public:
  CPolicyList();
  ~CPolicyList();
  void lock(){_mtx.lock();}
  void unlock(){_mtx.unlock();}
  bool find(CKeyID* id);
  virtual void clear();
  void remove(CKeyID* id);
  virtual CKeyID at(std::vector<CKeyID>::size_type pos);
  virtual std::vector<CKeyID>::size_type size();
  void delete_address(std::string addressIn);

  //This will be made prive int CWhitelist.
  virtual void add_sorted(CKeyID* keyId);

 enum Errc{
    INVALID_ADDRESS_OR_KEY,
    INVALID_KEY_DERIVATION
  };

 protected:
	boost::recursive_mutex _mtx;
};
