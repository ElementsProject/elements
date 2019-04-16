// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//A thread-safe policy address list e.g. whitelist, freezelist, burnlist.

#pragma once

#include "pubkey.h"
#include "base58.h"
#include "utilstrencodings.h"
#include "util.h"
#include "coins.h"
#include <string>
#include <set>
#include <boost/thread/recursive_mutex.hpp>
#include <boost/thread/mutex.hpp>

class CPolicyList : private std::set<CKeyID>
{
  using base = std::set<CKeyID>;
  using baseIter = base::iterator;

 public:
  CPolicyList();
  virtual ~CPolicyList();
  void lock(){_mtx.lock();}
  void unlock(){_mtx.unlock();}
  bool find(const CKeyID* id);
  virtual void clear();
  baseIter remove(CKeyID* id);
  //virtual CKeyID at(base::size_type pos);
  virtual base::size_type size();
  void delete_address(std::string addressIn);

  //Enable public access to base class iterator accessors 
  using base::begin;
  using base::end;

  //This will be made prive int CWhitelist.
  virtual void add_sorted(CKeyID* keyId);
  void swap(CPolicyList* l_new);

  //Update from transaction
  virtual bool Update(const CTransaction& tx, const CCoinsViewCache& mapInputs);

 enum Errc{
    INVALID_ADDRESS_OR_KEY,
    INVALID_KEY_DERIVATION
  };

 protected:
	boost::recursive_mutex _mtx;
  CAsset _asset;

};
