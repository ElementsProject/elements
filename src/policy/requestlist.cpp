// Copyright (c) 2019 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "requestlist.h"
#include "policy/policy.h"
#include "util.h"

CRequestList::CRequestList(){;}
CRequestList::~CRequestList(){;}

std::pair<bool, CRequestList::baseIter> CRequestList::find(const uint256 &txid)
{
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  base::find(txid);
}

void CRequestList::clear()
{
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return base::clear();
}

void CRequestList::remove(const uint256 &txid)
{
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  baseIter it = base::find(txid);
  if(it != this->end())
    base::erase(it);
}

CRequestList::base::size_type CRequestList::size()
{
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  return base::size();
}

void CRequestList::add(const uint256 &txid, CRequest *req)
{
  boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
  base::insert(std::make_pair(txid, *req));
}

/** Load request list from utxo set */
bool CRequestList::Load(CCoinsView *view)
{
    std::unique_ptr<CCoinsViewCursor> pcursor(view->Cursor());
    while (pcursor->Valid()) {
        boost::this_thread::interruption_point();
        uint256 key;
        CCoins coins;
        if (pcursor->GetKey(key) && pcursor->GetValue(coins)) {
            if (coins.vout.size() == 1 && !coins.IsCoinBase() &&
            coins.vout[0].nAsset.IsExplicit() && coins.vout[0].nAsset.GetAsset() == permissionAsset) {
                vector<vector<unsigned char>> vSolutions;
                txnouttype whichType;
                if (Solver(coins.vout[0].scriptPubKey, whichType, vSolutions)
                && whichType == TX_LOCKED_MULTISIG) {
                    auto request = CRequest::FromSolutions(vSolutions);
                    add(key, &request);
                }
            }
        } else {
            return error("%s: unable to read value", __func__);
        }
        pcursor->Next();
    }
    return true;
}
