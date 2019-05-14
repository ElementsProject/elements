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
    baseIter it = base::find(txid);
    if (it != this->end()) {
        return std::make_pair(true, it);
    }
    return std::make_pair(false, this->end());
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

/** Load request bid from utxo set */
bool CRequestList::LoadBid(vector<CTxOut> outs, uint256 hash, uint32_t nConfirmedHeight)
{
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    CBid bid;
    if (GetRequestBid(outs, hash, nConfirmedHeight, bid)) {
        auto res = base::find(bid.hashRequest);
        if (res != this->end()) {
            if (IsValidRequestBid(res->second, bid)) {
                bid.SetBidHash(hash);
                if (res->second.AddBid(bid))
                    return true;
            }
        }
    }
    return false;
}

/** Load request bids from utxo set */
bool CRequestList::LoadBids(CCoinsView *view, uint32_t nHeight)
{
    std::unique_ptr<CCoinsViewCursor> pcursor(view->Cursor());
    while (pcursor->Valid()) {
        boost::this_thread::interruption_point();
        uint256 key;
        CCoins coins;
        if (pcursor->GetKey(key) && pcursor->GetValue(coins)) {
            if (coins.vout.size() > 1){
                this->LoadBid(coins.vout, key, coins.nHeight);
            }
        } else {
            return error("%s: unable to read value", __func__);
        }
        pcursor->Next();
    }
    return true;
}

/** Load request from utxo set */
bool CRequestList::LoadRequest(CTxOut out, uint256 hash, uint32_t nHeight, uint32_t nConfirmedHeight)
{
    CRequest request;
    if (GetRequest(out, hash, nConfirmedHeight, request)) {
        if (IsValidRequest(request, nHeight)) {
            this->add(hash, &request);
            return true;
        }
    }
    return false;
}

/** Load request list from utxo set */
bool CRequestList::Load(CCoinsView *view, uint32_t nHeight)
{
    std::unique_ptr<CCoinsViewCursor> pcursor(view->Cursor());
    while (pcursor->Valid()) {
        boost::this_thread::interruption_point();
        uint256 key;
        CCoins coins;
        if (pcursor->GetKey(key) && pcursor->GetValue(coins)) {
            if (coins.vout.size() == 1 && !coins.IsCoinBase() &&
            coins.vout[0].nAsset.IsExplicit() && coins.vout[0].nAsset.GetAsset() == permissionAsset) {
                this->LoadRequest(coins.vout[0], key, nHeight, coins.nHeight);
            }
        } else {
            return error("%s: unable to read value", __func__);
        }
        pcursor->Next();
    }
    return LoadBids(view, nHeight);
}

/** Remove any expired requests */
void CRequestList::RemoveExpired(uint32_t nHeight)
{
    boost::recursive_mutex::scoped_lock scoped_lock(_mtx);
    for (auto it = this->begin(); it != this->cend();)
    {
        if (it->second.nEndBlockHeight < nHeight) {
            it = base::erase(it);
        }
        else {
            ++it;
        }
    }
}
