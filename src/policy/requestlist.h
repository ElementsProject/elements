// Copyright (c) 2019 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// Class to store the list of requests

#ifndef OCEAN_REQUEST_LIST_H
#define OCEAN_REQUEST_LIST_H

#include <boost/thread/recursive_mutex.hpp>
#include <boost/thread/mutex.hpp>

#include <request.h>
#include <coins.h>

class CRequestList : private std::map<uint256, CRequest>
{
    using base = std::map<uint256, CRequest>;
    using baseIter = base::iterator;

public:
    CRequestList();
    virtual ~CRequestList();

    //Enable public access to base class iterator accessors
    using base::begin;
    using base::end;

    void lock(){_mtx.lock();}
    void unlock(){_mtx.unlock();}

    std::pair<bool, baseIter> find(const uint256 &txid);
    void clear();
    void remove(const uint256 &txid);
    void add(const uint256 &txid, CRequest *req);
    base::size_type size();

    // Load request list from utxo set
    bool Load(CCoinsView *view, uint32_t nHeight);
    bool LoadRequest(CTxOut out, uint256 hash, uint32_t nHeight, uint32_t nConfirmedHeight);
    // Load request bids from utxo set
    bool LoadBids(CCoinsView *view, uint32_t nHeight);
    bool LoadBid(vector<CTxOut> outs, uint256 hash, uint32_t nConfirmedHeight);

    // Remove any expired requests
    void RemoveExpired(uint32_t nHeight);


protected:
    boost::recursive_mutex _mtx;
};

#endif // OCEAN_REQUEST_LIST_H
