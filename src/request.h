// Copyright (c) 2019 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef OCEAN_REQUEST_H
#define OCEAN_REQUEST_H

#include "version.h"
#include "streams.h"
#include "uint256.h"
#include "pubkey.h"
#include "amount.h"
#include "script/script.h"

using namespace std;

/** Class for service request winning bids */
class CBid {
public:
    uint32_t nLockBlockHeight;
    uint32_t nConfirmedBlockHeight;
    uint256 hashRequest;
    CPubKey feePubKey;
    CAmount nStakePrice;

    uint256 hashBid;
    void SetBidHash(const uint256 &hash) { hashBid = hash; };

    static CBid FromSolutions(const vector<vector<unsigned char>> &vSolutions, CAmount nAmount, uint32_t nConfirmedHeight)
    {
        CBid bid;
        char pubInt;
        CDataStream output3(vSolutions[3], SER_NETWORK, PROTOCOL_VERSION);
        output3 >> pubInt;
        output3 >> bid.hashRequest;
        bid.feePubKey = CPubKey(vSolutions[4]);

        bid.nLockBlockHeight = CScriptNum(vSolutions[0], true).getint();
        bid.nConfirmedBlockHeight = nConfirmedHeight;
        bid.nStakePrice = nAmount;
        return bid;
    }

    bool operator<(const CBid& other) const
    {
        if (nConfirmedBlockHeight != other.nConfirmedBlockHeight) {
            return nConfirmedBlockHeight < other.nConfirmedBlockHeight;
        } else if (nStakePrice != other.nStakePrice) {
            return nStakePrice > other.nStakePrice;
        }
        return hashBid < other.hashBid;
    }
};

/** Class for service requests */
class CRequest {
public:
    uint32_t nNumTickets;
    uint32_t nDecayConst;
    uint32_t nFeePercentage;
    uint32_t nStartBlockHeight;
    uint32_t nEndBlockHeight;
    uint32_t nConfirmedBlockHeight;
    uint256 hashGenesis;
    CAmount nStartPrice;

    set<CBid> sBids;
    bool AddBid(const CBid &bid)
    {
        if (sBids.insert(bid).second) {
            // If size exceeded, remove the last element
            // Size might be exceeded in the rescan case only
            if (sBids.size() > nNumTickets) {
                sBids.erase(prev(sBids.end()));
            }
            return true;
        }
        return false;
    };

    CAmount GetAuctionPrice(uint32_t height) const
    {
        uint32_t t = height - nConfirmedBlockHeight;
        if(t < 0) return 0; // auction not started yet
        return nStartPrice*(1 + t)/(1 + t + pow(t,3)/nDecayConst);
    }

    static CRequest FromSolutions(const vector<vector<unsigned char>> &vSolutions, uint32_t nConfirmedHeight)
    {
        CRequest request;
        request.nEndBlockHeight = CScriptNum(vSolutions[0], true).getint();
        char pubInt;
        CDataStream output3(vSolutions[3], SER_NETWORK, PROTOCOL_VERSION);
        output3 >> pubInt;
        output3 >> request.hashGenesis;
        CDataStream output4(vSolutions[4], SER_NETWORK, PROTOCOL_VERSION);
        output4 >> pubInt;
        output4 >> request.nStartBlockHeight;
        output4 >> request.nNumTickets;
        output4 >> request.nDecayConst;
        output4 >> request.nFeePercentage;
        output4 >> request.nStartPrice;

        request.nConfirmedBlockHeight = nConfirmedHeight;
        return request;
    }
};

#endif // OCEAN_REQUEST_H
