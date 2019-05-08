// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//An implementation of ECIES AES256CBC Encryption, with hex encoding

#include "ecies_hex.h"
#include "utilstrencodings.h"

CECIES_hex::CECIES_hex(){;}
CECIES_hex::~CECIES_hex(){;}

std::string CECIES_hex::Encode(const uCharVec& vch){
	return HexStr(vch);
}

bool CECIES_hex::Decode(const std::string strIn, uCharVec& decoded){
	if(!IsHex(strIn)) return false;
	decoded=ParseHex(strIn);
}