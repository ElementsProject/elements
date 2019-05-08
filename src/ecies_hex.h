// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//An implementation of ECIES AES256CBC Encryption with hexadecimal encoding

#ifndef OCEAN_ECIES_HEX_H
#define OCEAN_ECIES_HEX_H

#include "ecies.h"

class CECIES_hex: public CECIES{
public:
	CECIES_hex();
	~CECIES_hex();
private:
	virtual std::string Encode(const uCharVec& vch);
    virtual bool Decode(const std::string strIn, uCharVec& decoded);
};

#endif //#ifndef OCEAN_ECIES_HEX_H

