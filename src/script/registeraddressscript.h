// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// An ecrypted "register address" transaction script.

#pragma once
#include "script.h"
#include "ecies_hex.h"
#include "validation.h"

using ucvec=std::vector<unsigned char>;

enum RegisterAddressType { RA_PUBLICKEY, RA_MULTISIG, RA_ONBOARDING };

class CRegisterAddressScript {
public:
	CRegisterAddressScript(RegisterAddressType type);
	CRegisterAddressScript(const CRegisterAddressScript* script, RegisterAddressType type);
	virtual ~CRegisterAddressScript();

	//Encrypt the payload using the public, private key and build the script.
	virtual bool Finalize(CScript& script, const CPubKey& ePubKey, const CKey& ePrivKey);
	virtual bool FinalizeUnencrypted(CScript& script);
	bool Append(const CPubKey& key);
	bool Append(const std::vector<CPubKey>& keys);
	bool Append(const int nMultisig, const CTxDestination keyID, const std::vector<CPubKey>& keys);

	virtual void clear(){_payload.clear(); _encrypted.clear(); ((CScript*)this)->clear();}

protected:
	ucvec _payload;
	ucvec _encrypted;
	RegisterAddressType whitelistType;
};