// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// An ecrypted "register address" transaction script.

#pragma once
#include "script.h"
#include "ecies_hex.h"
#include "validation.h"

using ucvec=std::vector<unsigned char>;

struct OnboardMultisig {
    uint8_t nMultisig;
    CTxDestination scriptID;
    std::vector<CPubKey> pubKeys;
    OnboardMultisig(uint8_t _nMultisig, CTxDestination _scriptID, std::vector<CPubKey> _pubKeys){
    	nMultisig = _nMultisig;
    	scriptID = _scriptID;
    	pubKeys = _pubKeys;
    }
};

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
	bool Append(const uint8_t nMultisig, const CTxDestination keyID, const std::vector<CPubKey>& keys);
	bool Append(const std::vector<OnboardMultisig>& _data);
	std::size_t getPayloadSize() { return _payload.size(); }

	virtual void clear(){_payload.clear(); _encrypted.clear(); ((CScript*)this)->clear();}

	//Make this a "deregister" transaction (remove address from whitelist).
	void SetDeregister(bool bDereg){
		bDereg ? _opcode = OP_DEREGISTERADDRESS: _opcode = OP_REGISTERADDRESS;
	}

protected:
	ucvec _payload;
	ucvec _encrypted;
	RegisterAddressType whitelistType;
	opcodetype _opcode = OP_REGISTERADDRESS;
};