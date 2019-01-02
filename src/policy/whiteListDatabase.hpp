// Copyright (c) 2018 The CommerceBlock Developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#pragma once
#include "policyListDatabase.hpp"
#include "whiteList.hpp"

class whiteListDatabase : public policyListDatabase{
public:
	whiteListDatabase();
	virtual ~whiteListDatabase();

	virtual void synchronise();

private:
	virtual void collectionName(){_collectionName="whitelist";}
	virtual void readAddressesKeys(const bsoncxx::v_noabi::document::view* doc);
	virtual void readAddressesKeys(const bsoncxx::v_noabi::document::view* doc, CWhiteList* wl);
};