// Copyright (c) 2020-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_SCRIPT_PEGINS_H
#define BITCOIN_SCRIPT_PEGINS_H

#include <primitives/transaction.h>
#include <script/script.h>

// Constructs unblinded output to be used in amount and scriptpubkey checks during pegin
CTxOut GetPeginOutputFromWitness(const CScriptWitness& pegin_witness);

#endif // BITCOIN_SCRIPT_PEGINS_H
