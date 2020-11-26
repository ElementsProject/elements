// Copyright (c) 2020-2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// ELEMENTS

#include <primitives/transaction.h>
#include <script/pegins.h>
#include <script/script.h>
#include <streams.h>
#include <version.h>

CTxOut GetPeginOutputFromWitness(const CScriptWitness& pegin_witness) {
    if (pegin_witness.stack.size() < 4) {
        return CTxOut();
    }

    CDataStream stream(pegin_witness.stack[0], SER_NETWORK, PROTOCOL_VERSION);
    CAmount value;
    stream >> value;

    return CTxOut(CAsset(pegin_witness.stack[1]), CConfidentialValue(value), CScript(pegin_witness.stack[3].begin(), pegin_witness.stack[3].end()));
}
