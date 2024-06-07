// Copyright (c) 2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <primitives/transaction.h>
extern "C" {
#include <simplicity/elements/env.h>
#include <simplicity/elements/exec.h>
}
#include <test/fuzz/FuzzedDataProvider.h>
#include <test/fuzz/fuzz.h>
#include <test/fuzz/util.h>

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

FUZZ_TARGET(simplicity)
{
    FuzzedDataProvider fuzzed_data_provider(buffer.data(), buffer.size());
    {
        const std::optional<CMutableTransaction> mtx_precomputed = ConsumeDeserializable<CMutableTransaction>(fuzzed_data_provider);
        if (mtx_precomputed) {
            const CTransaction tx_precomputed{*mtx_precomputed};
            const PrecomputedTransactionData precomputed_transaction_data{tx_precomputed};
            const transaction* tx = precomputed_transaction_data.m_simplicity_tx_data;

            const uint256 genesisBlockHash = precomputed_transaction_data.m_hash_genesis_block;

            std::vector<unsigned char> imr = fuzzed_data_provider.ConsumeBytes<unsigned char>(32);

            const uint_fast32_t ix = fuzzed_data_provider.ConsumeIntegral<uint_fast32_t>();

            const std::vector<unsigned char> control = ConsumeRandomLengthByteVector(fuzzed_data_provider);
            // control block invariant: 33 + pathLen*32
            // https://github.com/ElementsProject/elements/blob/174c46baecd/src/script/interpreter.cpp#L3285
            if (
                control.size() >= TAPROOT_CONTROL_BASE_SIZE &&
                control.size() <= TAPROOT_CONTROL_MAX_SIZE &&
                ((control.size() - TAPROOT_CONTROL_BASE_SIZE) % TAPROOT_CONTROL_NODE_SIZE) == 0
            ) {
                const std::vector<unsigned char> script_bytes = fuzzed_data_provider.ConsumeBytes<unsigned char>(32);
                // script_bytes invariant: 32 bytes
                // https://github.com/ElementsProject/elements/blob/174c46baecd/src/script/interpreter.cpp#L3300
                if (script_bytes.size() == 32) {
                    rawTapEnv simplicityRawTap;
                    simplicityRawTap.controlBlock = control.data();
                    simplicityRawTap.pathLen = (control.size() - TAPROOT_CONTROL_BASE_SIZE) / TAPROOT_CONTROL_NODE_SIZE;
                    simplicityRawTap.scriptCMR = script_bytes.data();
                    tapEnv* taproot = elements_simplicity_mallocTapEnv(&simplicityRawTap);

                    const int64_t budget = fuzzed_data_provider.ConsumeIntegral<int64_t>();
                    const std::vector<unsigned char> amr = fuzzed_data_provider.ConsumeBytes<unsigned char>(32);
                    const std::vector<unsigned char> program = ConsumeRandomLengthByteVector(fuzzed_data_provider);

                    simplicity_err error;
                    elements_simplicity_execSimplicity(&error, imr.data(), tx, ix, taproot, genesisBlockHash.data(), budget, amr.data(), program.data(), program.size());
                    free(taproot);
                }
            }
        }
    }
}
