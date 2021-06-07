// Copyright (c) 2020 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <script/bitcoinconsensus.h>
#include <script/interpreter.h>
#include <test/fuzz/FuzzedDataProvider.h>
#include <test/fuzz/fuzz.h>
#include <test/fuzz/util.h>

#include <cstdint>
#include <string>
#include <vector>

void test_one_input(const std::vector<uint8_t>& buffer)
{
    FuzzedDataProvider fuzzed_data_provider(buffer.data(), buffer.size());
    const std::vector<uint8_t> random_bytes_1 = ConsumeRandomLengthByteVector(fuzzed_data_provider);
    const std::vector<uint8_t> random_bytes_2 = ConsumeRandomLengthByteVector(fuzzed_data_provider);
    const uint256 random_hash = ConsumeUInt256(fuzzed_data_provider);

    const std::optional<CConfidentialValue> money = ConsumeDeserializable<CConfidentialValue>(fuzzed_data_provider);
    bitcoinconsensus_error err;
    bitcoinconsensus_error* err_p = fuzzed_data_provider.ConsumeBool() ? &err : nullptr;
    const unsigned int n_in = fuzzed_data_provider.ConsumeIntegral<unsigned int>();
    const unsigned int flags = fuzzed_data_provider.ConsumeIntegral<unsigned int>();
    assert(bitcoinconsensus_version() == BITCOINCONSENSUS_API_VER);
    if ((flags & SCRIPT_VERIFY_WITNESS) != 0 && (flags & SCRIPT_VERIFY_P2SH) == 0) {
        return;
    }
    (void)bitcoinconsensus_verify_script(random_hash.begin() ,random_bytes_1.data(), random_bytes_1.size(), random_bytes_2.data(), random_bytes_2.size(), n_in, flags, err_p);
    if (money) {
        CDataStream data_stream(SER_NETWORK, PROTOCOL_VERSION);
        data_stream << *money;
        (void)bitcoinconsensus_verify_script_with_amount(random_hash.begin(), random_bytes_1.data(), random_bytes_1.size(), (unsigned char*) data_stream.data(), data_stream.size(), random_bytes_2.data(), random_bytes_2.size(), n_in, flags, err_p);
    }
}
