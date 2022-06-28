// Copyright (c) 2020-2021 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <consensus/consensus.h>
#include <net.h>
#include <net_processing.h>
#include <protocol.h>
#include <test/fuzz/FuzzedDataProvider.h>
#include <test/fuzz/fuzz.h>
#include <test/fuzz/util.h>
#include <test/util/mining.h>
#include <test/util/net.h>
#include <test/util/setup_common.h>
#include <test/util/validation.h>
#include <txorphanage.h>
#include <validation.h>
#include <validationinterface.h>

namespace {
const TestingSetup* g_setup;
} // namespace

void initialize_process_messages()
{
    static const auto testing_setup = MakeNoLogFileContext<const TestingSetup>();
    g_setup = testing_setup.get();
    for (int i = 0; i < 2 * COINBASE_MATURITY; i++) {
        MineBlock(g_setup->m_node, CScript() << OP_TRUE);
    }
    SyncWithValidationInterfaceQueue();
}

FUZZ_TARGET_INIT(process_messages, initialize_process_messages)
{
    FuzzedDataProvider fuzzed_data_provider(buffer.data(), buffer.size());

    ConnmanTestMsg& connman = *static_cast<ConnmanTestMsg*>(g_setup->m_node.connman.get());
    TestChainState& chainstate = *static_cast<TestChainState*>(&g_setup->m_node.chainman->ActiveChainstate());
    SetMockTime(1610000000); // any time to successfully reset ibd
    chainstate.ResetIbd();

    std::vector<CNode*> peers;
    const auto num_peers_to_add = fuzzed_data_provider.ConsumeIntegralInRange(1, 3);
    for (int i = 0; i < num_peers_to_add; ++i) {
        peers.push_back(ConsumeNodeAsUniquePtr(fuzzed_data_provider, i).release());
        CNode& p2p_node = *peers.back();

        const bool successfully_connected{fuzzed_data_provider.ConsumeBool()};
        p2p_node.fSuccessfullyConnected = successfully_connected;
        p2p_node.fPauseSend = false;
        g_setup->m_node.peerman->InitializeNode(&p2p_node);
        FillNode(fuzzed_data_provider, p2p_node, /* init_version */ successfully_connected);

        connman.AddTestNode(p2p_node);
    }

    int elements_iter_count = 0;
    while (fuzzed_data_provider.ConsumeBool()) {
        if (elements_iter_count++ > 100) {
            // ELEMENTS: this loop runs on a single core and achieves nothing that couldn't
            //  be achieved by just repeating the fuzz runs. It typically takes around 11
            //  minutes on Bitcoin and around 60 minutes on Elements (presumably because the
            //  seed vectors aren't valid Elements messages so the fuzzer gets lost and starts
            //  adding tons of iterations).
            //
            // Capping to 100 iterations reduces the run time to 4-5 minutes on both Bitcoin
            //  and Elements.
            break;
        }

        const std::string random_message_type{fuzzed_data_provider.ConsumeBytesAsString(CMessageHeader::COMMAND_SIZE).c_str()};

        const auto mock_time = ConsumeTime(fuzzed_data_provider);
        SetMockTime(mock_time);

        CSerializedNetMsg net_msg;
        net_msg.m_type = random_message_type;
        net_msg.data = ConsumeRandomLengthByteVector(fuzzed_data_provider);

        CNode& random_node = *PickValue(fuzzed_data_provider, peers);

        (void)connman.ReceiveMsgFrom(random_node, net_msg);
        random_node.fPauseSend = false;

        try {
            connman.ProcessMessagesOnce(random_node);
        } catch (const std::ios_base::failure&) {
        }
        {
            LOCK(random_node.cs_sendProcessing);
            g_setup->m_node.peerman->SendMessages(&random_node);
        }
    }
    SyncWithValidationInterfaceQueue();
    g_setup->m_node.connman->StopNodes();
}
