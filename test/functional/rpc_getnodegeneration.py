#!/usr/bin/env python3
# Copyright (c) 2026 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test process and active-chain generation identity."""

import hashlib
import platform
import threading
import time

from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    assert_raises_rpc_error,
    get_rpc_proxy,
)


class NodeGenerationTest(BitcoinTestFramework):
    def set_test_params(self):
        self.num_nodes = 1
        self.setup_clean_chain = True
        self.extra_args = [["-rpcdoccheck=1"]]

    @staticmethod
    def assert_generation_schema(generation):
        assert_equal(set(generation), {
            "startup_id",
            "chainstate_revision",
            "blocks",
            "bestblockhash",
        })
        assert isinstance(generation["startup_id"], str)
        assert_equal(len(generation["startup_id"]), 64)
        int(generation["startup_id"], 16)
        assert generation["startup_id"] != "0" * 64
        assert isinstance(generation["chainstate_revision"], int)
        assert 0 <= generation["chainstate_revision"] <= 2**64 - 1
        assert isinstance(generation["blocks"], int)
        assert_equal(len(generation["bestblockhash"]), 64)
        int(generation["bestblockhash"], 16)

    @staticmethod
    def common_derived_identifiers(pid, observed_time):
        """Return common PID/time/uptime derivations a mutation must not use."""
        source_bytes = {
            str(pid).encode(),
            pid.to_bytes(4, byteorder="big", signed=False),
            pid.to_bytes(4, byteorder="little", signed=False),
        }
        numeric_values = {pid, *range(0, 11)}
        for second in range(observed_time - 5, observed_time + 6):
            numeric_values.add(second)
        observed_millis = observed_time * 1000
        for millis in range(observed_millis - 2000, observed_millis + 2001):
            numeric_values.add(millis)

        for value in numeric_values:
            source_bytes.add(str(value).encode())
            if value >= 0:
                source_bytes.add(value.to_bytes(32, byteorder="big", signed=False))
                source_bytes.add(value.to_bytes(32, byteorder="little", signed=False))

        derived = set()
        for source in source_bytes:
            if len(source) <= 32:
                derived.add(source.rjust(32, b"\x00").hex())
                derived.add(source.ljust(32, b"\x00").hex())
            first_hash = hashlib.sha256(source).digest()
            second_hash = hashlib.sha256(first_hash).digest()
            for digest in (first_hash, second_hash):
                derived.add(digest.hex())
                derived.add(digest[::-1].hex())
        return derived

    def assert_fresh_process_generation(self, seen_startup_ids):
        node = self.nodes[0]
        generation = node.getnodegeneration()
        self.assert_generation_schema(generation)
        assert generation["startup_id"] not in seen_startup_ids
        assert generation["startup_id"] not in self.common_derived_identifiers(
            node.process.pid,
            int(time.time()),
        )
        seen_startup_ids.add(generation["startup_id"])
        return generation

    def test_process_identity(self):
        node = self.nodes[0]
        seen_startup_ids = set()

        first = self.assert_fresh_process_generation(seen_startup_ids)
        assert_equal(node.getnodegeneration(), first)
        assert_equal(node.getnodegeneration(), first)

        self.restart_node(0)
        self.assert_fresh_process_generation(seen_startup_ids)

        environment_sentinel = "a5" * 32
        self.stop_node(0)
        self.start_node(0, env={"ELEMENTS_STARTUP_ID": environment_sentinel})
        environment_generation = self.assert_fresh_process_generation(seen_startup_ids)
        assert environment_generation["startup_id"] != environment_sentinel

        node.process.kill()
        node.wait_until_stopped(expected_ret_code=1 if platform.system() == "Windows" else -9)
        self.start_node(0)
        self.assert_fresh_process_generation(seen_startup_ids)

        self.stop_node(0)
        node.assert_start_raises_init_error(
            extra_args=[f"-nodegenerationstartupid={environment_sentinel}"],
        )
        with open(node.bitcoinconf, "a", encoding="utf8") as config:
            config.write(f"nodegenerationstartupid={environment_sentinel}\n")
        with node.assert_debug_log(expected_msgs=[
            "Ignoring unknown configuration value elementsregtest.nodegenerationstartupid",
        ]):
            self.start_node(0)
        config_generation = self.assert_fresh_process_generation(seen_startup_ids)
        assert config_generation["startup_id"] != environment_sentinel

    def test_schema_and_help(self):
        node = self.nodes[0]
        generation = node.getnodegeneration()
        self.assert_generation_schema(generation)
        assert_equal(generation["blocks"], node.getblockcount())
        assert_equal(generation["bestblockhash"], node.getbestblockhash())
        assert_raises_rpc_error(-1, "getnodegeneration", node.getnodegeneration, 1)

        help_text = node.help("getnodegeneration")
        for text in (
            "startup_id",
            "chainstate_revision",
            "blocks",
            "bestblockhash",
            "ABA detection",
            "process restart",
            "chainstate_revision changes",
            "do not establish binary provenance",
            "do not prove that the connected node is honest",
        ):
            assert text in help_text

    def test_active_chain_transitions_and_aba(self):
        node = self.nodes[0]
        base = node.getnodegeneration()
        base_height = base["blocks"]
        base_hash = base["bestblockhash"]

        first_block = self.generate(node, 1, sync_fun=self.no_op)[0]
        connected = node.getnodegeneration()
        assert_equal(connected["chainstate_revision"], base["chainstate_revision"] + 1)
        assert_equal((connected["blocks"], connected["bestblockhash"]), (base_height + 1, first_block))

        node.invalidateblock(first_block)
        disconnected = node.getnodegeneration()
        assert_equal(disconnected["chainstate_revision"], connected["chainstate_revision"] + 1)
        assert_equal((disconnected["blocks"], disconnected["bestblockhash"]), (base_height, base_hash))

        node.reconsiderblock(first_block)
        reconnected = node.getnodegeneration()
        assert_equal(reconnected["chainstate_revision"], disconnected["chainstate_revision"] + 1)
        assert_equal((reconnected["blocks"], reconnected["bestblockhash"]), (base_height + 1, first_block))

        before_aba = node.getnodegeneration()
        branch_a = self.generate(node, 3, sync_fun=self.no_op)
        branch_a_tip = node.getnodegeneration()
        assert_equal(branch_a_tip["chainstate_revision"], before_aba["chainstate_revision"] + 3)

        node.invalidateblock(branch_a[0])
        branch_point = node.getnodegeneration()
        assert_equal(branch_point["chainstate_revision"], branch_a_tip["chainstate_revision"] + 3)
        assert_equal(branch_point["bestblockhash"], first_block)

        # Ensure the replacement branch does not reproduce the deterministic
        # signed block that was just invalidated.
        node.setmocktime(node.getblockheader(branch_a[-1])["time"] + 100)
        branch_b = self.generate(node, 2, sync_fun=self.no_op)
        branch_b_tip = node.getnodegeneration()
        assert_equal(branch_b_tip["chainstate_revision"], branch_point["chainstate_revision"] + 2)
        assert_equal(branch_b_tip["bestblockhash"], branch_b[-1])

        node.reconsiderblock(branch_a[0])
        aba_result = node.getnodegeneration()
        assert_equal(aba_result["chainstate_revision"], branch_b_tip["chainstate_revision"] + 5)
        assert_equal(aba_result["blocks"], branch_a_tip["blocks"])
        assert_equal(aba_result["bestblockhash"], branch_a_tip["bestblockhash"])

    def test_concurrent_atomic_sampling(self):
        node = self.nodes[0]
        sampler_rpc = get_rpc_proxy(
            node.url,
            node.index + 100,
            timeout=600,
            coveragedir=node.coverage_dir,
        )
        observations = []
        sampler_errors = []
        stop_sampling = threading.Event()

        def sample_generation():
            try:
                while not stop_sampling.is_set():
                    observations.append(sampler_rpc.getnodegeneration())
                    time.sleep(0.001)
            except Exception as error:  # Test thread reports failures to the main thread.
                sampler_errors.append(error)

        initial = node.getnodegeneration()
        expected_height = initial["blocks"]
        expected_hash = initial["bestblockhash"]
        previous_revision = initial["chainstate_revision"]
        expected_by_revision = {
            previous_revision: (expected_height, expected_hash),
        }

        def record_transition(height, block_hash):
            nonlocal previous_revision
            generation = node.getnodegeneration()
            assert_equal(generation["chainstate_revision"], previous_revision + 1)
            assert_equal((generation["blocks"], generation["bestblockhash"]), (height, block_hash))
            previous_revision = generation["chainstate_revision"]
            expected_by_revision[previous_revision] = (height, block_hash)

        sampler = threading.Thread(target=sample_generation, daemon=True)
        sampler.start()
        try:
            for _ in range(25):
                parent_height = expected_height
                parent_hash = expected_hash
                block_hash = self.generate(node, 1, sync_fun=self.no_op)[0]
                expected_height += 1
                expected_hash = block_hash
                record_transition(expected_height, expected_hash)

                node.invalidateblock(block_hash)
                expected_height = parent_height
                expected_hash = parent_hash
                record_transition(expected_height, expected_hash)

                node.reconsiderblock(block_hash)
                expected_height += 1
                expected_hash = block_hash
                record_transition(expected_height, expected_hash)
        finally:
            stop_sampling.set()
            sampler.join(timeout=10)

        assert not sampler.is_alive()
        assert not sampler_errors
        assert observations
        startup_id = initial["startup_id"]
        for observation in observations:
            assert_equal(observation["startup_id"], startup_id)
            revision = observation["chainstate_revision"]
            assert revision in expected_by_revision
            assert_equal(
                (observation["blocks"], observation["bestblockhash"]),
                expected_by_revision[revision],
            )

    def run_test(self):
        self.test_process_identity()
        self.test_schema_and_help()
        self.test_active_chain_transitions_and_aba()
        self.test_concurrent_atomic_sampling()


if __name__ == "__main__":
    NodeGenerationTest(__file__).main()
