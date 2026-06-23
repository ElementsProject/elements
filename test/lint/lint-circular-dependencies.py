#!/usr/bin/env python3
#
# Copyright (c) 2020-2022 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
#
# Check for circular dependencies

import os
import re
import subprocess
import sys

EXPECTED_CIRCULAR_DEPENDENCIES = (
    "chainparamsbase -> common/args -> chainparamsbase",
    "node/blockstorage -> validation -> node/blockstorage",
    "node/utxo_snapshot -> validation -> node/utxo_snapshot",
    "qt/addresstablemodel -> qt/walletmodel -> qt/addresstablemodel",
    "qt/recentrequeststablemodel -> qt/walletmodel -> qt/recentrequeststablemodel",
    "qt/sendcoinsdialog -> qt/walletmodel -> qt/sendcoinsdialog",
    "qt/transactiontablemodel -> qt/walletmodel -> qt/transactiontablemodel",
    "wallet/wallet -> wallet/walletdb -> wallet/wallet",
    "kernel/coinstats -> validation -> kernel/coinstats",

    # Temporary, removed in followup https://github.com/bitcoin/bitcoin/pull/24230
    "index/base -> node/context -> net_processing -> index/blockfilterindex -> index/base",
    # ELEMENTs: introduced by https://github.com/ElementsProject/elements/pull/1270
    "chain -> validation -> chain",
    "chain -> validation -> consensus/tx_verify -> chain",
    "dynafed -> validation -> dynafed",
    "pegins -> validation -> pegins",
    "chain -> node/context -> net_processing -> headerssync -> chain",
    "chain -> node/context -> net_processing -> index/blockfilterindex -> chain",
    "chain -> node/context -> txmempool -> chain",
    "chain -> validation -> deploymentstatus -> chain",
    "chain -> validation -> pow -> chain",
    "chain -> validation -> primitives/pak -> chain",
    "chain -> validation -> validationinterface -> chain",
    "chain -> validation -> versionbits -> chain",
    "confidential_validation -> pegins -> validation -> confidential_validation",
    "consensus/tx_verify -> pegins -> validation -> consensus/tx_verify",
    "dynafed -> validation -> primitives/pak -> dynafed",
    "pegins -> validation -> txmempool -> pegins",
    "block_proof -> chain -> validation -> block_proof",
    "block_proof -> chain -> validation -> txdb -> block_proof",
    "chain -> node/context -> net_processing -> node/blockstorage -> chain",
    "consensus/tx_verify -> pegins -> validation -> txmempool -> consensus/tx_verify",
    "block_proof -> chain -> node/context -> net_processing -> node/blockstorage -> block_proof",
    "core_io -> script/sign -> pegins -> validation -> signet -> core_io",
    # ELEMENTS: will be fixed by blinding cleanup
    "blindpsbt -> psbt -> blindpsbt",
    # ELEMENTS FIXME: introduced during 25-26 merges
    "chain -> validation -> kernel/chain -> chain",
    "chain -> node/context -> node/kernel_notifications -> chain",
    "interfaces/chain.h -> validation -> kernel/chain -> interfaces/chain.h",
)

CODE_DIR = "src"


def main():
    circular_dependencies = []
    exit_code = 0

    os.chdir(CODE_DIR)
    files = subprocess.check_output(
        ['git', 'ls-files', '--', '*.h', '*.cpp'],
        text=True,
    ).splitlines()

    command = [sys.executable, "../contrib/devtools/circular-dependencies.py", *files]
    dependencies_output = subprocess.run(
        command,
        stdout=subprocess.PIPE,
        text=True,
    )

    for dependency_str in dependencies_output.stdout.rstrip().split("\n"):
        circular_dependencies.append(
            re.sub("^Circular dependency: ", "", dependency_str)
        )

    # Check for an unexpected dependencies
    for dependency in circular_dependencies:
        if dependency not in EXPECTED_CIRCULAR_DEPENDENCIES:
            exit_code = 1
            print(
                f'A new circular dependency in the form of "{dependency}" appears to have been introduced.\n',
                file=sys.stderr,
            )

    # Check for missing expected dependencies
    for expected_dependency in EXPECTED_CIRCULAR_DEPENDENCIES:
        if expected_dependency not in circular_dependencies:
            exit_code = 1
            print(
                f'Good job! The circular dependency "{expected_dependency}" is no longer present.',
            )
            print(
                f"Please remove it from EXPECTED_CIRCULAR_DEPENDENCIES in {__file__}",
            )
            print(
                "to make sure this circular dependency is not accidentally reintroduced.\n",
            )

    sys.exit(exit_code)


if __name__ == "__main__":
    main()
