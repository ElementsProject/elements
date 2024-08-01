#!/usr/bin/env python3
#
# Copyright (c) 2020-2022 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
#
# Check for circular dependencies

import glob
import os
import re
import subprocess
import sys

EXPECTED_CIRCULAR_DEPENDENCIES = (
    "chainparamsbase -> util/system -> chainparamsbase",
    "node/blockstorage -> validation -> node/blockstorage",
    "index/blockfilterindex -> node/blockstorage -> validation -> index/blockfilterindex",
    "index/base -> validation -> index/blockfilterindex -> index/base",
    "index/coinstatsindex -> node/coinstats -> index/coinstatsindex",
    "policy/fees -> txmempool -> policy/fees",
    "qt/addresstablemodel -> qt/walletmodel -> qt/addresstablemodel",
    "qt/recentrequeststablemodel -> qt/walletmodel -> qt/recentrequeststablemodel",
    "qt/sendcoinsdialog -> qt/walletmodel -> qt/sendcoinsdialog",
    "qt/transactiontablemodel -> qt/walletmodel -> qt/transactiontablemodel",
    "wallet/fees -> wallet/wallet -> wallet/fees",
    "wallet/wallet -> wallet/walletdb -> wallet/wallet",
    "node/coinstats -> validation -> node/coinstats",
)

CODE_DIR = "src"


def main():
    circular_dependencies = []
    exit_code = 0
    os.chdir(
        CODE_DIR
    )  # We change dir before globbing since glob.glob's root_dir option is only available in Python 3.10

    # Using glob.glob since subprocess.run's globbing won't work without shell=True
    files = []
    for path in ["*", "*/*", "*/*/*"]:
        for extension in ["h", "cpp"]:
            files.extend(glob.glob(f"{path}.{extension}"))

    command = ["python3", "../contrib/devtools/circular-dependencies.py", *files]
    dependencies_output = subprocess.run(
        command,
        stdout=subprocess.PIPE,
        universal_newlines=True,
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
