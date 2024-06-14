#!/usr/bin/env bash
#
# Copyright (c) 2018-2021 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
#
# Check for circular dependencies

export LC_ALL=C

EXPECTED_CIRCULAR_DEPENDENCIES=(
    "chainparamsbase -> util/system -> chainparamsbase"
    "node/blockstorage -> validation -> node/blockstorage"
    "index/blockfilterindex -> node/blockstorage -> validation -> index/blockfilterindex"
    "index/base -> validation -> index/blockfilterindex -> index/base"
    "index/coinstatsindex -> node/coinstats -> index/coinstatsindex"
    "policy/fees -> txmempool -> policy/fees"
    "qt/addresstablemodel -> qt/walletmodel -> qt/addresstablemodel"
    "qt/recentrequeststablemodel -> qt/walletmodel -> qt/recentrequeststablemodel"
    "qt/sendcoinsdialog -> qt/walletmodel -> qt/sendcoinsdialog"
    "qt/transactiontablemodel -> qt/walletmodel -> qt/transactiontablemodel"
    "wallet/fees -> wallet/wallet -> wallet/fees"
    "wallet/wallet -> wallet/walletdb -> wallet/wallet"
    "node/coinstats -> validation -> node/coinstats"
    # ELEMENTs: introduced by https://github.com/ElementsProject/elements/pull/1270
    "chain -> validation -> chain"
    "chain -> validation -> consensus/tx_verify -> chain"
    "dynafed -> validation -> dynafed"
    "pegins -> validation -> pegins"
    "chain -> node/context -> txmempool -> chain"
    "chain -> validation -> deploymentstatus -> chain"
    "chain -> validation -> index/blockfilterindex -> chain"
    "chain -> validation -> primitives/pak -> chain"
    "chain -> validation -> txdb -> chain"
    "chain -> validation -> validationinterface -> chain"
    "chain -> validation -> txdb -> pow -> chain"
    "chain -> validation -> deploymentstatus -> versionbits -> chain"
    "confidential_validation -> pegins -> validation -> confidential_validation"
    "consensus/tx_verify -> pegins -> validation -> consensus/tx_verify"
    "dynafed -> validation -> primitives/pak -> dynafed"
    "pegins -> validation -> txmempool -> pegins"
    "block_proof -> chain -> validation -> block_proof"
    "block_proof -> chain -> validation -> txdb -> block_proof"
    "chain -> node/context -> net_processing -> node/blockstorage -> chain"
    "consensus/tx_verify -> pegins -> validation -> txmempool -> consensus/tx_verify"
    "block_proof -> chain -> node/context -> net_processing -> node/blockstorage -> block_proof"
    "core_io -> script/sign -> pegins -> validation -> signet -> core_io"
    # ELEMENTS: will be fixed by blinding cleanup
    "blindpsbt -> psbt -> blindpsbt"
    # ELEMENTS: not so easy to fix, caused by us doing asset ID lookups in the
    # wallet, from coin selection, to decide whether we are looking at a
    # multi-asset transaction or not. Probably this check should be done in
    # CreateTransaction instead.
    "wallet/coinselection -> wallet/wallet -> wallet/coinselection"
)

EXIT_CODE=0

CIRCULAR_DEPENDENCIES=()

IFS=$'\n'
for CIRC in $(cd src && ../contrib/devtools/circular-dependencies.py {*,*/*,*/*/*}.{h,cpp} | sed -e 's/^Circular dependency: //'); do
    CIRCULAR_DEPENDENCIES+=( "$CIRC" )
    IS_EXPECTED_CIRC=0
    for EXPECTED_CIRC in "${EXPECTED_CIRCULAR_DEPENDENCIES[@]}"; do
        if [[ "${CIRC}" == "${EXPECTED_CIRC}" ]]; then
            IS_EXPECTED_CIRC=1
            break
        fi
    done
    if [[ ${IS_EXPECTED_CIRC} == 0 ]]; then
        echo "A new circular dependency in the form of \"${CIRC}\" appears to have been introduced."
        echo
        EXIT_CODE=1
    fi
done

for EXPECTED_CIRC in "${EXPECTED_CIRCULAR_DEPENDENCIES[@]}"; do
    IS_PRESENT_EXPECTED_CIRC=0
    for CIRC in "${CIRCULAR_DEPENDENCIES[@]}"; do
        if [[ "${CIRC}" == "${EXPECTED_CIRC}" ]]; then
            IS_PRESENT_EXPECTED_CIRC=1
            break
        fi
    done
    if [[ ${IS_PRESENT_EXPECTED_CIRC} == 0 ]]; then
        echo "Good job! The circular dependency \"${EXPECTED_CIRC}\" is no longer present."
        echo "Please remove it from EXPECTED_CIRCULAR_DEPENDENCIES in $0"
        echo "to make sure this circular dependency is not accidentally reintroduced."
        echo
        EXIT_CODE=1
    fi
done

exit ${EXIT_CODE}
