#!/usr/bin/env bash

set -eo pipefail

BASE=merged-master
BITCOIN_UPSTREAM=bitcoin/master
ELEMENTS_UPSTREAM=upstream/master

# BEWARE: On some systems /tmp/ gets periodically cleaned, which may cause
#   random files from this directory to disappear based on timestamp, and
#   make git very confused
WORKTREE="/tmp/elements-merge-worktree"

# These should be tuned to your machine; below values are for an 8-core
#   16-thread macbook pro
PARALLEL_BUILD=16  # passed to make -j
PARALLEL_TEST=8  # passed to test_runner.py --jobs
PARALLEL_FUZZ=5  # passed to test_runner.py -j when fuzzing

if [[ "$1" == "continue" ]]; then
    BASE="$BASE^1"
    ECHO_CONTINUE=1
    DO_BUILD=1
elif [[ "$1" == "go" ]]; then
    ECHO_CONTINUE=0
    DO_BUILD=1
elif [[ "$1" == "list-only" ]]; then
    ECHO_CONTINUE=0
    DO_BUILD=0
elif [[ "$1" == "step" ]]; then
    BASE="$BASE^1"
    ECHO_CONTINUE=1
    DO_BUILD=1
else
    echo "Usage: $0 <go|continue|list-only|step>"
    echo "    go will try to merge every PR, building/testing each"
    echo "    continue assumes the first git-merge has already happened"
    echo "    list-only will simply list all the PRs yet to be done"
    echo "    step will try to merge/build/test a single PR"
    exit 1
fi

if [[ "$1" != "list-only" ]]; then
    if [[ -f "$WORKTREE/.git/MERGE_MSG" ]]; then
        echo "It looks like you're in the middle of a merge. Finish fixing"
        echo "things then run 'git commit' before running this program."
        exit 1
    fi
fi

## Get full list of merges
ELT_COMMITS=$(git -C "$WORKTREE" log "$ELEMENTS_UPSTREAM" --not $BASE --merges --first-parent --pretty='format:%ct %cI %h Elements %s')
BTC_COMMITS=$(git -C "$WORKTREE" log "$BITCOIN_UPSTREAM" --not $BASE --merges --first-parent --pretty='format:%ct %cI %h Bitcoin %s')

#ELT_COMMITS=
#BTC_COMMITS=$(git -C "$WORKTREE" log v0.21.0 --not $BASE --merges --first-parent --pretty='format:%ct %cI %h Bitcoin %s')

#play /home/apoelstra/games/Hover/sounds/mixed/hit_wall.wav 2>/dev/null ## play start sound

cd "$WORKTREE"

# temporarily disable chronic
alias chronic=""

## Sort by unix timestamp and iterate over them
#echo "$ELT_COMMITS" "$BTC_COMMITS" | sort -n -k1 | while read line
echo "$ELT_COMMITS" | tac | while read line
do
    echo
    echo "=-=-=-=-=-=-=-=-=-=-="
    echo

    ## Extract data and output what we're doing
    DATE=$(echo $line | cut -d ' ' -f 2)
    HASH=$(echo $line | cut -d ' ' -f 3)
    CHAIN=$(echo $line | cut -d ' ' -f 4)
    PR_ID=$(echo $line | cut -d ' ' -f 6 | tr -d :)
    echo -e "$CHAIN PR \e[37m$PR_ID \e[33m$HASH\e[0m on \e[32m$DATE\e[0m "

    ## Do it
    if [[ "$1" == "list-only" ]]; then
        continue
    fi

    if [[ "$ECHO_CONTINUE" == "1" ]]; then
        echo -e "Continuing build of \e[37m$PR_ID\e[0m at $(date)"
    else
        echo -e "Start merge/build of \e[37m$PR_ID\e[0m at $(date)"
        git -C "$WORKTREE" merge $HASH --no-ff -m "Merge $HASH into merged_master ($CHAIN PR $PR_ID)"
    fi

    if [[ "$DO_BUILD" == "1" ]]; then
        # Clean up
        echo "Cleaning up"
        # NB: this will fail the first time because there's not yet a makefile
        chronic make distclean || true
        chronic git -C "$WORKTREE" clean -xf
        echo "autogen & configure"
        chronic ./autogen.sh
        chronic ./configure --with-incompatible-bdb
        # The following is an expansion of `make check` that skips the libsecp
        # tests and also the benchmarks (though it does build them!)
        echo "Building"
        chronic make -j"$PARALLEL_BUILD" -k
#        chronic make -j1 check
        echo "Linting"
        chronic ./ci/lint/06_script.sh
        echo "Testing"
        chronic ./src/qt/test/test_elements-qt
        chronic ./src/test/test_bitcoin
        chronic ./src/bench/bench_bitcoin
        chronic ./test/util/bitcoin-util-test.py
        chronic ./test/util/rpcauth-test.py
        chronic make -C src/univalue/ check
        echo "Functional testing"
        chronic ./test/functional/test_runner.py --jobs="$PARALLEL_TEST"
        echo "Cleaning for fuzz"
        chronic make distclean || true
        chronic git -C "$WORKTREE" clean -xf
        echo "Building for fuzz"
        chronic ./autogen.sh
        # TODO turn on `,integer` after this rebase
        chronic ./configure --with-incompatible-bdb --enable-fuzz --with-sanitizers=address,fuzzer,undefined CC=clang CXX=clang++
        chronic make -j"$PARALLEL_BUILD" -k
        echo "Fuzzing"
        chronic ./test/fuzz/test_runner.py -j"$PARALLEL_FUZZ" ~/code/bitcoin/qa-assets/fuzz_seed_corpus/
    fi

    if [[ "$1" == "step" ]]; then
        exit 1
    fi

#    bummer1.sh
    ECHO_CONTINUE=0
done
