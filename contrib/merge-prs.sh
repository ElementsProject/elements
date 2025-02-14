#!/usr/bin/env bash

export LC_ALL=C
set -eo pipefail

BASE_ORIG=merged-master
BASE="${BASE_ORIG}"
BITCOIN_UPSTREAM_REMOTE=bitcoin
BITCOIN_UPSTREAM="${BITCOIN_UPSTREAM_REMOTE}/master"
# ELEMENTS_UPSTREAM_REMOTE=upstream
# ELEMENTS_UPSTREAM="${ELEMENTS_UPSTREAM_REMOTE}/master"

# Replace this with the location where we should put the fuzz test corpus
BITCOIN_QA_ASSETS="${HOME}/.tmp/bitcoin/qa-assets"
FUZZ_CORPUS="${BITCOIN_QA_ASSETS}/fuzz_seed_corpus/"
mkdir -p "$(dirname "${BITCOIN_QA_ASSETS}")"

# BEWARE: On some systems /tmp/ gets periodically cleaned, which may cause
#   random files from this directory to disappear based on timestamp, and
#   make git very confused
WORKTREE="${HOME}/.tmp/elements-merge-worktree"
mkdir -p "${HOME}/.tmp"

# These should be tuned to your machine; below values are for an 8-core
#   16-thread macbook pro
PARALLEL_BUILD=4  # passed to make -j
PARALLEL_TEST=12  # passed to test_runner.py --jobs
PARALLEL_FUZZ=8  # passed to test_runner.py -j when fuzzing

SKIP_MERGE=0
DO_BUILD=1
KEEP_GOING=1

if [[ "$1" == "setup" ]]; then
    echo "Setting up..."
    echo
    git config remote.upstream.url >/dev/null || remote add upstream "https://github.com/ElementsProject/elements.git"
    git config remote.bitcoin.url >/dev/null || git remote add bitcoin "https://github.com/bitcoin/bitcoin.git"
    if git worktree list --porcelain | grep --silent prunable; then
        echo "You have stale git worktrees, please either fix them or run 'git worktree prune'."
        exit 1
    fi
    git worktree list --porcelain | grep --silent "${WORKTREE}" || git worktree add "${WORKTREE}" --force --no-checkout --detach
    echo
    echo "Fetching all remotes..."
    echo
    git fetch --all
    echo
    #echo "Cloning fuzz test corpus..."
    #echo
    #if [[ ! -d "${BITCOIN_QA_ASSETS}" ]]; then
    #    cd "$(dirname ${BITCOIN_QA_ASSETS})" && git clone https://github.com/bitcoin-core/qa-assets.git
    #fi
    #echo
    echo "Done! Remember to also check out merged-master, and push it back up when finished."
    exit 0
elif [[ "$1" == "continue" ]]; then
    SKIP_MERGE=1
elif [[ "$1" == "go" ]]; then
    true  # this is the default, do nothing
elif [[ "$1" == "list-only" ]]; then
    DO_BUILD=0
elif [[ "$1" == "step" ]]; then
    KEEP_GOING=0
elif [[ "$1" == "step-continue" ]]; then
    SKIP_MERGE=1
    KEEP_GOING=0
else
    echo "Usage: $0 <setup|list-only|go|continue|step|step-continue>"
    echo "    setup will configure your repository for the first run of this script"
    echo "    list-only will simply list all the PRs yet to be done"
    echo "    go will try to merge every PR, building/testing each"
    echo "    continue assumes the first git-merge has already happened, and starts with building"
    echo "    step will try to merge/build/test a single PR"
    echo "    step-continue assumes the first git-merge has already happened, and will try to build/test a single PR"
    echo
    echo "Prior to use, please create a git worktree for the elements repo at:"
    echo "    $WORKTREE"
    echo "Make sure it has an elements remote named '$ELEMENTS_UPSTREAM_REMOTE' and a bitcoin remote named '$BITCOIN_UPSTREAM_REMOTE'."
    echo "Make sure that your local branch '$BASE_ORIG' contains the integration"
    echo "branch you want to start from, and remember to push it up somewhere"
    echo "when you're done!"
    echo
    echo "You can also edit PARALLEL_{BUILD,TEST,FUZZ} in the script to tune for your machine."
    echo "And you can edit VERBOSE in the script to watch the build process."
    echo "(By default only the output of failing steps will be shown.)"
    exit 1
fi

if [[ "$1" != "list-only" ]]; then
    if [[ -f "$WORKTREE/.git/MERGE_MSG" ]]; then
        echo "It looks like you're in the middle of a merge. Finish fixing"
        echo "things then run 'git commit' before running this program."
        exit 1
    fi
fi

if [[ "$SKIP_MERGE" == "1" ]]; then
    # Rewind so the first loop iteration is the last one that we already merged.
    BASE="$BASE^1"
fi

## Get full list of merges
# for elements
# COMMITS=$(git -C "$WORKTREE" log "$ELEMENTS_UPSTREAM" --not $BASE --merges --first-parent --pretty='format:%ct %cI %h Elements %s')
# for bitcoin
COMMITS=$(git -C "$WORKTREE" log "$BITCOIN_UPSTREAM" --not $BASE --merges --first-parent --pretty='format:%ct %cI %h Bitcoin %s')

cd "$WORKTREE"

VERBOSE=1

quietly () {
    if [[ "$VERBOSE" == "1" ]]; then
        "$@"
    else
        chronic "$@"
    fi
}

## Sort by unix timestamp and iterate over them
#echo "$ELT_COMMITS" "$BTC_COMMITS" | sort -n -k1 | while read line
echo "$COMMITS" | tac | while read -r line
do
    echo
    echo "=-=-=-=-=-=-=-=-=-=-="
    echo

    echo -e "$line"
    ## Extract data and output what we're doing
    DATE=$(echo "$line" | cut -d ' ' -f 2)
    HASH=$(echo "$line" | cut -d ' ' -f 3)
    CHAIN=$(echo "$line" | cut -d ' ' -f 4)
    PR_ID=$(echo "$line" | cut -d ' ' -f 6 | tr -d :)
    PR_ID_ALT=$(echo "$line" | cut -d ' ' -f 8 | tr -d :)

    if [[ "$PR_ID" == "pull" ]]; then
	PR_ID="${PR_ID_ALT}"
    fi
    echo -e "$CHAIN PR \e[37m$PR_ID \e[33m$HASH\e[0m on \e[32m$DATE\e[0m "

    ## Do it
    if [[ "$1" == "list-only" ]]; then
        continue
    fi

    if [[ "$SKIP_MERGE" == "1" ]]; then
        echo -e "Continuing build of \e[37m$PR_ID\e[0m at $(date)"
    else
        echo -e "Start merge/build of \e[37m$PR_ID\e[0m at $(date)"
        git -C "$WORKTREE" merge "$HASH" --no-ff -m "Merge $HASH into merged_master ($CHAIN PR $PR_ID)"
    fi

    if [[ "$DO_BUILD" == "1" ]]; then
        # Clean up
        echo "Cleaning up"
        # NB: this will fail the first time because there's not yet a makefile
        quietly make distclean || true
        quietly git -C "$WORKTREE" clean -xf
        echo "autogen & configure"
        quietly ./autogen.sh
        quietly ./configure --with-incompatible-bdb
        # The following is an expansion of `make check` that skips the libsecp
        # tests and also the benchmarks (though it does build them!)
        echo "Building"
        quietly make -j"$PARALLEL_BUILD" -k
#        quietly make -j1 check
        echo "Linting"
        quietly ./ci/lint/06_script.sh
        echo "Testing"
        quietly ./src/qt/test/test_elements-qt
        quietly ./src/test/test_bitcoin
        quietly ./src/bench/bench_bitcoin
        quietly ./test/util/bitcoin-util-test.py
        quietly ./test/util/rpcauth-test.py
        quietly make -C src/univalue/ check
        echo "Functional testing"
        quietly ./test/functional/test_runner.py --jobs="$PARALLEL_TEST"
        echo "Cleaning for fuzz"
        quietly make distclean || true
        quietly git -C "$WORKTREE" clean -xf
        echo "Building for fuzz"
        quietly ./autogen.sh
        # TODO turn on `,integer` after this rebase
        quietly ./configure --with-incompatible-bdb --enable-fuzz --with-sanitizers=address,fuzzer,undefined CC=clang CXX=clang++
        quietly make -j"$PARALLEL_BUILD" -k
        echo "Fuzzing"
        quietly ./test/fuzz/test_runner.py -j"$PARALLEL_FUZZ" "${FUZZ_CORPUS}"
    fi

    if [[ "$KEEP_GOING" == "0" ]]; then
        exit 1
    fi

#    bummer1.sh
    SKIP_MERGE=0
done
