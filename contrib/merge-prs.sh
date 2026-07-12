#!/usr/bin/env bash

export LC_ALL=C
set -eo pipefail

# Setup base branch and Bitcoin/Elements remote names.
BASE_ORIG=merged-master
BASE="${BASE_ORIG}"
BITCOIN_UPSTREAM_REMOTE=bitcoin
export BITCOIN_UPSTREAM="${BITCOIN_UPSTREAM_REMOTE}/master"
ELEMENTS_UPSTREAM_REMOTE=upstream
export ELEMENTS_UPSTREAM="${ELEMENTS_UPSTREAM_REMOTE}/master"

# START USER CONFIG:
# Set your target upstream here
TARGET_UPSTREAM=$BITCOIN_UPSTREAM
TARGET_NAME="Bitcoin"
PR_PREFIX="bitcoin/bitcoin"
# TARGET_UPSTREAM=$ELEMENTS_UPSTREAM
# TARGET_NAME="Elements"
# PR_PREFIX="ElementsProject/elements"

# Set your git worktree location here. This is where the merges will be done, and where you should checkout the merged-master branch.
WORKTREE="/home/byron/code/elements-worktree"

# Set your parallelism during build/test. You probably want as many cores as possible.
# Parallel functional tests can somewhat exceed your core count, depends on the build machine CPU/RAM.
PARALLEL_BUILD=23  # passed to make -j
PARALLEL_TEST=46  # passed to test_runner.py --jobs
PARALLEL_FUZZ=12  # passed to test_runner.py -j when fuzzing

# Setup a ccache dir if necessary.
#export CCACHE_DIR="/tmp/ccache"
#export CCACHE_MAXSIZE="20G"

# Set and export a WEBHOOK environment variable to a Discord webhook URL outside of this script to get notifications of progress and failures.

# We don't currently fuzz during merging. Check fuzzing and CI after a merge run.
# Replace this with the location where we should put the fuzz test corpus
# BITCOIN_QA_ASSETS="${HOME}/code/bitcoin/qa-assets"
# FUZZ_CORPUS="${BITCOIN_QA_ASSETS}/fuzz_seed_corpus/"

# END USER CONFIG

# Script
SKIP_MERGE=0
DO_BUILD=1
KEEP_GOING=1
DO_TEST=1
DO_FUZZ=0
NUM=15
COUNT=0

if [[ "$1" == "setup" ]]; then
    echo "Setting up..."
    echo
    git config remote.upstream.url >/dev/null || git remote add upstream "https://github.com/ElementsProject/elements.git"
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
    echo "Done! Remember to also checkout merged-master at ${WORKTREE}"
    exit 0
elif [[ "$1" == "continue" ]]; then
    SKIP_MERGE=1
elif [[ "$1" == "go" ]]; then
    true  # this is the default, do nothing
elif [[ "$1" == "list-only" ]]; then
    DO_BUILD=0
elif [[ "$1" == "step" ]]; then
    KEEP_GOING=0
elif [[ "$1" == "merge-only" ]]; then
    SKIP_MERGE=0
    KEEP_GOING=0
    DO_BUILD=0
    DO_TEST=0
elif [[ "$1" == "step-continue" ]]; then
    SKIP_MERGE=1
    KEEP_GOING=0
elif [[ "$1" == "step-test" ]]; then
    SKIP_MERGE=1
    KEEP_GOING=0
    DO_BUILD=0
elif [[ "$1" == "step-fuzz" ]]; then
    SKIP_MERGE=1
    KEEP_GOING=0
    DO_BUILD=0
    DO_TEST=0
elif [[ "$1" == "analyze" ]]; then
    DO_BUILD=0
    DO_TEST=0
else
    echo "Usage: $0 <setup|list-only|go|continue|step|step-continue|analyze>"
    echo "    setup will configure your repository for the first run of this script"
    echo "    list-only will simply list all the PRs yet to be done"
    echo "    go will try to merge every PR, building/testing each"
    echo "    continue assumes the first git-merge has already happened, and starts with building"
    echo "    step will try to merge/build/test a single PR"
    echo "    step-continue assumes the first git-merge has already happened, and will try to build/test a single PR"
    echo "    analyze will analyze the next $NUM PRs and count conflicts NB: DO NOT CTRL+C THIS PROCESS"
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
COMMITS=$(git -C "$WORKTREE" log "$TARGET_UPSTREAM" --not $BASE --merges --first-parent --pretty="format:%ct %cI %h $TARGET_NAME %s")

cd "$WORKTREE" || exit 1

VERBOSE=1

echo start > merge.log

quietly () {
    if [[ "$VERBOSE" == "1" ]]; then
    date | tee --append merge.log
        time "$@" 2>&1 | tee --append merge.log
    else
        chronic "$@"
    fi
}

notify () {
    local MESSAGE="$1"
    local JSON="{\"content\": \"$MESSAGE\"}"
    if [ -n "$WEBHOOK" ]; then
        curl -d "$JSON" -H "Content-Type: application/json" "$WEBHOOK"
    else
        echo "$MESSAGE"
    fi
    if [[ "$2" == "1" ]]; then
        exit 1
    fi
}

## Sort by unix timestamp and iterate over them
echo "$COMMITS" | tac | while read -r line
do
    ## Extract data and output what we're doing
    HASH=$(echo "$line" | cut -d ' ' -f 3)
    CHAIN=$(echo "$line" | cut -d ' ' -f 4)
    PR_ID=$(echo "$line" | grep -o -P "#\d+")

    GIT_HEAD=$(git rev-parse HEAD)

    ## Do it
    if [[ "$1" == "list-only" ]]; then
        echo -e "$line"
        continue
    fi
    if [[ "$1" == "analyze" ]]; then
        COUNT=$((COUNT + 1))
        # todo: count conflicts in critical files
        # CRITICAL_FILES=("src/wallet/spend.h", "src/wallet/spend.cpp")
        MERGE_FILE="/tmp/$HASH.merge"
        DIFF_FILE="/tmp/$HASH.diff"
        git -C "$WORKTREE" merge "$HASH" --no-ff -m "Merge $HASH into merged_master ($CHAIN PR $PR_PREFIX$PR_ID)" > "$MERGE_FILE" || true
        git -C "$WORKTREE" diff > "$DIFF_FILE"
        git -C "$WORKTREE" reset --hard "$GIT_HEAD" > /dev/null
        # FILES=$(grep "CONFLICT" "$MERGE_FILE")
        NUM_FILES=$(grep -c "CONFLICT" "$MERGE_FILE")
        NUM_CONFLICTS=$(grep -c "<<<<<<<" "$DIFF_FILE")
        echo "$COUNT. Merge up to $PR_ID ($HASH) has $NUM_CONFLICTS conflicts in $NUM_FILES files."
        if [[ "$COUNT" == "$NUM" ]]; then
            exit 0
        else
            continue
        fi
    fi
    notify "starting merge of $PR_ID"

    # check for stoppers and halt if found
    # a stopper is normally the PR after the version has been changed
    # ie. the branch point we want to stop at for this version
    STOPPERS=(
        "#30716" # bitcoin v28
        "#32041" # bitcoin v29
    )
    for STOPPER in "${STOPPERS[@]}"
    do
    if [[ "$PR_ID" == *"$STOPPER"* ]]; then
        echo "Found $STOPPER in $PR_ID! Exiting."
        notify "hit stopper, exiting"
        exit 1
    else
        echo "Didn't find $STOPPER in $PR_ID. Continuing."
    fi
    done

    if [[ "$SKIP_MERGE" == "1" ]]; then
        echo -e "Continuing build of \e[37m$PR_ID\e[0m at $(date)"
    else
        echo -e "Start merge/build of \e[37m$PR_ID\e[0m at $(date)"
        git -C "$WORKTREE" merge "$HASH" --no-ff -m "Merge $HASH into merged_master ($CHAIN PR $PR_PREFIX$PR_ID)" || notify "fail merge" 1
    fi

    # FIXME: ELEMENTS, move make building process into CMake one?
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
        quietly make -j"$PARALLEL_BUILD" -k || notify "fail build" 1
        # todo: fix linting step
        # echo "Linting"
        # quietly ./ci/lint/06_script.sh || notify "fail lint"
    fi

    if [[ "$DO_TEST" == "1" ]]; then
        echo "Testing"
        quietly ./src/qt/test/test_elements-qt || notify "fail test qt" 1
        quietly ./src/test/test_bitcoin || notify "fail test bitcoin" 1
        quietly ./src/bench/bench_bitcoin || notify "fail test bench" 1
        quietly ./test/util/test_runner.py || notify "fail test util" 1
        quietly ./test/util/rpcauth-test.py || notify "fail test rpc" 1
        echo "Functional testing"
        quietly ./test/functional/test_runner.py --jobs="$PARALLEL_TEST" || notify "fail test runner" 1
    fi

    if [[ "$DO_FUZZ" == "1" ]]; then
        echo "Cleaning for fuzz"
        quietly make distclean || true
        quietly git -C "$WORKTREE" clean -xf
        echo "Building for fuzz"
        quietly ./autogen.sh
        # TODO turn on `,integer` after this rebase
        quietly ./configure --enable-fuzz --with-sanitizers=address,fuzzer,undefined CC="ccache clang" CXX="ccache clang++"
        quietly make -j"$PARALLEL_BUILD" -k
        echo "Fuzzing"
        quietly ./test/fuzz/test_runner.py -j"$PARALLEL_FUZZ" "${FUZZ_CORPUS}" || notify "fail fuzz" 1
    fi

    if [[ "$KEEP_GOING" == "0" ]]; then
        notify "$PR_ID done, exiting"
        exit 0
    else
        echo "$PR_ID done, continuing"
    fi

    SKIP_MERGE=0
    echo "end" >> merge.log
done
