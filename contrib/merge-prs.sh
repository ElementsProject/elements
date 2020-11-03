#!/bin/sh

echo 'Please copy this script to /tmp, remove this warning, and run it from the root of your Elements repo as `/tmp/merge-prs.sh go`.'
exit 1

set -eo pipefail

BASE=merged-master

if [[ "$1" == "" ]]; then
    echo "Usage: $0 <go|continue|list-only|step>"
    echo "    go will try to merge every PR, building/testing each"
    echo "    continue assumes the first git-merge has already happened"
    echo "    list-only will simply list all the PRs yet to be done"
    echo "    step will try to merge/build/test a single PR"
    exit 1
fi

if [[ "$1" != "list-only" ]]; then
    if [[ -f ".git/MERGE_MSG" ]]; then
        echo "It looks like you're in the middle of a merge. Finish fixing"
        echo "things then run 'git commit' before running this program."
        exit 1
    fi
fi

if [[ "$1" == "continue" ]]; then
    BASE="$BASE^1"
    ECHO_CONTINUE=1
    DO_BUILD=1
elif [[ "$1" == "go" ]]; then
    ECHO_CONTINUE=0
    DO_BUILD=1
else
    ECHO_CONTINUE=0
    DO_BUILD=0
fi

## Get full list of merges
ELT_COMMITS=$(git log master --not $BASE --merges --first-parent --pretty='format:%ct %cI %h Elements %s')
BTC_COMMITS=$(git log bitcoin/master --not $BASE --merges --first-parent --pretty='format:%ct %cI %h Bitcoin %s')

## Sort by unix timestamp and iterate over them
echo "$ELT_COMMITS" "$BTC_COMMITS" | sort -n -k1 | while read line
do
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
        echo -e "Continuing build of \e[37m$PR_ID\e[0m at $(date -Is)"
    else
        echo -e "Start merge/build of \e[37m$PR_ID\e[0m at $(date -Is)"
        git merge $HASH -m "Merge $HASH into merged_master ($CHAIN PR $PR_ID)"
    fi

    if [[ "$DO_BUILD" == "1" ]]; then
        # Skip autogen/configure/clean because it'd take way too long
        #./autogen.sh
        #./configure --with-incompatible-bdb
        chronic git checkout -- src/secp256k1/src/
        # The following is an expansion of `make check` that skips the libsecp
        # tests and also the benchmarks (though it does build them!)
        chronic make -j8
        chronic make -j8 -C src/ check-TESTS
        chronic ./test/util/bitcoin-util-test.py
        chronic ./test/util/rpcauth-test.py
        chronic make -C src/univalue/ check
        chronic ./test/functional/test_runner.py --jobs=8
    fi

    if [[ "$1" == "step" ]]; then
        exit 1
    fi

    ECHO_CONTINUE=0
done


