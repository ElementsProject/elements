#!/usr/bin/env bash
# Copyright (c) 2018 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.

#
# Issue blocks using a local node at a given interval.
#

if [ $# -lt 3 ]; then
    echo "syntax: $0 <min_time> <max_time> <bitcoin-cli path> [<bitcoin-cli args>]" ; exit 1
fi

function log()
{
    echo "- $(date +%H:%M:%S): $*"
}

min_time=$1
shift
max_time=$1
shift
bcli=$1
shift

# https://stackoverflow.com/questions/806906/how-do-i-test-if-a-variable-is-a-number-in-bash
re='^[0-9]+$'
if ! [[ $min_time =~ $re ]] ; then
   echo "error: min_time $min_time is not a number" ; exit 1
fi
if ! [[ $max_time =~ $re ]] ; then
   echo "error: max_time $max_time is not a number" ; exit 1
fi

let randinterval=max_time-min_time
if [ $randinterval -lt 1 ]; then
    echo "error: interval min..max must be positive and greater than 0" ; exit 1
fi

if ! [ -e "$bcli" ]; then
    which "$bcli" &> /dev/null
    if [ $? -ne 0 ]; then
        echo "error: unable to find bitcoin binary: $bcli" ; exit 1
    fi
fi

echo "- checking node status"
conns=$($bcli "$@" getconnectioncount)

if [ $? -ne 0 ]; then
    echo "node error" ; exit 1
fi

if [ $conns -lt 1 ]; then
    echo "warning: node is not connected to any other node"
fi

log "node OK with $conns connection(s)"
log "mining in random intervals between $min_time .. $max_time seconds"
log "hit ^C to stop"

while [ 1 ]; do
    let rv=$RANDOM%$randinterval
    echo -n -e "- $(date +%H:%M:%S): next block in $rv seconds..."
    sleep $rv
    echo -n -e " [submit]"
    blockhash=$($bcli "$@" getnewblockhex true)
    if [ $? -ne 0 ]; then
        echo "node error; aborting" ; exit 1
    fi
    echo ""
    log "broadcasting block $($bcli "$@" getblockcount) $blockhash to $($bcli "$@" getconnectioncount) peer(s)"
done
