#!/bin/bash
set -e

if [ -f /run/secrets/ocean_user ] && [ -f /run/secrets/ocean_pass ]; then
    creds=("--rpcuser=$(cat /run/secrets/ocean_user)" "--rpcpassword=$(cat /run/secrets/ocean_pass)")
elif [ -f /run/secrets/ocean_pass ]; then
    creds=("--rpcpassword=$(cat /run/secrets/ocean_pass)")
fi

if [[ "$1" = "oceand" ]]; then
    exec gosu bitcoin "$@" "${creds[@]}"
elif [[ "$1" == "ocean-cli" ]]; then
    exec gosu bitcoin "$@" "${creds[@]}"
elif [[ "$1" == "ocean-tx" ]]; then
    exec gosu bitcoin "$@" "${creds[@]}"
else
    exec "$@"
fi
