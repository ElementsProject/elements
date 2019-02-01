#!/bin/bash
set -e

if [[ "$1" = "oceand" ]]; then
    exec gosu bitcoin "$@"
elif [[ "$1" == "ocean-cli" ]]; then
    exec gosu bitcoin "$@"
elif [[ "$1" == "ocean-tx" ]]; then
    exec gosu bitcoin "$@"
else
    exec "$@"
fi
