#!/bin/bash
set -e

if [[ "$1" = "elementsd" ]]; then
    exec gosu bitcoin "$@"
elif [[ "$1" == "elements-cli" ]]; then
    exec gosu bitcoin "$@"
elif [[ "$1" == "elements-tx" ]]; then
    exec gosu bitcoin "$@"
else
    exec "$@"
fi
