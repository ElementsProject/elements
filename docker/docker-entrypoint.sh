#!/bin/bash
set -e

if [[ "$1" = "elementsd" ]]; then
    exec gosu bitcoin elementsd "${*:2}"
elif [[ "$1" == "elements-cli" ]]; then
    exec gosu bitcoin elements-cli "${*:2}"
elif [[ "$1" == "elements-tx" ]]; then
    exec gosu bitcoin elements-tx "${*:2}"
else
    exec "$@"
fi