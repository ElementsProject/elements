#!/usr/bin/env bash
export LC_ALL=C

# Fixes permission issues when there is a container UID/GID mismatch with the owner
# of the mounted bitcoin src dir.
git config --global --add safe.directory /bitcoin

if [ -z "$1" ]; then
  LOCAL_BRANCH=1 bash -ic "./ci/lint/06_script.sh"
else
  exec "$@"
fi
