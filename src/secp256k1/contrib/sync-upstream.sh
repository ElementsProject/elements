#!/usr/bin/env bash

set -eou pipefail

help() {
cat <<EOT
$0: Prepare a pull request that syncs a branch with upstream

Usage:
  $0 [--switch] <base-branch> <upstream-ref>

This script creates a sync local branch pointing to <upstream-ref>. Moreover, it
generates a helper script for opening a pull request (PR) merging the created
local branch into <base-branch>.

The synced upstream PRs are listed in the title and the description of the PR.
(This relies on upstream merging PRs using merge commits with titles of the form
"Merge <repo>#<prnum>: ...".)

Arguments:
  --switch:        Try to switch to the created sync branch
  <base-branch>:   The branch to sync with upstream
  <upstream-ref>:  The upstream ref to merge into <base-branch>

Usage examples:
  $0 --switch master upstream/master
  $0 master abc1234

To find candidate merge commits from <upstream-ref> (oldest first), use:
  git log --oneline --topo-order --reverse --merges \$(git merge-base <upstream-ref> <base-branch>)..<upstream-ref>
EOT
}

### Parse arguments
SWITCH=false
if [ "$#" -ge 1 ] && [ "$1" = "--switch" ]; then
    SWITCH=true
    shift
fi
if [ "$#" -ne 2 ]; then
    help
    exit 1
fi
BASE_BRANCH="$1"
UPSTREAM_REF="$2"

### Create PR metadata
TITLE="Upstream PRs"
RANGESTART_COMMIT=$(git merge-base "$UPSTREAM_REF" "$BASE_BRANCH")
RANGEEND_COMMIT=$(git rev-parse "$UPSTREAM_REF")
COMMITS=$(git --no-pager log --pretty=format:%H --topo-order --reverse --merges "$RANGESTART_COMMIT".."$RANGEEND_COMMIT")
# If there are no commits, exit successfully
if [ -z "$COMMITS" ]; then
  echo "No merge commits in range ${RANGESTART_COMMIT}..${RANGEEND_COMMIT}" >&2
  exit 0
fi
BODY="${GITHUB_ACTIONS+*Note: This PR has been created by a GitHub Actions workflow without human involvement.*

}"
BODY+="This PR syncs the following upstream PRs:"
for COMMIT in $COMMITS; do
    PRNUM=$(git log -1 "$COMMIT" --pretty=format:%s | sed s/'Merge .*#\([0-9]*\):.*'/'\1'/)
    TITLE="$TITLE $PRNUM,"
    BODY=$(printf "%s\n * %s" "$BODY" "$(git log -1 "$COMMIT" --pretty=format:%s | sed s/'Merge '//)")
done
# Remove trailing ","
TITLE=${TITLE%?}
BODY+=$(cat <<'EOF'


Usage hints:
 * If this PR has merge conflicts, resolve these by switching to the PR branch and merging the base branch into it using `git merge <base-branch>`.
 * To show the conflict resolution diff from an existing merge commit, use `git show --remerge-diff <merge-commit>`.
 * In case you are recreating the PR branch locally, you can (during the conflict resolution state) replay this conflict resolution diff using `git read-tree --reset -u <merge-commit>`.
   Be aware that this may discard your index as well as the uncommitted changes and untracked files in your worktree.
EOF
)

### Create a sync branch locally.
SYNC_BRANCH="sync-$(git rev-parse --short "$UPSTREAM_REF")"
# This will error out if the branch already exists, which is what we want.
git branch --no-track "$SYNC_BRANCH" "$UPSTREAM_REF"

### Print the PR metadata
echo "-----------------------------------"
echo "$TITLE"
echo "-----------------------------------"
echo "$BODY"
echo "-----------------------------------"

### Generate the helper script for creating the PR
FNAME="gh-pr-create.sh"
# Escape single quote ' -> '\''
quote() {
    local quoted=${1//\'/\'\\\'\'}
    printf "%s" "$quoted"
}
TITLE=$(quote "$TITLE")
BODY=$(quote "$BODY")
cat <<EOT > "$FNAME"
#!/bin/sh
TITLE='$TITLE'
BODY='$BODY'
SYNC_BRANCH='$SYNC_BRANCH'
BASE_BRANCH='$BASE_BRANCH'

gh pr create --base "\$BASE_BRANCH" --head "\$SYNC_BRANCH" --title "\$TITLE" --body "\$BODY" "\$@"
EOT
chmod +x "$FNAME"

echo "Successfully created local sync branch $SYNC_BRANCH starting at $UPSTREAM_REF."
echo
echo "You can now:"
echo "  1. Optionally resolve merge conflicts by merging $BASE_BRANCH into $SYNC_BRANCH."
echo "  2. Push $SYNC_BRANCH to some GitHub remote."
echo "  3. Run ./$FNAME to create a pull request. (Tip: Pass --dry-run first.)"

if [ "${SWITCH:-false}" = true ]; then
    echo
    echo "Trying to switch to the sync branch..."
    echo
    git switch "$SYNC_BRANCH"
fi
