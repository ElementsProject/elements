#!/usr/bin/env python3

"""
Script for reviewing semi-automated Elements merges.
"""

import subprocess
from subprocess import CalledProcessError
import sys
import re
import os
import shlex

from typing import List, Dict, Any

BITCOIN_MASTER = "bitcoin/master"
ELEMENTS_MASTER = "upstream/master"
MERGED_MASTER = "upstream/merged-master"
MERGED_MASTER_REVIEWED = "merged-master-reviewed"

# XXX: This is not actually a good idea. On many systems (incl. macOS) random
# files in the worktree will start to go missing a few days after its creation,
# because of temp-directory-cleaning scripts that work on a file-by-file basis.
WORKTREE_LOCATION = "/tmp/elements-merge-review-worktree"

def print_startup_warning() -> None:
    print()
    print("To prepare to use this script, make sure the following things are set up:")
    print(" - The remotes 'bitcoin' and 'upstream' should point to Bitcoin Core and")
    print("   Elements upstream repos, respectively.")
    print(f" - The latest {MERGED_MASTER_REVIEWED} branch should be checked out locally.")
    print(f" - We are currently using '{MERGED_MASTER}' as our branch to review.")
    print("   To change this, edit the constant MERGED_MASTER in the script.")
    print(" - We will reuse or create a git worktree at:")
    print(f"   {WORKTREE_LOCATION}")
    print("   If this fails, delete that directory, run 'git worktree prune', and retry.")

    print()
    result = prompt_chars("Continue?", "yn")
    if (result != "y"):
        sys.exit(1)

ECHO_COMMANDS = True
GIT_DIFF_OPTS = "--color=always --color-moved=dimmed-zebra --color-moved-ws=allow-indentation-change --ignore-space-change --histogram"

class CommandFailed(Exception):
    """Exception for failure of a shell command."""

def shell_oneline(cmd: str, **kwargs) -> str:
    """Run a shell command whose output is just a single line, and return the line."""
    result = shell(cmd, **kwargs)
    if len(result) != 1:
        raise CommandFailed(f"In shell_oneline, when running {cmd}, result was unexpectedly multiline: {result}")
    return result[0]

def shell(cmd: str, suppress_stderr=False, check_returncode=True) -> List[str]:
    """Run a shell command, capturing the lines of stdout.

    The command WILL be parsed in a shell-like fashion. Be careful with quoting when interpolating variables into it. Use shlex.quote() if necessary.

    suppress_stderr: if False (default), stderr will be sent to the terminal.
    check_returncode: if True (default), throw an exception if the return code is nonzero."""

    handle_stderr = subprocess.PIPE if suppress_stderr else None

    # If check is True, a CalledProcessError will be raised on nonzero exit code.
    if ECHO_COMMANDS:
        print(f" > {cmd}")
    result = subprocess.run(["sh", "-c", cmd], stdout=subprocess.PIPE, stderr=handle_stderr, check=check_returncode)
    return result.stdout.decode("utf-8").rstrip().split("\n")

def prompt_chars(prompt: str, chars: str) -> str:
    """Prompt the user with a multiple-choice question."""
    said = ""
    while said not in list(chars):
        said = input(f"{prompt} [{chars}]> ").lower()
    return said

def get_bitcoin_commits():
    """Get the list of upstream bitcoin commits which should be included in merges not yet reviewed."""

    BTC_COMMITS_CMD=f"git log '{BITCOIN_MASTER}' --not '{MERGED_MASTER_REVIEWED}' --merges --first-parent --reverse --pretty='format:%ct %cI %H Bitcoin %s'"

    bitcoin_commits_raw = shell(BTC_COMMITS_CMD)
    bitcoin_commits = []
    for line in bitcoin_commits_raw:
        m = re.match(r"\d+ ([^ ]+) ([0-9a-f]+) Bitcoin Merge ((?:[-_a-zA-Z0-9]*/[-_a-zA-Z0-9]*)?)#(\d+): (.*)", line)
        if m is None:
            raise Exception(f"Merge commit message in Bitcoin Core history had unexpected format:\n   > {line}")
        [date, cid, repo, prno, msg] = m.groups()
        fromgui = None
        if repo == "":
            fromgui = False
        elif repo == "bitcoin/bitcoin":
            fromgui = False
        elif repo == "bitcoin-core/gui":
            fromgui = True
        else:
            raise Exception(f"Merge into Bitcoin Core from unexpected repo, or commit message had unexpected format: \n   > {line}")

        bitcoin_commits.append({
            "date": date,
            "cid": cid,
            "fromgui": fromgui,
            "prno": prno,
            "msg": msg
        })
    return bitcoin_commits

def get_elements_commits():
    """Get the list of elements commits which should be included in merges not yet reviewed."""

    ELT_COMMITS_CMD=f"git log '{ELEMENTS_MASTER}' --not '{MERGED_MASTER_REVIEWED}' --merges --first-parent --reverse --pretty='format:%ct %cI %H Elements %s'"

    elements_commits_raw = shell(ELT_COMMITS_CMD)
    elements_commits = []
    for line in elements_commits_raw:
        m = re.fullmatch(r"\d+ ([^ ]+) ([0-9a-f]+) Elements Merge (?:pull request )?((?:[-_a-zA-Z0-9]*/[-_a-zA-Z0-9]*)?)#(\d+):? (.*)", line)
        if m is None:
            raise Exception(f"Merge commit message in Elements history had unexpected format: \n   > {line}")
        [date, cid, repo, prno, msg] = m.groups()
        if repo != "" and repo != "ElementsProject/elements":
            raise Exception(f"Merge into Elements from unexpected repo, or commit message had unexpected format: \n   > {line}")
        elements_commits.append({
            "date": date,
            "cid": cid,
            "prno": prno,
            "msg": msg
        })
    return elements_commits

def get_merged_commits():
    """Get the list of merge commits still needing to be reviewed."""

    MERGED_COMMITS_CMD=f"git log '{MERGED_MASTER}' --not '{MERGED_MASTER_REVIEWED}' --first-parent --reverse --pretty='format:%ct %cI %H Merged %s'"

    merged_commits_raw = shell(MERGED_COMMITS_CMD)
    merged_commits = []
    for line in merged_commits_raw:
        #print(line)
        m = re.fullmatch(r"\d+ ([^ ]+) ([0-9a-f]+) Merged Merge ([0-9a-f]+) into merged_master \((.+) PR (?:pull )?((?:[-_a-zA-Z0-9]*/[-_a-zA-Z0-9]*)?)#(\d+)\)(.*)", line)
        m_secp = re.fullmatch(r"\d+ ([^ ]+) ([0-9a-f]+) Merged update libsecp256k1-zkp to ([0-9a-f]+)", line)
        m_misc = re.fullmatch(r"\d+ ([^ ]+) ([0-9a-f]+) Merged (.*)$", line)

        fromgui = False
        fromsecp = False

        if m is not None:
            [date, cid, merged_cid, chain, repo, prno, trailing] = m.groups()
            if chain == "Bitcoin":
                if repo == "bitcoin-core/gui":
                    fromgui = True
                elif repo != "" and repo != "bitcoin/bitcoin":
                    raise Exception(f"Merge into Bitcoin Core from unexpected repo, or commit message had unexpected format:\n   > {line}")
            elif chain == "Elements":
                if repo != "" and repo != "ElementsProject/elements":
                    raise Exception(f"Merge into Elements from unexpected repo, or commit message had unexpected format:\n   > {line}")
            else:
                raise Exception(f"Commit message had unexpected format:\n   > {line}")
        elif m_secp is not None:
            [date, cid, merged_cid] = m_secp.groups()
            fromsecp = True
            chain = ""
            prno = ""
            trailing = ""
        elif m_misc is not None:
            [date, cid, trailing] = m_misc.groups()
            merged_commits.append({
                "date": date,
                "cid": cid,
                "trailing": trailing,
                "handreview": True,
            })
            continue
        else:
            raise Exception(f"Commit {cid} did not match any of the expected templates. Not sure what to do.\n   > {line}")

        merged_commits.append({
            "date": date,
            "cid": cid,
            "merged_cid": merged_cid,
            "chain": chain,
            "prno": prno,
            "trailing": trailing,
            "fromgui": fromgui,
            "fromsecp": fromsecp,
        })
    return merged_commits

def check_commit(commit, last_reviewed, incoming_commit) -> None:
    """Verify some invariants about a commit, and fill in the full parent commid IDs."""

    cid = commit["cid"]
    parents = shell(f"git cat-file -p {cid} | grep '^parent'")
    if len(parents) != 2:
        print(f"WARNING: Expected merge, but commit {cid} has {parents} parents, which is not two! Please hand-review.")
        return

    parent_cids = []
    for p in parents:
        m = re.fullmatch("parent ([0-9a-f]+)", p)
        assert m is not None
        parent_cids.append(m.group(1))

    full_merged_cid = shell_oneline(f"git rev-parse {commit['merged_cid']}")
    if parent_cids[1] != full_merged_cid:
        raise Exception("Merge isn't merging what the commit message claims to be merging")

    if parent_cids[0] != last_reviewed:
        raise Exception("First parent of next commit to review should be last commit reviewed.")

    if full_merged_cid != incoming_commit["cid"]:
        print("WARNING: Merge isn't merging the next expected Bitcoin/Elements commit.")
        print("This could mean something was skipped, or it could just mean that some extra fixup commits were added.")
        print("If the diff looks really wrong, stop here -- some manual review will be required.")

    commit["parent_cid"] = parent_cids[0]
    commit["merged_cid"] = full_merged_cid

def check_or_create_worktree(path) -> None:
    """Verify that a git worktree (or repo) exists at `path`. Offer to create it if missing. Exit if something is wrong."""

    try:
        shell_oneline(f"git -C {shlex.quote(path)} rev-parse --show-toplevel", suppress_stderr=True)
    except CalledProcessError:
        said = prompt_chars(f"No git worktree or repository found at '{path}'. Ok to create a worktree there?", "yn")
        if said != "y":
            sys.exit(1)

        # Can't create a worktree without something to check out -- this is an arbitrary choice (apparently the first commit in the bitcoin repo.)
        shell(f"git worktree add {shlex.quote(path)} 4405b78d6059e536c36974088a8ed4d9f0f29898")

def main() -> None:
    """Interactively review commits."""

    print_startup_warning()

    check_or_create_worktree(WORKTREE_LOCATION)
    WQ = shlex.quote(WORKTREE_LOCATION)

    print("Fetching all remotes...")
    os.system(f"git -C {WQ} fetch --all")

    print()
    print(f"For our already-reviewed base branch, using `{MERGED_MASTER_REVIEWED}`. If this fails, create / check out that branch locally from upstream's copy. Starting from there:")

    bitcoin_commits = get_bitcoin_commits()
    print(f"Found a total of {len(bitcoin_commits)} Bitcoin Core commits to review (on `{BITCOIN_MASTER}`).")

    elements_commits = get_elements_commits()
    print(f"Found a total of {len(elements_commits)} Elements commits to review (on `{ELEMENTS_MASTER}`).")

    merged_commits = get_merged_commits()
    print(f"Found a total of {len(merged_commits)} commits to review on merged-master (`{MERGED_MASTER}`).")

    last_reviewed = shell_oneline(f"git rev-parse {MERGED_MASTER_REVIEWED}")

    unclean = shell(f"git -C {WQ} status --porcelain --untracked-files=no")
    if len("".join(unclean)) != 0:
        print("You have uncommitted changes in your working directory! Refusing to run!")
        sys.exit(1)

    untracked = shell(f"git -C {WQ} status --porcelain")
    if len("".join(untracked)) != 0:
        print("You have untracked files in your working directory! Please be careful; checkouts may overwrite them!")

    cstyle = shell_oneline("git config --get merge.conflictstyle", check_returncode=False)
    if cstyle != "diff3":
        print("You may want to run 'git config --global merge.conflictstyle diff3' to get more useful diffs when running this script (and in general.)")

    if prompt_chars("Ready to start?", "yn") != "y":
        sys.exit(1)
    print()

    SKIP_CLEAN = True

    for commit in merged_commits:
        REQUIRE_MANUAL_REVIEW = False
        # Figure out what incoming/upstream commit this is merging, from which side.
        incoming_commit: Dict[str, Any] = {}
        if commit.get("chain", None) == "Bitcoin":
            incoming_commit = bitcoin_commits.pop(0)
        elif commit.get("chain", None) == "Elements":
            incoming_commit = elements_commits.pop(0)
        elif commit.get("fromsecp", False):
            incoming_commit = {"cid": commit["merged_cid"]}
            print()
            print("WARNING: The next commit claims to merge a libsecp256k1 commit. We have no way to verify where it came from.")
            print()
            REQUIRE_MANUAL_REVIEW = True
        else:
            # TODO: A bunch of stuff doesn't really work right in this mode. Fix the UI so it makes sense.
            incoming_commit = None
            print(f"WARNING: This is neither a Bitcoin nor an Elements merge; I don't know what to do with it. Details: {commit}")
            REQUIRE_MANUAL_REVIEW = True

        check_commit(commit, last_reviewed, incoming_commit)

        print("Next commit:", commit["cid"])

        cid = commit["cid"]

        # stderr is going to yell at us about throwing away our temp commit, so ignore it
        shell(f"git -C {WQ} checkout {last_reviewed}", suppress_stderr=True)

        if incoming_commit is not None:
            # We expect this to complain if the merge is not clean, but that's okay, so we ignore it.
            shell(f"git -C {WQ} merge --no-rerere-autoupdate --no-ff --no-commit {incoming_commit['cid']}", suppress_stderr=True, check_returncode=False)

            shell(f"git -C {WQ} add -u")
            shell(f"git -C {WQ} commit -m 'TEMP REVIEW COMMIT'")

            diff = shell(f"git -C {WQ} diff --histogram HEAD {cid}")
            diffstr = "\n".join(diff)
        else:
            diffstr = "<Could not find incoming commit; no diff available>"

        if len(diffstr) == 0 and SKIP_CLEAN and (not REQUIRE_MANUAL_REVIEW):
            last_reviewed = cid
            continue

        # Force 'less' to always wait before exiting, so that short output doesn't get lost when followed by long output.
        os.environ["LESS"] = "RSX"

        print()
        print("** COMMIT WE ARE REVIEWING:")
        os.system(f"git -C {WQ} log -1 --pretty=full {cid}")
        print()

        def diff4():
            os.system(f"git -C {WQ} diff {GIT_DIFF_OPTS} HEAD {cid}")

        if incoming_commit is not None:
            print("** UPSTREAM COMMIT MERGED THEREIN:")
            os.system(f"git -C {WQ} log -1 --pretty=full {incoming_commit['cid']}")
            print()

            diff4()

        said = ""
        if incoming_commit is not None:
            while said != "y":
                said = prompt_chars("Accept this commit? (If unsure, say 'N', which will exit the review script.) Or show a [d]iff, [r]edisplay commit, or [a]utoskip clean diffs [toggle]?", "yndra")

                if said == "a":
                    SKIP_CLEAN = not SKIP_CLEAN
                    print("Autoskip clean diffs now: " + ("on" if SKIP_CLEAN else "off"))
                    said = "y"
                    continue
                elif said == "r":
                    print()
                    print("** COMMIT WE ARE REVIEWING:")
                    os.system(f"git -C {WQ} log -1 --pretty=full {cid}")
                    print()

                    if incoming_commit is not None:
                        print("** UPSTREAM COMMIT MERGED THEREIN:")
                        os.system(f"git -C {WQ} log -1 --pretty=full {incoming_commit['cid']}")
                        print()

                elif said == "d":
                    diff = prompt_chars("Type of diff to show: [4]way, [o]rig-commits, [m]erged-commits, merged-[f]lattened, or get [h]elp?", "4omfh")
                    if diff == "4":
                        diff4()
                    elif diff == "o":
                        os.system(f"git -C {WQ} show {GIT_DIFF_OPTS} {commit['merged_cid']}^1..{commit['merged_cid']}")
                    elif diff == "m":
                        os.system(f"git -C {WQ} show {GIT_DIFF_OPTS} {cid}^1..{cid}")
                    elif diff == "f":
                        os.system(f"git -C {WQ} diff {GIT_DIFF_OPTS} {cid}^1..{cid}")
                    elif diff == "h":
                        print("Diff modes supported:")
                        print(" - 4way: shows a very confusing diff between (1) the conflicted merge git would have made, left to its own devices, and (2) the resolved merge in the actual merged history.")
                        print(" - orig-commits: shows the commits from the original (upstream) PR, using `git show`.")
                        print(" - merged-commits: shows the commits of the PR as merged into the actual merged history, using `git show`. This will normally be the same commits as upstream, plus a merge commit resolving the merge conflicts, which is shown in a confusing format as described under `COMBINED DIFF FORMAT` in `man git-diff`.")
                        print(" - merged-flattened: shows a single flattened diff of the entire PR as applied in the actual merged history.")
                        # XXX: It would be nice to have a mode showing merged-flattened and orig-flattened (which I maybe could add) side-by-side.
                    print()

                elif said == "n":
                    break
        else:  # incoming_commit is None
            os.system(f"git -C {WQ} show {GIT_DIFF_OPTS} {cid}")
            while said != "y":
                said = prompt_chars("Accept this commit? (If unsure, say 'N', which will exit the review script.) Or [r]edisplay commit and diff?", "ynr")

                if said == "r":
                    print()
                    print("** COMMIT WE ARE REVIEWING:")
                    os.system(f"git -C {WQ} log -1 --pretty=full {cid}")
                    print()
                    os.system(f"git -C {WQ} show {GIT_DIFF_OPTS} {cid}")
                elif said == "n":
                    break

        if said == "n":
            print(f"The current commit (in `{WORKTREE_LOCATION}`) is the conflicted diff as git produced it. The command we used to diff it against the actual merge was:")
            print(f"git -C {WQ} diff {GIT_DIFF_OPTS} HEAD {cid}")
            print("Look over the commits however you like, or contact someone for assistance. If you are satisfied that the diff is okay, run the review script again.")
            sys.exit(1)

        shell(f"git -C {WQ} branch -f {MERGED_MASTER_REVIEWED} {cid}")
        print(f"Done. (Updated local branch `{MERGED_MASTER_REVIEWED}` in `{WORKTREE_LOCATION}`. ** You will need to push this branch to gitlab if you want to persist this. **)")
        print()

        last_reviewed = cid

if __name__ == "__main__":
    main()
