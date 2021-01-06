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
MERGED_MASTER = "apoelstra/merged-master"
MERGED_MASTER_REVIEWED = "merged-master-reviewed"

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
    check_returncode: if True (defualt), throw an exception if the return code is nonzero."""

    handle_stderr = subprocess.PIPE if suppress_stderr else None

    # If check is True, a CalledProcessError will be raised on nonzero exit code.
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

    BTC_COMMITS_CMD=f"git log {BITCOIN_MASTER} --not {MERGED_MASTER_REVIEWED} --merges --first-parent --reverse --pretty='format:%ct %cI %H Bitcoin %s'"

    bitcoin_commits_raw = shell(BTC_COMMITS_CMD)
    bitcoin_commits = []
    for line in bitcoin_commits_raw:
        m = re.match(r"\d+ ([^ ]+) ([0-9a-f]+) Bitcoin Merge ((?:bitcoin-core/gui)?)#(\d+): (.*)", line)
        if m is None:
            raise Exception("Merge commit message in Bitcoin Core history had unexpected format")
        [date, cid, guirepo, prno, msg] = m.groups()
        fromgui = None
        if guirepo == "":
            fromgui = False
        elif guirepo == "bitcoin-core/gui":
            fromgui = True
        else:
            raise Exception("Merge into Bitcoin Core from unexpected repo, or commit message had unexpected format")

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

    ELT_COMMITS_CMD=f"git log {ELEMENTS_MASTER} --not {MERGED_MASTER_REVIEWED} --merges --first-parent --reverse --pretty='format:%ct %cI %H Elements %s'"

    elements_commits_raw = shell(ELT_COMMITS_CMD)
    elements_commits = []
    for line in elements_commits_raw:
        m = re.fullmatch(r"\d+ ([^ ]+) ([0-9a-f]+) Elements Merge (?:pull request )?#(\d+):? (.*)", line)
        if m is None:
            raise Exception("Merge commit message in Elements history had unexpected format")
        [date, cid, prno, msg] = m.groups()
        elements_commits.append({
            "date": date,
            "cid": cid,
            "prno": prno,
            "msg": msg
        })
    return elements_commits

def get_merged_commits():
    """Get the list of merge commits still needing to be reviewed."""

    MERGED_COMMITS_CMD=f"git log {MERGED_MASTER} --not {MERGED_MASTER_REVIEWED} --first-parent --reverse --pretty='format:%ct %cI %H Merged %s'"

    merged_commits_raw = shell(MERGED_COMMITS_CMD)
    merged_commits = []
    for line in merged_commits_raw:
        #print(line)
        m = re.fullmatch(r"\d+ ([^ ]+) ([0-9a-f]+) Merged Merge ([0-9a-f]+) into merged_master \((.+) PR ((?:bitcoin-core/gui)?)#(\d+)\)(.*)", line)
        m_secp = re.fullmatch(r"\d+ ([^ ]+) ([0-9a-f]+) Merged update libsecp256k1-zkp to ([0-9a-f]+)", line)

        fromgui = False
        fromsecp = False
        if m is not None:
            [date, cid, merged_cid, chain, guirepo, prno, trailing] = m.groups()
            if guirepo == "bitcoin-core/gui":
                fromgui = True
            elif guirepo != "":
                raise Exception("Merge into Bitcoin Core from unexpected repo, or commit message had unexpected format")
        elif m_secp is not None:
            [date, cid, merged_cid] = m_secp.groups()
            fromsecp = True
            chain = ""
            prno = ""
            trailing = ""
        else:
            raise Exception(f"Commit {cid} did not match any of the expected templates. Please hand-review.")

        merged_commits.append({
            "date": date,
            "cid": cid,
            "merged_cid": merged_cid,
            "chain": chain,
            "prno": prno,
            "trailing": trailing,
            "fromgui": fromgui,
            "fromsecp": fromsecp
        })
    return merged_commits

def check_commit(commit, last_reviewed, incoming_commit) -> None:
    """Verify some invariants about a commit, and fill in the full parent commid IDs."""

    cid = commit["cid"]
    parents = shell(f"git cat-file -p {cid} | grep '^parent'")
    if len(parents) != 2:
        raise Exception(f"Expected merge, but commit {cid} has {parents} parents, which is not two! Please hand-review.")

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
        raise Exception("Merge isn't merging the next expected Bitcoin/Elements commit.")

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

    WORKTREE_LOCATION = "/tmp/elements-merge-review-worktree"
    check_or_create_worktree(WORKTREE_LOCATION)
    WQ = shlex.quote(WORKTREE_LOCATION)

    print("Fetching all remotes...")
    os.system(f"git -C {WQ} fetch --all")

    print()
    print(f"For our already-reviewed base branch, using `{MERGED_MASTER_REVIEWED}`. Starting from there:")

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

    cstyle = shell_oneline("git config --get merge.conflictstyle")
    if cstyle != "diff3":
        print("You may want to run git 'config --global merge.conflictstyle diff3' to get more useful diffs when running this script (and in general.)")

    if prompt_chars("Ready to start?", "yn") != "y":
        sys.exit(1)
    print()

    SKIP_CLEAN = False

    for commit in merged_commits:
        # Figure out what incoming/upstream commit this is merging, from which side.
        incoming_commit: Dict[str, Any] = {}
        if commit["chain"] == "Bitcoin":
            incoming_commit = bitcoin_commits.pop(0)
        elif commit["chain"] == "Elements":
            incoming_commit = elements_commits.pop(0)
        else:
            raise Exception("This is neither a Bitcoin nor an Elements merge; I don't know what to do with it.")

        check_commit(commit, last_reviewed, incoming_commit)

        print("Next commit:", commit["cid"])

        cid = commit["cid"]

        # stderr is going to yell at us about throwing away our temp commit, so ignore it
        shell(f"git -C {WQ} checkout {last_reviewed}", suppress_stderr=True)

        # We expect this to complain if the merge is not clean, but that's okay, so we ignore it.
        shell(f"git -C {WQ} merge --no-rerere-autoupdate --no-ff --no-commit {incoming_commit['cid']}", suppress_stderr=True, check_returncode=False)

        shell(f"git -C {WQ} add -u")
        shell(f"git -C {WQ} commit -m 'TEMP REVIEW COMMIT'")

        diff = shell(f"git -C {WQ} diff --color=always --histogram HEAD {cid}")
        diffstr = "\n".join(diff)
        if len(diffstr) == 0 and SKIP_CLEAN:
            last_reviewed = cid
            continue

        said = ""
        while said != "y":
            print()
            print("** COMMIT WE ARE REVIEWING:")
            os.system(f"git -C {WQ} log -1 --pretty=full {cid}")
            print()
            print("** UPSTREAM COMMIT MERGED THEREIN:")
            os.system(f"git -C {WQ} log -1 --pretty=full {incoming_commit['cid']}")
            print()

            if len(diffstr) > 0:
                print("** AND HERE'S THE DIFF:")
                print()
                print(diffstr)
            else:
                print("** No diff, merge was clean!")

            print()
            said = prompt_chars("Accept this commit? (If unsure, say 'N', which will exit the review script.) Or [r]edisplay commit, or [a]utoskip clean diffs?", "ynra")

            if said == "a":
                SKIP_CLEAN = not SKIP_CLEAN
                print("Autoskip clean diffs: " + ("on" if SKIP_CLEAN else "off"))
                continue
            elif said == "r":
                continue
            elif said == "n":
                print(f"The current commit (in `{WORKTREE_LOCATION}`) is the conflicted diff as git produced it. The command we used to diff it against the actual merge was:")
                print(f"git -C {WQ} diff --color=always --histogram --exit-code HEAD {cid}")
                print("Look over the commits however you like, or contact someone for assistance. If you are satisfied that the diff is okay, run the review script again.")
                sys.exit(1)

        if prompt_chars("Locally mark all commits up to and including this commit as reviewed, so we skip them in the future?", "yn") == "y":
            shell(f"git -C {WQ} branch -f {MERGED_MASTER_REVIEWED} {cid}")
            print(f"Done. (Updated local branch `{MERGED_MASTER_REVIEWED}` in `{WORKTREE_LOCATION}`. ** You will need to push this branch to gitlab if you want to persist this. **)")

        print()

        last_reviewed = cid

if __name__ == "__main__":
    main()
