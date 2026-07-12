# github-merge.py

Please use this python script from the [Bitcoin maintainer tools](https://github.com/bitcoin-core/bitcoin-maintainer-tools/) repo for merging PRs.

- Clone the repo and copy or just download the [github-merge.py](https://github.com/bitcoin-core/bitcoin-maintainer-tools/blob/main/github-merge.py) script into a directory on your $PATH.

```
wget https://raw.githubusercontent.com/bitcoin-core/bitcoin-maintainer-tools/refs/heads/main/github-merge.py -O ~/.local/bin/github-merge.py
chmod +x ~/.local/bin/github-merge.py
```

- In your Elements repo, configure the merge repository.

```
git config githubmerge.repository ElementsProject/elements
```

- Run the script with the PR number you want to test/merge.

```
github-merge.py <PR_NUMBER>
```

For example for PR 1518 I see this output:

```
ElementsProject/elements#1518 Avoid Simplicity header dependency propagation into master
* 6c7788adf373cd8f0dc5c4fe2b7674625631721e Avoid Simplicity header dependency propagation (Russell O'Connor) (upstream/simplicity, pull/1518/head)

Dropping you on a shell so you can try building/testing the merged source.
Run 'git diff HEAD~' to show the changes being merged.
Type 'exit' when done.
```

- Now you can build and test the PR branch, or do whatever review/testing you require.

- Once you are done testing, comment on the PR with your `ACK BRANCH_COMMIT` and/or comments.

Note: this merge script requires one or more ACKs on the top commit of the PR.

- Type `exit` to continue after testing.

```
exit
```

In our example this results in the following output:

```
[pull/1518/local-merge 5e1a950e52] Merge ElementsProject/elements#1518: Avoid Simplicity header dependency propagation
 Date: Thu Jan 22 14:49:26 2026 +0200
ElementsProject/elements#1518 Avoid Simplicity header dependency propagation into master
* 6c7788adf373cd8f0dc5c4fe2b7674625631721e Avoid Simplicity header dependency propagation (Russell O'Connor) (upstream/simplicity, pull/1518/head)
ACKs:
* ACK 6c7788a; built and tested locally  (delta1)
* ACK 6c7788adf373cd8f0dc5c4fe2b7674625631721e; successfully ran local tests (apoelstra)
Type 's' to sign off on the above merge, or 'x' to reject and exit.
```

- If all looks good then type `s` and hit enter to sign off on the merge. Otherwise type `x` and hit enter to exit.

Signing off in our example shows this output:

```
Type 'push' to push the result to git@github.com:ElementsProject/elements, branch master, or 'x' to exit without pushing.
```

- Type `push` and hit enter to finish the merge.
