# Updating Simplicity C code in Elements

This document describes how to update the Simplicity C code subtree in the Elements repository.

Reference: https://github.com/BlockstreamResearch/simplicity/issues/329#issuecomment-3715844042

## Simplicity

- Clone or pull the latest `master` branch of the [Simplicity](https://github.com/BlockstreamResearch/simplicity) repository.

- Split out a new subtree of the Simplicity `C` source to the `C-master` branch.

```
git subtree split -P C  -b C-master
```

- Push the `C-master` branch to a public remote.

```
git push <remote> C-master
```

## Elements

- Add a reference to the above simplicity remote in your Elements repo.

```
git remote add <new-remote-name> git@github.com:<user>/simplicity.git
```

- Pull and squash the `C-master` branch subtree into the `src/simplicity` directory in Elements.

```
git subtree pull --prefix src/simplicity <new-remote-name> C-master --squash
```

- Run build and tests.

- Create a new PR to Elements.
