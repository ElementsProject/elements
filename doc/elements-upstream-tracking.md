NOTE: I'm not currently sure whether the proposed new process (see below) would actually be a good idea, but here it is for consideration.


### Current process for elements tracking upstream bitcoin changes:

* At various points (ideally after each major Bitcoin release, optionally after minor releases), someone performs a merge from the Bitcoin release, or some nearby commit on the Bitcoin release branch, into the Elements `master` branch.
  * This usually seems to go through a third, temporary branch, onto which fixes can be applied to make sure that the result builds and passes tests, before merging it back into Elements `master`.
  * This requires quite a lot of work from whoever is performing the merge, and it's generally all done at once, in a single big-bang merge commit.
  * As a result of this process, the Elements master branch not only gets commits from Bitcoin master, it also gets commits from Bitcoin release branches, including version numbering changes, various release-related cleanup, and rebased copies of some future commits from Bitcoin master. Some of these things are desirable; some are annoying.
  * A modified version of this process is possible, in which the 'merge manager' still does all the merging at once, but brings the Bitcoin side over one pull request at a time, rather than all at once, resolving merge conflicts as they go. This might give an easier time.


### Proposed new process for elements tracking upstream bitcoin changes:

* Upstream Bitcoin branches/tags (outside our control):
  * `master` (main development)
  * `0.XX` -- release branches (one for each major version)
  * [tags] `v0.XX.Y` -- one for each release
* Our branches:
  * `master` (main elements development)
  * (proposed) `merged-master` (contains a merged combination of all commits from _both_ elements `master` _and_ bitcoin `master`)
  * `0.XX` / `0.XX.Y` -- release branches
    * Each of these is based on `master`. We do not directly pull in any commits from the upstream release branches; for each cherry-pick into the upstream release branches, we cherry-pick from our `merged-master` branch instead. For administrivia (bumping version numbers, updating changelogs, etc.), we do this ourselves, to reduce merge conflicts.

* Some automated process merges each merged upstream pull request, and each merged Elements merge request, into the `merged-master` branch.
  * If the automated process fails, an issue is created, and someone has to do the merge manually, and fix the conflicts. (This is the same work someone would have to do in the current process, but without batching it all up to the very end like we do now.)

* When Bitcoin Core branches off for a major release, creating a new `0.XX` release branch, we take the last commit _before_ the upstream release branch -- which has already been merged into our `merged-master` branch -- and merge that into our local `master` elements development branch.
  * This means we will always be developing based on the latest major release from Core.
    * (If anything is too broken at this point on the upstream `master` branch to even be able to develop, we may have to cherry-pick fixes from the upstream release branch.)
  * We _wait_ until Core finalizes the `0.XX.0` release, then we prepare a corresponding `0.XX` Elements release.
    * We create our own parallel release branch, and make the same cherry-picks that Core does on their release branch, but we do it from our `merged-master` branch (where any merge conflicts between Core's work and ours have already been resolved.) For any administrative changes, such as version bumps and changelog edits, we do those ourselves on our own release branch.

* When we want to make a minor release, we will repeat the release process, branching from the Elements development `master` branch.
  * We will need to cherry-pick any changes from the Core release branch again, since they are not in our dev branch.
  * If Core has made any minor releases, it will be a matter of judgement to decide what exactly we cherry-pick for our minor release; most likely we will want to take everything from the Core release branch, corresponding to the latest Core minor release.

### Proposed additional changes to the Elements development process

* The biggest issue for this whole process, whether we do it the old way or the new way, seems to be around refactoring on the Bitcoin side. Movement of code is very confusing to `git diff` and `git merge`. (I strongly recommend using the `patience` mode, which can help somewhat.)
  * A way of reducing the impact of this dramatically, is to move as much of our code as possible to separate files. E.g. instead of putting Elements wallet RPCs into `rpcwallet.cpp`, put them into `rpcwallet-elements.cpp` or similar.
  * In cases where git's textual diffs get confused by code movement, this should prevent spurious conflicts completely.
  * In cases where upstream changes things like function signatures, this will turn a merge conflict into a compile error, which is probably easier to fix.
  * We already do some of this by separating our code within files, but git's diff algorithm is still somewhat lousy at dealing with changes _near_ other changes, or wholesale moves of files where code also changes.
  * We will still need changes in upstream files, but we should try to keep them as small as practical.

* Another annoying issue is the rename from `bitcoin` to `elements`, which conflicts with any refactoring in the build system files, for example. If possible, we may consider trying to automate this process, so that we can avoid having to merge a rename commit, and instead regenerate it by running a script against the new Bitcoin release.
