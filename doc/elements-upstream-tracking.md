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
  * (proposed) `merged-0.XX` (contains a merged combination of all commits from both elements `master` and bitcoin's `0.XX` release branch)
    * We should only bother with this for the latest bitcoin major release, and retire the older release branches. If there are bugfix releases for those older versions, better for us to just say that we don't support them, and people should upgrade, to reduce the overhead of this process.

* Some automated process constantly (for each new commit) merges each bitcoin branch into the corresponding `merged-` branch, and constantly (for each new commit) merges elements `master` into _every_ `merged-` branch.
  * This will generally happen at the granularity of pull-requests / merge-requests, because the branches on each side are made up almost exclusively of merge commits.
  * If the automated process fails, an issue is created, and someone has to do the merge manually, and fix the conflicts. (This is the same work someone would have to do in the current process, but without batching it all up to the very end like we do now.)
  * (There was a proposal to only test the merge from the bitcoin side, and then throw it away if it's clean; and only keep it if it's nontrivial and requires human intervention. But while that reduces the total number of merges, it also means that Elements-side changes are not getting tested against the current bitcoin master immediately.)

* When Bitcoin Core branches off for a major release, creating a new `0.XX` release branch, we branch off `merged-0.XX` to follow it.
  * We _wait_ until Core finalizes the `0.XX.0` release, then we prepare a corresponding `0.XX` Elements release based on the `merged-0.XX` branch.
  * (This next part is the trickiest part of the whole thing, and I'm not totally clear on how it should work.)
  * We then take the _last_ commit _before_ Bitcoin 0.XX.0 branched off of Bitcoin master, and merge _that_ into the Elements master branch for further development.
    * We will need to apply human judgement on what to do with the additional commits on the 0.XX release branch. Historically when merging in a Bitcoin release, we've pulled those in as well, as described above. However, some of those commits will be cherry-picked/rebased from the master branch, which means we are going to end up getting them twice. (Git seems to handle that well, as long as it can see that the two changes are the same.)
    * This same issue will apply for each Bitcoin 0.XX.1, .2, etc. release. Those seem to also be made by cherry-picking / rebasing commits from the Bitcoin master branch, so the same issue exists.


### Proposed additional changes to the Elements development process

* The biggest issue for this whole process, whether we do it the old way or the new way, seems to be around refactoring on the Bitcoin side. Movement of code is very confusing to `git diff` and `git merge`. (I strongly recommend using the `patience` mode, which can help somewhat.)
  * A way of reducing the impact of this dramatically, is to move as much of our code as possible to separate files. E.g. instead of putting Elements wallet RPCs into `rpcwallet.cpp`, put them into `rpcwallet-elements.cpp` or similar.
  * In cases where git's textual diffs get confused by code movement, this should prevent spurious conflicts completely.
  * In cases where upstream changes things like function signatures, this will turn a merge conflict into a compile error, which is probably easier to fix.
  * We already do some of this by separating our code within files, but git's diff algorithm is still somewhat lousy at dealing with changes _near_ other changes, or wholesale moves of files where code also changes.
  * We will still need changes in upstream files, but we should try to keep them as small as practical.

* Another annoying issue is the rename from `bitcoin` to `elements`, which conflicts with any refactoring in the build system files, for example. If possible, we may consider trying to automate this process, so that we can avoid having to merge a rename commit, and instead regenerate it by running a script against the new Bitcoin release.
