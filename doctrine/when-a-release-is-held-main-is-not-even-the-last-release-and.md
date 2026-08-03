## WHEN A RELEASE IS HELD, `main` IS NOT EVEN THE LAST RELEASE — AND YOUR TARGET MAY EXIST ONLY ON `merger`
(2026-07-31, `flt-lean-344`.) Every rule in this file about the release window is written
for the case where the target is OPEN on `main` and already PROVEN on `merger`. There is a
mirror case, and it is worse, because the target does not exist on `main` **at all**:
* the task named `finite_maximalSpectrum_of_isLocalRing_of_module_finite` at "the top of
  `Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/ShortExact.lean`";
* `grep -rn` over the whole worktree returned **nothing**, and so did
  `git show main:<that file> | grep -c <name>` — **zero on `main`, four on `merger`**;
* the worktree was `1587` commits behind `merger`, and `merger` was `868` commits ahead of
  `main` because **release 27 had been HELD** (`main`'s own tip commit says so:
  *"a merge worker may HOLD its release, and that is not a panic"*).
So `main` was release 26 plus four tooling commits, and **`main` was not even an ancestor of
`merger`**. Every "fast-forward to `main` first" instruction in this file would have put the
worktree further from the task, not closer.
**The diagnostic, and it is three cheap commands rather than the usual one:**
    git rev-list --count HEAD..main;  git merge-base --is-ancestor HEAD main   && echo anc-main
    git rev-list --count HEAD..merger; git merge-base --is-ancestor main merger && echo main-anc-merger
    git show merger:<the file> | grep -c '<the declaration your task names>'
If `main` is NOT an ancestor of `merger`, a release is being held and `main` is stale by a
whole release. **Then the correct base is `merger`** — `git merge --ff-only merger`, which is
a genuine fast-forward whenever your worktree sits on an earlier `merger` commit, so it costs
nothing and risks nothing. Your branch is then `merger` plus your own commit, which is the
cheapest possible thing for the next merge worker to take.
Two riders:
* **"The declaration does not exist anywhere in the tree" is a BASE symptom before it is a
  rename symptom**, and this is the third distinct cause recorded in this file for it
  (stale worktree; declined merge; and now *held release*). Run the three commands before
  writing a single word about a phantom target.
* **Do not conclude "main is broken" or set `to_medic`.** A held release is a documented,
  intended state of the loop; the file `tools/merge/RELEASE-27-HANDOVER.md` on `merger`
  explains exactly why this one was held. `to_medic` is for a loop that cannot operate, and
  this loop was operating correctly.
**Corollary for `.lake`.** `~/.flt-release-lake/build` is built at the last PUBLISHED release,
so under a held release it is a whole release stale and the usual "rsync it and the build is a
replay" shortcut does not apply. Check what it is worth before spending a minute on it:
    git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- 'Fermat/**'   # non-empty => it is stale
Here the worktree's own `.lake` was newer than the snapshot (it had been seeded at the held
release), and the target module rebuilt in 29 s from it while the snapshot would have forced a
rebuild of the whole changed cone.
