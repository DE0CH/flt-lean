## SEVENTH invisibility class: a leaf that exists ONLY on `merger`, because the release was HELD
(2026-07-31, `flt-lean-356`.) The release-window section above records that a leaf named as open
by every instrument may already be PROVEN on an unmerged branch. **The mirror case is worse and
nothing above covers it: a leaf that does not EXIST on `main` at all**, because the cut that
created it was made after the last release was HELD.
Release 31 was held — X0 was the sole red module, 39 errors — so `main` did not move. The queue
was still generated from `merger`'s frontier and still dispatched. A prover sent at
`exists_nonConstant_qExpansion_gamma0GITPresentation` "in `Fermat/FLT/ModularCurve/X0.lean`, ~line
14418" found **zero occurrences of the name** in its worktree, on `main`, or anywhere in the
release. `git log -S` located it on `merger` alone, in a commit two hours old. Every ownership and
frontier check in this file agrees the leaf is unowned, and they are all answering a question about
a declaration the worker cannot see.
**First command when a target is missing — before concluding it was proven, renamed, or never
existed:**
    git show merger:<the file> | grep -n <name>
Then decide, and the decision is NOT "rebase onto `merger`". At the moment this happened `merger`
was 1448 commits ahead of `main` and RED in the very file the task was about, so basing on it buys
a tree that cannot be built. `git cherry-pick` of the cut commit is no better: cuts land bundled
with unrelated relocations, and it conflicted on both files it touched.
**Redo the cut yourself, on `main`, copying `merger` verbatim.** The task prompt quotes the leaf's
statement; `git show merger:<file>` gives the surrounding declarations, their ORDER, and their
docstrings. Reproduce all of it — same names, same order, same text — and put your own work on top.
The cost is one localized conflict in one region, which `to_merger` can resolve in a sentence
("take mine; it is your text plus a proof"), against a rebase of the world.
Two things make this cheap that are not obvious:
- **A hoist is usually part of the cut.** Merger's cut moved
  `isRegularRing_coarseRing_of_gamma0GITPresentation` ~250 lines up so the new assembly could cite
  it. Reproduce the move to the same place; the alternative — duplicating 30 lines of proof inline
  — reads as a second declaration to every duplicate scan.
- **The merger's own commit message says which relocation it chose and why** ("85 lines of text
  against 300 for moving the two consumers down"). Read it rather than re-deriving the choice.

