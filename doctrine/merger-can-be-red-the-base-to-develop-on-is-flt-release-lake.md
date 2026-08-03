## `merger` CAN BE RED — the base to develop on is `~/.flt-release-lake/sha`, not `merger` and not `main`
(2026-07-31, flt-lean-354, cost ~80 minutes.) A prover was told its target's neighbourhood
had gained new machinery "landed 2026-07-31". That machinery was not on `main` — it was on
`merger`, 1587 commits ahead. Fast-forwarding to `merger` looked right (the work lands there
anyway, and the merge is then trivial) and produced a tree whose `X0.lean` **does not
compile**: 100+ errors, `maxErrors` reached, no `.olean` at the end of a 68-minute build.
`merger` mid-release is a WORKING COPY, not a publishable state — release 27's own handover
commit says so in its subject line — and CLAUDE.md's seventh class explains exactly why a
release build fails several rounds before it goes green.
`main` is not the answer either. At that moment `main` was **701 commits BEHIND** the commit
whose artifacts sit in `~/.flt-release-lake/build`. So the release-lake oleans do not match
`main`, and `lake build` on `main` would have rebuilt from whatever was on disk.
**The green base is `$(cat ~/.flt-release-lake/sha)`, by construction**: `flt-cycle.py release`
stamps it only after the merger reports green, and it is the commit those artifacts were built
at. Three facts follow, and they are worth more than any of the three branch names:
    git reset --hard $(cat ~/.flt-release-lake/sha)
    rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/<worktree>/.lake/build/
    lake build <YourModule>      # a REPLAY: ~9 minutes, not ~70
- it is an ancestor of `merger`, so a branch based on it merges as an ordinary branch;
- its artifacts are on hand, so the first build is a replay and the scratch-module loop works
  immediately (50 s per iteration against a 81 530-line `X0.lean`);
- **it is a consistent olean set**, which neither of the other two bases gives you.
**And when the machinery you need exists only on `merger`, COPY IT UNDER A DIFFERENT NAME.**
Citing it is impossible; taking `merger` wholesale is what this section is about. But copying
it verbatim under the SAME name is a trap of its own: the declaration-level merge keys on the
name, sees it already present in `ours`, and keeps *merger's* copy — **at merger's position**.
Here that position was ~1000 lines BELOW the leaf being proven, so the merged file would have
had a forward reference and gone red, and every merge check would have passed. An `_aux`
suffix makes the merge green whichever way it resolves, at the price of one redundant
declaration; say in its docstring which copy should survive, and put the deletion in
`to_merger`. (This is the already-recorded "a helper you need may exist only DOWNSTREAM, and
then you copy it, deliberately" rule, in its merge-ordering form.)
