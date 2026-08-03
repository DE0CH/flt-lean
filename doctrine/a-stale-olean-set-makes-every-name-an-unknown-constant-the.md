## A STALE OLEAN SET MAKES EVERY NAME AN "UNKNOWN CONSTANT" — the phantom-target symptom with a third cause
(Same task.)  A fresh `#check @Fermat.Gamma0Datum.ker_of_geomFibrePt` in a scratch that
`public import`s the target's module came back **`Unknown constant`**, together with three
other names that are visibly in the source.  Every diagnosis this file offers for that
symptom — a stale worktree, a declined merge, a rename, a runaway comment — was wrong.
The SOURCES were current (`git rev-list --count HEAD..main` = 0 after one fast-forward);
the `.lake` was not, because the worktree had just been fast-forwarded **1518 commits** and
its oleans were from before the leaf was cut.
So add to the triage: **an `unknown constant` for a name whose declaration you can see in
the source of an IMPORTED module is a stale olean**, and the fix is the release-snapshot
rsync (`git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- Fermat/` empty ⟹
`rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/`,
15 seconds).  The tell that separates it from the source-level causes is that the name is
absent from the OLEAN while present in the FILE — one `grep -n` and one `#check`.
**And check for orphaned `lean` processes in your worktree before rsyncing.**  This one had
a `lean` elaborating `MazurTorsion.lean` with `ppid 1`, **42 hours** old, holding 11.7 GB,
and burning **0 CPU ticks in 10 seconds** — the documented dead-but-not-exited orphan,
which would have written a stale olean over the seeded one had it ever woken up.  The CPU
delta is the discriminator; `etimes` and RSS look identical for a healthy elaboration.
