## VERIFYING AN EDIT WHEN YOUR BASE BRANCH IS RED UPSTREAM — elaborate the ONE file against the RELEASE olean farm
(Same run. `merger` at `9e7f6e4b` had `X0.lean` RED — release 27 was mid-repair — and
`X1.lean` `public import`s it, so `lake build Fermat.FLT.ModularCurve.X1` cannot even
start. The target declaration exists ONLY on `merger`, so dropping back to `main` was not
an option either.)
The scratch-module section above already gives the symlink-farm trick for the case where
`lake build` has deleted your target's olean. It works just as well for a base that is
broken, and the setup is the same three commands:
    cp -rs ~/.flt-release-lake/build/lib /tmp/relean-N/                  # 0.3 s, no disk
      ~/.elan/toolchains/leanprover--lean4---v4.32.0-rc1/bin/lean Fermat/FLT/.../X1.lean
Four things make the result trustworthy rather than merely green-looking, and all four
must be checked:
1. **The farm is a COMPLETE, CONSISTENT olean set** — it is the last release's, built in
   one go — so none of the inconsistent-olean pathologies apply. That is the whole reason
   to use it rather than your own half-rebuilt `.lake`.
2. **Confirm the release really is `main` for Lean purposes.**
   `git diff --stat $(cat ~/.flt-release-lake/sha) main -- <your file> <its imports>`
   empty means the farm's oleans match those sources exactly.
3. **The residual errors are IDENTIFIABLE.** Here exactly three survived, and every one
   named a declaration `merger` had ADDED to `X0.lean` since the release
   (`algebraSmooth_of_smoothOfRelativeDimension`, …). An error of that shape is your
   base's staleness, not your edit; an error inside your own line range is yours. Say
   which in the commit message.
4. **Diff the `declaration uses 'sorry'` set against your own expectation.** Mine went
   `24 -> 25` with the target's warning GONE and two new ones at the leaves I cut — which
   is the cut, exactly, and is a stronger statement than "it compiled".
Bare `lean` must be the TOOLCHAIN's binary. The one on `PATH` is elan's default and dies
instantly with `failed to read file '…/Init.olean', incompatible header` — which reads
like a corrupt farm and is a wrong-binary error.
### `tools/merge/frontier.py` SCANNED `/home/chend/flt-staging`, NOT YOUR WORKTREE
Found by the check in point 4 and fixed in this commit. `ROOT` was hardcoded to the merge
worker's staging worktree, so **run from any other worktree it silently reported that
tree's counts and that tree's line numbers, under repo-relative paths** — indistinguishable
from a scan of your own. It reported X1 unchanged at `24` across an edit the compiler said
took it to `25`, and the line numbers it printed were of declarations at their PRE-edit
positions, which reads as "the scan disagrees with the compiler" rather than as "the scan
is looking somewhere else".
`ROOT` now defaults to the repository the script lives in, with `--root DIR` to override;
re-run in this worktree it matches the compiler's warning set for `X1.lean` exactly,
`25 = 25`. This is the third script in this repo to carry a hardcoded absolute root (see
the memory note `flt-hidden-sorries-scans-main-repo`), so **before quoting any frontier
number, `grep -n 'ROOT' <the script>`** — it is one command and the failure is silent.
