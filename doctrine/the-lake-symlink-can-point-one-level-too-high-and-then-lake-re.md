## THE `.lake` SYMLINK CAN POINT ONE LEVEL TOO HIGH, AND THEN LAKE RE-CLONES MATHLIB
(2026-07-31, `flt-lean-273`.) The batch-2/3 layout is `$HOME/flt-lean-N/.lake ->
/scratch/chend-flt/flt-lean-N/.lake` — note the **trailing `.lake`**. This worktree was
dispatched with the symlink recreated as `-> /scratch/chend-flt/flt-lean-273`, i.e. the
PARENT, whose only children are `.lake/` and `.report-server/`. Lake then found no
`packages/` where it expected one and did the only thing it can: **cloned mathlib, aesop,
batteries, ProofWidgets and the rest from GitHub and started building 5264 targets from
source.** It also created `packages/`, `config/` and `build/` as siblings of the real
`.lake`, so a second run would have compounded it.
Cost if not caught: hours of a worker's life spent rebuilding a mathlib that was already on
disk, 6.4 G of it, twenty metres away.
**The tell is in the FIRST LINES of the build log, not in the errors:**
    info: mathlib: cloning https://github.com/leanprover-community/mathlib4
    ✔ [664/5264] Built Mathlib.Algebra.Ring.Defs (4.2s)
A real build never clones and never has five thousand targets — a repointed worktree replays
from cache and rebuilds tens. **So look at `head` of the log, not `tail`.** `tail` shows
plausible-looking green `Built` lines for hours.
Check before the first build, and fix it in place — it is local state, not tracked, so no
commit carries the repair:
    ls -ld ~/flt-lean-N/.lake        # MUST end in /.lake
    ls ~/flt-lean-N/.lake/packages   # MUST list mathlib
Repair: `rm .lake && ln -s /scratch/chend-flt/flt-lean-N/.lake .lake`, then
`rsync -a --delete ~/.flt-release-lake/build/ .lake/build/` — note the release snapshot is
the PROJECT build only (`.lake/build`), never the mathlib package builds, which live in
`.lake/packages/mathlib/.lake/build` and are what the bad symlink hid. Then delete the junk
the runaway created (`build`, `packages`, `config` directly under
`/scratch/chend-flt/flt-lean-N/`); they are minutes old, and the real tree is the dotted one.
Corollary worth generalising: **an environment fault here looks exactly like slow work.** A
worker rebuilding mathlib and a worker elaborating a 15 k-line file both show `lean` processes
burning CPU and produce nothing for a long time. The staleness sweeps cannot tell them apart;
the build log's first line can.
