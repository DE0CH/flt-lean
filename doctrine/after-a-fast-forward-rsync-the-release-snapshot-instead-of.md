## After a fast-forward, RSYNC the release snapshot instead of rebuilding

(2026-07-31, `flt-lean-373`.) A worktree seeded at release *R* and then
fast-forwarded to a later `main` has an `.olean` set for *R*, so the first
`lake build` of anything rebuilds the whole changed cone — >10 minutes before it
even reaches your own module, and that is the state of EVERY worktree whose
targets were introduced after its seed (mine did not contain its three targets
at all until the ff).

`~/.flt-release-lake/build` is the current snapshot and `~/.flt-release-lake/sha`
names the commit it was built at. **The snapshot is valid for your tree exactly
when no commit between that sha and your HEAD touches `Fermat/`:**

    S=$(cat ~/.flt-release-lake/sha)
    git merge-base --is-ancestor $S HEAD && git log --oneline $S..HEAD -- Fermat/

Empty output → the oleans match your sources, so

    rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/

is a complete substitute for the rebuild (2.3G, under a minute). It replaces only
the PROJECT build; `.lake/packages/mathlib/.lake/build` is a separate directory
and is untouched. Kill your own `lake`/`lean` first (**by PID after checking
`/proc/<pid>/cwd`**, never by pattern) — rsyncing under a live build is exactly
the torn-snapshot state the release seeder's own guard exists to prevent.

If the `git log` is NON-empty the snapshot is stale for those modules and you
must build; the check is cheap and there is no partial-credit version of it.

### …AND THE EMPTY `git diff` IS NECESSARY BUT **NOT SUFFICIENT** — THE SNAPSHOT'S OLEAN FOR ONE MODULE CAN PREDATE ITS OWN SOURCE

(2026-08-02, `flt-lean-88`, measured against release 33's snapshot.) The rule above,
and the half-dozen shim recipes that build on it, all certify the snapshot the same
way: `git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- Fermat/` empty ⟹ "the
oleans match your sources". **That inference is false, and it fails silently in the
most expensive direction.**

Measured: `S = fe5131ca` (release 33, PUBLISHED), `HEAD = 280981f1`, `S` an ancestor,
`git diff --stat S HEAD -- Fermat/` **EMPTY**, `git log S..HEAD -- Fermat/` **EMPTY**
— i.e. every clause of the standing check passes. And the snapshot's
`X0.olean` was missing **seven** declarations that are in that very source:
`basePointIdealPow`, `relSectionIdealProd`, `relPicEquiv_sheaf_listSum_aj`,
`relPicEquiv_divisor_of_listSum_aj_eq`, `listSum_map_eq_of_relPicEquiv_divisor`,
`listSum_map_eq_of_listSum_aj_eq_of_compactSpace`, `exists_heckeCorrespondenceMorphism`
— while containing their older neighbours. The olean simply predated the source by two
days' worth of restatements.

**The reason is structural and will recur.** The snapshot is an `rsync` of the merge
worker's `.lake/build`, and an olean in there is whatever that directory last held for
that module. A module that was not rebuilt during the release — because the release was
held, because the build stopped at a red upstream, because lake replayed a `.trace` it
should not have — keeps an older olean while the SOURCE moves under it. The sha stamps
the SOURCES; nothing stamps the artifacts.

**The symptom is the one this file already teaches you to diagnose as something else.**
A scratch importing the module reports `Unknown identifier` for a name `grep` finds in
that module's source. That is the signature of a runaway comment (fourth/seventh
invisibility classes), of a namespace you guessed wrong, or of a missing import — and
all three of those checks come back CLEAN here, which reads as "impossible" rather than
as "the olean is old". Rule out the cheap causes and then suspect the artifact:

    # 1. is the name inside a comment?  character-level nesting scan -> depth 0 at its line
    # 2. is the namespace right?  probe the environment, do not guess:
    cat > Fermat/Probe.lean <<'EOF'
    module
    public import Fermat.FLT.<TheModule>
    @[expose] public section
    open Lean in
    run_cmd do
      let env ← Lean.getEnv
      let pats := ["<name1>", "<name2>"]          -- names you can SEE in the source
      let mut found : List String := []
      for (n, _) in env.constants.toList do
        for p in pats do
          if (n.toString.splitOn p).length ≥ 2 then found := n.toString :: found
      Lean.logInfo (String.intercalate "\n" found.eraseDups)
    EOF

Five seconds, and it is decisive: **a name present in the source and absent from the
environment, with comments balanced, means the olean is stale.** Nothing else produces
that combination.

**Consequences, and the second is the one that costs a run.** Every diagnostic from a
shim farm built on that snapshot is untrustworthy for the affected module — this is the
inconsistent-olean-set hazard, arriving through a route the existing recipes explicitly
bless. And the repair is NOT another `rsync`: it is `lake build <TheModule>`, which
rebuilds against the real sources. Budget it. Here that was ~40 min and it rebuilt far
more than the one module (811 of 5276 targets), so the staleness was not X0-only — the
"rsync it and the build is a replay" figure quoted elsewhere in this file did not hold
for release 33 either.

**So the honest sequencing for any task in a giant module is: build the UNMODIFIED
module first, then iterate in the scratch off that fresh olean, then one final build.**
Two builds, not one — but the first is not waste: it certifies the base you inherited,
it refreshes the artifact every later shim depends on, and it gives you the baseline
`declaration uses 'sorry'` line set that makes the differential check below possible.
Measured here: 5 s per scratch round afterwards, against 40 min per real build.

**And the differential check is what turns "it built" into "I broke nothing".** Take the
sorry-warning line numbers from both builds, drop your target from the baseline, and
require the two lists to correspond 1:1 under a MONOTONE, PIECEWISE-CONSTANT shift whose
steps equal your own insertions. Here that was `0 / 63 / 66 / 67 / 69` across four edited
regions, and it reproduces the `git diff` hunk sizes exactly — a receipt that no other
declaration in a 119 000-line file changed status, computable in a second from two logs.

