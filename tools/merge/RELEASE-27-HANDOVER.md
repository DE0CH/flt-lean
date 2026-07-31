# Release 27 — NOT PUBLISHED, and exactly why

`main` was **not moved** and `~/.flt-release-lake/sha` was **not rewritten**.
`main` is still `5b621e59` (= the last published release `7080929d` plus 19
`flt-loop:` tooling commits, no Lean), and the snapshot under
`~/.flt-release-lake/build` still matches it. That pairing is intact and was
deliberately left alone: publishing a red tree would have replaced a **green**
`main` and seeded every worktree in the fleet from a snapshot missing
`ModularCurve/X0.olean` and its whole cone.

`queue1` WAS rewritten — 337 tasks, `AUDITED: 5b621e59`, `queue2` emptied — so the
fleet is not idle. The tasks are audited against `main`, which is what dispatch
reads.

## What DID land, on `merger`

All 206 branches of the batch are ancestors of `merger`: 187 from release 26, and
the 19 this release merged. `verify_added.py --base 952fdf7d` over all 19 reports
**exactly one** set of missing declarations — flt-lean-106's, declined on purpose
(see its merge commit). Nothing was dropped by accident. `xdup.py`'s qualified
pass differences to **empty** against 952fdf7d, and `scopecheck.py`'s report shape
differs from the baseline only by MazurTorsion's four reports moving to X0 with
flt-lean-86's hoist.

Every module except `ModularCurve/X0.lean` builds. Rounds 1 and 2 of the release
build cleared `CurveAffineComplement`, `HyperellipticJacobian`,
`BinaryQuadraticForm` and `MoretBailly`, each verified individually with
`lake env lean`, EXIT=0.

## THE ONE BLOCKER: X0.lean, and it is INHERITED

**`X0.lean` has not been built since release 25.** Release 26's worker was killed
before reaching it, and every wound below is present *verbatim* at `952fdf7d`, its
tip — checked, not assumed. This release fixed nine of them and the count went
248 → 193. It is a multi-hour job on a file that takes ~35 minutes to elaborate,
and it is the only thing between this tree and a release.

### Method, in the order that pays

1. **Fix PARSE errors first, and expect more each round.** One parse error
   truncates the file, so every later error is invisible until it is fixed —
   which is why the count fell only 248 → 193 while nine real wounds were
   repaired. After round 2 these remained: 80434, 80524, 80542, 82118, 82209,
   82217, 95137, 97943.
2. The dominant shape is an **orphaned docstring body**: prose sitting
   immediately after a proof's last line with its `/--` gone. Repair by reopening
   it — as `/--` if the following declaration has no docstring, as `/-` if it
   does. Five were fixed this release (28613, 39659, 80879, 81547, and the
   truncated-header pair).
3. The other shape is a **truncated header**: `theorem foo {N : ℕ} {S : …}` and
   nothing else, with the renamed declaration following. Two were fixed. Check
   the CALL SITES to decide which signature survives, and put the retired name
   back as a one-line delegation.
4. **Read the warnings before the errors.** `linter.dupNamespace` named
   `Fermat.RelPoint.RelPoint.post_pre` three lines below the first of the 21
   errors it caused.
5. Only then the semantic residue: `Function expected at` (41),
   `Unknown identifier` (44), `Ambiguous term` (8), five `whnf` timeouts. A
   `whnf` timeout is reported at the START OF A DOCSTRING — the declaration to
   bump is the one BELOW that line.

The last full log is `/tmp/v_X0b.log` on nightcrawler (`-DmaxErrors=800`); it will
not survive a reboot, so regenerate with

    lake env lean -DmaxErrors=800 Fermat/FLT/ModularCurve/X0.lean

### Declaration order

Three order breakages were repaired (the `IsBaseChangeOf` calculus above the
rigidified-moduli cluster; `natDegree_minpoly_weberAlpha_le`; the
CurveAffineComplement swap). `flt-hoistcheck.py` decides these in seconds and
should be run BOTH directions before choosing which side to move. Note that
moving a declaration also moves it out of any `open X in` / `set_option … in`
that bound it — twice this release that was the second failure after the first
was fixed.

## Tooling added here

* `tools/merge/frontier.py` — the direct-sorry scan, VALIDATED against the
  compiler (25/25 modules exact). `flt-frontier.py` under-reports: 5 for
  `Interface.lean` against a true 15, 321 total against 333. The queue-coverage
  invariant is computed from that number.
* `tools/merge/xdup.py` — cross-file duplicates restricted to import-cone pairs,
  in a qualified pass (error) and a last-component pass (review list, only usable
  differenced against pre-merge `main`). The qualified pass is silent on this
  tree's giant modules because bare `end`s break namespace tracking, which is how
  flt-lean-86's ~80-declaration hoist duplication was nearly missed.
* `verify_added.py` now takes `--base <pre-merge sha>`; without it the check is
  vacuous after the batch and passes every branch.
