## PARSE WOUNDS ARE FOUND IN ONE PASS, NOT ONE PER BUILD ROUND — `tools/merge/parsecheck.py`
(2026-07-31, `flt-lean-327`.) Release 27 did not publish, and its single blocker was
`ModularCurve/X0.lean` failing to PARSE. The handover's own accounting is the argument for this
tool: *"One parse error truncates the file, so every later error is invisible until it is fixed —
which is why the count fell only 248 → 193 while nine real wounds were repaired."* Each round
costs a ~35-minute elaboration of a 108k-line file, so the wounds are cleared SERIALLY, at
build-cost each, for hours.
They do not need a build. The dominant wound is a merge dropping a `/--` opener while its prose
and its `-/` survive, which leaves **an unmatched `-/` — not legal Lean 4 in any context**, so it
is exactly detectable by a scanner in under a second. `tools/merge/parsecheck.py` finds that, the
mirror case (a lost `-/`, whose block comment swallows the rest of the file), and naked prose in
column 0 when the `/--` and `-/` were lost together — including a markdown `## heading`, which is
not a Lean `#` command.
- **Calibrated on green trees, and keep it that way**: 0 findings over `main`'s 359 files
  (release 26's published tree) and over `merger`'s 376 unwounded files. A hard finding on a file
  that really compiles is a whitelist bug — add the starter, never weaken the check.
- **The merge worker should run it after EVERY merge**: `tools/merge/parsecheck.py --git <rev>`
  needs no checkout and no build, and sweeps the tree in ~30 s. It found a wound in
  `FreyCurve/MazurTorsion.lean` that release 28 had just introduced and its build had not reached.
- **Do not chase the compiler's line numbers past the first wound.** Of the eight positions the
  release-27 handover lists as still failing, `82118` is not a wound at all — it sits inside a
  properly delimited comment, and was reported only because the compiler's comment nesting had
  already diverged at the unmatched `-/` above it. Repair everything the scanner reports in one
  pass, then rebuild.
- **What it does not catch**: an orphaned fragment that is INDENTED (X0.lean at `1ead8a94` had one
  at 95137, a binder list left under a finished proof by a retyped header). Column 0 is what makes
  the other shapes decidable without a parser. A clean run promises sound delimiters, not that the
  file parses.
