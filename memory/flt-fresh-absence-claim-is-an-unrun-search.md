---
name: flt-fresh-absence-claim-is-an-unrun-search
description: "An absence claim in a leaf YOU are writing is as wrong as an inherited one — check your own import cone with #check, not the pin at large"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 763221bf-b241-4c0f-8234-03cf7cded384
  modified: 2026-08-02T04:07:32.627Z
---

(2026-07-31, `flt-lean-61`, `MazurTorsion.lean`.) I wrote a `MACHINERY SURVEY`
on a leaf I was **creating**, saying the pin has "no lattices in `ℂ`, no
Weierstrass `℘`, and no uniformisation". False on two of three counts the day it
was written: `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` is
1080 lines carrying `PeriodPair`, `℘`, `℘'`, `g₂`, `g₃` and
`derivWeierstrassP_sq` — the whole lattice-→-cubic direction — and it was
**already in that file's import cone** via
`KnownIn1980s/EllipticCurves/TateCurveConstruction.lean`.

**Why:** I searched for the THEORY name ("uniformisation", "complex torus") and
never asked what my own declaration could CITE. A leaf's survey is not a claim
about the pin at large; it is a claim about the leaf's import cone, and that is
computable.

**How to apply:** before writing "the pin lacks X" in any docstring —
`ls .lake/packages/mathlib/Mathlib/<dir X would live in>/`, then decisively
`#check @<name>` from a scratch that `public import`s YOUR OWN file (~15 s).
Also `grep -rn "FALSE-ABSENCE" --include=*.lean Fermat/` — in this fleet the
same correction has usually been made already, and here it had been, one file
away in `X0.lean`, the previous day.

Corrected, the survey re-priced the residue from "take on the analytic theory"
to four named gaps on top of an existing `℘`. See
[[flt-inventory-audits-understate-what-exists]] and
[[audit-lacks-x-is-about-x]]; this is the same defect with the staleness
removed.
