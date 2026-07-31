---
name: flt-hoisted-leaf-orphaned-by-reproof
description: Glue-first hoisting plus a later re-proof of the parent leaves the hoisted leaf with no consumer — a free-floating sorry that every frontier scan reports as ordinary work
metadata:
  type: project
---

`diffChar_pullbackRatio_eq` was hoisted out of an inner `have … := sorry` inside
`exists_diffCharScalar_poly` on 2026-07-30 — correct glue-first practice, so the
open node would have a name a frontier scan could dispatch at. **Later the same
day** the parent was re-proved along a completely different route (over
`exists_diffCharScalar_polyData`, no derivation on the coordinate ring at all).
The hoisted declaration was left in the file with **no consumer**, carrying a
150-line docstring that still asserted it was "the one remaining input" of a
theorem that no longer calls it.

It survived a release and was still there on 2026-07-31, sitting one line below
the genuinely open leaf, indistinguishable from it to every instrument: it emits
`declaration uses 'sorry'`, it is in no ownership record, and its docstring reads
as a live route.

**Why:** hoisting creates a consumer edge that the parent's *next* proof does not
have to preserve, and nothing checks that it still exists. This is the same shape
as [[flt-delete-times-refactor-orphans-a-leaf]] but from one author in one day, so
no merge is involved and no conflict ever surfaces.

**How to apply:** when you re-prove a theorem along a new route, `grep` for every
leaf you previously hoisted out of its old proof and check it still has a caller —
`grep -n '<name>'` and look for a use that is not a docstring. If it has none,
delete it and say in the commit where to recover it. And when reading a leaf's
docstring, treat "its one remaining input is X" as a claim to verify against the
parent's actual proof term, not as fact; here the parent's body was three lines and
mentioned nothing of the sort.
