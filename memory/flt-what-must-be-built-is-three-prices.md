---
name: flt-what-must-be-built-is-three-prices
description: "A leaf's \"WHAT MUST BE BUILT: X, Y, Z\" is three separate prices; one item is often a 60-line CONSTRUCTION you can hand in as a hypothesis, giving a clean 1→1 recut"
metadata: 
  node_type: memory
  type: project
  originSessionId: 0e57a746-72b7-460b-a457-aa14865253be
  modified: 2026-08-01T00:58:21.537Z
---

`exists_fontaineCoordinates_of_not_primeFieldValued` (ModThree.lean) listed three
build-items and had been reported as "a chapter" three times. Item 1 — the unramified
coefficient ring `W(κ) ⊆ 𝒪_E` — was **60 lines**, and handing it in as a hypothesis is a
`1 → 1` recut that leaves the expensive items untouched.

**Why:** a list item that is a CONSTRUCTION can be handed in as a hypothesis; a list item
that is a THEORY cannot. Nobody prices them separately because the list reads as one cost.

**How to apply:** split any "WHAT MUST BE BUILT" list and price each entry alone. Then:

* the coefficient-ring construction is `exists_teichmullerSection` (now in ModThree.lean):
  Hensel on `X ^ q − X` once per element of the finite residue field. Use `X ^ q − X` (its
  derivative is `−1` on the nose, no case split) and lift EVERY element rather than a
  generator of `kˣ` — the generator route needs `Subgroup.zpowers` bookkeeping that timed
  out in `Patching.lean`. `HenselianRing R (maximalIdeal R)` is free from `IsAdicComplete`;
  `HenselianLocalRing` is a different class with no instance path from it.
* **base-change the ALGEBRA (`A ⊗ 𝒲`), never map `𝒲` into `A ⧸ J`** — the tensor carries
  the structure by construction, so no second Hensel lift is owed. Legal because an
  UNRAMIFIED base extension does not move the Hom-sets (a map `𝒲 → 𝒪/𝔪^k` over a fixed
  residue map is unique).
* the one-line check that a base change is FORCED: a surjection out of a LOCAL ring makes
  the target's residue field a QUOTIENT of the source's, and an extra power-series VARIABLE
  cannot supply a residue generator (variables land in the maximal ideal, a generator lift
  is a unit).

Report it as a recut: the count does not move. See [[flt-leaf-cost-estimates-are-hypotheses]].
