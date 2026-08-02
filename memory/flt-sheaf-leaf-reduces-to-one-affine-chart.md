---
name: flt-sheaf-leaf-reduces-to-one-affine-chart
description: "A leaf whose clauses quantify over OPENS is a leaf about one ring; mathlib has all three bridges, and the third is unfindable by concept-grep"
metadata: 
  node_type: memory
  type: project
  originSessionId: 392ffa15-6363-45d5-ab3f-87e4bca0b93a
  modified: 2026-08-01T17:36:09.492Z
---

(2026-08-01, `flt-lean-193`, `exists_generator_sectionIdeal_at_section` in
`ModularCurve/RelativePicard.lean`.) Two recuts in one run, `1 → 1` each, taking the leaf from
"a clause at every open `W ≤ U`" to "one affine chart, `ker (σ.app U) = span {s}` with
`s ∈ nonZeroDivisors`" — Stacks 0C4S as the literature states it.

**The reduction is two mechanical steps and the pin supports both end to end.**

1. *all opens → a BASIS*: `TopCat.Sheaf.eq_of_locally_eq'` for a "`… = 0 → … = 0`" clause,
   `TopCat.Sheaf.existsUnique_gluing'` for an "`∃ r, x = r·s`" clause. Prove the first for
   every open FIRST and consume it — it is what makes the local cofactors agree on overlaps.
   Take the basis as an abstract predicate so the caller picks the family.
2. *a basis → ONE affine chart*, the basis being the basic opens of an affine `U`:
   * `IsAffineOpen.exists_basicOpen_le` (basis fact, for an affine OPEN — `isBasis_basicOpen`
     is only for `⊤` of an affine scheme and transporting it by hand is the wrong move);
   * `IsAffineOpen.isLocalization_basicOpen`, with `X.presheaf.map (homOfLE (basicOpen_le f)).op a`
     **= `algebraMap … a` by `rfl`** (`algebra_section_section_basicOpen`);
   * **`IsAffineOpen.app_basicOpen_eq_away_map`** — factors `f.app (Y.basicOpen r)` as
     `IsLocalization.Away.map` of `f.app U` then an `eqToHom` transport. Needs
     `IsAffineOpen (f ⁻¹ᵁ U)` too. This is what makes "the kernel of `f^♯` localizes" six lines.

**A concept-grep never finds the third one** — "kernel", "localize", "exact" all miss; it is
named after the shape of the factorization. Read the `isLocalization_basicOpen` neighbourhood
of `Mathlib/AlgebraicGeometry/AffineScheme.lean` top to bottom instead: `appLE_eq_away_map`,
`app_basicOpen_eq_away_map`, `appBasicOpenIsoAwayMap` are the whole affine-chart dictionary and
sit within thirty lines of each other.

**Derive the bridge's extra hypothesis in the ASSEMBLY, not by widening the leaf.**
`IsAffineOpen (σ ⁻¹ᵁ U)` was free: `IsProper` + section ⟹ closed immersion ⟹ `IsAffineHom`
(instance) ⟹ `IsAffineOpen.preimage`. That also corrected the leaf's own audit, which said
`_hproper` was unused in that half.

See [[flt-leaf-cost-estimates-are-hypotheses]] and
[[flt-inventory-audits-understate-what-exists]]; the CLAUDE.md section of the same title has
the Lean traps (`ConcreteCategory.hom` vs `CommRingCat.Hom.hom`, cured by a type-ascribing
`have`).
