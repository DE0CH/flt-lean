---
name: flt-galois-map-surjectivity-is-a-silent-debt
description: "A clause quantified over `σ : Γ F` constrains `Γ ℚ` only on the image of `Field.absoluteGaloisGroup.map`; a leaf reading it at arbitrary `τ` silently owes surjectivity, and `Type u` indexing forces `F = ULift.{u} ℚ`."
metadata: 
  node_type: memory
  type: project
  originSessionId: 423cf59a-ac46-4e0c-b81e-718ff9e73a77
  modified: 2026-08-02T19:19:25.354Z
---

(2026-08-02, `det_eq_cycCharModN_of_isStandardLevelModule`, `Modularity/MoretBailly.lean`.)
`Field.absoluteGaloisGroup.map f` is built from an ARBITRARILY CHOSEN embedding of
algebraic closures, so a hypothesis of the shape
`∀ (F : Type u) … (σ : Γ F), P (ρ (map (algebraMap ℚ F) σ))` constrains `ρ` only on
`range (map (algebraMap ℚ F))`. A leaf whose conclusion is about an arbitrary
`τ : Γ ℚ` therefore owes SURJECTIVITY of that map, and nothing in the statement says so
— the map is applied inside the clause where nobody reads it.

**Why:** the leaf's own three-step route omitted this entirely; it was found only by
asking how `τ` gets into the equivariance clause at all.

**How to apply:** when a leaf's conclusion names an object at `τ : Γ K` and its
hypothesis names it at `map g σ`, compute `range (map g)` before costing anything.
`Λ`-style families indexed by `F : Type u` cannot be instantiated at `ℚ : Type 0`, so
the admissible copy is `ULift.{u} ℚ` and `algebraMap ℚ (ULift.{u} ℚ)` is an
isomorphism — then `surjective_absoluteGaloisGroup_map_of_bijective` (proven in that
file) discharges it. The same range is computed as an internal `have` inside
`normal_range_absoluteGaloisGroup_map`, which exports only normality — see
[[flt-fact-proven-inside-a-body]] shape. Instance traps: `Algebra.IsAlgebraic K
(AlgebraicClosure K)` is NOT an instance (use `AlgebraicClosure.isAlgebraic K`), and
the torsion hypothesis is spelled `Module.IsTorsionFree`.
