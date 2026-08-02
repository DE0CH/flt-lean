---
name: flt-correct-the-generators-dont-extract
description: "When a leaf wants h generators of an ideal inside a distinguished subset, correct the h you were given instead of extracting new ones — Nakayama discards the correction and the Krull-height count vanishes."
metadata: 
  node_type: memory
  type: project
  originSessionId: f4ab43e6-c139-40d6-97ce-7a7682a10ade
  modified: 2026-08-02T06:28:50.826Z
---

(2026-08-02, `flt-lean-367`, `exists_span_range_eq_of_span_union_pderiv_mem` in
`Fermat/FLT/GaloisRepresentation/HardlyRamified/ModThree.lean`.)

A leaf of the shape *"`I` has exactly `h` generators, all inside a distinguished subset
`S`"* looks like it needs a MINIMAL generating set — and then a lower bound on `μ(I)` to
get exactly `h`, which over a power series ring is Krull's height theorem and dimension
theory that this pin does not have. That was this leaf's recorded route and its whole
cost.

**No count is needed when the leaf already hands you `h` generators `P`.** Expand each
`Pᵢ = Σₖ a_{ik} sₖ` with `sₖ ∈ S`, and replace every coefficient by its CONSTANT part:

    P'ᵢ := Σₖ C(constantCoeff a_{ik}) · sₖ  ∈ S ,   Pᵢ − P'ᵢ ∈ 𝔪·I

so `I = span (range P) ≤ span (range P') + 𝔪·I`, and one application of
`Submodule.le_of_le_smul_of_le_jacobson_bot` gives `I = span (range P')`. The index type
stays `Fin h` by construction.

**Why:** `Submodule.mem_span_set'` + Nakayama. Two conditions, both cheap here —

* `S` is an additive subgroup closed under multiplication by CONSTANTS (not an ideal);
  true whenever `S` is cut out by a derivation, e.g. `{f ∈ I | ∀ j, ∂f/∂Xⱼ ∈ (3)}`;
* the coefficient subring reaches the residue field, which in `MvPowerSeries σ 𝒪` with
  `𝒪` local is `MvPowerSeries.isUnit_iff_constantCoeff` applied to
  `a − C(constantCoeff a)` and needs no knowledge of the residue field at all.

**How to spot it:** the docstring will say the count "is what keeps `P'` indexed by
`Fin h`". That is true of the route which THROWS AWAY the given generators and false of
every route that keeps them. See [[flt-leaf-cost-estimates-are-hypotheses]].

Mathlib pieces: `Submodule.le_of_le_smul_of_le_jacobson_bot`
(`Mathlib/RingTheory/Nakayama.lean` — eight variants there, read the list),
`Module.Flat.isSMulRegular_of_nonZeroDivisors`, `Submodule.mem_span_set'`. Transporting
regularity across a quotient by an idempotent ideal `(ε)` is four lines
(`3a = εx ⟹ 3(a − εa) = 0`), not a direct-sum decomposition.
