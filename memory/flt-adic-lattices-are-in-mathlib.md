---
name: flt-adic-lattices-are-in-mathlib
description: 𝒪_w-lattice leaves are cheap — Mathlib.Algebra.Module.Lattice does the free/rank/extend work, and the only missing piece is IsPrincipalIdealRing on adicCompletionIntegers, now proven in KhareWintenberger.lean
metadata:
  type: project
---

`Mathlib.Algebra.Module.Lattice` (already imported by `Modularity/KhareWintenberger.lean`)
carries the whole `𝒪`-lattice toolkit: `Submodule.IsLattice` (fg + spans over `K`),
`IsLattice.free`, `Basis.extendOfIsLattice` (an `𝒪`-basis of a lattice IS a `K`-basis of the
ambient space), and `IsLattice.finrank_of_pi`. Anything of the shape "a full `𝒪_w`-lattice
in `K^n` is free of rank `n` and its basis is a `K`-basis" is four lines, not a project.

The one instance mathlib does NOT have is `IsPrincipalIdealRing ↥(v.adicCompletionIntegers K)`.
It is now `GaloisRepresentation.Modularity.isPrincipalIdealRing_adicCompletionIntegers` in
`Modularity/KhareWintenberger.lean` (2026-07-31): `Valued.v` on the completion is surjective
(`valuedAdicCompletion_surjective`), so its `valueGroup` is `⊤` in `ℤᵐ⁰ˣ`, hence cyclic and
nontrivial, hence `Valuation.valuationSubring_isPrincipalIdealRing` applies —
`adicCompletionIntegers K v` is `Valued.v.valuationSubring` by `rfl`. `IsFractionRing`,
`IsDomain` and `Module.IsTorsionFree` for it already resolve by `inferInstance`.

**Why:** `exists_integralSplitting_of_valuation_traceDiscr_eq_one`'s docstring had recorded
"`IsMaximalOrder` has zero hits in mathlib, so the maximal-order vocabulary has to be
introduced" and predicted a theory-building job. No maximal-order vocabulary was needed at
all: the classical "all maximal orders of `M₂(F_w)` are conjugate to `M₂(𝒪_w)`" splits into
(a) conjugate the order INTO `M₂(𝒪_w)` — pure lattice theory, `Λ · e₀` is a stable full
lattice — and (b) get the REVERSE inclusion from the UNIT discriminant, by unimodularity of
the trace form: `tⱼ = tr(x βⱼ)` is integral and `c ᵥ* G = t`, so `c = t ᵥ* G⁻¹` is integral.
No index formula `disc Λ = [Λ':Λ]² disc Λ'` is ever needed, and the `2⁴` in the regular-trace
Gram determinant never has to be computed.

**How to apply:** when a leaf asks for an integral normal form at a place, look for the
lattice + unimodular-pairing pair of halves before believing a docstring that says new
theory is required. Reading matrices in a lattice basis is
`Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv eK)` — an `AlgEquiv`, i.e. the
conjugation, without ever forming the change-of-basis matrix or inverting it.
See [[flt-cleaner-statement-harder-proof]] and [[audit-searched-production-not-invariant]].
