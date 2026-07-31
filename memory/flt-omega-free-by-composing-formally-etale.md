---
name: flt-omega-free-by-composing-formally-etale
description: Ω[K⁄k] free on a separating transcendence basis comes from FormallyEtale.comp + tensorKaehlerEquivOfFormallyEtale — no Jacobi–Zariski exact sequence
metadata:
  type: reference
---

To prove `Ω[K⁄k]` is free on `dt₁,…,dt_d` for a **separating** transcendence
basis, the obvious route is `Mathlib/RingTheory/Kaehler/JacobiZariski.lean`:
the exact sequence for `k → k(t) → K`, `Ω[K⁄k(t)] = 0` by separability, then an
injectivity argument for the base-change map. The dispatch prompt named exactly
that route.

The short route does not touch an exact sequence at all. With
`A := MvPolynomial ι k` mapped to `K` by `aeval t`:

* `A → k(t)` is `IsFractionRing`, hence `Algebra.FormallyEtale.of_isLocalization`;
* `k(t) → K` is separable algebraic, hence `Algebra.FormallyEtale.of_isSeparable`;
* `Algebra.FormallyEtale.comp` gives `FormallyEtale A K`;
* `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A K : K ⊗[A] Ω[A⁄k] ≃ₗ[K] Ω[K⁄k]`;
* `KaehlerDifferential.mvPolynomialBasis k ι` is a basis of `Ω[A⁄k]`, and
  `Module.Basis.baseChange` carries it across.

That is ~40 lines. The fiddly parts are not mathematical: building
`Algebra A ↥(IntermediateField.adjoin k (Set.range t))` and getting
`IsFractionRing A ↥E` out of `AlgebraicIndependent.aevalEquivField` (a `k`-algebra
equiv, which has to be upgraded to an `A`-algebra equiv with
`AlgEquiv.ofRingEquiv` before `IsFractionRing.of_algEquiv` will take it).

Done in `Fermat/FLT/Mathlib/FieldTheory/KaehlerField.lean` as
`FLT.exists_kaehlerBasis_of_isTranscendenceBasis` (2026-07-31).

General form: **when a prompt names an exact sequence, first check whether the
property it is being used to establish is already a composable class.**
Formal étaleness, flatness and smoothness all compose, and a composition lemma
beats an exactness argument every time.

See [[flt-derivations-replace-a-p-basis]] for what this freeness then buys.
