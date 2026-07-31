/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.RingTheory.InvariantBaseChange
public import Fermat.FLT.Mathlib.AlgebraicGeometry.SmoothConnectedCriteria
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The invariants of a smooth curve algebra are geometrically regular

Let `k` be a field, `S` a smooth `k`-algebra of Krull dimension one, `G` a finite group
acting on `S` by `k`-algebra automorphisms and `R = S^G` its ring of invariants, embedded
in `S`.  This module proves

  `isRegularRing_tensorProduct_of_isInvariant : IsRegularRing (K ⊗[k] R)`

for every ALGEBRAIC field extension `K/k` — in the application `K = k̄`, and the point of
the base change is that `IsRegularRing R` alone is strictly weaker over an imperfect `k`
and does not give smoothness (the standing witness is the quasi-elliptic
`y² = x³ + t` over `𝔽₃(t)`, recorded on
`smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing`).

## What is proven here and what is left

Everything about the BASE CHANGE is proven:

* `R ⊗[k] K` is the ring of invariants of `S ⊗[k] K` — this is
  `Fermat.InvariantBaseChange.isInvariant_tensor`, since a field extension is flat;
* `S ⊗[k] K` is smooth over `K` — `Algebra.Smooth.baseChange`, transported across
  `Algebra.TensorProduct.commRight` because mathlib states the instance for `K ⊗[k] S`
  and the invariant machinery is written for `S ⊗[k] K`;
* `ringKrullDim (S ⊗[k] K) = ringKrullDim S`.  **No dimension theory of finite-type
  algebras is needed for this, and that is worth knowing**: because `K/k` is ALGEBRAIC,
  `S ⊗[k] K` is INTEGRAL over `S` (`Algebra.IsIntegral.tensorProduct`) and `S` injects
  into it (`Algebra.TensorProduct.includeLeft_injective`, `S` being flat over the field
  `k`), so `ringKrullDim_eq_of_isIntegral_of_injective` applies verbatim.  A route through
  "Krull dimension is invariant under base field extension" — which the leaf's docstring in
  `ModularCurve/X1.lean` named as one of the three missing general theorems — would have
  been a genuine piece of missing theory; it is not needed at an algebraic extension.

What is left is ONE leaf, `isRegularRing_of_isInvariant_of_smooth`, which contains no
tensor product and no base change: *the ring of invariants of a finite group acting on a
smooth algebra of Krull dimension one over a field is regular.*  See its docstring.
-/

@[expose] public section

open scoped TensorProduct

namespace Fermat.InvariantTensorRegular

/-! ### The residual leaf -/

/-- **The invariants of a finite group acting on a SMOOTH algebra of Krull dimension one
over a field form a REGULAR ring** (sorry leaf) — Deligne–Rapoport III.1, Katz–Mazur 8.2.1,
in the ring-theoretic form; classically, "the quotient of a smooth affine curve by a finite
group is again a smooth affine curve" in the normal-and-one-dimensional formulation.

This is what is left of `X1.lean`'s
`isRegularRing_tensorAlgebraicClosure_of_isInvariant` once the base change is paid for; see
that file for the modular consumer and this module's header for what the base change costs
(nothing — it is `Fermat.InvariantBaseChange.isInvariant_tensor` plus integrality of an
algebraic extension).

## THE ROUTE, AND WHY IT IS NOT FIVE LINES

The classical argument is three steps:

1. `S` is smooth over a field, hence REGULAR, hence REDUCED and integrally closed in its
   total quotient ring;
2. the invariants of a normal ring under a finite group are normal
   (`Algebra.IsInvariant.isIntegrallyClosed_of_isInvariant` in
   `Fermat/FLT/Mathlib/RingTheory/InvariantCoarseRing.lean`), and the Krull dimension is
   unchanged because `R → S` is integral and injective
   (`ringKrullDim_eq_of_isIntegral_of_injective`);
3. normal + Noetherian + dimension one ⇒ regular, which for a DOMAIN is mathlib's
   `[IsDedekindDomain R] : IsRegularRing R`.

**`IsDomain` is the whole difficulty, and it is not available.** `S` here is the base
change to `k̄` of the coordinate ring of a rigidified moduli scheme, and over a field
containing `ζ_n` that scheme SPLITS into `φ(n)` components — so neither `S` nor `R` is a
domain, and both step 2's `isIntegrallyClosed_of_isInvariant` and step 3's Dedekind
instance carry `[IsDomain R]` at this pin (verified in `InvariantCoarseRing.lean` and in
`Mathlib/RingTheory/RegularLocalRing/Defs.lean`).

So a prover has to supply, in some form, the **product decomposition**: a reduced normal
Noetherian ring is a finite product of normal domains, `G` permutes the factors, and the
invariant ring is the finite product of the invariant rings of the STABILISERS, each of
which IS a domain and to which the existing lemmas then apply; and a finite product is
regular iff each factor is.  The same decomposition is written out on
`transitiveMinimalPrimes_of_gamma1GITPresentation` in `X1.lean`.

## WHAT IS MISSING FROM THE PIN (measured 2026-07-31, at `a3364fa`)

Three separate absences, each checked by grep rather than recalled:

* **smooth over a field ⇒ regular, or ⇒ integrally closed.**
  `grep -rn 'IsRegularLocalRing\|IsRegularRing' Mathlib/RingTheory/Smooth/ Mathlib/RingTheory/Etale/`
  is EMPTY, and `Mathlib/RingTheory/RegularLocalRing/` consists of `Defs.lean` and
  `Polynomial.lean` only — there is no `IsRegularLocalRing → IsIntegrallyClosed` and no
  link to smoothness anywhere.  This tree has the CONVERSE,
  `Algebra.Smooth.of_isRegularRing_of_perfectField`
  (`Fermat/FLT/Mathlib/RingTheory/Smooth/RegularLocal.lean`), and it cannot be run
  backwards.  What this tree DOES have in the forward direction is
  `Algebra.Smooth.isReduced_of_isField`
  (`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`), which is
  reducedness and nothing more.
* **normality does not localise without a domain.**  Every lemma in
  `Mathlib/RingTheory/LocalProperties/IntegrallyClosed.lean` — `of_localization_maximal`,
  `of_localization`, `of_isLocalization_maximal` — carries `[IsDomain R]`.  So the obvious
  "check regularity prime by prime" reduction of step 3 does NOT go through as stated: one
  can localise `IsNoetherianRing`, `IsReduced` and `Ring.KrullDimLE 1` and not
  `IsIntegrallyClosed`.
* **no structure theory of reduced normal Noetherian rings.**  There is no
  "finite product of normal domains" statement, and the total quotient ring of a reduced
  Noetherian ring is not known to be artinian here, so the idempotent argument that
  produces the decomposition has to be built.

**The route that DOES look shortest**, and the reason the second bullet is worth recording:
prove `IsRegularRing` prime-locally after all, and get the domain property at each prime
from the LOCAL statement *a reduced Noetherian local ring that is integrally closed in its
total quotient ring is a domain* (its total quotient ring is artinian and reduced, hence a
finite product of fields; the idempotents are integral over the ring, hence in it; a local
ring has no nontrivial idempotents, so there is one minimal prime).  Mathlib does have the
artinian half of that — `IsArtinianRing.equivPi` for a reduced commutative artinian ring,
and `IsArtinianRing.isField_of_isReduced_of_isLocalRing`.

## FAITHFULNESS

`hdim` is load-bearing and is where NONDEGENERACY enters: it is consumed as
`Ring.KrullDimLE 1 S` and is what makes step 3 available at all.  Note that regularity is
FALSE for invariants in dimension `≥ 2` — `k[x,y]^{±1}`, the quadric cone
`k[u,v,w]/(uv − w²)`, is normal and not regular — so no proof can avoid using it.

`hinj` is what makes `R` a subring of `S` rather than merely an algebra over it; without it
take `R := k[x]/(x²) → S := k` with `G` trivial, where `R` is `S^G` in the sense of
`Algebra.IsInvariant` and `R` is not reduced, let alone regular.

`[Finite G]` is consumed twice: by `Algebra.IsInvariant.isIntegral`, and by the orbit
grouping in the product decomposition.

The statement is NOT vacuous: `S := k[x]`, `G := ℤ/2` acting by `x ↦ -x`, `R = k[x²]` is an
inhabitant with `R` regular, and so is any `S` split into several components with `G`
permuting them. -/
theorem isRegularRing_of_isInvariant_of_smooth (K R S : Type)
    [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra R S] [Algebra K S]
    [IsScalarTower K R S] (G : Type) [Group G] [Finite G] [MulSemiringAction G S]
    [SMulCommClass G R S] [Algebra.IsInvariant R S G] [Algebra.Smooth K S]
    (_hinj : Function.Injective (algebraMap R S))
    (_hdim : ringKrullDim S = (1 : ℕ)) :
    IsRegularRing R :=
  sorry

/-! ### The base change, which is free -/

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k K R S : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsIntegral k K]
  [CommRing R] [CommRing S] [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
  (G : Type) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]

omit [Algebra.IsIntegral k K] in
/-- `S` embeds in `S ⊗[k] K`, because `S` is flat over the field `k`. -/
theorem injective_algebraMap_tensorRight :
    Function.Injective (algebraMap S (S ⊗[k] K)) :=
  Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k K).injective

/-- **The Krull dimension is unchanged by an ALGEBRAIC base field extension** — because the
extension is then integral, so no dimension theory of finite-type algebras is needed. -/
theorem ringKrullDim_tensorRight :
    ringKrullDim (S ⊗[k] K) = ringKrullDim S :=
  ringKrullDim_eq_of_isIntegral_of_injective S (S ⊗[k] K)
    (injective_algebraMap_tensorRight k K S)

omit [Algebra.IsIntegral k K] in
/-- The scalar tower `K → R ⊗[k] K → S ⊗[k] K`, for the right-hand algebra structures and
the base-changed inclusion. -/
theorem isScalarTower_tensorRight :
    letI := Fermat.InvariantBaseChange.bcAlgebra (B := R) (A := S) k K
    IsScalarTower K (R ⊗[k] K) (S ⊗[k] K) := by
  letI := Fermat.InvariantBaseChange.bcAlgebra (B := R) (A := S) k K
  refine IsScalarTower.of_algebraMap_eq fun κ => ?_
  show (1 : S) ⊗ₜ[k] κ = Fermat.InvariantBaseChange.bcInclusion k K ((1 : R) ⊗ₜ[k] κ)
  rw [Fermat.InvariantBaseChange.bcInclusion_tmul, map_one]

omit [Algebra.IsIntegral k K] in
/-- `S ⊗[k] K` is smooth over `K` — mathlib's `Algebra.Smooth.baseChange` states this for
`K ⊗[k] S`, and `Algebra.TensorProduct.commRight` is the `K`-algebra equivalence between
the two orientations. -/
theorem smooth_tensorRight [Algebra.Smooth k S] : Algebra.Smooth K (S ⊗[k] K) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k K S)

/-- **THE BASE-CHANGED INVARIANT RING OF A SMOOTH CURVE ALGEBRA IS REGULAR**, for any
ALGEBRAIC extension `K/k` — proven over the single leaf
`isRegularRing_of_isInvariant_of_smooth`, which mentions no tensor product.

The `K`-algebra structure on `K ⊗[k] R` in the conclusion is mathlib's standard one, so a
consumer never has to know that the proof runs on the other orientation. -/
theorem isRegularRing_tensorProduct_of_isInvariant
    [Algebra.IsInvariant R S G] [Algebra.Smooth k S]
    (hinj : Function.Injective (algebraMap R S))
    (hdim : ringKrullDim S = (1 : ℕ)) :
    IsRegularRing (K ⊗[k] R) := by
  classical
  haveI : SMulCommClass G k S :=
    Fermat.InvariantBaseChange.smulCommClass_of_isScalarTower k R S G
  letI := Fermat.InvariantBaseChange.bcAction (A := S) k K G
  letI := Fermat.InvariantBaseChange.bcAlgebra (B := R) (A := S) k K
  haveI := Fermat.InvariantBaseChange.isInvariant_tensor (B := R) (A := S) k K G
  haveI := Fermat.InvariantBaseChange.smulCommClass_tensor (B := R) (A := S) k K G
  haveI := isScalarTower_tensorRight k K R S
  haveI := smooth_tensorRight k K S
  have hinj' : Function.Injective (algebraMap (R ⊗[k] K) (S ⊗[k] K)) :=
    Fermat.InvariantBaseChange.injective_bcInclusion k K hinj
  have hdim' : ringKrullDim (S ⊗[k] K) = (1 : ℕ) := by
    rw [ringKrullDim_tensorRight k K S, hdim]
  haveI := isRegularRing_of_isInvariant_of_smooth K (R ⊗[k] K) (S ⊗[k] K) G hinj' hdim'
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k R K).toRingEquiv

end BaseChange

end Fermat.InvariantTensorRegular

end
