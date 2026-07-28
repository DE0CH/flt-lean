/-
Fermat/FLT/Mathlib/RingTheory/InvariantCoarseRing.lean — own work for the
Fermat project (not vendored from the FLT project).

# The ring of invariants of a Dedekind domain under a finite group

This module is the commutative-algebra half of "the coarse space of a
Katz–Mazur atlas is a smooth geometrically connected curve": everything about
`Spec (A^G)` that can be said without mentioning a moduli problem.

Its consumer is `Fermat/FLT/ModularCurve/X0.lean`, where `A` is the coordinate
ring of the rigidified moduli scheme `𝔐([Γ₀(N)], [Γ(n)])`, `G = GL₂(ℤ/n)` is
the deck group and `B = A^G` is the coordinate ring of `Y_0(N)`.  Nothing here
knows that; the statements are about an arbitrary finite group acting on an
arbitrary Dedekind domain of finite type over a field.

## The classical statement

Let `k` be a field, `S` a Dedekind domain of finite type over `k`, `G` a finite
group acting on `S` by `k`-algebra automorphisms, and `R = S^G` its ring of
invariants.  Then `R` is again a Dedekind domain of finite type over `k`, with
the same Krull dimension as `S`.  The three inputs are:

1. **Noether's theorem on invariants** — `R` is of finite type over `k`.  The
   proof here is the Artin–Tate one: `S` is integral over `R`
   (`Algebra.IsInvariant.isIntegral`, mathlib) and of finite type over `R`,
   hence module-finite over `R`, and `Algebra.fg_of_fg_of_fg` (mathlib's
   Artin–Tate lemma, Atiyah–Macdonald 7.8) concludes.
2. **Invariants of a normal domain are normal** — Matsumura §23, or
   Bourbaki *Commutative Algebra* V §1.9.  This is
   `isIntegrallyClosed_of_isInvariant`.
3. **Krull dimension is unchanged by a finite group quotient** — because `S` is
   integral over `R`, going up and incomparability make
   `PrimeSpectrum S → PrimeSpectrum R` a surjection that reflects and preserves
   strict inclusions.  Here only the one-dimensional case is needed, so it is
   proven directly from `Ring.DimensionLEOne` plus lying over.

Regularity is then free: mathlib has `[IsDedekindDomain R] : IsRegularRing R`.

## Geometric integrality

The second half of the consumer's needs is that `B ⊗[ℚ] K` is a domain for every
field extension `K/ℚ`.  Two pieces live here:

* `isDomain_tensorProduct_of_algebraicClosure_eq_bot` — the field-theoretic
  statement that a field extension `L/k` over a PERFECT `k` with `k`
  algebraically closed in `L` is a *regular* extension, i.e. `L ⊗[k] K` is a
  domain for every `K/k`.  This is the one LEAF of this module.  (The hypothesis
  was `CharZero k` until 2026-07-28; it was weakened to `PerfectField k`, which
  is what the recorded proof sketch actually uses and what the characteristic-`p`
  consumer over `𝔽_p` needs.  `CharZero ⟹ PerfectField` is an instance, so no
  call site changed.)
* `isDomain_tensorProduct_of_injective` — the transfer from the fraction field
  down to the ring, which is just flatness of a field over a field (PROVEN).

## Contents

* `Algebra.IsInvariant.finiteType_of_isInvariant` — Noether (PROVEN)
* `Algebra.IsInvariant.isIntegrallyClosed_of_isInvariant` — normality (PROVEN)
* `Algebra.IsInvariant.dimensionLEOne_of_isInvariant` — dimension ≤ 1 (PROVEN)
* `Algebra.IsInvariant.ringKrullDim_eq_one_of_isInvariant` — dimension = 1 (PROVEN)
* `Algebra.IsInvariant.isDedekindDomain_of_isInvariant` — assembly (PROVEN)
* `Algebra.IsInvariant.isRegularRing_of_isInvariant` — the packaged conclusion
  the modular-curve consumer asks for (PROVEN)
* `isDomain_tensorProduct_of_algebraicClosure_eq_bot` — regular extensions (LEAF)
* `isDomain_tensorProduct_of_injective` — descent to a subring (PROVEN)
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

open scoped TensorProduct

namespace Algebra.IsInvariant

/-! ### Noether's theorem on invariants -/

/-- **Noether's theorem on invariants** (PROVEN): the invariants of a
finite-type algebra under a finite group are again of finite type.

The proof is Artin–Tate.  `S` is integral over `R = S^G` because `G` is finite
(`Algebra.IsInvariant.isIntegral`, mathlib), and `S` is of finite type over `R`
because it is of finite type over `k`; an integral algebra of finite type is
module-finite, so `Algebra.fg_of_fg_of_fg` applies to the tower `k ⊆ R ⊆ S`. -/
theorem finiteType_of_isInvariant (k R S : Type*) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsNoetherianRing k] [Algebra.FiniteType k S]
    (hinj : Function.Injective (algebraMap R S)) :
    Algebra.FiniteType k R := by
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType k R S
  haveI : Module.Finite R S := Algebra.IsIntegral.finite
  exact ⟨fg_of_fg_of_fg k R S ‹Algebra.FiniteType k S›.out ‹Module.Finite R S›.fg_top hinj⟩

/-! ### Invariants of a normal domain are normal -/

/-- **Invariants of an integrally closed domain are integrally closed**
(PROVEN) — Matsumura §23, Bourbaki *Commutative Algebra* V §1.9.

Write `K = Frac R`, `L = Frac S`.  Because `R → S` is injective and `S` is a
domain, `K` embeds in `L` as a subfield (`FractionRing.liftAlgebra`), and the
`G`-action on `S` extends to `L` (`IsFractionRing.mulSemiringAction`) fixing the
image of `K` pointwise — each element of `K` is a quotient of elements of `R`,
and `G` fixes `R` by `SMulCommClass G R S`.

Now let `x ∈ K` be integral over `R`.  Then its image `z ∈ L` is integral over
`S`, so `z = algebraMap S L s` for some `s ∈ S` because `S` is integrally
closed; `z` is `G`-fixed, hence so is `s`, hence `s` lies in the image of `R` by
`Algebra.IsInvariant`; and that preimage maps to `x` because `K → L` is
injective.  That is exactly the criterion `isIntegrallyClosed_iff`. -/
theorem isIntegrallyClosed_of_isInvariant (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsDomain R] [IsDomain S] [IsIntegrallyClosed S]
    (hinj : Function.Injective (algebraMap R S)) :
    IsIntegrallyClosed R := by
  letI := IsFractionRing.mulSemiringAction G S (FractionRing S)
  haveI := IsFractionRing.smulDistribClass G S (FractionRing S)
  haveI hRL : Function.Injective (algebraMap R (FractionRing S)) := by
    rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
    exact (IsFractionRing.injective S (FractionRing S)).comp hinj
  haveI : FaithfulSMul R (FractionRing S) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hRL
  letI := FractionRing.liftAlgebra R (FractionRing S)
  haveI := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have hKL : Function.Injective (algebraMap (FractionRing R) (FractionRing S)) :=
    (algebraMap (FractionRing R) (FractionRing S)).injective
  refine (isIntegrallyClosed_iff (FractionRing R)).mpr ?_
  intro x hx
  set z : FractionRing S := algebraMap (FractionRing R) (FractionRing S) x with hz
  have hzR : IsIntegral R z := hx.map (IsScalarTower.toAlgHom R (FractionRing R) (FractionRing S))
  have hzS : IsIntegral S z := hzR.tower_top
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzS
  have hfix : ∀ g : G, g • z = z := by
    intro g
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hmap : ∀ r : R, g • (algebraMap R (FractionRing S) r)
        = algebraMap R (FractionRing S) r := by
      intro r
      rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
      simp [← algebraMap.coe_smul', smul_algebraMap]
    rw [hz]
    rw [map_div₀, ← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
      ← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S)]
    rw [show g • (algebraMap R (FractionRing S) a / algebraMap R (FractionRing S) b)
        = (g • algebraMap R (FractionRing S) a) / (g • algebraMap R (FractionRing S) b) from
      map_div₀ (MulSemiringAction.toRingHom G (FractionRing S) g) _ _, hmap, hmap]
  have key : ∀ (g : G) (t : S), algebraMap S (FractionRing S) (g • t)
      = g • algebraMap S (FractionRing S) t := by
    intro g t
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      smul_distrib_smul, smul_one]
  have hsfix : ∀ g : G, g • s = s := by
    intro g
    apply IsFractionRing.injective S (FractionRing S)
    rw [key g s, hs, hfix g]
  obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := R) (B := S) (G := G) s hsfix
  refine ⟨y, ?_⟩
  apply hKL
  rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
    IsScalarTower.algebraMap_eq R S (FractionRing S)]
  simp only [RingHom.coe_comp, Function.comp_apply, hy, hs, hz]

/-! ### Krull dimension -/

/-- **A finite group quotient does not raise the dimension above one** (PROVEN).

A nonzero prime `p` of `R` lies under some prime `Q` of `S` (lying over, valid
because `S` is integral over `R` and `R → S` is injective), that `Q` is nonzero
because its contraction is, hence maximal since `dim S ≤ 1`, and the
contraction of a maximal ideal along an integral extension is maximal. -/
theorem dimensionLEOne_of_isInvariant (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsDomain S] [Ring.DimensionLEOne S]
    (hinj : Function.Injective (algebraMap R S)) :
    Ring.DimensionLEOne R := by
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  refine ⟨fun {p} hp0 hp => ?_⟩
  haveI := hp
  have hcomapbot : (⊥ : Ideal S).comap (algebraMap R S) = ⊥ := by
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun h => hinj (by simpa using h), fun h => by simp [h]⟩
  obtain ⟨Q, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (R := R) (S := S) p
      (by rw [RingHom.ker_eq_comap_bot, hcomapbot]; exact bot_le)
  haveI := hQ
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp0 (by rw [← hQc, hcomapbot])
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal hQ hQ0
  exact hQc ▸ Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := S) Q

/-- **The Krull dimension is unchanged** (PROVEN, in the only case needed).

`≤` is `dimensionLEOne_of_isInvariant`.  `≥` holds because contraction along an
integral extension is strictly monotone on primes
(`Ideal.IsIntegral.comap_lt_comap`), so it embeds a chain of `Spec S` into a
chain of `Spec R`. -/
theorem ringKrullDim_eq_one_of_isInvariant (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsDomain S] [Ring.DimensionLEOne S]
    (hinj : Function.Injective (algebraMap R S)) (hdim : ringKrullDim S = (1 : ℕ)) :
    ringKrullDim R = (1 : ℕ) := by
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  haveI := dimensionLEOne_of_isInvariant R S G hinj
  refine le_antisymm (Ring.krullDimLE_iff.mp inferInstance) ?_
  rw [← hdim]
  refine Order.krullDim_le_of_strictMono
    (fun Q : PrimeSpectrum S => (⟨Q.asIdeal.comap (algebraMap R S), inferInstance⟩ :
      PrimeSpectrum R)) ?_
  intro Q Q' h
  exact Ideal.IsIntegral.comap_lt_comap h

/-! ### The packaged conclusion -/

/-- **The invariants of a Dedekind domain of finite type over a field form a
Dedekind domain of finite type over that field** (PROVEN) — the assembly of the
three inputs above.

`IsNoetherianRing R` is not an extra input: it follows from
`Algebra.FiniteType k R` by the Hilbert basis theorem. -/
theorem isDedekindDomain_of_isInvariant (k R S : Type*) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsNoetherianRing k] [Algebra.FiniteType k S]
    [IsDedekindDomain S] (hinj : Function.Injective (algebraMap R S)) :
    IsDomain R ∧ IsDedekindDomain R ∧ Algebra.FiniteType k R := by
  haveI hdom : IsDomain R := Function.Injective.isDomain (algebraMap R S) hinj
  haveI hft : Algebra.FiniteType k R := finiteType_of_isInvariant k R S G hinj
  haveI hnoeth : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI hic : IsIntegrallyClosed R := isIntegrallyClosed_of_isInvariant R S G hinj
  haveI hd1 : Ring.DimensionLEOne R := dimensionLEOne_of_isInvariant R S G hinj
  haveI : IsDedekindRing R := { hnoeth, hd1, hic with }
  exact ⟨hdom, inferInstance, hft⟩

/-- **The coarse ring of a one-dimensional Dedekind presentation is a regular
finite-type domain of Krull dimension one** (PROVEN).

This is the exact package the modular-curve consumer
`isRegularRing_coarseRing_of_gamma0GITPresentation` asks for; `IsRegularRing`
comes from mathlib's instance `[IsDedekindDomain R] : IsRegularRing R`. -/
theorem isRegularRing_of_isInvariant (k R S : Type*) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] [IsNoetherianRing k] [Algebra.FiniteType k S]
    [IsDedekindDomain S] (hinj : Function.Injective (algebraMap R S))
    (hdim : ringKrullDim S = (1 : ℕ)) :
    IsDomain R ∧ IsRegularRing R ∧ Algebra.FiniteType k R ∧ ringKrullDim R = (1 : ℕ) := by
  obtain ⟨hdom, hded, hft⟩ := isDedekindDomain_of_isInvariant k R S G hinj
  haveI := hdom
  haveI := hded
  exact ⟨hdom, inferInstance, hft, ringKrullDim_eq_one_of_isInvariant R S G hinj hdim⟩

end Algebra.IsInvariant

/-! ### Regular field extensions and geometric integrality -/

/-- **The fraction field of a normal domain in which the base field is
algebraically closed is a regular extension** (sorry leaf).

`k` being algebraically closed *in `B`* is the same as `k` being algebraically
closed *in `Frac B`* when `B` is integrally closed — an element of `Frac B`
algebraic over the field `k` is integral over `k`, hence over `B`, hence lies in
`B` — and a field extension `L/k` with `k` algebraically closed in `L` is
**regular** as soon as `L/k` is separable, i.e. `L ⊗[k] K` is a domain for every
field extension `K/k`.  Over a PERFECT `k` separability is automatic (Stacks
030W), which is why that is the hypothesis carried here.  Bourbaki *Algebra*
V §17, EGA IV 4.6.1, Stacks 04KM.

Together with `isDomain_tensorProduct_of_injective` below this is exactly
"geometrically integral", which is what an affine geometric-connectedness
criterion needs.

**What blocks it in the pin, checked 2026-07-27.**  Mathlib has the linear
disjointness theory (`Mathlib/FieldTheory/LinearDisjoint.lean`, in particular
`IntermediateField.LinearDisjoint.isDomain`,
`IntermediateField.LinearDisjoint.isDomain'` and
`Algebra.TensorProduct.isField_of_isAlgebraic`) but **no notion of a regular or
primary field extension** and no statement of this criterion; `algebraicClosure`
(`Mathlib/FieldTheory/AlgebraicClosure.lean`) is developed only as an
intermediate field, with nothing relating it to base change.  *The checks that
would refute this*:
`grep -rn "IsPrimaryExtension\|IsRegularExtension" .lake/packages/mathlib/Mathlib/`
returning anything, or a lemma whose conclusion is `IsDomain (L ⊗[k] K)` and
whose hypothesis mentions `algebraicClosure`.

**The classical proof, for whoever closes it.**  Reduce to `K/k` algebraic:
choose a transcendence basis `(tᵢ)` of `K/k`; then `L ⊗[k] k(t) = L(t)` is a
domain (a localization of a polynomial ring over the domain `L`), `k(t)` is
algebraically closed in `L(t)` because `k` is in `L`, and `K/k(t)` is algebraic.
For `K/k` algebraic, `k` is perfect, so it is enough to treat `K/k` finite
Galois, where `L ⊗[k] K` is a *field* exactly because `L ∩ K = k` inside a
common overfield — and that last step is precisely what mathlib's
`IntermediateField.LinearDisjoint` API provides.

The `k`-algebra structure on `FractionRing B` is the one mathlib already
supplies for a localization, and it is compatible with `Algebra k B` by the
ambient `IsScalarTower k B (FractionRing B)` instance, so it is not a choice.

**Faithfulness note — what is load-bearing is PERFECTION, not characteristic
zero** (corrected 2026-07-28; the hypothesis read `CharZero k` until then, and
this note read "`CharZero k` is load-bearing").  The statement is FALSE over an
IMPERFECT base: for `k = 𝔽_p(u)`, `B = L = k(u^{1/p})`, `K = L`, the base field
`k` *is* algebraically closed in nothing bigger inside `L` in the separable
sense, yet `L ⊗[k] L` contains the nonzero nilpotent
`u^{1/p} ⊗ 1 - 1 ⊗ u^{1/p}` and is not a domain.  That counterexample is exactly
a failure of perfection — `u` has no `p`-th root in `k` — and says nothing
against characteristic `p` per se.  `PerfectField k` is therefore the right
hypothesis, it is strictly weaker than `CharZero k`
(`PerfectField.ofCharZero` is an instance, so every existing `ℚ`-call site is
undisturbed), and it is what the recorded proof sketch above already uses
("`k` is perfect, so it is enough to treat `K/k` finite Galois").

The weakening is not cosmetic: `Fermat.geometricallyConnected_of_gamma0AtlasOver_zmod`
and `Fermat.isDomain_of_gamma0AtlasOver_zmod` consume this leaf at `k = ZMod p`,
which is perfect (`PerfectField.ofFinite`) and emphatically not `CharZero`. -/
theorem isDomain_fractionRing_tensorProduct_of_isAlgebraic_mem_bot
    (k B : Type*) [Field k] [PerfectField k] [CommRing B] [IsDomain B] [Algebra k B]
    [IsIntegrallyClosed B]
    (h : ∀ x : B, IsAlgebraic k x → x ∈ (⊥ : Subalgebra k B))
    (K : Type*) [Field K] [Algebra k K] :
    IsDomain (FractionRing B ⊗[k] K) :=
  sorry

/-- **Geometric integrality descends from the fraction field to the ring**
(PROVEN).

If `B` is a `k`-algebra which embeds in a `k`-algebra `L` and `L ⊗[k] K` is a
domain, then so is `B ⊗[k] K`: over a field every module is flat, so
`B ⊗[k] K → L ⊗[k] K` is injective, and a subring of a domain is a domain. -/
theorem isDomain_tensorProduct_of_injective
    (k B L K : Type*) [Field k] [CommRing B] [CommRing L] [CommRing K]
    [Algebra k B] [Algebra k L] [Algebra k K]
    (f : B →ₐ[k] L) (hf : Function.Injective f) [IsDomain (L ⊗[k] K)] :
    IsDomain (B ⊗[k] K) := by
  have hcoe : ∀ x : B ⊗[k] K, Algebra.TensorProduct.map f (AlgHom.id k K) x
      = LinearMap.rTensor K f.toLinearMap x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => simp
    | add x y hx hy => simp [map_add, hx, hy]
  have hrt : Function.Injective (LinearMap.rTensor K f.toLinearMap) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hf
  have hinj : Function.Injective (Algebra.TensorProduct.map f (AlgHom.id k K)) := by
    intro x y hxy
    refine hrt ?_
    rw [← hcoe x, ← hcoe y]
    exact hxy
  exact Function.Injective.isDomain
    (Algebra.TensorProduct.map f (AlgHom.id k K)).toRingHom hinj

/-- **A normal domain in which the base field is algebraically closed is
geometrically integral** (PROVEN over
`isDomain_fractionRing_tensorProduct_of_isAlgebraic_mem_bot`).

`B ⊗[k] K` embeds into `Frac B ⊗[k] K` because `K` is flat over the field `k`,
and the latter is a domain by the leaf.  This is the form the affine
geometric-connectedness criterion
`AlgebraicGeometry.geometricallyConnected_specMap_algebraMap_of_forall_isDomain`
consumes.

`PerfectField k` rather than `CharZero k` since 2026-07-28 — see the
faithfulness note on the leaf above. -/
theorem isDomain_tensorProduct_of_isAlgebraic_mem_bot
    (k B : Type*) [Field k] [PerfectField k] [CommRing B] [IsDomain B] [Algebra k B]
    [IsIntegrallyClosed B]
    (h : ∀ x : B, IsAlgebraic k x → x ∈ (⊥ : Subalgebra k B))
    (K : Type*) [Field K] [Algebra k K] :
    IsDomain (B ⊗[k] K) := by
  haveI : IsDomain (FractionRing B ⊗[k] K) :=
    isDomain_fractionRing_tensorProduct_of_isAlgebraic_mem_bot k B h K
  exact isDomain_tensorProduct_of_injective k B (FractionRing B) K
    (IsScalarTower.toAlgHom k B (FractionRing B)) (IsFractionRing.injective B (FractionRing B))

end
