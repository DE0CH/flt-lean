/-
Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean — own work
for the Fermat project (not vendored from the FLT project).

# Sufficient criteria for `GeometricallyConnected` and `SmoothOfRelativeDimension`

Mathlib's `Geometrically/*` files and `Morphisms/Smooth.lean` are, at the pin,
**purely consequential**: every lemma about `GeometricallyConnected` and about
`SmoothOfRelativeDimension` either *uses* the class or transports it (base
change, restriction, fibres, composition).  Neither file contains a single way
to *construct* one from ring-theoretic data.  That was checked on 2026-07-27:

    grep -rln "GeometricallyConnected"  .lake/packages/mathlib/Mathlib/
      -- one file: AlgebraicGeometry/Geometrically/Connected.lean
    grep -rn  "SmoothOfRelativeDimension" .lake/packages/mathlib/Mathlib/
      -- one file: AlgebraicGeometry/Morphisms/Smooth.lean, no dimension theory

*The check that would refute either claim*: the same two greps returning a
second file.

This module supplies the missing constructors for the **affine over a field**
case, which is the only case this development needs, and states them about a
ring so that a consumer can discharge them by commutative algebra.

## Contents

* `geometricallyConnected_of_geometricallyIrreducible` — the missing
  `GeometricallyIrreducible ⟹ GeometricallyConnected` implication (PROVEN).
* `geometricallyConnected_specMap_algebraMap_of_forall_connectedSpace` — for an
  affine `Spec B ⟶ Spec R`, geometric connectedness is exactly connectedness of
  `Spec (B ⊗[R] K)` for every field extension `K/R` (PROVEN, via
  `pullbackSpecIso`).
* `geometricallyConnected_specMap_algebraMap_of_forall_isDomain` — the usable
  corollary: `B ⊗[R] K` a domain for every field `K` over `R` suffices, because
  the spectrum of a domain is irreducible (PROVEN).
* `smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing` — *regular +
  finite type over a perfect field ⟹ smooth*, with the relative dimension read
  off the Krull dimension.  **PROVEN 2026-07-27** over the two leaves below; see
  its docstring for the assembly.
* `Ideal.injective_lTensor_inclusion_of_isRegularLocalRing` — a regular quotient
  of a regular local ring has `κ ⊗ I ↪ κ ⊗ 𝔪`, i.e. `I` is a complete
  intersection (LEAF, and after the reduction below it is the ENTIRE remaining
  content of Stacks `056S` here: pure local commutative algebra, no fields, no
  perfectness, no Kähler differentials).
* `Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField` — the local
  form of Stacks `056S`: a regular local ring essentially of finite type over a
  perfect field is formally smooth over it.  **PROVEN 2026-07-28** over the leaf
  above; see its docstring for the reduction.
* `Algebra.FormallySmooth.of_isRegularRing_of_perfectField` — the global
  consequence, PROVEN from the theorem above by `Algebra.smoothLocus_eq_univ_iff`.
* `Algebra.FormallySmooth.of_isDiscreteValuationRing_of_perfectField` — the
  DVR form, PROVEN as a one-line corollary (a DVR is a regular local ring of
  dimension one).  It is what
  `CurveExtension.lean`'s `formallySmooth_of_isDiscreteValuationRing_of_perfectField`
  and `CurveCompactification.lean`'s `smoothOfRelativeDimension_one_fromNormalization`
  want, and it is stated here so that it is proven ONCE.
* `Algebra.rank_kaehlerDifferential_eq_trdeg_of_perfectField` — for a finitely
  generated field extension `L/K` with `K` perfect,
  `rank_L Ω[L⁄K] = trdeg K L` (PROVEN 2026-07-27; mathlib has neither this nor
  any other computation of the rank of a module of Kähler differentials of a
  field extension).
* `ringKrullDim_eq_of_isIntegral_of_injective` — an injective integral ring
  extension preserves the Krull dimension, Stacks `00OJ`+`00OK` (LEAF).
* `Algebra.trdeg_fractionRing_eq_of_ringKrullDim` — *dimension equals
  transcendence degree* for a finite-type domain over a field, PROVEN from the
  leaf above by Noether normalisation.
* `Algebra.rank_kaehlerDifferential_eq_of_ringKrullDim` — the combination,
  PROVEN from the two above.

## Why the connectedness criterion has to go through the function field

The cheap classical criterion — connected plus a rational point, EGA IV 4.5.13 —
is **mathematically** unavailable in the intended application: the consumer is
`Y_0(N)`, whose set of `ℚ`-points is empty for most `N`, and proving that
emptiness is the whole point of `Fermat/FLT/ModularCurve/X0.lean`.  So the
criterion offered here is the tensor-product one, which is the algebraic form of
"`R` is algebraically closed in `Frac B`".
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct CommRingCat

/-! ### Commutative-algebra input: regularity, smoothness, and the rank of `Ω`

The two `sorry` leaves of this file both live here, in ring-theoretic form.  The
scheme-level statement at the end of the file is then *assembled* from them with
no further mathematical content.
-/

open IsLocalRing in
/-- **THE CONORMAL MODULE OF A REGULAR QUOTIENT OF A REGULAR LOCAL RING INJECTS INTO THE
COTANGENT SPACE** (sorry leaf, opened 2026-07-28).

Let `P` be a regular local ring with maximal ideal `𝔪`, let `I ≤ 𝔪` be an ideal such that
`P ⧸ I` is again a regular local ring, and let `κ` be a field receiving `P` surjectively —
for a local ring that forces `κ ≅ P ⧸ 𝔪`, and the hypothesis is stated this way only so a
caller may hand over whatever presentation of the residue field it happens to hold.  Then

    κ ⊗[P] I  ⟶  κ ⊗[P] 𝔪

is injective.  Unwinding the two sides by Nakayama this reads `I / 𝔪I ↪ 𝔪 / 𝔪²`, i.e.

    I ⊓ 𝔪 ^ 2  ≤  𝔪 * I,

which is the classical statement that a regular quotient of a regular local ring is a
COMPLETE INTERSECTION: `I` is generated by `dim P - dim (P ⧸ I)` elements, forming part of
a regular system of parameters (Stacks `00NQ`, Matsumura §21).

**This is the whole of Stacks `056S` that is left in this development.**  The reduction is
on `Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField` below; note what it
achieves — the leaf carries no field, no perfectness and no Kähler differentials, because
perfectness was consumed once and for all by the residue field being formally smooth.

## The classical proof, and what it needs that the pin does not have

Write `D = dim P` and `d = dim (P ⧸ I)`.  Regularity of `P ⧸ I` says
`dim_κ 𝔪/(I + 𝔪²) = d`, so the image of `I` in `𝔪/𝔪²` has dimension `D - d`.  Pick
`f₁, …, f_{D-d} ∈ I` whose classes are a basis of that image and put
`I' = (f₁, …, f_{D-d}) ≤ I`.  Then

1. `P ⧸ I'` has `dim_κ 𝔪/(I' + 𝔪²) = d`, so `ringKrullDim (P ⧸ I') ≤ d` by
   `ringKrullDim_le_spanFinrank_maximalIdeal`; and `ringKrullDim (P ⧸ I') ≥ d` because
   `P ⧸ I' ↠ P ⧸ I`.  So `P ⧸ I'` is a regular local ring of dimension `d`.
2. A regular local ring is a DOMAIN.  **Not in the pin** — `grep -rn "IsDomain"
   Mathlib/RingTheory/RegularLocalRing/` is empty — but it IS in this project, sorry-free,
   as `GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing`
   (`Fermat/FLT/Modularity/RegularStalks.lean`).  A prover should HOIST it to a
   `Fermat/FLT/Mathlib/` module rather than reprove it; importing `Modularity` from this
   shim directory would be a cycle.
3. In a Noetherian local domain `R`, `ringKrullDim (R ⧸ J) < ringKrullDim R` whenever
   `J ≠ ⊥`: every minimal prime `𝔭` over `J` has `ht 𝔭 ≥ 1` (as `(0)` is prime and does
   not contain `J`), and `dim (R ⧸ 𝔭) + ht 𝔭 ≤ dim R` always.  Applied to `R = P ⧸ I'`
   and `J = I ⧸ I'` — whose quotient is `P ⧸ I`, of dimension `d = dim R` — this forces
   `I = I'`, hence `spanFinrank I ≤ D - d`.
4. `dim_κ (κ ⊗[P] I) = spanFinrank I ≤ D - d` is exactly the dimension of the image, so
   the surjection `κ ⊗[P] I ↠ (I + 𝔪²)/𝔪²` is an isomorphism and the displayed map is
   injective.

*The check that would refute the two "not in the pin" claims*: `grep -rn "IsDomain"` over
`Mathlib/RingTheory/RegularLocalRing/` returning anything, or a general
`Module.finrank κ (κ ⊗[P] M) = Submodule.spanFinrank M` for a finite module over a local
ring turning up in `Mathlib/RingTheory/Ideal/Cotangent.lean` or
`Mathlib/Algebra/Module/SpanRankOperations.lean`.

## Faithfulness

`IsRegularLocalRing (P ⧸ I)` is load-bearing and the statement is FALSE without it: take
`P = k[x]_{(x)}` and `I = (x²)`.  Then `P ⧸ I` is local artinian with
`dim_κ 𝔪/𝔪² = 1 ≠ 0 = ringKrullDim`, so not regular; `κ ⊗[P] I = (x²)/(x³)` is
one-dimensional, while `I ≤ 𝔪²` sends all of it to `0` in `𝔪/𝔪²`.  So the map is the zero
map on a nonzero space.

`IsRegularLocalRing P` enters only through `dim_κ 𝔪/𝔪² = dim P` in step 1.  No
counterexample to dropping it has been produced here, so a prover who finds the argument
goes through without it should say so rather than assume it is needed. -/
theorem Ideal.injective_lTensor_inclusion_of_isRegularLocalRing
    {P : Type*} [CommRing P] [IsRegularLocalRing P] {I J : Ideal P}
    (hIJ : I ≤ J) (hJ : J = maximalIdeal P) [IsRegularLocalRing (P ⧸ I)]
    {κ : Type*} [Field κ] [Algebra P κ] (hκ : Function.Surjective (algebraMap P κ)) :
    Function.Injective (LinearMap.lTensor κ (Submodule.inclusion hIJ)) :=
  sorry

namespace Algebra

open IsLocalRing KaehlerDifferential in
/-- **A regular local ring essentially of finite type over a perfect field is
formally smooth over it** — the local form of Stacks `056S` ("regular is
equivalent to smooth over a perfect field"), Matsumura *Commutative Ring Theory*
§28.  **PROVEN 2026-07-28** over the single leaf
`Ideal.injective_lTensor_inclusion_of_isRegularLocalRing` above.

## The reduction, which is what this proof contributes

The obvious route — apply the local Jacobian criterion
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange` to a presentation
`0 → I → P → A → 0` and count dimensions of Kähler differentials — needs `dim P`,
`rank Ω[κ⁄K] = trdeg K κ`, and the dimension formula `n = dim P + trdeg K κ` for a
prime of a polynomial ring, i.e. the catenary property.  **None of that is needed.**

Take `P = (K[X₁,…,X_n])_𝔮`, the localization of a polynomial ring at the
contraction `𝔮` of `𝔪_A`; `Algebra.EssFiniteType K A` gives a finite-type
subalgebra of which `A` is a localization, and `A` being LOCAL makes `P ↠ A`
surjective (every element outside `𝔮` maps to a unit).  Now apply the SAME Jacobian
criterion twice with the SAME `P`:

* to `S = A`, giving `FormallySmooth K A ↔ κ ⊗[P] I → κ ⊗[P] Ω[P⁄K]` injective;
* to `S = κ`, the residue field itself, giving
  `FormallySmooth K κ ↔ κ ⊗[P] 𝔪_P → κ ⊗[P] Ω[P⁄K]` injective.

The second is **known**: `κ` is essentially of finite type over `K` and `K` is
PERFECT, so `Algebra.FormallySmooth.of_perfectField` applies.  And by
`KaehlerDifferential.cotangentComplexBaseChange_tmul` the two maps are given by the
same formula `a ⊗ b ↦ a • (1 ⊗ d b)`, so the first FACTORS through the second along
`κ ⊗[P] I → κ ⊗[P] 𝔪_P` induced by `I ≤ 𝔪_P`.  Injectivity of that inclusion map is
therefore all that remains — and it mentions neither `K`, nor perfectness, nor `Ω`.

**So `PerfectField K` is consumed exactly once, and exactly where the mathematics
says it must be.**  At the quasi-elliptic witness (`y² = x³ + t` over `𝔽₃(t)`, at the
point with residue field `k(t^{1/3})`) the residue field is purely inseparable over
`k`, `κ` is *not* formally smooth over `k`, the second application above fails, and
the conclusion is false even though the ring is a DVR.  That is the mechanism a
prover must defeat, and here it is defeated by hypothesis rather than by hand.

## Faithfulness

Both hypotheses are load-bearing.  `EssFiniteType K A` cannot be dropped (formal
smoothness of a general regular local `K`-algebra is false — a complete local ring
such as `K⟦t⟧` is regular but not formally smooth over `K` for the discrete
topology), and `PerfectField K` cannot be dropped (the quasi-elliptic witness
above; a fuller account is on
`CurveExtension.lean`'s `formallySmooth_of_isDiscreteValuationRing_of_perfectField`). -/
theorem FormallySmooth.of_isRegularLocalRing_of_perfectField
    (K A : Type u) [Field K] [PerfectField K] [CommRing A] [Algebra K A]
    [Algebra.EssFiniteType K A] [IsRegularLocalRing A] :
    Algebra.FormallySmooth K A := by
  classical
  -- Present `A` as a localization of a polynomial ring at a prime.  `EssFiniteType` gives a
  -- finite-type subalgebra `B ⊆ A` of which `A` is a localization; choose a surjection
  -- `K[X₁,…,X_n] ↠ B` and let `𝔮` be the contraction of `𝔪_A` along the composite `g`.
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K (Algebra.EssFiniteType.subalgebra K A))
  set g : MvPolynomial (Fin n) K →ₐ[K] A :=
    (IsScalarTower.toAlgHom K (Algebra.EssFiniteType.subalgebra K A) A).comp f₀ with hg
  set 𝔮 : Ideal (MvPolynomial (Fin n) K) := (maximalIdeal A).comap g with h𝔮
  haveI : 𝔮.IsPrime := Ideal.comap_isPrime (f := g.toRingHom) _
  have hunit : ∀ y : 𝔮.primeCompl, IsUnit (g y) := fun y ↦
    IsLocalRing.notMem_maximalIdeal.mp (show (y : MvPolynomial (Fin n) K) ∉ 𝔮 from y.2)
  letI : Algebra (Localization.AtPrime 𝔮) A :=
    (IsLocalization.lift (M := 𝔮.primeCompl) (g := g.toRingHom) hunit).toAlgebra
  have hmapPA : (algebraMap (Localization.AtPrime 𝔮) A) =
      IsLocalization.lift (M := 𝔮.primeCompl) (g := g.toRingHom) hunit := rfl
  haveI : IsScalarTower K (Localization.AtPrime 𝔮) A := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) (Localization.AtPrime 𝔮),
      hmapPA, IsLocalization.lift_eq]
    simp
  -- `P := (K[X₁,…,X_n])_𝔮` surjects onto `A`: `A` is generated over the image of `B` by
  -- inverses of elements that are units in `A`, and — `A` being local — those are exactly
  -- the elements outside `𝔮`.
  have h₁ : Function.Surjective (algebraMap (Localization.AtPrime 𝔮) A) := by
    intro a
    obtain ⟨b, m, rfl⟩ := IsLocalization.exists_mk'_eq (Algebra.EssFiniteType.submonoid K A) a
    obtain ⟨x, rfl⟩ := hf₀ b
    obtain ⟨y, hy⟩ := hf₀ (m : Algebra.EssFiniteType.subalgebra K A)
    have hmu : IsUnit (g y) := by
      rw [hg]; simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hy]; exact m.2
    have hy𝔮 : y ∈ 𝔮.primeCompl := IsLocalRing.notMem_maximalIdeal.mpr hmu
    refine ⟨IsLocalization.mk' (Localization.AtPrime 𝔮) x ⟨y, hy𝔮⟩, ?_⟩
    rw [hmapPA, IsLocalization.lift_mk'_spec]
    have e1 : g.toRingHom (y : MvPolynomial (Fin n) K)
        = algebraMap (Algebra.EssFiniteType.subalgebra K A) A m := by simp [hg, hy]
    have e2 : g.toRingHom x = algebraMap (Algebra.EssFiniteType.subalgebra K A) A (f₀ x) := by
      simp [hg]
    rw [e1, e2, mul_comm, IsLocalization.mk'_spec]
  have h₂ : (RingHom.ker (algebraMap (Localization.AtPrime 𝔮) A)).FG := IsNoetherian.noetherian _
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin n) K) (Localization.AtPrime 𝔮) :=
    Algebra.FormallyEtale.of_isLocalization 𝔮.primeCompl
  haveI : Algebra.FormallySmooth K (Localization.AtPrime 𝔮) := .comp _ (MvPolynomial (Fin n) K) _
  haveI : Module.Free (Localization.AtPrime 𝔮) Ω[Localization.AtPrime 𝔮⁄K] :=
    .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
      (MvPolynomial (Fin n) K) (Localization.AtPrime 𝔮))
  haveI : Module.Finite (Localization.AtPrime 𝔮) Ω[Localization.AtPrime 𝔮⁄K] := inferInstance
  -- The residue field `κ` of `A` is also the residue field of `P`, and it is formally smooth
  -- over `K` because `K` is PERFECT.  This is the only place perfectness is used.
  haveI : Algebra.EssFiniteType K (ResidueField A) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom K A (ResidueField A))
      IsLocalRing.residue_surjective
  letI : Algebra (Localization.AtPrime 𝔮) (ResidueField A) :=
    ((algebraMap A (ResidueField A)).comp (algebraMap (Localization.AtPrime 𝔮) A)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime 𝔮) A (ResidueField A) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (Localization.AtPrime 𝔮) (ResidueField A) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply K A (ResidueField A),
        IsScalarTower.algebraMap_apply K (Localization.AtPrime 𝔮) A,
        IsScalarTower.algebraMap_apply (Localization.AtPrime 𝔮) A (ResidueField A)]
  have hsurjκ : Function.Surjective (algebraMap (Localization.AtPrime 𝔮) (ResidueField A)) :=
    IsLocalRing.residue_surjective.comp h₁
  have h₂κ : (RingHom.ker (algebraMap (Localization.AtPrime 𝔮) (ResidueField A))).FG :=
    IsNoetherian.noetherian _
  have hJ : RingHom.ker (algebraMap (Localization.AtPrime 𝔮) (ResidueField A))
      = maximalIdeal (Localization.AtPrime 𝔮) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurjκ)
  have hIJ : RingHom.ker (algebraMap (Localization.AtPrime 𝔮) A)
      ≤ RingHom.ker (algebraMap (Localization.AtPrime 𝔮) (ResidueField A)) := by
    intro x hx
    simp only [RingHom.mem_ker] at hx ⊢
    rw [IsScalarTower.algebraMap_apply (Localization.AtPrime 𝔮) A (ResidueField A), hx, map_zero]
  -- The Jacobian criterion applied to `κ` ITSELF: `κ ⊗ 𝔪_P → κ ⊗ Ω[P⁄K]` is injective.
  have hψ : Function.Injective (KaehlerDifferential.cotangentComplexBaseChange K
      (ResidueField A) (Localization.AtPrime 𝔮) (ResidueField A)) := by
    refine (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange
      (R := K) (S := ResidueField A) (Localization.AtPrime 𝔮) (ResidueField A)
      hsurjκ h₂κ ?_).mp inferInstance
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact bot_le
  -- The Jacobian criterion applied to `A`.
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange
    (R := K) (S := A) (Localization.AtPrime 𝔮) (ResidueField A) h₁ h₂
    (le_of_eq (Ideal.mk_ker).symm)]
  haveI : IsRegularLocalRing
      ((Localization.AtPrime 𝔮) ⧸ RingHom.ker (algebraMap (Localization.AtPrime 𝔮) A)) :=
    IsRegularLocalRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective h₁).symm
  have hι := Ideal.injective_lTensor_inclusion_of_isRegularLocalRing
    (P := Localization.AtPrime 𝔮) hIJ hJ hsurjκ
  -- The two criteria are the same map, the first precomposed with `κ ⊗ I → κ ⊗ 𝔪_P`.
  have hcompL :
      ((KaehlerDifferential.cotangentComplexBaseChange K (ResidueField A)
          (Localization.AtPrime 𝔮) (ResidueField A)).restrictScalars
            (Localization.AtPrime 𝔮)).comp
        (LinearMap.lTensor (ResidueField A) (Submodule.inclusion hIJ))
      = (KaehlerDifferential.cotangentComplexBaseChange K A
          (Localization.AtPrime 𝔮) (ResidueField A)).restrictScalars
            (Localization.AtPrime 𝔮) :=
    _root_.TensorProduct.ext' fun a b ↦ rfl
  intro x y hxy
  refine hι (hψ ?_)
  exact (LinearMap.congr_fun hcompL x).trans (hxy.trans (LinearMap.congr_fun hcompL y).symm)

/-- **A regular ring of finite type over a perfect field is formally smooth over
it** (PROVEN 2026-07-27 over `FormallySmooth.of_isRegularLocalRing_of_perfectField`).

`Algebra.smoothLocus_eq_univ_iff` turns formal smoothness of `B` into formal
smoothness of every `Bₚ`, and `IsRegularRing` is *defined* as regularity of every
`Bₚ`, so the two match up point by point.  The only work is producing
`EssFiniteType K Bₚ`, which is `EssFiniteType.of_isLocalization` composed with
`EssFiniteType K B`. -/
theorem FormallySmooth.of_isRegularRing_of_perfectField
    (K B : Type u) [Field K] [PerfectField K] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B] [IsRegularRing B] :
    Algebra.FormallySmooth K B := by
  haveI : Algebra.FinitePresentation K B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [← Algebra.smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro p
  show Algebra.FormallySmooth K (Localization.AtPrime p.asIdeal)
  haveI : Algebra.EssFiniteType B (Localization.AtPrime p.asIdeal) :=
    .of_isLocalization _ p.asIdeal.primeCompl
  haveI : Algebra.EssFiniteType K (Localization.AtPrime p.asIdeal) := .comp _ B _
  exact FormallySmooth.of_isRegularLocalRing_of_perfectField K _

/-- **A DISCRETE VALUATION RING ESSENTIALLY OF FINITE TYPE OVER A PERFECT FIELD IS FORMALLY
SMOOTH** (PROVEN 2026-07-28, a one-line corollary of
`FormallySmooth.of_isRegularLocalRing_of_perfectField`).

A DVR is exactly a regular local ring of dimension one, and at this pin that implication is
free: `IsDiscreteValuationRing` gives `IsLocalRing` and `IsPrincipalIdealRing`, and mathlib's
`instance [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] : IsRegularLocalRing R`
(`Mathlib/RingTheory/RegularLocalRing/Defs.lean`) fires.  So there is nothing here beyond the
regular-local theorem, which is exactly why this statement is proven ONCE, here, rather than
separately in each consumer.

Known consumers, all of which state this as their own leaf:
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`'s
`formallySmooth_of_isDiscreteValuationRing_of_perfectField`, and through it
`smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk`;
`CurveCompactification.lean`'s `smoothOfRelativeDimension_one_fromNormalization`;
`ModularCurve/X0.lean`'s `smoothOfRelativeDimension_of_gamma0GITPresentation`.

`PerfectField K` is load-bearing: over `k = 𝔽₃(t)` the quasi-elliptic curve `y² = x³ + t`
has, at its unique Jacobian-degenerate point, a local ring that is a DVR essentially of
finite type over `k` and is NOT formally smooth over `k` — the residue field `k(t^{1/3})` is
purely inseparable over `k`, so it is not itself formally smooth over `k` and the reduction
in the regular-local theorem breaks at exactly that step. -/
theorem FormallySmooth.of_isDiscreteValuationRing_of_perfectField
    (K R : Type u) [Field K] [PerfectField K] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra K R] [Algebra.EssFiniteType K R] :
    Algebra.FormallySmooth K R :=
  FormallySmooth.of_isRegularLocalRing_of_perfectField K R

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- **The rank of the module of Kähler differentials of a finitely generated field
extension of a perfect field is its transcendence degree** (PROVEN 2026-07-27).

Mathlib computes `Ω` for a polynomial ring (`KaehlerDifferential.mvPolynomialBasis`)
and has the whole separably-generated theory
(`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`), but nowhere
connects them: `grep -rn "trdeg" Mathlib/RingTheory/Kaehler/` is empty at this pin,
and so is the reverse grep for `Ω[` over `Mathlib/FieldTheory/`.

The proof is a chain of three base changes along formally étale maps, each of
which multiplies the rank by nothing:

    K[s]  ⟶  Algebra.adjoin K s  ⟶  IntermediateField.adjoin K s  ⟶  L
          ≃                     localization                  separable algebraic

`KaehlerDifferential.isBaseChange_of_formallyEtale` turns each arrow into a base
change of `Ω`, and `IsBaseChange.rank_eq` — which needs only that the target has no
zero divisors and receives the source faithfully — reads the rank back unchanged.
The left-hand end is `KaehlerDifferential.mvPolynomialBasis`, of rank `#s`; the
right-hand end is `Ω[L⁄K]`; and `#s = trdeg K L` because `s` is a transcendence
basis.

`PerfectField K` is load-bearing and is used exactly once, to produce a
*separating* transcendence basis: over an imperfect field the third arrow can fail
to be separable and the rank strictly exceeds the transcendence degree (e.g.
`L = K(t^{1/p})` over `K = 𝔽_p(t)`, where `trdeg = 0` but `Ω[L⁄K]` is
one-dimensional). -/
theorem rank_kaehlerDifferential_eq_trdeg_of_perfectField
    (K L : Type u) [Field K] [PerfectField K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Module.rank L Ω[L⁄K] = Algebra.trdeg K L := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  have hrange : Set.range (Subtype.val : {x // x ∈ s} → L) = (s : Set L) := Subtype.range_coe
  set P := MvPolynomial {x // x ∈ s} K with hP
  set A := Algebra.adjoin K (s : Set L) with hA
  set E := IntermediateField.adjoin K (s : Set L) with hE
  -- `L` is formally étale over `E`, because `L/E` is separable algebraic.
  haveI : Algebra.FormallyEtale E L := Algebra.FormallyEtale.of_isSeparable E L
  haveI : FaithfulSMul E L :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap E L).injective
  have h1 : Module.rank L Ω[L⁄K] = Module.rank E Ω[E⁄K] :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale K E L).rank_eq
  -- `E` is the fraction field of `A`, hence formally étale over it.
  haveI : Algebra.FormallyEtale A E := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  haveI : FaithfulSMul A E :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective E le_rfl)
  have h2 : Module.rank E Ω[E⁄K] = Module.rank A Ω[A⁄K] :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale K A E).rank_eq
  -- `A` is a polynomial ring on the transcendence basis.
  have hAeq : Algebra.adjoin K (Set.range (Subtype.val : {x // x ∈ s} → L)) = A := by
    rw [hrange]
  let e : P ≃ₐ[K] A := hs.1.aevalEquiv.trans (Subalgebra.equivOfEq _ _ hAeq)
  letI : Algebra P A := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
  haveI : Algebra.FormallyEtale P A :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ ↦ rfl)
  haveI : FaithfulSMul P A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr e.injective
  have h3 : Module.rank A Ω[A⁄K] = Module.rank P Ω[P⁄K] :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale K P A).rank_eq
  have h4 : Module.rank P Ω[P⁄K] = Cardinal.mk {x // x ∈ s} :=
    (KaehlerDifferential.mvPolynomialBasis K {x // x ∈ s}).mk_eq_rank''.symm
  have h5 : Cardinal.mk {x // x ∈ s} = Algebra.trdeg K L := by
    simpa using hs.lift_cardinalMk_eq_trdeg
  rw [h1, h2, h3, h4, h5]

end Algebra

/-- **An injective integral ring extension preserves the Krull dimension**
(sorry leaf, opened 2026-07-27).

Stacks `00OK` (`dim S ≤ dim R`, by incomparability) together with `00OJ`
(`dim R ≤ dim S`, by lying over and going up).  This is the only gap left in the
dimension half of this file, and it is stated in full mathlib generality rather
than for the finite-type case that needs it, because that is what it is.

## What the pin has, checked 2026-07-27

Both halves of the argument are present as statements about a *single* prime; only
the passage to chains is missing.

* Incomparability: `Ideal.IsIntegral.comap_lt_comap` — for `I < J` primes of `S`,
  `comap I < comap J`.  So `PrimeSpectrum.comap (algebraMap R S)` is strictly
  monotone and `Order.krullDim_le_of_strictMono` gives `dim S ≤ dim R` directly.
* Lying over and going up: `Ideal.exists_ideal_over_prime_of_isIntegral` and
  `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime` (the latter takes a
  prime `I` of `S` with `comap I ≤ P` and produces `Q ≥ I` over `P`).  Turning a
  chain `p₀ < ⋯ < p_n` of `R` into a chain of `S` is an induction on the chain
  using the second, i.e. an `RelSeries`/`LTSeries` induction; that induction is the
  work, and **mathlib says so itself** — the comment above
  `exists_ideal_over_prime_of_isIntegral_of_isPrime` reads *"TODO: Version of
  going-up theorem with arbitrary length chains (by induction on this)?  Not sure
  how best to write an ascending chain in Lean"*.

A dead end worth recording so it is not re-explored: the `≥` direction does **not**
follow from `Order.krullDim_le_of_strictComono_and_surj` even though
`Algebra.IsIntegral.comap_surjective` supplies its surjectivity hypothesis, because
`PrimeSpectrum.comap` is not strictly comonotone.  Counterexample: `R = k[x]`,
`S = k[x] × k[x]`, `q₁ = 0 × k[x]`, `q₂ = k[x] × (x)`; then
`comap q₁ = (0) < (x) = comap q₂` while `q₁ ⊄ q₂` (as `(0,1) ∈ q₁ \ q₂`).  So the
lifted chain really has to be built step by step, each prime chosen above the
previous one.

*The check that would refute this*: `grep -rn "krullDim" Mathlib/RingTheory/Ideal/GoingUp.lean`
or `grep -rn "IsIntegral" Mathlib/RingTheory/KrullDimension/` returning anything —
both are empty at this pin.

## Faithfulness

Injectivity is load-bearing on both sides: without it take `R` any ring and
`S = 0`, which is integral over `R` with `ringKrullDim S = ⊥ ≠ ringKrullDim R`. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (h : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R :=
  sorry

namespace Algebra

/-- **Krull dimension equals transcendence degree for a finite-type domain over a
field** (PROVEN 2026-07-27 over `ringKrullDim_eq_of_isIntegral_of_injective`).

This is the fundamental theorem of dimension theory for affine varieties
(Stacks `00OS`/`00P0`, Matsumura §14, Eisenbud Thm. A).  Mathlib does not have it,
but it does have both ingredients apart from the one leaf above:

* Noether normalisation, as `exists_finite_inj_algHom_of_fg`
  (`Mathlib/RingTheory/NoetherNormalization.lean`): an injective
  `K[X₁,…,X_s] →ₐ[K] B` making `B` a finite module.
* `MvPolynomial.ringKrullDim_of_isNoetherianRing` plus
  `ringKrullDim_eq_zero_of_field`, giving `ringKrullDim K[X₁,…,X_s] = s`.
* `IsTranscendenceBasis.mvPolynomial` (the variables are a transcendence basis of
  the polynomial ring) and `IsTranscendenceBasis.algebraMap_comp` (a transcendence
  basis survives an algebraic extension), applied twice: once along
  `K[X₁,…,X_s] → B`, which is integral, and once along `B → Frac B`.

So `trdeg K (Frac B) = s = ringKrullDim B`, the middle equality being the leaf.

## Faithfulness

`IsDomain B` is load-bearing: `Frac B` does not exist without it, and for a
reducible finite-type algebra `ringKrullDim` records only the largest component
while no single transcendence degree exists.  `Algebra.FiniteType K B` is
load-bearing: for `B = K(t)` (not of finite type) the dimension is `0` and the
transcendence degree is `1`.  `PerfectField K` is *not* needed here — this
statement is characteristic-free — and is deliberately absent from the hypotheses. -/
theorem trdeg_fractionRing_eq_of_ringKrullDim
    (K B : Type u) [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] (n : ℕ) (hdim : ringKrullDim B = n) :
    Algebra.trdeg K (FractionRing B) = n := by
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg K B
  letI : Algebra (MvPolynomial (Fin s) K) B := g.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  haveI : Module.Finite (MvPolynomial (Fin s) K) B := hgfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) B := Algebra.IsIntegral.of_finite _ _
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hginj
  haveI : FaithfulSMul B (FractionRing B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective B _)
  -- the Krull dimension of `B` is the number of normalising variables
  have hdimP : ringKrullDim (MvPolynomial (Fin s) K) = (s : ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hns : (n : WithBot ℕ∞) = (s : ℕ∞) := by
    rw [← hdim, ringKrullDim_eq_of_isIntegral_of_injective _ B hginj, hdimP]
  -- the normalising variables are a transcendence basis of `Frac B`
  have hb1 : IsTranscendenceBasis K
      (algebraMap (MvPolynomial (Fin s) K) B ∘ (MvPolynomial.X : Fin s → _)) :=
    (IsTranscendenceBasis.mvPolynomial (Fin s) K).algebraMap_comp
  haveI : Algebra.IsAlgebraic B (FractionRing B) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  have hb2 := hb1.algebraMap_comp (A := FractionRing B)
  have hcard : (s : Cardinal.{u}) = Algebra.trdeg K (FractionRing B) := by
    simpa using hb2.lift_cardinalMk_eq_trdeg
  rw [← hcard]
  have : n = s := by exact_mod_cast hns
  simp [this]

/-- **The module of Kähler differentials of a finite-type domain over a perfect
field has rank the Krull dimension** (PROVEN 2026-07-27 over the two results above).

`Ω[B⁄K]` and `Ω[Frac B⁄K]` have the same rank, because `Frac B` is a localization of
`B`, hence formally étale over it, so `Ω` base-changes; then the rank at the generic
point is the transcendence degree, which is the dimension. -/
theorem rank_kaehlerDifferential_eq_of_ringKrullDim
    (K B : Type u) [Field K] [PerfectField K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] (n : ℕ) (hdim : ringKrullDim B = n) :
    Module.rank B Ω[B⁄K] = n := by
  haveI : Algebra.FormallyEtale B (FractionRing B) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType B (FractionRing B) := .of_isLocalization _ (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType K (FractionRing B) := .comp K B _
  rw [← (KaehlerDifferential.isBaseChange_of_formallyEtale K B (FractionRing B)).rank_eq,
    rank_kaehlerDifferential_eq_trdeg_of_perfectField K (FractionRing B),
    trdeg_fractionRing_eq_of_ringKrullDim K B n hdim]

end Algebra

namespace AlgebraicGeometry

/-! ### Geometric connectedness -/

/-- **A geometrically irreducible morphism is geometrically connected**
(PROVEN 2026-07-27).

Mathlib has both classes and every stability property of each, but not this
implication between them, even though it is immediate from
`IrreducibleSpace ⟹ ConnectedSpace` fibre by fibre. -/
theorem geometricallyConnected_of_geometricallyIrreducible {X Y : Scheme.{u}} (f : X ⟶ Y)
    [h : GeometricallyIrreducible f] : GeometricallyConnected f := by
  rw [geometricallyIrreducible_iff, geometrically_iff_of_isClosedUnderIsomorphisms] at h
  rw [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  haveI := h K y
  infer_instance

/-- **Geometric connectedness of an affine scheme over an affine base, read on
the ring** (PROVEN 2026-07-27).

`Spec B ⟶ Spec R` is geometrically connected as soon as `Spec (B ⊗[R] K)` is a
connected space for every field `K` that is an `R`-algebra.  This is exactly
`geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` combined with
`pullbackSpecIso`, which identifies the pullback along `Spec K ⟶ Spec R` with
`Spec (B ⊗[R] K)`.

The hypothesis is *equivalent* to the conclusion — no strength is lost — but the
lemma is stated as an implication because that is the direction a prover needs.
-/
theorem geometricallyConnected_specMap_algebraMap_of_forall_connectedSpace
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (h : ∀ (K : Type u) [Field K] [Algebra R K],
      ConnectedSpace (PrimeSpectrum (B ⊗[R] K))) :
    GeometricallyConnected (Spec.map (ofHom (algebraMap R B))) := by
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  exact (pullbackSpecIso R B K).hom.homeomorph.connectedSpace_iff.mpr (h K)

/-- **A geometrically integral affine ring gives a geometrically connected
morphism** (PROVEN 2026-07-27).

The usable form of the criterion above: the spectrum of a domain is irreducible
(`PrimeSpectrum.irreducibleSpace`), hence connected, so it is enough that
`B ⊗[R] K` be a domain for every field extension. -/
theorem geometricallyConnected_specMap_algebraMap_of_forall_isDomain
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (B ⊗[R] K)) :
    GeometricallyConnected (Spec.map (ofHom (algebraMap R B))) := by
  refine geometricallyConnected_specMap_algebraMap_of_forall_connectedSpace R B ?_
  intro K _ _
  haveI := h K
  infer_instance

/-! ### Smoothness of an affine curve over a perfect field -/

/-- **Regular + finite type over a perfect field ⟹ smooth of relative dimension
the Krull dimension** (opened 2026-07-27 as a sorry leaf; **PROVEN the same day**
over `Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField` and
`ringKrullDim_eq_of_isIntegral_of_injective`, the two ring-theoretic leaves at
the top of this file — of which the FIRST is itself now proven, 2026-07-28, over
`Ideal.injective_lTensor_inclusion_of_isRegularLocalRing`).

This is the ring form of Stacks `056S` ("regular is equivalent to smooth over a
perfect field"), together with the identification of the relative dimension: for
an *integral* finite-type algebra over a field the local dimensions are all
equal to `ringKrullDim`, so a single `n` governs every point.

## The assembly (no mathematical content beyond the two leaves)

1. `Algebra.FinitePresentation.of_finiteType` upgrades finite type to finite
   presentation, since a field is Noetherian.
2. `Algebra.FormallySmooth.of_isRegularRing_of_perfectField` (proven here from the
   first leaf) gives `Algebra.Smooth K B`.
3. `Algebra.Smooth.exists_span_eq_top_isStandardSmooth` covers `Spec B` by basic
   opens `D(t)` on which `B_t` is *standard* smooth.  Mathlib's
   `SmoothOfRelativeDimension` is defined through standard smoothness, so this
   step is unavoidable and is exactly what mathlib supplies.
4. On each such `B_t`, `IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth`
   reduces the relative dimension to `rank_{B_t} Ω[B_t⁄K] = n`, and
   `KaehlerDifferential.isBaseChange_of_formallyEtale` transports the rank from `B`
   itself (a localization is formally étale), where it is `n` by
   `Algebra.rank_kaehlerDifferential_eq_of_ringKrullDim` — the second leaf.
5. `HasRingHomProperty.Spec_iff` and `RingHom.locally_iff_span_eq_top` turn the
   covering statement into the scheme-level conclusion.  The element `0` is
   discarded from the cover before step 4 (it would give the trivial ring, where
   the relative dimension is not `n`); `Submodule.span_insert_zero` shows this
   costs nothing.

## Why this leaf is worth having stated here

Two open nodes of this development want exactly this bridge, and neither can be
closed without it:

* `Fermat/FLT/ModularCurve/X0.lean`'s
  `smoothOfRelativeDimension_of_gamma0GITPresentation`, where `B = A^G` is the
  ring of invariants of the Katz–Mazur rigidified moduli scheme and the whole
  point of the GIT presentation is that the coarse space is `Spec B`;
* `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`'s
  `smoothOfRelativeDimension_one_fromNormalization`, which is the *scheme* form
  of the same statement (normal + dimension one + perfect base ⟹ smooth) and is
  described there as "the deepest" of that file's leaves.

Proving it once here serves both.  A consumer of the scheme form can obtain it
from this one on an affine cover; the two are deliberately not merged in this
release because `CurveCompactification.lean` has a different owner.

## What blocks it in the pin, checked 2026-07-27 (now localised in the two leaves)

Mathlib has all three ingredients and no link between them.

1. `IsRegularRing` (`Mathlib/RingTheory/RegularLocalRing/Defs.lean`), with
   `[IsDedekindDomain R] : IsRegularRing R` — so the dimension-one case of the
   hypothesis is available from normality for free.
2. `Algebra.Smooth`, `Algebra.smoothLocus`, and the local Jacobian criterion
   `Algebra.FormallySmooth.iff_injective_lTensor_residueField`
   (`Mathlib/RingTheory/Smooth/Local.lean`).
3. `Algebra.FormallySmooth.of_perfectField`
   (`Mathlib/RingTheory/Smooth/Field.lean`), which gives formal smoothness of a
   *field* extension essentially of finite type over a perfect field — i.e. the
   statement at the GENERIC point only.  That is also as far as mathlib's own
   `Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField` and
   `Scheme.Hom.dense_smoothLocus_of_perfectField` get: the smooth locus is dense,
   never all of `X`.

*The check that would refute this*: `grep -rn "IsRegularRing"` over
`Mathlib/RingTheory/Smooth/` or `Mathlib/AlgebraicGeometry/` returning anything
— at this pin it returns nothing in either.

The missing step is therefore smoothness at the CLOSED points, i.e. formal
smoothness of a regular local ring essentially of finite type over a perfect
field.  In characteristic zero every residue field is separable over the base,
so the Jacobian criterion of ingredient 2 applies once `dim_k m/m² = dim` is
converted into injectivity of `k ⊗ I/I² → k ⊗ Ω[P/K]`; that conversion is the
whole content and it is not in the pin.  That step is
`Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField`, PROVEN 2026-07-28,
and the conversion turned out to need **no dimension theory at all**: applying the
same Jacobian criterion to the residue field itself factors the map through
`κ ⊗ I → κ ⊗ 𝔪_P`, leaving only
`Ideal.injective_lTensor_inclusion_of_isRegularLocalRing`, which mentions no field.

A *second* thing was missing and had not been noticed when this leaf was first
stated: mathlib's `SmoothOfRelativeDimension` is a statement about the RANK of
`Ω`, so identifying the relative dimension with `ringKrullDim` needs "dimension =
transcendence degree", which is also absent from the pin.  That reduces, by
Noether normalisation, to the second leaf
`ringKrullDim_eq_of_isIntegral_of_injective`.  The bridge between the two — that
the rank of `Ω` of a finitely generated field extension of a perfect field *is*
the transcendence degree — is proven above.

## Faithfulness

`IsDomain B` is load-bearing and must not be dropped: without it a regular ring
can have components of different dimensions (`B = K × K[x]`), `ringKrullDim B`
records only the largest, and no single relative dimension exists — the
statement would be false at the points of the small component.

`PerfectField K` is load-bearing too, and this is not a formalisation artefact:
over an imperfect field of characteristic `p` the curve `y ^ p = t * x ^ p + t`
(`t ∈ k \ k ^ p`) is regular and not smooth.  `ℚ` is perfect, so the modular
application is unaffected. -/
theorem smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing
    (K B : Type u) [Field K] [PerfectField K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] [IsRegularRing B] (n : ℕ) (hdim : ringKrullDim B = n) :
    SmoothOfRelativeDimension n (Spec.map (ofHom (algebraMap K B))) := by
  haveI : Algebra.FinitePresentation K B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.FormallySmooth K B :=
    Algebra.FormallySmooth.of_isRegularRing_of_perfectField K B
  haveI : Algebra.Smooth K B := ⟨inferInstance, inferInstance⟩
  have hrank : Module.rank B Ω[B⁄K] = n :=
    Algebra.rank_kaehlerDifferential_eq_of_ringKrullDim K B n hdim
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  show RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) _
  rw [RingHom.locally_iff_span_eq_top]
  obtain ⟨s, hs, hst⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth K B
  refine top_le_iff.mp ?_
  calc (⊤ : Ideal B)
      = Ideal.span s := hs.symm
    _ ≤ Ideal.span (insert 0 {g : B | RingHom.IsStandardSmoothOfRelativeDimension n
          ((algebraMap B (Localization.Away g)).comp (Hom.hom (ofHom (algebraMap K B))))}) := by
        refine Ideal.span_mono fun t ht ↦ ?_
        rcases eq_or_ne t 0 with rfl | ht0
        · exact Set.mem_insert _ _
        refine Set.mem_insert_of_mem _ ?_
        haveI : Algebra.IsStandardSmooth K (Localization.Away t) := hst t ht
        have hle : Submonoid.powers t ≤ nonZeroDivisors B :=
          powers_le_nonZeroDivisors_of_noZeroDivisors ht0
        haveI : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
        haveI : FaithfulSMul B (Localization.Away t) :=
          (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
        haveI : Algebra.FormallyEtale B (Localization.Away t) :=
          Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
        have hr : Module.rank (Localization.Away t) Ω[Localization.Away t⁄K] = n := by
          rw [(KaehlerDifferential.isBaseChange_of_formallyEtale K B
            (Localization.Away t)).rank_eq, hrank]
        haveI : Algebra.IsStandardSmoothOfRelativeDimension n K (Localization.Away t) :=
          (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr hr
        show RingHom.IsStandardSmoothOfRelativeDimension n _
        rw [CommRingCat.hom_ofHom, ← IsScalarTower.algebraMap_eq K B (Localization.Away t)]
        exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance
    _ = _ := Submodule.span_insert_zero

end AlgebraicGeometry
