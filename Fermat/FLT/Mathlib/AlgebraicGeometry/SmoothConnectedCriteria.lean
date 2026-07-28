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
  off the Krull dimension (**PROVEN 2026-07-28** over
  `Algebra.Smooth.of_isRegularRing_of_perfectField`, i.e. over Stacks `056S`,
  and over the pure dimension leaf below).
* `smoothOfRelativeDimension_specMap_algebraMap_of_smooth` — what is LEFT of the
  previous item once regularity and perfectness have been consumed: for a
  **smooth** finite-type domain over ANY field, the relative dimension is the
  Krull dimension (**PROVEN 2026-07-28**; no perfectness, no regularity).
* `Algebra.linearIndepOn_pow_of_formallySmooth` — a formally smooth field extension
  is separable in MacLane's sense, Stacks `0323` (**PROVEN 2026-07-28**).  It is what
  the previous item pays for dropping `PerfectField`; mathlib records the same
  implication as a TODO of its own in `Mathlib/FieldTheory/SeparablyGenerated.lean`,
  so this is plausibly upstreamable as stated.
* `Algebra.exists_derivation_extension_of_formallySmooth` — the derivation half of
  that argument: a formally smooth extension extends every derivation of the base,
  by lifting `id` through the square-zero extension `TrivSqZeroExt L L` twisted into
  a `K`-algebra by the derivation (**PROVEN 2026-07-28**).
* `Algebra.exists_derivation_apply_ne_zero_of_forall_pow_ne` — the file's ONLY
  remaining leaf, and pure elementary field theory: over a field of characteristic
  `p`, an element that no derivation moves is a `p`-th power.  Its docstring
  CORRECTS the earlier claim that this needs `p`-basis theory — Zorn over partial
  `K ^ p`-derivations suffices, because the obstruction to crossing a simple
  purely-inseparable step is `D (y ^ p)`, which vanishes for free.
* `ringKrullDim_eq_of_isIntegral_of_injective` — an injective integral ring
  extension preserves the Krull dimension, Stacks `00OJ`+`00OK` (**PROVEN
  2026-07-28**, by an `RelSeries.inductionOn'` lift of chains — this is the
  arbitrary-length going-up theorem mathlib records as a TODO of its own).

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
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.FieldTheory.PerfectClosure
public import Fermat.FLT.Mathlib.RingTheory.Smooth.RegularLocal
-- (restored at the release-12 integration: these were dropped when an import-block
-- conflict was resolved to one SIDE instead of as a UNION.  Every one is needed by a
-- proof that is already in this file.)
public import Mathlib.RingTheory.Smooth.Field
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
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct CommRingCat

/-! ### Commutative-algebra input: regularity, smoothness, and the rank of `Ω`

`ringKrullDim_eq_of_isIntegral_of_injective` was PROVEN 2026-07-28, and so was the
scheme section's `smoothOfRelativeDimension_specMap_algebraMap_of_smooth`.
`Algebra.linearIndepOn_pow_of_formallySmooth` — MacLane's separability condition for
a formally smooth field extension, Stacks `0323`, and the only place where dropping
`PerfectField` from the smoothness criterion is paid for — was PROVEN later the same
day, over two new lemmas below.

The ONE remaining leaf of the whole file is now
`Algebra.exists_derivation_apply_ne_zero_of_forall_pow_ne`: over a field of
characteristic `p`, an element killed by every derivation is a `p`-th power.  It has
no schemes, no smoothness, no dimension theory and no differentials in it — it is
elementary field theory, and mathlib has no `Derivation` API for fields outside the
characteristic-zero `Mathlib/FieldTheory/Differential/` pair.
-/

namespace Algebra

/-! #### **A regular local ring essentially of finite type over a perfect field is
formally smooth over it** (sorry leaf, opened 2026-07-27).

This is the local form of Stacks `056S` ("regular is equivalent to smooth over a
perfect field"), equivalently Matsumura *Commutative Ring Theory* §28, and it is
the single piece of this file's development that mathlib does not supply in any
form.

## What mathlib has, checked 2026-07-27

1. `IsRegularLocalRing` (`Mathlib/RingTheory/RegularLocalRing/Defs.lean`), and
   `IsRegularRing` as "every localization at a prime is regular local".
2. The local Jacobian criterion
   `Algebra.FormallySmooth.iff_injective_lTensor_residueField`
   (`Mathlib/RingTheory/Smooth/Local.lean`): for a presentation `0 → I → P → A → 0`
   with `P` formally smooth over the base and `Ω[P⁄R]` finite free, `A` is
   formally smooth iff `κ ⊗ I/I² → κ ⊗ Ω[P⁄R]` is injective.
3. `Algebra.FormallySmooth.of_perfectField` (`Mathlib/RingTheory/Smooth/Field.lean`):
   a field extension essentially of finite type over a perfect field is formally
   smooth.  That is this statement at the GENERIC point, and it is as far as
   mathlib's `Scheme.Hom.dense_smoothLocus_of_perfectField` gets as well.

*The check that would refute this*: `grep -rn "IsRegularRing"` over
`Mathlib/RingTheory/Smooth/` or `Mathlib/AlgebraicGeometry/` returning anything —
at this pin it returns nothing in either.

## The intended route

Present `A = P/I` with `P` a localization of a polynomial ring at a prime, so
that ingredient 2 applies, and prove injectivity of `κ ⊗ I/I² → κ ⊗ Ω[P⁄K]` by
counting: `dim_κ (I/I² ⊗ κ) = μ(I) ≥ ht I = dim P - dim A` always, and regularity
of `A` together with separability of `κ/K` (automatic over a perfect field) forces
equality.  The separability of the residue field is exactly where `PerfectField K`
enters, and it is genuinely needed — see the faithfulness note on the theorem at
the end of this file for the standard counterexample over an imperfect field.

## Faithfulness

Both hypotheses are load-bearing.  `EssFiniteType K A` cannot be dropped (formal
smoothness of a general regular local `K`-algebra is false — a complete local ring
such as `K⟦t⟧` is regular but not formally smooth over `K` for the discrete
topology), and `PerfectField K` cannot be dropped (same counterexample as below). -/
-- (`Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField` is declared in
-- `Fermat/FLT/Mathlib/RingTheory/Smooth/RegularLocal.lean`, which this module `public
-- import`s, and it is PROVEN there over the single leaf
-- `Algebra.injective_lTensor_residueField_kerInclusion`.  Two branches wrote the same
-- statement into two files, one importing the other -- the release-6 defect class -- so the
-- SORRIED copy that stood here has been deleted.  The surviving form takes `K` and `R`
-- IMPLICITLY; the docstring above is retained for its faithfulness note.)

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
  exact FormallySmooth.of_isRegularLocalRing_of_perfectField (K := K)

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- **The rank of the module of Kähler differentials of a SEPARABLY GENERATED field
extension is its transcendence degree** (PROVEN 2026-07-27 for a perfect base;
generalised 2026-07-28 by moving the separating transcendence basis into the
hypothesis, which is all the proof ever used).

Mathlib computes `Ω` for a polynomial ring (`KaehlerDifferential.mvPolynomialBasis`)
and has the whole separably-generated theory
(`Mathlib/FieldTheory/SeparablyGenerated.lean`), but nowhere connects them:
`grep -rn "trdeg" Mathlib/RingTheory/Kaehler/` is empty at this pin, and so is the
reverse grep for `Ω[` over `Mathlib/FieldTheory/`.

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

## Faithfulness

The separating-basis hypothesis is load-bearing and cannot be weakened to the mere
existence of a transcendence basis: for `L = K(t^{1/p})` over `K = 𝔽_p(t)` the
transcendence degree is `0` while `Ω[L⁄K]` is one-dimensional.  What the hypothesis
buys is exactly that the last arrow is separable algebraic, hence formally étale. -/
theorem rank_kaehlerDifferential_eq_trdeg_of_exists_separating
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L]
    (hsg : ∃ s : Finset L, IsTranscendenceBasis K ((↑) : s → L) ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set L)) L) :
    Module.rank L Ω[L⁄K] = Algebra.trdeg K L := by
  obtain ⟨s, hs, hsep⟩ := hsg
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

/-- **A formally smooth extension extends every derivation of the base**
(PROVEN 2026-07-28; step 1 of MacLane's criterion below).

Given `D : K → L`, the assignment `k ↦ k + (D k) ε` makes the square-zero extension
`L[ε] = TrivSqZeroExt L L` into a `K`-algebra whose structure map has `fst`
component `algebraMap K L`, so the projection `fst : L[ε] → L` is a `K`-algebra map,
surjective, with square-zero — hence nilpotent — kernel.
`Algebra.FormallySmooth.liftOfSurjective` lifts `id : L →ₐ[K] L` through it to
`σ : L →ₐ[K] L[ε]` with `(σ x).fst = x`, and `D' x := (σ x).snd` is the derivation
wanted: `σ` multiplicative gives Leibniz through `TrivSqZeroExt.snd_mul`, and
`σ.commutes` gives `D' ∘ algebraMap = D`.

Abstractly this is the split injectivity of `Ω[K⁄ℤ] ⊗_K L → Ω[L⁄ℤ]`, i.e. the
vanishing of `H¹L_{L/K}`; the square-zero extension is that statement made
elementary, and needs no Jacobi–Zariski machinery.

Stated over `ℤ` rather than over the prime field on purpose: a derivation over `ℤ`
is just an additive Leibniz map, which is the weakest hypothesis the consumer needs
and the strongest conclusion this proof gives. -/
theorem exists_derivation_extension_of_formallySmooth
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.FormallySmooth K L]
    (D : Derivation ℤ K L) :
    ∃ D' : Derivation ℤ L L, ∀ x : K, D' (algebraMap K L x) = D x := by
  classical
  let φ : K →+* TrivSqZeroExt L L :=
    { toFun := fun k => TrivSqZeroExt.inl (algebraMap K L k) + TrivSqZeroExt.inr (D k)
      map_one' := by ext <;> simp
      map_mul' := fun a b => by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp [D.leibniz, Algebra.smul_def]; ring
      map_zero' := by ext <;> simp
      map_add' := fun a b => by refine TrivSqZeroExt.ext ?_ ?_ <;> simp }
  letI : Algebra K (TrivSqZeroExt L L) := φ.toAlgebra
  have hAM : ∀ k : K, algebraMap K (TrivSqZeroExt L L) k
      = TrivSqZeroExt.inl (algebraMap K L k) + TrivSqZeroExt.inr (D k) := fun k => rfl
  have hfst : ∀ k : K, (algebraMap K (TrivSqZeroExt L L) k).fst = algebraMap K L k := by
    intro k; rw [hAM]; simp
  have hsnd : ∀ k : K, (algebraMap K (TrivSqZeroExt L L) k).snd = D k := by
    intro k; rw [hAM]; simp
  let g : TrivSqZeroExt L L →ₐ[K] L :=
    { toFun := TrivSqZeroExt.fst
      map_one' := by simp
      map_mul' := fun a b => by simp
      map_zero' := by simp
      map_add' := fun a b => by simp
      commutes' := hfst }
  have hgapp : ∀ y : TrivSqZeroExt L L, g y = y.fst := fun _ => rfl
  have hgsurj : Function.Surjective g := fun x => ⟨TrivSqZeroExt.inl x, by simp [hgapp]⟩
  have hker : IsNilpotent (RingHom.ker (g : TrivSqZeroExt L L →+* L)) := by
    have hmul : RingHom.ker (g : TrivSqZeroExt L L →+* L)
        * RingHom.ker (g : TrivSqZeroExt L L →+* L) = ⊥ := by
      rw [eq_bot_iff]
      refine Ideal.mul_le.2 fun r hr t ht => ?_
      rw [RingHom.mem_ker] at hr ht
      have hr' : r.fst = 0 := hr
      have ht' : t.fst = 0 := ht
      have hrt : r * t = 0 := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp [hr', ht']
      simp [hrt]
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, ← hmul]
    ring
  let σ : L →ₐ[K] TrivSqZeroExt L L :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K L) g hgsurj hker
  have hσ : ∀ x : L, (σ x).fst = x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id K L) g hgsurj hker x
  let f : L →+ L :=
    { toFun := fun x => (σ x).snd
      map_zero' := by simp
      map_add' := fun x y => by simp }
  refine ⟨{ toLinearMap := f.toIntLinearMap
            map_one_eq_zero' := by simp [f]
            leibniz' := fun a b => ?_ }, fun x => ?_⟩
  · show (σ (a * b)).snd = a • (σ b).snd + b • (σ a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hσ, hσ, op_smul_eq_smul]
  · show (σ (algebraMap K L x)).snd = D x
    rw [σ.commutes, hsnd]

/-- **Derivations of a field of characteristic `p` separate it from its `p`-th
powers** (sorry leaf, opened 2026-07-28 as the ONE residual of MacLane's criterion
below).

Pure elementary field theory: no schemes, no smoothness, no differentials, and — see
the route below — **no `p`-basis theory**.  This is Matsumura, *Commutative Ring
Theory*, Thm. 26.5 / the standard "`ker d = K ^ p` in `Ω[K⁄K ^ p]`" statement, in the
one direction the criterion needs.

## Route: ZORN OVER PARTIAL DERIVATIONS, not a `p`-basis

Both earlier write-ups of this node (and mathlib-facing folklore) say the missing
ingredient is `p`-basis theory — "extend `{c}` to a `p`-basis of `K` over `K ^ p`".
**That is more than is needed, and the cheaper argument is the one to write.**  Set
`k := K ^ p`, a subfield (Frobenius is a ring hom, and its image is closed under
inverses).  Note first that any additive derivation of `K` automatically kills `k`,
since `D (x ^ p) = p • x ^ (p - 1) • D x = 0` in characteristic `p` — so "derivation
of `K`" and "`k`-derivation of `K`" are the same thing here, and that is what makes
the extension step free:

1. *Base.*  `c ∉ k` and `p` is prime, so `X ^ p - C (c ^ p)` is irreducible over `k`
   (`X_pow_sub_C_irreducible_iff_of_prime`) and `k (c) = k [X] / (X ^ p - C (c ^ p))`
   has degree `p` over `k`.  Its formal derivative is `p X ^ (p - 1) = 0`, so
   `d / dc` is a well-defined `k`-derivation `k (c) → K` with `d c / d c = 1 ≠ 0`.
2. *Zorn.*  Order the partial `k`-derivations `(F, D)` — `k (c) ≤ F ≤ K` an
   intermediate field, `D : F → K` a `k`-derivation extending the base one — by
   extension.  A chain has its union as an upper bound (the domain of a union of a
   chain of subfields is a subfield, and functionality of the union is exactly the
   chain condition), so a maximal `(F, D)` exists.
3. *Extension step — this is where `p`-basis theory is NOT needed.*  If `F ≠ K`, pick
   `y ∈ K \ F`.  Then `y ^ p ∈ k ⊆ F` and the minimal polynomial of `y` over `F` is
   `X ^ p - C (y ^ p)`: it is killed by `y`, and `(X - y) ^ k` has `F`-coefficient
   `- k y`, so `k < p` would force `y ∈ F`.  To extend `D` across `F ⊆ F (y)` with
   `D y := 0` one must check that `D` annihilates the minimal polynomial's
   coefficients, i.e. that `D (y ^ p) = 0` — **and that is automatic, because
   `y ^ p ∈ k` and `D` is a `k`-derivation.**  (Contrast a general simple extension,
   where this obstruction is a real condition and is what forces a `p`-basis.)  So
   the extension always exists, contradicting maximality; hence `F = K`.

Mechanically, step 3 is the pattern of `Mathlib/FieldTheory/Differential/Basic.lean`,
which extends a derivation across `AdjoinRoot p` using `Derivation.liftOfSurjective`
and `Derivation.mapCoeffs` — but with the `p`-th-power obstruction vanishing instead
of being divided away by `derivative p` (which is `0` here, so the char-zero file's
own argument does *not* transfer; only its shape does).

*Checks re-run 2026-07-28, both confirming absence*: `grep -rn "pBasis\|PBasis"
.lake/packages/mathlib/Mathlib/` has no field-theoretic hit, and `grep -rn
"Derivation" .lake/packages/mathlib/Mathlib/FieldTheory/*.lean` finds only
`Differential/{Basic,Liouville}.lean`, which are characteristic-zero.  `~/cs/FLT` has
nothing on either.

## Faithfulness

Both hypotheses are load-bearing.  Primality of `p`: over a field of characteristic
`0` every `D` is a derivation of a perfect field and the conclusion "`c` is a `p`-th
power" is false for, e.g., `p = 4`, `K = ℚ`, `c = 2` (`ℚ` has no derivations at all,
so the hypothesis is vacuously satisfied while `2` is no fourth power) — the
statement is only about the characteristic.  `CharP K p` is what makes `D` kill
`K ^ p` and hence makes the conclusion reachable.

*Not vacuous*: at `K = 𝔽_p (t)`, `c = t`, the derivation `d / dt` has `D t = 1 ≠ 0`,
so the conclusion is a genuine existence statement rather than one discharged by
`D = 0`.  Conversely for `K` perfect the hypothesis `∀ b, b ^ p ≠ c` is unsatisfiable
and the leaf says nothing — which is exactly why characteristic `0` never consumes
it. -/
theorem exists_derivation_apply_ne_zero_of_forall_pow_ne
    (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] {c : K}
    (hc : ∀ b : K, b ^ p ≠ c) :
    ∃ D : Derivation ℤ K K, D c ≠ 0 :=
  sorry

/-- **`p`-th powers preserve `K`-linear independence in a formally smooth extension**
(**PROVEN 2026-07-28** over `exists_derivation_apply_ne_zero_of_forall_pow_ne`;
opened as a sorry leaf earlier the same day).

This is Stacks `0323` — *a formally smooth field extension is separable* — in the
concrete "MacLane condition" form that mathlib's separably-generated file consumes
(`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`,
which is Stacks `030W` (2) ⇒ (1)).  Mathlib records the missing converse as a TODO
of its own, right above that lemma: *"TODO: show that this is an if and only if."*

The condition is the linear-independence form of "`L ⊗_K K^{1/p}` is reduced".

## How it is proven

`p = 1` (characteristic zero) is `pow_one`.  For `p` prime, by
`linearIndepOn_iff'` it suffices to kill every finite relation
`∑_{y ∈ t} g y • y ^ p = 0` with `t ⊆ s`, and that goes by strong induction on `t`:

* Normalise at a `y = x` with `g x ≠ 0`, so the coefficients `c y := (g x)⁻¹ * g y`
  have `c x = 1`.
* For **any** derivation `D` of `K`, extend it to `L` by
  `exists_derivation_extension_of_formallySmooth` and apply the extension to the
  relation.  Each `D' (y ^ p) = p • y ^ (p - 1) • D' y = 0` in characteristic `p`,
  so Leibniz leaves `∑_{y ∈ t} D (c y) • y ^ p = 0`.  Its coefficient at `x` is
  `D 1 = 0`, so it is a relation over `t.erase x` and the induction hypothesis kills
  it: `D (c y) = 0` for every `y ∈ t` and every `D`.
* Hence every `c y` is a `p`-th power `b y ^ p`, by
  `exists_derivation_apply_ne_zero_of_forall_pow_ne` (contrapositive).
* Freshman's dream (`sum_pow_char`) gives `(∑ b y • y) ^ p = ∑ c y • y ^ p = 0`, so
  `∑ b y • y = 0`, so `hs` forces `b x = 0` — contradicting `b x ^ p = c x = 1`.

## Faithfulness

TRUE as stated, and not vacuous.  `[ExpChar K p]` allows `p = 1` (characteristic
zero), where `(· ^ 1)` is the identity and the statement is trivially true; the
content is at `p = char K` prime.  `Algebra.FormallySmooth K L` is load-bearing:
without it take `K = 𝔽_p(t)`, `L = K(t ^ (1 / p))`, and the `K`-linearly independent
pair `{1, t ^ (1 / p)}`, whose `p`-th powers `{1, t}` satisfy the nontrivial relation
`t · 1 - 1 · t = 0`.  No finiteness hypothesis is needed — Stacks `0323` is stated
for an arbitrary extension.

`hs` is load-bearing too — without it take `s = {a, 2 * a}` in characteristic
`p ≠ 2`, whose `p`-th powers `{a ^ p, 2 ^ p * a ^ p}` are always dependent — and the
proof above uses it in its very last step. -/
theorem linearIndepOn_pow_of_formallySmooth
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.FormallySmooth K L]
    (p : ℕ) [hexp : ExpChar K p] (s : Finset L) (hs : LinearIndepOn K _root_.id (s : Set L)) :
    LinearIndepOn K (· ^ p) (s : Set L) := by
  classical
  rcases hexp with _ | ⟨hp⟩
  · have hs' : LinearIndepOn K (fun x : L => x) (s : Set L) := hs
    simpa only [pow_one] using hs'
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI hLp : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    haveI : ExpChar L p := .prime hp
    rw [linearIndepOn_iff'] at hs ⊢
    intro t
    induction t using Finset.strongInduction with
    | _ t IH =>
      intro g hts hsum x hx
      by_contra hgx
      set c : L → K := fun y => (g x)⁻¹ * g y with hcdef
      have hcx : c x = 1 := by simp [hcdef, inv_mul_cancel₀ hgx]
      have hcsum : ∑ y ∈ t, c y • y ^ p = 0 := by
        have hscale : ∑ y ∈ t, c y • y ^ p = (g x)⁻¹ • ∑ y ∈ t, g y • y ^ p := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun y _ => by rw [hcdef]; simp [smul_smul]
        rw [hscale, hsum, smul_zero]
      -- every derivation of `K` kills every coefficient
      have hker : ∀ D : Derivation ℤ K K, ∀ y ∈ t, D (c y) = 0 := by
        intro D
        obtain ⟨D', hD'⟩ :=
          exists_derivation_extension_of_formallySmooth K L ((Algebra.linearMap K L).compDer D)
        have hpow : ∀ z : L, D' (z ^ p) = 0 := by
          intro z
          rw [Derivation.leibniz_pow]
          have hp0 : (p : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L p
          rw [← Nat.cast_smul_eq_nsmul L, hp0, zero_smul]
        have hterm : ∀ y : L, D' (c y • y ^ p) = D (c y) • y ^ p := by
          intro y
          rw [Algebra.smul_def, D'.leibniz, hpow, smul_zero, zero_add, hD']
          show y ^ p • (Algebra.linearMap K L) (D (c y)) = _
          simp [Algebra.linearMap_apply, Algebra.smul_def, mul_comm]
        have key : ∑ y ∈ t, D (c y) • y ^ p = 0 := by
          have hD0 := congrArg D' hcsum
          rw [map_sum, map_zero] at hD0
          rw [← hD0]
          exact Finset.sum_congr rfl fun y _ => (hterm y).symm
        have hDx : D (c x) = 0 := by rw [hcx]; simp
        have key' : ∑ y ∈ t.erase x, D (c y) • y ^ p = 0 := by
          rw [← Finset.add_sum_erase t _ hx, hDx, zero_smul, zero_add] at key
          exact key
        have hsmall := IH (t.erase x) (Finset.erase_ssubset hx) (fun y => D (c y))
          (fun y hy => hts (Finset.mem_of_mem_erase hy)) key'
        intro y hy
        rcases eq_or_ne y x with rfl | hyx
        · exact hDx
        · exact hsmall y (Finset.mem_erase.2 ⟨hyx, hy⟩)
      -- so every coefficient is a `p`-th power
      have hpth : ∀ y : L, ∃ bb : K, y ∈ t → bb ^ p = c y := by
        intro y
        by_cases hy : y ∈ t
        · have hex : ∃ bb : K, bb ^ p = c y := by
            by_contra hb
            obtain ⟨D, hD⟩ :=
              exists_derivation_apply_ne_zero_of_forall_pow_ne K p (fun bb hbb => hb ⟨bb, hbb⟩)
            exact hD (hker D y hy)
          obtain ⟨bb, hbb⟩ := hex
          exact ⟨bb, fun _ => hbb⟩
        · exact ⟨0, fun h => absurd h hy⟩
      choose b hb using hpth
      have hzero : (∑ y ∈ t, b y • y) ^ p = 0 := by
        rw [← hcsum, sum_pow_char]
        exact Finset.sum_congr rfl fun y hy => by rw [smul_pow, hb y hy]
      have hsum0 : ∑ y ∈ t, b y • y = 0 := pow_eq_zero_iff (Nat.Prime.ne_zero hp) |>.1 hzero
      have hbx0 := hs t b hts (by simpa using hsum0) x hx
      have hbx : b x ^ p = c x := hb x hx
      rw [hbx0, zero_pow (Nat.Prime.ne_zero hp), hcx] at hbx
      exact zero_ne_one hbx

/-- **A formally smooth field extension of finite type is separably generated**
(PROVEN 2026-07-28 over the leaf above).

In characteristic zero the base field is perfect and mathlib's
`exists_isTranscendenceBasis_and_isSeparable_of_perfectField` applies directly, so
the leaf is only ever consumed in characteristic `p`. -/
theorem exists_isTranscendenceBasis_and_isSeparable_of_formallySmooth
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L]
    [Algebra.FormallySmooth K L] :
    ∃ s : Finset L, IsTranscendenceBasis K ((↑) : s → L) ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set L)) L := by
  obtain _ | ⟨p, hp, hpK⟩ := CharP.exists' K
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  · haveI : ExpChar K p := .prime hp.out
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      p hp.out fun s hs ↦ linearIndepOn_pow_of_formallySmooth K L p s hs

/-- **The rank of `Ω` of a formally smooth field extension of finite type is its
transcendence degree** (PROVEN 2026-07-28).

This is the characteristic-free replacement for
`rank_kaehlerDifferential_eq_trdeg_of_perfectField`: formal smoothness does exactly
the job perfectness did, namely produce a *separating* transcendence basis. -/
theorem rank_kaehlerDifferential_eq_trdeg_of_formallySmooth
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L]
    [Algebra.FormallySmooth K L] :
    Module.rank L Ω[L⁄K] = Algebra.trdeg K L :=
  rank_kaehlerDifferential_eq_trdeg_of_exists_separating K L
    (exists_isTranscendenceBasis_and_isSeparable_of_formallySmooth K L)

/-- **The rank of the module of Kähler differentials of a finitely generated field
extension of a perfect field is its transcendence degree** (PROVEN 2026-07-27; since
2026-07-28 a two-line corollary of
`rank_kaehlerDifferential_eq_trdeg_of_exists_separating`, which carries the proof).

`PerfectField K` is load-bearing and is used exactly once, to produce a
*separating* transcendence basis: over an imperfect field the third arrow can fail
to be separable and the rank strictly exceeds the transcendence degree (e.g.
`L = K(t^{1/p})` over `K = 𝔽_p(t)`, where `trdeg = 0` but `Ω[L⁄K]` is
one-dimensional). -/
theorem rank_kaehlerDifferential_eq_trdeg_of_perfectField
    (K L : Type u) [Field K] [PerfectField K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Module.rank L Ω[L⁄K] = Algebra.trdeg K L :=
  rank_kaehlerDifferential_eq_trdeg_of_exists_separating K L
    (exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L)

end Algebra

/-- **An injective integral ring extension preserves the Krull dimension**
(opened as a sorry leaf 2026-07-27; **PROVEN 2026-07-28**).

Stacks `00OK` (`dim S ≤ dim R`, by incomparability) together with `00OJ`
(`dim R ≤ dim S`, by lying over and going up).  It is stated in full mathlib
generality rather than for the finite-type case that needs it, because that is
what it is.  Mathlib flags the chain form of going-up as a TODO of its own — see
below — so this fills that gap.

## The proof

Both halves of the argument are present in the pin as statements about a *single*
prime; the content added here is the passage to chains.

* `≤` (Stacks `00OK`): incomparability, `Ideal.IsIntegral.comap_lt_comap` — for
  `I < J` primes of `S`, `comap I < comap J`.  So `PrimeSpectrum.comap
  (algebraMap R S)` is strictly monotone and `Order.krullDim_le_of_strictMono`
  gives `dim S ≤ dim R` in one line.  (Injectivity is not needed here.)
* `≥` (Stacks `00OJ`): every `LTSeries (PrimeSpectrum R)` is lifted to an
  `LTSeries (PrimeSpectrum S)` of the *same length* lying over it, by
  `RelSeries.inductionOn'` — the induction principle that builds a series from a
  singleton by repeated `snoc`, which is exactly the shape of a going-up
  argument.  The singleton case is lying over,
  `Ideal.exists_ideal_over_prime_of_isIntegral` applied with `I = ⊥` (this is
  where injectivity enters, as `RingHom.ker (algebraMap R S) = ⊥ ≤ P`); the
  `snoc` case is going up,
  `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`, which produces
  `Q ≥ q.last` over the next prime `x` of the chain.  Strictness of the new step
  is *not* given by that lemma and has to be argued: `q.last ≤ Q` and the two
  contract to `p.last < x`, so they cannot be equal.  Then
  `Order.LTSeries.length_le_krullDim` on the lifted series bounds each length in
  the supremum defining `krullDim (PrimeSpectrum R)`.

Mathlib asks for precisely this: the comment above
`exists_ideal_over_prime_of_isIntegral_of_isPrime` reads *"TODO: Version of
going-up theorem with arbitrary length chains (by induction on this)?  Not sure
how best to write an ascending chain in Lean"*.  The answer is `LTSeries`, and
`RelSeries.inductionOn'` is the induction it asks for.

A dead end worth recording so it is not re-explored: the `≥` direction does **not**
follow from `Order.krullDim_le_of_strictComono_and_surj` even though
`Algebra.IsIntegral.comap_surjective` supplies its surjectivity hypothesis, because
`PrimeSpectrum.comap` is not strictly comonotone.  Counterexample: `R = k[x]`,
`S = k[x] × k[x]`, `q₁ = 0 × k[x]`, `q₂ = k[x] × (x)`; then
`comap q₁ = (0) < (x) = comap q₂` while `q₁ ⊄ q₂` (as `(0,1) ∈ q₁ \ q₂`).  So the
lifted chain really has to be built step by step, each prime chosen above the
previous one — which is what the `snoc` case does.

## Faithfulness

Injectivity is load-bearing: without it take `R` any ring and `S = 0`, which is
integral over `R` with `ringKrullDim S = ⊥ ≠ ringKrullDim R`.  It is used exactly
once, in the lying-over step. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (h : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R := by
  have hker : RingHom.ker (algebraMap R S) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp h
  refine le_antisymm ?_ ?_
  · -- `00OK`: incomparability makes `comap` strictly monotone.
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro x y hxy
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hxy ⊢
    exact Ideal.IsIntegral.comap_lt_comap hxy
  · -- `00OJ`: lying over and going up lift a chain of `R` to a chain of `S` of the same length.
    have key : ∀ p : LTSeries (PrimeSpectrum R), ∃ q : LTSeries (PrimeSpectrum S),
        q.length = p.length ∧ PrimeSpectrum.comap (algebraMap R S) q.last = p.last := by
      intro p
      induction p using RelSeries.inductionOn' with
      | singleton x =>
          -- lying over
          obtain ⟨Q, -, hQp, hQc⟩ :=
            Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal S)
              (by simp [← RingHom.ker_eq_comap_bot, hker])
          refine ⟨RelSeries.singleton _ ⟨Q, hQp⟩, rfl, ?_⟩
          rw [RelSeries.last_singleton]
          exact PrimeSpectrum.ext hQc
      | snoc p x hx ih =>
          -- going up, one step
          obtain ⟨q, hlen, hcomap⟩ := ih
          have hlt : p.last.asIdeal < x.asIdeal := PrimeSpectrum.asIdeal_lt_asIdeal _ _ |>.mpr hx
          have hle : q.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
            have : (PrimeSpectrum.comap (algebraMap R S) q.last).asIdeal ≤ x.asIdeal := by
              rw [hcomap]; exact hlt.le
            exact this
          obtain ⟨Q, hQge, hQp, hQc⟩ :=
            Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime x.asIdeal q.last.asIdeal hle
          -- the new prime is *strictly* above the old one, because their contractions differ
          have hrel : q.last < (⟨Q, hQp⟩ : PrimeSpectrum S) := by
            rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
            refine lt_of_le_of_ne hQge fun hEq => ?_
            have h1 : (PrimeSpectrum.comap (algebraMap R S) q.last).asIdeal = x.asIdeal := by
              show q.last.asIdeal.comap (algebraMap R S) = x.asIdeal
              rw [hEq]; exact hQc
            rw [hcomap] at h1
            exact absurd h1 hlt.ne
          refine ⟨q.snoc ⟨Q, hQp⟩ hrel, by simp [hlen], ?_⟩
          simp only [RelSeries.last_snoc]
          exact PrimeSpectrum.ext hQc
    rw [ringKrullDim, ringKrullDim, Order.krullDim]
    refine iSup_le fun p => ?_
    obtain ⟨q, hlen, -⟩ := key p
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim q

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

/-- **The module of Kähler differentials of a SMOOTH finite-type domain over ANY field
has rank the Krull dimension** (PROVEN 2026-07-28).

The characteristic-free companion of `rank_kaehlerDifferential_eq_of_ringKrullDim`:
smoothness replaces perfectness of the base, because `Frac B` is then formally smooth
over `K` and `rank_kaehlerDifferential_eq_trdeg_of_formallySmooth` applies at the
generic point.  The rest is the same two moves: `Frac B` is a localization of `B`,
hence formally étale over it, so `Ω` base-changes and the rank is read at the generic
point; and there the rank is the transcendence degree, which is the dimension. -/
theorem rank_kaehlerDifferential_eq_of_ringKrullDim_of_smooth
    (K B : Type u) [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.Smooth K B] (n : ℕ) (hdim : ringKrullDim B = n) :
    Module.rank B Ω[B⁄K] = (n : Cardinal) := by
  haveI : Algebra.FormallyEtale B (FractionRing B) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType B (FractionRing B) := .of_isLocalization _ (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType K (FractionRing B) := .comp K B _
  haveI : Algebra.FormallySmooth K (FractionRing B) := .comp K B _
  rw [← (KaehlerDifferential.isBaseChange_of_formallyEtale K B (FractionRing B)).rank_eq,
    rank_kaehlerDifferential_eq_trdeg_of_formallySmooth K (FractionRing B),
    trdeg_fractionRing_eq_of_ringKrullDim K B n hdim]

/-- **A localization away from a nonzero element of a smooth finite-type domain is
standard smooth of relative dimension the Krull dimension of the domain** (PROVEN
2026-07-28).

This is the chart-level statement that makes the scheme statement below local: the
relative dimension of a chart `B_t` is read off `Module.rank B_t Ω[B_t⁄K]`
(`Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth`), and that rank
is the rank of `Ω[B⁄K]` because `Ω[B_t⁄K]` is the localization of `Ω[B⁄K]`
(`KaehlerDifferential.map` is an `IsLocalizedModule`) — so no dimension theory of the
localization is needed and, in particular, one never has to know that
`ringKrullDim B_t = ringKrullDim B`.

`t ≠ 0` is load-bearing: `Localization.Away 0` is the zero ring, whose `Ω` has rank `0`,
and the conclusion fails there for every `n ≠ 0`.  It is used twice, for `Nontrivial B_t`
and to put the powers of `t` inside the non-zero-divisors. -/
theorem isStandardSmoothOfRelativeDimension_localizationAway_of_smooth
    (K B : Type u) [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.Smooth K B] (n : ℕ) (hdim : ringKrullDim B = n)
    {Bt : Type u} [CommRing Bt] [Algebra B Bt] [Algebra K Bt] [IsScalarTower K B Bt]
    (t : B) (ht : t ≠ 0) [IsLocalization.Away t Bt] [Algebra.IsStandardSmooth K Bt] :
    Algebra.IsStandardSmoothOfRelativeDimension n K Bt := by
  have hp : Submonoid.powers t ≤ nonZeroDivisors B :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero ht)
  haveI : Nontrivial Bt := (IsLocalization.injective Bt hp).nontrivial
  have h1 : Module.rank B Ω[B⁄K] = (n : Cardinal) :=
    rank_kaehlerDifferential_eq_of_ringKrullDim_of_smooth K B n hdim
  have h2 : Module.rank Bt Ω[Bt⁄K] = Module.rank B Ω[Bt⁄K] :=
    IsLocalization.rank_eq (R := B) Bt (Submonoid.powers t) hp
  have h3 : Module.rank B Ω[Bt⁄K] = Module.rank B Ω[B⁄K] :=
    IsLocalizedModule.rank_eq (p := Submonoid.powers t) (hp := hp)
      (f := KaehlerDifferential.map K K B Bt)
  exact (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr
    (by rw [h2, h3, h1])

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

/-- **THE RELATIVE DIMENSION OF A SMOOTH AFFINE VARIETY IS ITS KRULL DIMENSION**
(opened as a sorry leaf 2026-07-28 as the residue of
`smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing` after Stacks
`056S` was discharged onto `Algebra.Smooth.of_isRegularRing_of_perfectField`;
**PROVEN 2026-07-28**, over the single new field-theoretic leaf
`Algebra.linearIndepOn_pow_of_formallySmooth` — see "How it was closed" below).

**There is no perfectness and no regularity left in this statement**, and that
is the point of the cut: everything characteristic-theoretic has been consumed
by `Fermat/FLT/Mathlib/RingTheory/Smooth/RegularLocal.lean`, and what remains is
pure dimension theory over an arbitrary field.

TRUE and classical.  `Smooth K B` gives a cover of `Spec B` by basic opens
`D(t)` with `B_t` standard smooth over `K`
(`Algebra.Smooth.exists_span_eq_top_isStandardSmooth`), and
`Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth` turns
"relative dimension `n`" on such a chart into `Module.rank B_t Ω[B_t⁄K] = n`.
So the whole content is:

* for a smooth finite-type algebra over a field, `rank Ω[B⁄K] = dim B` — the
  smooth case of "the module of differentials of a variety has rank equal to its
  dimension"; and
* `IsDomain B` is what makes that rank CONSTANT: `dim B_t = dim B` for every
  `t ≠ 0` because `B` and `B_t` are finite-type domains with the same fraction
  field, hence the same transcendence degree, hence the same dimension.

*Refute it with*: a smooth finite-type `K`-DOMAIN whose relative dimension over
`K` differs from `ringKrullDim`.  There is none.  Note `IsDomain` cannot be
dropped — see the faithfulness note on the consumer below — and `t = 0` must be
excluded from the cover, since `Localization.Away 0` is the zero ring.

## How it was closed

`HasRingHomProperty.Spec_iff` turns the goal into
`Locally (IsStandardSmoothOfRelativeDimension n) (algebraMap K B)`, i.e. into a
cover of `Spec B` by basic opens on each of which the relative dimension is `n`.
`Algebra.Smooth.exists_span_eq_top_isStandardSmooth` supplies a cover on which the
charts are standard smooth; **`0` is deleted from it by hand** (which does not
change the span), and then
`Algebra.isStandardSmoothOfRelativeDimension_localizationAway_of_smooth` reads the
relative dimension of each chart off `Module.rank B Ω[B⁄K]`.  Note that the Krull
dimension of the CHART is never mentioned: the rank, not the dimension, is what
localizes, which is why no catenary/equidimensionality theory is needed.

The one piece of real mathematics is `Module.rank B Ω[B⁄K] = ringKrullDim B` for a
smooth finite-type domain over an ARBITRARY field
(`Algebra.rank_kaehlerDifferential_eq_of_ringKrullDim_of_smooth`), and it rests on
one leaf: a formally smooth field extension is separably generated
(`Algebra.linearIndepOn_pow_of_formallySmooth`, Stacks `0323`).  That is where the
"no perfectness" of this statement is paid for — over a perfect base the same rank
computation is unconditional. -/
theorem smoothOfRelativeDimension_specMap_algebraMap_of_smooth
    (K B : Type u) [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.Smooth K B] (n : ℕ) (hdim : ringKrullDim B = n) :
    SmoothOfRelativeDimension n (Spec.map (ofHom (algebraMap K B))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  obtain ⟨s, hspan, hsm⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth K B
  refine ⟨s \ {0}, ?_, ?_⟩
  · rw [eq_top_iff, ← hspan, Ideal.span_le]
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · exact Ideal.subset_span ⟨hx, hx0⟩
  · rintro t ⟨hts, ht0⟩
    haveI := hsm t hts
    have hcomp : (algebraMap B (Localization.Away t)).comp
        ((ofHom (algebraMap K B) : CommRingCat.of K ⟶ CommRingCat.of B)).hom
        = algebraMap K (Localization.Away t) :=
      (IsScalarTower.algebraMap_eq K B (Localization.Away t)).symm
    rw [hcomp, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact Algebra.isStandardSmoothOfRelativeDimension_localizationAway_of_smooth
      K B n hdim t (by simpa using ht0)

/-- **Regular + finite type over a perfect field ⟹ smooth of relative dimension
the Krull dimension** (**PROVEN 2026-07-28**; opened as a sorry leaf 2026-07-27).

This is the ring form of Stacks `056S` ("regular is equivalent to smooth over a
perfect field"), together with the identification of the relative dimension: for
an *integral* finite-type algebra over a field the local dimensions are all
equal to `ringKrullDim`, so a single `n` governs every point.

## How it was closed, and what moved where

The `056S` half — the only half in which `PerfectField` and `IsRegularRing`
appear — is now `Algebra.Smooth.of_isRegularRing_of_perfectField` in
`Fermat/FLT/Mathlib/RingTheory/Smooth/RegularLocal.lean`, a module with **no
`Fermat` imports** that states the underlying commutative algebra ONCE:

> a regular local ring essentially of finite type over a perfect field is
> formally smooth over that field

(`Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField`), together with
its global corollary for regular rings.  The local-to-global passage is free at
this pin: `Algebra.smoothLocus_eq_univ_iff` makes `FormallySmooth K B`
equivalent to formal smoothness of every localization `B_𝔭`, and `IsRegularRing`
is by definition regularity of every `B_𝔭`, so the two definitions meet
pointwise with no covering argument.  That module in turn rests on a single
named leaf, `Algebra.injective_lTensor_residueField_kerInclusion`, which is the
first of the two arrows of the local Jacobian criterion's injectivity and
mentions no field, no perfectness and no module of differentials: for a
surjection `P ↠ S` of regular local rings, `I/𝔪_P I → 𝔪_P/𝔪_P²` is injective.
The second arrow — the one where `PerfectField` is used — is PROVEN there, by
reading mathlib's own criterion at the residue field.

What is left HERE is `smoothOfRelativeDimension_specMap_algebraMap_of_smooth`
above: pure dimension theory, no perfectness, no regularity.  The paragraph
below headed "What blocks it in the pin" is retained as the historical record of
why this leaf was opened; item 3 and the closing paragraph are now DISCHARGED.

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
whole content and it is not in the pin.  That step, and it alone, is now the leaf
`Algebra.FormallySmooth.of_isRegularLocalRing_of_perfectField`.

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

`PerfectField K` is load-bearing too, and this is not a formalisation artefact.

**COUNTEREXAMPLE CORRECTED (2026-07-28).**  This paragraph used to cite the curve
`y ^ p = t * x ^ p + t` (`t ∈ k \ k ^ p`) as "regular and not smooth".  That
witness is INVALID: in characteristic `p`, `t * x ^ p + t = t * (x + 1) ^ p`, so
after `u = x + 1` the equation reads `y ^ p = t * u ^ p`, whose defining
polynomial lies in `𝔪 ²` at the `k`-rational point `u = y = 0` — the local ring
there has `dim_k 𝔪 / 𝔪 ² = 2` in dimension one, so the curve is NOT regular (its
integral closure is the strictly larger `k (t ^ (1 / p)) [u]`).  It is also not
geometrically reduced, being `(y - t ^ (1 / p) * (x + 1)) ^ p = 0` over `k̄`.

The correct witness is the classical **quasi-elliptic** curve, which exists only
in characteristics `2` and `3`: over `k = 𝔽₃ (t)` take `B = k [x, y] / (y ² - x ³ - t)`.
It is a finite-type domain of Krull dimension one, and it is REGULAR — in
characteristic `3` the partials are `∂ / ∂ y = 2 y` and `∂ / ∂ x = - 3 x ² = 0`, so
the only candidate singular point is `y = 0`, `x ³ = - t`, a single closed point
with residue field `k (t ^ (1 / 3))`, where the maximal ideal `(y, x ³ + t)` equals
`(y)` because `x ³ + t = y ²`; a one-dimensional local ring with principal maximal
ideal is a DVR.  It is NOT smooth there: over `k̄`, `x ³ + t = (x + t ^ (1 / 3)) ³`,
so the base change is the cuspidal cubic.  Machine-checked in `Magma`: genus `1`
over `𝔽₃ (t)`, genus `0` after the purely inseparable base change `t = s ³`, a drop
of `(p - 1) / 2` as Tate's genus-change theorem permits at `p = 3`.

`ℚ` is perfect, so the modular application is unaffected. -/
theorem smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing
    (K B : Type u) [Field K] [PerfectField K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] [IsRegularRing B] (n : ℕ) (hdim : ringKrullDim B = n) :
    SmoothOfRelativeDimension n (Spec.map (ofHom (algebraMap K B))) :=
  haveI := Algebra.Smooth.of_isRegularRing_of_perfectField K B
  smoothOfRelativeDimension_specMap_algebraMap_of_smooth K B n hdim

end AlgebraicGeometry
