/-
Fermat/FLT/ModularCurve/PlaneModelFunctionField.lean — own work for the Fermat
project (not vendored from the FLT project).

# A plane model for the function field of a smooth proper curve over `𝔽_q`

This module carries the whole of
`Fermat.exists_planeModel_ringEquiv_functionField_of_isProperSmoothCurve`
(`Fermat/FLT/Modularity/Interface.lean`), which is now a one-line delegation to
`exists_planeModel_ringEquiv_functionField_specZMod` below.

## Why a separate module

`Interface.lean` sits at the very bottom of this development's import graph
(`Interface → MazurTorsion → X0 → …`), so anything proved there costs a
25-minute elaboration per iteration, and — on `merger` at release 28 — that cone
does not build at all (see the module note at the end of this docstring).  The
mathematics here needs **nothing from the project**: the statement is entirely in
mathlib's vocabulary (`Scheme`, `IsProper`, `SmoothOfRelativeDimension`,
`GeometricallyConnected`, `Scheme.functionField`, `MvPolynomial`), so it is
stated and proved here against mathlib alone, verifiable in ~90 seconds.

`Fermat.SpecF q` is `noncomputable abbrev SpecF (ℓ : ℕ) := Spec (CommRingCat.of (ZMod ℓ))`
(`X0.lean`), so the statement below is *definitionally* the one `Interface.lean`
asks for and the delegation there is an `exact`.

## Contents

* `exists_mvPolynomial_ringEquiv_fractionRing_of_trdeg_eq_one` (**PROVEN**) — the
  pure field theory: a field `K`, essentially of finite type and of transcendence
  degree `1` over a perfect field `k`, is `Frac (k[X,Y]/(F))` for an irreducible
  `F`.  This is the half the old docstring called "separating transcendence basis,
  primitive element, clearing denominators", and it is the whole of that half.
* `exists_algebra_essFiniteType_trdeg_one_functionField` (**sorry leaf**) — the
  GEOMETRY: `K(X)` is a finitely generated field extension of `𝔽_q` of
  transcendence degree `1`.
* `irreducible_map_algebraicClosure_functionField` (**sorry leaf**) — the other
  half of the geometry: `𝔽_q` is algebraically closed in `K(X)`, expressed as the
  absolute irreducibility of any plane model.
* `exists_planeModel_ringEquiv_functionField_specZMod` (**PROVEN** over the three
  above).

## How the pure field theory goes, since it is not the route the old docstring gave

The old route said "pick a separating transcendence basis, then
`Field.exists_primitive_element`, then **clear denominators from the minimal
polynomial of `y` over `𝔽_q(x)`**".  The last step is not needed and was the
expensive one.  Instead:

* `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`
  (`Mathlib/FieldTheory/SeparablyGenerated.lean`, `@[stacks 030W]`) hands over the
  separating transcendence basis outright — this is the single hardest classical
  input and it is off the shelf;
* the basis is a SINGLETON because its cardinality *is* the transcendence degree
  (`IsTranscendenceBasis.cardinalMk_eq_trdeg`);
* `Algebra.FormallyUnramified.of_isSeparable` + `.finite_of_free` upgrade
  "separable and essentially of finite type" to `Module.Finite`, which is what
  `Field.exists_primitive_element` wants;
* for `F` take a nonzero relation of `![x, y]` of MINIMAL TOTAL DEGREE.
  `MvPolynomial.irreducible_of_forall_totalDegree_le` (same mathlib file) says
  such an `F` is irreducible *outright* — no minimal polynomial, no denominators,
  no Gauss's lemma;
* the kernel is then `span {F}` by a DIMENSION count rather than by elimination
  theory: `ringKrullDim 𝔽_q[X,Y] = 2`, and two applications of
  `ringKrullDim_succ_le_of_surjective` force `ringKrullDim (𝔽_q[X,Y]/ker) ≤ 0`
  if the inclusion `span {F} ≤ ker` were strict.  A zero-dimensional domain is a
  field, so Zariski's lemma (`finite_of_finite_type_of_isJacobsonRing`,
  `@[stacks 0CY7]`) makes `x` algebraic over `𝔽_q` — contradiction;
* finally `IsFractionRing.of_field` plus `IntermediateField.mem_adjoin_iff_div`
  identify `K` with `Frac (𝔽_q[X,Y]/(F))` directly, so no `Subalgebra`/`Subring`
  transport is needed at all.

## Release-28 note (2026-07-31)

At `merger` release 28 the project does not build: there is an IMPORT CYCLE
`ModularCurve.X0 → FreyCurve.IsogenySignature → ModularCurve.HyperellipticJacobian
→ ModularCurve.X0` (the last two are non-`public` imports added by different
branches).  Nothing in this module is affected — it imports only mathlib — and it
is verified green on its own.
-/
module

public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Data.ZMod.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

@[expose] public noncomputable section

open MvPolynomial Cardinal AlgebraicGeometry

namespace Fermat

/-- `d + 2 ≤ 2` forces `d ≤ 0` in `WithBot ℕ∞`.  Stated separately because
`ringKrullDim` is `WithBot ℕ∞`-valued and neither `omega` nor `gcongr` can cancel
there: `ℕ∞` is not cancellative (`⊤ + 1 = ⊤`), so the two degenerate values have
to be dispatched by hand. -/
theorem le_zero_of_add_two_le_two (d : WithBot ℕ∞) (hd : d + 1 + 1 ≤ (2 : WithBot ℕ∞)) :
    d ≤ 0 := by
  have h2 : (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
  have h0 : (0 : WithBot ℕ∞) = ((0 : ℕ∞) : WithBot ℕ∞) := rfl
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_add, h2, WithBot.coe_le_coe] at hd
    rw [h0, WithBot.coe_le_coe]
    induction b using WithTop.recTopCoe with
    | top =>
      exfalso
      have h1 : (⊤ : ℕ∞) ≤ 2 := le_trans (le_trans le_self_add le_self_add) hd
      simp at h1
    | coe m =>
      have hd' : ((m + 1 + 1 : ℕ) : ℕ∞) ≤ ((2 : ℕ) : ℕ∞) := by push_cast; exact hd
      have hm : m + 1 + 1 ≤ 2 := by exact_mod_cast hd'
      have hm0 : m = 0 := by omega
      subst hm0
      exact le_of_eq Nat.cast_zero

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- **A FIELD OF TRANSCENDENCE DEGREE ONE, ESSENTIALLY OF FINITE TYPE OVER A
PERFECT FIELD, IS THE FUNCTION FIELD OF A PLANE CURVE** (**PROVEN** 2026-07-31).

`K ≃+* Frac (k[X,Y]/(F))` with `F` irreducible.  See the module docstring for the
route; the only non-obvious moves are that the minimal-total-degree relation is
irreducible for free (`MvPolynomial.irreducible_of_forall_totalDegree_le`) and that
`ker (aeval ![x,y]) = span {F}` is a Krull-dimension count rather than elimination
theory.

FAITHFULNESS.  `PerfectField k` is load-bearing: over an imperfect `k` a
transcendence basis need not be separating and `K` need not be generated by two
elements (`k = 𝔽_p(t)`, `K = k(u)` with `u^p = t` is generated by one, but
`k(u, v)` with `u^p = t`, `v^p = t'` over `k = 𝔽_p(t, t')` has transcendence
degree `1` over neither — the honest witness is that `Field.exists_primitive_element`
fails without separability).  `Algebra.EssFiniteType k K` is load-bearing:
`k(u₁, u₂, …)` of transcendence degree `1` over `k` but not finitely generated has
no plane model.  `trdeg = 1` is load-bearing in BOTH directions: at `trdeg = 0` the
kernel of `aeval ![x,y]` is maximal, not principal, and at `trdeg = 2` there is no
nonzero relation at all. -/
theorem exists_mvPolynomial_ringEquiv_fractionRing_of_trdeg_eq_one
    (k K : Type) [Field k] [PerfectField k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (htr : Algebra.trdeg k K = 1) :
    ∃ F : MvPolynomial (Fin 2) k, Irreducible F ∧
      Nonempty (K ≃+* FractionRing (MvPolynomial (Fin 2) k ⧸ Ideal.span {F})) := by
  classical
  -- STEP 1: a separating transcendence basis, necessarily a singleton `{x}`.
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hmk : #{ a // a ∈ s } = 1 := by rw [hs.cardinalMk_eq_trdeg, htr]
  have hcard : s.card = 1 := by
    have h2 : ((s.card : ℕ) : Cardinal) = 1 := by rw [← Cardinal.mk_coe_finset]; exact hmk
    exact_mod_cast h2
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
  have hxtr : Transcendental k x := by
    have := hs.1.transcendental ⟨x, Finset.mem_singleton_self x⟩
    simpa using this
  have hcoe : (({x} : Finset K) : Set K) = ({x} : Set K) := by simp
  have hsep' : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set K)) K := by
    rw [hcoe] at hsep; exact hsep
  -- STEP 2: `K` is finite over `k(x)`, so it has a primitive element `y`.
  haveI := hsep'
  haveI : Algebra.EssFiniteType (IntermediateField.adjoin k ({x} : Set K)) K :=
    Algebra.EssFiniteType.of_comp k (IntermediateField.adjoin k ({x} : Set K)) K
  haveI : Algebra.FormallyUnramified (IntermediateField.adjoin k ({x} : Set K)) K :=
    Algebra.FormallyUnramified.of_isSeparable _ K
  haveI : Module.Finite (IntermediateField.adjoin k ({x} : Set K)) K :=
    Algebra.FormallyUnramified.finite_of_free _ K
  haveI : FiniteDimensional (IntermediateField.adjoin k ({x} : Set K)) K := inferInstance
  obtain ⟨y, hy⟩ := Field.exists_primitive_element
    (IntermediateField.adjoin k ({x} : Set K)) K
  have htop : IntermediateField.adjoin k ({x, y} : Set K) = ⊤ := by
    have h1 := IntermediateField.adjoin_simple_adjoin_simple k x y
    rw [hy] at h1
    simpa using h1.symm
  -- STEP 3: a relation of `a = ![x, y]` of minimal total degree is irreducible.
  set a : Fin 2 → K := ![x, y] with ha
  set ψ : MvPolynomial (Fin 2) k →ₐ[k] K := MvPolynomial.aeval a with hψ
  have hnotind : ¬ AlgebraicIndependent k a := by
    intro hind
    have hlt : Algebra.trdeg k K < ℵ₀ := by rw [htr]; exact one_lt_aleph0
    have hle : Algebra.trdeg k K ≤ #(Fin 2) := by rw [htr]; simp
    have hb := hind.isTranscendenceBasis_of_trdeg_le hlt hle
    have h2 := hb.cardinalMk_eq_trdeg
    rw [htr] at h2
    simp at h2
  have hex : ∃ n : ℕ, ∃ G : MvPolynomial (Fin 2) k, G ≠ 0 ∧ ψ G = 0 ∧ G.totalDegree = n := by
    rw [algebraicIndependent_iff_injective_aeval] at hnotind
    rw [injective_iff_map_eq_zero] at hnotind
    push Not at hnotind
    obtain ⟨G, hG1, hG2⟩ := hnotind
    exact ⟨G.totalDegree, G, hG2, hG1, rfl⟩
  obtain ⟨F, hF0, hFa, hFdeg⟩ := Nat.find_spec hex
  have hmin : ∀ G : MvPolynomial (Fin 2) k, G ≠ 0 → ψ G = 0 →
      F.totalDegree ≤ G.totalDegree := by
    intro G hG0 hGa
    rw [hFdeg]
    exact Nat.find_le ⟨G, hG0, hGa, rfl⟩
  have hFirr : Irreducible F := MvPolynomial.irreducible_of_forall_totalDegree_le hmin hF0 hFa
  refine ⟨F, hFirr, ?_⟩
  -- STEP 4: the kernel is exactly `span {F}` — a Krull-dimension count.
  haveI hFprime : (Ideal.span {F} : Ideal (MvPolynomial (Fin 2) k)).IsPrime :=
    (Ideal.span_singleton_prime hFirr.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hFirr)
  haveI hPprime : (RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)).IsPrime :=
    RingHom.ker_isPrime _
  have hle : Ideal.span {F} ≤ RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K) := by
    rw [Ideal.span_le]
    simpa [RingHom.mem_ker] using hFa
  have hdimR : ringKrullDim (MvPolynomial (Fin 2) k) = 2 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hker : RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K) = Ideal.span {F} := by
    by_contra hne
    obtain ⟨g, hgP, hgnot⟩ : ∃ g ∈ RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K),
        g ∉ Ideal.span {F} := by
      by_contra hc
      push Not at hc
      exact hne (le_antisymm hc hle)
    have hgne : (Ideal.Quotient.mk (Ideal.span {F}) g) ≠ 0 := by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hgnot
    have hnzd : (Ideal.Quotient.mk (Ideal.span {F}) g) ∈
        nonZeroDivisors (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hgne
    have hstep1 :
        ringKrullDim (MvPolynomial (Fin 2) k ⧸ RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K))
          + 1 ≤ ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) :=
      ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
        (Ideal.Quotient.factor_surjective hle) hnzd
        (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hgP)
    have hstep2 : ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) + 1
        ≤ ringKrullDim (MvPolynomial (Fin 2) k) :=
      ringKrullDim_quotient_succ_le_of_nonZeroDivisor
        (mem_nonZeroDivisors_iff_ne_zero.mpr hF0)
    have hdimP : ringKrullDim (MvPolynomial (Fin 2) k ⧸
        RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) ≤ 0 := by
      refine le_zero_of_add_two_le_two _ ?_
      calc ringKrullDim (MvPolynomial (Fin 2) k ⧸
              RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) + 1 + 1
          ≤ ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) + 1 := by gcongr
        _ ≤ ringKrullDim (MvPolynomial (Fin 2) k) := hstep2
        _ = 2 := hdimR
    haveI : Ring.KrullDimLE 0
        (MvPolynomial (Fin 2) k ⧸ RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) :=
      Ring.krullDimLE_iff.mpr (by simpa using hdimP)
    haveI : IsDomain (MvPolynomial (Fin 2) k ⧸ RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) :=
      Ideal.Quotient.isDomain _
    have hbotmax : (⊥ : Ideal (MvPolynomial (Fin 2) k ⧸
        RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K))).IsMaximal :=
      Ideal.isMaximal_of_isPrime (I := ⊥)
    have hfield : IsField (MvPolynomial (Fin 2) k ⧸
        RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) :=
      Ring.isField_iff_maximal_bot.mpr hbotmax
    letI : Field (MvPolynomial (Fin 2) k ⧸ RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) :=
      hfield.toField
    haveI : Algebra.FiniteType k
        (MvPolynomial (Fin 2) k ⧸ RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) :=
      Algebra.FiniteType.of_surjective
        (Ideal.Quotient.mkₐ k (RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)))
        Ideal.Quotient.mk_surjective
    haveI : Module.Finite k (MvPolynomial (Fin 2) k ⧸
        RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) :=
      finite_of_finite_type_of_isJacobsonRing k _
    haveI : Algebra.IsIntegral k (MvPolynomial (Fin 2) k ⧸
        RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) := Algebra.IsIntegral.of_finite k _
    have hint : IsIntegral k x := by
      have h0 : IsIntegral k (Ideal.Quotient.mk
          (RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) (MvPolynomial.X 0)) :=
        Algebra.IsIntegral.isIntegral _
      have himg := h0.map (Ideal.Quotient.liftₐ
        (RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K)) ψ (fun b hb => hb))
      simpa [hψ, ha] using himg
    exact hxtr hint.isAlgebraic
  -- STEP 5: `K` IS the fraction field of `k[X,Y] ⧸ span {F}`.
  have hrangeset : Set.range a = ({x, y} : Set K) := by
    apply Set.eq_of_subset_of_subset
    · rintro z ⟨i, rfl⟩
      fin_cases i <;> simp [ha]
    · rintro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨0, by simp [ha]⟩
      · exact ⟨1, by simp [ha]⟩
  have hrange : ψ.range = Algebra.adjoin k ({x, y} : Set K) := by
    have h1 : Algebra.adjoin k (Set.range a) = (MvPolynomial.aeval a).range :=
      Algebra.adjoin_range_eq_range_aeval k a
    rw [hrangeset] at h1
    rw [hψ]
    exact h1.symm
  letI : Algebra (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) K :=
    (Ideal.Quotient.lift (Ideal.span {F}) (ψ : MvPolynomial (Fin 2) k →+* K)
      (fun b hb => by rw [← hker] at hb; exact hb)).toAlgebra
  have hmapeq : ∀ u : MvPolynomial (Fin 2) k,
      algebraMap (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) K
        (Ideal.Quotient.mk (Ideal.span {F}) u) = ψ u :=
    fun u => Ideal.Quotient.lift_mk _ _ _
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) K) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [hmapeq] at hw
    have hv : v ∈ RingHom.ker (ψ : MvPolynomial (Fin 2) k →+* K) := hw
    rw [hker] at hv
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hv
  haveI : FaithfulSMul (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) K :=
    (faithfulSMul_iff_algebraMap_injective _ K).mpr hinj
  haveI : IsFractionRing (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) K := by
    refine IsFractionRing.of_field _ K ?_
    intro z
    have hz : z ∈ IntermediateField.adjoin k ({x, y} : Set K) := by rw [htop]; trivial
    obtain ⟨r, hr, t, ht, hrt⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    rw [← hrange] at hr ht
    obtain ⟨u, hu⟩ := hr
    obtain ⟨v, hv⟩ := ht
    have hu' : ψ u = r := hu
    have hv' : ψ v = t := hv
    refine ⟨Ideal.Quotient.mk _ u, Ideal.Quotient.mk _ v, ?_⟩
    rw [hmapeq, hmapeq, hu', hv']
    exact hrt
  exact ⟨(FractionRing.algEquiv (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) K).symm.toRingEquiv⟩

/-- **THE FUNCTION FIELD OF A SMOOTH PROPER GEOMETRICALLY CONNECTED CURVE OVER
`𝔽_q` IS A FINITELY GENERATED EXTENSION OF TRANSCENDENCE DEGREE ONE** (sorry
leaf, 2026-07-31, cut out of
`exists_planeModel_ringEquiv_functionField_of_isProperSmoothCurve`).

STATEMENT.  For `strX : X ⟶ Spec 𝔽_q` proper, smooth of relative dimension `1`
and geometrically connected, `K(X)` carries an `𝔽_q`-algebra structure for which
it is essentially of finite type and has `Algebra.trdeg 𝔽_q K(X) = 1`.

WHY THE ALGEBRA STRUCTURE IS EXISTENTIALLY QUANTIFIED, AND WHY THAT IS NOT THE
JUNK-WITNESS TRAP.  `ZMod q` is a QUOTIENT OF `ℤ`, so `RingHom.ext_zmod` makes
`ZMod q →+* K(X)` a subsingleton: there is AT MOST ONE `𝔽_q`-algebra structure on
`K(X)`, and the `∃` therefore pins it exactly.  (This is the same observation
that makes `Interface.lean`'s `hom_specF_eq_of_affine` work.)  Quantifying it
away is what keeps this statement free of any project vocabulary — the structure
morphism `strX` would otherwise have to be turned into an `algebraMap` by hand,
through `Scheme.ΓSpecIso`, `Scheme.Hom.appTop` and `Scheme.germToFunctionField`,
which is bookkeeping the consumer does not need: the target's conclusion is a
BARE `RingEquiv` and mentions no `𝔽_q`-structure at all.

ROUTE.  Take any nonempty affine open `U ⊆ X`.  Then

* `Γ(X, U)` is a finite-type `𝔽_q`-algebra, because `IsProper` extends
  `LocallyOfFiniteType` and `HasRingHomProperty.appLE` reads that off on an
  affine; it is a domain because `X` is integral
  (`isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`,
  `CurveExtension.lean`);
* `K(X) = Frac Γ(X, U)` is `AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen`
  (`Mathlib/AlgebraicGeometry/FunctionField.lean:148`).  `Algebra.EssFiniteType`
  then follows from `Algebra.EssFiniteType.of_isLocalization` composed with
  `Algebra.EssFiniteType.of_finiteType`;
* `Algebra.trdeg 𝔽_q (Frac Γ(X, U)) = ringKrullDim Γ(X, U)` is the project's own
  `trdeg_fractionRing_eq_of_ringKrullDim`
  (`Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean:842`,
  Stacks 00OS/00P0, PROVEN and NOT in mathlib);
* so what is left is `ringKrullDim Γ(X, U) = 1`.  The `≤ 1` half is
  `topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one`
  (`CurveCompactification.lean:3288`).  The `≥ 1` half — equivalently, that `X`
  is not a finite `𝔽_q`-scheme — is the only genuinely new work; it is where
  `SmoothOfRelativeDimension 1` is spent, and the cheapest formal route is
  probably `rank_kaehlerDifferential_eq_of_ringKrullDim_of_smooth`
  (same project file) read backwards from `Module.rank Γ Ω[Γ⁄𝔽_q] = 1`.

FAITHFULNESS.  TRUE.  `GeometricallyConnected` is load-bearing: it excludes
`X = ∅`, where `IrreducibleSpace X` fails and the statement cannot even be
formed; `[IsIntegral X]` is carried for the same reason and is discharged by the
consumer from the other three hypotheses.  `SmoothOfRelativeDimension 1` is
load-bearing for `trdeg = 1` (at relative dimension `0` the transcendence degree
is `0` and at `2` it is `2`).  NOT vacuous: `X = ℙ¹_{𝔽_q}` satisfies every
hypothesis, and there `K(X) = 𝔽_q(t)` has transcendence degree `1`.

DO NOT WEAKEN `= 1` TO `≤ 1`: the consumer needs the lower bound, because at
`trdeg = 0` the relation ideal of `![x, y]` is maximal rather than principal and
the plane model does not exist. -/
theorem exists_algebra_essFiniteType_trdeg_one_functionField
    {q : ℕ} [Fact q.Prime] {X : Scheme.{0}} (strX : X ⟶ Spec (CommRingCat.of (ZMod q)))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX] [GeometricallyConnected strX]
    [AlgebraicGeometry.IsIntegral X] :
    ∃ alg : Algebra (ZMod q) ↥X.functionField,
      @Algebra.EssFiniteType (ZMod q) ↥X.functionField _ _ alg ∧
        @Algebra.trdeg (ZMod q) ↥X.functionField _ _ alg = 1 :=
  sorry

/-- **`𝔽_q` IS ALGEBRAICALLY CLOSED IN THE FUNCTION FIELD OF A SMOOTH PROPER
GEOMETRICALLY CONNECTED CURVE — EQUIVALENTLY, EVERY PLANE MODEL IS ABSOLUTELY
IRREDUCIBLE** (sorry leaf, 2026-07-31, cut out of
`exists_planeModel_ringEquiv_functionField_of_isProperSmoothCurve`).

STATEMENT.  If `F ∈ 𝔽_q[X,Y]` is irreducible and `Frac (𝔽_q[X,Y]/(F)) ≅ K(X)` as
bare rings, then `F ⊗ 𝔽̄_q` is irreducible in `𝔽̄_q[X,Y]`.

WHY IT IS STATED THIS WAY.  The mathematical content is "`𝔽_q` is algebraically
closed in `K(X)`", i.e. `K(X)` is a GEOMETRICALLY INTEGRAL `𝔽_q`-algebra, and
this is where `GeometricallyConnected` is spent for the second time.  Phrasing it
as a statement about `F` bundles that geometry together with the (routine but
real) commutative algebra that transports it to the plane model, so that the
consumer needs nothing else.  The two-step route is:

1. `X` proper smooth geometrically connected over a field is GEOMETRICALLY
   INTEGRAL (`X_{𝔽̄_q}` is connected by hypothesis and regular by smoothness,
   hence irreducible and reduced), so `𝔽̄_q ⊗_{𝔽_q} K(X)` is a DOMAIN;
2. writing `A = 𝔽_q[X,Y]/(F)`, the map `𝔽̄_q ⊗ A → 𝔽̄_q ⊗ K(X)` is injective
   (`𝔽̄_q` is free over `𝔽_q`, hence flat), so `𝔽̄_q ⊗ A ≅ 𝔽̄_q[X,Y]/(F ⊗ 𝔽̄_q)`
   is a domain, so `(F ⊗ 𝔽̄_q)` is prime, so `F ⊗ 𝔽̄_q` is irreducible
   (`Ideal.span_singleton_prime`, using `F ≠ 0` and injectivity of
   `MvPolynomial.map`).

WHAT IS NOT NEEDED.  The CONVERSE direction — absolute irreducibility descending
to irreducibility over `𝔽_q` — is already PROVEN in `Interface.lean` as
`irreducible_of_irreducible_map_algebraicClosure`, and is not what this leaf is
about; do not confuse the two.  `Irreducible F` is passed in rather than derived
so that step 2 can use `F ≠ 0`.

FAITHFULNESS.  TRUE.  `GeometricallyConnected` is load-bearing and the leaf is
FALSE without it: for `X = Spec 𝔽_{q²}` (proper, smooth of relative dimension `0`
— take a product with a curve to fix the dimension) the function field contains
`𝔽_{q²}`, and a plane model of `𝔽_{q²}(t)` over `𝔽_q` is `Y² − c` for a
non-square `c`, which SPLITS over `𝔽̄_q`.  The hypothesis `Irreducible F` is not
load-bearing for truth but is available at the call site for free and makes step
2 shorter.  NOT vacuous — an inhabitant of the hypotheses exists (`X = ℙ¹`,
`F = Y`, `Frac (𝔽_q[X,Y]/(Y)) = 𝔽_q(X) = K(ℙ¹)`), and there `F ⊗ 𝔽̄_q = Y` is
indeed irreducible. -/
theorem irreducible_map_algebraicClosure_functionField
    {q : ℕ} [Fact q.Prime] {X : Scheme.{0}} (strX : X ⟶ Spec (CommRingCat.of (ZMod q)))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX] [GeometricallyConnected strX]
    [AlgebraicGeometry.IsIntegral X]
    (F : MvPolynomial (Fin 2) (ZMod q)) (hF : Irreducible F)
    (e : ↥X.functionField ≃+*
      FractionRing (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})) :
    Irreducible (MvPolynomial.map
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) F) :=
  sorry

/-- **A PLANE MODEL OF THE FUNCTION FIELD, AS A BARE `RingEquiv`** (**PROVEN**
2026-07-31 over the three declarations above).

This is `Fermat.exists_planeModel_ringEquiv_functionField_of_isProperSmoothCurve`
(`Fermat/FLT/Modularity/Interface.lean`) with `Fermat.SpecF q` unfolded to its
definition `Spec (CommRingCat.of (ZMod q))`, so that this module needs no project
import at all.  The two are definitionally equal (`SpecF` is an `abbrev`) and the
declaration in `Interface.lean` is a one-line `exact` over this one.

The assembly is three steps: `ZMod q` is a finite field hence perfect; the
geometry leaf supplies the `𝔽_q`-structure on `K(X)` together with
`EssFiniteType` and `trdeg = 1`; the field-theory theorem then produces `F` and
the ring isomorphism, and the second geometry leaf upgrades `Irreducible F` to
absolute irreducibility. -/
theorem exists_planeModel_ringEquiv_functionField_specZMod
    {q : ℕ} [Fact q.Prime] {X : Scheme.{0}} (strX : X ⟶ Spec (CommRingCat.of (ZMod q)))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX] [GeometricallyConnected strX]
    [AlgebraicGeometry.IsIntegral X] :
    ∃ F : MvPolynomial (Fin 2) (ZMod q),
      Irreducible (MvPolynomial.map
        (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) F) ∧
      Nonempty (↥X.functionField ≃+*
        FractionRing (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})) := by
  obtain ⟨alg, hess, htr⟩ := exists_algebra_essFiniteType_trdeg_one_functionField strX
  letI := alg
  haveI := hess
  obtain ⟨F, hFirr, ⟨e⟩⟩ :=
    exists_mvPolynomial_ringEquiv_fractionRing_of_trdeg_eq_one (ZMod q) ↥X.functionField htr
  exact ⟨F, irreducible_map_algebraicClosure_functionField strX F hFirr e, ⟨e⟩⟩

end Fermat

end
