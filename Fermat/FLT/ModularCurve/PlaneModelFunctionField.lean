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
STATEMENT here is entirely in mathlib's vocabulary (`Scheme`, `IsProper`,
`SmoothOfRelativeDimension`, `GeometricallyConnected`, `Scheme.functionField`,
`MvPolynomial`), which is what lets it be stated and proved outside that cone.

Until 2026-08-02 the PROOFS needed nothing from the project either.  They now use
one project theorem — `Algebra.rank_kaehlerDifferential_eq_trdeg_of_formallySmooth`
from `Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean`, MacLane's
criterion, which is genuinely not in mathlib at this pin — so this module now
imports that one file.  That adds four mathlib-facing modules to the closure and no
cycle (the only consumer of this module is `Interface.lean`, which none of them
reaches); a scratch round trip against the built oleans is still ~12 seconds.

`Fermat.SpecF q` is `noncomputable abbrev SpecF (ℓ : ℕ) := Spec (CommRingCat.of (ZMod ℓ))`
(`X0.lean`), so the statement below is *definitionally* the one `Interface.lean`
asks for and the delegation there is an `exact`.

## Contents

* `exists_mvPolynomial_ringEquiv_fractionRing_of_trdeg_eq_one` (**PROVEN**) — the
  pure field theory: a field `K`, essentially of finite type and of transcendence
  degree `1` over a perfect field `k`, is `Frac (k[X,Y]/(F))` for an irreducible
  `F`.  This is the half the old docstring called "separating transcendence basis,
  primitive element, clearing denominators", and it is the whole of that half.
* `essFiniteType_and_trdeg_of_isStandardSmoothOfRelativeDimension` (**PROVEN**) —
  the fraction field of a standard smooth domain of relative dimension `n` over a
  field is essentially of finite type of transcendence degree `n`.  No dimension
  theory: the rank of `Ω` is read off the standard smooth presentation directly.
* `exists_algebra_essFiniteType_trdeg_one_functionField` (**PROVEN** 2026-08-02) —
  the GEOMETRY: `K(X)` is a finitely generated field extension of `𝔽_q` of
  transcendence degree `1`.  Note this does NOT go through `ringKrullDim`; see its
  docstring for why that route reduces to another open leaf and closes nothing.
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
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Etale.Kaehler
-- The ONLY project import, and it buys exactly one theorem:
-- `Algebra.rank_kaehlerDifferential_eq_trdeg_of_formallySmooth`
-- (`Module.rank L Ω[L⁄K] = Algebra.trdeg K L` for a formally smooth `L/K` of finite
-- type), which is PROVEN there over MacLane's separability criterion and is not in
-- mathlib at this pin.  It adds four modules to this module's closure
-- (`SmoothConnectedCriteria`, `RegularStalks`, `IrreducibleNhds`,
-- `RingTheory.Smooth.RegularLocal`), all of them mathlib-facing, and creates no
-- cycle: the only consumer of THIS module is `Modularity/Interface.lean`, which none
-- of the four reaches.
public import Fermat.FLT.Mathlib.AlgebraicGeometry.SmoothConnectedCriteria
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveExtension
public import Fermat.FLT.Mathlib.AlgebraicGeometry.ProperPushforward
public import Fermat.FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothReduced
public import Fermat.FLT.Mathlib.RingTheory.InvariantCoarseRing

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

/-- **THE FRACTION FIELD OF A STANDARD SMOOTH DOMAIN OF RELATIVE DIMENSION `n` OVER A
FIELD IS ESSENTIALLY OF FINITE TYPE OF TRANSCENDENCE DEGREE `n`** (PROVEN 2026-08-02).

The characteristic-free, dimension-theory-free companion of
`Algebra.trdeg_fractionRing_eq_of_ringKrullDim`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean`): that one reads
the transcendence degree off `ringKrullDim B`, this one reads it off the RELATIVE
DIMENSION of a standard smooth presentation, which is available directly from
`SmoothOfRelativeDimension` at the scheme level and needs no dimension theory at all.

Three moves, all off the shelf:

* `Module.rank B Ω[B⁄K] = n` is
  `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` (mathlib);
* `L` is a localization of `B`, hence formally étale over it, so `Ω` base-changes and
  `Module.rank L Ω[L⁄K] = Module.rank B Ω[B⁄K]`
  (`KaehlerDifferential.isBaseChange_of_formallyEtale`);
* `Module.rank L Ω[L⁄K] = Algebra.trdeg K L` is
  `Algebra.rank_kaehlerDifferential_eq_trdeg_of_formallySmooth`, which is where
  MacLane's criterion is spent and is the one thing not in mathlib.

`L` is taken as a parameter with `[IsFractionRing B L]` rather than as `FractionRing B`
so that the consumer can feed it `X.functionField` directly — the geometric statement
identifies `K(X)` with `Frac Γ(X, V)` through `IsFractionRing` and never through a
`RingEquiv`, so no transport is needed anywhere.

WHERE THIS BELONGS: beside `rank_kaehlerDifferential_eq_of_ringKrullDim_of_smooth` in
`SmoothConnectedCriteria.lean`.  It is stated here because it has exactly one consumer,
immediately below, and that file is large and concurrently edited; hoisting it is a
pure move whenever a second consumer appears. -/
theorem essFiniteType_and_trdeg_of_isStandardSmoothOfRelativeDimension
    (K B L : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K B]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [IsScalarTower K B L] :
    Algebra.EssFiniteType K L ∧ Algebra.trdeg K L = (n : Cardinal) := by
  haveI : Algebra.IsStandardSmooth K B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := n)
  haveI : Algebra.Smooth K B := inferInstance
  haveI : Algebra.EssFiniteType K B := Algebra.EssFiniteType.of_finiteType K B
  haveI : Algebra.FormallyEtale B L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType B L :=
    Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.comp K B L
  haveI : Algebra.FormallySmooth K L := Algebra.FormallySmooth.comp K B L
  refine ⟨inferInstance, ?_⟩
  have hrank : Module.rank B Ω[B⁄K] = (n : Cardinal) :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  have hbc : Module.rank L Ω[L⁄K] = Module.rank B Ω[B⁄K] :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale K B L).rank_eq
  have htr : Module.rank L Ω[L⁄K] = Algebra.trdeg K L :=
    Algebra.rank_kaehlerDifferential_eq_trdeg_of_formallySmooth K L
  rw [← htr, hbc, hrank]

/-- **THE FUNCTION FIELD OF A SMOOTH PROPER GEOMETRICALLY CONNECTED CURVE OVER
`𝔽_q` IS A FINITELY GENERATED EXTENSION OF TRANSCENDENCE DEGREE ONE** (**PROVEN**
2026-08-02; cut out of
`exists_planeModel_ringEquiv_functionField_of_isProperSmoothCurve` on 2026-07-31).

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

**PROVEN 2026-08-02.  THE KRULL DIMENSION IS A DETOUR, AND IT WAS THE WHOLE OF THE
RECORDED COST.**  The route recorded here until then (kept below, struck, because
its dead end is worth knowing) went
`trdeg = ringKrullDim Γ(X, U)` and then owed `ringKrullDim Γ(X, U) = 1`, calling the
`≥ 1` half "the only genuinely new work".  That half is genuinely missing — and it is
missing as an OPEN SORRY LEAF, `AlgebraicGeometry.ringKrullDim_eq_of_smoothOfRelativeDimension`
(`SmoothConnectedCriteria.lean:1304`), whose own docstring records that mathlib has no
`ringKrullDim`-of-a-quotient-by-a-regular-sequence and no `ringKrullDim`-vs-`trdeg`
theorem at all.  So the recorded route reduces this leaf to another open leaf and
closes nothing.

`ringKrullDim` never has to be mentioned.  What `SmoothOfRelativeDimension 1` gives at
a point is an affine open `V ∋ x` with `Γ(X, V)` STANDARD SMOOTH OF RELATIVE DIMENSION
`1` over the base, and for such an algebra the rank of `Ω` is `1` OUTRIGHT
(`Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`, mathlib).  The
transcendence degree is that same rank, so the two are connected without any dimension
theory in between:

* `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension x` hands over
  `U`, `V`, `e : V ≤ strX ⁻¹ᵁ U` and standard smoothness of `strX.appLE U V e`.  `U = ⊤`
  because `Spec` of a FIELD is a one-point space (`instance [Field K] : Unique (Spec (.of K))`)
  and `U` is nonempty (it contains `strX.base x`);
* `Γ(Spec 𝔽_q, ⊤) ≅ 𝔽_q` (`Scheme.ΓSpecIso`) is bijective, hence standard smooth of
  relative dimension `0` (`of_algebraMap_bijective`), so
  `IsStandardSmoothOfRelativeDimension.trans` gives relative dimension `1 + 0` over
  `𝔽_q` itself.  This is the only place the base is used, and it is where a base that
  is not a field would break;
* the rest is `essFiniteType_and_trdeg_of_isStandardSmoothOfRelativeDimension` above,
  pure algebra, at `n = 1`, with `K(X) = Frac Γ(X, V)` supplied by
  `AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen`.

Note `IsProper` is NOT used, and neither is `GeometricallyConnected` except through the
`[IsIntegral X]` instance the consumer discharges from it; both are kept because the
call site holds them for free and dropping them would move a signature.  The honest
statement is that this is true for any smooth-of-relative-dimension-`1` integral scheme
over a field.

~~ROUTE (superseded).  Take any nonempty affine open `U ⊆ X`.  Then `Γ(X, U)` is a
finite-type `𝔽_q`-algebra and a domain, `K(X) = Frac Γ(X, U)`, and
`Algebra.trdeg 𝔽_q (Frac Γ(X, U)) = ringKrullDim Γ(X, U)` by the project's own
`trdeg_fractionRing_eq_of_ringKrullDim`; so what is left is `ringKrullDim Γ(X, U) = 1`,
whose `≤ 1` half is `topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one`
(`CurveCompactification.lean`) and whose `≥ 1` half is open.~~

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
        @Algebra.trdeg (ZMod q) ↥X.functionField _ _ alg = 1 := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hU, V, hV, hxV, e, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := strX) x
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  -- `Spec` of a field is a one-point space, so the nonempty `U` handed over is `⊤`.
  have hUtop : U = ⊤ := by
    ext y
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hy : y = strX.base x := Subsingleton.elim _ _
    rw [hy]
    exact e hxV
  subst hUtop
  letI algA : Algebra (ZMod q) ↥Γ(Spec (CommRingCat.of (ZMod q)), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (ZMod q))).inv).hom.toAlgebra
  letI algB : Algebra ↥Γ(Spec (CommRingCat.of (ZMod q)), ⊤) ↥Γ(X, V) :=
    (strX.appLE ⊤ V e).hom.toAlgebra
  letI algAB : Algebra (ZMod q) ↥Γ(X, V) :=
    (((strX.appLE ⊤ V e).hom).comp
      ((Scheme.ΓSpecIso (CommRingCat.of (ZMod q))).inv).hom).toAlgebra
  haveI : IsScalarTower (ZMod q) ↥Γ(Spec (CommRingCat.of (ZMod q)), ⊤) ↥Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- `𝔽_q ≅ Γ(Spec 𝔽_q, ⊤)` is bijective, hence of relative dimension `0`; composing
  -- transports the relative dimension `1` from the base `Γ(Spec 𝔽_q, ⊤)` to `𝔽_q`.
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (ZMod q)
      ↥Γ(Spec (CommRingCat.of (ZMod q)), ⊤) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
      (Scheme.ΓSpecIso (CommRingCat.of (ZMod q))).symm.commRingCatIsoToRingEquiv.bijective
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1
      ↥Γ(Spec (CommRingCat.of (ZMod q)), ⊤) ↥Γ(X, V) := hss
  haveI h10 : Algebra.IsStandardSmoothOfRelativeDimension (1 + 0) (ZMod q) ↥Γ(X, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans (n := 0) (m := 1) (R := ZMod q)
      (S := ↥Γ(Spec (CommRingCat.of (ZMod q)), ⊤)) (T := ↥Γ(X, V))
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 (ZMod q) ↥Γ(X, V) := by
    simpa using h10
  haveI : IsDomain ↥Γ(X, V) := inferInstance
  haveI : IsFractionRing ↥Γ(X, V) ↥X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  letI algK : Algebra (ZMod q) ↥X.functionField :=
    ((algebraMap ↥Γ(X, V) ↥X.functionField).comp
      (algebraMap (ZMod q) ↥Γ(X, V))).toAlgebra
  haveI : IsScalarTower (ZMod q) ↥Γ(X, V) ↥X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨hef, htr⟩ := essFiniteType_and_trdeg_of_isStandardSmoothOfRelativeDimension
    (ZMod q) ↥Γ(X, V) ↥X.functionField 1
  exact ⟨algK, hef, by simpa using htr⟩

/-- **A RING MAP TO THE PRIME FIELD FORCES DEGREE ONE** (PROVEN).

A ring hom `θ : L →+* ZMod q` out of a field `L` that is finite over `ZMod q` forces
`finrank (ZMod q) L = 1`.

No compatibility between `θ` and the `ZMod q`-algebra structures has to be assumed: `ZMod q`
is a quotient of `ℤ`, so `RingHom.ext_zmod` makes `ZMod q →+* R` a subsingleton and `θ` is
automatically `ZMod q`-linear.  That is the only reason the consumer below may read a bare
scheme-theoretic `Γ`-map as a map of `𝔽_q`-algebras without producing a single commuting
square. -/
theorem finrank_eq_one_of_ringHom_zmod {q : ℕ} [Fact q.Prime] (L : Type) [Field L]
    [Algebra (ZMod q) L] [Module.Finite (ZMod q) L] (θ : L →+* ZMod q) :
    Module.finrank (ZMod q) L = 1 := by
  have hcomp : θ.comp (algebraMap (ZMod q) L) = RingHom.id (ZMod q) :=
    RingHom.ext_zmod _ _
  have hsmul : ∀ (c : ZMod q) (x : L), θ (c • x) = c • θ x := by
    intro c x
    rw [Algebra.smul_def, map_mul, smul_eq_mul]
    congr 1
    exact congrFun (congrArg (fun f : (ZMod q) →+* (ZMod q) => (f : ZMod q → ZMod q)) hcomp) c
  let θl : L →ₗ[ZMod q] ZMod q :=
    { toFun := θ, map_add' := θ.map_add, map_smul' := fun c x => hsmul c x }
  have hinj : Function.Injective θl := θ.injective
  have hle : Module.finrank (ZMod q) L ≤ Module.finrank (ZMod q) (ZMod q) :=
    θl.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at hle
  have hpos : 0 < Module.finrank (ZMod q) L := Module.finrank_pos
  omega

/-- **AN ELEMENT WHOSE MINIMAL POLYNOMIAL HAS DEGREE ONE LIES IN THE BASE FIELD** (PROVEN). -/
theorem mem_bot_of_natDegree_minpoly_eq_one {k E : Type} [Field k] [Field E] [Algebra k E]
    {z : E} (hz : IsIntegral k z) (h : (minpoly k z).natDegree = 1) :
    z ∈ (⊥ : IntermediateField k E) := by
  have hmonic : (minpoly k z).Monic := minpoly.monic hz
  have heq : minpoly k z = Polynomial.X + Polynomial.C ((minpoly k z).coeff 0) :=
    hmonic.eq_X_add_C h
  have h0 : Polynomial.aeval z (minpoly k z) = 0 := minpoly.aeval k z
  rw [heq] at h0
  simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C] at h0
  have : z = algebraMap k E (-(minpoly k z).coeff 0) := by
    rw [map_neg]; linear_combination h0
  rw [this]
  exact IntermediateField.algebraMap_mem _ _

/-- **`𝔽_q` IS ALGEBRAICALLY CLOSED IN THE FUNCTION FIELD OF A SMOOTH PROPER GEOMETRICALLY
CONNECTED CURVE** (**PROVEN** 2026-08-02) — the geometric half of
`irreducible_map_algebraicClosure_functionField`.

THE ARGUMENT, and it needs neither normality of `X` nor a single gluing.  Let
`z ∈ K(X)` be integral over `𝔽_q` and nonzero.

1. `Γ(X, ⊤) = 𝔽_q`.  This is `isIso_appTop_of_isProper_over_field`
   (`Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean`), whose geometric-reducedness
   hypothesis is discharged by `GeometricallyReduced.of_smooth`.  This is where
   `GeometricallyConnected` is spent, and it is the ONLY place.
2. `z` is a unit on some affine open.  `AlgebraicGeometry.exists_isUnit_germ_eq` (mathlib)
   hands over an affine `U`, a section `f' ∈ Γ(X, U)` and `germ f' = z`.
3. `L := AdjoinRoot (minpoly 𝔽_q z)` is a finite field extension of `𝔽_q`, and `f'` gives a
   ring map `L → Γ(X, U)` by `AdjoinRoot.lift`.  Its side condition
   `eval₂ σ f' (minpoly 𝔽_q z) = 0` is `minpoly.aeval` pushed back through the INJECTIVE germ
   map `Γ(X, U) → K(X)`.  Passing to `Spec` turns that ring map into `U ⟶ Spec L` over
   `Spec 𝔽_q`.
4. `Spec L ⟶ Spec 𝔽_q` is FINITE, hence proper, so
   `exists_unique_extension_of_valuationRing_stalk_of_isOpenImmersion`
   (`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`) extends `U ⟶ Spec L` to
   `Φ : X ⟶ Spec L`.  Its hypothesis — every local ring of `X` is a valuation ring — is
   `valuationRing_stalk_of_smoothOfRelativeDimension_one`, and dominance of `U ↪ X` is
   irreducibility of `X` plus `U ≠ ∅`.
5. `Φ.appTop` composed with `Γ(X, ⊤) ≅ 𝔽_q` is a ring map `L →+* 𝔽_q`, so
   `finrank_eq_one_of_ringHom_zmod` gives `[L : 𝔽_q] = 1`, i.e. `deg (minpoly 𝔽_q z) = 1`,
   i.e. `z ∈ 𝔽_q`.

WHY THE ALGEBRA STRUCTURE IS AN EXPLICIT ARGUMENT rather than an instance: `K(X)` has no
`𝔽_q`-algebra instance in scope, and building one out of `strX` costs `Scheme.ΓSpecIso`,
`Scheme.Hom.appTop` and `germToFunctionField` plumbing that the statement does not need.
Taking it as an argument is harmless because it is UNIQUE — `ZMod q` is a quotient of `ℤ`, so
`RingHom.ext_zmod` makes `ZMod q →+* K(X)` a subsingleton — and the proof never assumes the
supplied structure is the geometric one; it only ever uses `RingHom.ext_zmod` to identify two
maps out of `ZMod q`.  For the same reason no compatibility has to be checked when the
consumer transports along the bare `RingEquiv` `e`.

FAITHFULNESS.  TRUE, and `GeometricallyConnected` is load-bearing: without it, take a curve
over `𝔽_{q²}` regarded as an `𝔽_q`-scheme (proper, smooth of relative dimension `1`, integral),
whose function field contains `𝔽_{q²}` and for which the conclusion fails.  What that
witness breaks is step 1: `Γ(X, ⊤) = 𝔽_{q²} ≠ 𝔽_q`.  NOT vacuous: `X = ℙ¹_{𝔽_q}` satisfies
every hypothesis. -/
theorem eq_bot_algebraicClosure_functionField
    {q : ℕ} [Fact q.Prime] {X : Scheme.{0}} (strX : X ⟶ Spec (CommRingCat.of (ZMod q)))
    [IsProper strX] [SmoothOfRelativeDimension 1 strX] [GeometricallyConnected strX]
    [AlgebraicGeometry.IsIntegral X] (alg : Algebra (ZMod q) ↥X.functionField) :
    @algebraicClosure (ZMod q) ↥X.functionField _ _ alg = ⊥ := by
  letI := alg
  haveI : Smooth strX := SmoothOfRelativeDimension.smooth 1 strX
  haveI : GeometricallyReduced strX := GeometricallyReduced.of_smooth strX
  haveI hiso : IsIso strX.appTop := isIso_appTop_of_isProper_over_field (Field.toIsField _) strX
  refine le_antisymm (fun z hz => ?_) bot_le
  rw [mem_algebraicClosure_iff'] at hz
  rcases eq_or_ne z 0 with rfl | hz0
  · exact zero_mem _
  obtain ⟨U, hU, f', hUne, hgerm, hunit⟩ := AlgebraicGeometry.exists_isUnit_germ_eq X z hz0
  haveI : IsAffine U.toScheme := hU
  -- the structure map of `U`, read as a ring map
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (hU.isoSpec.inv ≫ U.ι ≫ strX)
  set pz : Polynomial (ZMod q) := minpoly (ZMod q) z with hpz
  haveI : Fact (Irreducible pz) := ⟨minpoly.irreducible hz⟩
  -- the minimal polynomial kills `f'`, because the germ map is injective
  have hev : Polynomial.eval₂ σ.hom f' pz = 0 := by
    have hinj : Function.Injective (X.germToFunctionField U) :=
      X.germToFunctionField_injective U
    apply hinj
    rw [map_zero]
    show (X.germToFunctionField U).hom (Polynomial.eval₂ σ.hom f' pz) = 0
    rw [Polynomial.hom_eval₂]
    have h1 : ((X.germToFunctionField U).hom).comp σ.hom
        = algebraMap (ZMod q) ↥X.functionField := RingHom.ext_zmod _ _
    rw [h1, hgerm, ← Polynomial.aeval_def]
    exact minpoly.aeval _ _
  have hpz0 : pz ≠ 0 := minpoly.ne_zero hz
  haveI : Module.Finite (ZMod q) (AdjoinRoot pz) := (AdjoinRoot.powerBasis hpz0).finite
  -- the classifying ring map, and the morphism `U ⟶ Spec L` it induces
  set ψ : AdjoinRoot pz →+* ↥Γ(X, U) := AdjoinRoot.lift σ.hom f' hev with hψ
  have hψcomp : ψ.comp (algebraMap (ZMod q) (AdjoinRoot pz)) = σ.hom := by
    ext c
    show AdjoinRoot.lift σ.hom f' hev (AdjoinRoot.of pz c) = σ.hom c
    exact AdjoinRoot.lift_of hev
  set strZ : Spec (CommRingCat.of (AdjoinRoot pz)) ⟶ Spec (CommRingCat.of (ZMod q)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (AdjoinRoot pz))) with hstrZ
  haveI : IsFinite strZ :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  set φ : U.toScheme ⟶ Spec (CommRingCat.of (AdjoinRoot pz)) :=
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ) with hφdef
  have hcomp2 :
      CommRingCat.ofHom (algebraMap (ZMod q) (AdjoinRoot pz)) ≫ CommRingCat.ofHom ψ = σ := by
    rw [← CommRingCat.ofHom_comp, hψcomp, CommRingCat.ofHom_hom]
  have hφ : φ ≫ strZ = U.ι ≫ strX := by
    rw [hφdef, hstrZ, Category.assoc, ← Spec.map_comp, hcomp2, hσ, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  -- extend it to all of `X` by the valuative criterion
  haveI : Nonempty U.toScheme := hUne
  haveI : IsDominant U.ι := by
    refine ⟨?_⟩
    show Dense (Set.range _)
    rw [Scheme.Opens.range_ι]
    exact U.isOpen.dense (Set.nonempty_coe_sort.mp hUne)
  obtain ⟨Φ, ⟨-, -⟩, -⟩ :=
    exists_unique_extension_of_valuationRing_stalk_of_isOpenImmersion (strX := strX)
      (strZ := strZ) (valuationRing_stalk_of_smoothOfRelativeDimension_one strX) φ hφ
  -- read off a ring map `L → 𝔽_q` and conclude
  set θ : CommRingCat.of (AdjoinRoot pz) ⟶ CommRingCat.of (ZMod q) :=
    (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot pz))).inv ≫ Φ.appTop ≫ inv strX.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (ZMod q))).hom with hθ
  have hfr : Module.finrank (ZMod q) (AdjoinRoot pz) = 1 :=
    finrank_eq_one_of_ringHom_zmod (AdjoinRoot pz) θ.hom
  have hdim : Module.finrank (ZMod q) (AdjoinRoot pz) = pz.natDegree := by
    rw [(AdjoinRoot.powerBasis hpz0).finrank, AdjoinRoot.powerBasis_dim]
  exact mem_bot_of_natDegree_minpoly_eq_one hz (by rw [← hdim, hfr])

section

open TensorProduct

/-- **THE COMMUTATIVE-ALGEBRA HALF: "`𝔽_q` ALGEBRAICALLY CLOSED IN `K`" TRANSPORTS TO
ABSOLUTE IRREDUCIBILITY OF ANY PLANE MODEL** (**PROVEN** 2026-08-02).

No geometry: `K` is an arbitrary field with a bare `RingEquiv` to `Frac (𝔽_q[X,Y]/(F))`.
The chain is

* `𝔽_q` is PERFECT (it is finite), so `isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot`
  (`Fermat/FLT/Mathlib/RingTheory/InvariantCoarseRing.lean`) turns `algebraicClosure 𝔽_q K = ⊥`
  into `IsDomain (K ⊗_{𝔽_q} 𝔽̄_q)` — this is regularity of the extension `K/𝔽_q`;
* transport along `e` (an `AlgEquiv` for free, by `RingHom.ext_zmod`), then descend along
  `A ↪ Frac A` with `isDomain_tensorProduct_of_injective` (same file; `𝔽̄_q` is flat over the
  field `𝔽_q`), giving `IsDomain (𝔽̄_q ⊗_{𝔽_q} A)` for `A = 𝔽_q[X,Y]/(F)`;
* `Algebra.TensorProduct.tensorQuotientEquiv` and `MvPolynomial.algebraTensorAlgEquiv` (both
  mathlib) identify `𝔽̄_q ⊗_{𝔽_q} A` with `𝔽̄_q[X,Y]/(F ⊗ 𝔽̄_q)`, the ideal comparison being
  `Ideal.map_span` twice plus the single computation
  `algebraTensorAlgEquiv (1 ⊗ₜ F) = MvPolynomial.map φ F`;
* so `(F ⊗ 𝔽̄_q)` is prime, hence `F ⊗ 𝔽̄_q` is prime, hence irreducible.

`Irreducible F` is used only for `IsDomain (𝔽_q[X,Y]/(F))` (so that `Frac` is a field) and for
`F ≠ 0`. -/
theorem irreducible_map_algebraicClosure_of_ringEquiv {q : ℕ} [Fact q.Prime]
    (K : Type) [Field K] (algK : Algebra (ZMod q) K)
    (F : MvPolynomial (Fin 2) (ZMod q)) (hF : Irreducible F)
    (e : K ≃+* FractionRing (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F}))
    (hbot : @algebraicClosure (ZMod q) K _ _ algK = ⊥) :
    Irreducible (MvPolynomial.map
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) F) := by
  letI := algK
  haveI hprime :
      (Ideal.span {F} : Ideal (MvPolynomial (Fin 2) (ZMod q))).IsPrime :=
    (Ideal.span_singleton_prime hF.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hF)
  haveI : IsDomain (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F}) := Ideal.Quotient.isDomain _
  -- regularity of `K/𝔽_q`
  haveI hKd : IsDomain (K ⊗[ZMod q] AlgebraicClosure (ZMod q)) :=
    isDomain_tensorProduct_of_isAlgebraic_of_algebraicClosure_eq_bot (ZMod q) K hbot
      (AlgebraicClosure (ZMod q))
  -- `e` is automatically an `𝔽_q`-algebra map
  have hcomm : ∀ c : ZMod q, e (algebraMap (ZMod q) K c)
      = algebraMap (ZMod q)
        (FractionRing (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})) c := by
    intro c
    have := RingHom.ext_zmod ((e : K →+* _).comp (algebraMap (ZMod q) K))
      (algebraMap (ZMod q) (FractionRing (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})))
    exact congrFun (congrArg (fun f : ZMod q →+* _ => (f : ZMod q → _)) this) c
  let eAlg : K ≃ₐ[ZMod q] FractionRing (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F}) :=
    { e with commutes' := hcomm }
  haveI : IsDomain (FractionRing (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})
      ⊗[ZMod q] AlgebraicClosure (ZMod q)) :=
    (Algebra.TensorProduct.congr eAlg
      (AlgEquiv.refl (R := ZMod q) (A₁ := AlgebraicClosure (ZMod q)))).symm.toMulEquiv.isDomain
  haveI : IsDomain ((MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})
      ⊗[ZMod q] AlgebraicClosure (ZMod q)) :=
    isDomain_tensorProduct_of_injective (ZMod q) (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})
      (FractionRing (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})) (AlgebraicClosure (ZMod q))
      (IsScalarTower.toAlgHom (ZMod q) _ _) (IsFractionRing.injective _ _)
  haveI : IsDomain (AlgebraicClosure (ZMod q)
      ⊗[ZMod q] (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})) :=
    (Algebra.TensorProduct.comm (ZMod q) (AlgebraicClosure (ZMod q))
      (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})).toMulEquiv.isDomain
  -- identify the base change with the base-changed plane model
  have hideal : Ideal.span {MvPolynomial.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) F}
      = ((Ideal.span {F}).map
          (Algebra.TensorProduct.includeRight :
            MvPolynomial (Fin 2) (ZMod q) →ₐ[ZMod q]
              AlgebraicClosure (ZMod q) ⊗[ZMod q] MvPolynomial (Fin 2) (ZMod q))).map
        ((MvPolynomial.algebraTensorAlgEquiv (ZMod q) (AlgebraicClosure (ZMod q))
          (σ := Fin 2)) :
            (AlgebraicClosure (ZMod q) ⊗[ZMod q] MvPolynomial (Fin 2) (ZMod q)) →+*
              MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q))) := by
    have hval : (MvPolynomial.algebraTensorAlgEquiv (ZMod q) (AlgebraicClosure (ZMod q))
        (σ := Fin 2))
          (Algebra.TensorProduct.includeRight F)
        = MvPolynomial.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) F := by
      show MvPolynomial.algebraTensorAlgEquiv (ZMod q) (AlgebraicClosure (ZMod q))
          ((1 : AlgebraicClosure (ZMod q)) ⊗ₜ[ZMod q] F) = _
      simp
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun t => Ideal.span {t}) hval.symm
  haveI : IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q)) ⧸
      Ideal.span {MvPolynomial.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) F}) :=
    ((Algebra.TensorProduct.tensorQuotientEquiv (R := ZMod q) (AlgebraicClosure (ZMod q))
      (MvPolynomial (Fin 2) (ZMod q)) (AlgebraicClosure (ZMod q)) (Ideal.span {F})).trans
      (Ideal.quotientEquivAlg _ _
        (MvPolynomial.algebraTensorAlgEquiv (ZMod q) (AlgebraicClosure (ZMod q))
          (σ := Fin 2)) hideal)).symm.toMulEquiv.isDomain
  have hG0 : MvPolynomial.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) F ≠ 0 := by
    intro h
    exact hF.ne_zero (MvPolynomial.map_injective _
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective (by simpa using h))
  have hGp : (Ideal.span
      {MvPolynomial.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) F}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp ‹_›
  exact ((Ideal.span_singleton_prime hG0).mp hGp).irreducible

end

end AlgebraicallyClosedIn

/-- **`𝔽_q` IS ALGEBRAICALLY CLOSED IN THE FUNCTION FIELD OF A SMOOTH PROPER
GEOMETRICALLY CONNECTED CURVE — EQUIVALENTLY, EVERY PLANE MODEL IS ABSOLUTELY
IRREDUCIBLE** (**PROVEN** 2026-08-02; cut as a sorry leaf 2026-07-31 out of
`exists_planeModel_ringEquiv_functionField_of_isProperSmoothCurve`).

STATEMENT.  If `F ∈ 𝔽_q[X,Y]` is irreducible and `Frac (𝔽_q[X,Y]/(F)) ≅ K(X)` as
bare rings, then `F ⊗ 𝔽̄_q` is irreducible in `𝔽̄_q[X,Y]`.

PROVEN over the two halves in the section above, and the assembly is three lines: give
`K(X)` the `𝔽_q`-algebra structure transported from the plane model along `e` (any structure
would do — `ZMod q →+* K(X)` is a subsingleton), feed it to
`eq_bot_algebraicClosure_functionField`, and feed the result to
`irreducible_map_algebraicClosure_of_ringEquiv`.

THE ROUTE THIS LEAF'S ORIGINAL DOCSTRING PRESCRIBED WAS RIGHT ABOUT THE ALGEBRA AND
INCOMPLETE ABOUT THE GEOMETRY, and the correction is worth recording.  It said step 1 is
"`X` proper smooth geometrically connected over a field is GEOMETRICALLY INTEGRAL (`X_{𝔽̄_q}`
is connected by hypothesis and regular by smoothness, hence irreducible and reduced), so
`𝔽̄_q ⊗ K(X)` is a DOMAIN".  That is true and it is NOT the cheapest route at this pin: the
implication "connected + regular ⟹ irreducible" for `X_{𝔽̄_q}` is not available, and the
comparison of `K(X_{𝔽̄_q})` with `K(X) ⊗ 𝔽̄_q` is a further step.  What is available is
`Γ(X, ⊤) = 𝔽_q` (`isIso_appTop_of_isProper_over_field`, already proven in this project) plus
the valuative criterion for a smooth proper curve (`CurveExtension.lean`), which together give
"`𝔽_q` is algebraically closed in `K(X)`" directly — see
`eq_bot_algebraicClosure_functionField`.  Step 2 of the original route survives essentially
verbatim as `irreducible_map_algebraicClosure_of_ringEquiv`.

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
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) F) := by
  haveI hprime : (Ideal.span {F} : Ideal (MvPolynomial (Fin 2) (ZMod q))).IsPrime :=
    (Ideal.span_singleton_prime hF.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hF)
  haveI : IsDomain (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F}) := Ideal.Quotient.isDomain _
  letI algK : Algebra (ZMod q) ↥X.functionField :=
    (((e.symm : _ →+* ↥X.functionField)).comp
      (algebraMap (ZMod q)
        (FractionRing (MvPolynomial (Fin 2) (ZMod q) ⧸ Ideal.span {F})))).toAlgebra
  exact irreducible_map_algebraicClosure_of_ringEquiv ↥X.functionField algK F hF e
    (eq_bot_algebraicClosure_functionField strX algK)

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
