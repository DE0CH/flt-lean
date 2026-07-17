/-
MazurTorsion.lean — own work for the Fermat project (not vendored from the
FLT project).

Decomposition of `FreyPackage.mazur` (irreducibility of the mod-`p` Galois
representation on the `p`-torsion of the Frey curve) into two explicit
sorry nodes, following Serre's argument (Duke Math. J. 54 (1987), §4.1):

* `FreyPackage.exists_torsion_embedding_of_not_isIrreducible` (sorry node):
  **Serre's reducible-case analysis.** If the mod-`p` representation of the
  Frey curve `E` is not irreducible, then there is a Galois-stable line in
  `E[p]` (the `p`-torsion is `2`-dimensional over `𝔽_p`, so a proper nonzero
  invariant submodule is a line), i.e. a rational subgroup `C ⊆ E` of order
  `p`, giving an extension `0 → χ₁ → E[p] → χ₂ → 0` of characters with
  `χ₁ χ₂ = ω̄` (mod-`p` cyclotomic, by the Weil pairing). The Frey curve is
  semistable, so both characters are unramified away from `p` (unipotent
  inertia at multiplicative primes, triviality at good primes), and at `p`
  one of them is unramified (the supersingular case is excluded because
  inertia at `p` then acts irreducibly, contradicting reducibility). An
  everywhere-unramified character of `Gal(ℚ̄/ℚ)` is trivial (Minkowski: `ℚ`
  has no unramified extension). If `χ₁ = 1` then `E` has a rational point
  of order `p`; if `χ₂ = 1` then the quotient curve `E' = E/C` (a `ℚ`-rational
  quotient by a rational subgroup, Vélu) has one, namely the image of `E[p]`.
  Whichever curve carries the point of order `p` also carries full rational
  `2`-torsion: `E` visibly (`y² = x(x − aᵖ)(x + bᵖ)` has `(0,0)`, `(aᵖ,0)`,
  `(−bᵖ,0)`), and `E/C` because the quotient isogeny has odd degree `p`
  (so is injective on `E[2]`) and is defined over `ℚ`. Since `p` is odd,
  `(ℤ/2)² × ℤ/p ≅ ℤ/2 × ℤ/2p`, so SOME elliptic curve over `ℚ` has a
  subgroup of rational points isomorphic to `ℤ/2 × ℤ/2p`. The statement
  folds the quotient-curve construction (not yet available in mathlib) into
  an existential over Weierstrass models; a later layer must construct
  quotients by finite rational subgroups and split this node accordingly.

* `WeierstrassCurve.mazur_classification` (sorry node): **Mazur's torsion
  theorem** (Mazur, 1977/1978), stated faithfully: the torsion subgroup of
  the rational points of an elliptic curve over `ℚ` is isomorphic to one of
  the fifteen groups `ℤ/n` for `n ∈ {1, …, 10, 12}` or `ℤ/2 × ℤ/2m` for
  `m ∈ {1, 2, 3, 4}`.

* `WeierstrassCurve.mazur_torsion_bound` (PROVEN from the classification):
  **Mazur's torsion theorem, weak form.** No elliptic curve over `ℚ` has a
  subgroup of rational points isomorphic to `ℤ/2 × ℤ/2p` for a prime
  `p ≥ 5`. Derivation: the image of an injective homomorphism
  `ℤ/2 × ℤ/2p →+ E(ℚ)` consists of torsion points (every element of the
  finite source has finite additive order), so the homomorphism corestricts
  to an injection into the torsion subgroup; by the classification the
  torsion subgroup is finite of order at most `16`, while the source has
  order `4p ≥ 20`.

Given the two nodes, `FreyPackage.mazur` is immediate: if the representation
were reducible, the first node produces a curve whose rational points contain
`ℤ/2 × ℤ/2p`, which the second node forbids.
-/
module

public import Fermat.FLT.FreyCurve.Basic
public import Fermat.FLT.EllipticCurve.Torsion
-- `cyclotomicCharacterModL` and the stable-line extraction, used in the
-- character bookkeeping of the Serre §4.1 dichotomy.
public import Fermat.FLT.GaloisRepresentation.Chebotarev
-- `det_galoisRep_eq_cyclotomic` (the DERIVED determinant node), the
-- `χ₁χ₂ = ω̄` input of the dichotomy derivation.
public import Fermat.FLT.EllipticCurve.WeilPairing
-- `FreyCurve.torsion_isUnramified` (unramifiedness outside `{2, p}`),
-- consumed by the derivation of the semistability leaf.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.FreyConditions
-- `localInertiaGroup` and the restriction `Γ ℚ_q → Γ ℚ`, used to state
-- the Minkowski node.
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
-- `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`, the place of `ℚ`
-- attached to a prime number.
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- Minkowski's discriminant theorem (`exists_not_isUnramifiedAt_int_of_isGalois`)
-- and the going-up prime lifting, used in the Minkowski assembly proof.
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.RingTheory.Ideal.GoingUp
-- The local inertia-fixed-field node (`e(M/ℚ_q) = 1` for finite
-- subextensions of `ℚ_qᵃˡᵍ` fixed by the local inertia), consumed by
-- the transport proof of the Minkowski surjectivity theorem below.
import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField
-- `adicCompletion.maximalIdeal_eq_span_uniformizer`, used to identify
-- the maximal ideal of `ℤ_q` with the span of `q`.
import Fermat.FLT.DedekindDomain.AdicValuation

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine

set_option warn.sorry false in
/-- **Mazur's torsion theorem** (sorry node): the torsion subgroup of the
rational points of an elliptic curve over `ℚ` is isomorphic to one of the
fifteen groups `ℤ/n` with `n ∈ {1, …, 10, 12}` or `ℤ/2 × ℤ/2m` with
`m ∈ {1, 2, 3, 4}`. Mazur, "Modular curves and the Eisenstein ideal"
(Publ. Math. IHÉS 47, 1977) and "Rational isogenies of prime degree"
(Invent. Math. 44, 1978). -/
theorem WeierstrassCurve.mazur_classification (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (∃ n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ),
      Nonempty ((Submodule.torsion ℤ (E⁄ℚ).Point) ≃+ ZMod n)) ∨
    (∃ m ∈ ({1, 2, 3, 4} : Finset ℕ),
      Nonempty ((Submodule.torsion ℤ (E⁄ℚ).Point) ≃+ (ZMod 2 × ZMod (2 * m)))) :=
  sorry

/-- **Mazur's torsion theorem, weak form**: the rational points of an
elliptic curve over `ℚ` contain no subgroup isomorphic to `ℤ/2 × ℤ/2p` for
any `p ≥ 5` (primality is not needed: the order comparison `4p ≥ 20 > 16`
alone suffices) — equivalently, no additive homomorphism
`ℤ/2 × ℤ/2p →+ E(ℚ)` is injective. Derived from `mazur_classification`:
the image consists of torsion points, so the homomorphism corestricts to an
injection into the torsion subgroup, which by the classification is finite
of order at most `16 < 4p`. -/
theorem WeierstrassCurve.mazur_torsion_bound (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (h5 : 5 ≤ p)
    (φ : (ZMod 2 × ZMod (2 * p)) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  haveI : NeZero (2 * p) := ⟨by omega⟩
  -- every image point is torsion: `x` has finite additive order in the
  -- finite group `ℤ/2 × ℤ/2p`, and `φ` transports the annihilation
  have hmem : ∀ x : ZMod 2 × ZMod (2 * p),
      φ x ∈ Submodule.torsion ℤ (E⁄ℚ).Point := by
    intro x
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨(addOrderOf x : ℤ),
      mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (addOrderOf_pos x).ne')⟩, ?_⟩
    show (addOrderOf x : ℤ) • φ x = 0
    rw [natCast_zsmul, ← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
  -- corestrict to the torsion subgroup, preserving injectivity
  let φ' : (ZMod 2 × ZMod (2 * p)) →+ (Submodule.torsion ℤ (E⁄ℚ).Point) :=
    φ.codRestrict (Submodule.torsion ℤ (E⁄ℚ).Point) hmem
  have hφ' : Function.Injective φ' := fun a b hab => hφ (Subtype.ext_iff.mp hab)
  -- compare cardinalities against the fifteen groups
  rcases E.mazur_classification with ⟨n, hn, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · have hn12 : 1 ≤ n ∧ n ≤ 12 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      omega
    haveI : NeZero n := ⟨by omega⟩
    haveI : Finite (Submodule.torsion ℤ (E⁄ℚ).Point) :=
      Finite.of_equiv (ZMod n) e.symm.toEquiv
    have hcard := Nat.card_le_card_of_injective φ' hφ'
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod,
      Nat.card_congr e.toEquiv, Nat.card_zmod] at hcard
    omega
  · have hm4 : 1 ≤ m ∧ m ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    haveI : NeZero (2 * m) := ⟨by omega⟩
    haveI : Finite (Submodule.torsion ℤ (E⁄ℚ).Point) :=
      Finite.of_equiv (ZMod 2 × ZMod (2 * m)) e.symm.toEquiv
    have hcard := Nat.card_le_card_of_injective φ' hφ'
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod, Nat.card_congr e.toEquiv,
      Nat.card_prod, Nat.card_zmod, Nat.card_zmod] at hcard
    omega

/-- The prime of `𝓞 ℚ` attached to the prime number `q` is the span of
`q`: unfolding `toHeightOneSpectrumRingOfIntegersRat`, the ideal is the
comap of `span {(q : ℤ)}` along `Rat.ringOfIntegersEquiv`, and a ring
isomorphism carries spans of singletons to spans of singletons while
preserving the naturals. -/
lemma asIdeal_toHeightOneSpectrumRingOfIntegersRat {q : ℕ} (hq : q.Prime) :
    hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal =
      Ideal.span {(q : NumberField.RingOfIntegers ℚ)} := by
  have h1 : hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal =
      Ideal.comap (Rat.ringOfIntegersEquiv.symm.symm) (Ideal.span {(q : ℤ)}) := rfl
  rw [h1, RingEquiv.symm_symm, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton,
    map_natCast]

open IsDedekindDomain.HeightOneSpectrum in
set_option maxHeartbeats 1000000 in
/-- `q` is a uniformizer of the completed integer ring `ℤ_q`: the maximal
ideal of `(ℤ_q)ˆ = 𝒪ᵥ` (for `v = v_q` the place of `ℚ` at `q`) is the
span of `q`. Via `maximalIdeal_eq_span_uniformizer` it suffices that the
valuation of `q` in `ℚ_q` is exactly `ofAdd (-1)`, which reduces through
`valuedAdicCompletion_eq_valuation` and `valuation_of_algebraMap` to the
`intValuation` of `q` in `𝓞 ℚ`, computed by `intValuation_singleton`
from `v_q = span {q}`. -/
lemma maximalIdeal_adicCompletionIntegers_eq_span {q : ℕ} (hq : q.Prime) :
    IsLocalRing.maximalIdeal
        (adicCompletionIntegers ℚ hq.toHeightOneSpectrumRingOfIntegersRat) =
      Ideal.span
        {(q : adicCompletionIntegers ℚ hq.toHeightOneSpectrumRingOfIntegersRat)} := by
  have hq0 : ((q : NumberField.RingOfIntegers ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr hq.ne_zero
  have hval : hq.toHeightOneSpectrumRingOfIntegersRat.intValuation
      ((q : NumberField.RingOfIntegers ℚ)) = Multiplicative.ofAdd (-1 : ℤ) :=
    hq.toHeightOneSpectrumRingOfIntegersRat.intValuation_singleton hq0
      (asIdeal_toHeightOneSpectrumRingOfIntegersRat hq)
  apply adicCompletion.maximalIdeal_eq_span_uniformizer
  -- the valuation of `q` in `ℚ_q`, assembled entirely in the mathlib
  -- lemmas' own coercion spelling (avoiding any cross-spelling defeq)
  have h := (valuedAdicCompletion_eq_valuation
      (v := hq.toHeightOneSpectrumRingOfIntegersRat) (K := ℚ)
      ((q : NumberField.RingOfIntegers ℚ))).trans
    ((valuation_of_algebraMap
      (v := hq.toHeightOneSpectrumRingOfIntegersRat) (K := ℚ)
      ((q : NumberField.RingOfIntegers ℚ))).trans hval)
  convert h using 2
  norm_cast

set_option backward.isDefEq.respectTransparency false in
/-- **Minkowski surjectivity transport** (DERIVED 2026-07-16 from the
local inertia-fixed-field node
`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup`): if the image
in `G_ℚ` of the local inertia group at `q` fixes the finite Galois
extension `L/ℚ` pointwise, then SOME prime `Q₀` of `𝓞 L` above `q` has
trivial ideal-inertia in `Gal(L/ℚ)`. Construction: the chosen embedding
`ι : ℚᵃˡᵍ → (ℚ_q)ᵃˡᵍ` (the one underlying `absoluteGaloisGroup.map`)
carries `L` into the finite subextension `M := ℚ_q(ι(L))`, which the
hypothesis and `lift_map` place inside the fixed field of the local
inertia; the local node then makes `q` a uniformizer of the integral
closure `𝒪_M`. Pulling the maximal ideal of `𝒪_M` back along
`ι : 𝓞 L → 𝒪_M` yields a prime `Q₀ ∋ q` with `e(Q₀|q) = 1` (if `e ≥ 2`
then `q ∈ Q₀²`, so `q ∈ 𝔪_M² = (q²)`, making `q` a unit of `𝒪_M` —
absurd), and `#I(Q₀) = e = 1` closes by
`card_inertia_eq_ramificationIdxIn`. No decomposition-group theory or
henselian lifting is used. -/
theorem exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup) :
    ∃ (Q₀ : Ideal (NumberField.RingOfIntegers L)) (_ : Q₀.IsPrime)
      (_ : (q : NumberField.RingOfIntegers L) ∈ Q₀),
      Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  classical
  -- the chosen embedding of algebraic closures underlying the map of
  -- absolute Galois groups
  set f : ℚ →+* IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat :=
    algebraMap ℚ _ with hf
  set ι : AlgebraicClosure ℚ →+* AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    AlgebraicClosure.map f with hι
  -- a finite generating set for `L/ℚ`
  obtain ⟨s, hs⟩ := L.fg_iff_finiteType.mpr (inferInstanceAs (Algebra.FiniteType ℚ L))
  have hL : L = IntermediateField.adjoin ℚ ↑s :=
    IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ hs.symm
  -- the image field `M := ℚ_q(ι(s)) = ℚ_q(ι(L))`
  set M : IntermediateField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    IntermediateField.adjoin _ (ι '' ↑s) with hM
  -- `ι` carries all of `L` into `M`
  have hsub : ∀ x ∈ L, ι x ∈ M := by
    intro x hx
    rw [hL] at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | algebraMap c =>
        rw [AlgebraicClosure.map_algebraMap]
        exact M.algebraMap_mem _
    | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
    | inv x hx ihx => rw [map_inv₀]; exact inv_mem ihx
    | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
  -- `M/ℚ_q` is finite: it is generated by the finite set `ι '' s` of
  -- integral (= algebraic) elements
  haveI hfdM : FiniteDimensional
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M := by
    haveI : Finite (ι '' (↑s : Set (AlgebraicClosure ℚ))) :=
      (s.finite_toSet.image ι).to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      fun x _ => Algebra.IsIntegral.isIntegral x
  -- the hypothesis places `M` inside the fixed field of the local inertia
  have hMfix : M ≤ IntermediateField.fixedField
      (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) := by
    rw [hM, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    -- `σ (ι y) = ι ((map f σ) y) = ι y` by `lift_map` and the hypothesis
    have hmem : (Field.absoluteGaloisGroup.map f) σ ∈ L.fixingSubgroup :=
      hle (Subgroup.mem_map_of_mem _ hσ)
    have hfixy : (Field.absoluteGaloisGroup.map f σ) y = y :=
      (IntermediateField.mem_fixingSubgroup_iff L ((Field.absoluteGaloisGroup.map f) σ)).mp
        hmem y (hL ▸ IntermediateField.subset_adjoin _ _ hy)
    calc σ (ι y) = ι ((Field.absoluteGaloisGroup.map f σ) y) :=
          (Field.absoluteGaloisGroup.lift_map f σ y).symm
      _ = ι y := by rw [hfixy]
  -- the local node: `q` generates the maximal ideal of `𝒪_M`
  have hmax := maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup
    hq.toHeightOneSpectrumRingOfIntegersRat M hMfix
  have hspan : IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M) =
      Ideal.span {(q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M)} := by
    rw [← hmax, maximalIdeal_adicCompletionIntegers_eq_span hq, Ideal.map_span,
      Set.image_singleton, map_natCast]
  -- the ring homomorphism `ψ : L → M` induced by `ι`
  let ψ : L →+* M :=
    { toFun := fun y => ⟨ι (y : AlgebraicClosure ℚ), hsub _ y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun a b => by
        apply Subtype.ext
        simp }
  -- `ψ` carries the ring of integers of `L` into `𝒪_M`
  have hψint : ∀ x : NumberField.RingOfIntegers L,
      ψ (algebraMap (NumberField.RingOfIntegers L) L x) ∈
        integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M := by
    intro x
    have h1 : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers L) L x) :=
      NumberField.RingOfIntegers.isIntegral_coe x
    -- promote `ψ` to a `ℤ`-algebra homomorphism with the AMBIENT `ℤ`-algebra
    -- structures (all ring homs from `ℤ` agree, so `commutes'` is by
    -- uniqueness of `ℤ →+* ·`)
    let ψℤ : L →ₐ[ℤ] M :=
      { toRingHom := ψ
        commutes' := fun n => by
          rw [RingHom.eq_intCast' (algebraMap ℤ L), RingHom.eq_intCast' (algebraMap ℤ M)]
          exact map_intCast ψ n }
    have h2 : IsIntegral ℤ (ψ (algebraMap (NumberField.RingOfIntegers L) L x)) :=
      h1.map ψℤ
    -- pass from `ℤ`-integrality to `𝒪ᵥ`-integrality by pushing the monic
    -- witness through `ℤ → 𝒪ᵥ` (instance-agnostic: all ring homs from `ℤ`
    -- agree)
    obtain ⟨p, hp, hpeval⟩ := h2
    refine ⟨p.map (Int.castRingHom
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, Subsingleton.elim
      ((algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M).comp
        (Int.castRingHom
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
      (algebraMap ℤ M)]
    exact hpeval
  let φ : NumberField.RingOfIntegers L →+*
      IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M :=
    (ψ.comp (algebraMap (NumberField.RingOfIntegers L) L)).codRestrict
      (integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M) hψint
  -- the embedding prime: the pullback of the maximal ideal of `𝒪_M`
  haveI hmaxprime : (IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M)).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  refine ⟨Ideal.comap φ (IsLocalRing.maximalIdeal _), Ideal.IsPrime.comap φ, ?_, ?_⟩
  · -- `q` lands in the pullback: `φ q = q ∈ 𝔪_M = (q)`
    rw [Ideal.mem_comap, map_natCast, hspan]
    exact Ideal.mem_span_singleton_self _
  -- inertia is trivial: `#I(Q₀) = e(Q₀|q) = 1`
  have hQ₀mem : (q : NumberField.RingOfIntegers L) ∈
      Ideal.comap φ (IsLocalRing.maximalIdeal _) := by
    rw [Ideal.mem_comap, map_natCast, hspan]
    exact Ideal.mem_span_singleton_self _
  haveI hQ₀prime : (Ideal.comap φ (IsLocalRing.maximalIdeal _)).IsPrime :=
    Ideal.IsPrime.comap φ
  -- instance pack for `card_inertia_eq_ramificationIdxIn` (mirrors the
  -- inertia dictionary proof below)
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  haveI hsp : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ
  have hne : (Ideal.span {((q : ℤ))} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : (Ideal.comap φ (IsLocalRing.maximalIdeal _)).LiesOver
      (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff hQ₀prime.ne_top hqZ).mpr (by exact_mod_cast hQ₀mem)
  haveI hfinq : Finite (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ)) :=
    Ring.HasFiniteQuotients.finiteQuotient hne
  haveI hmaxZ : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  have hsurjZ : Function.Surjective
      (algebraMap (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ))
        ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField)) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxZ)
  haveI : Finite ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField) :=
    Finite.of_surjective _ hsurjZ
  -- the ramification index (old spelling) is `1`
  have hple : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
      (Ideal.span {((q : ℤ))}) ≤ Ideal.comap φ (IsLocalRing.maximalIdeal _) := by
    rw [Ideal.map_span, Set.image_singleton]
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact_mod_cast hQ₀mem
  have he1 : Ideal.ramificationIdx' (Ideal.span {((q : ℤ))})
      (Ideal.comap φ (IsLocalRing.maximalIdeal _)) = 1 := by
    by_contra hne1
    have hsq := (Ideal.ramificationIdx'_ne_one_iff hple).mp hne1
    -- then `q ∈ Q₀²`, so `φ q = q ∈ 𝔪_M² = (q²)`, making `q` a unit
    have hqQ2 : (q : NumberField.RingOfIntegers L) ∈
        (Ideal.comap φ (IsLocalRing.maximalIdeal _)) ^ 2 := by
      refine hsq ?_
      have : algebraMap ℤ (NumberField.RingOfIntegers L) (q : ℤ) ∈
          Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers L))
            (Ideal.span {((q : ℤ))}) :=
        Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
      simpa using this
    have hcomap2 : (Ideal.comap φ (IsLocalRing.maximalIdeal _)) ^ 2 ≤
        Ideal.comap φ ((IsLocalRing.maximalIdeal _) ^ 2) := by
      rw [pow_two, pow_two]
      exact Ideal.mul_le.mpr fun r hr t ht => Ideal.mem_comap.mpr
        (by rw [map_mul]; exact Ideal.mul_mem_mul hr ht)
    have hφq := Ideal.mem_comap.mp (hcomap2 hqQ2)
    rw [map_natCast, hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hφq
    obtain ⟨c, hc⟩ := hφq
    -- `q ≠ 0` in `𝒪_M` (its image in `(ℚ_q)ᵃˡᵍ` is `q ≠ 0` by char zero)
    haveI : CharZero (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat)) :=
      charZero_of_injective_algebraMap (algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) _).injective
    have hq0 : ((q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M)) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun z => (algebraMap M (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))
        ((algebraMap (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) M) M) z))) h0
      simp only [map_natCast, map_zero] at h1
      exact Nat.cast_ne_zero.mpr hq.ne_zero h1
    -- cancel one factor of `q`: `q · c = 1`
    have hcancel : (q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M) * c = 1 := by
      have hmul : (q : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) M) *
          ((q : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat) M) * c) =
          (q : IntegralClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat) M) * 1 := by
        rw [mul_one, ← mul_assoc, ← pow_two]
        exact hc.symm
      exact mul_left_cancel₀ hq0 hmul
    -- but `q` lies in the proper maximal ideal — contradiction
    have hqmem : (q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M) ∈
        IsLocalRing.maximalIdeal _ := by
      rw [hspan]; exact Ideal.mem_span_singleton_self _
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hqmem
        (isUnit_iff_exists.mpr ⟨c, hcancel, by rwa [mul_comm] at hcancel⟩))
  -- bridge to the `Module.length` spelling and conclude via
  -- `#I(Q₀) = e = 1`
  have h2 : (Ideal.comap φ (IsLocalRing.maximalIdeal _)).ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {((q : ℤ))})
      (Ideal.comap φ (IsLocalRing.maximalIdeal _)) hne]
    exact he1
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (L ≃ₐ[ℚ] L)) (Ideal.span {((q : ℤ))})
    (Ideal.comap φ (IsLocalRing.maximalIdeal _))
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {((q : ℤ))})
    (Ideal.comap φ (IsLocalRing.maximalIdeal _)) (L ≃ₐ[ℚ] L), h2] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard

set_option backward.isDefEq.respectTransparency false in
/-- **Conjugacy propagation of trivial inertia** (PROVEN 2026-07-16): if ONE
prime of `𝓞 L` above `q` has trivial ideal-inertia in `Gal(L/ℚ)`, then
EVERY prime above `q` does. Classical: `Gal(L/ℚ)` acts transitively on
the primes above `q` (`Ideal.IsInvariant.orbit_eq_primesOver` /
going-up), and inertia groups at conjugate primes are conjugate
(`I(g • Q) = g I(Q) g⁻¹`), so triviality propagates along the orbit. -/
theorem inertia_eq_bot_of_exists_prime_over
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (Q₀ : Ideal (NumberField.RingOfIntegers L)) [Q₀.IsPrime]
    (hQ₀mem : (q : NumberField.RingOfIntegers L) ∈ Q₀)
    (hQ₀ : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    (hQmem : (q : NumberField.RingOfIntegers L) ∈ Q) :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  haveI hsp : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ
  have hne : (Ideal.span {((q : ℤ))} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hmax : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  haveI hlies₀ : Q₀.LiesOver (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top ‹Q₀.IsPrime›) hqZ).mpr
      (by exact_mod_cast hQ₀mem)
  haveI hlies : Q.LiesOver (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top ‹Q.IsPrime›) hqZ).mpr
      (by exact_mod_cast hQmem)
  haveI := IsGaloisGroup.of_isFractionRing (L ≃ₐ[ℚ] L) ℤ
    (NumberField.RingOfIntegers L) ℚ L
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (Ideal.span {((q : ℤ))}) Q₀ Q ((L ≃ₐ[ℚ] L))
  rw [← hσ]
  rw [Subgroup.eq_bot_iff_forall] at hQ₀ ⊢
  intro g hg
  have hconj : σ⁻¹ * g * σ ∈ Q₀.inertia (L ≃ₐ[ℚ] L) := by
    intro y
    have h1 := hg (σ • y)
    rw [Submodule.mem_toAddSubgroup,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem] at h1
    rw [Submodule.mem_toAddSubgroup]
    have h2 : σ⁻¹ • (g • σ • y - σ • y) = (σ⁻¹ * g * σ) • y - y := by
      rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul]
    rwa [h2] at h1
  have h3 : σ⁻¹ * g * σ = 1 := hQ₀ _ hconj
  have h4 : g = σ * (σ⁻¹ * g * σ) * σ⁻¹ := by group
  rw [h4, h3, mul_one, mul_inv_cancel]

/-- **The inertia transport** (DERIVED 2026-07-16 from the two nodes
above): the image of `localInertiaGroup q` fixing `L` pointwise
trivializes the global ideal-inertia at EVERY prime above `q` — the
embedding-determined prime has trivial inertia by the surjectivity
node, and conjugacy propagates it. -/
theorem inertia_eq_bot_of_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    (hQmem : (q : NumberField.RingOfIntegers L) ∈ Q) :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  obtain ⟨Q₀, hQ₀p, hQ₀mem, hQ₀⟩ :=
    exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup L hq hle
  exact inertia_eq_bot_of_exists_prime_over L hq Q₀ hQ₀mem hQ₀ Q hQmem

set_option backward.isDefEq.respectTransparency false in
/-- **The inertia dictionary** (DERIVED 2026-07-16 from the transport
node above): if the image in `G_ℚ` of the local inertia group at `q`
fixes the finite Galois extension `L/ℚ` pointwise, then every prime of
`𝓞 L` above `q` is unramified over `ℤ`. Chain: the transport node
trivializes the global ideal-inertia `Q.inertia Gal(L/ℚ)`; its
cardinality IS the ramification index
(`card_inertia_eq_ramificationIdxIn`); `ramificationIdxIn` transfers to
the specific prime; and `ramificationIdx_eq_one_iff` converts `e = 1`
to `Algebra.IsUnramifiedAt` (the `PerfectField` side condition comes
from finiteness of the residue field, via the fraction-ring bridge and
`maximal_ideal_iff_isField_quotient`). -/
theorem isUnramifiedAt_of_inertia_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L] [IsGalois ℚ L]
    {q : ℕ} (hq : q.Prime)
    (hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup)
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    (hQmem : (q : NumberField.RingOfIntegers L) ∈ Q) :
    Algebra.IsUnramifiedAt ℤ Q := by
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  haveI hsp : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ
  have hne : (Ideal.span {((q : ℤ))} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hlies : Q.LiesOver (Ideal.span {((q : ℤ))}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top ‹Q.IsPrime›) hqZ).mpr
      (by exact_mod_cast hQmem)
  haveI hfinq : Finite (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ)) :=
    Ring.HasFiniteQuotients.finiteQuotient hne
  haveI hmax : (Ideal.span {((q : ℤ))} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  have hsurj : Function.Surjective
      (algebraMap (ℤ ⧸ (Ideal.span {((q : ℤ))} : Ideal ℤ))
        ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField)) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
  haveI : Finite ((Ideal.span {((q : ℤ))} : Ideal ℤ).ResidueField) :=
    Finite.of_surjective _ hsurj
  -- `e = |inertia| = |⊥| = 1`
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (L ≃ₐ[ℚ] L)) (Ideal.span {((q : ℤ))}) Q
  rw [inertia_eq_bot_of_le_fixingSubgroup L hq hle Q hQmem] at hcard
  have h1 : Ideal.ramificationIdxIn (Ideal.span {((q : ℤ))})
      (NumberField.RingOfIntegers L) = 1 := by
    rw [← hcard]
    simp
  have h2 : Q.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx
      (Ideal.span {((q : ℤ))}) Q (L ≃ₐ[ℚ] L)]
    exact h1
  exact Ideal.ramificationIdx_eq_one_iff.mp h2

set_option backward.isDefEq.respectTransparency false in
/-- **Minkowski, subgroup form** (DERIVED 2026-07-16 from the inertia
dictionary and mathlib's discriminant theory): an open normal subgroup
of `G_ℚ` containing the image of the local inertia group at every prime
is everything. Assembly: the fixed field `L` of `H` recovers `H` by the
infinite Galois correspondence (`H` is closed since open); `L` is a
finite Galois number field (`isOpen_iff_finite`, `normal_iff_isGalois`);
if `H ≠ ⊤` then `L ≠ ⊥` so `1 < finrank ℚ L`, and
`exists_not_isUnramifiedAt_int_of_isGalois` produces a prime `p` all of
whose primes in `𝓞 L` are ramified; but the inertia hypothesis plus the
dictionary make the lifted prime above `p` unramified — contradiction. -/
theorem open_normal_subgroup_eq_top_of_inertia_le
    (H : Subgroup (Field.absoluteGaloisGroup ℚ)) [hnorm : H.Normal]
    (hopen : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ)))
    (hinertia : ∀ (q : ℕ) (hq : q.Prime),
      Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) ≤ H) :
    H = ⊤ := by
  haveI hgal : IsGalois ℚ (AlgebraicClosure ℚ) := inferInstance
  by_contra hne
  have hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isClosed_of_isOpen H hopen
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.fixedField (E := AlgebraicClosure ℚ) H with hLdef
  have hfix : L.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hclosed⟩
  haveI hfd : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hopen)
  haveI hgalL : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp
    (by rw [hfix]; exact hnorm)
  haveI : NumberField L := ⟨⟩
  have hrank : 1 < Module.finrank ℚ L := by
    rcases Nat.lt_or_ge 1 (Module.finrank ℚ L) with h | h
    · exact h
    · exfalso
      have h0 : 0 < Module.finrank ℚ L := Module.finrank_pos
      have h1 : Module.finrank ℚ L = 1 := by omega
      apply hne
      rw [← hfix, IntermediateField.finrank_eq_one_iff.mp h1,
        IntermediateField.fixingSubgroup_bot]
  obtain ⟨p, hp, hram⟩ := NumberField.exists_not_isUnramifiedAt_int_of_isGalois
    (K := L) (𝒪 := NumberField.RingOfIntegers L) hrank
  -- lift `p` to a prime of `𝓞 L`
  haveI := IsIntegralClosure.isIntegral_algebra ℤ (A := NumberField.RingOfIntegers L) L
  have hpZ : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  haveI hPspan : (Ideal.span {((p : ℤ))} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr hpZ
  have hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers L)) ≤
      Ideal.span {((p : ℤ))} := by
    intro x hx
    have hx0 : algebraMap ℤ (NumberField.RingOfIntegers L) x = 0 := hx
    have hxL : algebraMap ℤ L x = 0 := by
      rw [IsScalarTower.algebraMap_eq ℤ (NumberField.RingOfIntegers L) L, RingHom.comp_apply,
        hx0, map_zero]
    have : (x : ℤ) = 0 := by
      have := congrArg (fun y => y) hxL
      exact_mod_cast (by simpa using hxL : ((x : ℤ) : L) = 0)
    rw [this]
    exact Ideal.zero_mem _
  obtain ⟨Q, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := NumberField.RingOfIntegers L) (Ideal.span {((p : ℤ))}) hker
  haveI := hQprime
  have hpQ : ((p : ℕ) : NumberField.RingOfIntegers L) ∈ Q := by
    have hmem : ((p : ℤ)) ∈ Ideal.span {((p : ℤ))} :=
      Ideal.subset_span rfl
    rw [← hQcomap] at hmem
    have := Ideal.mem_comap.mp hmem
    simpa using this
  exact hram Q hQprime hpQ
    (isUnramifiedAt_of_inertia_le_fixingSubgroup L hp
      (le_trans (hinertia p hp) (le_of_eq hfix.symm)) Q hpQ)

/-- **Minkowski for mod-`p` characters** (DERIVED 2026-07-16 from the
subgroup form): a character `χ : G_ℚ → (ℤ/p)ˣ` with open kernel that is
unramified at every finite place (the local inertia group at every
prime `q` is killed by the restriction of `χ` to `G_{ℚ_q}`) is trivial.
The kernel is an open normal subgroup containing every inertia image,
hence everything. -/
theorem minkowski_character_trivial {p : ℕ}
    (χ : Field.absoluteGaloisGroup ℚ →* (ZMod p)ˣ)
    (hker : IsOpen (χ.ker : Set (Field.absoluteGaloisGroup ℚ)))
    (hunram : ∀ (q : ℕ) (hq : q.Prime),
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) :
    χ = 1 := by
  have hker_top : χ.ker = ⊤ := by
    refine open_normal_subgroup_eq_top_of_inertia_le χ.ker hker ?_
    intro q hq
    rw [Subgroup.map_le_iff_le_comap]
    intro σ hσ
    have h := hunram q hq hσ
    rw [MonoidHom.mem_ker] at h
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    exact h
  ext g
  have hg : g ∈ χ.ker := hker_top ▸ Subgroup.mem_top g
  simpa [MonoidHom.mem_ker] using hg

set_option backward.isDefEq.respectTransparency false in
/-- **Galois descent for points** (PROVEN 2026-07-17): a point of
`E(ℚ̄)` fixed by every element of the absolute Galois group is the base
change of a rational point. The coordinates are fixed by all
automorphisms of the Galois extension `ℚ̄/ℚ`, hence lie in `ℚ`
(`InfiniteGalois.mem_range_algebraMap_iff_fixed`), and nonsingularity
descends along the injective base change
(`baseChange_nonsingular`). -/
theorem WeierstrassCurve.exists_point_eq_baseChange_of_fixed
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Pt : (E⁄(AlgebraicClosure ℚ)).Point)
    (hfix : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt = Pt) :
    ∃ Q : (E⁄ℚ).Point,
      Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) Q = Pt := by
  cases Pt with
  | zero => exact ⟨0, rfl⟩
  | some x y h =>
    have hx : x ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
      refine (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr fun σ => ?_
      have h1 := hfix σ
      rw [Affine.Point.map_some] at h1
      exact (Affine.Point.some.inj h1).left
    have hy : y ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) := by
      refine (InfiniteGalois.mem_range_algebraMap_iff_fixed y).mpr fun σ => ?_
      have h1 := hfix σ
      rw [Affine.Point.map_some] at h1
      exact (Affine.Point.some.inj h1).right
    obtain ⟨x₀, hx₀⟩ := hx
    obtain ⟨y₀, hy₀⟩ := hy
    have h₀ : (E⁄ℚ).Nonsingular x₀ y₀ := by
      have h2 := h
      rw [← hx₀, ← hy₀] at h2
      exact (Affine.baseChange_nonsingular (W := E)
        (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))
        (algebraMap ℚ (AlgebraicClosure ℚ)).injective x₀ y₀).mp h2
    refine ⟨Affine.Point.some x₀ y₀ h₀, ?_⟩
    have hmap := Affine.Point.map_some
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ)) h₀
    rw [show Affine.Point.baseChange ℚ (AlgebraicClosure ℚ)
        (Affine.Point.some x₀ y₀ h₀) =
      Affine.Point.map (Algebra.ofId ℚ (AlgebraicClosure ℚ))
        (Affine.Point.some x₀ y₀ h₀) from rfl, hmap]
    subst hx₀ hy₀
    rfl

/-!
### Character bookkeeping on a stable line

The linear algebra of Serre's §4.1 analysis, PROVEN here: a stable line
`W` in a 2-dimensional mod-`ℓ` representation carries a unit-valued
sub-character `χ₁` (the scalar action on the rank-1 space `W`), the
quotient carries a quotient-character `χ₂`, and
`det ρ g = χ₁ g · χ₂ g` (the triangular determinant,
`LinearMap.det_eq_det_mul_det`).
-/

section CharacterBookkeeping

set_option backward.isDefEq.respectTransparency false in
/-- **Scalar character on a rank-`1` module** (PROVEN): a multiplicative
family of endomorphisms of a `1`-dimensional space over `F` is
given by a unit-valued character. -/
lemma exists_unit_character_of_finrank_one {F : Type*} [Field F]
    {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module F M]
    [Module.Finite F M] (hM : Module.finrank F M = 1)
    (Φ : G → Module.End F M)
    (hΦ1 : Φ 1 = 1) (hΦmul : ∀ g h : G, Φ (g * h) = Φ g * Φ h) :
    ∃ χ : G →* Fˣ, ∀ g v, Φ g v = (χ g : F) • v := by
  classical
  let b : Module.Basis (Fin 1) F M :=
    Module.finBasisOfFinrankEq F M hM
  have hm₀ne : (b 0 : M) ≠ 0 := b.ne_zero 0
  have hspan : ∀ v : M, ∃ c : F, v = c • b 0 := by
    intro v
    have h1 := b.sum_repr v
    rw [Fin.sum_univ_one] at h1
    exact ⟨b.repr v 0, h1.symm⟩
  have huniq : ∀ {a c : F}, a • (b 0 : M) = c • b 0 → a = c := by
    intro a c h
    have h2 : (a - c) • (b 0 : M) = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hm₀ne
  choose c hc using fun g => hspan (Φ g (b 0))
  have hone : c 1 = 1 := by
    apply huniq
    rw [← hc 1, hΦ1, Module.End.one_apply, one_smul]
  have hmul : ∀ g h, c (g * h) = c g * c h := by
    intro g h
    apply huniq
    rw [← hc (g * h), hΦmul, Module.End.mul_apply, hc h, map_smul, hc g,
      smul_smul, mul_comm (c h) (c g)]
  have hunit : ∀ g, c g * c g⁻¹ = 1 := fun g => by
    rw [← hmul, mul_inv_cancel, hone]
  refine ⟨MonoidHom.mk' (fun g =>
      ⟨c g, c g⁻¹, hunit g, (mul_comm (c g⁻¹) (c g)).trans (hunit g)⟩)
    (fun g h => Units.ext (hmul g h)), ?_⟩
  intro g v
  obtain ⟨a, rfl⟩ := hspan v
  show Φ g (a • b 0) = c g • a • b 0
  rw [map_smul, hc g, smul_smul, smul_smul, mul_comm]

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [DiscreteTopology F] {V : Type*} [AddCommGroup V]
  [Module F V] [Module.Finite F V]

omit [IsTopologicalRing F] [DiscreteTopology F] in
set_option backward.isDefEq.respectTransparency false in
/-- **The sub-character of a stable line** (PROVEN): the restriction of
the representation to a rank-`1` stable submodule is a unit-valued
character. -/
lemma exists_subCharacter (ρbar : GaloisRep ℚ F V)
    (W : Submodule F V) (hW1 : Module.finrank F W = 1)
    (hstable : ∀ g v, v ∈ W → ρbar g v ∈ W) :
    ∃ χ₁ : Field.absoluteGaloisGroup ℚ →* Fˣ,
      ∀ g, ∀ v ∈ W, ρbar g v = (χ₁ g : F) • v := by
  have he : ∀ g, W ≤ W.comap (ρbar g) := fun g v hv => hstable g v hv
  obtain ⟨χ₁, hχ₁⟩ := exists_unit_character_of_finrank_one hW1
    (fun g => (ρbar g).restrict (he g))
    (by
      apply LinearMap.ext; intro v; apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, map_one, Module.End.one_apply,
        Module.End.one_apply])
    (by
      intro g h
      apply LinearMap.ext; intro v; apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, LinearMap.coe_restrict_apply,
        LinearMap.coe_restrict_apply])
  refine ⟨χ₁, fun g v hv => ?_⟩
  have h1 := hχ₁ g ⟨v, hv⟩
  have h2 := congrArg Subtype.val h1
  rw [LinearMap.coe_restrict_apply] at h2
  exact h2

omit [IsTopologicalRing F] [DiscreteTopology F] in
set_option backward.isDefEq.respectTransparency false in
/-- **The quotient-character of a stable line** (PROVEN): the induced
action on the quotient by a stable submodule with rank-`1` quotient is a
unit-valued character. -/
lemma exists_quotCharacter (ρbar : GaloisRep ℚ F V)
    (W : Submodule F V)
    (hQ1 : Module.finrank F (V ⧸ W) = 1)
    (hstable : ∀ g v, v ∈ W → ρbar g v ∈ W) :
    ∃ χ₂ : Field.absoluteGaloisGroup ℚ →* Fˣ,
      ∀ g v, W.mkQ (ρbar g v) = (χ₂ g : F) • W.mkQ v := by
  have he : ∀ g, W ≤ W.comap (ρbar g) := fun g v hv => hstable g v hv
  obtain ⟨χ₂, hχ₂⟩ := exists_unit_character_of_finrank_one hQ1
    (fun g => W.mapQ W (ρbar g) (he g))
    (by
      apply LinearMap.ext; intro z
      obtain ⟨v, rfl⟩ := W.mkQ_surjective z
      rw [Module.End.one_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        map_one, Module.End.one_apply])
    (by
      intro g h
      apply LinearMap.ext; intro z
      obtain ⟨v, rfl⟩ := W.mkQ_surjective z
      rw [Module.End.mul_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.mapQ_apply, Submodule.mapQ_apply, map_mul,
        Module.End.mul_apply])
  refine ⟨χ₂, fun g v => ?_⟩
  have h1 := hχ₂ g (W.mkQ v)
  rw [Submodule.mkQ_apply, Submodule.mapQ_apply] at h1
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact h1

omit [IsTopologicalRing F] [DiscreteTopology F] in
set_option backward.isDefEq.respectTransparency false in
/-- **The triangular determinant** (PROVEN): on a stable line, the
determinant is the product of the sub- and quotient-characters. -/
lemma det_eq_subCharacter_mul_quotCharacter
    (ρbar : GaloisRep ℚ F V)
    (W : Submodule F V) (hW1 : Module.finrank F W = 1)
    (hQ1 : Module.finrank F (V ⧸ W) = 1)
    (hstable : ∀ g v, v ∈ W → ρbar g v ∈ W)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ →* Fˣ)
    (hχ₁ : ∀ g, ∀ v ∈ W, ρbar g v = (χ₁ g : F) • v)
    (hχ₂ : ∀ g v, W.mkQ (ρbar g v) = (χ₂ g : F) • W.mkQ v)
    (g : Field.absoluteGaloisGroup ℚ) :
    LinearMap.det (ρbar g : Module.End F V) =
      (χ₁ g : F) * (χ₂ g : F) := by
  have he : W ≤ W.comap (ρbar g) := fun v hv => hstable g v hv
  rw [LinearMap.det_eq_det_mul_det W (ρbar g) he]
  congr 1
  · have hr : (ρbar g).restrict he =
        (χ₁ g : F) • (LinearMap.id : W →ₗ[F] W) := by
      apply LinearMap.ext; intro v; apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, hχ₁ g v.1 v.2]
      rfl
    rw [hr, LinearMap.det_smul, hW1, pow_one, LinearMap.det_id, mul_one]
  · have hr : W.mapQ W (ρbar g) he =
        (χ₂ g : F) • (LinearMap.id : (V ⧸ W) →ₗ[F] (V ⧸ W)) := by
      apply LinearMap.ext; intro z
      obtain ⟨v, rfl⟩ := W.mkQ_surjective z
      have h2 : (W.mapQ W (ρbar g) he) (W.mkQ v) = W.mkQ (ρbar g v) := by
        rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
      rw [h2, hχ₂ g v]
      rfl
    rw [hr, LinearMap.det_smul, hQ1, pow_one, LinearMap.det_id, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- **Openness of the kernel-level set of a mod-`ℓ`-style representation over a discrete field**
(PROVEN): the set where the representation is trivial is open — the
endomorphism space is discrete (finite module over the discrete
`F`), so the representation is locally constant. Stated with the
finiteness input as a plain hypothesis so that callers can supply it
for any definitionally-equal spelling of `V`. -/
lemma isOpen_setOf_galoisRep_eq_one {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [DiscreteTopology F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρbar : GaloisRep ℚ F V) (hfinV : Finite V) :
    IsOpen {g : Field.absoluteGaloisGroup ℚ | ρbar g = 1} := by
  haveI := hfinV
  letI := moduleTopology F (Module.End F V)
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun f => (f : V → V)) DFunLike.coe_injective
  haveI : Module.Finite F (Module.End F V) :=
    Module.Finite.of_finite
  haveI : DiscreteTopology (Module.End F V) :=
    GaloisRepresentation.discreteTopology_moduleTopology F
      (Module.End F V)
  have hcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρbar g :=
    ρbar.continuous_toFun
  exact (isOpen_discrete ({1} : Set (Module.End F V))).preimage hcont

set_option backward.isDefEq.respectTransparency false in
/-- **Unipotent scalars are trivial** (PROVEN): if `(f − 1)² = 0` and
`f` acts on a nonzero vector by the scalar `c`, then `c = 1` — the
eigenvalues of a unipotent endomorphism are `1`. -/
lemma subCharacter_eq_one_of_sq_eq_zero {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [DiscreteTopology F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (f : Module.End F V) (hf : (f - 1) ^ 2 = 0)
    {c : F} {w : V} (hw : w ≠ 0) (hcw : f w = c • w) : c = 1 := by
  have h1 : (f - 1) w = (c - 1) • w := by
    rw [LinearMap.sub_apply, Module.End.one_apply, hcw, sub_smul, one_smul]
  have h2 : ((f - 1) ^ 2 : Module.End F V) w =
      ((c - 1) ^ 2 : F) • w := by
    rw [pow_two, Module.End.mul_apply, h1, map_smul, h1, smul_smul,
      ← pow_two]
  rw [hf] at h2
  have h3 : ((c - 1) ^ 2 : F) • w = 0 := by
    rw [← h2]
    rfl
  rcases smul_eq_zero.mp h3 with h4 | h4
  · have h5 : (c - 1 : F) = 0 := pow_eq_zero_iff two_ne_zero |>.mp h4
    have h6 := sub_eq_zero.mp h5
    exact h6
  · exact absurd h4 hw

set_option backward.isDefEq.respectTransparency false in
/-- **Unipotent quotient scalars are trivial** (PROVEN): if
`(f − 1)² = 0` and `f` descends to the scalar `c` on the (nontrivial)
quotient by a stable submodule, then `c = 1`. -/
lemma quotCharacter_eq_one_of_sq_eq_zero {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [DiscreteTopology F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (f : Module.End F V) (hf : (f - 1) ^ 2 = 0)
    (W : Submodule F V) (hWtop : W ≠ ⊤) {c : F}
    (hc : ∀ v, W.mkQ (f v) = c • W.mkQ v) : c = 1 := by
  haveI : Nontrivial (V ⧸ W) := Submodule.Quotient.nontrivial_iff.mpr hWtop
  obtain ⟨z, hz⟩ := exists_ne (0 : V ⧸ W)
  obtain ⟨v, rfl⟩ := W.mkQ_surjective z
  have h1 : ∀ u, W.mkQ ((f - 1) u) = (c - 1 : F) • W.mkQ u := by
    intro u
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, hc, sub_smul,
      one_smul]
  have h2 : W.mkQ (((f - 1) ^ 2 : Module.End F V) v) =
      ((c - 1) ^ 2 : F) • W.mkQ v := by
    rw [pow_two, Module.End.mul_apply, h1 ((f - 1) v), h1 v, smul_smul,
      ← pow_two]
  rw [hf] at h2
  have h3 : ((c - 1) ^ 2 : F) • W.mkQ v = 0 := by
    rw [← h2]
    show W.mkQ ((0 : Module.End F V) v) = 0
    rw [LinearMap.zero_apply, map_zero]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)
  · exact absurd h4 hz

end CharacterBookkeeping

section GenericBridge

variable {K : Type*} [Field K] [NumberField K]

set_option backward.isDefEq.respectTransparency false in
/-- **Characters through an unramified representation are unramified**
(PROVEN, stated over a GENERIC number field so that the `algebraMap`
spelling agrees definitionally with the one inside `GaloisRep.toLocal`
— at `K = ℚ` a locally-elaborated `algebraMap` picks `Rat`-specific
instance paths that instance- and even default-transparency
unification cannot reconcile with the generic ones, because
`Field.absoluteGaloisGroup.map` is not exposed; callers at `ℚ` bridge
the two spellings with `Rat.subsingleton_ringHom` + `convert`): if the
representation kills the local inertia at `v` and `χ` is trivial
wherever the representation is, then the restriction of `χ` to the
local Galois group kills inertia. -/
lemma character_localInertia_le_ker_of_isUnramifiedAt {F : Type*}
    [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρbar : GaloisRep K F V)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hUn : ρbar.IsUnramifiedAt v)
    (χ : Field.absoluteGaloisGroup K →* Fˣ)
    (htriv : ∀ g, ρbar g = 1 → χ g = 1) :
    localInertiaGroup v ≤ (χ.comp (Field.absoluteGaloisGroup.map
      (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        K v))).toMonoidHom).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  apply htriv
  have h1 : (ρbar.toLocal v) σ = 1 := hUn.localInertiaGroup_le hσ
  exact h1

end GenericBridge

set_option warn.sorry false in
/-- **Unipotence of inertia at `2`** (sorry node — Tate-curve content):
the Frey curve has multiplicative reduction at `2` (its minimal model —
after the standard variable change — has a `2`-adic unit `c₄` and
positive-valuation discriminant), so by Tate's uniformization the
inertia at `2` acts on the `p`-torsion through the unipotent
translations of the Tate parameter: `(ρ(σ) − 1)² = 0` for every `σ` in
the local inertia group at `2`. -/
theorem FreyPackage.inertia_two_unipotent (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ σ ∈ localInertiaGroup
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
      (P.freyCurve.galoisRep P.p P.hppos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) σ) -
        1) ^ 2 = 0 :=
  sorry

set_option warn.sorry false in
/-- **The flat/ordinary analysis at `p`** (sorry node — the deepest
piece of Serre's §4.1 argument): given the stable line of the reducible
mod-`p` Frey representation with its characters `χ₁`, `χ₂`
(multiplying to `ω̄`), one of the two is unramified at `p` itself. The
Frey curve is semistable at `p`; in the good-ordinary/multiplicative
case the connected-étale sequence of the `p`-divisible group makes the
quotient (étale) character unramified; the supersingular case cannot
occur for a reducible representation (inertia at `p` would act through
the level-2 fundamental character, irreducibly). -/
theorem FreyPackage.subquotient_character_unramified_at_p
    (P : FreyPackage)
    (W : Submodule (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    (hW1 : Module.finrank (ZMod P.p) W = 1)
    (hstable : ∀ g v, v ∈ W → P.freyCurve.galoisRep P.p P.hppos g v ∈ W)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ →* (ZMod P.p)ˣ)
    (hχ₁ : ∀ g, ∀ v ∈ W,
      P.freyCurve.galoisRep P.p P.hppos g v = (χ₁ g : ZMod P.p) • v)
    (hχ₂ : ∀ g v, W.mkQ (P.freyCurve.galoisRep P.p P.hppos g v) =
      (χ₂ g : ZMod P.p) • W.mkQ v)
    (hcyclo : ∀ g : Field.absoluteGaloisGroup ℚ,
      (χ₁ g : ZMod P.p) * (χ₂ g : ZMod P.p) =
        ((@GaloisRepresentation.cyclotomicCharacterModL P.p ⟨P.pp⟩ g :
          (ZMod P.p)ˣ) : ZMod P.p)) :
    (localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ₁.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          P.pp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) ∨
    (localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          P.pp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **The semistability-unramifiedness statement** (DERIVED 2026-07-17
from the two leaves above and the PROVEN machinery): given a stable
line in the mod-`p` torsion of the Frey curve with its sub- and
quotient-characters `χ₁`, `χ₂`, ONE of the two characters is unramified
at EVERY finite place. Assembly: away from `{2, p}` the whole
representation is unramified (`FreyCurve.torsion_isUnramified` — the
PROVEN Néron–Ogg–Shafarevich node at good primes, the Tate glue at
multiplicative ones), so both characters are trivial on inertia (the
unipotent-scalar lemmas at `(ρ(σ) − 1)² = 0`, which holds a fortiori
when `ρ(σ) = 1`); at `2` inertia is unipotent
(`inertia_two_unipotent`), so again both characters are unramified; at
`p` the flat/ordinary leaf selects one character, and that character is
then unramified everywhere. -/
theorem FreyPackage.subquotient_character_unramified
    (P : FreyPackage)
    (W : Submodule (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    (hW1 : Module.finrank (ZMod P.p) W = 1)
    (hstable : ∀ g v, v ∈ W → P.freyCurve.galoisRep P.p P.hppos g v ∈ W)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ →* (ZMod P.p)ˣ)
    (hχ₁ : ∀ g, ∀ v ∈ W,
      P.freyCurve.galoisRep P.p P.hppos g v = (χ₁ g : ZMod P.p) • v)
    (hχ₂ : ∀ g v, W.mkQ (P.freyCurve.galoisRep P.p P.hppos g v) =
      (χ₂ g : ZMod P.p) • W.mkQ v)
    (hcyclo : ∀ g : Field.absoluteGaloisGroup ℚ,
      (χ₁ g : ZMod P.p) * (χ₂ g : ZMod P.p) =
        ((@GaloisRepresentation.cyclotomicCharacterModL P.p ⟨P.pp⟩ g :
          (ZMod P.p)ˣ) : ZMod P.p)) :
    (∀ (q : ℕ) (hq : q.Prime),
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ₁.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) ∨
    (∀ (q : ℕ) (hq : q.Prime),
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) := by
  classical
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  -- rank bookkeeping: a nonzero vector of `W`, and `W ≠ ⊤`
  have hcard : Nat.card
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) =
      P.p ^ 2 :=
    TorsionCard.card_torsionBy
      (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))) P.p
      (Nat.cast_ne_zero.mpr P.pp.ne_zero)
  haveI hfin : Finite
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcard]
      have := P.pp.pos
      positivity)
  haveI : Fintype
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Fintype.ofFinite _
  haveI : Module.Finite (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Module.Finite.of_finite
  have hfr : Module.finrank (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) =
      2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod P.p)
      (V := ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    rw [ZMod.card] at h1
    have h2 : P.p ^ 2 = P.p ^ Module.finrank (ZMod P.p)
        ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := by
      rw [← hcard, Nat.card_eq_fintype_card]
      exact h1
    exact Nat.pow_right_injective P.pp.two_le h2.symm
  have hW0 : W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hW1
    omega
  have hWtop : W ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, hfr] at hW1
    omega
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  obtain ⟨w₀, hw₀ne⟩ := exists_ne (0 : W)
  have hw₀V : (w₀ : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion P.p)) ≠ 0 :=
    fun hc => hw₀ne (Subtype.ext hc)
  -- the characters are trivial at any unipotent inertia element
  have hgen₁ : ∀ (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ))
      (σ : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      ((P.freyCurve.galoisRep P.p P.hppos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) σ) -
        1) ^ 2 = 0) →
      (χ₁.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          v))).toMonoidHom) σ = 1 := by
    intro v σ hsq
    apply Units.ext
    rw [Units.val_one, MonoidHom.comp_apply]
    exact subCharacter_eq_one_of_sq_eq_zero _ hsq hw₀V
      (hχ₁ _ (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) w₀.2)
  have hgen₂ : ∀ (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ))
      (σ : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)),
      ((P.freyCurve.galoisRep P.p P.hppos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) σ) -
        1) ^ 2 = 0) →
      (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          v))).toMonoidHom) σ = 1 := by
    intro v σ hsq
    apply Units.ext
    rw [Units.val_one, MonoidHom.comp_apply]
    exact quotCharacter_eq_one_of_sq_eq_zero _ hsq W hWtop (hχ₂ _)
  -- triviality of the characters wherever the representation is trivial
  have htriv₁ : ∀ g, P.freyCurve.galoisRep P.p P.hppos g = 1 → χ₁ g = 1 := by
    intro g hg
    apply Units.ext
    rw [Units.val_one]
    refine subCharacter_eq_one_of_sq_eq_zero
      (P.freyCurve.galoisRep P.p P.hppos g) ?_ hw₀V
      (hχ₁ g (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) w₀.2)
    rw [hg, sub_self]
    exact zero_pow two_ne_zero
  have htriv₂ : ∀ g, P.freyCurve.galoisRep P.p P.hppos g = 1 → χ₂ g = 1 := by
    intro g hg
    apply Units.ext
    rw [Units.val_one]
    refine quotCharacter_eq_one_of_sq_eq_zero
      (P.freyCurve.galoisRep P.p P.hppos g) ?_ W hWtop (hχ₂ g)
    rw [hg, sub_self]
    exact zero_pow two_ne_zero
  -- assemble via the flat/ordinary leaf at `p`
  rcases P.subquotient_character_unramified_at_p W hW1 hstable χ₁ χ₂ hχ₁
    hχ₂ hcyclo with hp | hp
  · left
    intro q hq σ hσ
    by_cases hq2 : q = 2
    · subst hq2
      rw [MonoidHom.mem_ker]
      exact hgen₁ _ σ (P.inertia_two_unipotent σ hσ)
    · by_cases hqp : q = P.p
      · subst hqp
        exact hp hσ
      · have h4 := character_localInertia_le_ker_of_isUnramifiedAt
          (P.freyCurve.galoisRep P.p P.hppos)
          hq.toHeightOneSpectrumRingOfIntegersRat
          (FreyCurve.torsion_isUnramified P q hq ⟨hq2, hqp⟩) χ₁ htriv₁
        have h5 := h4 hσ
        convert h5 using 5
        exact Subsingleton.elim _ _
  · right
    intro q hq σ hσ
    by_cases hq2 : q = 2
    · subst hq2
      rw [MonoidHom.mem_ker]
      exact hgen₂ _ σ (P.inertia_two_unipotent σ hσ)
    · by_cases hqp : q = P.p
      · subst hqp
        exact hp hσ
      · have h4 := character_localInertia_le_ker_of_isUnramifiedAt
          (P.freyCurve.galoisRep P.p P.hppos)
          hq.toHeightOneSpectrumRingOfIntegersRat
          (FreyCurve.torsion_isUnramified P q hq ⟨hq2, hqp⟩) χ₂ htriv₂
        have h5 := h4 hσ
        convert h5 using 5
        exact Subsingleton.elim _ _

/-- **Serre's stable-line dichotomy for the Frey curve** (DERIVED
2026-07-17 from the semistability leaf and the PROVEN character
bookkeeping): if the mod-`p` representation of the Frey curve is not
irreducible, then (given the Minkowski input) either there is a
Galois-FIXED point of exact order `p` in `E(ℚ̄)`, or there is a stable
line `W` with the induced action on `E[p]/W` trivial. Assembly: the
stable line exists (`exists_stable_line_of_not_isIrreducible`), carries
characters `χ₁`, `χ₂` with `χ₁χ₂ = ω̄` (the DERIVED
`det_galoisRep_eq_cyclotomic` through the triangular determinant); the
semistability leaf makes one of them everywhere-unramified; its kernel
is open (it contains the open kernel of the representation); the
Minkowski hypothesis kills it; `χ₁ = 1` fixes a basis vector of `W`
pointwise, `χ₂ = 1` trivializes the quotient action. -/
theorem FreyPackage.stable_line_dichotomy_of_not_isIrreducible
    (P : FreyPackage)
    (hmink : ∀ χ : Field.absoluteGaloisGroup ℚ →* (ZMod P.p)ˣ,
      IsOpen (χ.ker : Set (Field.absoluteGaloisGroup ℚ)) →
      (∀ (q : ℕ) (hq : q.Prime),
        localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
          (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) →
      χ = 1)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    (∃ Pt : ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point,
      addOrderOf Pt = P.p ∧
      ∀ σ : Field.absoluteGaloisGroup ℚ,
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt = Pt) ∨
    (∃ W : Submodule (ZMod P.p)
        ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p),
      W ≠ ⊥ ∧ W ≠ ⊤ ∧
      (∀ g : Field.absoluteGaloisGroup ℚ,
        ∀ v ∈ W, P.freyCurve.galoisRep P.p P.hppos g v ∈ W) ∧
      (∀ (g : Field.absoluteGaloisGroup ℚ)
        (v : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p),
        W.mkQ (P.freyCurve.galoisRep P.p P.hppos g v) = W.mkQ v)) := by
  classical
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  -- the torsion space has rank `2`
  have hcard : Nat.card ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) = P.p ^ 2 :=
    TorsionCard.card_torsionBy
      (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))) P.p
      (Nat.cast_ne_zero.mpr P.pp.ne_zero)
  haveI hfin : Finite ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    have := P.pp.pos
    positivity)
  haveI : Fintype ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod P.p) (V := ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    rw [ZMod.card] at h1
    have h2 : P.p ^ 2 = P.p ^ Module.finrank (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) := by
      rw [← hcard, Nat.card_eq_fintype_card]
      exact h1
    exact Nat.pow_right_injective P.pp.two_le h2.symm
  have hrank : Module.rank (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) = 2 := by
    have h1 := Module.finrank_eq_rank (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)
    rw [hfr] at h1
    exact_mod_cast h1.symm
  -- the stable line
  have hirr : ¬ (P.freyCurve.galoisRep P.p P.hppos).IsIrreducible := h
  obtain ⟨W, hW1, hstable⟩ :=
    GaloisRepresentation.exists_stable_line_of_not_isIrreducible hrank (P.freyCurve.galoisRep P.p P.hppos) hirr
  have hW0 : W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hW1
    omega
  have hWtop : W ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, hfr] at hW1
    omega
  have hQ1 : Module.finrank (ZMod P.p) (((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) ⧸ W) = 1 := by
    have hsum := Submodule.finrank_quotient_add_finrank W
    rw [hfr, hW1] at hsum
    omega
  -- the two characters
  obtain ⟨χ₁, hχ₁⟩ := exists_subCharacter (P.freyCurve.galoisRep P.p P.hppos) W hW1 hstable
  obtain ⟨χ₂, hχ₂⟩ := exists_quotCharacter (P.freyCurve.galoisRep P.p P.hppos) W hQ1 hstable
  -- `χ₁χ₂ = ω̄` through the determinant node
  have hcyclo : ∀ g, (χ₁ g : ZMod P.p) * (χ₂ g : ZMod P.p) =
      ((@GaloisRepresentation.cyclotomicCharacterModL P.p ⟨P.pp⟩ g :
        (ZMod P.p)ˣ) : ZMod P.p) := by
    intro g
    rw [← det_eq_subCharacter_mul_quotCharacter (P.freyCurve.galoisRep P.p P.hppos) W hW1 hQ1 hstable
      χ₁ χ₂ hχ₁ hχ₂ g, WeilPairing.cyclotomicCharacterModL_eq_toZMod]
    exact WeilPairing.det_galoisRep_eq_cyclotomic P.freyCurve P.p P.hppos g
  -- the kernel of the representation is open …
  let Kρ : Subgroup (Field.absoluteGaloisGroup ℚ) :=
    { carrier := {g | (P.freyCurve.galoisRep P.p P.hppos) g = 1}
      one_mem' := map_one (P.freyCurve.galoisRep P.p P.hppos)
      mul_mem' := by
        intro a b ha hb
        show (P.freyCurve.galoisRep P.p P.hppos) (a * b) = 1
        rw [map_mul, ha, hb, mul_one]
      inv_mem' := by
        intro a ha
        show (P.freyCurve.galoisRep P.p P.hppos) a⁻¹ = 1
        have h1 : (P.freyCurve.galoisRep P.p P.hppos) a⁻¹ * (P.freyCurve.galoisRep P.p P.hppos) a = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h1 }
  have hKρ_open : IsOpen (Kρ : Set (Field.absoluteGaloisGroup ℚ)) :=
    isOpen_setOf_galoisRep_eq_one (P.freyCurve.galoisRep P.p P.hppos) hfin
  -- … and lies in the kernels of both characters
  have hnontrivW : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  obtain ⟨w₀, hw₀ne⟩ := exists_ne (0 : W)
  have hw₀V : (w₀ : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)) ≠ 0 := fun hc => hw₀ne (Subtype.ext hc)
  have hker₁ : Kρ ≤ χ₁.ker := by
    intro g hg
    have hg1 : (P.freyCurve.galoisRep P.p P.hppos) g = 1 := hg
    rw [MonoidHom.mem_ker]
    have h1 := hχ₁ g (w₀ : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)) w₀.2
    rw [hg1, Module.End.one_apply] at h1
    have h2 : ((1 : ZMod P.p) - (χ₁ g : ZMod P.p)) • (w₀ : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)) = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero_of_eq h1
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact Units.ext (by
        rw [Units.val_one]
        exact (sub_eq_zero.mp h3).symm)
    · exact absurd h3 hw₀V
  have hker₂ : Kρ ≤ χ₂.ker := by
    intro g hg
    have hg1 : (P.freyCurve.galoisRep P.p P.hppos) g = 1 := hg
    rw [MonoidHom.mem_ker]
    haveI : Nontrivial (((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) ⧸ W) :=
      Submodule.Quotient.nontrivial_iff.mpr hWtop
    obtain ⟨z, hz⟩ := exists_ne (0 : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) ⧸ W)
    obtain ⟨v, rfl⟩ := W.mkQ_surjective z
    have h1 := hχ₂ g v
    rw [hg1, Module.End.one_apply] at h1
    have h2 : ((1 : ZMod P.p) - (χ₂ g : ZMod P.p)) • W.mkQ v = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero_of_eq h1
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact Units.ext (by
        rw [Units.val_one]
        exact (sub_eq_zero.mp h3).symm)
    · exact absurd h3 hz
  have hopen₁ : IsOpen (χ₁.ker : Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isOpen_mono hker₁ hKρ_open
  have hopen₂ : IsOpen (χ₂.ker : Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isOpen_mono hker₂ hKρ_open
  -- the semistability leaf, then Minkowski
  rcases P.subquotient_character_unramified W hW1 hstable χ₁ χ₂ hχ₁ hχ₂
    hcyclo with hun₁ | hun₂
  · -- `χ₁ = 1`: the basis vector of `W` is a fixed point of order `p`
    have hχ₁triv : χ₁ = 1 := hmink χ₁ hopen₁ hun₁
    left
    refine ⟨(show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from
      (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)).1), ?_, ?_⟩
    · -- exact order `p`
      have hsm : ((P.p : ℕ) : ℤ) •
          (w₀ : ((P.freyCurve.map (algebraMap ℚ
            (AlgebraicClosure ℚ))).nTorsion P.p)).1 = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp
          (w₀ : ((P.freyCurve.map (algebraMap ℚ
            (AlgebraicClosure ℚ))).nTorsion P.p)).2
      have hnat : P.p •
          (w₀ : ((P.freyCurve.map (algebraMap ℚ
            (AlgebraicClosure ℚ))).nTorsion P.p)).1 = 0 := by
        exact_mod_cast hsm
      have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hnat
      have hne : (w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p)).1 ≠ 0 :=
        fun hc => hw₀V (Subtype.ext hc)
      rcases P.pp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hne
      · exact h1
    · -- fixed by every `σ`
      intro σ
      have h1 := hχ₁ σ (w₀ : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)) w₀.2
      rw [hχ₁triv] at h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
      exact congrArg Subtype.val h1
  · -- `χ₂ = 1`: the quotient action is trivial
    have hχ₂triv : χ₂ = 1 := hmink χ₂ hopen₂ hun₂
    right
    refine ⟨W, hW0, hWtop, fun g v hv => hstable g v hv, fun g v => ?_⟩
    have h1 := hχ₂ g v
    rw [hχ₂triv] at h1
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact h1

set_option warn.sorry false in
/-- **The Vélu quotient leaf** (sorry node): given a Galois-stable line
`W` in the `p`-torsion of the Frey curve on whose quotient the Galois
action is trivial, the quotient curve `E/C` by the rational subgroup
`C` corresponding to `W` (a `ℚ`-rational cyclic subgroup of order `p`)
is an elliptic curve over `ℚ` carrying a rational point of order `p`
(the image of any torsion point mapping to a generator of the trivial
quotient) and full rational `2`-torsion (the image of the Frey curve's
full `2`-torsion through the odd-degree rational isogeny, injective on
`2`-torsion). The quotient-curve construction (Vélu) is not yet
available in mathlib, so the statement quantifies existentially over
Weierstrass models. -/
theorem FreyPackage.exists_quotient_curve_point
    (P : FreyPackage)
    (W : Submodule (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    (hW0 : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hstable : ∀ g : Field.absoluteGaloisGroup ℚ,
      ∀ v ∈ W, P.freyCurve.galoisRep P.p P.hppos g v ∈ W)
    (hquot : ∀ (g : Field.absoluteGaloisGroup ℚ)
      (v : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p),
      W.mkQ (P.freyCurve.galoisRep P.p P.hppos g v) = W.mkQ v) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ₂ : (ZMod 2 × ZMod 2) →+ (E'⁄ℚ).Point) (_ : Function.Injective φ₂)
      (Q : (E'⁄ℚ).Point), addOrderOf Q = P.p :=
  sorry

/-- **Serre's reducible-case analysis for the Frey curve, given
Minkowski** (DERIVED 2026-07-17 from the stable-line dichotomy, the
PROVEN Galois descent for points, and the Vélu quotient leaf): if the
mod-`p` Galois representation on the `p`-torsion of the Frey curve is
not irreducible, and every finite-order mod-`p` character of `G_ℚ`
unramified at all finite places is trivial (the Minkowski input, taken
as a hypothesis — see `minkowski_character_trivial`), then either the
Frey curve itself has a rational point of order `p`, or some elliptic
curve over `ℚ` (the Vélu quotient `E/C` by the rational subgroup of
order `p`) has full rational `2`-torsion together with a rational point
of order `p`. -/
theorem FreyPackage.exists_p_point_of_not_isIrreducible_of_minkowski
    (P : FreyPackage)
    (hmink : ∀ χ : Field.absoluteGaloisGroup ℚ →* (ZMod P.p)ˣ,
      IsOpen (χ.ker : Set (Field.absoluteGaloisGroup ℚ)) →
      (∀ (q : ℕ) (hq : q.Prime),
        localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
          (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) →
      χ = 1)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    (∃ Q : ((P.freyCurve)⁄ℚ).Point, addOrderOf Q = P.p) ∨
    (∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ₂ : (ZMod 2 × ZMod 2) →+ (E'⁄ℚ).Point) (_ : Function.Injective φ₂)
      (Q : (E'⁄ℚ).Point), addOrderOf Q = P.p) := by
  rcases P.stable_line_dichotomy_of_not_isIrreducible hmink h with
    ⟨Pt, hord, hfix⟩ | ⟨W, hW0, hWtop, hstable, hquot⟩
  · -- the fixed point of order `p` descends to a rational point
    left
    obtain ⟨Q, hQ⟩ :=
      WeierstrassCurve.exists_point_eq_baseChange_of_fixed P.freyCurve Pt hfix
    refine ⟨Q, ?_⟩
    rw [← hord, ← hQ]
    exact (addOrderOf_injective _
      (Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))) Q).symm
  · -- the trivial-quotient line goes through the Vélu leaf
    right
    exact P.exists_quotient_curve_point W hW0 hWtop hstable hquot

/-- **Serre's reducible-case analysis for the Frey curve** (DERIVED
2026-07-16 from the two preceding nodes, by discharging the Minkowski
hypothesis with `minkowski_character_trivial`). -/
theorem FreyPackage.exists_p_point_of_not_isIrreducible
    (P : FreyPackage)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    (∃ Q : ((P.freyCurve)⁄ℚ).Point, addOrderOf Q = P.p) ∨
    (∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ₂ : (ZMod 2 × ZMod 2) →+ (E'⁄ℚ).Point) (_ : Function.Injective φ₂)
      (Q : (E'⁄ℚ).Point), addOrderOf Q = P.p) :=
  P.exists_p_point_of_not_isIrreducible_of_minkowski
    (fun χ hker hunram => minkowski_character_trivial χ hker hunram) h

/-- **Assembly of coprime torsion** (PROVEN 2026-07-16): in an abelian
group, an injective `(ℤ/2)²` and an element of order exactly `p` (an odd
prime) combine into an injective `ℤ/2 × ℤ/2p`, via the Chinese remainder
isomorphism `ℤ/2p ≅ ℤ/2 × ℤ/p`. The two images intersect trivially
because their exponents `2` and `p` are coprime. -/
theorem embedding_assembly {A : Type*} [AddCommGroup A]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (φ₂ : (ZMod 2 × ZMod 2) →+ A) (hφ₂ : Function.Injective φ₂)
    (Q : A) (hQ : addOrderOf Q = p) :
    ∃ ψ : (ZMod 2 × ZMod (2 * p)) →+ A, Function.Injective ψ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr
    (Ne.symm hp2)
  -- the CRT isomorphism `ℤ/2p ≅ ℤ/2 × ℤ/p`
  let e : ZMod (2 * p) ≃+ ZMod 2 × ZMod p :=
    (ZMod.chineseRemainder hcop).toAddEquiv
  -- the `p`-part: `ℤ/p →+ A` sending `1 ↦ Q`
  have hpQ : (zmultiplesHom A Q) (p : ℤ) = 0 := by
    show (p : ℤ) • Q = 0
    rw [natCast_zsmul, ← hQ, addOrderOf_nsmul_eq_zero]
  let fQ : ZMod p →+ A := ZMod.lift p ⟨zmultiplesHom A Q, hpQ⟩
  have hfQ : ∀ k : ZMod p, fQ k = k.val • Q := by
    intro k
    have h1 : fQ (((k.val : ℤ) : ZMod p)) = zmultiplesHom A Q (k.val : ℤ) :=
      ZMod.lift_coe p _ (k.val : ℤ)
    rw [show (((k.val : ℤ)) : ZMod p) = k by
      rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]] at h1
    rw [h1]
    show ((k.val : ℤ)) • Q = _
    rw [natCast_zsmul]
  have hfQker : ∀ k : ZMod p, fQ k = 0 → k = 0 := by
    intro k hk
    rw [hfQ k] at hk
    have hdvd : addOrderOf Q ∣ k.val := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hk
    rw [hQ] at hdvd
    have hval0 : k.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt k)
    exact (ZMod.val_eq_zero k).mp hval0
  -- annihilation facts for the two parts
  have h2ann : ∀ y : ZMod 2 × ZMod 2, (2 : ℕ) • y = 0 := by decide
  have hpann : ∀ k : ZMod p, (p : ℕ) • k = 0 := by
    intro k
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  -- the assembled homomorphism
  let ψ : (ZMod 2 × ZMod (2 * p)) →+ A :=
    { toFun := fun x => φ₂ (x.1, (e x.2).1) + fQ (e x.2).2
      map_zero' := by
        have h0 : e 0 = 0 := map_zero e
        show φ₂ ((0 : ZMod 2 × ZMod (2 * p)).1, (e (0 : ZMod 2 × ZMod (2 * p)).2).1)
          + fQ (e (0 : ZMod 2 × ZMod (2 * p)).2).2 = 0
        rw [show ((0 : ZMod 2 × ZMod (2 * p)).2) = 0 from rfl, h0]
        rw [show (((0 : ZMod 2 × ZMod (2 * p)).1, ((0 : ZMod 2 × ZMod p)).1))
          = (0 : ZMod 2 × ZMod 2) from rfl,
          show ((0 : ZMod 2 × ZMod p)).2 = 0 from rfl, map_zero, map_zero, add_zero]
      map_add' := by
        intro x y
        have he : e (x.2 + y.2) = e x.2 + e y.2 := map_add e _ _
        rw [Prod.fst_add, Prod.snd_add, he, Prod.fst_add, Prod.snd_add,
          show (x.1 + y.1, (e x.2).1 + (e y.2).1)
            = (x.1, (e x.2).1) + (y.1, (e y.2).1) from rfl,
          map_add, map_add]
        abel }
  refine ⟨ψ, (injective_iff_map_eq_zero ψ).mpr ?_⟩
  intro x hx
  -- split `ψ x = 0` into the 2-part and the `p`-part
  set u := φ₂ (x.1, (e x.2).1) with hu
  set v := fQ (e x.2).2 with hv
  have huv : u + v = 0 := hx
  have h2u : (2 : ℕ) • u = 0 := by
    rw [hu, ← map_nsmul, h2ann, map_zero]
  have hpv : (p : ℕ) • v = 0 := by
    rw [hv, ← map_nsmul, hpann, map_zero]
  -- `p` odd kills the 2-part: `p•u = u` while `p•u = -p•v = 0`
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hpu : (p : ℕ) • u = u := by
    have hstep : (p : ℕ) • u = m • ((2 : ℕ) • u) + u := by
      rw [← mul_nsmul', ← succ_nsmul]
      congr 1
      omega
    rw [hstep, h2u, smul_zero, zero_add]
  have hpu0 : (p : ℕ) • u = 0 := by
    have h := congrArg (fun z => (p : ℕ) • z) huv
    simpa [smul_add, hpv] using h
  have hu0 : u = 0 := by rw [← hpu, hpu0]
  have hv0 : v = 0 := by
    have := huv
    rw [hu0, zero_add] at this
    exact this
  -- conclude componentwise
  have h1 : (x.1, (e x.2).1) = 0 :=
    (injective_iff_map_eq_zero φ₂).mp hφ₂ _ hu0
  have h2 : (e x.2).2 = 0 := hfQker _ hv0
  have hex : e x.2 = 0 := by
    have hfst : (e x.2).1 = 0 := congrArg Prod.snd h1
    exact Prod.ext hfst h2
  have hx2 : x.2 = 0 := e.injective (by rw [hex, map_zero])
  have hx1 : x.1 = 0 := congrArg Prod.fst h1
  exact Prod.ext hx1 hx2

section TwoTorsion

open WeierstrassCurve.Affine

/-- The trivial base change of the Frey curve to `ℚ` is elliptic. (Mathlib
has this instance for `E.map f`, but `WeierstrassCurve.baseChange` is a
non-reducible `def`, so instance search cannot see through it; several
derivations in this branch of the tree need the instance.) -/
instance (P : FreyPackage) : ((P.freyCurve)⁄ℚ).IsElliptic :=
  inferInstanceAs (P.freyCurve.map (algebraMap ℚ ℚ)).IsElliptic

/-- **Full rational 2-torsion of the Frey curve** (PROVEN 2026-07-16): the
Frey model has rational 2-torsion points `(0, 0)` and `(aᵖ/4, -aᵖ/8)` (in
the untransformed model `y² = x(x - aᵖ)(x + bᵖ)` the full 2-torsion is
visible; the transformed model retains it rationally, the quadratic
`x² + ((bᵖ-aᵖ)/4)x - aᵖbᵖ/16` factoring as `(x - aᵖ/4)(x + bᵖ/4)`). The
two points generate an injective `(ℤ/2)² →+ E(ℚ)`. -/
theorem FreyPackage.freyCurve_two_torsion_embedding (P : FreyPackage) :
    ∃ φ₂ : (ZMod 2 × ZMod 2) →+ ((P.freyCurve)⁄ℚ).Point, Function.Injective φ₂ := by
  -- the coefficients of the base-changed model
  have h1 : ((P.freyCurve)⁄ℚ).a₁ = 1 := by
    simp [WeierstrassCurve.baseChange, FreyPackage.freyCurve]
  have h2 : ((P.freyCurve)⁄ℚ).a₂ = (P.b ^ P.p - 1 - P.a ^ P.p) / 4 := by
    simp [WeierstrassCurve.baseChange, FreyPackage.freyCurve]
  have h3 : ((P.freyCurve)⁄ℚ).a₃ = 0 := by
    simp [WeierstrassCurve.baseChange, FreyPackage.freyCurve]
  have h4 : ((P.freyCurve)⁄ℚ).a₄ = -(P.a ^ P.p) * (P.b ^ P.p) / 16 := by
    simp [WeierstrassCurve.baseChange, FreyPackage.freyCurve]
  have h6 : ((P.freyCurve)⁄ℚ).a₆ = 0 := by
    simp [WeierstrassCurve.baseChange, FreyPackage.freyCurve]
  have hap : (P.a : ℚ) ^ P.p ≠ 0 := pow_ne_zero _ (by exact_mod_cast P.ha0)
  -- the two points satisfy the equation
  have heq₁ : ((P.freyCurve)⁄ℚ).Equation 0 0 := by
    rw [equation_iff, h1, h2, h3, h4, h6]
    ring
  have heq₂ : ((P.freyCurve)⁄ℚ).Equation
      ((P.a : ℚ) ^ P.p / 4) (-((P.a : ℚ) ^ P.p) / 8) := by
    rw [equation_iff, h1, h2, h3, h4, h6]
    field_simp
    ring
  have hns₁ : ((P.freyCurve)⁄ℚ).Nonsingular 0 0 :=
    equation_iff_nonsingular.mp heq₁
  have hns₂ : ((P.freyCurve)⁄ℚ).Nonsingular
      ((P.a : ℚ) ^ P.p / 4) (-((P.a : ℚ) ^ P.p) / 8) :=
    equation_iff_nonsingular.mp heq₂
  -- the points, their order-2 property, and their distinctness
  set Q₁ : ((P.freyCurve)⁄ℚ).Point := Point.some _ _ hns₁ with hQ₁def
  set Q₂ : ((P.freyCurve)⁄ℚ).Point := Point.some _ _ hns₂ with hQ₂def
  have hneg₁ : -Q₁ = Q₁ := by
    rw [hQ₁def, Point.neg_some]
    rw [Point.some.injEq]
    refine ⟨rfl, ?_⟩
    rw [negY, h1, h3]
    ring
  have hneg₂ : -Q₂ = Q₂ := by
    rw [hQ₂def, Point.neg_some]
    rw [Point.some.injEq]
    refine ⟨rfl, ?_⟩
    rw [negY, h1, h3]
    ring
  have h2Q₁ : (2 : ℤ) • Q₁ = 0 := by
    rw [two_zsmul]
    exact add_eq_zero_iff_eq_neg.mpr hneg₁.symm
  have h2Q₂ : (2 : ℤ) • Q₂ = 0 := by
    rw [two_zsmul]
    exact add_eq_zero_iff_eq_neg.mpr hneg₂.symm
  have hQ₁0 : Q₁ ≠ 0 := Point.some_ne_zero _
  have hQ₂0 : Q₂ ≠ 0 := Point.some_ne_zero _
  have hQ₁₂ : Q₁ ≠ Q₂ := by
    rw [hQ₁def, hQ₂def]
    intro h
    have hx := (Point.some.inj h).1
    rw [eq_comm, div_eq_iff (by norm_num : (4 : ℚ) ≠ 0), zero_mul] at hx
    exact hap hx
  -- assemble the embedding from the two order-2 points
  have hz₁ : (zmultiplesHom _ Q₁) (2 : ℤ) = 0 := h2Q₁
  have hz₂ : (zmultiplesHom _ Q₂) (2 : ℤ) = 0 := h2Q₂
  let f₁ : ZMod 2 →+ ((P.freyCurve)⁄ℚ).Point := ZMod.lift 2 ⟨zmultiplesHom _ Q₁, hz₁⟩
  let f₂ : ZMod 2 →+ ((P.freyCurve)⁄ℚ).Point := ZMod.lift 2 ⟨zmultiplesHom _ Q₂, hz₂⟩
  have hf₁ : f₁ 1 = Q₁ := by
    have := ZMod.lift_coe 2 (⟨zmultiplesHom _ Q₁, hz₁⟩ :
      {f : ℤ →+ ((P.freyCurve)⁄ℚ).Point // f 2 = 0}) (1 : ℤ)
    rw [show ((1 : ℤ) : ZMod 2) = 1 by norm_cast] at this
    rw [this]
    show (1 : ℤ) • Q₁ = Q₁
    rw [one_smul]
  have hf₂ : f₂ 1 = Q₂ := by
    have := ZMod.lift_coe 2 (⟨zmultiplesHom _ Q₂, hz₂⟩ :
      {f : ℤ →+ ((P.freyCurve)⁄ℚ).Point // f 2 = 0}) (1 : ℤ)
    rw [show ((1 : ℤ) : ZMod 2) = 1 by norm_cast] at this
    rw [this]
    show (1 : ℤ) • Q₂ = Q₂
    rw [one_smul]
  refine ⟨f₁.coprod f₂, (injective_iff_map_eq_zero _).mpr ?_⟩
  rintro ⟨i, j⟩ hx
  rw [AddMonoidHom.coprod_apply] at hx
  have hcases : ∀ i : ZMod 2, i = 0 ∨ i = 1 := by decide
  rcases hcases i with rfl | rfl <;> rcases hcases j with rfl | rfl
  · rfl
  · rw [map_zero, zero_add, hf₂] at hx
    exact absurd hx hQ₂0
  · rw [map_zero, add_zero, hf₁] at hx
    exact absurd hx hQ₁0
  · rw [hf₁, hf₂] at hx
    have h12 : Q₁ = Q₂ := by
      rw [eq_neg_of_add_eq_zero_left hx, hneg₂]
    exact absurd h12 hQ₁₂

end TwoTorsion

/-- **Serre's core, packaged with the 2-torsion** (DERIVED 2026-07-16 from
`exists_p_point_of_not_isIrreducible` and the PROVEN
`freyCurve_two_torsion_embedding`): if the mod-`p` representation of the
Frey curve is not irreducible, then some elliptic curve over `ℚ` has full
rational `2`-torsion and a rational point of order exactly `p`. In the
first case of the disjunction the curve is the Frey curve itself, whose
full rational `2`-torsion is proven; in the second the package is
supplied whole. -/
theorem FreyPackage.exists_two_torsion_and_p_point_of_not_isIrreducible
    (P : FreyPackage)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ₂ : (ZMod 2 × ZMod 2) →+ (E'⁄ℚ).Point) (_ : Function.Injective φ₂)
      (Q : (E'⁄ℚ).Point), addOrderOf Q = P.p := by
  rcases P.exists_p_point_of_not_isIrreducible h with ⟨Q, hQ⟩ | hpkg
  · obtain ⟨φ₂, hφ₂⟩ := P.freyCurve_two_torsion_embedding
    exact ⟨P.freyCurve, inferInstance, φ₂, hφ₂, Q, hQ⟩
  · exact hpkg

/-- **Serre's reducible-case embedding** (DERIVED 2026-07-16 from
`exists_two_torsion_and_p_point_of_not_isIrreducible` and the PROVEN
`embedding_assembly`): if the mod-`p` representation of the Frey curve is
not irreducible, then some elliptic curve over `ℚ` has a subgroup of
rational points isomorphic to `ℤ/2 × ℤ/2p` — the full rational
`2`-torsion and the rational point of order `p` produced by Serre's
analysis, assembled through the Chinese remainder isomorphism. -/
theorem FreyPackage.exists_torsion_embedding_of_not_isIrreducible (P : FreyPackage)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (ZMod 2 × ZMod (2 * P.p)) →+ (E'⁄ℚ).Point), Function.Injective φ := by
  obtain ⟨E', hE', φ₂, hφ₂, Q, hQ⟩ :=
    P.exists_two_torsion_and_p_point_of_not_isIrreducible h
  have hp2 : P.p ≠ 2 := by
    have := P.hp5
    omega
  obtain ⟨ψ, hψ⟩ := embedding_assembly P.pp hp2 φ₂ hφ₂ Q hQ
  exact ⟨E', hE', ψ, hψ⟩

/-- **An open subgroup of `G_ℚ` has finite quotient** (PROVEN
2026-07-16): `Γ ℚ = Gal(ℚ̄/ℚ)` is compact (mathlib's profinite-limit
instance, activated by `IsAlgClosure.isGalois`), and open subgroups of
compact groups have finite quotients. This is step (1) of the
`open_normal_subgroup_eq_top_of_inertia_le` route, compiled here to
certify that the entire instance chain synthesizes. -/
theorem finite_quotient_of_isOpen (H : Subgroup (Field.absoluteGaloisGroup ℚ))
    (hopen : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ))) :
    Finite (Field.absoluteGaloisGroup ℚ ⧸ H) :=
  Subgroup.quotient_finite_of_isOpen H hopen
