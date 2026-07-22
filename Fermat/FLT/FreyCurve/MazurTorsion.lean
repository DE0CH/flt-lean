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
-- The structure theorem for finite abelian groups
-- (`AddCommGroup.equiv_directSum_zmod_of_finite`) and the `ZMod` Chinese
-- remainder theorem (`ZMod.prodEquivPi`), used in the PROVEN rank-`≤ 2`
-- decomposition backing Mazur's classification.
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.ZMod.QuotientRing

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine

/-!
### Decomposition of Mazur's classification (2026-07-22)

`mazur_classification` is decomposed; after the third pass
(2026-07-22, night) the remaining SORRY leaves are exactly the
genuinely modular-curve-theoretic inputs:

* `mazur_point_order` (sorry node): Mazur's uniform bound — the order
  of a rational torsion point lies in `{1, …, 10, 12}` (Mazur 1977,
  Thm 8; Mazur 1978, "Rational isogenies of prime degree").
* `torsion_finite_rat` (DERIVED from `mazur_point_order`): the
  rational torsion subgroup is finite — every rational torsion point
  is killed by `2520 = lcm(1, …, 10, 12)`, and the geometric
  `2520`-torsion is finite.
* `not_full_odd_prime_torsion_rat` (PROVEN, from the DERIVED
  determinant node): no rational `(ℤ/ℓ)²` for an odd prime `ℓ` — a
  rational full level-`ℓ` structure trivializes the mod-`ℓ`
  representation, hence its determinant, the mod-`ℓ` cyclotomic
  character, forcing `μ_ℓ ⊆ ℚ`.
* `not_full_four_torsion_rat` (PROVEN 2026-07-22): no rational
  `(ℤ/4)²`, by the elementary square-product argument on the
  `2`-torsion abscissae (`cubic_vieta` + `halving_square` +
  `exists_halving_coords`, all PROVEN pure algebra).
* `not_full_torsion_rat` (DERIVED from the two preceding nodes): for
  `n ≥ 3` the full `n`-torsion is never rational.
* `not_two_ten_torsion`, `not_two_twelve_torsion` (sorry nodes): no
  rational `ℤ/2 × ℤ/10` or `ℤ/2 × ℤ/12` (the modular curves
  `X_1(2,10)` and `X_1(2,12)` have genus ≥ 1 and no non-cuspidal
  rational points; part of the fifteen-groups list of Mazur 1977).
* `not_two_cube_torsion` (PROVEN): no rational `(ℤ/2)³` — the geometric
  `2`-torsion has only `2² = 4` points.
* `AddCommGroup.exists_rank_le_two_decomposition` (PROVEN — pure
  finite-abelian-group bookkeeping over the structure theorem and the
  `ZMod` Chinese remainder theorem).
* `mazur_group_casework` (PROVEN): given the `ℤ/d × ℤ/n` shape, the
  order bound, and the two exclusions, the group is one of the fifteen.
-/

/-- **Mazur's uniform bound on orders of rational torsion points** (sorry
node): a rational torsion point of an elliptic curve over `ℚ` has order
in `{1, …, 10, 12}`. Mazur, "Modular curves and the Eisenstein ideal"
(Publ. Math. IHÉS 47, 1977), Thm 8, completed by "Rational isogenies of
prime degree" (Invent. Math. 44, 1978) for the prime orders `≥ 11`. -/
theorem WeierstrassCurve.mazur_point_order (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : Q ∈ Submodule.torsion ℤ (E⁄ℚ).Point) :
    addOrderOf Q ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Finiteness of the rational torsion subgroup** (DERIVED 2026-07-22
from the `mazur_point_order` leaf): the torsion subgroup of `E(ℚ)` is
finite. Every rational torsion point has order in `{1, …, 10, 12}` by
Mazur's uniform bound, hence is killed by `2520 = lcm(1, …, 10, 12)`;
the rational torsion therefore base-changes injectively into the
geometric `2520`-torsion, which has exactly `2520²` elements
(`TorsionCard.card_torsionBy`). The classical standalone routes
(Lutz–Nagell, injectivity of reduction at a good prime) are not needed
once the uniform bound is taken as the leaf. -/
theorem WeierstrassCurve.torsion_finite_rat (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (Submodule.torsion ℤ (E⁄ℚ).Point) := by
  classical
  have hcard : Nat.card
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2520) = 2520 ^ 2 :=
    TorsionCard.card_torsionBy (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) 2520
      (by norm_num)
  haveI hfin : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2520) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let ψ : (E⁄ℚ).Point →+ (E⁄(AlgebraicClosure ℚ)).Point :=
    Affine.Point.map (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ))
  let f : Submodule.torsion ℤ (E⁄ℚ).Point →
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2520 := fun Q =>
    ⟨show ((E.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point from
      ψ Q.1, by
        rw [Submodule.mem_torsionBy_iff]
        have h2520 : (2520 : ℕ) • (Q.1 : (E⁄ℚ).Point) = 0 := by
          have horder := E.mazur_point_order Q.1 Q.2
          simp only [Finset.mem_insert, Finset.mem_singleton] at horder
          have hdvd : addOrderOf (Q.1 : (E⁄ℚ).Point) ∣ 2520 := by
            rcases horder with h | h | h | h | h | h | h | h | h | h | h <;>
              rw [h] <;> norm_num
          exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd
        show ((2520 : ℕ) : ℤ) • (ψ Q.1) = 0
        rw [natCast_zsmul, ← map_nsmul, h2520, map_zero]⟩
  have hfinj : Function.Injective f := by
    intro Q Q' hQQ
    have h1 : ψ Q.1 = ψ Q'.1 := congrArg Subtype.val hQQ
    exact Subtype.ext (Affine.Point.map_injective (W' := E)
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ)) h1)
  exact Finite.of_injective f hfinj

/-- The standard embedding of `ℤ/m` into `ℤ/N` for `0 < m ∣ N ≠ 0`
(sending `1` to `N/m`), packaged as an existential (PROVEN): used to
push a full level-`n` structure down to full level-`ℓ` structures at
the prime(-power) divisors `ℓ` of `n`, and to inject cyclic pieces of a
finite abelian group into the factors of its primary decomposition. -/
lemma ZMod.exists_injective_addMonoidHom_of_dvd {m N : ℕ} (hm : 0 < m)
    (hdvd : m ∣ N) (hN : 0 < N) :
    ∃ g : ZMod m →+ ZMod N, Function.Injective g := by
  classical
  obtain ⟨t, rfl⟩ := hdvd
  have ht : 0 < t := Nat.pos_of_ne_zero fun h => by simp [h] at hN
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero (m * t) := ⟨hN.ne'⟩
  have hker : (zmultiplesHom (ZMod (m * t))) ((t : ZMod (m * t))) (m : ℤ) = 0 := by
    rw [zmultiplesHom_apply, zsmul_eq_mul]
    push_cast
    rw [← Nat.cast_mul, ZMod.natCast_self]
  refine ⟨ZMod.lift m ⟨(zmultiplesHom (ZMod (m * t))) ((t : ZMod (m * t))), hker⟩, ?_⟩
  intro x y hxy
  -- reduce to the vanishing on the difference
  have hsub : ZMod.lift m ⟨(zmultiplesHom (ZMod (m * t))) ((t : ZMod (m * t))), hker⟩
      (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  set z : ZMod m := x - y
  -- compute the lift on `z` as a natural multiple of `t`
  have hcast : ((((z.val : ℕ) : ℤ) : ZMod m)) = z := by
    push_cast
    exact ZMod.natCast_rightInverse z
  have hgz : ZMod.lift m ⟨(zmultiplesHom (ZMod (m * t))) ((t : ZMod (m * t))), hker⟩
      ((((z.val : ℕ) : ℤ) : ZMod m)) = ((z.val * t : ℕ) : ZMod (m * t)) := by
    rw [ZMod.lift_coe, zmultiplesHom_apply, zsmul_eq_mul]
    push_cast
    ring
  rw [hcast, hsub] at hgz
  have hz0 : ((z.val * t : ℕ) : ZMod (m * t)) = 0 := hgz.symm
  rw [ZMod.natCast_eq_zero_iff] at hz0
  -- cancel `t`: `m ∣ z.val`, so `z.val = 0` by size
  have hdvd' : m ∣ z.val := by
    rcases hz0 with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h2 : z.val * t = (m * c) * t := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_right ht h2
  have hzero : z.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (ZMod.val_lt z)
  have hz : z = 0 := by rw [← hcast, hzero]; simp
  exact sub_eq_zero.mp hz

set_option backward.isDefEq.respectTransparency false in
/-- **Irrationality of full `ℓ`-torsion at an odd prime** (PROVEN
2026-07-22 from the DERIVED determinant node
`det_galoisRep_eq_cyclotomic`): the rational points of an elliptic
curve over `ℚ` contain no subgroup isomorphic to `(ℤ/ℓ)²` for an odd
prime `ℓ`. A rational full level-`ℓ` structure base-changes to all of
the geometric `ℓ`-torsion (both sides have `ℓ²` elements), so the mod-`ℓ`
representation is trivial; its determinant — the mod-`ℓ` cyclotomic
character, by the determinant node — is then trivial, making every
`ℓ`-th root of unity Galois-fixed, hence rational
(`InfiniteGalois.mem_range_algebraMap_iff_fixed`). But a primitive
`ℓ`-th root of unity is not `1`, while `x ↦ x^ℓ` is injective on `ℚ`
for odd `ℓ`. Silverman AEC III.8, Cor 8.1.1. -/
theorem WeierstrassCurve.not_full_odd_prime_torsion_rat (E : WeierstrassCurve ℚ)
    [E.IsElliptic] {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (φ : (ZMod ℓ × ZMod ℓ) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  intro hφ
  -- the geometric `ℓ`-torsion has `ℓ²` elements
  have hcard : Nat.card
      ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion ℓ) = ℓ ^ 2 :=
    TorsionCard.card_torsionBy (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) ℓ
      (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  haveI hfin : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion ℓ) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hℓ.ne_zero)
  -- base-change the rational level structure into the geometric torsion
  let ψ : (E⁄ℚ).Point →+ (E⁄(AlgebraicClosure ℚ)).Point :=
    Affine.Point.map (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ))
  have hkill : ∀ z : ZMod ℓ × ZMod ℓ, (ℓ : ℕ) • z = 0 := by
    intro z
    have h1 : ∀ w : ZMod ℓ, (ℓ : ℕ) • w = 0 := fun w => by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    exact Prod.ext (h1 z.1) (h1 z.2)
  let f : (ZMod ℓ × ZMod ℓ) →
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion ℓ := fun z =>
    ⟨show ((E.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point from
      ψ (φ z), by
        rw [Submodule.mem_torsionBy_iff]
        show ((ℓ : ℕ) : ℤ) • (ψ (φ z)) = 0
        rw [natCast_zsmul, ← map_nsmul, ← map_nsmul, hkill z, map_zero, map_zero]⟩
  have hfinj : Function.Injective f := by
    intro z z' hzz
    exact hφ (Affine.Point.map_injective (W' := E)
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ)) (congrArg Subtype.val hzz))
  -- by cardinality the level structure exhausts the geometric torsion
  have hfbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr
      ⟨hfinj, by rw [hcard, Nat.card_prod, Nat.card_zmod]; ring⟩
  -- so the mod-`ℓ` representation is trivial …
  have hfixall : ∀ (g : Field.absoluteGaloisGroup ℚ)
      (v : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion ℓ),
      E.galoisRep ℓ hℓ.pos g v = v := by
    intro g v
    obtain ⟨z, rfl⟩ := hfbij.surjective v
    refine Subtype.ext ?_
    show Affine.Point.map
        (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (ψ (φ z)) =
      ψ (φ z)
    show Affine.Point.map
        (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom
        (Affine.Point.map (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (φ z)) =
      Affine.Point.map (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (φ z)
    rw [Affine.Point.map_map]
    have hcomp : ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
          AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).comp
        (Algebra.ofId ℚ (AlgebraicClosure ℚ)) =
        Algebra.ofId ℚ (AlgebraicClosure ℚ) :=
      AlgHom.ext fun x => by
        simp only [AlgHom.comp_apply, Algebra.ofId_apply]
        exact AlgHom.commutes _ x
    rw [hcomp]
  have hrep1 : ∀ g : Field.absoluteGaloisGroup ℚ, E.galoisRep ℓ hℓ.pos g = 1 := by
    intro g
    apply LinearMap.ext
    intro v
    rw [Module.End.one_apply]
    exact hfixall g v
  -- … its determinant, the mod-`ℓ` cyclotomic character, is trivial …
  have hchar : ∀ g : Field.absoluteGaloisGroup ℚ,
      GaloisRepresentation.cyclotomicCharacterModL ℓ g = 1 := by
    intro g
    have hdet := WeilPairing.det_galoisRep_eq_cyclotomic E ℓ hℓ.pos hodd g
    rw [hrep1 g, Module.End.one_eq_id, LinearMap.det_id] at hdet
    apply Units.ext
    rw [Units.val_one, WeilPairing.cyclotomicCharacterModL_eq_toZMod ℓ g]
    exact hdet.symm
  -- … so every `ℓ`-th root of unity is Galois-fixed, hence rational
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) ℓ
  have hζfix : ∀ σ : Field.absoluteGaloisGroup ℚ, σ ζ = ζ := by
    intro σ
    have h1 := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) ℓ)
      (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
        (AlgebraicClosure ℚ) σ) hζ.toRootsOfUnity.2
    have h2 : modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) ℓ)
        (MulSemiringAction.toRingAut (Field.absoluteGaloisGroup ℚ)
          (AlgebraicClosure ℚ) σ) =
        GaloisRepresentation.cyclotomicCharacterModL ℓ σ := rfl
    rw [h2, hchar σ, Units.val_one, ZMod.val_one, pow_one] at h1
    have h3 : ((hζ.toRootsOfUnity : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
        ζ := hζ.val_toRootsOfUnity_coe
    rw [h3] at h1
    exact h1
  have hrat : ζ ∈ Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed ζ).mpr hζfix
  obtain ⟨q, hq⟩ := hrat
  -- a rational `ℓ`-th root of unity is `1` for odd `ℓ` …
  have hq1 : q ^ ℓ = 1 := by
    have h1 : ζ ^ ℓ = 1 := hζ.pow_eq_one
    rw [← hq, ← map_pow] at h1
    have h2 : algebraMap ℚ (AlgebraicClosure ℚ) (q ^ ℓ) =
        algebraMap ℚ (AlgebraicClosure ℚ) 1 := by rw [map_one]; exact h1
    exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective h2
  have hqone : q = 1 := (hodd.strictMono_pow (R := ℚ)).injective
    (by simpa using hq1)
  -- … contradicting primitivity (`ℓ ≥ 3 > 1`)
  rw [hqone, map_one] at hq
  exact hζ.ne_one hℓ.one_lt hq.symm

/-- **Vieta's formulas for the `2`-division cubic** (PROVEN — pure field
algebra by pairwise root elimination): if `4t³ + Bt² + Ct + D` has three
distinct roots `T`, `U`, `V`, then its coefficients are the scaled
elementary symmetric functions of the roots. Consumed by
`not_full_four_torsion_rat` to identify the `2`-division cubic
`4x³ + b₂x² + 2b₄x + b₆` of a curve with full rational `2`-torsion. -/
lemma MazurFourTorsion.cubic_vieta {B C D T U V : ℚ} (hTU : T ≠ U)
    (hTV : T ≠ V) (hUV : U ≠ V)
    (h1 : 4 * T ^ 3 + B * T ^ 2 + C * T + D = 0)
    (h2 : 4 * U ^ 3 + B * U ^ 2 + C * U + D = 0)
    (h3 : 4 * V ^ 3 + B * V ^ 2 + C * V + D = 0) :
    B = -4 * (T + U + V) ∧ C = 4 * (T * U + T * V + U * V) ∧
      D = -4 * (T * U * V) := by
  have q12 : (T - U) * (4 * (T ^ 2 + T * U + U ^ 2) + B * (T + U) + C) = 0 := by
    linear_combination h1 - h2
  have h12 : 4 * (T ^ 2 + T * U + U ^ 2) + B * (T + U) + C = 0 :=
    (mul_eq_zero.mp q12).resolve_left (sub_ne_zero.mpr hTU)
  have q13 : (T - V) * (4 * (T ^ 2 + T * V + V ^ 2) + B * (T + V) + C) = 0 := by
    linear_combination h1 - h3
  have h13 : 4 * (T ^ 2 + T * V + V ^ 2) + B * (T + V) + C = 0 :=
    (mul_eq_zero.mp q13).resolve_left (sub_ne_zero.mpr hTV)
  have q23 : (U - V) * (4 * (T + U + V) + B) = 0 := by
    linear_combination h12 - h13
  have hB : B = -4 * (T + U + V) := by
    have h0 := (mul_eq_zero.mp q23).resolve_left (sub_ne_zero.mpr hUV)
    linarith
  have hC : C = 4 * (T * U + T * V + U * V) := by
    linear_combination h12 - (T + U) * hB
  have hD : D = -4 * (T * U * V) := by
    linear_combination h1 - T ^ 2 * hB - T * hC
  exact ⟨hB, hC, hD⟩

/-- **The halving square identity** (PROVEN — pure field algebra): if a
point `(x, y)` on a Weierstrass curve doubles, by the tangent-line
formula (`hl` is the cleared slope equation, `hx` the `addX` output),
onto the `2`-torsion abscissa `T`, and `T`, `U`, `V` satisfy the Vieta
identities of the `2`-division cubic (`b₂ = -4σ₁`, `2b₄ = 4σ₂`,
`b₆ = -4σ₃`), then `(T − U)(T − V) = (x − T)²` is a square. This is the
classical identity `x(2P) − e₁ = ((x − e₁)² − (e₁ − e₂)(e₁ − e₃))²/w²`
(`w = 2y + a₁x + a₃`) behind the criterion for halving `2`-torsion
points; the proof is a chain of `linear_combination` certificates
through the completed-square substitution `Y = y + (a₁x + a₃)/2`.
Consumed by `not_full_four_torsion_rat`. -/
lemma MazurFourTorsion.halving_square {a₁ a₂ a₃ a₄ a₆ x y l T U V : ℚ}
    (heq : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hB : a₁ ^ 2 + 4 * a₂ = -4 * (T + U + V))
    (hC : 2 * a₁ * a₃ + 4 * a₄ = 4 * (T * U + T * V + U * V))
    (hD : a₃ ^ 2 + 4 * a₆ = -4 * (T * U * V))
    (hl : l * (2 * y + a₁ * x + a₃) = 3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hx : l ^ 2 + a₁ * l - a₂ - x - x = T) :
    (T - U) * (T - V) = (x - T) ^ 2 := by
  -- the `2`-division cubic factors through the three abscissae
  have hw2 : (2 * y + a₁ * x + a₃) ^ 2 = 4 * ((x - T) * (x - U) * (x - V)) := by
    linear_combination 4 * heq + x ^ 2 * hB + x * hC + hD
  -- the completed-square slope `l + a₁/2` clears to the derivative
  have hFp : (l + a₁ / 2) * (2 * y + a₁ * x + a₃) =
      3 * x ^ 2 - 2 * (T + U + V) * x + (T * U + T * V + U * V) := by
    linear_combination hl + x / 2 * hB + (1 : ℚ) / 4 * hC
  -- the doubling output in completed-square form
  have hly : (l + a₁ / 2) ^ 2 = 2 * x + T - (T + U + V) := by
    linear_combination hx + (1 : ℚ) / 4 * hB
  -- the square of the defect vanishes …
  have hN2 : ((x - T) ^ 2 - (T - U) * (T - V)) ^ 2 = 0 := by
    linear_combination
      (-(3 * x ^ 2 - 2 * (T + U + V) * x + (T * U + T * V + U * V)) -
          (l + a₁ / 2) * (2 * y + a₁ * x + a₃)) * hFp +
        (2 * y + a₁ * x + a₃) ^ 2 * hly + (2 * x + T - (T + U + V)) * hw2
  -- … so the defect vanishes
  have hN : (x - T) ^ 2 - (T - U) * (T - V) = 0 := sq_eq_zero_iff.mp hN2
  linarith

/-- **Coordinate extraction for a halved `2`-torsion point** (PROVEN):
if `P + P = T` with `T ≠ 0` of order dividing `2`, then `T` is an affine
point `(θ, u)` on the `2`-torsion locus (`u = negY θ u`), `P` is an
affine point `(x, y)`, and the tangent-line doubling formula lands on
`θ`: the slope `l` satisfies the cleared slope equation and
`l² + a₁l − a₂ − 2x = θ`. Consumed by `not_full_four_torsion_rat`. -/
lemma MazurFourTorsion.exists_halving_coords {W : WeierstrassCurve.Affine ℚ}
    (P T : W.Point) (hPT : P + P = T) (hT2 : T + T = 0) (hT0 : T ≠ 0) :
    ∃ θ u x y l : ℚ,
      (∃ hns : W.Nonsingular θ u, T = Point.some θ u hns) ∧
      W.Equation θ u ∧ u = W.negY θ u ∧ W.Equation x y ∧
      l * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ∧
      l ^ 2 + W.a₁ * l - W.a₂ - x - x = θ := by
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, add_zero] at hPT
    exact hT0 hPT.symm
  rcases T with _ | ⟨θ, u, hns⟩
  · exact absurd rfl hT0
  · -- the `2`-torsion condition pins the ordinate: `u = negY θ u`
    have hneg : -Point.some θ u hns = Point.some θ u hns :=
      neg_eq_of_add_eq_zero_left hT2
    rw [Point.neg_some] at hneg
    have hu : W.negY θ u = u := (Point.some.inj hneg).2
    rcases P with _ | ⟨x, y, hPns⟩
    · exact absurd rfl hP0
    · -- `P` is not `2`-torsion (its double `T` is nonzero), so the
      -- tangent-line doubling formula applies
      have hy : y ≠ W.negY x y := fun h =>
        hT0 (hPT.symm.trans (Point.add_self_of_Y_eq h))
      have hadd := Point.add_self_of_Y_ne (h₁ := hPns) hy
      have hθ : W.addX x x (W.slope x x y y) = θ :=
        (Point.some.inj (hadd.symm.trans hPT)).1
      have hsub : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
        rw [negY]; ring
      have hlm : W.slope x x y y * (2 * y + W.a₁ * x + W.a₃) =
          3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
        rw [← hsub, slope_of_Y_ne rfl hy,
          div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
      simp only [addX] at hθ
      exact ⟨θ, u, x, y, W.slope x x y y, ⟨hns, rfl⟩, hns.1, hu.symm,
        hPns.1, hlm, hθ⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Irrationality of full `4`-torsion** (PROVEN 2026-07-22 by the
elementary square-product argument): the rational points of an elliptic
curve over `ℚ` contain no subgroup isomorphic to `(ℤ/4)²`. A rational
full level-`4` structure gives three rational points of order `4`
doubling onto the three distinct rational `2`-torsion points
`(θᵢ, uᵢ)`; the θᵢ are then the roots of the `2`-division cubic
`4x³ + b₂x² + 2b₄x + b₆` (`cubic_vieta`), and each halving forces
`(θᵢ − θⱼ)(θᵢ − θₖ)` to be a rational square (`halving_square`). But
the product of the three is `−((θ₁−θ₂)(θ₁−θ₃)(θ₂−θ₃))² < 0`, while a
product of nonzero rational squares is positive — absurd. (The
arithmetic content is `μ₄ ⊄ ℚ`; the Weil-pairing/determinant route
used for odd primes is unavailable here since
`det_galoisRep_eq_cyclotomic` requires `Odd p`.) Silverman AEC III.8,
Cor 8.1.1. -/
theorem WeierstrassCurve.not_full_four_torsion_rat (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (φ : (ZMod 4 × ZMod 4) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  -- the doubling relations `φ(z) + φ(z) = φ(2z)` for the three order-`4`
  -- elements `(1,0)`, `(0,1)`, `(1,1)` …
  have hdb1 : φ (1, 0) + φ (1, 0) = φ (2, 0) := by
    rw [← map_add]; exact congrArg φ (by decide)
  have hdb2 : φ (0, 1) + φ (0, 1) = φ (0, 2) := by
    rw [← map_add]; exact congrArg φ (by decide)
  have hdb3 : φ (1, 1) + φ (1, 1) = φ (2, 2) := by
    rw [← map_add]; exact congrArg φ (by decide)
  -- … the `2`-torsion relations for their doubles …
  have htor1 : φ (2, 0) + φ (2, 0) = 0 := by
    rw [← map_add, show ((2 : ZMod 4), (0 : ZMod 4)) + (2, 0) = 0 by decide,
      map_zero]
  have htor2 : φ (0, 2) + φ (0, 2) = 0 := by
    rw [← map_add, show ((0 : ZMod 4), (2 : ZMod 4)) + (0, 2) = 0 by decide,
      map_zero]
  have htor3 : φ (2, 2) + φ (2, 2) = 0 := by
    rw [← map_add, show ((2 : ZMod 4), (2 : ZMod 4)) + (2, 2) = 0 by decide,
      map_zero]
  -- … and their nontriviality and pairwise distinctness, by injectivity
  have hne1 : φ (2, 0) ≠ 0 := fun h =>
    absurd (hφ (h.trans (map_zero φ).symm)) (by decide)
  have hne2 : φ (0, 2) ≠ 0 := fun h =>
    absurd (hφ (h.trans (map_zero φ).symm)) (by decide)
  have hne3 : φ (2, 2) ≠ 0 := fun h =>
    absurd (hφ (h.trans (map_zero φ).symm)) (by decide)
  have hne12 : φ (2, 0) ≠ φ (0, 2) := fun h => absurd (hφ h) (by decide)
  have hne13 : φ (2, 0) ≠ φ (2, 2) := fun h => absurd (hφ h) (by decide)
  have hne23 : φ (0, 2) ≠ φ (2, 2) := fun h => absurd (hφ h) (by decide)
  -- extract the affine coordinates of the three halvings
  obtain ⟨θ₁, u₁, x₁, y₁, l₁, ⟨hns₁, hTeq₁⟩, hE₁, hu₁, hP₁, hl₁, hx₁⟩ :=
    MazurFourTorsion.exists_halving_coords _ _ hdb1 htor1 hne1
  obtain ⟨θ₂, u₂, x₂, y₂, l₂, ⟨hns₂, hTeq₂⟩, hE₂, hu₂, hP₂, hl₂, hx₂⟩ :=
    MazurFourTorsion.exists_halving_coords _ _ hdb2 htor2 hne2
  obtain ⟨θ₃, u₃, x₃, y₃, l₃, ⟨hns₃, hTeq₃⟩, hE₃, hu₃, hP₃, hl₃, hx₃⟩ :=
    MazurFourTorsion.exists_halving_coords _ _ hdb3 htor3 hne3
  rw [negY] at hu₁ hu₂ hu₃
  rw [equation_iff] at hE₁ hE₂ hE₃ hP₁ hP₂ hP₃
  -- distinct `2`-torsion points have distinct abscissae (the ordinate
  -- is determined by `2u = -(a₁θ + a₃)`)
  have hd12 : θ₁ ≠ θ₂ := by
    intro h
    subst h
    have huu : u₁ = u₂ := by linarith
    subst huu
    rw [hTeq₁, hTeq₂] at hne12
    exact hne12 rfl
  have hd13 : θ₁ ≠ θ₃ := by
    intro h
    subst h
    have huu : u₁ = u₃ := by linarith
    subst huu
    rw [hTeq₁, hTeq₃] at hne13
    exact hne13 rfl
  have hd23 : θ₂ ≠ θ₃ := by
    intro h
    subst h
    have huu : u₂ = u₃ := by linarith
    subst huu
    rw [hTeq₂, hTeq₃] at hne23
    exact hne23 rfl
  -- the three abscissae are roots of the `2`-division cubic
  have hroot₁ : 4 * θ₁ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ₁ ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ₁ +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * u₁ + (E⁄ℚ).a₁ * θ₁ + (E⁄ℚ).a₃) * hu₁ - 4 * hE₁
  have hroot₂ : 4 * θ₂ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ₂ ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ₂ +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * u₂ + (E⁄ℚ).a₁ * θ₂ + (E⁄ℚ).a₃) * hu₂ - 4 * hE₂
  have hroot₃ : 4 * θ₃ ^ 3 + ((E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂) * θ₃ ^ 2 +
      (2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄) * θ₃ +
      ((E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆) = 0 := by
    linear_combination (2 * u₃ + (E⁄ℚ).a₁ * θ₃ + (E⁄ℚ).a₃) * hu₃ - 4 * hE₃
  obtain ⟨hB, hC, hD⟩ :=
    MazurFourTorsion.cubic_vieta hd12 hd13 hd23 hroot₁ hroot₂ hroot₃
  -- each halving makes `(θᵢ − θⱼ)(θᵢ − θₖ)` a rational square
  have k₁ : (θ₁ - θ₂) * (θ₁ - θ₃) = (x₁ - θ₁) ^ 2 :=
    MazurFourTorsion.halving_square hP₁ hB hC hD hl₁ hx₁
  have hB₂ : (E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂ = -4 * (θ₂ + θ₁ + θ₃) := by
    linear_combination hB
  have hC₂ : 2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄ =
      4 * (θ₂ * θ₁ + θ₂ * θ₃ + θ₁ * θ₃) := by
    linear_combination hC
  have hD₂ : (E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆ = -4 * (θ₂ * θ₁ * θ₃) := by
    linear_combination hD
  have k₂ : (θ₂ - θ₁) * (θ₂ - θ₃) = (x₂ - θ₂) ^ 2 :=
    MazurFourTorsion.halving_square hP₂ hB₂ hC₂ hD₂ hl₂ hx₂
  have hB₃ : (E⁄ℚ).a₁ ^ 2 + 4 * (E⁄ℚ).a₂ = -4 * (θ₃ + θ₁ + θ₂) := by
    linear_combination hB
  have hC₃ : 2 * (E⁄ℚ).a₁ * (E⁄ℚ).a₃ + 4 * (E⁄ℚ).a₄ =
      4 * (θ₃ * θ₁ + θ₃ * θ₂ + θ₁ * θ₂) := by
    linear_combination hC
  have hD₃ : (E⁄ℚ).a₃ ^ 2 + 4 * (E⁄ℚ).a₆ = -4 * (θ₃ * θ₁ * θ₂) := by
    linear_combination hD
  have k₃ : (θ₃ - θ₁) * (θ₃ - θ₂) = (x₃ - θ₃) ^ 2 :=
    MazurFourTorsion.halving_square hP₃ hB₃ hC₃ hD₃ hl₃ hx₃
  -- but the product of the three squares is minus a nonzero square
  have hDne : (θ₁ - θ₂) * (θ₁ - θ₃) * (θ₂ - θ₃) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hd12) (sub_ne_zero.mpr hd13))
      (sub_ne_zero.mpr hd23)
  have hprod : ((x₁ - θ₁) * (x₂ - θ₂) * (x₃ - θ₃)) ^ 2 =
      -(((θ₁ - θ₂) * (θ₁ - θ₃) * (θ₂ - θ₃)) ^ 2) := by
    linear_combination (-(x₂ - θ₂) ^ 2 * (x₃ - θ₃) ^ 2) * k₁ -
      ((θ₁ - θ₂) * (θ₁ - θ₃) * (x₃ - θ₃) ^ 2) * k₂ -
      ((θ₁ - θ₂) * (θ₁ - θ₃) * (θ₂ - θ₁) * (θ₂ - θ₃)) * k₃
  have hpos : (0 : ℚ) < ((θ₁ - θ₂) * (θ₁ - θ₃) * (θ₂ - θ₃)) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hDne))
  linarith [sq_nonneg ((x₁ - θ₁) * (x₂ - θ₂) * (x₃ - θ₃)), hprod, hpos]

/-- **Irrationality of full `n`-torsion for `n ≥ 3`** (DERIVED
2026-07-22 from the PROVEN odd-prime case
`not_full_odd_prime_torsion_rat` and the level-`4` leaf
`not_full_four_torsion_rat`): the rational points of an elliptic curve
over `ℚ` contain no subgroup isomorphic to `(ℤ/n)²` for `n ≥ 3`.
Reduction: if an odd prime `ℓ` divides `n`, the `(n/ℓ)`-multiples give
`(ℤ/ℓ)² ↪ (ℤ/n)²`; otherwise `n ≥ 3` is a power of `2`, so `4 ∣ n` and
`(ℤ/4)² ↪ (ℤ/n)²`. Silverman AEC III.8. -/
theorem WeierstrassCurve.not_full_torsion_rat (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} (hn : 3 ≤ n) (φ : (ZMod n × ZMod n) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  by_cases hoddfac : ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ ℓ ∣ n
  · obtain ⟨ℓ, hℓp, hℓodd, hℓdvd⟩ := hoddfac
    obtain ⟨g, hg⟩ := ZMod.exists_injective_addMonoidHom_of_dvd hℓp.pos hℓdvd
      (by omega)
    have hgg : Function.Injective (g.prodMap g) := by
      rw [AddMonoidHom.coe_prodMap]
      exact hg.prodMap hg
    exact E.not_full_odd_prime_torsion_rat hℓp hℓodd (φ.comp (g.prodMap g))
      (hφ.comp hgg)
  · -- `n` is a power of `2`, so `4 ∣ n`
    have h4 : 4 ∣ n := by
      have h2 : ∀ {d : ℕ}, d.Prime → d ∣ n → d = 2 := by
        intro d hd hdvd
        by_contra hne
        exact hoddfac ⟨d, hd, hd.odd_of_ne_two hne, hdvd⟩
      have hpow := Nat.eq_prime_pow_of_unique_prime_dvd
        (n := n) (p := 2) (by omega) h2
      set k := n.primeFactorsList.length
      have hk2 : 2 ≤ k := by
        by_contra hklt
        have hklt' : k < 2 := by omega
        interval_cases k <;> norm_num at hpow <;> omega
      calc (4 : ℕ) = 2 ^ 2 := rfl
        _ ∣ 2 ^ k := pow_dvd_pow 2 hk2
        _ = n := hpow.symm
    obtain ⟨g, hg⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by norm_num) h4 (by omega)
    have hgg : Function.Injective (g.prodMap g) := by
      rw [AddMonoidHom.coe_prodMap]
      exact hg.prodMap hg
    exact E.not_full_four_torsion_rat (φ.comp (g.prodMap g)) (hφ.comp hgg)

/-- **Exclusion of rational `ℤ/2 × ℤ/10`** (sorry node): the modular
curve `X_1(2,10)` has no non-cuspidal rational point (Mazur 1977; the
list of fifteen). -/
theorem WeierstrassCurve.not_two_ten_torsion (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (φ : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ :=
  sorry

/-- **Exclusion of rational `ℤ/2 × ℤ/12`** (sorry node): the modular
curve `X_1(2,12)` has no non-cuspidal rational point (Mazur 1977; the
list of fifteen). -/
theorem WeierstrassCurve.not_two_twelve_torsion (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (φ : (ZMod 2 × ZMod 12) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **No rational `(ℤ/2)³`** (PROVEN 2026-07-22): the geometric
`2`-torsion of an elliptic curve has exactly `2² = 4` points
(`TorsionCard.card_torsionBy`), so already over `ℚ̄` there is no
injective `(ℤ/2)³`; a rational one would base-change to one. -/
theorem WeierstrassCurve.not_two_cube_torsion (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (φ : (ZMod 2 × ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  classical
  intro hφ
  -- the geometric `2`-torsion has `4` elements
  have hcard : Nat.card ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2) = 2 ^ 2 :=
    TorsionCard.card_torsionBy (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) 2
      (Nat.cast_ne_zero.mpr two_ne_zero)
  haveI hfin : Finite ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  -- every element of `(ℤ/2)³` is killed by `2`
  have h2ann : ∀ z : ZMod 2 × ZMod 2 × ZMod 2, (2 : ℕ) • z = 0 := by decide
  -- base-change the embedding to `ℚ̄` and corestrict to the `2`-torsion
  let ψ : (ZMod 2 × ZMod 2 × ZMod 2) →+ (E⁄(AlgebraicClosure ℚ)).Point :=
    (Affine.Point.map (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ))).comp φ
  let f : (ZMod 2 × ZMod 2 × ZMod 2) → (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2 :=
    fun z => ⟨show ((E.map (algebraMap ℚ (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point from
      ψ z, by
        rw [Submodule.mem_torsionBy_iff]
        show ((2 : ℕ) : ℤ) • (ψ z) = 0
        rw [natCast_zsmul, ← map_nsmul, h2ann z, map_zero]⟩
  have hfinj : Function.Injective f := by
    intro z z' hzz
    have h1 : ψ z = ψ z' := congrArg Subtype.val hzz
    have h2 : Affine.Point.map (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (φ z) =
        Affine.Point.map (W' := E) (Algebra.ofId ℚ (AlgebraicClosure ℚ)) (φ z') := h1
    exact hφ (Affine.Point.map_injective (W' := E)
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ)) h2)
  have hle : Nat.card (ZMod 2 × ZMod 2 × ZMod 2) ≤
      Nat.card ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion 2) :=
    Nat.card_le_card_of_injective f hfinj
  rw [hcard, Nat.card_prod, Nat.card_prod, Nat.card_zmod] at hle
  norm_num at hle

open scoped Function in
set_option backward.isDefEq.respectTransparency false in
/-- **Rank-`≤ 2` structure of the candidate torsion groups** (PROVEN
2026-07-22 — PURE FINITE ABELIAN GROUP THEORY, no arithmetic input): a
finite abelian group containing no subgroup `(ℤ/n)²` for any `n ≥ 3`
and no subgroup `(ℤ/2)³` is isomorphic to `ℤ/d × ℤ/n` with
`d ∈ {1, 2}`. Bookkeeping over the structure theorem
(`AddCommGroup.equiv_directSum_zmod_of_finite`): two prime-power
factors at the same odd prime `q` would give `(ℤ/q)²`, two `2`-power
factors of exponents `≥ 2` would give `(ℤ/4)²`, and three even factors
would give `(ℤ/2)³` — so at most one factor per odd prime, and the
`2`-part is at worst `ℤ/2 × ℤ/2^k`. Splitting off the (single) `ℤ/2`
factor if present, the remaining factors are pairwise coprime and merge
into a single cyclic group by the Chinese remainder theorem
(`ZMod.prodEquivPi`). -/
theorem AddCommGroup.exists_rank_le_two_decomposition
    (T : Type*) [AddCommGroup T] [Finite T]
    (hfull : ∀ n : ℕ, 3 ≤ n → ∀ φ : (ZMod n × ZMod n) →+ T, ¬ Function.Injective φ)
    (hcube : ∀ φ : (ZMod 2 × ZMod 2 × ZMod 2) →+ T, ¬ Function.Injective φ) :
    ∃ (d n : ℕ), (d = 1 ∨ d = 2) ∧ Nonempty (T ≃+ (ZMod d × ZMod n)) := by
  classical
  obtain ⟨ι, hι, p, hp, e, ⟨eqv0⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite T
  haveI := hι
  set a : ι → ℕ := fun i => p i ^ e i
  have hapos : ∀ i, 0 < a i := fun i => pow_pos (hp i).pos _
  let eqv : T ≃+ ∀ i, ZMod (a i) := eqv0.trans (DirectSum.addEquivProd _)
  -- (i) two distinct factors both divisible by `m ≥ 3` embed `(ℤ/m)²`
  have hpair : ∀ (m : ℕ), 3 ≤ m → ∀ i j : ι, i ≠ j → m ∣ a i → m ∣ a j → False := by
    intro m hm i j hij hdi hdj
    obtain ⟨gi, hgi⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by omega) hdi (hapos i)
    obtain ⟨gj, hgj⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by omega) hdj (hapos j)
    let Φ : (ZMod m × ZMod m) →+ ∀ k, ZMod (a k) :=
      ((AddMonoidHom.single (fun k => ZMod (a k)) i).comp gi).coprod
        ((AddMonoidHom.single (fun k => ZMod (a k)) j).comp gj)
    have hΦ : Function.Injective Φ := by
      intro x y hxy
      have hxi : Φ x i = Φ y i := congrFun hxy i
      have hxj : Φ x j = Φ y j := congrFun hxy j
      simp only [Φ, AddMonoidHom.coprod_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.single_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
        add_zero, zero_add] at hxi hxj
      exact Prod.ext (hgi hxi) (hgj hxj)
    exact hfull m hm ((eqv.symm.toAddMonoidHom).comp Φ)
      ((eqv.symm.injective).comp hΦ)
  -- (ii) three distinct even factors embed `(ℤ/2)³`
  have htriple : ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k →
      2 ∣ a i → 2 ∣ a j → 2 ∣ a k → False := by
    intro i j k hij hik hjk hdi hdj hdk
    obtain ⟨gi, hgi⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by omega) hdi (hapos i)
    obtain ⟨gj, hgj⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by omega) hdj (hapos j)
    obtain ⟨gk, hgk⟩ := ZMod.exists_injective_addMonoidHom_of_dvd
      (by omega) hdk (hapos k)
    let Φ : (ZMod 2 × ZMod 2 × ZMod 2) →+ ∀ l, ZMod (a l) :=
      ((AddMonoidHom.single (fun l => ZMod (a l)) i).comp gi).coprod
        ((((AddMonoidHom.single (fun l => ZMod (a l)) j).comp gj).coprod
          ((AddMonoidHom.single (fun l => ZMod (a l)) k).comp gk)))
    have hΦ : Function.Injective Φ := by
      intro x y hxy
      have hxi : Φ x i = Φ y i := congrFun hxy i
      have hxj : Φ x j = Φ y j := congrFun hxy j
      have hxk : Φ x k = Φ y k := congrFun hxy k
      simp only [Φ, AddMonoidHom.coprod_apply, AddMonoidHom.comp_apply,
        AddMonoidHom.single_apply, Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
        Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hik.symm,
        Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjk.symm,
        add_zero, zero_add] at hxi hxj hxk
      exact Prod.ext (hgi hxi) (Prod.ext (hgj hxj) (hgk hxk))
    exact hcube ((eqv.symm.toAddMonoidHom).comp Φ)
      ((eqv.symm.injective).comp hΦ)
  -- the genuinely-even factors
  set S₂ : Finset ι := Finset.univ.filter (fun i => p i = 2 ∧ 1 ≤ e i) with hS₂
  have hS₂mem : ∀ {i}, i ∈ S₂ ↔ p i = 2 ∧ 1 ≤ e i := fun {i} => by
    simp [hS₂]
  have hdvd2 : ∀ {i}, i ∈ S₂ → 2 ∣ a i := by
    intro i hi
    rcases hS₂mem.mp hi with ⟨hp2, he⟩
    show 2 ∣ p i ^ e i
    rw [hp2]
    exact dvd_pow_self 2 (by omega)
  -- distinct same-prime genuine factors force the prime to be `2`
  have hsameprime : ∀ i j : ι, i ≠ j → 1 ≤ e i → 1 ≤ e j → p i = p j →
      p i = 2 := by
    intro i j hij hei hej hpp
    by_contra hne2
    have h3 : 3 ≤ p i := by
      have h2 := (hp i).two_le
      omega
    refine hpair (p i) h3 i j hij (dvd_pow_self (p i) (by omega)) ?_
    rw [hpp]
    show p j ∣ p j ^ e j
    exact dvd_pow_self (p j) (by omega)
  -- at most two genuinely-even factors
  have hS₂card : S₂.card ≤ 2 := by
    by_contra hgt
    obtain ⟨u, husub, hucard⟩ := Finset.exists_subset_card_eq (show 3 ≤ S₂.card by omega)
    obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hucard
    exact htriple i j k hij hik hjk
      (hdvd2 (husub (by simp))) (hdvd2 (husub (by simp))) (hdvd2 (husub (by simp)))
  by_cases hcard2 : S₂.card = 2
  · -- the `2`-part is `ℤ/2 × ℤ/2^k`: split off the `ℤ/2` factor
    obtain ⟨i₀, j₀, hij₀, hS₂eq⟩ := Finset.card_eq_two.mp hcard2
    have hi₀ : p i₀ = 2 ∧ 1 ≤ e i₀ := hS₂mem.mp (by rw [hS₂eq]; simp)
    have hj₀ : p j₀ = 2 ∧ 1 ≤ e j₀ := hS₂mem.mp (by rw [hS₂eq]; simp)
    -- one of the two exponents is exactly `1` (else `(ℤ/4)²`)
    have hnot44 : ¬ (2 ≤ e i₀ ∧ 2 ≤ e j₀) := by
      rintro ⟨h2i, h2j⟩
      refine hpair 4 (by norm_num) i₀ j₀ hij₀ ?_ ?_
      · show 4 ∣ p i₀ ^ e i₀
        rw [hi₀.1]
        exact (show (4 : ℕ) = 2 ^ 2 from rfl) ▸ pow_dvd_pow 2 h2i
      · show 4 ∣ p j₀ ^ e j₀
        rw [hj₀.1]
        exact (show (4 : ℕ) = 2 ^ 2 from rfl) ▸ pow_dvd_pow 2 h2j
    obtain ⟨i₁, j₁, hij₁, hS₂eq', hei₁⟩ :
        ∃ i₁ j₁ : ι, i₁ ≠ j₁ ∧ S₂ = {i₁, j₁} ∧ e i₁ = 1 := by
      rcases (show e i₀ = 1 ∨ e j₀ = 1 by
        rcases hi₀ with ⟨-, h1⟩; rcases hj₀ with ⟨-, h2⟩; omega) with h1 | h1
      · exact ⟨i₀, j₀, hij₀, hS₂eq, h1⟩
      · exact ⟨j₀, i₀, hij₀.symm, by rw [hS₂eq, Finset.pair_comm], h1⟩
    have hi₁ : p i₁ = 2 ∧ 1 ≤ e i₁ := hS₂mem.mp (by rw [hS₂eq']; simp)
    -- the factors away from `i₁` are pairwise coprime
    have hcop' : Pairwise (Nat.Coprime on fun x : {x : ι // x ≠ i₁} => a x.1) := by
      intro x y hxy
      show Nat.Coprime (p x.1 ^ e x.1) (p y.1 ^ e y.1)
      have hne : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      rcases Nat.eq_zero_or_pos (e x.1) with hex | hex
      · rw [hex, pow_zero]; exact Nat.coprime_one_left _
      rcases Nat.eq_zero_or_pos (e y.1) with hey | hey
      · rw [hey, pow_zero]; exact Nat.coprime_one_right _
      by_cases hpp : p x.1 = p y.1
      · exfalso
        have hp2 := hsameprime x.1 y.1 hne hex hey hpp
        have hxS : x.1 ∈ S₂ := hS₂mem.mpr ⟨hp2, hex⟩
        have hyS : y.1 ∈ S₂ := hS₂mem.mpr ⟨by rw [← hpp]; exact hp2, hey⟩
        rw [hS₂eq'] at hxS hyS
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxS hyS
        rcases hxS with h | h
        · exact x.2 h
        rcases hyS with h' | h'
        · exact y.2 h'
        exact hne (h.trans h'.symm)
      · exact Nat.Coprime.pow (e x.1) (e y.1)
          ((Nat.coprime_primes (hp _) (hp _)).mpr hpp)
    refine ⟨2, ∏ x : {x : ι // x ≠ i₁}, a x.1, Or.inr rfl, ⟨?_⟩⟩
    have hsplit : (∀ i, ZMod (a i)) ≃+
        ZMod (a i₁) × ∀ x : {x : ι // x ≠ i₁}, ZMod (a x.1) :=
      { Equiv.piSplitAt i₁ (fun i => ZMod (a i)) with
        map_add' := fun f g => rfl }
    have hai₁ : a i₁ = 2 := by
      show p i₁ ^ e i₁ = 2
      rw [hi₁.1, hei₁, pow_one]
    exact eqv.trans (hsplit.trans (AddEquiv.prodCongr
      (ZMod.ringEquivCongr hai₁).toAddEquiv
      (ZMod.prodEquivPi (fun x : {x : ι // x ≠ i₁} => a x.1)
        hcop').toAddEquiv.symm))
  · -- at most one genuinely-even factor: everything is pairwise coprime
    have hcard1 : S₂.card ≤ 1 := by omega
    have hcop : Pairwise (Nat.Coprime on a) := by
      intro i j hij
      show Nat.Coprime (p i ^ e i) (p j ^ e j)
      rcases Nat.eq_zero_or_pos (e i) with hei | hei
      · rw [hei, pow_zero]; exact Nat.coprime_one_left _
      rcases Nat.eq_zero_or_pos (e j) with hej | hej
      · rw [hej, pow_zero]; exact Nat.coprime_one_right _
      by_cases hpp : p i = p j
      · exfalso
        have hp2 := hsameprime i j hij hei hej hpp
        have hiS : i ∈ S₂ := hS₂mem.mpr ⟨hp2, hei⟩
        have hjS : j ∈ S₂ := hS₂mem.mpr ⟨by rw [← hpp]; exact hp2, hej⟩
        have h2 : 1 < S₂.card := Finset.one_lt_card.mpr ⟨i, hiS, j, hjS, hij⟩
        omega
      · exact Nat.Coprime.pow (e i) (e j)
          ((Nat.coprime_primes (hp i) (hp j)).mpr hpp)
    refine ⟨1, ∏ i, a i, Or.inl rfl, ⟨?_⟩⟩
    exact eqv.trans ((ZMod.prodEquivPi a hcop).toAddEquiv.symm.trans
      AddEquiv.uniqueProd.symm)

/-- **The fifteen-groups casework** (PROVEN 2026-07-22): an abelian
group of the shape `ℤ/d × ℤ/n` with `d ∈ {1, 2}`, all of whose element
orders lie in `{1, …, 10, 12}`, and containing no `ℤ/2 × ℤ/10` and no
`ℤ/2 × ℤ/12`, is one of Mazur's fifteen groups. Casework: for `d = 1`
the generator's order pins `n` in the list; for `d = 2` and `n` odd the
group is cyclic of order `2n` by CRT and the generator's order pins
`2n`; for `d = 2` and `n` even the element `(0, 1)` has order `n`, so
`n ∈ {2, 4, 6, 8, 10, 12}`, and the two exclusions remove `10` and
`12`. -/
theorem mazur_group_casework (T : Type*) [AddCommGroup T]
    (horder : ∀ x : T, addOrderOf x ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ))
    (h210 : ∀ φ : (ZMod 2 × ZMod 10) →+ T, ¬ Function.Injective φ)
    (h212 : ∀ φ : (ZMod 2 × ZMod 12) →+ T, ¬ Function.Injective φ)
    (hdec : ∃ (d n : ℕ), (d = 1 ∨ d = 2) ∧ Nonempty (T ≃+ (ZMod d × ZMod n))) :
    (∃ n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ),
      Nonempty (T ≃+ ZMod n)) ∨
    (∃ m ∈ ({1, 2, 3, 4} : Finset ℕ),
      Nonempty (T ≃+ (ZMod 2 × ZMod (2 * m)))) := by
  classical
  obtain ⟨d, n, hd, ⟨e⟩⟩ := hdec
  rcases hd with rfl | rfl
  · -- `d = 1`: the group is cyclic of order `n`
    left
    have e' : T ≃+ ZMod n := e.trans AddEquiv.uniqueProd
    have hordx : addOrderOf (e'.symm 1) = n := by
      have h1 := addOrderOf_injective e'.toAddMonoidHom e'.injective (e'.symm 1)
      rw [show e'.toAddMonoidHom (e'.symm 1) = 1 from e'.apply_symm_apply 1,
        ZMod.addOrderOf_one] at h1
      exact h1.symm
    have hmem := horder (e'.symm 1)
    rw [hordx] at hmem
    exact ⟨n, hmem, ⟨e'⟩⟩
  · by_cases hpar : 2 ∣ n
    · -- `d = 2`, `n` even: `(0, 1)` has order `n`, and the exclusions apply
      -- the order of `(0, 1)` is `n`
      have hord01 : addOrderOf ((0, 1) : ZMod 2 × ZMod n) = n := by
        have h1 : n • ((0, 1) : ZMod 2 × ZMod n) = 0 := by
          have hz : n • (0 : ZMod 2) = 0 := smul_zero n
          have ho : n • (1 : ZMod n) = 0 := by
            rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
          rw [Prod.smul_mk, hz, ho]
          rfl
        have hdvd : addOrderOf ((0, 1) : ZMod 2 × ZMod n) ∣ n :=
          addOrderOf_dvd_of_nsmul_eq_zero h1
        have hdvd2 : n ∣ addOrderOf ((0, 1) : ZMod 2 × ZMod n) := by
          have h2 : (addOrderOf ((0, 1) : ZMod 2 × ZMod n)) •
              ((0, 1) : ZMod 2 × ZMod n) = 0 := addOrderOf_nsmul_eq_zero _
          have h3 : (addOrderOf ((0, 1) : ZMod 2 × ZMod n)) • (1 : ZMod n) = 0 :=
            congrArg Prod.snd h2
          have h4 := addOrderOf_dvd_of_nsmul_eq_zero h3
          rwa [ZMod.addOrderOf_one] at h4
        exact Nat.dvd_antisymm hdvd hdvd2
      have hordx : addOrderOf (e.symm ((0, 1) : ZMod 2 × ZMod n)) = n := by
        have h1 := addOrderOf_injective e.toAddMonoidHom e.injective (e.symm (0, 1))
        rw [show e.toAddMonoidHom (e.symm (0, 1)) = (0, 1) from e.apply_symm_apply _,
          hord01] at h1
        exact h1.symm
      have hmem := horder (e.symm ((0, 1) : ZMod 2 × ZMod n))
      rw [hordx] at hmem
      fin_cases hmem
      · exact absurd hpar (by norm_num)
      · exact Or.inr ⟨1, by decide, ⟨e⟩⟩
      · exact absurd hpar (by norm_num)
      · exact Or.inr ⟨2, by decide, ⟨e⟩⟩
      · exact absurd hpar (by norm_num)
      · exact Or.inr ⟨3, by decide, ⟨e⟩⟩
      · exact absurd hpar (by norm_num)
      · exact Or.inr ⟨4, by decide, ⟨e⟩⟩
      · exact absurd hpar (by norm_num)
      · exact absurd e.symm.injective (h210 e.symm.toAddMonoidHom)
      · exact absurd e.symm.injective (h212 e.symm.toAddMonoidHom)
    · -- `d = 2`, `n` odd: the group is cyclic of order `2n` by CRT
      left
      have hcop : Nat.Coprime 2 n := (Nat.prime_two.coprime_iff_not_dvd).mpr hpar
      have e' : T ≃+ ZMod (2 * n) :=
        e.trans ((ZMod.chineseRemainder hcop).toAddEquiv).symm
      have hordx : addOrderOf (e'.symm 1) = 2 * n := by
        have h1 := addOrderOf_injective e'.toAddMonoidHom e'.injective (e'.symm 1)
        rw [show e'.toAddMonoidHom (e'.symm 1) = 1 from e'.apply_symm_apply 1,
          ZMod.addOrderOf_one] at h1
        exact h1.symm
      have hmem := horder (e'.symm 1)
      rw [hordx] at hmem
      exact ⟨2 * n, hmem, ⟨e'⟩⟩

/-- **Mazur's torsion theorem** (DERIVED 2026-07-22 from the five
arithmetic leaves, the PROVEN `(ℤ/2)³` bound, the group-theoretic
rank-`≤2` leaf, and the PROVEN casework): the torsion subgroup of the
rational points of an elliptic curve over `ℚ` is isomorphic to one of
the fifteen groups `ℤ/n` with `n ∈ {1, …, 10, 12}` or `ℤ/2 × ℤ/2m` with
`m ∈ {1, 2, 3, 4}`. Mazur, "Modular curves and the Eisenstein ideal"
(Publ. Math. IHÉS 47, 1977) and "Rational isogenies of prime degree"
(Invent. Math. 44, 1978). -/
theorem WeierstrassCurve.mazur_classification (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (∃ n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ),
      Nonempty ((Submodule.torsion ℤ (E⁄ℚ).Point) ≃+ ZMod n)) ∨
    (∃ m ∈ ({1, 2, 3, 4} : Finset ℕ),
      Nonempty ((Submodule.torsion ℤ (E⁄ℚ).Point) ≃+ (ZMod 2 × ZMod (2 * m)))) := by
  haveI : Finite (Submodule.torsion ℤ (E⁄ℚ).Point) := E.torsion_finite_rat
  have hιinj : Function.Injective
      ((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom) :=
    Submodule.injective_subtype _
  refine mazur_group_casework (Submodule.torsion ℤ (E⁄ℚ).Point) ?_ ?_ ?_ ?_
  · -- element orders through Mazur's uniform bound
    intro x
    have h1 := addOrderOf_injective
      ((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom) hιinj x
    rw [← h1]
    exact E.mazur_point_order _ x.2
  · -- no `ℤ/2 × ℤ/10`
    intro φ hφ
    exact E.not_two_ten_torsion
      (((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom).comp φ)
      (hιinj.comp hφ)
  · -- no `ℤ/2 × ℤ/12`
    intro φ hφ
    exact E.not_two_twelve_torsion
      (((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom).comp φ)
      (hιinj.comp hφ)
  · -- the rank-`≤2` shape, from the Weil-pairing leaf and the `2`-torsion bound
    refine AddCommGroup.exists_rank_le_two_decomposition _ ?_ ?_
    · intro n hn φ hφ
      exact E.not_full_torsion_rat hn
        (((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom).comp φ)
        (hιinj.comp hφ)
    · intro φ hφ
      exact E.not_two_cube_torsion
        (((Submodule.torsion ℤ (E⁄ℚ).Point).subtype.toAddMonoidHom).comp φ)
        (hιinj.comp hφ)

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
theorem minkowski_character_trivial {T : Type*} [Group T]
    (χ : Field.absoluteGaloisGroup ℚ →* T)
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

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Unipotence of inertia at `2`** (DERIVED 2026-07-17 from the
pointwise Tate unipotence leaf and the PROVEN transport machinery): the
Frey curve has multiplicative reduction at `2`
(`freyCurve_hasMultiplicativeReduction_at_two`, PROVEN), so every
element of the local inertia group at `2` acts on the `p`-torsion with
`(ρ(σ) − 1)² = 0` — the pointwise statement
`torsion_unipotent_of_multiplicative_reduction` at the embedded
valuation subring, carried over by
`map_mem_inertiaSubgroup_of_mem_localInertiaGroup` and expanded
`(A − 1)² = A·A − A − A + 1` pointwise on the torsion. -/
theorem FreyPackage.inertia_two_unipotent (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ σ ∈ localInertiaGroup
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
      (P.freyCurve.galoisRep P.p P.hppos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) σ) -
        1) ^ 2 = 0 := by
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  intro σ hσ
  haveI := P.freyCurve_hasMultiplicativeReduction_at_two
  have hp2 : (2 : ℕ) ≠ P.p := by
    have := P.hp5
    omega
  have hpt := WeierstrassCurve.torsion_unipotent_of_multiplicative_reduction
    P.freyCurve Nat.prime_two hp2 σ hσ
  set A := P.freyCurve.galoisRep P.p P.hppos
    ((Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) σ) with hA
  apply LinearMap.ext
  intro v
  have hexp : ((A - 1) ^ 2 : Module.End (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p)) v =
      A (A v) - A v - A v + v := by
    rw [pow_two, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, LinearMap.sub_apply, Module.End.one_apply,
      map_sub]
    abel
  rw [hexp]
  have hv : ((v : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion P.p)) :
      ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point) ∈
      AddSubgroup.torsionBy
        ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point
        ((P.p : ℕ) : ℤ) := by
    have h1 := v.2
    rw [Submodule.mem_torsionBy_iff] at h1
    show ((P.p : ℕ) : ℤ) • (v : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point) = 0
    exact_mod_cast h1
  have hp := hpt v.1 hv
  apply Subtype.ext
  have hb : ∀ w : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion P.p),
      (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from (A w).1) =
      WeierstrassCurve.Affine.Point.map
        (((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) σ :
          AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
        (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from w.1) :=
    fun w => rfl
  have hgoal : (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from
      (A (A v) - A v - A v + v : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)).1) =
      (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from (A (A v)).1) -
      (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from (A v).1) -
      (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from (A v).1) +
      (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from v.1) := rfl
  show (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from
    (A (A v) - A v - A v + v : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion P.p)).1) =
    (show ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point from
      ((0 : Module.End (ZMod P.p) ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) v).1)
  rw [hgoal, hb (A v), hb v]
  exact hp

/-!
### Decomposition of the flat/ordinary analysis at `p` (2026-07-22)

`subquotient_character_unramified_at_p` is decomposed into two
reduction-type leaves producing an *étale line* `L` — a line in the
`p`-torsion on whose QUOTIENT the inertia at `p` acts trivially — and a
PROVEN linear-algebra assembly. After the third pass (2026-07-22,
night) the two reduction-type nodes are themselves DERIVED from three
sharper leaves cut along the same seams as the `Semistable.lean`
development:

* `exists_etale_line_of_split_multiplicative_self` (sorry node — the
  Tate/Kummer content proper): at a prime `p` where the COMPLETED
  curve has SPLIT multiplicative reduction, the Tate parametrization
  (`exists_tateEquivSepClosure`, stated at exactly this interface in
  `TateSepClosure.lean`) presents `E[p] ⊂ ℚ̂̄_pˣ/q_Eᶻ` as generated by
  `μ_p` and a `p`-th root `u` of `q_E`; for ANY `σ` in the local
  Galois group, `σ(u)/u` is a `p`-th root of unity (Kummer — no
  valuation estimate needed), so `(σ − 1)E[p]` lands in the `μ_p`
  line, which is the étale-quotient line. Silverman ATAEC V.3, V.5.
* `exists_etale_line_of_nonsplit_multiplicative_self` (sorry node —
  the quadratic-twist descent): if the completed curve is
  multiplicative but NOT split, the unramified quadratic twist to
  split reduction
  (`exists_quadraticTwist_hasSplitMultiplicativeReduction`)
  identifies the two `p`-torsion inertia modules (the twist character
  is unramified at `p`), transferring the split-case line.
* `exists_etale_line_of_multiplicative_self` (DERIVED 2026-07-22 from
  the two preceding leaves by the split/nonsplit case split, via
  `hasMultiplicativeReduction_adicCompletion`).
* `exists_etale_line_or_no_stable_line_of_good` (sorry node — the
  ordinary/supersingular dichotomy, with the stable-line hypothesis
  factored out): at a prime `p ≠ 2` of good reduction, EITHER the
  connected-étale sequence of `E[p]/ℤ_p` provides an étale-quotient
  line (the ordinary case), OR no line of `E[p]` is Galois-stable at
  all (the supersingular case: inertia acts through the level-2
  fundamental character, whose eigenvalues are `𝔽_{p²}`-conjugate and
  not `𝔽_p`-rational — Serre, Propriétés galoisiennes…, Invent. Math.
  15 (1972), §1.11–1.12, Prop. 12). Serre Duke 1987, §4.1.
* `exists_etale_line_of_good_of_stable_line` (DERIVED 2026-07-22 from
  the dichotomy leaf: the given stable line refutes the second
  disjunct).
* `character_unramified_at_p_of_etale_line` (PROVEN): given ANY such
  line `L`, either the stable line `W` equals `L` — then `χ₂` is the
  quotient character of `L` and is unramified at `p` — or `W ∩ L = 0` —
  then `W` maps isomorphically onto the quotient by `L`, forcing
  `χ₁` to be trivial on inertia at `p`.
-/

open ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **The Tate étale line at `p`, split multiplicative case** (sorry
node — the Tate/Kummer content proper): for an elliptic curve over `ℚ`
whose base change to `ℚ̂_p` has SPLIT multiplicative reduction, there is
a line `L ⊆ E[p]` such that the local inertia at `p` acts trivially on
`E[p]/L`. Content (Silverman ATAEC V.3, V.5): the Tate uniformization
`exists_tateEquivSepClosure` gives a Galois-equivariant
`ℚ̂̄_pˣ/q_Eᶻ ≅ E(ℚ̂̄_p)`; a `p`-torsion class is represented by `u` with
`u^p = q_E^a` (`exists_rep_pow_eq_zpow_of_torsion`), and for `σ` in the
local Galois group `σ(u)/u ∈ μ_p` since `σ` fixes `q_E` — so with `L`
the image of the `μ_p` classes (a line: `μ_p ∩ q_Eᶻ = 1` by valuations)
the quotient action of the WHOLE local Galois group, in particular of
inertia, is trivial; transport to the global torsion rides the chosen
embedding `ℚ̄ ↪ ℚ̂̄_p` as in the unramifiedness glue of
`Semistable.lean`. -/
theorem WeierstrassCurve.exists_etale_line_of_split_multiplicative_self
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [(E.map (algebraMap ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat]] :
    ∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v :=
  sorry

open ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **The Tate étale line at `p`, nonsplit multiplicative case** (sorry
node — the quadratic-twist descent): for an elliptic curve over `ℚ`
with multiplicative reduction at `p` whose completed base change is NOT
split, the étale-quotient line still exists. Content: the quadratic
twist by the unramified quadratic extension of `ℚ̂_p`
(`exists_quadraticTwist_hasSplitMultiplicativeReduction`) has split
multiplicative reduction and the same `j`-invariant; the twist
character is unramified at `p`, so the two mod-`p` INERTIA modules are
isomorphic, and the line of the split case transfers. Silverman ATAEC
V.5.4; Serre Duke 1987, §4.1. -/
theorem WeierstrassCurve.exists_etale_line_of_nonsplit_multiplicative_self
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hns : ¬ (E.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat]) :
    ∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v :=
  sorry

open ValuativeRel IsDedekindDomain in
set_option backward.isDefEq.respectTransparency false in
/-- **The Tate étale line at `p`, multiplicative case** (DERIVED
2026-07-22 from the split leaf
`exists_etale_line_of_split_multiplicative_self` and the nonsplit
twist leaf `exists_etale_line_of_nonsplit_multiplicative_self`, by the
split/nonsplit case split on the completed base change): for an
elliptic curve over `ℚ` with multiplicative reduction at `p`, there is
a line `L ⊆ E[p]` such that the local inertia at `p` acts trivially on
`E[p]/L`. Silverman ATAEC V.3, V.5. -/
theorem WeierstrassCurve.exists_etale_line_of_multiplicative_self
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    ∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v := by
  classical
  haveI := hasMultiplicativeReduction_adicCompletion hp E
  by_cases hsp : (E.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).HasSplitMultiplicativeReduction
      𝒪[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat]
  · haveI := hsp
    exact E.exists_etale_line_of_split_multiplicative_self hp
  · exact E.exists_etale_line_of_nonsplit_multiplicative_self hp hsp

set_option backward.isDefEq.respectTransparency false in
/-- **The connected-étale dichotomy at a good prime** (sorry node — the
ordinary/supersingular dichotomy, with the stable-line hypothesis
factored out): for an elliptic curve over `ℚ` with good reduction at an
odd prime `p`, EITHER there is a line `L ⊆ E[p]` such that the local
inertia at `p` acts trivially on `E[p]/L`, OR no line of `E[p]` is
stable under the full mod-`p` representation. Content: if the reduction
is ORDINARY, the connected-étale sequence of the finite flat group
scheme `E[p]/ℤ_p` has étale quotient of order `p`, on whose geometric
points inertia acts trivially — the first disjunct with `L` the
connected (multiplicative-type) line; if the reduction is
SUPERSINGULAR, inertia at `p` acts on `E[p]` through the fundamental
character of level 2, whose eigenvalues are conjugate over `𝔽_{p²}`
but not `𝔽_p`-rational, so not even a line stable under all of `Γℚ`
exists — the second disjunct (Serre, Propriétés galoisiennes…, Invent.
Math. 15 (1972), §1.11–1.12, Prop. 12). Serre Duke 1987, §4.1. -/
theorem WeierstrassCurve.exists_etale_line_or_no_stable_line_of_good
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    (∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v) ∨
    (∀ W : Submodule (ZMod p)
        ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) W = 1 →
      ¬ ∀ g v, v ∈ W → E.galoisRep p hp.pos g v ∈ W) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **The connected-étale line at `p`, good case** (DERIVED 2026-07-22
from the dichotomy leaf `exists_etale_line_or_no_stable_line_of_good`:
the given stable line refutes the second disjunct): for an elliptic
curve over `ℚ` with good reduction at an odd prime `p` whose mod-`p`
representation admits a stable line, there is a line `L ⊆ E[p]` such
that the local inertia at `p` acts trivially on `E[p]/L`. Serre Duke
1987, §4.1. -/
theorem WeierstrassCurve.exists_etale_line_of_good_of_stable_line
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    [E.HasGoodReduction
      (Localization.AtPrime hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (W : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p))
    (hW1 : Module.finrank (ZMod p) W = 1)
    (hstable : ∀ g v, v ∈ W → E.galoisRep p hp.pos g v ∈ W) :
    ∃ L : Submodule (ZMod p) ((E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p),
      Module.finrank (ZMod p) L = 1 ∧
      ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
        ∀ v, L.mkQ (E.galoisRep p hp.pos
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                hp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v := by
  rcases E.exists_etale_line_or_no_stable_line_of_good hp hodd with h | h
  · exact h
  · exact absurd hstable (h W hW1)

set_option backward.isDefEq.respectTransparency false in
/-- **Linear algebra of the étale line** (PROVEN 2026-07-22): given the
stable line `W` with its characters and ANY line `L` on whose quotient
the inertia at `p` acts trivially, one of `χ₁`, `χ₂` is unramified at
`p`. If `W = L`, the quotient character `χ₂` is trivial on inertia
directly; if `W ≠ L`, the two lines of the 2-dimensional space meet
trivially, so a nonzero vector of `W` has nonzero image in the quotient
by `L`, and comparing the scalar action `χ₁` with the trivial quotient
action kills `χ₁` on inertia. -/
lemma FreyPackage.character_unramified_at_p_of_etale_line
    (P : FreyPackage)
    (W L : Submodule (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p))
    (hW1 : Module.finrank (ZMod P.p) W = 1)
    (hL1 : Module.finrank (ZMod P.p) L = 1)
    (χ₁ χ₂ : Field.absoluteGaloisGroup ℚ →* (ZMod P.p)ˣ)
    (hχ₁ : ∀ g, ∀ v ∈ W,
      P.freyCurve.galoisRep P.p P.hppos g v = (χ₁ g : ZMod P.p) • v)
    (hχ₂ : ∀ g v, W.mkQ (P.freyCurve.galoisRep P.p P.hppos g v) =
      (χ₂ g : ZMod P.p) • W.mkQ v)
    (hL : ∀ σ ∈ localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat,
      ∀ v, L.mkQ (P.freyCurve.galoisRep P.p P.hppos
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              P.pp.toHeightOneSpectrumRingOfIntegersRat))) σ) v) = L.mkQ v) :
    (localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ₁.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          P.pp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) ∨
    (localInertiaGroup P.pp.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          P.pp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) := by
  classical
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  -- finiteness bookkeeping: the torsion space has rank `2`
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
  by_cases hWL : W = L
  · -- the stable line IS the étale line: `χ₂` is unramified at `p`
    right
    intro σ hσ
    rw [MonoidHom.mem_ker]
    have hWtop : W ≠ ⊤ := by
      intro htop
      rw [htop, finrank_top, hfr] at hW1
      omega
    haveI : Nontrivial
        (((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) ⧸ W) :=
      Submodule.Quotient.nontrivial_iff.mpr hWtop
    obtain ⟨z, hz⟩ := exists_ne (0 :
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) ⧸ W)
    obtain ⟨v, rfl⟩ := W.mkQ_surjective z
    have h1 := hχ₂ ((Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        P.pp.toHeightOneSpectrumRingOfIntegersRat))) σ) v
    have h2 := hL σ hσ v
    rw [← hWL] at h2
    rw [h2] at h1
    have h3 : ((1 : ZMod P.p) -
        (χ₂ ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            P.pp.toHeightOneSpectrumRingOfIntegersRat))) σ) : ZMod P.p)) •
        W.mkQ v = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero_of_eq h1
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact Units.ext (by
        rw [Units.val_one]
        exact (sub_eq_zero.mp h4).symm)
    · exact absurd h4 hz
  · -- the lines differ: `χ₁` is unramified at `p`
    left
    intro σ hσ
    rw [MonoidHom.mem_ker]
    have hW0 : W ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hW1
      omega
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
    obtain ⟨w₀, hw₀ne⟩ := exists_ne (0 : W)
    have hw₀V : (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) ≠ 0 :=
      fun hc => hw₀ne (Subtype.ext hc)
    -- `w₀ ∉ L`, else both lines are the span of `w₀`
    have hw₀L : (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) ∉ L := by
      intro hmem
      have hsp1 : Submodule.span (ZMod P.p) {(w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p))} ≤ W := by
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact w₀.2
      have hsp2 : Submodule.span (ZMod P.p) {(w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p))} ≤ L := by
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hmem
      have hrk : Module.finrank (ZMod P.p)
          (Submodule.span (ZMod P.p) {(w₀ : ((P.freyCurve.map (algebraMap ℚ
            (AlgebraicClosure ℚ))).nTorsion P.p))}) = 1 :=
        finrank_span_singleton hw₀V
      have hWeq : Submodule.span (ZMod P.p) {(w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p))} = W :=
        Submodule.eq_of_le_of_finrank_le hsp1 (le_of_eq (by rw [hW1, hrk]))
      have hLeq : Submodule.span (ZMod P.p) {(w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p))} = L :=
        Submodule.eq_of_le_of_finrank_le hsp2 (le_of_eq (by rw [hL1, hrk]))
      exact hWL (hWeq.symm.trans hLeq)
    have hquotne : L.mkQ (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) ≠ 0 := by
      rw [Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]
      exact hw₀L
    have h1 := hχ₁ ((Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        P.pp.toHeightOneSpectrumRingOfIntegersRat))) σ)
      (w₀ : ((P.freyCurve.map (algebraMap ℚ
        (AlgebraicClosure ℚ))).nTorsion P.p)) w₀.2
    have h2 := hL σ hσ (w₀ : ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion P.p))
    rw [h1, map_smul] at h2
    have h3 : ((1 : ZMod P.p) -
        (χ₁ ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            P.pp.toHeightOneSpectrumRingOfIntegersRat))) σ) : ZMod P.p)) •
        L.mkQ (w₀ : ((P.freyCurve.map (algebraMap ℚ
          (AlgebraicClosure ℚ))).nTorsion P.p)) = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero_of_eq h2.symm
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact Units.ext (by
        rw [Units.val_one]
        exact (sub_eq_zero.mp h4).symm)
    · exact absurd h4 hquotne

/-- **The flat/ordinary analysis at `p`** (DERIVED 2026-07-22 from the
two étale-line leaves and the PROVEN linear-algebra assembly): given
the stable line of the reducible mod-`p` Frey representation with its
characters `χ₁`, `χ₂` (multiplying to `ω̄`), one of the two is
unramified at `p` itself. The Frey curve is semistable at `p`
(`freyCurve_hasGoodReduction_of_not_dvd` /
`freyCurve_hasMultiplicativeReduction_of_dvd`, PROVEN, by `p ∣ abc` or
not); each reduction type yields an étale line via its leaf, and the
linear algebra compares it with the stable line. -/
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
    (_hcyclo : ∀ g : Field.absoluteGaloisGroup ℚ,
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
          P.pp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) := by
  classical
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  have hp2 : P.p ≠ 2 := by
    have := P.hp5
    omega
  by_cases hdvd : ((P.p : ℤ)) ∣ P.a * P.b * P.c
  · -- multiplicative reduction at `p`: the Tate étale line
    haveI := P.freyCurve_hasMultiplicativeReduction_of_dvd P.pp hp2 hdvd
    obtain ⟨L, hL1, hL⟩ :=
      WeierstrassCurve.exists_etale_line_of_multiplicative_self P.freyCurve P.pp
    exact P.character_unramified_at_p_of_etale_line W L hW1 hL1 χ₁ χ₂ hχ₁ hχ₂ hL
  · -- good reduction at `p`: the connected-étale line
    haveI := P.freyCurve_hasGoodReduction_of_not_dvd P.pp hp2 hdvd
    obtain ⟨L, hL1, hL⟩ :=
      WeierstrassCurve.exists_etale_line_of_good_of_stable_line P.freyCurve P.pp hp2
        W hW1 hstable
    exact P.character_unramified_at_p_of_etale_line W L hW1 hL1 χ₁ χ₂ hχ₁ hχ₂ hL

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
    exact WeilPairing.det_galoisRep_eq_cyclotomic P.freyCurve P.p P.hppos
      (P.pp.odd_of_ne_two (by have := P.hp5; omega)) g
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

/-!
### The Vélu quotient (decomposed 2026-07-22)

`exists_quotient_curve_point` is DERIVED below from two new leaves:

* `WeierstrassCurve.exists_quotient_isogeny` (sorry node) — the true
  Vélu core, stated curve-independently: the quotient of an elliptic
  curve over `ℚ` by a finite Galois-stable subgroup of geometric
  points exists as an elliptic curve over `ℚ`, together with the
  Galois-equivariant quotient homomorphism on `ℚ̄`-points whose kernel
  is exactly the subgroup.
* `FreyPackage.exists_two_torsion_embedding` (PROVEN) — the Frey
  curve's full rational `2`-torsion.

The assembly takes `C` to be the image of the line `W` (a cyclic
subgroup of order `p`, Galois-stable by `hstable`), pushes a vector
`v ∉ W` through the quotient map to get a Galois-fixed point of exact
order `p` (fixed because the quotient action is trivial, `hquot`),
pushes the rational `2`-torsion through (injectively, because the
kernel has odd exponent `p`), and descends both to `ℚ`-points by
`exists_point_eq_baseChange_of_fixed`.
-/

/-- **The quotient-isogeny leaf — Vélu's construction** (sorry node,
carved out of `exists_quotient_curve_point` 2026-07-22): for every
finite Galois-stable subgroup `C` of the geometric points of an
elliptic curve `E/ℚ` there are an elliptic curve `E'/ℚ` (the quotient
`E/C`) and a Galois-equivariant group homomorphism `E(ℚ̄) →+ E'(ℚ̄)`
(the quotient isogeny on points) with kernel exactly `C`. Vélu's
explicit formulas (Vélu 1971; Silverman AEC III.4.12 and Exercise
3.13) give the quotient curve's Weierstrass coefficients as symmetric
functions of the coordinates of the nonzero points of `C` — rational
because `C` is Galois-stable — and the isogeny's coordinate functions
as explicit rational functions; none of this is in mathlib yet. -/
theorem WeierstrassCurve.exists_quotient_isogeny
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (C : AddSubgroup ((E⁄(AlgebraicClosure ℚ)).Point))
    (hCfin : (C : Set ((E⁄(AlgebraicClosure ℚ)).Point)).Finite)
    (hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point),
      (∀ (σ : Field.absoluteGaloisGroup ℚ)
        (Pt : (E⁄(AlgebraicClosure ℚ)).Point),
        φ (Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom Pt) =
        Affine.Point.map
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ Pt)) ∧
      (∀ Pt : (E⁄(AlgebraicClosure ℚ)).Point, φ Pt = 0 ↔ Pt ∈ C) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Full rational `2`-torsion of the Frey curve** (PROVEN
2026-07-22): in the semistable model `y² + xy = x³ + a₂x² + a₄x` of
the Frey curve (`a₂ = (bᵖ − 1 − aᵖ)/4`, `a₄ = −aᵖbᵖ/16`) the
`2`-division polynomial `4x³ + b₂x² + 2b₄x + b₆` factors as
`4x(x − aᵖ/4)(x + bᵖ/4)` over `ℚ`: the points `(0, 0)` and
`(aᵖ/4, −aᵖ/8)` are rational of exact order `2` with distinct
`x`-coordinates, so they generate an injective `(ℤ/2)² →+ E(ℚ)`. -/
theorem FreyPackage.exists_two_torsion_embedding (P : FreyPackage) :
    ∃ φ₂ : (ZMod 2 × ZMod 2) →+ ((P.freyCurve)⁄ℚ).Point,
      Function.Injective φ₂ := by
  classical
  have ha0 : ((P.a : ℚ)) ^ P.p ≠ 0 :=
    pow_ne_zero _ (Int.cast_ne_zero.mpr P.ha0)
  -- the two affine points of order `2`
  have hE₁ : ((P.freyCurve)⁄ℚ).Equation 0 0 := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [FreyPackage.freyCurve]
  have hE₂ : ((P.freyCurve)⁄ℚ).Equation
      ((P.a : ℚ) ^ P.p / 4) (-((P.a : ℚ) ^ P.p) / 8) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
      FreyPackage.freyCurve, Algebra.algebraMap_self, RingHom.id_apply]
    push_cast
    ring
  have h₁ : ((P.freyCurve)⁄ℚ).Nonsingular 0 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hE₁
  have h₂ : ((P.freyCurve)⁄ℚ).Nonsingular
      ((P.a : ℚ) ^ P.p / 4) (-((P.a : ℚ) ^ P.p) / 8) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hE₂
  set Pt₁ : ((P.freyCurve)⁄ℚ).Point :=
    WeierstrassCurve.Affine.Point.some _ _ h₁
  set Pt₂ : ((P.freyCurve)⁄ℚ).Point :=
    WeierstrassCurve.Affine.Point.some _ _ h₂
  -- both points have order `2`
  have hneg₁ : (0 : ℚ) = ((P.freyCurve)⁄ℚ).negY 0 0 := by
    simp [WeierstrassCurve.Affine.negY, FreyPackage.freyCurve]
  have hneg₂ : -((P.a : ℚ) ^ P.p) / 8 =
      ((P.freyCurve)⁄ℚ).negY ((P.a : ℚ) ^ P.p / 4) (-((P.a : ℚ) ^ P.p) / 8) := by
    simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
      FreyPackage.freyCurve, Algebra.algebraMap_self, RingHom.id_apply]
    push_cast
    ring
  have h2Pt₁ : Pt₁ + Pt₁ = 0 :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_eq hneg₁
  have h2Pt₂ : Pt₂ + Pt₂ = 0 :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_eq hneg₂
  -- assemble the homomorphism `(ℤ/2)² →+ E(ℚ)` on the two generators
  have hz₁ : zmultiplesHom _ Pt₁ (2 : ℤ) = 0 := by
    show (2 : ℤ) • Pt₁ = 0
    rw [two_zsmul]
    exact h2Pt₁
  have hz₂ : zmultiplesHom _ Pt₂ (2 : ℤ) = 0 := by
    show (2 : ℤ) • Pt₂ = 0
    rw [two_zsmul]
    exact h2Pt₂
  let f₁ : ZMod 2 →+ ((P.freyCurve)⁄ℚ).Point :=
    ZMod.lift 2 ⟨zmultiplesHom _ Pt₁, hz₁⟩
  let f₂ : ZMod 2 →+ ((P.freyCurve)⁄ℚ).Point :=
    ZMod.lift 2 ⟨zmultiplesHom _ Pt₂, hz₂⟩
  have hf₁ : f₁ 1 = Pt₁ := by
    have h := ZMod.lift_coe 2 ⟨zmultiplesHom _ Pt₁, hz₁⟩ (1 : ℤ)
    rw [show (((1 : ℤ)) : ZMod 2) = 1 by norm_num] at h
    rw [h]
    exact one_zsmul Pt₁
  have hf₂ : f₂ 1 = Pt₂ := by
    have h := ZMod.lift_coe 2 ⟨zmultiplesHom _ Pt₂, hz₂⟩ (1 : ℤ)
    rw [show (((1 : ℤ)) : ZMod 2) = 1 by norm_num] at h
    rw [h]
    exact one_zsmul Pt₂
  refine ⟨f₁.coprod f₂, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  have h01 : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  obtain ⟨z₁, z₂⟩ := z
  rw [AddMonoidHom.coprod_apply] at hz
  -- the four cases: images `0`, `Pt₁`, `Pt₂`, `Pt₁ + Pt₂`
  rcases h01 z₁ with rfl | rfl <;> rcases h01 z₂ with rfl | rfl
  · rfl
  · rw [map_zero, zero_add, hf₂] at hz
    exact absurd hz (WeierstrassCurve.Affine.Point.some_ne_zero h₂)
  · rw [map_zero, add_zero, hf₁] at hz
    exact absurd hz (WeierstrassCurve.Affine.Point.some_ne_zero h₁)
  · rw [hf₁, hf₂] at hz
    have hxne : ¬((0 : ℚ) = (P.a : ℚ) ^ P.p / 4 ∧
        (0 : ℚ) = ((P.freyCurve)⁄ℚ).negY ((P.a : ℚ) ^ P.p / 4)
          (-((P.a : ℚ) ^ P.p) / 8)) := by
      rintro ⟨hx, -⟩
      exact ha0 (by linarith [hx.symm] : ((P.a : ℚ)) ^ P.p = 0)
    rw [WeierstrassCurve.Affine.Point.add_some hxne] at hz
    exact absurd hz (WeierstrassCurve.Affine.Point.some_ne_zero _)

set_option backward.isDefEq.respectTransparency false in
/-- **The Vélu quotient node** (DERIVED 2026-07-22 from the
quotient-isogeny leaf `exists_quotient_isogeny` and the PROVEN
`2`-torsion embedding `exists_two_torsion_embedding`): given a
Galois-stable line `W` in the `p`-torsion of the Frey curve on whose
quotient the Galois action is trivial, the quotient curve `E/C` by the
rational subgroup `C` corresponding to `W` (a `ℚ`-rational cyclic
subgroup of order `p`) is an elliptic curve over `ℚ` carrying a
rational point of order `p` (the image of any torsion point outside
`W`, Galois-fixed because the quotient action is trivial) and full
rational `2`-torsion (the image of the Frey curve's full `2`-torsion
through the odd-degree rational isogeny, injective on `2`-torsion). -/
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
      (Q : (E'⁄ℚ).Point), addOrderOf Q = P.p := by
  classical
  -- the inclusion of the `p`-torsion in the geometric point group
  let ι : ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) →+
      ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point :=
    { toFun := fun v => v.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun v w h => Subtype.ext h
  -- the kernel subgroup `C ⊆ E(ℚ̄)`: the image of the line `W`
  let C : AddSubgroup (((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point) :=
    AddSubgroup.map ι W.toAddSubgroup
  have hmemC : ∀ Pt : ((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point,
      Pt ∈ C ↔ ∃ v ∈ W, ι v = Pt := by
    intro Pt
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, Submodule.mem_toAddSubgroup.mp hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, Submodule.mem_toAddSubgroup.mpr hv, rfl⟩
  have hcard : Nat.card
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) =
      P.p ^ 2 :=
    TorsionCard.card_torsionBy (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ)))
      P.p (Nat.cast_ne_zero.mpr P.pp.ne_zero)
  haveI hNfin : Finite
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 P.pp.ne_zero)
  have hCfin : (↑C : Set (((P.freyCurve)⁄(AlgebraicClosure ℚ)).Point)).Finite := by
    rw [AddSubgroup.coe_map]
    exact (Set.toFinite _).image _
  have hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ C,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom x ∈ C := by
    intro σ x hx
    obtain ⟨v, hv, rfl⟩ := (hmemC x).mp hx
    have hcompat : Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (ι v) =
        ι (P.freyCurve.galoisRep P.p P.hppos σ v) := rfl
    rw [hcompat]
    exact (hmemC _).mpr ⟨_, hstable σ v hv, rfl⟩
  obtain ⟨E', hE', φ, hφeq, hφker⟩ :=
    WeierstrassCurve.exists_quotient_isogeny P.freyCurve C hCfin hCstable
  haveI := hE'
  -- Part 1: a Galois-fixed point of exact order `p` on the quotient
  obtain ⟨v, hvW⟩ : ∃ v, v ∉ W := by
    by_contra h
    push_neg at h
    exact hWtop (Submodule.eq_top_iff'.mpr h)
  have hQbar0 : φ (ι v) ≠ 0 := by
    intro h0
    obtain ⟨w, hw, hwv⟩ := (hmemC _).mp ((hφker _).mp h0)
    exact hvW (hι hwv ▸ hw)
  have hp_smul : P.p • φ (ι v) = 0 := by
    have h1 : P.p • (ι v) = 0 := by
      have h2 : ((P.p : ℕ) : ℤ) • (ι v) = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp v.2
      exact_mod_cast h2
    rw [← map_nsmul, h1, map_zero]
  have hordQbar : addOrderOf (φ (ι v)) = P.p := by
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hp_smul
    rcases P.pp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hQbar0
    · exact h1
  have hfixQ : ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ (ι v)) =
      φ (ι v) := by
    intro σ
    have hcompat : Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (ι v) =
        ι (P.freyCurve.galoisRep P.p P.hppos σ v) := rfl
    have hsub : P.freyCurve.galoisRep P.p P.hppos σ v - v ∈ W := by
      have h := hquot σ v
      rwa [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
    have hker : φ (ι (P.freyCurve.galoisRep P.p P.hppos σ v)) = φ (ι v) := by
      have hzero : φ (ι (P.freyCurve.galoisRep P.p P.hppos σ v) - ι v) = 0 :=
        (hφker _).mpr ((hmemC _).mpr ⟨_, hsub, map_sub ι _ _⟩)
      rw [map_sub, sub_eq_zero] at hzero
      exact hzero
    calc Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ (ι v))
        = φ (Affine.Point.map
            (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (ι v)) :=
          (hφeq σ (ι v)).symm
      _ = φ (ι (P.freyCurve.galoisRep P.p P.hppos σ v)) := by rw [hcompat]
      _ = φ (ι v) := hker
  obtain ⟨Q, hQ⟩ :=
    WeierstrassCurve.exists_point_eq_baseChange_of_fixed E' (φ (ι v)) hfixQ
  have hordQ : addOrderOf Q = P.p := by
    rw [← hordQbar, ← hQ]
    exact (addOrderOf_injective _
      (Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))) Q).symm
  -- Part 2: the full rational `2`-torsion of the quotient
  obtain ⟨φ₂, hφ₂⟩ := P.exists_two_torsion_embedding
  let ψ : (ZMod 2 × ZMod 2) →+ (E'⁄(AlgebraicClosure ℚ)).Point :=
    φ.comp ((Affine.Point.baseChange (W' := P.freyCurve) ℚ
      (AlgebraicClosure ℚ)).comp φ₂)
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    -- the image lies in `C`, which has exponent `p`, but is `2`-torsion
    have hmem : Affine.Point.baseChange (W' := P.freyCurve) ℚ
        (AlgebraicClosure ℚ) (φ₂ z) ∈ C :=
      (hφker _).mp hz
    obtain ⟨w, -, hw⟩ := (hmemC _).mp hmem
    have h2ann : ∀ w : ZMod 2 × ZMod 2, (2 : ℕ) • w = 0 := by decide
    have h2x : (2 : ℕ) •
        Affine.Point.baseChange (W' := P.freyCurve) ℚ (AlgebraicClosure ℚ)
          (φ₂ z) = 0 := by
      rw [← map_nsmul, ← map_nsmul, h2ann, map_zero, map_zero]
    have hpx : P.p •
        Affine.Point.baseChange (W' := P.freyCurve) ℚ (AlgebraicClosure ℚ)
          (φ₂ z) = 0 := by
      rw [← hw]
      have h2 : ((P.p : ℕ) : ℤ) • (ι w) = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp w.2
      exact_mod_cast h2
    have hcop : Nat.Coprime 2 P.p :=
      (Nat.coprime_primes Nat.prime_two P.pp).mpr (by have := P.hp5; omega)
    have hone : addOrderOf (Affine.Point.baseChange (W' := P.freyCurve) ℚ
        (AlgebraicClosure ℚ) (φ₂ z)) = 1 :=
      Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd
        (addOrderOf_dvd_of_nsmul_eq_zero h2x)
        (addOrderOf_dvd_of_nsmul_eq_zero hpx))
    have hz0 : φ₂ z = 0 := by
      apply Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))
      rw [map_zero]
      exact AddMonoid.addOrderOf_eq_one_iff.mp hone
    exact (injective_iff_map_eq_zero φ₂).mp hφ₂ z hz0
  have hfixψ : ∀ z : ZMod 2 × ZMod 2, ∀ σ : Field.absoluteGaloisGroup ℚ,
      Affine.Point.map
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (ψ z) =
      ψ z := by
    intro z σ
    show Affine.Point.map _ (φ (Affine.Point.baseChange (W' := P.freyCurve) ℚ
      (AlgebraicClosure ℚ) (φ₂ z))) = _
    rw [← hφeq σ _]
    exact congrArg φ (Affine.Point.map_baseChange
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom (φ₂ z))
  have hdesc : ∀ z : ZMod 2 × ZMod 2, ∃ Q₀ : (E'⁄ℚ).Point,
      Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) Q₀ = ψ z := fun z =>
    WeierstrassCurve.exists_point_eq_baseChange_of_fixed E' (ψ z) (hfixψ z)
  choose g hg using hdesc
  have hgadd : ∀ z z' : ZMod 2 × ZMod 2, g (z + z') = g z + g z' := by
    intro z z'
    apply Affine.Point.map_injective (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))
    show Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (g (z + z')) =
      Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (g z + g z')
    rw [map_add, hg, hg, hg]
    exact map_add ψ z z'
  have hginj : Function.Injective (AddMonoidHom.mk' g hgadd) := by
    intro z z' hzz
    apply hψinj
    rw [← hg z, ← hg z']
    exact congrArg _ hzz
  exact ⟨E', hE', AddMonoidHom.mk' g hgadd, hginj, Q, hordQ⟩

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

