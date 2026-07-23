/-
FreyConditions.lean — own work for the Fermat project (not vendored from
the FLT project).

Decomposition of `FreyCurve.torsion_isHardlyRamified` (the mod-`p` Galois
representation on the `p`-torsion of the Frey curve is hardly ramified)
into the four defining conditions of `IsHardlyRamified`, each an explicit
sorry node with distinct mathematical content:

* `FreyCurve.torsion_det` (sorry node): the determinant of the mod-`p`
  representation is the mod-`p` cyclotomic character. This is the **Weil
  pairing** statement: `E[p] ∧ E[p] ≅ μ_p` equivariantly, so
  `det ρ̄ = ω̄`. Needs the Weil pairing, not yet in mathlib.

* `FreyCurve.torsion_isUnramified` (sorry node): the representation is
  unramified at every prime `q ∉ {2, p}`. At primes of good reduction this
  is the criterion of **Néron–Ogg–Shafarevich**; at the (multiplicative)
  bad primes of the semistable Frey curve it is the **Tate curve**
  argument: `q ∤ 2` bad means `v_q(j) = v_q(Δ) < 0` with
  `p ∣ v_q(j)` (proven in `FreyCurve.j_valuation_of_bad_prime`), so the
  Tate parameter is a `p`-th power up to units and the `p`-torsion of the
  Tate curve `ℚ_q^×/q_E^ℤ` is fixed by inertia.

* `FreyCurve.torsion_isFlat` (sorry node): the representation is flat at
  `p` — the `p`-torsion extends to a finite flat group scheme over `ℤ_p`.
  For the semistable Frey curve this comes from the Néron model (good
  ordinary/supersingular reduction) or the Tate curve at `p` together with
  `p ∣ v_p(j)` (multiplicative reduction).

* `FreyCurve.torsion_isTameAtTwo` (sorry node): at `2` the representation
  is upper-triangular with a free rank-1 quotient on which `G_{ℚ_2}` acts
  through an unramified character whose square is trivial. The Frey curve
  has multiplicative reduction at `2` (here `b` even and `a ≡ 3 mod 4` are
  used), so the Tate curve at `2` exhibits the quotient character as the
  unramified quadratic twist character.

Given the four nodes, `FreyCurve.torsion_isHardlyRamified` is the
structure constructor applied to them (`Frey.lean`).
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Fermat.FLT.FreyCurve.Basic
public import Fermat.FLT.EllipticCurve.Torsion
-- The Weil pairing node and the determinant-of-pairing linear algebra,
-- used to derive `torsion_det`.
import Fermat.FLT.EllipticCurve.WeilPairing
import Fermat.FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction
import Mathlib.RingTheory.Valuation.Integral
-- The Frey reduction-type nodes and the local-global glue nodes
-- (public: the tame-at-2 glue node stated in this file mentions
-- `HasMultiplicativeReduction` over the localization, whose instance
-- package lives in `Semistable`).
public import Fermat.FLT.FreyCurve.Semistable
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

@[expose] public section

open GaloisRepresentation

variable (P : FreyPackage)

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ` (mirrors the local
instance of `HardlyRamified/Frey.lean`; needed to state the determinant
condition). -/
noncomputable local instance instAlgebraPadicIntZModFreyConditions
    (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

set_option backward.isDefEq.respectTransparency false in
/-- **Determinant of the Frey torsion representation**: the determinant of
the mod-`p` Galois representation on the `p`-torsion of the Frey curve is
the mod-`p` cyclotomic character. DERIVED (2026-07-16) from the Weil
pairing node (`WeilPairing.exists_weilPairing`: a perfect alternating
Galois-equivariant pairing on `E[p]`, scaled by the cyclotomic character)
and the proven linear algebra (`WeilPairing.det_eq_of_conj`: on the rank-2
torsion, an endomorphism scaling a nonzero alternating pairing by `c` has
determinant `c`). -/
theorem FreyCurve.torsion_det :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ g, (P.freyCurve.galoisRep P.p P.hppos).det g =
      algebraMap ℤ_[P.p] (ZMod P.p)
        (cyclotomicCharacter (AlgebraicClosure ℚ) P.p g.toRingEquiv) := by
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  intro g
  obtain ⟨e, halt, hnd, hequiv⟩ :=
    WeilPairing.exists_weilPairing P.freyCurve P.p P.hppos
      (P.pp.odd_of_ne_two (by have := P.hp5; omega))
  have hrank : Module.rank (ZMod P.p)
      ((P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p) = 2 :=
    (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).p_torsion_rank
      (Nat.cast_ne_zero.mpr P.hp0)
  exact WeilPairing.det_eq_of_conj hrank e halt hnd (hequiv g)

/-- **Unramifiedness at good primes** (DERIVED 2026-07-16 from the two
nodes of `FreyCurve/Semistable.lean`): at a prime `q ∉ {2, p}` not
dividing `abc`, the Frey curve has good reduction over `ℤ_(q)`
(`FreyPackage.freyCurve_hasGoodReduction_of_not_dvd` — the discriminant
`(abc)^{2p}/2⁸` is a `q`-adic unit and the Frey equation is minimal at
`q`), and the Néron–Ogg–Shafarevich local-global glue
(`WeierstrassCurve.isUnramifiedAt_of_hasGoodReduction`) makes the
`p`-torsion unramified at `q`. -/
theorem FreyCurve.torsion_isUnramified_of_good :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ q (hq : q.Prime), q ≠ 2 ∧ q ≠ P.p → ¬((q : ℤ) ∣ P.a * P.b * P.c) →
      (P.freyCurve.galoisRep P.p P.hppos).IsUnramifiedAt
        hq.toHeightOneSpectrumRingOfIntegersRat := by
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  intro q hq hq2p hndvd
  haveI := P.freyCurve_hasGoodReduction_of_not_dvd hq hq2p.1 hndvd
  exact WeierstrassCurve.isUnramifiedAt_of_hasGoodReduction P.freyCurve P.hppos
    (P.pp.odd_of_ne_two (by have := P.hp5; omega)) hq hq2p.2

/-- **Unramifiedness at multiplicative primes** (DERIVED 2026-07-16): at
a prime `q ∉ {2, p}` dividing `abc`, the Frey curve has multiplicative
reduction (`FreyPackage.freyCurve_hasMultiplicativeReduction_of_dvd`,
PROVEN) and non-integral `j`-invariant with `p ∣ v_q(j)`
(`FreyCurve.j_valuation_of_bad_prime`, PROVEN), and the Tate-curve glue
(`WeierstrassCurve.isUnramifiedAt_of_hasMultiplicativeReduction`, to be
closed against the quadratic-twist and Tate-uniformization nodes) makes
the `p`-torsion unramified at `q`. -/
theorem FreyCurve.torsion_isUnramified_of_multiplicative :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ q (hq : q.Prime), q ≠ 2 ∧ q ≠ P.p → (q : ℤ) ∣ P.a * P.b * P.c →
      (P.freyCurve.galoisRep P.p P.hppos).IsUnramifiedAt
        hq.toHeightOneSpectrumRingOfIntegersRat := by
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  intro q hq hq2p hdvd
  haveI := P.freyCurve_hasMultiplicativeReduction_of_dvd hq hq2p.1 hdvd
  have hqodd : 2 < q := lt_of_le_of_ne hq.two_le (Ne.symm hq2p.1)
  exact WeierstrassCurve.isUnramifiedAt_of_hasMultiplicativeReduction P.freyCurve
    P.hppos hq hq2p.2 hq2p.1 (FreyCurve.j_valuation_of_bad_prime P hq hdvd hqodd)

/-- **Unramifiedness of the Frey torsion representation outside `2p`**
(DERIVED 2026-07-16 from the two preceding nodes by the case split on
`q ∣ abc`): the mod-`p` representation on the `p`-torsion of the Frey
curve is unramified at every prime `q` with `q ≠ 2` and `q ≠ p`.
Néron–Ogg–Shafarevich at primes of good reduction
(`torsion_isUnramified_of_good`); the Tate curve plus `p ∣ v_q(j)`
(`torsion_isUnramified_of_multiplicative`) at the multiplicative primes
of the semistable Frey curve. -/
theorem FreyCurve.torsion_isUnramified :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ q (hq : q.Prime), q ≠ 2 ∧ q ≠ P.p →
      (P.freyCurve.galoisRep P.p P.hppos).IsUnramifiedAt
        hq.toHeightOneSpectrumRingOfIntegersRat := by
  intro q hq hq2p
  by_cases hdvd : (q : ℤ) ∣ P.a * P.b * P.c
  · exact FreyCurve.torsion_isUnramified_of_multiplicative P q hq hq2p hdvd
  · exact FreyCurve.torsion_isUnramified_of_good P q hq hq2p hdvd

/-- **Flatness at `p`, good-reduction case** (DERIVED 2026-07-16): if
`p ∤ abc` then the Frey curve has good reduction at `p`
(`FreyPackage.freyCurve_hasGoodReduction_of_not_dvd`, PROVEN — the
discriminant `(abc)^{2p}/2⁸` is a `p`-adic unit and the Frey equation is
minimal at `p`), and the flatness glue
(`WeierstrassCurve.isFlatAt_of_hasGoodReduction`, to be closed against
the vendored `torsion_flat_of_good_reduction`) exhibits the `p`-torsion
as a finite flat group scheme over `ℤ_p`. -/
theorem FreyCurve.torsion_isFlat_of_good :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ¬((P.p : ℤ) ∣ P.a * P.b * P.c) →
      (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
        P.pp.toHeightOneSpectrumRingOfIntegersRat := by
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  intro hndvd
  have hp2 : P.p ≠ 2 := by
    have := P.hp5
    omega
  haveI := P.freyCurve_hasGoodReduction_of_not_dvd P.pp hp2 hndvd
  exact WeierstrassCurve.isFlatAt_of_hasGoodReduction P.freyCurve P.pp P.hppos

/-- **Flatness at `p`, multiplicative case** (DERIVED 2026-07-16): if
`p ∣ abc` then the Frey curve has multiplicative reduction at `p`
(`FreyPackage.freyCurve_hasMultiplicativeReduction_of_dvd`, PROVEN) with
`p ∣ v_p(j)` (`FreyCurve.j_valuation_of_bad_prime`, PROVEN), and the
peu-ramifiée glue
(`WeierstrassCurve.isFlatAt_of_hasMultiplicativeReduction`) exhibits the
`p`-torsion as prolonging to a finite flat group scheme over `ℤ_p`. -/
theorem FreyCurve.torsion_isFlat_of_multiplicative :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.p : ℤ) ∣ P.a * P.b * P.c →
      (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
        P.pp.toHeightOneSpectrumRingOfIntegersRat := by
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  intro hdvd
  have hp2 : P.p ≠ 2 := by
    have := P.hp5
    omega
  have hpodd : 2 < P.p := by
    have := P.hp5
    omega
  haveI := P.freyCurve_hasMultiplicativeReduction_of_dvd P.pp hp2 hdvd
  exact WeierstrassCurve.isFlatAt_of_hasMultiplicativeReduction P.freyCurve
    P.pp P.hppos hp2 (FreyCurve.j_valuation_of_bad_prime P P.pp hdvd hpodd)

/-- **Flatness of the Frey torsion representation at `p`** (DERIVED
2026-07-16 from the two preceding nodes by the case split on `p ∣ abc`):
the mod-`p` representation on the `p`-torsion of the Frey curve is flat at
`p`, i.e. arises from a finite flat group scheme over `ℤ_p`. From the
Néron model at good reduction (`torsion_isFlat_of_good`), or from the
Tate curve at `p` together with `p ∣ v_p(j)` in the multiplicative case
(`torsion_isFlat_of_multiplicative`). -/
theorem FreyCurve.torsion_isFlat :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
      P.pp.toHeightOneSpectrumRingOfIntegersRat := by
  by_cases hdvd : (P.p : ℤ) ∣ P.a * P.b * P.c
  · exact FreyCurve.torsion_isFlat_of_multiplicative P hdvd
  · exact FreyCurve.torsion_isFlat_of_good P hdvd

open WeierstrassCurve in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The tame quotient in the split case at `2`** (assembled from the
Tate valuation-exponent quotient `exists_tateTorsionQuotient`): if the
`ℚ_[2]`-base change has SPLIT multiplicative reduction, the mod-`p`
torsion of `E(ℚ̄)` carries a surjective `ZMod p`-linear quotient on
which `G_{ℚ_2}` acts TRIVIALLY — the exponent character of the Tate
uniformization, transported along the (bijective, by torsion counting)
embedding of global into local torsion. The trivial quotient is
unramified and squares to `1`: the split half of the tame-at-`2`
condition. -/
theorem exists_tame_quotient_of_split_padic_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime]
    (hp : 0 < p)
    [hsplit : (E.map (algebraMap ℚ ℚ_[2])).HasSplitMultiplicativeReduction
      (ValuativeRel.valuation ℚ_[2]).integer] :
    ∃ (π : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p
        →ₗ[ZMod p] ZMod p)
      (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] (ZMod p) (ZMod p)),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2],
        ∀ v : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p,
          π ((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
          (AddSubgroup.inertia
            ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
              AddSubgroup Z2bar)
            (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
          (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1) := by
  classical
  letI := algebraRatAlgClosurePadic 2
  -- the uniformization witness and the exponent quotient
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_tateEquivSepClosure
    (k := ℚ_[2]) (E := E.map (algebraMap ℚ ℚ_[2]))
    (Ω := AlgebraicClosure ℚ_[2])
  haveI : CharZero (AlgebraicClosure ℚ_[2]) :=
    charZero_of_injective_algebraMap
      ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])).injective)
  obtain ⟨π₀, hπ₀surj, hπ₀inv⟩ :=
    WeierstrassCurve.exists_tateTorsionQuotient
      (k := ℚ_[2]) (E := E.map (algebraMap ℚ ℚ_[2]))
      (Ω := AlgebraicClosure ℚ_[2]) e he (p := p) hp.ne'
      (Nat.cast_ne_zero.mpr hp.ne')
  -- the torsion transport, as an additive map
  let T : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →+
      AddSubgroup.torsionBy
        (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point
        ((p : ℕ) : ℤ) :=
    { toFun := fun v => ⟨WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingPadic 2)
        (show ((E⁄(AlgebraicClosure ℚ))).Point from v.1), by
          have h0 := v.2
          rw [Submodule.mem_torsionBy_iff] at h0
          have h1 : ((p : ℕ) : ℤ) • (show ((E⁄(AlgebraicClosure ℚ))).Point
              from v.1) = 0 := h0
          show ((p : ℕ) : ℤ) • (WeierstrassCurve.Affine.Point.map (W' := E)
            (algClosureEmbeddingPadic 2)
            (show ((E⁄(AlgebraicClosure ℚ))).Point from v.1)) = 0
          rw [← map_zsmul, h1, map_zero]⟩
      map_zero' := Subtype.ext (by
        show WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureEmbeddingPadic 2) 0 = 0
        exact map_zero _)
      map_add' := fun v w => Subtype.ext (by
        show WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureEmbeddingPadic 2) _ = _
        exact map_add _ _ _) }
  -- `T` is bijective: injective plus equal (finite) torsion counts
  have hTinj : Function.Injective T := by
    intro v w hvw
    have h1 := congrArg Subtype.val hvw
    have h2 := WeierstrassCurve.Affine.Point.map_injective
      (f := algClosureEmbeddingPadic 2) h1
    exact Subtype.ext h2
  have hploc : ((p : ℕ) : AlgebraicClosure ℚ_[2]) ≠ 0 :=
    Nat.cast_ne_zero.mpr hp.ne'
  have hpglob : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hp.ne'
  have hcard₁ : Nat.card ((E.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion p) = p ^ 2 :=
    WeierstrassCurve.n_torsion_card _ hpglob
  have hcard₂ : Nat.card (((E.map (algebraMap ℚ ℚ_[2])).map
      (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))).nTorsion p) = p ^ 2 :=
    WeierstrassCurve.n_torsion_card _ hploc
  -- carrier equivalence between the two torsion spellings
  let eq2 : AddSubgroup.torsionBy
      (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point
      ((p : ℕ) : ℤ) ≃
      ((E.map (algebraMap ℚ ℚ_[2])).map
        (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))).nTorsion p :=
    { toFun := fun x => ⟨x.1, by
        rw [Submodule.mem_torsionBy_iff]
        have h0 : ((p : ℕ) : ℤ) • x.1 = 0 := x.2
        exact_mod_cast h0⟩
      invFun := fun x => ⟨x.1, by
        have h1 := x.2
        rw [Submodule.mem_torsionBy_iff] at h1
        show ((p : ℕ) : ℤ) • x.1 = 0
        exact_mod_cast h1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard₃ : Nat.card (AddSubgroup.torsionBy
      (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point
      ((p : ℕ) : ℤ)) = p ^ 2 := by
    rw [Nat.card_congr eq2]
    exact hcard₂
  have hTsurj : Function.Surjective T := by
    haveI hfin : Finite (AddSubgroup.torsionBy
        (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point
        ((p : ℕ) : ℤ)) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [hcard₃]
      have := (Fact.out : p.Prime).pos
      positivity
    have hbij : Function.Bijective T :=
      (Nat.bijective_iff_injective_and_card T).mpr
        ⟨hTinj, by rw [hcard₁, hcard₃]⟩
    exact hbij.surjective
  -- the trivial quotient representation
  let δ : GaloisRep ℚ_[2] (ZMod p) (ZMod p) :=
    letI := moduleTopology (ZMod p) (Module.End (ZMod p) (ZMod p))
    { toMonoidHom := 1
      continuous_toFun := continuous_const }
  refine ⟨AddMonoidHom.toZModLinearMap p (π₀.comp T), ?_, δ, ?_⟩
  · show Function.Surjective (π₀.comp T)
    exact hπ₀surj.comp hTsurj
  intro g v
  refine ⟨?_, ?_, ?_⟩
  · -- equivariance: the action is invisible to the exponent quotient
    show π₀ (T ((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v)) =
      δ g (π₀ (T v))
    have hδ : δ g (π₀ (T v)) = π₀ (T v) := rfl
    rw [hδ]
    have hact : ((((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v) :
        (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :
        ((E.map (algebraMap ℚ
          (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point) =
        WeierstrassCurve.Affine.Point.map (W' := E)
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])) g :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
          (show ((E⁄(AlgebraicClosure ℚ))).Point from v.1) :=
      congrArg (fun f : ℚ →+* ℚ_[2] =>
        WeierstrassCurve.Affine.Point.map (W' := E)
          (((Field.absoluteGaloisGroup.map f) g :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
          (show ((E⁄(AlgebraicClosure ℚ))).Point from v.1))
        (Subsingleton.elim _ _)
    refine hπ₀inv ((g : (AlgebraicClosure ℚ_[2])
        ≃ₐ[ℚ_[2]] (AlgebraicClosure ℚ_[2]))) (T v)
      (T ((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v)) ?_
    show WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingPadic 2) _ = _
    rw [hact]
    have hcomm := point_map_algClosureEmbeddingPadic_comm 2 E g
      (show ((E⁄(AlgebraicClosure ℚ))).Point from v.1)
    rw [hcomm]
    have hbb : ∀ Q : ((E)⁄(AlgebraicClosure ℚ_[2])).Point,
        WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureSigmaPadic 2 g) Q =
        (show ((E)⁄(AlgebraicClosure ℚ_[2])).Point from
          WeierstrassCurve.Affine.Point.map
            (W' := E.map (algebraMap ℚ ℚ_[2]))
            (((g : (AlgebraicClosure ℚ_[2])
                ≃ₐ[ℚ_[2]] (AlgebraicClosure ℚ_[2]))).toAlgHom)
            (show ((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure
              ℚ_[2])).Point from Q)) := by
      intro Q
      cases Q with
      | zero => rfl
      | some x y h => rfl
    rw [hbb]
    rfl
  · -- the trivial character is unramified
    intro σ _
    show δ σ = 1
    rfl
  · -- and squares to `1`
    intro g'
    show (1 : Module.End (ZMod p) (ZMod p)) * 1 = 1
    rw [one_mul]

open WithZero in
/-- The multiplicative valuation of `ℚ_[q]` is at most `1` exactly on
the closed unit ball. -/
theorem Padic.mulValuation_le_one_iff {q : ℕ} [Fact q.Prime] (x : ℚ_[q]) :
    Padic.mulValuation x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · rw [Padic.mulValuation_eq hx0, Padic.norm_le_one_iff_val_nonneg,
      show (1 : ℤᵐ⁰) = WithZero.exp (0 : ℤ) from rfl, WithZero.exp_le_exp]
    exact neg_nonpos

set_option backward.isDefEq.respectTransparency false in
/-- Membership in `Z2bar` for base-field images is the closed unit
ball: the spectral valuation extends the `2`-adic norm. -/
theorem algebraMap_mem_Z2bar_iff (x : ℚ_[2]) :
    algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x ∈ Z2bar ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff]
  have hkey : ((Valued.v (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x) :
      NNReal) : ℝ) = ‖x‖ := by
    rw [← spectralNorm_extends (K := ℚ_[2]) (L := AlgebraicClosure ℚ_[2]) x]
    rfl
  constructor
  · intro h
    have h1 : ((Valued.v (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x) :
        NNReal) : ℝ) ≤ 1 := by exact_mod_cast h
    rw [hkey] at h1
    exact h1
  · intro h
    have h1 : ((Valued.v (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x) :
        NNReal) : ℝ) ≤ 1 := by rw [hkey]; exact h
    exact_mod_cast h1

/-- Elements of the canonical integer ring of `ℚ_[2]` have norm at most
`1`. -/
theorem norm_le_one_of_mem_integer {x : ℚ_[2]}
    (hx : x ∈ (ValuativeRel.valuation ℚ_[2]).integer) : ‖x‖ ≤ 1 := by
  have h1 : Padic.mulValuation x ≤ 1 :=
    (Valuation.isEquiv_iff_val_le_one.mp
      (ValuativeRel.isEquiv _ _)).mp ((Valuation.mem_integer_iff _ _).mp hx)
  exact (Padic.mulValuation_le_one_iff x).mp h1

open scoped Pointwise in
set_option backward.isDefEq.respectTransparency false in
/-- Every `ℚ_[2]`-automorphism of the algebraic closure stabilizes
`Z2bar`: the spectral norm is invariant under such automorphisms. -/
theorem mem_decompositionSubgroup_Z2bar
    (σ : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]] (AlgebraicClosure ℚ_[2])) :
    σ ∈ Z2bar.decompositionSubgroup ℚ_[2] := by
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hx' : Valued.v x ≤ 1 := hx
    show Valued.v (σ x) ≤ 1
    convert hx' using 1
    apply NNReal.coe_injective
    exact (spectralNorm_eq_of_equiv σ x).symm
  · intro x hx
    have hx' : Valued.v x ≤ 1 := hx
    refine ⟨σ⁻¹ x, ?_, ?_⟩
    · show Valued.v (σ⁻¹ x) ≤ 1
      convert hx' using 1
      apply NNReal.coe_injective
      exact (spectralNorm_eq_of_equiv
        (σ⁻¹ : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
          (AlgebraicClosure ℚ_[2])) x).symm
    · show σ (σ⁻¹ x) = x
      exact σ.apply_symm_apply x

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The two spellings of inertia at `Z2bar` agree**: an element of the
mod-`𝔪` inertia lies in the `ValuationSubring.inertiaSubgroup` (trivial
action on the residue field); the congruence is read through
`Ideal.Quotient.eq`. -/
theorem mem_inertiaSubgroup_Z2bar
    {g : Field.absoluteGaloisGroup ℚ_[2]}
    (hg : g ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2])) :
    (⟨(g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]] (AlgebraicClosure ℚ_[2])),
      mem_decompositionSubgroup_Z2bar _⟩ :
      Z2bar.decompositionSubgroup ℚ_[2]) ∈
      Z2bar.inertiaSubgroup ℚ_[2] := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := Z2bar) z
  have h1 : (MulSemiringAction.toRingAut
      (Z2bar.decompositionSubgroup ℚ_[2])
      (IsLocalRing.ResidueField Z2bar)
      (⟨(g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]] (AlgebraicClosure ℚ_[2])),
        mem_decompositionSubgroup_Z2bar _⟩))
      (IsLocalRing.residue _ a) =
      IsLocalRing.residue _
        ((⟨(g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2])),
          mem_decompositionSubgroup_Z2bar _⟩ :
          Z2bar.decompositionSubgroup ℚ_[2]) • a) := rfl
  rw [h1]
  show IsLocalRing.residue _ _ = IsLocalRing.residue _ a
  exact Ideal.Quotient.eq.mpr (hg a)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Inertia fixes unramified embeddings, `Z2bar` spelling** (the
`ℚ_[2]`-analogue of the PROVEN
`inertia_fixes_algHom_of_unramified_gen`, at the spectral-norm
valuation subring `Z2bar` of `ℚ_[2]ᵃˡᵍ`): for an extension `L/ℚ_[2]`
generated by `θ` with a monic integral lift `Q` of separable residue
reduction, every element of the mod-`𝔪` inertia of `Z2bar` fixes the
image of any embedding `ι : L → ℚ_[2]ᵃˡᵍ` pointwise. Content: the
master root-fixing lemma (`inertia_fixes_root_of_separable_residue`)
at `A = Z2bar`, with the coefficient transport `𝒪[ℚ_[2]] → Z2bar`
(spectral norm extends the base norm on integral elements) and the
mod-`𝔪`-to-residue-fixing bridge. -/
theorem inertia_fixes_algHom_of_unramified_gen_padic_two
    {L : Type*} [Field L] [Algebra ℚ_[2] L]
    (θ : L) (hθtop : Algebra.adjoin ℚ_[2] ({θ} : Set L) = ⊤)
    (Q : Polynomial (ValuativeRel.valuation ℚ_[2]).integer)
    (hQm : Q.Monic)
    (hθQ : Polynomial.aeval θ (Q.map (algebraMap
      (ValuativeRel.valuation ℚ_[2]).integer ℚ_[2])) = 0)
    (hQsep : (Q.map (IsLocalRing.residue
      (ValuativeRel.valuation ℚ_[2]).integer)).Separable)
    {g : Field.absoluteGaloisGroup ℚ_[2]}
    (hg : g ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2]))
    (ι : L →ₐ[ℚ_[2]] (AlgebraicClosure ℚ_[2])) (y : L) :
    (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]] (AlgebraicClosure ℚ_[2]))
      (ι y) = ι y := by
  classical
  -- the coefficient-inclusion hom into `Z2bar`
  have hmemA : ∀ z : (ValuativeRel.valuation ℚ_[2]).integer,
      (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))
        (z : ℚ_[2]) ∈ Z2bar := fun z =>
    (algebraMap_mem_Z2bar_iff _).mpr (norm_le_one_of_mem_integer z.2)
  let j₂ : (ValuativeRel.valuation ℚ_[2]).integer →+* Z2bar :=
    { toFun := fun z => ⟨_, hmemA z⟩
      map_one' := Subtype.ext (by push_cast; rfl)
      map_mul' := fun a b => Subtype.ext (by push_cast; rfl)
      map_zero' := Subtype.ext (by push_cast; rfl)
      map_add' := fun a b => Subtype.ext (by push_cast; rfl) }
  -- `j₂` is local: nonunits land in the maximal ideal
  have hj₂m : ∀ m : (ValuativeRel.valuation ℚ_[2]).integer,
      m ∈ IsLocalRing.maximalIdeal _ →
      j₂ m ∈ IsLocalRing.maximalIdeal _ := by
    intro m hm
    rw [IsLocalRing.mem_maximalIdeal] at hm ⊢
    intro hunit
    apply hm
    by_cases hm0 : (m : ℚ_[2]) = 0
    · exfalso
      have hz : j₂ m = 0 := Subtype.ext (by
        show (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])) (m : ℚ_[2]) = 0
        rw [hm0, map_zero])
      rw [hz] at hunit
      exact not_isUnit_zero hunit
    · obtain ⟨u, hu⟩ := hunit
      have huv : ((u : Z2bar) : AlgebraicClosure ℚ_[2]) =
          (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])) (m : ℚ_[2]) := by
        rw [hu]
        rfl
      have hmul : ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))
          (m : ℚ_[2])) * (((u⁻¹ : Z2barˣ) : Z2bar) :
          AlgebraicClosure ℚ_[2]) = 1 := by
        have h0 : ((u : Z2bar) * ((u⁻¹ : Z2barˣ) : Z2bar) : Z2bar) = 1 :=
          u.mul_inv
        calc ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])) (m : ℚ_[2])) *
              (((u⁻¹ : Z2barˣ) : Z2bar) : AlgebraicClosure ℚ_[2])
            = (((u : Z2bar) * ((u⁻¹ : Z2barˣ) : Z2bar) : Z2bar) :
              AlgebraicClosure ℚ_[2]) := by
              rw [← huv]
              rfl
          _ = ((1 : Z2bar) : AlgebraicClosure ℚ_[2]) := by rw [h0]
          _ = 1 := rfl
      have hainv : (((u⁻¹ : Z2barˣ) : Z2bar) : AlgebraicClosure ℚ_[2]) =
          ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))
            ((m : ℚ_[2])⁻¹)) := by
        rw [map_inv₀]
        exact eq_inv_of_mul_eq_one_right hmul
      -- the inverse has norm at most `1`, so `m` is a unit downstairs
      have hinvmem : (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))
          ((m : ℚ_[2])⁻¹) ∈ Z2bar := by
        rw [← hainv]
        exact ((u⁻¹ : Z2barˣ) : Z2bar).2
      have hninv : ‖(m : ℚ_[2])⁻¹‖ ≤ 1 :=
        (algebraMap_mem_Z2bar_iff _).mp hinvmem
      have hn : ‖(m : ℚ_[2])‖ ≤ 1 := norm_le_one_of_mem_integer m.2
      have hval1 : Padic.mulValuation (m : ℚ_[2]) = 1 := by
        have h1 : Padic.mulValuation (m : ℚ_[2]) ≤ 1 :=
          (Padic.mulValuation_le_one_iff _).mpr hn
        have h2 : (Padic.mulValuation (m : ℚ_[2]))⁻¹ ≤ 1 := by
          rw [← map_inv₀]
          exact (Padic.mulValuation_le_one_iff _).mpr hninv
        have h3 : Padic.mulValuation (m : ℚ_[2]) ≠ 0 :=
          (Padic.mulValuation).ne_zero_iff.mpr hm0
        have h4 : 1 ≤ Padic.mulValuation (m : ℚ_[2]) :=
          (inv_le_one₀ (zero_lt_iff.mpr h3)).mp h2
        exact le_antisymm h1 h4
      have hcan1 : ValuativeRel.valuation ℚ_[2] (m : ℚ_[2]) = 1 :=
        (Valuation.isEquiv_iff_val_eq_one.mp
          (ValuativeRel.isEquiv _ _)).mpr hval1
      have hints0 : (ValuativeRel.valuation ℚ_[2]).Integers
          (ValuativeRel.valuation ℚ_[2]).integer :=
        Valuation.integer.integers _
      exact hints0.isUnit_iff_valuation_eq_one.mpr hcan1
  -- the induced residue-field hom and separability of the reduction
  let φ := Ideal.Quotient.lift
    (IsLocalRing.maximalIdeal (ValuativeRel.valuation ℚ_[2]).integer)
    ((IsLocalRing.residue Z2bar).comp j₂)
    (fun m hm => by
      rw [RingHom.comp_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hj₂m m hm))
  have hfactor : (IsLocalRing.residue Z2bar).comp j₂ =
      φ.comp (IsLocalRing.residue
        (ValuativeRel.valuation ℚ_[2]).integer) := by
    apply RingHom.ext
    intro z
    rfl
  have hsepA : ((Q.map j₂).map (IsLocalRing.residue Z2bar)).Separable := by
    rw [Polynomial.map_map, hfactor, ← Polynomial.map_map]
    exact hQsep.map
  -- the image of `θ` is an integral root, hence lies in `Z2bar`
  have haevalx : Polynomial.aeval (ι θ) (Q.map (algebraMap
      (ValuativeRel.valuation ℚ_[2]).integer ℚ_[2])) = 0 := by
    rw [Polynomial.aeval_algHom_apply, hθQ, map_zero]
  have hcomp2 : (Z2bar.subtype.comp j₂) =
      ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])).comp
        (algebraMap (ValuativeRel.valuation ℚ_[2]).integer ℚ_[2])) := by
    apply RingHom.ext
    intro z
    rfl
  have hxA : (ι θ) ∈ Z2bar := by
    have hints : (Valued.v : Valuation (AlgebraicClosure ℚ_[2]) NNReal).Integers
        (Valued.v.valuationSubring : ValuationSubring
          (AlgebraicClosure ℚ_[2])) :=
      Valuation.valuationSubring.integers _
    have hint : IsIntegral (Z2bar : ValuationSubring
        (AlgebraicClosure ℚ_[2])) (ι θ) := by
      refine ⟨Q.map j₂, hQm.map _, ?_⟩
      rw [← Polynomial.eval_map, Polynomial.map_map]
      rw [show ((algebraMap (Z2bar : ValuationSubring
          (AlgebraicClosure ℚ_[2])) (AlgebraicClosure ℚ_[2])).comp j₂) =
        ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])).comp
          (algebraMap (ValuativeRel.valuation ℚ_[2]).integer ℚ_[2]))
        from hcomp2]
      rw [← Polynomial.map_map, Polynomial.eval_map,
        ← Polynomial.aeval_def]
      exact haevalx
    exact hints.mem_of_integral hint
  -- the root equation over `Z2bar`
  have hroot : (Q.map j₂).eval (⟨ι θ, hxA⟩ : Z2bar) = 0 := by
    apply Subtype.ext
    have h1 : ((((Q.map j₂).eval (⟨ι θ, hxA⟩ : Z2bar)) : Z2bar) :
        AlgebraicClosure ℚ_[2]) =
        ((Q.map j₂).map Z2bar.subtype).eval (ι θ) := by
      conv_rhs => rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_apply (p := Q.map j₂)
        Z2bar.subtype (⟨ι θ, hxA⟩ : Z2bar)).symm
    show ((((Q.map j₂).eval (⟨ι θ, hxA⟩ : Z2bar)) : Z2bar) :
        AlgebraicClosure ℚ_[2]) =
      (((0 : Z2bar)) : AlgebraicClosure ℚ_[2])
    rw [h1, Polynomial.map_map, hcomp2, ← Polynomial.map_map,
      Polynomial.eval_map, ← Polynomial.aeval_def]
    exact haevalx
  -- coefficients come from the base field
  have hcoeff : ∀ i, (((Q.map j₂).coeff i : Z2bar) :
      AlgebraicClosure ℚ_[2]) ∈
      Set.range (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])) := by
    intro i
    rw [Polynomial.coeff_map]
    exact ⟨((Q.coeff i : (ValuativeRel.valuation ℚ_[2]).integer) :
      ℚ_[2]), rfl⟩
  -- the master root-fixing lemma fixes `ι θ`
  have hθfix := (Z2bar : ValuationSubring
    (AlgebraicClosure ℚ_[2])).inertia_fixes_root_of_separable_residue
    (⟨(g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]] (AlgebraicClosure ℚ_[2])),
      mem_decompositionSubgroup_Z2bar _⟩)
    (mem_inertiaSubgroup_Z2bar hg)
    (Q.map j₂) hcoeff hsepA hxA hroot
  -- `θ` generates: the embedding is fixed pointwise
  have hle : Algebra.adjoin ℚ_[2] ({θ} : Set L) ≤
      AlgHom.equalizer
        (((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
          (AlgebraicClosure ℚ_[2]))).toAlgHom.comp ι) ι := by
    rw [Algebra.adjoin_le_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hθfix
  rw [hθtop] at hle
  exact hle (Algebra.mem_top)

open WeierstrassCurve in
open scoped WeierstrassCurve.Affine in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **Tame quotient at `2`, nonsplit case** (assembled — the
Tate-theoretic content of the tame-at-`2` condition): as the split case
(`exists_tame_quotient_of_split_padic_two`), but the `ℚ_[2]`-base
change has NONSPLIT multiplicative reduction. The unramified quadratic
twist has split reduction, and its exponent quotient transports back
with the action twisted by the quadratic character of the unramified
quadratic extension — which is unramified (inertia fixes unramified
extensions) and squares to `1`. -/
theorem WeierstrassCurve.exists_tame_quotient_of_nonsplit_padic_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime] (hp : 0 < p)
    (_hp2 : p ≠ 2)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat.asIdeal)]
    (hnonsplit : ¬ (E.map (algebraMap ℚ ℚ_[2])).HasSplitMultiplicativeReduction
      (ValuativeRel.valuation ℚ_[2]).integer) :
    ∃ (π : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p
        →ₗ[ZMod p] ZMod p)
      (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] (ZMod p) (ZMod p)),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2],
        ∀ v : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p,
          π ((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
          (AddSubgroup.inertia
            ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
              AddSubgroup Z2bar)
            (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
          (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1) := by
  classical
  letI := algebraRatAlgClosurePadic 2
  haveI := hasMultiplicativeReduction_padic Nat.prime_two E
  -- the unramified quadratic twist with split reduction and its witness
  obtain ⟨L, _, _, _, _, hsplit', θL, Q, hQm, hθtop, hθQ, hQsep⟩ :=
    WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction
      (E := E.map (algebraMap ℚ ℚ_[2]))
      (R := (ValuativeRel.valuation ℚ_[2]).integer) hnonsplit
  set Tw : WeierstrassCurve ℚ_[2] :=
    (E.map (algebraMap ℚ ℚ_[2])).quadraticTwist L
  set Mt : WeierstrassCurve ℚ_[2] :=
    Tw.minimal (ValuativeRel.valuation ℚ_[2]).integer
  set Cb : WeierstrassCurve.VariableChange (AlgebraicClosure ℚ_[2]) :=
    ((Tw.exists_isMinimal
      (ValuativeRel.valuation ℚ_[2]).integer).choose.baseChange
      (AlgebraicClosure ℚ_[2])) with hCbdef
  haveI hMtsplit : Mt.HasSplitMultiplicativeReduction
      (ValuativeRel.valuation ℚ_[2]).integer := hsplit'
  haveI hTwell : Tw.IsElliptic :=
    inferInstanceAs (((E.map (algebraMap ℚ ℚ_[2])).quadraticTwist
      L).IsElliptic)
  haveI hMtell : Mt.IsElliptic :=
    inferInstanceAs (((Tw.exists_isMinimal
      (ValuativeRel.valuation ℚ_[2]).integer).choose • Tw).IsElliptic)
  haveI hTwΩell : (Tw⁄(AlgebraicClosure ℚ_[2])).IsElliptic :=
    inferInstanceAs ((Tw.map (algebraMap ℚ_[2]
      (AlgebraicClosure ℚ_[2]))).IsElliptic)
  letI algLΩ : Algebra L (AlgebraicClosure ℚ_[2]) :=
    (IsAlgClosed.lift (M := AlgebraicClosure ℚ_[2]) (R := ℚ_[2])
      (S := L)).toAlgebra
  haveI : IsScalarTower ℚ_[2] L (AlgebraicClosure ℚ_[2]) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      ((IsAlgClosed.lift (M := AlgebraicClosure ℚ_[2]) (R := ℚ_[2])
        (S := L)).commutes x).symm)
  -- uniformization witness and exponent quotient for the twisted minimal model
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_tateEquivSepClosure
    (k := ℚ_[2]) (E := Mt) (Ω := AlgebraicClosure ℚ_[2])
  haveI : CharZero (AlgebraicClosure ℚ_[2]) :=
    charZero_of_injective_algebraMap
      ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])).injective)
  obtain ⟨π₀, hπ₀surj, hπ₀inv⟩ :=
    WeierstrassCurve.exists_tateTorsionQuotient
      (k := ℚ_[2]) (E := Mt) (Ω := AlgebraicClosure ℚ_[2]) e he
      (p := p) hp.ne' (Nat.cast_ne_zero.mpr hp.ne')
  -- the point equivalence to the base change
  have hEq : (Mt⁄(AlgebraicClosure ℚ_[2])) =
      Cb • (Tw⁄(AlgebraicClosure ℚ_[2])) :=
    (WeierstrassCurve.baseChange_smul_baseChange _ _ _).symm
  let Φ : ((Mt⁄(AlgebraicClosure ℚ_[2])).Point) ≃+
      (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2])).Point) :=
    ((WeierstrassCurve.Affine.Point.equivOfEq hEq).trans
      (WeierstrassCurve.Affine.Point.equivVariableChange
        (Tw⁄(AlgebraicClosure ℚ_[2])) Cb)).trans
      ((E.map (algebraMap ℚ ℚ_[2])).quadraticTwistPointEquiv L
        (AlgebraicClosure ℚ_[2]))
  -- coefficient fixedness under every local automorphism
  have hσu : ∀ g : Field.absoluteGaloisGroup ℚ_[2],
      (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
        (AlgebraicClosure ℚ_[2])).toAlgHom
        ((Cb.u : AlgebraicClosure ℚ_[2])) =
      (Cb.u : AlgebraicClosure ℚ_[2]) := by
    intro g
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map, Units.coe_map, MonoidHom.coe_coe]
    exact ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
      (AlgebraicClosure ℚ_[2])).toAlgHom).commutes _
  have hσr : ∀ g : Field.absoluteGaloisGroup ℚ_[2],
      (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
        (AlgebraicClosure ℚ_[2])).toAlgHom Cb.r = Cb.r := by
    intro g
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map]
    exact ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
      (AlgebraicClosure ℚ_[2])).toAlgHom).commutes _
  have hσs : ∀ g : Field.absoluteGaloisGroup ℚ_[2],
      (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
        (AlgebraicClosure ℚ_[2])).toAlgHom Cb.s = Cb.s := by
    intro g
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map]
    exact ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
      (AlgebraicClosure ℚ_[2])).toAlgHom).commutes _
  have hσt : ∀ g : Field.absoluteGaloisGroup ℚ_[2],
      (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
        (AlgebraicClosure ℚ_[2])).toAlgHom Cb.t = Cb.t := by
    intro g
    rw [hCbdef]
    simp only [WeierstrassCurve.VariableChange.baseChange,
      WeierstrassCurve.VariableChange.map]
    exact ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
      (AlgebraicClosure ℚ_[2])).toAlgHom).commutes _
  -- Φ-equivariance, twisted by the quadratic character
  have hcommΦ : ∀ (g : Field.absoluteGaloisGroup ℚ_[2])
      (Qt : (Mt⁄(AlgebraicClosure ℚ_[2])).Point),
      Φ (WeierstrassCurve.Affine.Point.map (W' := Mt)
        (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
          (AlgebraicClosure ℚ_[2])).toAlgHom Qt) =
      ((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
        (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
          (AlgebraicClosure ℚ_[2]))) : ℤ) •
        WeierstrassCurve.Affine.Point.map (W' := E.map (algebraMap ℚ ℚ_[2]))
          (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2])).toAlgHom (Φ Qt) := by
    intro g Qt
    have h12 : (WeierstrassCurve.Affine.Point.equivVariableChange
        (Tw⁄(AlgebraicClosure ℚ_[2])) Cb)
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq)
          (WeierstrassCurve.Affine.Point.map (W' := Mt)
            (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
              (AlgebraicClosure ℚ_[2])).toAlgHom Qt)) =
        WeierstrassCurve.Affine.Point.map (W' := Tw)
          (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2])).toAlgHom
          ((WeierstrassCurve.Affine.Point.equivVariableChange
            (Tw⁄(AlgebraicClosure ℚ_[2])) Cb)
            ((WeierstrassCurve.Affine.Point.equivOfEq hEq) Qt)) := by
      cases Qt with
      | zero => simp [← WeierstrassCurve.Affine.Point.zero_def]
      | some x y hxy =>
        rw [WeierstrassCurve.Affine.Point.map_some,
          WeierstrassCurve.Affine.Point.equivOfEq_some,
          WeierstrassCurve.Affine.Point.equivOfEq_some,
          WeierstrassCurve.Affine.Point.equivVariableChange_some,
          WeierstrassCurve.Affine.Point.equivVariableChange_some,
          WeierstrassCurve.Affine.Point.map_some]
        refine WeierstrassCurve.Affine.Point.some_eq_some _ ?_ ?_
        · simp only [map_add, map_mul, map_pow, hσu g, hσr g]
        · simp only [map_add, map_mul, map_pow, hσu g, hσs g, hσt g]
    show ((E.map (algebraMap ℚ ℚ_[2])).quadraticTwistPointEquiv L
        (AlgebraicClosure ℚ_[2]))
        ((WeierstrassCurve.Affine.Point.equivVariableChange
          (Tw⁄(AlgebraicClosure ℚ_[2])) Cb)
          ((WeierstrassCurve.Affine.Point.equivOfEq hEq)
            (WeierstrassCurve.Affine.Point.map (W' := Mt)
              (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
                (AlgebraicClosure ℚ_[2])).toAlgHom Qt))) = _
    rw [h12]
    exact (E.map (algebraMap ℚ ℚ_[2])).quadraticTwistPointEquiv_galois L
      (M := AlgebraicClosure ℚ_[2])
      ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]] (AlgebraicClosure ℚ_[2])))
      ((WeierstrassCurve.Affine.Point.equivVariableChange
        (Tw⁄(AlgebraicClosure ℚ_[2])) Cb)
        ((WeierstrassCurve.Affine.Point.equivOfEq hEq) Qt))
  -- the global-to-local torsion transport (as in the split case)
  let T : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →+
      AddSubgroup.torsionBy
        (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point
        ((p : ℕ) : ℤ) :=
    { toFun := fun v => ⟨WeierstrassCurve.Affine.Point.map (W' := E)
        (algClosureEmbeddingPadic 2)
        (show ((E⁄(AlgebraicClosure ℚ))).Point from v.1), by
          have h0 := v.2
          rw [Submodule.mem_torsionBy_iff] at h0
          have h1 : ((p : ℕ) : ℤ) • (show ((E⁄(AlgebraicClosure ℚ))).Point
              from v.1) = 0 := h0
          show ((p : ℕ) : ℤ) • (WeierstrassCurve.Affine.Point.map (W' := E)
            (algClosureEmbeddingPadic 2)
            (show ((E⁄(AlgebraicClosure ℚ))).Point from v.1)) = 0
          rw [← map_zsmul, h1, map_zero]⟩
      map_zero' := Subtype.ext (by
        show WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureEmbeddingPadic 2) 0 = 0
        exact map_zero _)
      map_add' := fun v w => Subtype.ext (by
        show WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureEmbeddingPadic 2) _ = _
        exact map_add _ _ _) }
  have hTinj : Function.Injective T := by
    intro v w hvw
    have h1 := congrArg Subtype.val hvw
    have h2 := WeierstrassCurve.Affine.Point.map_injective
      (f := algClosureEmbeddingPadic 2) h1
    exact Subtype.ext h2
  have hcard₁ : Nat.card ((E.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).nTorsion p) = p ^ 2 :=
    WeierstrassCurve.n_torsion_card _ (Nat.cast_ne_zero.mpr hp.ne')
  have hcard₂ : Nat.card (((E.map (algebraMap ℚ ℚ_[2])).map
      (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))).nTorsion p) = p ^ 2 :=
    WeierstrassCurve.n_torsion_card _ (Nat.cast_ne_zero.mpr hp.ne')
  let eq2 : AddSubgroup.torsionBy
      (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point
      ((p : ℕ) : ℤ) ≃
      ((E.map (algebraMap ℚ ℚ_[2])).map
        (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))).nTorsion p :=
    { toFun := fun x => ⟨x.1, by
        rw [Submodule.mem_torsionBy_iff]
        have h0 : ((p : ℕ) : ℤ) • x.1 = 0 := x.2
        exact_mod_cast h0⟩
      invFun := fun x => ⟨x.1, by
        have h1 := x.2
        rw [Submodule.mem_torsionBy_iff] at h1
        show ((p : ℕ) : ℤ) • x.1 = 0
        exact_mod_cast h1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard₃ : Nat.card (AddSubgroup.torsionBy
      (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point
      ((p : ℕ) : ℤ)) = p ^ 2 := by
    rw [Nat.card_congr eq2]
    exact hcard₂
  have hTsurj : Function.Surjective T := by
    haveI hfin : Finite (AddSubgroup.torsionBy
        (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point
        ((p : ℕ) : ℤ)) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [hcard₃]
      have := (Fact.out : p.Prime).pos
      positivity
    have hbij : Function.Bijective T :=
      (Nat.bijective_iff_injective_and_card T).mpr
        ⟨hTinj, by rw [hcard₁, hcard₃]⟩
    exact hbij.surjective
  -- torsion transport through `Φ.symm`
  let T' : AddSubgroup.torsionBy
      (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point
      ((p : ℕ) : ℤ) →+
      AddSubgroup.torsionBy ((Mt⁄(AlgebraicClosure ℚ_[2]))).Point
      ((p : ℕ) : ℤ) :=
    { toFun := fun x => ⟨Φ.symm x.1, by
        have h0 : ((p : ℕ) : ℤ) • x.1 = 0 := x.2
        show ((p : ℕ) : ℤ) • Φ.symm x.1 = 0
        rw [← map_zsmul Φ.symm, h0, map_zero]⟩
      map_zero' := Subtype.ext (by
        show Φ.symm 0 = 0
        exact map_zero _)
      map_add' := fun x y => Subtype.ext (by
        show Φ.symm (x.1 + y.1) = Φ.symm x.1 + Φ.symm y.1
        exact map_add _ _ _) }
  have hT'surj : Function.Surjective T' := by
    intro y
    refine ⟨⟨Φ y.1, ?_⟩, Subtype.ext ?_⟩
    · have h0 : ((p : ℕ) : ℤ) • y.1 = 0 := y.2
      show ((p : ℕ) : ℤ) • Φ y.1 = 0
      rw [← map_zsmul Φ, h0, map_zero]
    · show Φ.symm (Φ y.1) = y.1
      exact Φ.symm_apply_apply _
  -- the quadratic-character quotient representation
  haveI hHfd : FiniteDimensional ℚ_[2]
      ((IsScalarTower.toAlgHom ℚ_[2] L
        (AlgebraicClosure ℚ_[2])).fieldRange) :=
    LinearEquiv.finiteDimensional
      (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ_[2] L
        (AlgebraicClosure ℚ_[2]))).toLinearEquiv
  have hHopen : IsOpen (((IsScalarTower.toAlgHom ℚ_[2] L
      (AlgebraicClosure ℚ_[2])).fieldRange).fixingSubgroup :
      Set (Field.absoluteGaloisGroup ℚ_[2])) :=
    ((IsScalarTower.toAlgHom ℚ_[2] L
      (AlgebraicClosure ℚ_[2])).fieldRange).fixingSubgroup_isOpen
  have hfixχ : ∀ h : Field.absoluteGaloisGroup ℚ_[2],
      h ∈ ((IsScalarTower.toAlgHom ℚ_[2] L
        (AlgebraicClosure ℚ_[2])).fieldRange).fixingSubgroup →
      quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
        (h : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
          (AlgebraicClosure ℚ_[2])) = 1 := by
    intro h hh
    rw [quadraticCharacter_eq_one_iff]
    intro x
    exact hh ⟨algebraMap L (AlgebraicClosure ℚ_[2]) x, ⟨x, rfl⟩⟩
  let δ : GaloisRep ℚ_[2] (ZMod p) (ZMod p) :=
    letI := moduleTopology (ZMod p) (Module.End (ZMod p) (ZMod p))
    { toFun := fun g =>
        (((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
          (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2])) : ℤ) : ZMod p)) •
          (1 : Module.End (ZMod p) (ZMod p))
      map_one' := by
        have h1 : ((1 : Field.absoluteGaloisGroup ℚ_[2]) :
            (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
              (AlgebraicClosure ℚ_[2])) = 1 := rfl
        rw [h1, map_one]
        simp
      map_mul' := fun a b => by
        have h1 : ((a * b : Field.absoluteGaloisGroup ℚ_[2]) :
            (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
              (AlgebraicClosure ℚ_[2])) =
            (a : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
              (AlgebraicClosure ℚ_[2])) *
            (b : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
              (AlgebraicClosure ℚ_[2])) := rfl
        rw [h1, map_mul]
        push_cast
        rw [smul_mul_smul_comm, one_mul]
      continuous_toFun := by
        refine continuous_def.mpr fun U _ =>
          isOpen_iff_forall_mem_open.mpr fun σ hσ' => ?_
        open Pointwise in
        refine ⟨σ • ((((IsScalarTower.toAlgHom ℚ_[2] L
          (AlgebraicClosure ℚ_[2])).fieldRange).fixingSubgroup :
          Subgroup (Field.absoluteGaloisGroup ℚ_[2])) :
          Set (Field.absoluteGaloisGroup ℚ_[2])), ?_, ?_, ?_⟩
        · rintro τ ⟨u, hu, rfl⟩
          show (((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
            ((σ * u : Field.absoluteGaloisGroup ℚ_[2]) :
              (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
                (AlgebraicClosure ℚ_[2])) : ℤ) : ZMod p)) •
            (1 : Module.End (ZMod p) (ZMod p)) ∈ U
          have h2 : ((σ * u : Field.absoluteGaloisGroup ℚ_[2]) :
              (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
                (AlgebraicClosure ℚ_[2])) =
              (σ : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
                (AlgebraicClosure ℚ_[2])) *
              (u : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
                (AlgebraicClosure ℚ_[2])) := rfl
          rw [h2, map_mul, hfixχ u hu, mul_one]
          exact hσ'
        · exact hHopen.leftCoset σ
        · exact ⟨1, Subgroup.one_mem _, mul_one σ⟩ }
  -- assemble
  refine ⟨AddMonoidHom.toZModLinearMap p (π₀.comp (T'.comp T)), ?_, δ, ?_⟩
  · show Function.Surjective (π₀.comp (T'.comp T))
    exact hπ₀surj.comp (hT'surj.comp hTsurj)
  intro g v
  refine ⟨?_, ?_, ?_⟩
  · -- equivariance: the action descends to the quadratic character
    show π₀ (T' (T ((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v))) =
      δ g (π₀ (T' (T v)))
    -- the acted point transports to the local `σ`-image
    have hact : ((((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v) :
        (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :
        ((E.map (algebraMap ℚ
          (AlgebraicClosure ℚ)))⁄(AlgebraicClosure ℚ)).Point) =
        WeierstrassCurve.Affine.Point.map (W' := E)
          (((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])) g :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
          (show ((E⁄(AlgebraicClosure ℚ))).Point from v.1) :=
      congrArg (fun f : ℚ →+* ℚ_[2] =>
        WeierstrassCurve.Affine.Point.map (W' := E)
          (((Field.absoluteGaloisGroup.map f) g :
            AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)).toAlgHom
          (show ((E⁄(AlgebraicClosure ℚ))).Point from v.1))
        (Subsingleton.elim _ _)
    have hbb : ∀ Q : ((E)⁄(AlgebraicClosure ℚ_[2])).Point,
        WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureSigmaPadic 2 g) Q =
        (show ((E)⁄(AlgebraicClosure ℚ_[2])).Point from
          WeierstrassCurve.Affine.Point.map
            (W' := E.map (algebraMap ℚ ℚ_[2]))
            (((g : (AlgebraicClosure ℚ_[2])
                ≃ₐ[ℚ_[2]] (AlgebraicClosure ℚ_[2]))).toAlgHom)
            (show ((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure
              ℚ_[2])).Point from Q)) := by
      intro Q
      cases Q with
      | zero => rfl
      | some x y h => rfl
    have hstep1 : (T ((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v) :
        (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point) =
        WeierstrassCurve.Affine.Point.map (W' := E.map (algebraMap ℚ ℚ_[2]))
          ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2]))).toAlgHom ((T v).1) := by
      show WeierstrassCurve.Affine.Point.map (W' := E)
          (algClosureEmbeddingPadic 2) _ = _
      rw [hact]
      have hcomm := point_map_algClosureEmbeddingPadic_comm 2 E g
        (show ((E⁄(AlgebraicClosure ℚ))).Point from v.1)
      rw [hcomm]
      rw [hbb]
      rfl
    -- transport through `Φ.symm` picks up the character
    have hχsq : ∀ x : ((Mt⁄(AlgebraicClosure ℚ_[2])).Point),
        ((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
          (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2]))) : ℤ) •
        (((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
          (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2]))) : ℤ) • x) = x := by
      intro x
      rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
        one_smul]
    have hΦsymm : ∀ R : (((E.map (algebraMap ℚ
        ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point,
        Φ.symm (WeierstrassCurve.Affine.Point.map
          (W' := E.map (algebraMap ℚ ℚ_[2]))
          ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2]))).toAlgHom R) =
        ((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
          (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2]))) : ℤ) •
          WeierstrassCurve.Affine.Point.map (W' := Mt)
            ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
              (AlgebraicClosure ℚ_[2]))).toAlgHom (Φ.symm R) := by
      intro R
      have h1 := hcommΦ g (Φ.symm R)
      rw [Φ.apply_symm_apply] at h1
      have h2 := congrArg Φ.symm h1
      rw [Φ.symm_apply_apply, map_zsmul Φ.symm] at h2
      rw [h2, hχsq]
    -- assemble the three steps
    have htorQ : ((p : ℕ) : ℤ) • (WeierstrassCurve.Affine.Point.map
        (W' := Mt) ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
          (AlgebraicClosure ℚ_[2]))).toAlgHom ((T' (T v)).1)) = 0 := by
      have h0 : ((p : ℕ) : ℤ) • ((T' (T v)).1) = 0 := (T' (T v)).2
      rw [← map_zsmul (WeierstrassCurve.Affine.Point.map (W' := Mt)
        ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
          (AlgebraicClosure ℚ_[2]))).toAlgHom), h0, map_zero]
    have hstep2 : T' (T ((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v)) =
        ((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
          (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2]))) : ℤ) •
        (⟨WeierstrassCurve.Affine.Point.map (W' := Mt)
          ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
            (AlgebraicClosure ℚ_[2]))).toAlgHom ((T' (T v)).1), htorQ⟩ :
          AddSubgroup.torsionBy ((Mt⁄(AlgebraicClosure ℚ_[2]))).Point
            ((p : ℕ) : ℤ)) := by
      apply Subtype.ext
      show Φ.symm (T ((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v) :
        (((E.map (algebraMap ℚ ℚ_[2]))⁄(AlgebraicClosure ℚ_[2]))).Point) = _
      rw [hstep1, hΦsymm]
      rfl
    rw [hstep2, map_zsmul π₀]
    have hinv := hπ₀inv ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
        (AlgebraicClosure ℚ_[2]))) (T' (T v))
      (⟨WeierstrassCurve.Affine.Point.map (W' := Mt)
        ((g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
          (AlgebraicClosure ℚ_[2]))).toAlgHom ((T' (T v)).1), htorQ⟩) rfl
    rw [hinv]
    show _ = (((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
      (g : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
        (AlgebraicClosure ℚ_[2])) : ℤ) : ZMod p)) •
      (1 : Module.End (ZMod p) (ZMod p)) (π₀ (T' (T v)))
    rw [Module.End.one_apply, zsmul_eq_mul, smul_eq_mul]
  · -- the character is unramified: inertia fixes the unramified `L`
    intro g' hg'
    show (((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
      (g' : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
        (AlgebraicClosure ℚ_[2])) : ℤ) : ZMod p)) •
      (1 : Module.End (ZMod p) (ZMod p)) = 1
    have hχ1 : quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
        (g' : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
          (AlgebraicClosure ℚ_[2])) = 1 := by
      rw [quadraticCharacter_eq_one_iff]
      intro x
      exact inertia_fixes_algHom_of_unramified_gen_padic_two
        θL hθtop Q hQm hθQ hQsep hg'
        (IsAlgClosed.lift (M := AlgebraicClosure ℚ_[2]) (R := ℚ_[2])
          (S := L)) x
    rw [hχ1]
    simp
  · -- and squares to `1`
    intro g'
    show ((((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
      (g' : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
        (AlgebraicClosure ℚ_[2])) : ℤ) : ZMod p)) •
      (1 : Module.End (ZMod p) (ZMod p))) *
      ((((quadraticCharacter ℚ_[2] L (AlgebraicClosure ℚ_[2])
      (g' : (AlgebraicClosure ℚ_[2]) ≃ₐ[ℚ_[2]]
        (AlgebraicClosure ℚ_[2])) : ℤ) : ZMod p)) •
      (1 : Module.End (ZMod p) (ZMod p))) = 1
    rw [smul_mul_smul_comm, one_mul, ← Int.cast_mul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, Int.cast_one, one_smul]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Tame quotient at `2` from multiplicative reduction** (assembled
from the split assembly `exists_tame_quotient_of_split_padic_two`, the
reduction transfer `hasMultiplicativeReduction_padic`, and the nonsplit
leaf, by the split/nonsplit case split): if `E` has multiplicative
reduction at `2` and `p` is an odd prime, then restricted to `G_{ℚ_2}`
the mod-`p` torsion representation has a surjection onto a rank-1
quotient on which the action is through an unramified character whose
square is trivial. -/
theorem WeierstrassCurve.isTameAtTwo_of_hasMultiplicativeReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime] (hp : 0 < p)
    (hp2 : p ≠ 2)
    [E.HasMultiplicativeReduction
      (Localization.AtPrime Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat.asIdeal)] :
    ∃ (π : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p
        →ₗ[ZMod p] ZMod p)
      (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] (ZMod p) (ZMod p)),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2],
        ∀ v : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p,
          π ((E.galoisRep p hp).map (algebraMap ℚ ℚ_[2]) g v)
              = δ g (π v) ∧
            (AddSubgroup.inertia
              ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
              (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
            (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) := by
  classical
  haveI := hasMultiplicativeReduction_padic Nat.prime_two E
  by_cases hsp : (E.map (algebraMap ℚ ℚ_[2])).HasSplitMultiplicativeReduction
      (ValuativeRel.valuation ℚ_[2]).integer
  · haveI := hsp
    obtain ⟨π, hπ, δ, hδ⟩ := exists_tame_quotient_of_split_padic_two E hp
    exact ⟨π, hπ, δ, fun g v => ⟨(hδ g v).1, (hδ g v).2.1, (hδ g v).2.2⟩⟩
  · obtain ⟨π, hπ, δ, hδ⟩ :=
      WeierstrassCurve.exists_tame_quotient_of_nonsplit_padic_two E hp hp2 hsp
    exact ⟨π, hπ, δ, fun g v => ⟨(hδ g v).1, (hδ g v).2.1, (hδ g v).2.2⟩⟩

/-- **Tameness of the Frey torsion representation at `2`** (DERIVED
2026-07-16): the Frey curve has multiplicative reduction at `2`
(`FreyPackage.freyCurve_hasMultiplicativeReduction_at_two`, PROVEN —
this is where `b ≡ 0 mod 2` and `a ≡ 3 mod 4` are used), and the Tate
glue at `2` (`isTameAtTwo_of_hasMultiplicativeReduction`) produces the
rank-1 unramified quotient with character squaring to `1`. -/
theorem FreyCurve.torsion_isTameAtTwo :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∃ (π : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p
        →ₗ[ZMod P.p] ZMod P.p)
      (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] (ZMod P.p) (ZMod P.p)),
      ∀ g : Field.absoluteGaloisGroup ℚ_[2],
        ∀ v : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p,
          π ((P.freyCurve.galoisRep P.p P.hppos).map (algebraMap ℚ ℚ_[2]) g v)
              = δ g (π v) ∧
            (AddSubgroup.inertia
              ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
              (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
            (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) := by
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  have hp2 : P.p ≠ 2 := by
    have := P.hp5
    omega
  haveI := P.freyCurve_hasMultiplicativeReduction_at_two
  exact WeierstrassCurve.isTameAtTwo_of_hasMultiplicativeReduction
    P.freyCurve P.hppos hp2
