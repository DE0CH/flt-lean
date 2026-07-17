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

set_option warn.sorry false in
/-- **Tame quotient at `2`, nonsplit case** (sorry node — the remaining
Tate-theoretic content of the tame-at-`2` condition): as the split case
(`exists_tame_quotient_of_split_padic_two`), but the `ℚ_[2]`-base
change has NONSPLIT multiplicative reduction. The unramified quadratic
twist has split reduction, and its exponent quotient transports back
with the action twisted by the quadratic character of the unramified
quadratic extension — which is unramified (inertia fixes unramified
extensions) and squares to `1`. -/
theorem WeierstrassCurve.exists_tame_quotient_of_nonsplit_padic_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} [Fact p.Prime] (hp : 0 < p)
    (hp2 : p ≠ 2)
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
          (∀ g' : Field.absoluteGaloisGroup ℚ_[2], δ g' * δ g' = 1) :=
  sorry

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
