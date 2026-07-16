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
-- The Frey good-reduction node and the NOS local-global glue node, used
-- to derive `torsion_isUnramified_of_good`.
import Fermat.FLT.FreyCurve.Semistable

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
  exact WeierstrassCurve.isUnramifiedAt_of_hasGoodReduction P.freyCurve P.hppos hq hq2p.2

set_option warn.sorry false in
/-- **Unramifiedness at multiplicative primes** (sorry node): at a prime
`q ∉ {2, p}` dividing `abc`, the Frey curve has multiplicative reduction
and non-integral `j`-invariant with `p ∣ v_q(j)`
(`FreyCurve.j_valuation_of_bad_prime`). After the unramified quadratic
twist making the reduction split
(`exists_quadraticTwist_hasSplitMultiplicativeReduction`), the **Tate
uniformization** (`WeierstrassCurve.exists_tateEquivSepClosure`)
identifies `E[p]` with the group generated by `μ_p` and a `p`-th root of
the Tate parameter `q_E`; since `p ∣ v_q(q_E) = -v_q(j)`, the root can be
chosen so that inertia (which fixes `μ_p ⊆ ℚ_q^{unr}` and moves `q_E^{1/p}`
by roots of unity that are trivial here) acts trivially. -/
theorem FreyCurve.torsion_isUnramified_of_multiplicative :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ q (hq : q.Prime), q ≠ 2 ∧ q ≠ P.p → (q : ℤ) ∣ P.a * P.b * P.c →
      (P.freyCurve.galoisRep P.p P.hppos).IsUnramifiedAt
        hq.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

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

set_option warn.sorry false in
/-- **Flatness at `p`, multiplicative case** (sorry node): if `p ∣ abc`
then the Frey curve has multiplicative reduction at `p` with
`p ∣ v_p(j)` (`FreyCurve.j_valuation_of_bad_prime`), so after the
unramified quadratic twist making the reduction split, the Tate
uniformization identifies `E[p]` over `ℚ_p` with an extension of `ℤ/p` by
`μ_p` that is *peu ramifiée* (the Tate parameter is a `p`-th power times
a unit, as `p ∣ v_p(q_E)`), and such extensions prolong to finite flat
group schemes over `ℤ_p`. -/
theorem FreyCurve.torsion_isFlat_of_multiplicative :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.p : ℤ) ∣ P.a * P.b * P.c →
      (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
        P.pp.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

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

set_option warn.sorry false in
/-- **Tameness of the Frey torsion representation at `2`** (sorry node):
restricted to `G_{ℚ_2}`, the mod-`p` representation on the `p`-torsion of
the Frey curve has a surjection onto a rank-1 quotient on which the action
is through an unramified character whose square is trivial. The Frey curve
has multiplicative reduction at `2` (using `b ≡ 0 mod 2`, `a ≡ 3 mod 4`),
so the Tate-curve uniformization at `2` gives the exact sequence
`0 → μ_p → E[p] → ℤ/p → 0` over `G_{ℚ_2}` up to the unramified quadratic
twist, whose quotient character squares to `1`. -/
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
            (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) :=
  sorry
