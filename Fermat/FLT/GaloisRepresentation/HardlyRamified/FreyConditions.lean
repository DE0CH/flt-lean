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

set_option warn.sorry false in
/-- **Unramifiedness of the Frey torsion representation outside `2p`**
(sorry node): the mod-`p` representation on the `p`-torsion of the Frey
curve is unramified at every prime `q` with `q ≠ 2` and `q ≠ p`.
Néron–Ogg–Shafarevich at primes of good reduction; the Tate curve plus
`p ∣ v_q(j)` (`FreyCurve.j_valuation_of_bad_prime`) at the multiplicative
primes of the semistable Frey curve. -/
theorem FreyCurve.torsion_isUnramified :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∀ q (hq : q.Prime), q ≠ 2 ∧ q ≠ P.p →
      (P.freyCurve.galoisRep P.p P.hppos).IsUnramifiedAt
        hq.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

set_option warn.sorry false in
/-- **Flatness of the Frey torsion representation at `p`** (sorry node):
the mod-`p` representation on the `p`-torsion of the Frey curve is flat at
`p`, i.e. arises from a finite flat group scheme over `ℤ_p`. From the
Néron model at good reduction, or from the Tate curve at `p` together with
`p ∣ v_p(j)` in the multiplicative case. -/
theorem FreyCurve.torsion_isFlat :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    (P.freyCurve.galoisRep P.p P.hppos).IsFlatAt
      P.pp.toHeightOneSpectrumRingOfIntegersRat :=
  sorry

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
