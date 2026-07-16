/-
Lift.lean — own work for the Fermat project (not vendored from the FLT
project).

The decomposition of **B5** ("hardly ramified mod-ℓ with ℓ ≥ 5 is not
irreducible") following the FLT project's plan (Buzzard, 2026 EPSRC course,
Lecture 4):

* **B6a** (`exists_hardlyRamifiedLift`, sorry node): an irreducible hardly
  ramified mod-`ℓ` representation lifts to a hardly ramified `ℓ`-adic
  representation over the integers `O` of a finite extension of `ℚ_ℓ`,
  compatibly with characteristic polynomials of Frobenius. The lift data is
  bundled in the structure `HardlyRamifiedLift`.

* **B6bc** (`residual_charFrob_eq`, sorry node): the residual
  characteristic polynomials of Frobenius of a liftable representation are
  those of `1 ⊕ χ̄` (i.e. `X² − (q+1)X + q` at `Frob_q`). Mathematically
  this is the composite of two further statements which a later layer must
  separate: the `ℓ`-adic lift spreads out into a weakly compatible family
  of hardly ramified `p`-adic representations over the completions of a
  number field (B6b, "spreading out" — provable *without* a residual
  modularity hypothesis, the 21st-century input), and any hardly ramified
  `3`-adic representation is an extension of the trivial character by the
  cyclotomic character (B6c), which pins the traces of the whole family.

* **Chebotarev–Brauer–Nesbitt** (`not_isIrreducible_of_charFrob_eq`, sorry
  node): a continuous mod-`ℓ` representation whose Frobenius characteristic
  polynomials away from `{2, 3, ℓ}` are those of `1 ⊕ χ̄` is not
  irreducible: the Frobenii are dense (Chebotarev), so all characteristic
  polynomials agree with those of `1 ⊕ χ̄`, and Brauer–Nesbitt forces the
  semisimplification to be `1 ⊕ χ̄`, which is reducible.

Given these, B5 is proven in `Reducible.lean`.
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
public import Mathlib.Topology.Instances.ZMod

@[expose] public section

open GaloisRepresentation Polynomial

namespace GaloisRepresentation

/-- The natural `ℤ_ℓ`-algebra structure on `ℤ/ℓℤ`. -/
noncomputable local instance (ℓ : ℕ) [Fact ℓ.Prime] : Algebra ℤ_[ℓ] (ZMod ℓ) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- The standard rank-2 free module `Fin 2 → O` has rank 2. -/
lemma rank_finTwoFun (O : Type*) [CommRing O] [Nontrivial O] :
    Module.rank O (Fin 2 → O) = 2 := by
  simp

variable {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
  {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V]
  [Module.Finite (ZMod ℓ) V] [Module.Free (ZMod ℓ) V]
  (hdim : Module.rank (ZMod ℓ) V = 2)

/-- The data of a hardly ramified `ℓ`-adic lift of a mod-`ℓ` representation
`ρbar`: a coefficient ring `O` (abstractly: the integers of a finite
extension of `ℚ_ℓ` — a compact topological local domain, finite over
`ℤ_ℓ`), a hardly ramified representation `ρ : Gal(ℚ̄/ℚ) → GL₂(O)`, and a
reduction map `π : O →+* ℤ/ℓℤ` matching the characteristic polynomials of
Frobenius of `ρ` with those of `ρbar` at all good primes. -/
structure HardlyRamifiedLift (ρbar : GaloisRep ℚ (ZMod ℓ) V) where
  /-- The coefficient ring of the lift. -/
  O : Type
  [commRing : CommRing O]
  [isDomain : IsDomain O]
  [topologicalSpace : TopologicalSpace O]
  [isTopologicalRing : IsTopologicalRing O]
  [isLocalRing : IsLocalRing O]
  [algebra : Algebra ℤ_[ℓ] O]
  [moduleFinite : Module.Finite ℤ_[ℓ] O]
  /-- The lifted representation, framed by the standard basis. -/
  ρ : FramedGaloisRep ℚ O (Fin 2)
  /-- The lift is hardly ramified. -/
  isHardlyRamified : IsHardlyRamified hℓOdd
    (rank_finTwoFun O) ρ
  /-- The reduction map to the residue characteristic-`ℓ` world. -/
  π : O →+* ZMod ℓ
  /-- The lift reduces to `ρbar`: the characteristic polynomials of
  Frobenius match at every prime `q ∉ {2, ℓ}`. -/
  charFrob_compat : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ ℓ →
    (ρ.charFrob hq.toHeightOneSpectrumRingOfIntegersRat).map π =
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat

set_option warn.sorry false in
/-- **B6a** (sorry node): an irreducible hardly ramified mod-`ℓ`
representation with `ℓ ≥ 5` admits a hardly ramified `ℓ`-adic lift.

This is a modularity-lifting-style deformation-theoretic statement with no
residual modularity hypothesis (the hypothesis is replaced by "the residual
representation is valued in `GL₂(ℤ/ℓℤ)`"). -/
theorem exists_hardlyRamifiedLift (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ (ZMod ℓ) V} (h : IsHardlyRamified hℓOdd hdim ρbar)
    (hirr : ρbar.IsIrreducible) :
    Nonempty (HardlyRamifiedLift hℓOdd ρbar) :=
  sorry

set_option warn.sorry false in
/-- **B6b + B6c** (sorry node, to be split by a later layer): the residual
characteristic polynomials of Frobenius of a liftable hardly ramified
representation are those of `1 ⊕ χ̄`, i.e. `X² − (q+1)X + q` at `Frob_q`.

Route: the `ℓ`-adic lift spreads out into a weakly compatible family of
hardly ramified `p`-adic representations over the completions of a number
field (B6b); the `3`-adic member is an extension of the trivial character
by the cyclotomic character (B6c), so its Frobenius traces at `q ∉ {2,3}`
are `q + 1`; by compatibility the same holds for the `ℓ`-adic member and
hence residually. -/
theorem residual_charFrob_eq (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ (ZMod ℓ) V} (L : HardlyRamifiedLift hℓOdd ρbar) :
    ∀ q (hq : q.Prime), q ≠ 2 → q ≠ 3 → q ≠ ℓ →
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        X ^ 2 - C ((q : ZMod ℓ) + 1) * X + C (q : ZMod ℓ) :=
  sorry

set_option warn.sorry false in
/-- **Chebotarev + Brauer–Nesbitt** (sorry node): a continuous mod-`ℓ`
representation of `Gal(ℚ̄/ℚ)` whose characteristic polynomials of Frobenius
away from `{2, 3, ℓ}` are those of `1 ⊕ χ̄` is not irreducible. -/
theorem not_isIrreducible_of_charFrob_eq
    {ρbar : GaloisRep ℚ (ZMod ℓ) V}
    (h : ∀ q (hq : q.Prime), q ≠ 2 → q ≠ 3 → q ≠ ℓ →
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        X ^ 2 - C ((q : ZMod ℓ) + 1) * X + C (q : ZMod ℓ)) :
    ¬ ρbar.IsIrreducible :=
  sorry

end GaloisRepresentation
