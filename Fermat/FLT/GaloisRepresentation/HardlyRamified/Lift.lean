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
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Family
public import Mathlib.Topology.Instances.ZMod
-- Chebotarev density, the mod-ℓ cyclotomic character, Brauer–Nesbitt and
-- the bridge lemmas, used in the proof of `not_isIrreducible_of_charFrob_eq`.
import Fermat.FLT.GaloisRepresentation.Chebotarev
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Threeadic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange

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
  -- The topology is the `ℤ_ℓ`-module topology (true for the integers of a
  -- finite extension of `ℚ_ℓ`; added so the lift can be fed to the
  -- compatible-family layer `Family.lean`, whose statements require it).
  [isModuleTopology : IsModuleTopology ℤ_[ℓ] O]
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

set_option backward.isDefEq.respectTransparency false in
/-- Any number field embeds into the algebraic closure of `ℚ_p` — the
coefficient field of a compatible family can be evaluated at every prime
(an ingredient of the proof of `residual_charFrob_eq_of_family`, where
the `3`-adic member of the family is extracted). The target is an
algebraically closed field of characteristic zero, so `IsAlgClosed.lift`
applies to the algebraic extension `E/ℚ`. -/
lemma nonempty_ringHom_to_padicAlgClosure
    (E : Type*) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] :
    Nonempty (E →+* AlgebraicClosure ℚ_[p]) := by
  haveI : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := E)
    (M := AlgebraicClosure ℚ_[p])).toRingHom⟩

set_option backward.isDefEq.respectTransparency false in
open scoped TensorProduct in
/-- Characteristic-polynomial transport through base change and framing:
the family-membership equation `(τ.baseChange B).conj e = σ_φ` identifies
the characteristic polynomials of the family member with the images of
those of `τ` under the coefficient map. (Ingredient of the proof of
`residual_charFrob_eq_of_family`.) -/
lemma charpoly_baseChange_conj {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    {W : Type*} [AddCommGroup W] [Module A W] [Module.Finite A W]
    [Module.Free A W] {N : Type*} [AddCommGroup N] [Module B N]
    [Module.Finite B N] [Module.Free B N]
    (τ : GaloisRep ℚ A W) (e : (B ⊗[A] W) ≃ₗ[B] N)
    (g : Field.absoluteGaloisGroup ℚ) :
    (((τ.baseChange B).conj e) g).charpoly =
      ((τ g).charpoly).map (algebraMap A B) := by
  rw [GaloisRep.conj_apply, LinearEquiv.charpoly_conj]
  show ((Module.End.baseChangeHom A B W) (τ g)).charpoly = _
  rw [show (Module.End.baseChangeHom A B W) (τ g) =
    LinearMap.baseChange B (τ g) from rfl, LinearMap.charpoly_baseChange]

set_option warn.sorry false in
/-- **Compatibility bookkeeping** (sorry node): if the hardly ramified
`ℓ`-adic lift of `ρbar` lives in a compatible family of hardly ramified
representations, then the residual characteristic polynomials of Frobenius
of `ρbar` at `q ∉ {2, 3, ℓ}` are those of `1 ⊕ χ̄`, i.e.
`X² − (q+1)X + q` at `Frob_q`.

The eventual proof is bookkeeping around **B6c**
(`IsHardlyRamified.three_adic`, `Threeadic.lean`): the family's `3`-adic
member is hardly ramified, so by B6c its Frobenius traces at primes
`q ≥ 5` are `1 + q`; its Frobenius determinants are `q` (cyclotomic
determinant, part of `IsHardlyRamified`); compatibility transports the
resulting characteristic polynomial `X² − (q+1)X + q` from the `3`-adic
member to the `ℓ`-adic member, and the lift's `charFrob_compat` reduces it
to `ρbar`. No arithmetic-geometric content remains in this node — only
linear-algebra and base-change bookkeeping.

AUDIT RESTATEMENT (2026-07-16): the conclusion allows a finite
exceptional set `S` of places — the compatibility of the family
(`GaloisRepFamily.isCompatible`) only pins the characteristic
polynomials outside an unspecified finite set of places, so the former
`∀ q ∉ {2,3,ℓ}` form was unprovable from the stated hypotheses. The
downstream Chebotarev–Brauer–Nesbitt argument is insensitive to any
finite exceptional set. -/
theorem residual_charFrob_eq_of_family (_hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ (ZMod ℓ) V} (L : HardlyRamifiedLift hℓOdd ρbar)
    (hfam :
      letI := L.commRing; letI := L.isDomain; letI := L.topologicalSpace
      letI := L.isTopologicalRing; letI := L.isLocalRing; letI := L.algebra
      letI := L.moduleFinite; letI := L.isModuleTopology
      IsHardlyRamified.IsInHardlyRamifiedFamily (p := ℓ) L.ρ) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ℚ)),
      ∀ q (hq : q.Prime),
        Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S → q ≠ ℓ →
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
          X ^ 2 - C ((q : ZMod ℓ) + 1) * X + C (q : ZMod ℓ) := by
  classical
  letI := L.commRing; letI := L.isDomain; letI := L.topologicalSpace
  letI := L.isTopologicalRing; letI := L.isLocalRing; letI := L.algebra
  letI := L.moduleFinite; letI := L.isModuleTopology
  obtain ⟨E, iF, iNF, σ, ⟨S₀, Pv, hPv⟩, hodd, iAlgR, iCSR, hinjR, ψ, r', hψ⟩ :=
    hfam
  letI := iF; letI := iNF; letI := iAlgR; letI := iCSR
  haveI h3fact : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨φ₃⟩ := nonempty_ringHom_to_padicAlgClosure E 3
  obtain ⟨A, iA1, iA2, iA3, iA4, iA5, iA6, iA7, iA8, iA9, iA10, iA11, iA12,
      hinjA, W, iW1, iW2, iW3, iW4, hW, τ, r, hτHR, hτeq⟩ :=
    hodd h3fact (by decide) φ₃
  letI := iA1; letI := iA2; letI := iA3; letI := iA4; letI := iA5
  letI := iA6; letI := iA7; letI := iA8; letI := iA9; letI := iA10
  letI := iA11; letI := iA12
  letI := iW1; letI := iW2; letI := iW3; letI := iW4
  refine ⟨insert Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat
    (insert Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat S₀), ?_⟩
  intro q hq hqS hqℓ
  -- unpack the exceptional-set membership
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hqS (Finset.mem_insert.mpr (Or.inl rfl))
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact hqS (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inl rfl))))
  have hqS₀ : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S₀ :=
    fun hmem => hqS (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem))
  have hq5 : 5 ≤ q := by
    have h2 := hq.two_le
    rcases Nat.lt_or_ge q 5 with h5 | h5
    · interval_cases q
      · omega
      · omega
      · exact absurd hq (by decide)
    · exact h5
  -- side conditions: the place has residue characteristic ≠ 3 and ≠ ℓ
  have hside3 : ((3 : ℕ) : NumberField.RingOfIntegers ℚ) ∉
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq).asIdeal := by
    rw [natCast_mem_toHeightOneSpectrum_iff (by decide) hq]
    omega
  have hsideℓ : ((ℓ : ℕ) : NumberField.RingOfIntegers ℚ) ∉
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq).asIdeal := by
    rw [natCast_mem_toHeightOneSpectrum_iff (Fact.out : ℓ.Prime) hq]
    exact fun h => hqℓ h.symm
  obtain ⟨-, hcomp3⟩ := hPv (p := 3) h3fact φ₃
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) hqS₀ hside3
  obtain ⟨-, hcompℓ⟩ := hPv (p := ℓ) ‹Fact ℓ.Prime› ψ
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) hqS₀ hsideℓ
  -- the 3-adic member's characteristic polynomial at Frobenius
  haveI : Nontrivial A := inferInstance
  have hτcp : (τ (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly =
      X ^ 2 - C ((q : A) + 1) * X + C (q : A) := by
    have hfin : Module.finrank A W = 2 := by
      unfold Module.finrank
      rw [hW]
      simp
    have hrec := charpoly_eq_quadratic_of_finrank_two (F := A) (V := W) hfin
      (τ (globalFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)))
    have htrace := IsHardlyRamified.three_adic W hW hτHR q hq hq5
    have hdet0 := hτHR.det (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))
    rw [cyclotomicCharacter_globalFrob (ℓ := 3) hq hq3, map_natCast] at hdet0
    have hdet1 : LinearMap.det (τ (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) = (q : A) :=
      hdet0
    have htrace1 : LinearMap.trace A W (τ (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) = 1 + (q : A) :=
      htrace
    rw [hrec, hdet1, htrace1, add_comm (1 : A) (q : A)]
  -- transport to the family member over `ℚ̄₃` and descend to `E`
  have h3top : ((σ h3fact φ₃) (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly =
      ((τ (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly).map
        (algebraMap A (AlgebraicClosure ℚ_[3])) := by
    rw [← hτeq]
    exact charpoly_baseChange_conj τ r _
  have hPvq : Pv (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) =
      X ^ 2 - C ((q : E) + 1) * X + C (q : E) := by
    apply Polynomial.map_injective φ₃ φ₃.injective
    rw [← hcomp3]
    show ((σ h3fact φ₃) (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly = _
    rw [h3top, hτcp]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, map_natCast,
      map_add, map_one]
  -- transport the `ℓ`-adic member and descend to the lift's coefficients
  have hℓtop : ((σ ‹Fact ℓ.Prime› ψ) (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly =
      ((L.ρ (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly).map
        (algebraMap L.O (AlgebraicClosure ℚ_[ℓ])) := by
    rw [← hψ]
    exact charpoly_baseChange_conj L.ρ r' _
  have hOcp : (L.ρ (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly =
      X ^ 2 - C ((q : L.O) + 1) * X + C (q : L.O) := by
    apply Polynomial.map_injective (algebraMap L.O (AlgebraicClosure ℚ_[ℓ]))
      hinjR
    rw [← hℓtop]
    show ((σ ‹Fact ℓ.Prime› ψ) (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly = _
    rw [show ((σ ‹Fact ℓ.Prime› ψ) (globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly =
        ((σ ‹Fact ℓ.Prime› ψ).toLocal
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)
          (Field.AbsoluteGaloisGroup.adicArithFrob
            (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly
        from rfl, hcompℓ, hPvq]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, map_natCast,
      map_add, map_one]
  -- reduce through the lift's compatibility
  have hred := L.charFrob_compat q hq hq2 hqℓ
  rw [show L.ρ.charFrob (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) =
    (L.ρ (globalFrob
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly
    from rfl, hOcp] at hred
  rw [← hred]
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, map_natCast,
    map_add, map_one]

/-- **B6b + B6c**: the residual characteristic polynomials of Frobenius of
a liftable hardly ramified representation are those of `1 ⊕ χ̄`, i.e.
`X² − (q+1)X + q` at `Frob_q`. Derived from **B6b**
(`IsHardlyRamified.mem_isCompatible`, `Family.lean`: the lift spreads out
into a compatible family of hardly ramified representations) and the
compatibility bookkeeping node above (which consumes **B6c**,
`IsHardlyRamified.three_adic`). -/
theorem residual_charFrob_eq (hℓ5 : 5 ≤ ℓ)
    {ρbar : GaloisRep ℚ (ZMod ℓ) V} (L : HardlyRamifiedLift hℓOdd ρbar) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ℚ)),
      ∀ q (hq : q.Prime),
        Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S → q ≠ ℓ →
        ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
          X ^ 2 - C ((q : ZMod ℓ) + 1) * X + C (q : ZMod ℓ) :=
  residual_charFrob_eq_of_family hℓOdd hℓ5 L
    (letI := L.commRing; letI := L.isDomain; letI := L.topologicalSpace
     letI := L.isTopologicalRing; letI := L.isLocalRing; letI := L.algebra
     letI := L.moduleFinite; letI := L.isModuleTopology
     IsHardlyRamified.mem_isCompatible hℓOdd (rank_finTwoFun L.O)
       L.isHardlyRamified)

set_option backward.isDefEq.respectTransparency false in
/-- **Chebotarev + Brauer–Nesbitt**: a continuous mod-`ℓ` representation
of `Gal(ℚ̄/ℚ)` whose characteristic polynomials of Frobenius away from
`{2, 3, ℓ}` are those of `1 ⊕ χ̄` is not irreducible.

DERIVED from the Chebotarev density node
(`dense_conjClasses_globalFrob`), the Brauer–Nesbitt node
(`not_isIrreducible_of_charpoly_eq`), the Frobenius value of the mod-`ℓ`
cyclotomic character (`cyclotomicCharacterModL_globalFrob`), and the
proven continuity/bridge lemmas of `Chebotarev.lean`: the set of `g` where
the characteristic polynomial of `ρbar g` agrees with that of `1 ⊕ χ̄` is
closed (both coefficient functions are continuous into the discrete
`ZMod ℓ` — the module topology on `End` is discrete) and contains the
dense set of Frobenius conjugates, hence is everything. -/
theorem not_isIrreducible_of_charFrob_eq
    {ρbar : GaloisRep ℚ (ZMod ℓ) V}
    (S : Finset (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ)))
    (h : ∀ q (hq : q.Prime),
      Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S → q ≠ ℓ →
      ρbar.charFrob hq.toHeightOneSpectrumRingOfIntegersRat =
        X ^ 2 - C ((q : ZMod ℓ) + 1) * X + C (q : ZMod ℓ)) :
    ¬ ρbar.IsIrreducible := by
  classical
  -- an auxiliary prime avoiding the exceptional places pins the rank at 2:
  -- distinct primes give distinct places, so a finite set of places
  -- excludes only finitely many primes
  obtain ⟨q₀, hq₀p, hq₀S, hq₀ℓ⟩ :
      ∃ q₀ : ℕ, ∃ hq₀ : q₀.Prime,
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀ ∉ S) ∧ q₀ ≠ ℓ := by
    set T : Finset ℕ := (insert
        ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat)
        S).attach.image
      (fun v => (exists_prime_toHeightOneSpectrum v.1).choose) with hT
    obtain ⟨q₀, hq₀ge, hq₀p⟩ := Nat.exists_infinite_primes (T.sup id + 1)
    have hq₀T : q₀ ∉ T := by
      intro hmem
      have := Finset.le_sup (f := id) hmem
      simp only [id] at this
      omega
    have hq₀S' : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p ∉
        insert ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat)
          S := by
      intro hmem
      apply hq₀T
      obtain ⟨hcp, hceq⟩ := (exists_prime_toHeightOneSpectrum
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p)).choose_spec
      have hch : (exists_prime_toHeightOneSpectrum
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq₀p)).choose = q₀ :=
        toHeightOneSpectrumRingOfIntegersRat_injective hcp hq₀p hceq.symm
      rw [hT]
      exact Finset.mem_image.mpr ⟨⟨_, hmem⟩, Finset.mem_attach _ _, hch⟩
    refine ⟨q₀, hq₀p, fun hmem => hq₀S' (Finset.mem_insert_of_mem hmem), ?_⟩
    rintro rfl
    exact hq₀S' (Finset.mem_insert.mpr (Or.inl rfl))
  have hfr : Module.finrank (ZMod ℓ) V = 2 := by
    have h0 := congrArg Polynomial.natDegree (h q₀ hq₀p hq₀S hq₀ℓ)
    rwa [GaloisRep.charFrob_eq_charpoly_globalFrob,
      LinearMap.charpoly_natDegree, natDegree_comparisonQuadratic] at h0
  have hrank : Module.rank (ZMod ℓ) V = 2 := by
    rw [← Module.finrank_eq_rank (ZMod ℓ) V, hfr]
    norm_num
  -- the endomorphism space is discrete in its module topology
  letI : TopologicalSpace (Module.End (ZMod ℓ) V) :=
    moduleTopology (ZMod ℓ) (Module.End (ZMod ℓ) V)
  haveI : DiscreteTopology (Module.End (ZMod ℓ) V) :=
    discreteTopology_moduleTopology _ _
  have hρcont : Continuous fun g : Field.absoluteGaloisGroup ℚ => ρbar g :=
    ContinuousMonoidHom.continuous_toFun ρbar
  -- the agreement set is closed …
  have hχcont := continuous_cyclotomicCharacterModL ℓ
  have hc1 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      (ρbar g).charpoly.coeff 1 := by
    exact Continuous.comp (continuous_of_discreteTopology
      (f := fun φ : Module.End (ZMod ℓ) V => φ.charpoly.coeff 1)) hρcont
  have hc0 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      (ρbar g).charpoly.coeff 0 := by
    exact Continuous.comp (continuous_of_discreteTopology
      (f := fun φ : Module.End (ZMod ℓ) V => φ.charpoly.coeff 0)) hρcont
  have hb1 : Continuous fun g : Field.absoluteGaloisGroup ℚ =>
      -(((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) := by
    exact Continuous.comp (g := fun x : ZMod ℓ => -(x + 1))
      continuous_of_discreteTopology hχcont
  have hDclosed : IsClosed {g : Field.absoluteGaloisGroup ℚ |
      (ρbar g).charpoly.coeff 1 =
        -(((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
      (ρbar g).charpoly.coeff 0 =
        ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)} := by
    rw [Set.setOf_and]
    exact (isClosed_eq hc1 hb1).inter (isClosed_eq hc0 hχcont)
  -- … and contains the dense set of Frobenius conjugates
  have hsub : {x : Field.absoluteGaloisGroup ℚ |
      ∃ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        v ∉ insert
          ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat) S ∧
        ∃ g, x = g * globalFrob v * g⁻¹} ⊆
      {g : Field.absoluteGaloisGroup ℚ |
        (ρbar g).charpoly.coeff 1 =
          -(((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
        (ρbar g).charpoly.coeff 0 =
          ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ)} := by
    rintro x ⟨v, hvS, g, rfl⟩
    obtain ⟨q, hq, rfl⟩ := exists_prime_toHeightOneSpectrum v
    have hqS : Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq ∉ S :=
      fun hmem => hvS (Finset.mem_insert_of_mem hmem)
    have hqℓ : q ≠ ℓ := by
      rintro rfl
      exact hvS (Finset.mem_insert.mpr (Or.inl rfl))
    -- conjugation invariance of the characteristic polynomial
    have hgu : (ρbar g).comp (ρbar g⁻¹) = LinearMap.id := by
      have : ρbar g * ρbar g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      exact this
    have hgu' : (ρbar g⁻¹).comp (ρbar g) = LinearMap.id := by
      have : ρbar g⁻¹ * ρbar g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      exact this
    have hconj : (ρbar (g * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹)).charpoly =
        (ρbar (globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))).charpoly := by
      have heq : ρbar (g * globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹) =
          (LinearEquiv.ofLinear (ρbar g) (ρbar g⁻¹) hgu hgu').conj
            (ρbar (globalFrob
              (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq))) := by
        ext x
        simp [map_mul, LinearEquiv.conj_apply, Module.End.mul_apply]
      rw [heq, LinearEquiv.charpoly_conj]
    -- conjugation invariance of the cyclotomic character
    have hχconj : cyclotomicCharacterModL ℓ (g * globalFrob
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq) * g⁻¹) =
        cyclotomicCharacterModL ℓ (globalFrob
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat hq)) := by
      rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
    have hval := h q hq hqS hqℓ
    rw [GaloisRep.charFrob_eq_charpoly_globalFrob] at hval
    have hfrob := cyclotomicCharacterModL_globalFrob (ℓ := ℓ) hq hqℓ
    constructor
    · show (ρbar _).charpoly.coeff 1 = _
      rw [hconj, hval, coeff_one_comparisonQuadratic, hχconj, hfrob]
    · show (ρbar _).charpoly.coeff 0 = _
      rw [hconj, hval, coeff_zero_comparisonQuadratic, hχconj, hfrob]
  -- density: the agreement set is everything
  have hDall : ∀ g : Field.absoluteGaloisGroup ℚ,
      (ρbar g).charpoly.coeff 1 =
        -(((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) + 1) ∧
      (ρbar g).charpoly.coeff 0 =
        ((cyclotomicCharacterModL ℓ g : (ZMod ℓ)ˣ) : ZMod ℓ) := by
    intro g
    have hdense := dense_conjClasses_globalFrob (K := ℚ)
      (insert ((Fact.out : ℓ.Prime).toHeightOneSpectrumRingOfIntegersRat) S)
    have : (Set.univ : Set (Field.absoluteGaloisGroup ℚ)) ⊆ _ :=
      hdense.closure_eq ▸ hDclosed.closure_subset_iff.mpr hsub
    exact this (Set.mem_univ g)
  -- reconstruct the polynomial identity and conclude by Brauer–Nesbitt
  apply not_isIrreducible_of_charpoly_eq hrank ρbar
  intro g
  obtain ⟨h1, h0⟩ := hDall g
  refine monic_quadratic_ext (LinearMap.charpoly_monic _)
    (monic_comparisonQuadratic _) ?_ (natDegree_comparisonQuadratic _) ?_ ?_
  · rw [LinearMap.charpoly_natDegree, hfr]
  · rw [h1, coeff_one_comparisonQuadratic]
  · rw [h0, coeff_zero_comparisonQuadratic]

end GaloisRepresentation
