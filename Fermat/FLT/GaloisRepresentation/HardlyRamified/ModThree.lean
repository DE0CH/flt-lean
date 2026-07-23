/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
-- The PROVEN character bookkeeping (stable-line characters, kernel
-- openness, the Minkowski triviality, the generic unramifiedness
-- bridge) used by the derivation of `mod_three_of_stable_line`.
public import Fermat.FLT.FreyCurve.MazurTorsion
-- Irreducible ↔ absolutely irreducible given a 1-dimensional fixed space
-- (complex conjugation), used by the derivation of `mod_three_reducible`.
public import Fermat.FLT.KnownIn1980s.RepresentationTheory.OddAbsIrred
-- `ℂ` is an algebraic closure of `ℝ` (for the complex-conjugation
-- involution in `exists_conj_cyclotomicCharacter_three`)
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Instances.Complex
-- Dickson's classification of the finite subgroups of PGL₂(𝔽̄₃)
-- (vendored PROVEN), consumed by `not_isAbsolutelyIrreducible`.
public import Fermat.FLT.KnownIn1980s.PGL2.Defs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
-- The number-field vocabulary (`NumberField.discr`,
-- `NumberField.IsTotallyComplex`) of the root-discriminant skeleton
-- for the exceptional Serre-elimination cases.
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
-- `differentIdeal` and `NumberField.not_dvd_discr_iff_forall_mem`
-- (a prime not dividing the discriminant ⇔ unramified above it), for
-- the discriminant leaves of the kernel field.
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
-- `Ideal.card_inertia_eq_ramificationIdxIn` and the `ramificationIdxIn`
-- dictionary, for the inertia-to-ramification-index conversion in the
-- tame-at-`2` discriminant exponent glue.
public import Mathlib.NumberTheory.RamificationInertia.Galois
-- `Ideal.ramificationIdx'_eq_ramificationIdx`, same conversion.
public import Mathlib.RingTheory.RamificationInertia.Ramification
-- Analytic vocabulary of the Poitou–Odlyzko root-discriminant
-- decomposition (`odlyzko_rootDiscr_totallyComplex`): the
-- Euler–Mascheroni constant, `Real.sinh`, and the Bochner set
-- integral against Lebesgue measure appear in the leaf STATEMENTS
-- (hence public); the numeric bounds on `π`/`exp` and the elementary
-- interval-integral computations are proof-only.
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
-- Phragmén–Lindelöf on the vertical strip, for the interior positivity
-- of `Re Φ` in the Poitou explicit-formula decomposition (proof-only).
import Mathlib.Analysis.Complex.PhragmenLindelof
-- `LinearMap.trace`, for the trace-zero interface of the dihedral case.
public import Mathlib.LinearAlgebra.Trace
-- The vendored Dickson `SL₂`/`PSL₂` toolkit (elementary generation,
-- centre and cardinality computations, the index-two membership lemma),
-- consumed by the proofs of the group-theoretic degree bound
-- `card_matrixRange_ge_of_exceptional` below.
import Fermat.FLT.Slop.PGL2.FiniteSubgroups.PSLBasic
-- `PadicInt.zmodRepr`, for the ±1 evaluation of the mod-3 cyclotomic
-- determinant on the matrix image.
import Mathlib.NumberTheory.Padics.RingHoms
-- `LinearMap.det_baseChange`, for the determinant of the base-changed
-- representation.
import Mathlib.LinearAlgebra.Charpoly.BaseChange
-- `Set.ncard_pair`, for the two-element determinant image.
import Mathlib.Data.Set.Card
-- `Ideal.sum_ramification_inertia` (the fundamental identity
-- `Σ e·f = [K:ℚ]`), `Ideal.absNorm_eq_pow_inertiaDeg'` and the
-- `normalizedFactors` bookkeeping, for the discriminant-exponent
-- norm accounting of the kernel field.
import Mathlib.NumberTheory.RamificationInertia.Basic
-- `Algebra.FormallyEtale.of_isSeparable`, for the Cohen-style
-- multiplicative section in the tame different bound.
import Mathlib.RingTheory.Etale.Field
-- `Polynomial.irreducible_of_degree_le_three_of_not_isRoot`, for the
-- irreducibility of `X² + X + 1` over `ℚ₃ᵥ` in the finite-level
-- inertia leaf.
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Mod-3 hardly ramified representations

A mod-3 hardly ramified representation is shown to be an extension of
the trivial character by the mod-3 cyclotomic character.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

open scoped TensorProduct MatrixGroups

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

universe u

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
open Field in
/-- **Complex conjugation and the 3-adic cyclotomic character** (DERIVED
2026-07-18 — the oddness input): the absolute Galois group of `ℚ`
contains an involution on which the 3-adic cyclotomic character takes
the value `-1`. Construction: `ℝᵃˡᵍ ≃ₐ[ℝ] ℂ`, so `Γ ℝ` has exactly two
elements (Galois, degree `2`); the image `c` of the nontrivial one
under `Γ ℝ → Γ ℚ` is an involution, so `χ₃(c)² = 1`, i.e. `χ₃(c) = ±1`
in the domain `ℤ_[3]`; and `χ₃(c) = 1` would force `c` to fix a
primitive cube root of unity `ζ`, hence the nontrivial element of `Γ ℝ`
to fix `ι ζ ∉ ℝ` — but `ℝ(ι ζ) = ℝᵃˡᵍ` in degree `2`, so that element
would be the identity. -/
theorem exists_conj_cyclotomicCharacter_three :
    ∃ c : Γ ℚ, c * c = 1 ∧
      ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 c.toRingEquiv :
        ℤ_[3]ˣ) : ℤ_[3]) = -1 := by
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  classical
  -- `ℝᵃˡᵍ ≃ₐ[ℝ] ℂ`, hence `Γ ℝ` has exactly two elements
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, Algebra.IsAlgebraic.of_finite ℝ ℂ⟩
  let e : AlgebraicClosure ℝ ≃ₐ[ℝ] ℂ :=
    IsAlgClosure.equiv ℝ (AlgebraicClosure ℝ) ℂ
  haveI : FiniteDimensional ℝ (AlgebraicClosure ℝ) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have hfr : Module.finrank ℝ (AlgebraicClosure ℝ) = 2 := by
    rw [e.toLinearEquiv.finrank_eq]
    exact Complex.finrank_real_complex
  haveI : IsGalois ℝ (AlgebraicClosure ℝ) := ⟨⟩
  have hcard : Nat.card (Γ ℝ) = 2 :=
    (IsGalois.card_aut_eq_finrank ℝ (AlgebraicClosure ℝ)).trans hfr
  -- the nontrivial element of `Γ ℝ`
  haveI : Finite (Γ ℝ) := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial (Γ ℝ) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : Γ ℝ)
  have hσ2 : σ * σ = 1 := by
    have h : σ ^ Nat.card (Γ ℝ) = 1 := pow_card_eq_one'
    rwa [hcard, pow_two] at h
  -- its image in `Γ ℚ` is the sought involution
  refine ⟨absoluteGaloisGroup.map (algebraMap ℚ ℝ) σ, ?_, ?_⟩
  · rw [← map_mul, hσ2, map_one]
  · set c : Γ ℚ := absoluteGaloisGroup.map (algebraMap ℚ ℝ) σ
    set x : ℤ_[3] :=
      ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 c.toRingEquiv :
        ℤ_[3]ˣ) : ℤ_[3])
    -- `x² = 1`, so `x = ±1` in the domain `ℤ_[3]`
    have hsq : x * x = 1 := by
      have hmul : (c * c).toRingEquiv = c.toRingEquiv * c.toRingEquiv := rfl
      have hone : ((1 : Γ ℚ).toRingEquiv) = 1 := rfl
      have h := congrArg (fun g => ((cyclotomicCharacter
        (AlgebraicClosure ℚ) 3 g : ℤ_[3]ˣ) : ℤ_[3]))
        (hmul.symm.trans (by rw [← map_mul, hσ2, map_one, hone] : _ = _))
      simpa [map_mul] using h
    rcases mul_self_eq_one_iff.mp hsq with hx1 | hxm1
    swap
    · exact hxm1
    -- rule out `x = 1`: `c` would fix a primitive cube root of unity
    exfalso
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure ℚ) 3
    -- `c ζ = ζ ^ (x mod 3) = ζ`
    have hfix : c.toRingEquiv ζ = ζ := by
      have hspec := cyclotomicCharacter.spec 3 (n := 1) c.toRingEquiv ζ
        (by rw [pow_one]; exact hζ.pow_eq_one)
      rw [hspec, show (cyclotomicCharacter (AlgebraicClosure ℚ) 3
        c.toRingEquiv).val = x from rfl, hx1, map_one]
      rw [show ((1 : ZMod (3 ^ 1)).val) = 1 from rfl, pow_one]
    -- transport along the embedding `ι : ℚᵃˡᵍ → ℝᵃˡᵍ`
    have hσz : σ (AlgebraicClosure.map (algebraMap ℚ ℝ) ζ) =
        AlgebraicClosure.map (algebraMap ℚ ℝ) ζ := by
      rw [← absoluteGaloisGroup.lift_map (algebraMap ℚ ℝ) σ ζ]
      exact congrArg _ hfix
    set z : AlgebraicClosure ℝ := AlgebraicClosure.map (algebraMap ℚ ℝ) ζ
    -- `z` is a primitive cube root of unity, hence not real
    have hzprim : IsPrimitiveRoot z 3 :=
      hζ.map_of_injective (AlgebraicClosure.map (algebraMap ℚ ℝ)).injective
    have hznotbot : z ∉ (⊥ : IntermediateField ℝ (AlgebraicClosure ℝ)) := by
      intro hmem
      obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hmem
      -- `r³ = 1` in `ℝ` forces `r = 1`, forcing `z = 1`
      have hr3 : r ^ 3 = 1 := by
        have h := hzprim.pow_eq_one
        rw [← hr] at h
        exact (algebraMap ℝ (AlgebraicClosure ℝ)).injective
          (by rw [map_pow, map_one]; exact h)
      have hr1 : r = 1 := by nlinarith [sq_nonneg (r - 1), sq_nonneg (r + 1)]
      exact hzprim.ne_one (by norm_num) (by rw [← hr, hr1, map_one])
    -- `ℝ(z) = ℝᵃˡᵍ` in degree `2`
    have htop : IntermediateField.adjoin ℝ {z} = ⊤ := by
      rw [← IntermediateField.finrank_eq_one_iff_eq_top]
      have hmul : Module.finrank ℝ (IntermediateField.adjoin ℝ {z}) *
          Module.finrank (IntermediateField.adjoin ℝ {z})
            (AlgebraicClosure ℝ) = 2 := by
        rw [Module.finrank_mul_finrank]
        exact hfr
      have hne1 : Module.finrank ℝ (IntermediateField.adjoin ℝ {z}) ≠ 1 := by
        rw [Ne, IntermediateField.finrank_eq_one_iff]
        intro hbot
        exact hznotbot (hbot ▸ IntermediateField.mem_adjoin_simple_self ℝ z)
      have hdvd : Module.finrank ℝ (IntermediateField.adjoin ℝ {z}) ∣ 2 :=
        ⟨_, hmul.symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd h1 hne1
      · rw [h2] at hmul
        omega
    -- `σ` fixes `ℝ` and `z`, hence everything — contradicting `σ ≠ 1`
    refine hσ (AlgEquiv.ext fun w => ?_)
    have hw : w ∈ IntermediateField.adjoin ℝ {z} :=
      htop ▸ IntermediateField.mem_top
    show σ w = w
    induction hw using IntermediateField.adjoin_induction with
    | mem u hu =>
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact hσz
    | algebraMap r => exact σ.commutes r
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    | inv a _ ha => rw [map_inv₀, ha]

/-- A finite field admitting a `ℤ_[3]`-algebra structure has `3 = 0`:
the image of `3` under `ℤ_[3] → k` is not a unit (else the composite
would embed a characteristic-`p ≠ 3` situation into `ℤ_[3]ˣ`), and in a
field every nonzero element is a unit. Precisely: `k` has prime
characteristic `p`; if `p ≠ 3` then `(p : ℤ_[3])` is a unit (its
residue mod `3` is nonzero), yet it maps to `(p : k) = 0`, which is not
a unit — contradiction. -/
theorem charP_three_of_finite_padicIntThree_algebra
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k] : CharP k 3 := by
  cases nonempty_fintype k
  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI := hchar
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  rcases eq_or_ne p 3 with rfl | hp3
  · exact hchar
  · exfalso
    -- `(p : ℤ_[3])` is a unit: its norm is not `< 1` since `3 ∤ p`
    have hunit : IsUnit ((p : ℕ) : ℤ_[3]) := by
      by_contra hnu
      have hlt : ‖((p : ℕ) : ℤ_[3])‖ < 1 := PadicInt.not_isUnit_iff.mp hnu
      rw [show ‖((p : ℕ) : ℤ_[3])‖ = ‖((p : ℕ) : ℚ_[3])‖ from by
        rw [PadicInt.norm_def]; norm_cast] at hlt
      have hdvd : (3 : ℕ) ∣ p := Padic.norm_natCast_lt_one_iff.mp hlt
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp hdvd).symm
    -- but it maps to `(p : k) = 0` under the algebra map
    have hzero : algebraMap ℤ_[3] k ((p : ℕ) : ℤ_[3]) = 0 := by
      rw [map_natCast]
      exact CharP.cast_eq_zero k p
    exact (hunit.map (algebraMap ℤ_[3] k)).ne_zero hzero

/-- A finite field admitting a `ℤ_[3]`-algebra structure has `3 = 0`
(the cast form of `charP_three_of_finite_padicIntThree_algebra`). -/
theorem three_eq_zero_of_finite_padicIntThree_algebra
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k] : (3 : k) = 0 :=
  haveI := charP_three_of_finite_padicIntThree_algebra (k := k)
  CharP.cast_eq_zero k 3

/-- **The `1`-eigenspace of an odd involution is a line**: on a
`2`-dimensional space over a field where `2 ≠ 0`, a linear involution
of determinant `-1` has a `1`-dimensional fixed space. The involution
splits the space as `E₁ ⊕ E₋₁` (via `v = 2⁻¹(v + fv) + 2⁻¹(v - fv)`);
`E₁ = ⊤` forces `f = 1` of determinant `1`, `E₋₁ = ⊤` forces `f = -1`
of determinant `(-1)² = 1`, so determinant `-1` leaves only the split
`1 + 1`. -/
theorem finrank_eigenspace_one_of_involution {k : Type u} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (hrank : Module.rank k V = 2) {f : V →ₗ[k] V}
    (hsq : f * f = 1) (hdet : LinearMap.det f = -1) (h2 : (2 : k) ≠ 0) :
    Module.finrank k (Module.End.eigenspace f 1) = 1 := by
  have hfr : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hrank)
  have hff : ∀ v, f (f v) = v := fun v =>
    congrFun (congrArg DFunLike.coe hsq) v
  -- the sum of the eigenspaces is everything:
  -- `v = 2⁻¹ • (v + f v) + 2⁻¹ • (v - f v)`
  have hsup : Module.End.eigenspace f 1 ⊔ Module.End.eigenspace f (-1) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : v + f v ∈ Module.End.eigenspace f 1 := by
      rw [Module.End.mem_eigenspace_iff, one_smul, map_add, hff]
      abel
    have h2' : v - f v ∈ Module.End.eigenspace f (-1) := by
      rw [Module.End.mem_eigenspace_iff, map_sub, hff, neg_smul, one_smul,
        neg_sub]
    have hv : v = (2 : k)⁻¹ • (v + f v) + (2 : k)⁻¹ • (v - f v) := by
      rw [← smul_add]
      have hvv : (v + f v) + (v - f v) = (2 : k) • v := by
        rw [two_smul]; abel
      rw [hvv, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hv]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ h1))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ h2'))
  -- the intersection is trivial: `v = f v = -v` forces `2v = 0`
  have hinf : Module.End.eigenspace f 1 ⊓ Module.End.eigenspace f (-1) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    rw [Module.End.mem_eigenspace_iff, one_smul] at hv1
    rw [Module.End.mem_eigenspace_iff] at hv2
    have h2v : (2 : k) • v = 0 := by
      rw [two_smul]
      nth_rw 1 [← hv1]
      rw [hv2, neg_smul, one_smul]
      abel
    rw [smul_eq_zero] at h2v
    exact Submodule.mem_bot _ |>.mpr (h2v.resolve_left h2)
  -- dimension bookkeeping
  have hdim : Module.finrank k (Module.End.eigenspace f 1) +
      Module.finrank k (Module.End.eigenspace f (-1)) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (Module.End.eigenspace f 1) (Module.End.eigenspace f (-1))
    rw [hsup, hinf, finrank_top, hfr, finrank_bot, add_zero] at h
    exact h.symm
  -- eliminate `E₁ = ⊤` (then `f = 1`, determinant `1`)
  have hone_ne : (-1 : k) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hcase2 : Module.finrank k (Module.End.eigenspace f 1) ≠ 2 := by
    intro htwo
    have htop : Module.End.eigenspace f 1 = ⊤ :=
      Submodule.eq_top_of_finrank_eq (htwo.trans hfr.symm)
    have hfone : f = 1 := by
      ext v
      have hv : v ∈ Module.End.eigenspace f 1 := htop ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff, one_smul] at hv
      simpa using hv
    rw [hfone] at hdet
    rw [show LinearMap.det (1 : V →ₗ[k] V) = 1 from LinearMap.det_id] at hdet
    exact hone_ne hdet.symm
  -- eliminate `E₁ = ⊥` (then `E₋₁ = ⊤`, `f = -1`, determinant `(-1)² = 1`)
  have hcase0 : Module.finrank k (Module.End.eigenspace f 1) ≠ 0 := by
    intro hzero
    have htwo2 : Module.finrank k (Module.End.eigenspace f (-1)) = 2 := by
      omega
    have htop : Module.End.eigenspace f (-1) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (htwo2.trans hfr.symm)
    have hfneg : f = (-1 : k) • (1 : V →ₗ[k] V) := by
      ext v
      have hv : v ∈ Module.End.eigenspace f (-1) := htop ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hv
      simpa using hv
    rw [hfneg, LinearMap.det_smul] at hdet
    rw [show LinearMap.det (1 : V →ₗ[k] V) = 1 from LinearMap.det_id,
      hfr] at hdet
    simp only [neg_one_sq, mul_one] at hdet
    exact hone_ne hdet.symm
  omega

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The Serre elimination, semidirect case** (PROVEN 2026-07-18 —
purely representation-theoretic): the left factor gives a nontrivial
normal exponent-3 subgroup of `π.range`; its `Γ ℚ`-preimage (the kernel
of the right-component character `r`) acts by scalar-times-unipotent
operators (the cube is central hence scalar by irreducibility, a cube
root and the char-3 Frobenius give `(σρ g − μ)² = 0`, with `μ ≠ 0` by
invertibility); either every kernel element is scalar (then the left
factor is trivial in `PGL₂`, contradicting `m ≥ 1`) or some nonscalar
`g₀` has a `1`-dimensional eigenline `W` (rank–nullity) shared by every
nonscalar kernel element (the unipotent parameter is unique, central
commutator scalars are `±1` by determinants, and `−1` is impossible in
characteristic `3` by expanding the two nilpotency relations), so
normality of the kernel makes `W` a `Γ ℚ`-stable line — contradicting
absolute irreducibility. -/
theorem serre_elimination_semidirect {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (_hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    {m t : ℕ} (hm : m ≥ 1)
    (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod 3)))
    (hiso : Nonempty (π.range ≃*
      (Multiplicative (Fin m → ZMod 3)) ⋊[φ] Multiplicative (ZMod t))) :
    False := by
  classical
  obtain ⟨eiso⟩ := hiso
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := AlgebraicClosure k
  set σρ : Representation L (Γ ℚ) (L ⊗[k] V) :=
    Slop.OddRep.baseChange L (MonoidHomClass.toMonoidHom ρ)
  have hirr : σρ.IsIrreducible := habs
  haveI : Module.Finite L (L ⊗[k] V) := Module.Finite.base_change k L V
  have hfr2 : Module.finrank L (L ⊗[k] V) = 2 := by
    rw [Module.finrank_baseChange]
    exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  haveI : Nontrivial (L ⊗[k] V) :=
    Module.nontrivial_of_finrank_pos (R := L) (by omega)
  obtain ⟨hnt, hsub⟩ := (Slop.OddRep.isIrreducible_iff_forall σρ).mp hirr
  -- characteristic `3` in `L` and in the endomorphism ring
  haveI hchark : CharP k 3 := charP_three_of_finite_padicIntThree_algebra
  haveI hcharL : CharP L 3 :=
    charP_of_injective_algebraMap (algebraMap k L).injective 3
  have hEnd_ne : (1 : Module.End L (L ⊗[k] V)) ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : L ⊗[k] V)
    intro h1
    exact hv (by simpa using congrFun (congrArg DFunLike.coe h1) v)
  haveI hcharEnd : CharP (Module.End L (L ⊗[k] V)) 3 := by
    refine charP_of_injective_algebraMap (R := L) ?_ 3
    intro a c hac
    obtain ⟨v, hv⟩ := exists_ne (0 : L ⊗[k] V)
    have h := congrFun (congrArg DFunLike.coe hac) v
    simp only [Module.algebraMap_end_apply] at h
    have h2 : (a - c) • v = 0 := by
      have h3 := sub_smul a c v
      rw [h, sub_self] at h3
      exact h3
    rcases smul_eq_zero.mp h2 with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hv
  -- transport toolkit
  have hmap_inj : ∀ M N : Matrix (Fin 2) (Fin 2) (AlgebraicClosure k),
      M.map e = N.map e → M = N := by
    intro M N h
    ext i j
    exact e.injective (congrFun (congrFun (congrArg Matrix.of.symm h) i) j)
  have hmulM : ∀ gg₁ gg₂ : Γ ℚ, LinearMap.toMatrix b b (σρ gg₁) *
      LinearMap.toMatrix b b (σρ gg₂) =
      LinearMap.toMatrix b b (σρ gg₁ * σρ gg₂) :=
    fun gg₁ gg₂ => (LinearMap.toMatrix_comp b b b _ _).symm
  -- σρ takes values in units
  have hunit : ∀ g : Γ ℚ, σρ g * σρ g⁻¹ = 1 := by
    intro g
    rw [← map_mul, mul_inv_cancel, map_one]
  -- commuting with the whole action forces a scalar
  have hscalar_of_comm : ∀ T : Module.End L (L ⊗[k] V),
      (∀ h : Γ ℚ, T * σρ h = σρ h * T) → ∃ ν : L, T = ν • 1 := by
    intro T hT
    obtain ⟨ν, hν⟩ := Module.End.exists_eigenvalue T
    have hEinv : ∀ h : Γ ℚ, ∀ w ∈ Module.End.eigenspace T ν,
        σρ h w ∈ Module.End.eigenspace T ν := by
      intro h w hw
      rw [Module.End.mem_eigenspace_iff] at hw ⊢
      have hc := congrFun (congrArg DFunLike.coe (hT h)) w
      simp only [Module.End.mul_apply] at hc
      rw [hc, hw, map_smul]
    rcases hsub (Module.End.eigenspace T ν) hEinv with hE | hE
    · exact absurd hE hν
    · refine ⟨ν, LinearMap.ext fun v => ?_⟩
      have hv : v ∈ Module.End.eigenspace T ν := hE ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hv
      simpa using hv
  -- a `g` whose projective class is trivial acts by a scalar
  have hscalar_of_pi_one : ∀ g : Γ ℚ, π g = 1 → ∃ ν : L, σρ g = ν • 1 := by
    intro g hg
    refine hscalar_of_comm (σρ g) fun h => ?_
    -- the matrix of `g` is central, so it commutes with the matrix of `h`
    have hcen : (u g : GL (Fin 2) (Dickson.K 3)) ∈
        Subgroup.center (GL (Fin 2) (Dickson.K 3)) := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center
        (GL (Fin 2) (Dickson.K 3))), MonoidHom.mem_ker]
      exact ((hπ g).symm.trans hg : _)
    have hcommGL : u g * u h = u h * u g :=
      (Subgroup.mem_center_iff.mp hcen (u h)).symm
    have hval := congrArg Units.val hcommGL
    rw [Units.val_mul, Units.val_mul, hu, hu, ← Matrix.map_mul,
      ← Matrix.map_mul] at hval
    have hmat := hmap_inj _ _ hval
    rw [hmulM, hmulM] at hmat
    exact (LinearMap.toMatrix b b).injective hmat
  -- conversely: a scalar action has trivial projective class
  have hpi_one_of_scalar : ∀ g : Γ ℚ, (∃ ν : L, σρ g = ν • 1) → π g = 1 := by
    rintro g ⟨ν, hν⟩
    have hval : ((u g : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) = e ν • 1 := by
      rw [hu, hν, map_smul, LinearMap.toMatrix_one]
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.map_apply, Matrix.smul_apply, hij]
    have hcen : (u g : GL (Fin 2) (Dickson.K 3)) ∈
        Subgroup.center (GL (Fin 2) (Dickson.K 3)) := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hval]
      rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    rw [hπ g]
    have : QuotientGroup.mk' (Subgroup.center
        (GL (Fin 2) (Dickson.K 3))) (u g) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hcen
    exact this
  -- the kernel of the right component: the `Γ ℚ`-preimage of the
  -- normal elementary abelian `3`-subgroup
  set r : Γ ℚ →* Multiplicative (ZMod t) :=
    (SemidirectProduct.rightHom.comp eiso.toMonoidHom).comp
      π.rangeRestrict
  -- elements of the kernel cube to a central class
  have hcube : ∀ g : Γ ℚ, g ∈ r.ker → (π g) ^ 3 = 1 := by
    intro g hg
    have hy : SemidirectProduct.rightHom (eiso (π.rangeRestrict g)) = 1 := hg
    have hy3 : (eiso (π.rangeRestrict g)) ^ 3 = 1 := by
      have hmem : eiso (π.rangeRestrict g) ∈
          (SemidirectProduct.inl (φ := φ)).range := by
        rw [SemidirectProduct.range_inl_eq_ker_rightHom]
        exact hy
      obtain ⟨n, hn⟩ := hmem
      rw [← hn, ← map_pow]
      have hn3 : n ^ 3 = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        funext i
        show (3 : ℕ) • Multiplicative.toAdd n i = 0
        rw [nsmul_eq_mul,
          show ((3 : ℕ) : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
      rw [hn3, map_one]
    have hx3 : (π.rangeRestrict g) ^ 3 = 1 := by
      apply eiso.injective
      rw [map_pow, hy3, map_one]
    have := congrArg Subtype.val hx3
    simpa using this
  -- kernel elements act by scalar-times-unipotent operators
  have hcube_scalar : ∀ g : Γ ℚ, g ∈ r.ker →
      ∃ ν : L, (σρ g) ^ 3 = ν • 1 := by
    intro g hg
    have hpi3 : π (g ^ 3) = 1 := by rw [map_pow]; exact hcube g hg
    obtain ⟨ν, hν⟩ := hscalar_of_pi_one (g ^ 3) hpi3
    exact ⟨ν, by rw [← map_pow]; exact hν⟩
  -- the unipotent structure: `(σρ g − μ)² = 0` with `μ³ = ν`, `μ ≠ 0`
  have hunip : ∀ g : Γ ℚ, g ∈ r.ker →
      ∃ μ : L, μ ≠ 0 ∧ (σρ g - μ • 1) ^ 2 = 0 := by
    intro g hg
    obtain ⟨ν, hν⟩ := hcube_scalar g hg
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (k := L) ν
      (n := 3) (by norm_num)
    have hcomm : Commute (σρ g) (μ • (1 : Module.End L (L ⊗[k] V))) := by
      unfold Commute SemiconjBy
      rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    have hnil3 : (σρ g - μ • 1) ^ 3 = 0 := by
      have hfrob := sub_pow_char_of_commute (p := 3)
        (x := σρ g) (y := μ • (1 : Module.End L (L ⊗[k] V))) hcomm
      rw [hfrob, hν, smul_pow, one_pow, hμ, sub_self]
    have hnil2 : (σρ g - μ • 1) ^ 2 = 0 := by
      have hnil : IsNilpotent (σρ g - μ • 1) := ⟨3, hnil3⟩
      have hchar := IsNilpotent.charpoly_eq_X_pow_finrank hnil
      have haev := LinearMap.aeval_self_charpoly (σρ g - μ • 1)
      rw [hchar, hfr2] at haev
      simpa using haev
    refine ⟨μ, ?_, hnil2⟩
    -- `μ ≠ 0`: otherwise `σρ g` is nilpotent yet invertible
    intro hμ0
    rw [hμ0] at hμ
    have hν0 : ν = 0 := by rw [← hμ]; ring
    rw [hν0, zero_smul] at hν
    have hcomm' : Commute (σρ g) (σρ g⁻¹) := by
      show σρ g * σρ g⁻¹ = σρ g⁻¹ * σρ g
      rw [← map_mul, ← map_mul, mul_inv_cancel, inv_mul_cancel]
    have h1 : (1 : Module.End L (L ⊗[k] V)) = 0 := by
      have h2 : (σρ g) ^ 3 * (σρ g⁻¹) ^ 3 = 1 := by
        rw [← hcomm'.mul_pow, hunit, one_pow]
      rw [← h2, hν, zero_mul]
    exact hEnd_ne h1
  -- Case split: either every kernel element is scalar, or some is not
  by_cases hallscalar : ∀ g : Γ ℚ, g ∈ r.ker → ∃ ν : L, σρ g = ν • 1
  · -- then the elementary abelian subgroup is trivial in `PGL₂`
    -- pick a nontrivial element of the left factor
    haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
    haveI : Nontrivial (Fin m → ZMod 3) := inferInstance
    obtain ⟨n₀, hn₀⟩ := exists_ne (1 : Multiplicative (Fin m → ZMod 3))
    obtain ⟨g₀, hg₀⟩ := π.rangeRestrict_surjective
      (eiso.symm (SemidirectProduct.inl n₀))
    have hg₀ker : g₀ ∈ r.ker := by
      show SemidirectProduct.rightHom (eiso (π.rangeRestrict g₀)) = 1
      rw [hg₀, MulEquiv.apply_symm_apply]
      exact SemidirectProduct.rightHom_inl n₀
    have hπg₀ : π g₀ ≠ 1 := by
      intro hone
      have hx1 : π.rangeRestrict g₀ = 1 := by
        apply Subtype.ext
        simpa using hone
      rw [hx1] at hg₀
      have hinl1 : SemidirectProduct.inl (φ := φ) n₀ = 1 := by
        have := congrArg eiso hg₀
        rw [MulEquiv.apply_symm_apply, map_one] at this
        exact this.symm
      exact hn₀ (SemidirectProduct.inl_injective (by rw [hinl1, map_one]))
    exact hπg₀ (hpi_one_of_scalar g₀ (hallscalar g₀ hg₀ker))
  · -- some kernel element is nonscalar: its eigenline is stable
    push Not at hallscalar
    obtain ⟨g₀, hg₀ker, hg₀ns'⟩ := hallscalar
    have hg₀ns : ¬ ∃ ν : L, σρ g₀ = ν • 1 := by
      rintro ⟨ν, hν⟩
      exact hg₀ns' ν hν
    obtain ⟨μ₀, hμ₀ne, hμ₀nil⟩ := hunip g₀ hg₀ker
    set A := σρ g₀ with hA
    set W := LinearMap.ker (A - μ₀ • 1) with hW
    -- a nonzero square-nilpotent operator on a `2`-dimensional space has
    -- a `1`-dimensional kernel
    have hline : ∀ T : Module.End L (L ⊗[k] V), T ≠ 0 → T ^ 2 = 0 →
        Module.finrank L (LinearMap.ker T) = 1 := by
      intro T hTne hT2
      have hrange : LinearMap.range T ≤ LinearMap.ker T := by
        rintro _ ⟨v, rfl⟩
        rw [LinearMap.mem_ker]
        have := congrFun (congrArg DFunLike.coe hT2) v
        simpa [pow_two] using this
      have hrn := LinearMap.finrank_range_add_finrank_ker T
      rw [hfr2] at hrn
      have hrpos : 0 < Module.finrank L (LinearMap.range T) := by
        rcases Nat.eq_zero_or_pos (Module.finrank L (LinearMap.range T))
          with h0 | hp
        · exact absurd (LinearMap.range_eq_bot.mp
            (Submodule.finrank_eq_zero.mp h0)) hTne
        · exact hp
      have hle := Submodule.finrank_mono hrange
      omega
    -- the eigenline is one-dimensional
    have hNne : A - μ₀ • 1 ≠ 0 := by
      intro h0
      exact hg₀ns ⟨μ₀, sub_eq_zero.mp h0⟩
    have hWfr : Module.finrank L W = 1 := by
      rw [hW]
      exact hline _ hNne hμ₀nil
    -- projective classes of kernel elements commute (the left factor of
    -- the semidirect product is abelian)
    have hπcomm : ∀ g g' : Γ ℚ, g ∈ r.ker → g' ∈ r.ker →
        π g * π g' = π g' * π g := by
      intro g g' hg hg'
      have hinl : ∀ gg : Γ ℚ, gg ∈ r.ker → ∃ n,
          SemidirectProduct.inl (φ := φ) n = eiso (π.rangeRestrict gg) := by
        intro gg hgg
        have hmem : eiso (π.rangeRestrict gg) ∈
            (SemidirectProduct.inl (φ := φ)).range := by
          rw [SemidirectProduct.range_inl_eq_ker_rightHom]
          exact hgg
        exact hmem
      obtain ⟨n, hn⟩ := hinl g hg
      obtain ⟨n', hn'⟩ := hinl g' hg'
      have hx : π.rangeRestrict g * π.rangeRestrict g' =
          π.rangeRestrict g' * π.rangeRestrict g := by
        apply eiso.injective
        rw [map_mul, map_mul, ← hn, ← hn', ← map_mul, ← map_mul,
          mul_comm n n']
      have := congrArg Subtype.val hx
      simpa using this
  -- the scalar factor of a commutator of kernel elements is `±1`,
    -- and `-1` is impossible; so kernel elements commute with `A`
    have hcommA : ∀ g : Γ ℚ, g ∈ r.ker → (¬ ∃ ν : L, σρ g = ν • 1) →
        ∀ μ : L, (σρ g - μ • 1) ^ 2 = 0 → μ ≠ 0 →
        σρ g * A = A * σρ g := by
      intro g hg hgns μ hμnil _
      set B := σρ g with hB
      -- the commutator acts by a scalar `λ'`
      have hπc : π (g * g₀ * g⁻¹ * g₀⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        rw [show π g * π g₀ = π g₀ * π g from hπcomm g g₀ hg hg₀ker]
        group
      obtain ⟨lam, hlam⟩ := hscalar_of_pi_one _ hπc
      -- `B A = lam • (A B)`
      have hBA : B * A = lam • (A * B) := by
        have hc : σρ (g * g₀ * g⁻¹ * g₀⁻¹) = B * A * σρ g⁻¹ * σρ g₀⁻¹ := by
          rw [map_mul, map_mul, map_mul]
        rw [hc] at hlam
        have h1 : σρ g⁻¹ * B = 1 := by
          rw [hB, ← map_mul, inv_mul_cancel, map_one]
        have h2 : σρ g₀⁻¹ * A = 1 := by
          rw [hA, ← map_mul, inv_mul_cancel, map_one]
        calc B * A = B * A * σρ g⁻¹ * σρ g₀⁻¹ * (A * B) * 1 * 1 := by
              have e1 : B * A * σρ g⁻¹ * σρ g₀⁻¹ * (A * B) =
                  B * A * σρ g⁻¹ * ((σρ g₀⁻¹ * A) * B) := by
                simp only [mul_assoc]
              rw [mul_one, mul_one, e1, h2, one_mul]
              have e2 : B * A * σρ g⁻¹ * B = B * A * (σρ g⁻¹ * B) := by
                simp only [mul_assoc]
              rw [e2, h1, mul_one]
          _ = lam • (A * B) := by
              rw [mul_one, mul_one, hlam, smul_mul_assoc, one_mul]
      -- `lam² = 1` via determinants
      have hdetAB : LinearMap.det (A * B) ≠ 0 := by
        have hAB : A * B = σρ (g₀ * g) := by rw [map_mul, hA, hB]
        have hinv : σρ (g₀ * g) * σρ ((g₀ * g)⁻¹) = 1 := by
          rw [← map_mul, mul_inv_cancel, map_one]
        intro h0
        have hd := congrArg LinearMap.det hinv
        rw [map_mul, map_one, ← hAB, h0, zero_mul] at hd
        exact zero_ne_one hd
      have hlam2 : lam * lam = 1 := by
        have hdet := congrArg LinearMap.det hBA
        rw [LinearMap.det_smul, hfr2] at hdet
        have hcommdet : LinearMap.det (B * A) = LinearMap.det (A * B) := by
          rw [map_mul, map_mul, mul_comm]
        rw [hcommdet] at hdet
        have h1 : (1 : L) * LinearMap.det (A * B) =
            lam ^ 2 * LinearMap.det (A * B) := by
          rw [one_mul, ← hdet]
        have h2 := mul_right_cancel₀ hdetAB h1
        rw [pow_two] at h2
        exact h2.symm
      rcases mul_self_eq_one_iff.mp hlam2 with hl1 | hlm1
      · rw [hl1, one_smul] at hBA
        exact hBA
      · -- `lam = -1` is impossible
        exfalso
        rw [hlm1] at hBA
        -- conjugating `A` by `B` gives `-A`
        have hBinv : B * σρ g⁻¹ = 1 := by
          rw [hB, ← map_mul, mul_inv_cancel, map_one]
        have hconjA : B * A * σρ g⁻¹ = -A := by
          rw [hBA]
          have e1 : (-1 : L) • (A * B) * σρ g⁻¹ =
              (-1 : L) • (A * (B * σρ g⁻¹)) := by
            rw [smul_mul_assoc, mul_assoc]
          rw [e1, hBinv, mul_one]
          exact neg_one_smul L A
        -- `(-A - μ₀ • 1)² = 0` from conjugating the nilpotency of `A`
        have hnegnil : (-A - μ₀ • 1) ^ 2 = 0 := by
          rw [← hconjA]
          have hfacB : B * A * σρ g⁻¹ - μ₀ • 1 =
              B * (A - μ₀ • 1) * σρ g⁻¹ := by
            have hdist : B * (A - μ₀ • 1) * σρ g⁻¹ =
                B * A * σρ g⁻¹ - B * (μ₀ • 1) * σρ g⁻¹ := by
              refine LinearMap.ext fun v => ?_
              simp only [Module.End.mul_apply, LinearMap.sub_apply,
                LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
            rw [hdist]
            congr 1
            rw [mul_smul_comm, mul_one, smul_mul_assoc, hBinv]
          rw [hfacB]
          have hswap : σρ g⁻¹ * B = 1 := by
            rw [hB, ← map_mul, inv_mul_cancel, map_one]
          have hexp : (B * (A - μ₀ • 1) * σρ g⁻¹) ^ 2 =
              B * ((A - μ₀ • 1) * (σρ g⁻¹ * B) * (A - μ₀ • 1)) * σρ g⁻¹ := by
            rw [pow_two]
            noncomm_ring
          rw [hexp, hswap, mul_one, ← pow_two, hμ₀nil, mul_zero, zero_mul]
        -- expand both nilpotency relations and subtract: `(4 μ₀) • A = 0`
        have e1 : (A - μ₀ • 1) ^ 2 =
            A * A - (2 * μ₀) • A + (μ₀ * μ₀) • 1 := by
          rw [pow_two]
          refine LinearMap.ext fun v => ?_
          simp only [Module.End.mul_apply, LinearMap.sub_apply,
            LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
            map_sub, map_smul]
          module
        have e2 : (-A - μ₀ • 1) ^ 2 =
            A * A + (2 * μ₀) • A + (μ₀ * μ₀) • 1 := by
          rw [pow_two]
          refine LinearMap.ext fun v => ?_
          simp only [Module.End.mul_apply, LinearMap.sub_apply,
            LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
            Module.End.one_apply, map_sub, map_neg, map_smul]
          module
        have h5 : (A * A + (2 * μ₀) • A + (μ₀ * μ₀) • 1) -
            (A * A - (2 * μ₀) • A + (μ₀ * μ₀) • 1) = 0 := by
          rw [← e1, ← e2, hμ₀nil, hnegnil]
          exact sub_self (0 : Module.End L (L ⊗[k] V))
        have h6 : (A * A + (2 * μ₀) • A + (μ₀ * μ₀) • 1) -
            (A * A - (2 * μ₀) • A + (μ₀ * μ₀) • 1) =
            ((4 : L) * μ₀) • A := by
          refine LinearMap.ext fun v => ?_
          simp only [LinearMap.sub_apply, LinearMap.add_apply,
            LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply]
          module
        rw [h6] at h5
        have h4 : ((4 : L) * μ₀) = μ₀ := by
          have h3L : (3 : L) = 0 := by
            exact_mod_cast CharP.cast_eq_zero L 3
          linear_combination μ₀ * h3L
        rw [h4] at h5
        have hA0 : A = 0 := by
          rcases smul_eq_zero.mp h5 with h' | h'
          · exact absurd h' hμ₀ne
          · exact h'
        have hAinv : A * σρ g₀⁻¹ = 1 := by
          rw [hA, ← map_mul, mul_inv_cancel, map_one]
        rw [hA0, zero_mul] at hAinv
        exact hEnd_ne hAinv.symm
    -- key: any nonscalar kernel element has the same eigenline
    have hshare : ∀ g : Γ ℚ, g ∈ r.ker → (¬ ∃ ν : L, σρ g = ν • 1) →
        ∀ μ : L, (σρ g - μ • 1) ^ 2 = 0 →
        LinearMap.ker (σρ g - μ • 1) = W := by
      intro g hg hgns μ hμnil
      -- `μ ≠ 0` (as for every kernel element)
      obtain ⟨μ', hμ'ne, hμ'nil⟩ := hunip g hg
      have hμμ' : μ = μ' := by
        -- two square-nilpotent shifts of the same nonscalar operator
        -- have equal parameters
        by_contra hne
        set B' := σρ g
        have e1 : (B' - μ • 1) ^ 2 =
            B' * B' - (2 * μ) • B' + (μ * μ) • 1 := by
          rw [pow_two]
          refine LinearMap.ext fun v => ?_
          simp only [Module.End.mul_apply, LinearMap.sub_apply,
            LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
            map_sub, map_smul]
          module
        have e2 : (B' - μ' • 1) ^ 2 =
            B' * B' - (2 * μ') • B' + (μ' * μ') • 1 := by
          rw [pow_two]
          refine LinearMap.ext fun v => ?_
          simp only [Module.End.mul_apply, LinearMap.sub_apply,
            LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
            map_sub, map_smul]
          module
        have h5 : (B' * B' - (2 * μ) • B' + (μ * μ) • 1) -
            (B' * B' - (2 * μ') • B' + (μ' * μ') • 1) = 0 := by
          rw [← e1, ← e2, hμnil, hμ'nil]
          exact sub_self (0 : Module.End L (L ⊗[k] V))
        have h6 : (B' * B' - (2 * μ) • B' + (μ * μ) • 1) -
            (B' * B' - (2 * μ') • B' + (μ' * μ') • 1) =
            ((2 : L) * (μ' - μ)) • B' - ((μ' * μ' - μ * μ)) • 1 := by
          refine LinearMap.ext fun v => ?_
          simp only [LinearMap.sub_apply, LinearMap.add_apply,
            LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply]
          module
        rw [h6] at h5
        have h2ne : ((2 : L) * (μ' - μ)) ≠ 0 := by
          refine mul_ne_zero ?_ (sub_ne_zero.mpr (Ne.symm hne))
          intro h2
          have h3L : (3 : L) = 0 := by
            exact_mod_cast CharP.cast_eq_zero L 3
          have h1 : (1 : L) = 0 := by linear_combination h3L - h2
          exact one_ne_zero h1
        refine hgns ⟨((2 : L) * (μ' - μ))⁻¹ * (μ' * μ' - μ * μ), ?_⟩
        have hB'eq : ((2 : L) * (μ' - μ)) • B' =
            ((μ' * μ' - μ * μ)) • (1 : Module.End L (L ⊗[k] V)) :=
          sub_eq_zero.mp h5
        have := congrArg (fun T => (((2 : L) * (μ' - μ))⁻¹) • T) hB'eq
        simp only [smul_smul, inv_mul_cancel₀ h2ne, one_smul] at this
        exact this
      subst hμμ'
      -- kernel elements commute with `A`
      have hBA := hcommA g hg hgns μ hμnil hμ'ne
      -- `σρ g` preserves `W`, so a spanning vector of `W` is an
      -- eigenvector of `σρ g` with its unique eigenvalue `μ`
      obtain ⟨w, hwW, hwne⟩ : ∃ w ∈ W, w ≠ 0 := by
        by_contra hnone
        push Not at hnone
        have : W = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          rcases eq_or_ne x 0 with rfl | hxne
          · exact Submodule.zero_mem _
          · exact absurd (hnone x hx) (by simpa using hxne)
        rw [this, finrank_bot] at hWfr
        omega
      have hspan : Submodule.span L {w} = W := by
        apply Submodule.eq_of_le_of_finrank_le
          ((Submodule.span_singleton_le_iff_mem w W).mpr hwW)
        rw [hWfr, finrank_span_singleton hwne]
      have hBw : σρ g w ∈ W := by
        rw [hW, LinearMap.mem_ker] at hwW ⊢
        have hcommshift : (A - μ₀ • 1) * σρ g = σρ g * (A - μ₀ • 1) := by
          refine LinearMap.ext fun v => ?_
          simp only [Module.End.mul_apply, LinearMap.sub_apply,
            LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
          rw [show A (σρ g v) = σρ g (A v) from
            congrFun (congrArg DFunLike.coe hBA.symm) v]
        have := congrFun (congrArg DFunLike.coe hcommshift) w
        simp only [Module.End.mul_apply] at this
        rw [this, hwW, map_zero]
      have hBw' : σρ g w ∈ Submodule.span L {w} := by
        rw [hspan]
        exact hBw
      obtain ⟨cst, hcst⟩ := (Submodule.mem_span_singleton).mp hBw'
      -- the eigenvalue is `μ`
      have hcstμ : cst = μ := by
        have happ : (((σρ g - μ • 1) ^ 2 : Module.End L (L ⊗[k] V))) w =
            ((cst - μ) * (cst - μ)) • w := by
          rw [pow_two]
          have h1 : (σρ g - μ • 1) w = (cst - μ) • w := by
            have h2 : (σρ g - μ • 1) w = σρ g w - μ • w := by
              simp [LinearMap.sub_apply, LinearMap.smul_apply,
                Module.End.one_apply]
            rw [h2, ← hcst]
            module
          show (σρ g - μ • 1) ((σρ g - μ • 1) w) = _
          rw [h1, map_smul, h1, smul_smul]
        rw [hμnil] at happ
        have h0 : ((cst - μ) * (cst - μ)) • w = 0 := by
          rw [← happ]
          simp
        rcases smul_eq_zero.mp h0 with h' | h'
        · exact sub_eq_zero.mp (mul_self_eq_zero.mp h')
        · exact absurd h' hwne
      -- hence `w ∈ ker (σρ g − μ)`, and the two lines coincide
      have hwker : w ∈ LinearMap.ker (σρ g - μ • 1) := by
        rw [LinearMap.mem_ker]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply]
        rw [← hcst, hcstμ, sub_self]
      have hkerfr : Module.finrank L (LinearMap.ker (σρ g - μ • 1)) = 1 := by
        refine hline _ ?_ hμnil
        intro h0
        exact hgns ⟨μ, sub_eq_zero.mp h0⟩
      symm
      apply Submodule.eq_of_le_of_finrank_le
      · rw [← hspan]
        exact (Submodule.span_singleton_le_iff_mem w _).mpr hwker
      · rw [hWfr, hkerfr]
    -- stability of `W` under the whole action, by normality of the kernel
    have hstable : ∀ h : Γ ℚ, ∀ w ∈ W, σρ h w ∈ W := by
      intro h w hw
      -- the conjugate `h g₀ h⁻¹` is again in the kernel
      have hconjker : h * g₀ * h⁻¹ ∈ r.ker := by
        have : r (h * g₀ * h⁻¹) = r h * r g₀ * (r h)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        rw [MonoidHom.mem_ker, this, hg₀ker, mul_one, mul_inv_cancel]
      -- its action is the conjugated operator, nonscalar, with the same
      -- unipotent parameter `μ₀` and eigenline `σρ h '' W`
      have hconj : σρ (h * g₀ * h⁻¹) = σρ h * A * σρ h⁻¹ := by
        rw [map_mul, map_mul, hA]
      have h1inv : σρ h⁻¹ * σρ h = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      have hconjns : ¬ ∃ ν : L, σρ (h * g₀ * h⁻¹) = ν • 1 := by
        rintro ⟨ν, hν⟩
        refine hg₀ns ⟨ν, ?_⟩
        have h2 : A = σρ h⁻¹ * σρ (h * g₀ * h⁻¹) * σρ h := by
          rw [hconj]
          have h3 : σρ h⁻¹ * (σρ h * A * σρ h⁻¹) * σρ h =
              (σρ h⁻¹ * σρ h) * A * (σρ h⁻¹ * σρ h) := by
            simp only [mul_assoc]
          rw [h3, h1inv, one_mul, mul_one]
        rw [h2, hν]
        rw [mul_smul_comm, smul_mul_assoc, mul_one, h1inv]
      have hfac : σρ (h * g₀ * h⁻¹) - μ₀ • 1 =
          σρ h * (A - μ₀ • 1) * σρ h⁻¹ := by
        rw [hconj]
        have hdist : σρ h * (A - μ₀ • 1) * σρ h⁻¹ =
            σρ h * A * σρ h⁻¹ - σρ h * (μ₀ • 1) * σρ h⁻¹ := by
          refine LinearMap.ext fun v => ?_
          simp [Module.End.mul_apply, LinearMap.sub_apply, map_sub,
            LinearMap.smul_apply, Module.End.one_apply, map_smul]
        rw [hdist]
        congr 1
        rw [mul_smul_comm, mul_one, smul_mul_assoc, hunit]
      have hconjnil : (σρ (h * g₀ * h⁻¹) - μ₀ • 1) ^ 2 = 0 := by
        rw [hfac]
        have hexp : (σρ h * (A - μ₀ • 1) * σρ h⁻¹) ^ 2 =
            σρ h * ((A - μ₀ • 1) * (σρ h⁻¹ * σρ h) * (A - μ₀ • 1)) *
              σρ h⁻¹ := by
          rw [pow_two]
          noncomm_ring
        rw [hexp, h1inv, mul_one, ← pow_two, hμ₀nil, mul_zero, zero_mul]
      have hkerconj : LinearMap.ker (σρ (h * g₀ * h⁻¹) - μ₀ • 1) = W :=
        hshare _ hconjker hconjns μ₀ hconjnil
      -- `σρ h w` lies in that kernel
      rw [← hkerconj, LinearMap.mem_ker]
      rw [hfac]
      have hinvw : σρ h⁻¹ (σρ h w) = w := by
        have h4 := congrFun (congrArg DFunLike.coe h1inv) w
        simp only [Module.End.mul_apply, Module.End.one_apply] at h4
        exact h4
      show σρ h ((A - μ₀ • 1) (σρ h⁻¹ (σρ h w))) = 0
      rw [hinvw]
      have hw0 : (A - μ₀ • 1) w = 0 := LinearMap.mem_ker.mp hw
      rw [hw0, map_zero]
    -- contradiction with irreducibility
    rcases hsub W hstable with hbot | htop
    · rw [hbot] at hWfr
      rw [finrank_bot] at hWfr
      omega
    · rw [htop] at hWfr
      rw [finrank_top, hfr2] at hWfr
      omega

/-- **Index-two parity: odd-order elements** (PROVEN 2026-07-22): a
subgroup of index dividing `2` contains every element of odd order
(index `1` is everything; index exactly `2` is the vendored Dickson
helper `mem_of_odd_orderOf_of_index_two`). -/
theorem mem_of_index_dvd_two_of_odd_orderOf {G : Type*} [Group G] (H : Subgroup G)
    (hidx : H.index ∣ 2) (g : G) (hodd : Odd (orderOf g)) : g ∈ H := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    rw [h1]
    exact Subgroup.mem_top g
  · exact mem_of_odd_orderOf_of_index_two H h2 g hodd

/-- **Alternating groups have no index-two subgroups** (PROVEN
2026-07-22): the alternating group is generated by its three-cycles
(`Equiv.Perm.closure_three_cycles_eq_alternating`), which have odd
order `3`, so a subgroup of index dividing `2` is everything. -/
theorem alternating_subgroup_eq_top_of_index_dvd_two {n : ℕ}
    (H : Subgroup (alternatingGroup (Fin n))) (hidx : H.index ∣ 2) : H = ⊤ := by
  have hcl : Subgroup.closure
      {x : alternatingGroup (Fin n) | (x : Equiv.Perm (Fin n)).IsThreeCycle} = ⊤ := by
    apply Subgroup.map_injective (alternatingGroup (Fin n)).subtype_injective
    have himg : (alternatingGroup (Fin n)).subtype ''
        {x : alternatingGroup (Fin n) | (x : Equiv.Perm (Fin n)).IsThreeCycle} =
        {σ : Equiv.Perm (Fin n) | σ.IsThreeCycle} := by
      apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hx
      · intro σ hσ
        exact ⟨⟨σ, hσ.mem_alternatingGroup⟩, hσ, rfl⟩
    rw [MonoidHom.map_closure, himg, Equiv.Perm.closure_three_cycles_eq_alternating]
    exact (Subgroup.range_subtype _).symm.trans (MonoidHom.range_eq_map _)
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  intro x hx
  have hx' : (x : Equiv.Perm (Fin n)).IsThreeCycle := hx
  have h3 : orderOf x = 3 := by
    rw [← orderOf_injective (alternatingGroup (Fin n)).subtype
      (alternatingGroup (Fin n)).subtype_injective x]
    exact hx'.orderOf
  exact mem_of_index_dvd_two_of_odd_orderOf H hidx x (by rw [h3]; decide)

/-- **`SL₂` over a char-3 field has no index-two subgroups** (PROVEN
2026-07-22): `SL₂(F)` is generated by the elementary matrices
(`SL2.closure_elementary_eq_top`, vendored Dickson), which in
characteristic `3` have order `3`. -/
theorem sl2_subgroup_eq_top_of_index_dvd_two {F : Type*} [Field F] [CharP F 3]
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hidx : H.index ∣ 2) :
    H = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmul12 : ∀ a c : F, SL2.E12 F a * SL2.E12 F c = SL2.E12 F (a + c) := by
    intro a c
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show (!![1, a; 0, 1] * !![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, a + c; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hmul21 : ∀ a c : F, SL2.E21 F a * SL2.E21 F c = SL2.E21 F (a + c) := by
    intro a c
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show (!![1, 0; a, 1] * !![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, 0; a + c, 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hzero12 : SL2.E12 F 0 = 1 := by
    apply Subtype.ext
    show (!![1, (0 : F); 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.one_fin_two]
  have hzero21 : SL2.E21 F 0 = 1 := by
    apply Subtype.ext
    show (!![1, 0; (0 : F), 1] : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.one_fin_two]
  have h3a : ∀ a : F, a + a + a = 0 := by
    intro a
    have h30 : ((3 : ℕ) : F) = 0 := CharP.cast_eq_zero F 3
    push_cast at h30
    linear_combination a * h30
  have hcube12 : ∀ a : F, SL2.E12 F a ^ 3 = 1 := by
    intro a
    calc SL2.E12 F a ^ 3 = SL2.E12 F (a + a + a) := by
          rw [pow_succ, pow_two, hmul12, hmul12]
      _ = 1 := by rw [h3a, hzero12]
  have hcube21 : ∀ a : F, SL2.E21 F a ^ 3 = 1 := by
    intro a
    calc SL2.E21 F a ^ 3 = SL2.E21 F (a + a + a) := by
          rw [pow_succ, pow_two, hmul21, hmul21]
      _ = 1 := by rw [h3a, hzero21]
  have hord12 : ∀ a : F, a ≠ 0 → orderOf (SL2.E12 F a) = 3 := by
    intro a ha
    refine orderOf_eq_prime (hcube12 a) fun h1 => ha ?_
    have h01 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F) 0 1) h1
    simpa [SL2.E12, Matrix.one_apply] using h01
  have hord21 : ∀ a : F, a ≠ 0 → orderOf (SL2.E21 F a) = 3 := by
    intro a ha
    refine orderOf_eq_prime (hcube21 a) fun h1 => ha ?_
    have h10 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F) 1 0) h1
    simpa [SL2.E21, Matrix.one_apply] using h10
  rw [eq_top_iff, ← SL2.closure_elementary_eq_top F, Subgroup.closure_le]
  rintro x (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · rcases eq_or_ne a 0 with rfl | ha
    · rw [hzero12]
      exact H.one_mem
    · exact mem_of_index_dvd_two_of_odd_orderOf H hidx _ (by rw [hord12 a ha]; decide)
  · rcases eq_or_ne a 0 with rfl | ha
    · rw [hzero21]
      exact H.one_mem
    · exact mem_of_index_dvd_two_of_odd_orderOf H hidx _ (by rw [hord21 a ha]; decide)

/-- **`PSL₂` over a char-3 field has no index-two subgroups** (PROVEN
2026-07-22): pull an index-`≤ 2` subgroup back along the surjection
`SL₂ → PSL₂` and apply the `SL₂` statement. -/
theorem psl2_subgroup_eq_top_of_index_dvd_two {F : Type*} [Field F] [CharP F 3]
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (hidx : H.index ∣ 2) : H = ⊤ := by
  have hsurj : Function.Surjective
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    QuotientGroup.mk'_surjective _
  have htop := sl2_subgroup_eq_top_of_index_dvd_two
    (H.comap (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))))
    (by rw [H.index_comap_of_surjective hsurj]; exact hidx)
  rw [← Subgroup.map_comap_eq_self_of_surjective hsurj H, htop,
    Subgroup.map_top_of_surjective _ hsurj]

/-- **The cardinality of `PSL₂` of a finite char-3 field** (PROVEN
2026-07-22): `|PSL₂(F)| · 2 = q(q² − 1)`, from the vendored
`SL2_card` (`|SL₂| = q(q² − 1)`) and `SL2_center_card`
(`|Z(SL₂)| = 2`). -/
theorem card_psl2_mul_two (F : Type*) [Field F] [Fintype F] [CharP F 3] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * 2 =
      Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact ((3 : ℕ) > 2) := ⟨by norm_num⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  rw [SL2_center_card 3 F, SL2_card F Fintype.one_lt_card] at h
  exact h.symm

/-- **Arithmetic of `q = 3^m`** (PROVEN 2026-07-22): `q² − 1` is a
positive multiple of `8` (as `9^m ≡ 1 mod 8`) and `q ≥ 3`. -/
theorem galoisField_three_pow_arith (m : ℕ) (hm : 1 ≤ m) :
    ∃ t : ℕ, 1 ≤ t ∧ (3 ^ m) ^ 2 - 1 = 8 * t ∧ 3 ≤ 3 ^ m := by
  have h9 : (3 ^ m) ^ 2 % 8 = 1 := by
    rw [show ((3 : ℕ) ^ m) ^ 2 = 9 ^ m by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      Nat.pow_mod]
    norm_num
  have h3m : 3 ≤ 3 ^ m :=
    calc (3 : ℕ) = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hx9 : 9 ≤ (3 ^ m) ^ 2 := by nlinarith
  exact ⟨((3 ^ m) ^ 2 - 1) / 8, by omega, by omega, h3m⟩

/-- **Index-`≤ 2` subgroups of `PGL₂(𝔽_{3^m})` are even of order
`≥ 12`** (PROVEN 2026-07-22): index `1` is everything, of cardinality
`q(q² − 1) ≥ 24`; index `2` contains the image of `PSL₂` (the vendored
`PSLImageInPGL_le_of_index_two`), of even cardinality
`q(q² − 1)/2 ≥ 12` dividing the subgroup's. -/
theorem pgl2_galoisField_subgroup_card {m : ℕ} (hm : 1 ≤ m)
    (H : Subgroup (GL (Fin 2) (GaloisField 3 m) ⧸
      Subgroup.center (GL (Fin 2) (GaloisField 3 m))))
    (hidx : H.index ∣ 2) : 2 ∣ Nat.card H ∧ 12 ≤ Nat.card H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact ((3 : ℕ) > 2) := ⟨by norm_num⟩
  haveI : Fintype (GaloisField 3 m) := Fintype.ofFinite _
  obtain ⟨t, ht1, ht8, h3m⟩ := galoisField_three_pow_arith m hm
  have hcF : Fintype.card (GaloisField 3 m) = 3 ^ m := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 m (by omega)]
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    rw [h1, Subgroup.card_top, Dickson.card_PGL2, hcF, ht8]
    exact ⟨⟨3 ^ m * (4 * t), by ring⟩, by nlinarith⟩
  · have hle : PSLImageInPGL (GaloisField 3 m) ≤ H :=
      PSLImageInPGL_le_of_index_two 3 (GaloisField 3 m) H h2
    have h1' := Subgroup.card_mul_index (MonoidHom.ker (SL2ToPGL (GaloisField 3 m)))
    rw [Subgroup.index_ker, SL2ToPGL_ker_eq_center, SL2_center_card 3 (GaloisField 3 m),
      SL2_card (GaloisField 3 m) Fintype.one_lt_card, hcF, ht8] at h1'
    have hcPSL : Nat.card (PSLImageInPGL (GaloisField 3 m)) = 3 ^ m * (4 * t) := by
      have h4 : (3 ^ m * (4 * t)) * 2 = 3 ^ m * (8 * t) := by ring
      have h5 : Nat.card (PSLImageInPGL (GaloisField 3 m)) =
          Nat.card (SL2ToPGL (GaloisField 3 m)).range := rfl
      omega
    have hdvd : Nat.card (PSLImageInPGL (GaloisField 3 m)) ∣ Nat.card H :=
      Subgroup.card_dvd_of_le hle
    have hpos : 0 < Nat.card H := Nat.card_pos
    constructor
    · exact dvd_trans ⟨3 ^ m * (2 * t), by rw [hcPSL]; ring⟩ hdvd
    · calc (12 : ℕ) ≤ 3 ^ m * (4 * t) := by nlinarith
        _ = Nat.card (PSLImageInPGL (GaloisField 3 m)) := hcPSL.symm
        _ ≤ Nat.card H := Nat.le_of_dvd hpos hdvd

/-- **Transport of the index-two subgroup bound along a group
isomorphism** (PROVEN 2026-07-22). -/
theorem subgroup_card_of_mulEquiv {P Gt : Type*} [Group P] [Group Gt]
    (ι : P ≃* Gt)
    (hGt : ∀ Ht : Subgroup Gt, Ht.index ∣ 2 → 2 ∣ Nat.card Ht ∧ 12 ≤ Nat.card Ht) :
    ∀ H : Subgroup P, H.index ∣ 2 → 2 ∣ Nat.card H ∧ 12 ≤ Nat.card H := by
  intro H hidx
  have hidxt : (H.map ι.toMonoidHom).index = H.index := by
    rw [Subgroup.index_map, (MonoidHom.ker_eq_bot_iff _).mpr ι.injective, sup_bot_eq,
      MonoidHom.range_eq_top.mpr ι.surjective, Subgroup.index_top, mul_one]
  have hcardt : Nat.card (H.map ι.toMonoidHom) = Nat.card H :=
    Nat.card_congr (H.equivMapOfInjective ι.toMonoidHom ι.injective).toEquiv.symm
  have h := hGt (H.map ι.toMonoidHom) (by rw [hidxt]; exact hidx)
  rwa [hcardt] at h

/-- **The five exceptional Dickson groups: subgroups of index `≤ 2`
are even of order `≥ 12`** (PROVEN 2026-07-22): in `A₄`, `A₅` and
`PSL₂(𝔽_{3^m})` an index-`≤ 2` subgroup is the whole group (generation
by order-3 elements) of even order `12`, `60`, `q(q² − 1)/2 ≥ 12`; in
`S₄` it has order `12` or `24`; in `PGL₂(𝔽_{3^m})` it contains the
`PSL₂` image. -/
theorem dickson_exceptional_subgroup_card {P : Type*} [Group P]
    (hcase :
      (Nonempty (P ≃* alternatingGroup (Fin 4))) ∨
      (Nonempty (P ≃* Equiv.Perm (Fin 4))) ∨
      (Nonempty (P ≃* alternatingGroup (Fin 5))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (P ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 m))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (P ≃*
        (GL (Fin 2) (GaloisField 3 m) ⧸
          Subgroup.center (GL (Fin 2) (GaloisField 3 m)))))) :
    ∀ H : Subgroup P, H.index ∣ 2 → 2 ∣ Nat.card H ∧ 12 ≤ Nat.card H := by
  rcases hcase with ⟨⟨ι⟩⟩ | ⟨⟨ι⟩⟩ | ⟨⟨ι⟩⟩ | ⟨m, hm, ⟨ι⟩⟩ | ⟨m, hm, ⟨ι⟩⟩
  · refine subgroup_card_of_mulEquiv ι ?_
    intro Ht hidxt
    rw [alternating_subgroup_eq_top_of_index_dvd_two Ht hidxt, Subgroup.card_top]
    have hc : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [hc]
    exact ⟨⟨6, rfl⟩, le_refl 12⟩
  · refine subgroup_card_of_mulEquiv ι ?_
    intro Ht hidxt
    have hc : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have hmul := Ht.card_mul_index
    rw [hc] at hmul
    rcases (Nat.dvd_prime Nat.prime_two).mp hidxt with h1 | h2
    · rw [h1] at hmul
      omega
    · rw [h2] at hmul
      omega
  · refine subgroup_card_of_mulEquiv ι ?_
    intro Ht hidxt
    rw [alternating_subgroup_eq_top_of_index_dvd_two Ht hidxt, Subgroup.card_top]
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [hc]
    exact ⟨⟨30, rfl⟩, by norm_num⟩
  · refine subgroup_card_of_mulEquiv ι ?_
    intro Ht hidxt
    haveI : Fintype (GaloisField 3 m) := Fintype.ofFinite _
    obtain ⟨t, ht1, ht8, h3m⟩ := galoisField_three_pow_arith m hm
    have hcF : Fintype.card (GaloisField 3 m) = 3 ^ m := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 3 m (by omega)]
    rw [psl2_subgroup_eq_top_of_index_dvd_two Ht hidxt, Subgroup.card_top]
    have hc2 := card_psl2_mul_two (GaloisField 3 m)
    rw [hcF, ht8] at hc2
    have hcPSL : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 m)) =
        3 ^ m * (4 * t) := by
      have h4 : (3 ^ m * (4 * t)) * 2 = 3 ^ m * (8 * t) := by ring
      omega
    rw [hcPSL]
    exact ⟨⟨3 ^ m * (2 * t), by ring⟩, by nlinarith⟩
  · refine subgroup_card_of_mulEquiv ι ?_
    intro Ht hidxt
    exact pgl2_galoisField_subgroup_card hm Ht hidxt

/-- **A nonscalar `2×2` matrix of determinant one does not square to
one away from characteristic `2`** (PROVEN 2026-07-22): if `x² = 1`
and `det x = 1`, the `2×2` Cayley–Hamilton identity gives
`(tr x)·x = 2·1`; `2 ≠ 0` forces `tr x ≠ 0`, so `x` is scalar —
i.e. central in `GL₂`. -/
theorem gl2_sq_ne_one_of_notMem_center {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (x : GL (Fin 2) F) (hdet : Matrix.GeneralLinearGroup.det x = 1)
    (hcen : x ∉ Subgroup.center (GL (Fin 2) F)) : x * x ≠ 1 := by
  intro hcontra
  apply hcen
  have hdetA : (x : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have h := congrArg Units.val hdet
    exact h
  have hAA : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have h := congrArg Units.val hcontra
    rwa [Units.val_mul, Units.val_one] at h
  have hCH : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) =
      (x : Matrix (Fin 2) (Fin 2) F).trace • (x : Matrix (Fin 2) (Fin 2) F) -
        (x : Matrix (Fin 2) (Fin 2) F).det • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.trace, Matrix.diag, Matrix.det_fin_two,
        Fin.sum_univ_two] <;> ring
  rw [hAA, hdetA, one_smul] at hCH
  have htrA : (x : Matrix (Fin 2) (Fin 2) F).trace • (x : Matrix (Fin 2) (Fin 2) F) =
      ((1 : F) + 1) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [add_smul, one_smul]
    exact (eq_sub_iff_add_eq.mp hCH).symm
  have htrne : (x : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at htrA
    have h00 := congrFun (congrFun htrA 0) 0
    rw [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at h00
    exact h2 (by linear_combination -h00)
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨(x : Matrix (Fin 2) (Fin 2) F).trace⁻¹ * (1 + 1), ?_⟩
  have hAs : (x : Matrix (Fin 2) (Fin 2) F) =
      ((x : Matrix (Fin 2) (Fin 2) F).trace⁻¹ * (1 + 1)) •
        (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [mul_smul, ← htrA, smul_smul, inv_mul_cancel₀ htrne, one_smul]
  conv_rhs => rw [hAs]
  ext i j
  rw [Matrix.smul_apply, Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · rw [smul_eq_mul, mul_one]
  · rw [smul_eq_mul, mul_zero]

/-- **Units of `ℤ₃` map to `±1` in characteristic 3** (PROVEN
2026-07-22): a `3`-adic unit is `≡ 1` or `2 (mod 3)`
(`PadicInt.zmodRepr`), and any ring homomorphism to a char-3 ring
kills the maximal ideal `(3)`. -/
theorem padic_three_ringHom_pm_one {R : Type*} [CommRing R] [CharP R 3]
    (f : ℤ_[3] →+* R) (x : ℤ_[3]ˣ) :
    f (x : ℤ_[3]) = 1 ∨ f (x : ℤ_[3]) = -1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hspec := PadicInt.zmodRepr_spec (x : ℤ_[3])
  have hfx : f (x : ℤ_[3]) = ((PadicInt.zmodRepr (x : ℤ_[3]) : ℕ) : R) := by
    have hmem := hspec.2
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    obtain ⟨w, hw⟩ := hmem
    have h0 : f ((x : ℤ_[3]) - (PadicInt.zmodRepr (x : ℤ_[3]) : ℕ)) = 0 := by
      rw [hw, map_mul]
      have h31 : f ((3 : ℕ) : ℤ_[3]) = 0 := by
        rw [map_natCast, CharP.cast_eq_zero R 3]
      rw [h31, zero_mul]
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, map_natCast]
  have hne0 : PadicInt.zmodRepr (x : ℤ_[3]) ≠ 0 := by
    intro h0
    have hmem : (x : ℤ_[3]) ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
      have h1 := hspec.2
      rwa [h0, Nat.cast_zero, sub_zero] at h1
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem) (Units.isUnit x)
  have h12 : PadicInt.zmodRepr (x : ℤ_[3]) = 1 ∨ PadicInt.zmodRepr (x : ℤ_[3]) = 2 := by
    omega
  rcases h12 with h | h
  · left
    rw [hfx, h, Nat.cast_one]
  · right
    rw [hfx, h]
    have h30 : ((3 : ℕ) : R) = 0 := CharP.cast_eq_zero R 3
    push_cast at h30 ⊢
    linear_combination h30

/-- **The 48-element counting core** (PROVEN 2026-07-22): a finite
group `N` with an index-two subgroup `S` (the determinant-one part)
and a homomorphism `ψ` onto `P` (the projectivization) has order
`≥ 48`, provided (i) every subgroup of `P` of index `≤ 2` — in
particular the image of `S` — is even of order `≥ 12`, and (ii) no
element of `S` over an involution of `P` squares to `1` (the
`−1 ∈ SL₂` lift). Chain:
`|N| = 2·|S| = 2·|ψ(S)|·|ker(ψ|_S)| ≥ 2·12·2 = 48` — the kernel is
nontrivial because Cauchy's theorem puts an involution in `ψ(S)`,
whose lift `s` has `s² ∈ ker(ψ|_S) \ {1}` by (ii). -/
theorem card_ge_48_of_index_two_kernel {N P : Type*} [Group N] [Finite N] [Group P]
    (S : Subgroup N) (hSidx : S.index = 2)
    (ψ : N →* P) (hψ : Function.Surjective ψ)
    (hcase : ∀ H : Subgroup P, H.index ∣ 2 → 2 ∣ Nat.card H ∧ 12 ≤ Nat.card H)
    (hlift : ∀ s : N, s ∈ S → orderOf (ψ s) = 2 → s * s ≠ 1) :
    48 ≤ Nat.card N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite P := Finite.of_surjective ψ hψ
  obtain ⟨hH'even, hH'12⟩ := hcase (S.map ψ) (hSidx ▸ S.index_map_dvd hψ)
  obtain ⟨y, hy2⟩ := exists_prime_orderOf_dvd_card' (G := S.map ψ) 2 hH'even
  have hzord : orderOf (y : P) = 2 := by
    rw [← hy2]
    exact orderOf_injective (S.map ψ).subtype (S.map ψ).subtype_injective y
  obtain ⟨s, hsS, hsz⟩ := Subgroup.mem_map.mp y.2
  have hs2ker : ψ (s * s) = 1 := by
    rw [map_mul, hsz, ← pow_two, ← hzord]
    exact pow_orderOf_eq_one _
  have hs2ne : s * s ≠ 1 := hlift s hsS (by rw [hsz]; exact hzord)
  have hrange : (ψ.comp S.subtype).range = S.map ψ := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(t : N), t.2, rfl⟩
    · intro hw
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hw
      exact ⟨⟨t, ht⟩, rfl⟩
  have hcardS : Nat.card S = Nat.card (S.map ψ) * Nat.card (ψ.comp S.subtype).ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (ψ.comp S.subtype).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (ψ.comp S.subtype)).toEquiv,
      hrange] at h1
    exact h1
  have hker2 : 2 ≤ Nat.card (ψ.comp S.subtype).ker := by
    have hmem : (⟨s, hsS⟩ : S) * ⟨s, hsS⟩ ∈ (ψ.comp S.subtype).ker := by
      rw [MonoidHom.mem_ker]
      exact hs2ker
    haveI : Nontrivial (ψ.comp S.subtype).ker :=
      ⟨⟨⟨(⟨s, hsS⟩ : S) * ⟨s, hsS⟩, hmem⟩, 1, fun hcontra => hs2ne (by
        have h0 := congrArg (fun w : (ψ.comp S.subtype).ker => ((w : S) : N)) hcontra
        simpa using h0)⟩⟩
    exact Finite.one_lt_card
  have hfin := S.card_mul_index
  rw [hSidx, hcardS] at hfin
  calc (48 : ℕ) = 12 * 2 * 2 := by norm_num
    _ ≤ Nat.card (S.map ψ) * Nat.card (ψ.comp S.subtype).ker * 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul hH'12 hker2) le_rfl
    _ = Nat.card N := hfin

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The exceptional projective images force a matrix image of order
`≥ 48`** (PROVEN 2026-07-22 — the group-theoretic half of the
root-discriminant elimination): if the projective image `π.range` of a
mod-3 hardly ramified representation is one of the five exceptional
Dickson groups, then the matrix image `u.range` has cardinality
`≥ 48`. Argument: `det ∘ u` takes only the values `±1` (the
determinant is the mod-3 cyclotomic character, and units of `ℤ₃` map
to `±1` in characteristic `3`), and the value `−1` is attained at
complex conjugation (`exists_conj_cyclotomicCharacter_three`), so the
determinant-one part `S ≤ u.range` has index exactly `2`; the counting
core `card_ge_48_of_index_two_kernel` applies to
`ψ : u.range → π.range` with the per-case subgroup bound
`dickson_exceptional_subgroup_card` and the Cayley–Hamilton lift
obstruction `gl2_sq_ne_one_of_notMem_center`. -/
theorem card_matrixRange_ge_of_exceptional {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase :
      (Nonempty (π.range ≃* alternatingGroup (Fin 4))) ∨
      (Nonempty (π.range ≃* Equiv.Perm (Fin 4))) ∨
      (Nonempty (π.range ≃* alternatingGroup (Fin 5))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 m))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        (GL (Fin 2) (GaloisField 3 m) ⧸
          Subgroup.center (GL (Fin 2) (GaloisField 3 m)))))) :
    48 ≤ Nat.card u.range := by
  classical
  -- (0) the matrix image is finite: `u` factors through the finite
  -- monoid `End k V`
  haveI : Finite V := Module.finite_of_finite k
  haveI hfinN : Finite u.range := by
    haveI : Finite (Module.End k V) :=
      Finite.of_injective _ DFunLike.coe_injective
    have hdep : ∀ g₁ g₂ : Γ ℚ, (MonoidHomClass.toMonoidHom ρ) g₁ =
        (MonoidHomClass.toMonoidHom ρ) g₂ → u g₁ = u g₂ := by
      intro g₁ g₂ h12
      apply Units.ext
      rw [hu, hu]
      show ((LinearMap.toMatrix b b
        (((MonoidHomClass.toMonoidHom ρ) g₁).baseChange (AlgebraicClosure k))).map e) =
        ((LinearMap.toMatrix b b
        (((MonoidHomClass.toMonoidHom ρ) g₂).baseChange (AlgebraicClosure k))).map e)
      rw [h12]
    let G' : Module.End k V → GL (Fin 2) (Dickson.K 3) := fun T =>
      if h : ∃ g, (MonoidHomClass.toMonoidHom ρ) g = T then u h.choose else 1
    have huG : ∀ g, u g = G' ((MonoidHomClass.toMonoidHom ρ) g) := by
      intro g
      have hex : ∃ g', (MonoidHomClass.toMonoidHom ρ) g' =
          (MonoidHomClass.toMonoidHom ρ) g := ⟨g, rfl⟩
      show u g = dite _ _ _
      rw [dif_pos hex]
      exact (hdep _ _ hex.choose_spec).symm
    have hsub : Set.range u ⊆ Set.range G' := by
      rintro _ ⟨g, rfl⟩
      exact ⟨_, (huG g).symm⟩
    exact ((Set.finite_range G').subset hsub).to_subtype
  -- (1) the determinant of the matrix action is the mod-3 cyclotomic
  -- character pushed to `𝔽̄₃`
  have hdet_val : ∀ g : Γ ℚ,
      ((Matrix.GeneralLinearGroup.det (u g) : (Dickson.K 3)ˣ) : Dickson.K 3) =
        ((e : AlgebraicClosure k →+* Dickson.K 3).comp
          ((algebraMap k (AlgebraicClosure k)).comp (algebraMap ℤ_[3] k)))
          ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) : ℤ_[3]) := by
    intro g
    calc ((Matrix.GeneralLinearGroup.det (u g) : (Dickson.K 3)ˣ) : Dickson.K 3)
        = ((u g : GL (Fin 2) (Dickson.K 3)) :
            Matrix (Fin 2) (Fin 2) (Dickson.K 3)).det := rfl
      _ = ((LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
            (MonoidHomClass.toMonoidHom ρ)) g)).map e).det := by rw [hu g]
      _ = e ((LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
            (MonoidHomClass.toMonoidHom ρ)) g)).det) :=
          (RingEquiv.map_det e _).symm
      _ = e (LinearMap.det ((Slop.OddRep.baseChange (AlgebraicClosure k)
            (MonoidHomClass.toMonoidHom ρ)) g)) := by rw [LinearMap.det_toMatrix]
      _ = e (algebraMap k (AlgebraicClosure k)
            (LinearMap.det ((MonoidHomClass.toMonoidHom ρ :
              Representation k (Γ ℚ) V) g))) := by
          rw [show (Slop.OddRep.baseChange (AlgebraicClosure k)
              (MonoidHomClass.toMonoidHom ρ)) g =
            ((MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g).baseChange
              (AlgebraicClosure k) from rfl, LinearMap.det_baseChange]
      _ = _ := by
          have hdg := hρ.det g
          rw [GaloisRep.det_apply] at hdg
          rw [show LinearMap.det ((MonoidHomClass.toMonoidHom ρ :
              Representation k (Γ ℚ) V) g) = LinearMap.det (ρ g) from rfl, hdg]
          rfl
  -- (2) hence the determinant character on `u.range` takes only the
  -- values `±1` …
  have h2ne : (2 : Dickson.K 3) ≠ 0 := by
    intro h
    have h3ne : ((2 : ℕ) : Dickson.K 3) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (Dickson.K 3) 3]
      omega
    exact h3ne (by push_cast; exact h)
  have hDpm : ∀ x : u.range,
      (Matrix.GeneralLinearGroup.det).comp u.range.subtype x = 1 ∨
      (Matrix.GeneralLinearGroup.det).comp u.range.subtype x = -1 := by
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := hx
    rcases padic_three_ringHom_pm_one ((e : AlgebraicClosure k →+* Dickson.K 3).comp
        ((algebraMap k (AlgebraicClosure k)).comp (algebraMap ℤ_[3] k)))
        (cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv) with h | h
    · left
      apply Units.ext
      rw [Units.val_one]
      exact (hdet_val g).trans h
    · right
      apply Units.ext
      rw [Units.val_neg, Units.val_one]
      exact (hdet_val g).trans h
  -- … and attains `−1` at complex conjugation
  have hDneg : ∃ x : u.range,
      (Matrix.GeneralLinearGroup.det).comp u.range.subtype x = -1 := by
    obtain ⟨c, -, hcχ⟩ := exists_conj_cyclotomicCharacter_three
    refine ⟨⟨u c, ⟨c, rfl⟩⟩, ?_⟩
    apply Units.ext
    rw [Units.val_neg, Units.val_one]
    exact (hdet_val c).trans (by rw [hcχ, map_neg, map_one])
  -- (3) so the determinant-one part of `u.range` has index exactly 2
  have hone_ne : (1 : (Dickson.K 3)ˣ) ≠ -1 := by
    intro h
    apply h2ne
    have hval := congrArg Units.val h
    rw [Units.val_one, Units.val_neg, Units.val_one] at hval
    linear_combination hval
  have hDrange : (((Matrix.GeneralLinearGroup.det).comp u.range.subtype).range :
      Set (Dickson.K 3)ˣ) = {1, -1} := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      rcases hDpm x with h | h <;> simp [h]
    · rintro y (rfl | rfl)
      · exact ⟨1, map_one _⟩
      · exact hDneg
  have hSidx : ((Matrix.GeneralLinearGroup.det).comp u.range.subtype).ker.index = 2 := by
    rw [Subgroup.index_ker, ← SetLike.coe_sort_coe, hDrange, Nat.card_coe_set_eq,
      Set.ncard_pair hone_ne]
  -- (4) the projection of `u.range` onto `π.range`
  have hmemπ : ∀ x : u.range,
      (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (Dickson.K 3)))).comp
        u.range.subtype x ∈ π.range := by
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := hx
    exact ⟨g, hπ g⟩
  have hψsurj : Function.Surjective
      (MonoidHom.codRestrict ((QuotientGroup.mk' (Subgroup.center
        (GL (Fin 2) (Dickson.K 3)))).comp u.range.subtype) π.range hmemπ) := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := hy
    exact ⟨⟨u g, ⟨g, rfl⟩⟩, Subtype.ext (hπ g).symm⟩
  -- (5) assemble via the counting core
  refine card_ge_48_of_index_two_kernel _ hSidx _ hψsurj
    (dickson_exceptional_subgroup_card hcase) ?_
  -- the lift obstruction: an element of the determinant-one part over
  -- an involution of `π.range` cannot square to `1`
  intro s hsS hord2 hcontra
  have hψne : MonoidHom.codRestrict ((QuotientGroup.mk' (Subgroup.center
      (GL (Fin 2) (Dickson.K 3)))).comp u.range.subtype) π.range hmemπ s ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord2
    omega
  have hcen : (s : GL (Fin 2) (Dickson.K 3)) ∉
      Subgroup.center (GL (Fin 2) (Dickson.K 3)) := by
    intro hc
    apply hψne
    apply Subtype.ext
    show QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (Dickson.K 3)))
      (s : GL (Fin 2) (Dickson.K 3)) = 1
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hc
  have hdet1 : Matrix.GeneralLinearGroup.det
      ((s : GL (Fin 2) (Dickson.K 3))) = 1 := hsS
  have hsq := gl2_sq_ne_one_of_notMem_center h2ne _ hdet1 hcen
  apply hsq
  have hval := congrArg (fun w : u.range => (w : GL (Fin 2) (Dickson.K 3))) hcontra
  simpa using hval

/-- **The kernel field of the matrix image** (sorry node — the
Galois-correspondence bookkeeping of the field cut, isolated
2026-07-23): the matrix form `u` of a mod-3 hardly ramified
representation cuts out a finite Galois number field `K` inside
`ℚᵃˡᵍ` — the fixed field of `ker u` — with
`Gal(K/ℚ) ≃ Γ ℚ / ker u ≃ u.range`, recorded by
`K.fixingSubgroup = u.ker` and `[K : ℚ] = #u.range`. Intended proof
(pure infinite-Galois bookkeeping, as in
`open_normal_subgroup_eq_top_of_inertia_le`): `ker ρ ≤ ker u` (`hu`
sends `ρ g = 1` to the identity matrix), and `ker ρ` is open
(`isOpen_setOf_galoisRep_eq_one`, `V` finite), so `ker u` is an open
(hence closed) normal subgroup; `K := fixedField (ker u)` recovers
`fixingSubgroup K = ker u` by the infinite Galois correspondence
(`InfiniteGalois.fixingSubgroup_fixedField`), is finite-dimensional
(`isOpen_iff_finite`) and Galois (`normal_iff_isGalois`); and
`[K : ℚ] = #(K ≃ₐ[ℚ] K)` (`IsGalois.card_aut_eq_finrank`)
`= #(Γ ℚ / ker u)` (restriction to `K` is surjective with kernel
`fixingSubgroup K`) `= #u.range` (first isomorphism theorem). -/
theorem exists_kernel_field_of_matrixRange {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (_hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField K),
      IsGalois ℚ K ∧ K.fixingSubgroup = u.ker ∧
      Module.finrank ℚ K = Nat.card u.range := by
  classical
  haveI hfinV : Finite V := Module.finite_of_finite k
  -- `ker ρ ≤ ker u`: the matrix transport of the identity is the identity
  have htriv : ∀ g : Γ ℚ, ρ g = 1 → u g = 1 := by
    intro g hg
    apply Units.ext
    rw [Units.val_one, hu g]
    have h1 : (Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g =
        ((MonoidHomClass.toMonoidHom ρ :
          Representation k (Γ ℚ) V) g).baseChange (AlgebraicClosure k) := rfl
    have h2 : (MonoidHomClass.toMonoidHom ρ :
        Representation k (Γ ℚ) V) g = 1 := hg
    rw [h1, h2, Module.End.one_eq_id, LinearMap.baseChange_id,
      ← Module.End.one_eq_id, LinearMap.toMatrix_one,
      Matrix.map_one _ (map_zero e) (map_one e)]
  -- `ker u` is an open (hence closed) normal subgroup
  let Kρ : Subgroup (Γ ℚ) :=
    { carrier := {g | ρ g = 1}
      one_mem' := map_one ρ
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) = 1
        rw [map_mul, ha, hb, mul_one]
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ = 1
        have h1 : ρ a⁻¹ * ρ a = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h1 }
  have hKρ_open : IsOpen (Kρ : Set (Γ ℚ)) :=
    isOpen_setOf_galoisRep_eq_one ρ hfinV
  have hker : Kρ ≤ u.ker := fun g hg => MonoidHom.mem_ker.mpr (htriv g hg)
  have hopen : IsOpen (u.ker : Set (Γ ℚ)) :=
    Subgroup.isOpen_mono hker hKρ_open
  have hclosed : IsClosed (u.ker : Set (Γ ℚ)) :=
    Subgroup.isClosed_of_isOpen u.ker hopen
  -- the fixed field of `ker u`
  haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  haveI hacQ : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    ⟨inferInstance, halgQ⟩
  haveI hnormQ : Normal ℚ (AlgebraicClosure ℚ) :=
    IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI hsepQ : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hgalQ : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  set K : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.fixedField (E := AlgebraicClosure ℚ) u.ker
  have hfix : K.fixingSubgroup = u.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨u.ker, hclosed⟩
  haveI hfd : FiniteDimensional ℚ K :=
    (InfiniteGalois.isOpen_iff_finite K).mp (by rw [hfix]; exact hopen)
  haveI hnorm : u.ker.Normal := u.normal_ker
  haveI hgalK : IsGalois ℚ K := (InfiniteGalois.normal_iff_isGalois K).mp
    (by rw [hfix]; exact hnorm)
  haveI : NumberField K := ⟨⟩
  -- the degree: `[K : ℚ] = #Gal(K/ℚ) = #(Γ ℚ / ker u) = #u.range`
  have e1 : (Γ ℚ) ⧸ u.ker ≃* ((IntermediateField.fixedField
      ((⟨u.ker, hclosed⟩ : ClosedSubgroup (Γ ℚ)) : Subgroup (Γ ℚ))) ≃ₐ[ℚ]
        (IntermediateField.fixedField
          ((⟨u.ker, hclosed⟩ : ClosedSubgroup (Γ ℚ)) : Subgroup (Γ ℚ)))) :=
    InfiniteGalois.normalAutEquivQuotient ⟨u.ker, hclosed⟩
  have e2 : (Γ ℚ) ⧸ u.ker ≃* u.range :=
    QuotientGroup.quotientKerEquivRange u
  have hcard1 : Nat.card (K ≃ₐ[ℚ] K) = Module.finrank ℚ K :=
    IsGalois.card_aut_eq_finrank ℚ K
  refine ⟨K, inferInstance, inferInstance, hfix, ?_⟩
  rw [← hcard1]
  exact ((Nat.card_congr e1.toEquiv).symm).trans (Nat.card_congr e2.toEquiv)

/-- **Complex conjugation at a real place** (PROVEN 2026-07-23 — the
embedding plumbing of the oddness argument; a `ρ`-free statement about
number fields): a subfield `K ⊆ ℚᵃˡᵍ` that is NOT totally complex
admits an element `c ∈ Γ ℚ` fixing `K` pointwise on which the 3-adic
cyclotomic character is `−1`. Proof: a real infinite place of `K` is
induced by a real embedding `φ : K → ℂ`; extend `φ` to `ψ : ℚᵃˡᵍ → ℂ`
THROUGH `K` (`IsAlgClosed.lift` over the algebraic extension
`K ⊆ ℚᵃˡᵍ`); complex conjugation restricts along `ψ` to the (normal)
image (`AlgEquiv.restrictNormal` with the `ψ`-algebra structure on
`ℂ`), giving `c ∈ Γ ℚ` with `ψ ∘ c = conj ∘ ψ`; `c` fixes `K`
pointwise (`ψ(K) = φ(K) ⊆ ℝ`) and is an involution fixing no
primitive cube root of unity (they are not real), so `χ₃(c)² = 1` and
`χ₃(c) ≠ 1` in the domain `ℤ_[3]`, forcing `χ₃(c) = −1` — the
argument of `exists_conj_cyclotomicCharacter_three` relative to the
place. -/
theorem exists_conj_fixingSubgroup_of_not_isTotallyComplex
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (hK : ¬ NumberField.IsTotallyComplex K) :
    ∃ c : Γ ℚ, c ∈ K.fixingSubgroup ∧
      ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 c.toRingEquiv :
        ℤ_[3]ˣ) : ℤ_[3]) = -1 := by
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  classical
  -- a real infinite place of `K` gives a real complex embedding
  obtain ⟨w, hw⟩ : ∃ w : NumberField.InfinitePlace K, w.IsReal := by
    rw [NumberField.isTotallyComplex_iff] at hK
    push Not at hK
    obtain ⟨w, hw⟩ := hK
    exact ⟨w, (NumberField.InfinitePlace.isReal_or_isComplex w).resolve_right hw⟩
  set φ : K →+* ℂ := w.embedding
  have hφreal : ∀ y : K, (starRingEnd ℂ) (φ y) = φ y := by
    intro y
    have h1 : NumberField.ComplexEmbedding.IsReal φ :=
      NumberField.InfinitePlace.isReal_iff.mp hw
    exact RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.mp h1) y
  -- extend `φ` to `ψ : ℚᵃˡᵍ → ℂ` THROUGH `K` (`IsAlgClosed.lift`)
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  letI : Algebra K ℂ := φ.toAlgebra
  haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  haveI halgK : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    have h1 : algebraMap ℚ ℂ q = (q : ℂ) := eq_ratCast _ q
    have h2 : φ (algebraMap ℚ K q) = (q : ℂ) :=
      eq_ratCast (φ.comp (algebraMap ℚ K)) q
    rw [h1, ← h2]
    rfl
  set ψK : AlgebraicClosure ℚ →ₐ[K] ℂ := IsAlgClosed.lift
  set ψ : AlgebraicClosure ℚ →+* ℂ := (ψK.restrictScalars ℚ).toRingHom
  have hψK : ∀ y : K, ψ (algebraMap K (AlgebraicClosure ℚ) y) = φ y :=
    fun y => ψK.commutes y
  -- pull complex conjugation back along `ψ` (the image is normal)
  letI : Algebra (AlgebraicClosure ℚ) ℂ := ψ.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
    IsScalarTower.of_algebraMap_eq fun q => by
      have h1 : algebraMap ℚ ℂ q = (q : ℂ) := eq_ratCast _ q
      have h2 : ψ (algebraMap ℚ (AlgebraicClosure ℚ) q) = (q : ℂ) :=
        eq_ratCast (ψ.comp (algebraMap ℚ (AlgebraicClosure ℚ))) q
      rw [h1, ← h2]
      rfl
  haveI hacQ : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, halgQ⟩
  haveI hnormQ : Normal ℚ (AlgebraicClosure ℚ) :=
    IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  set γ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  set c : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ) :=
    AlgEquiv.restrictNormal γ (AlgebraicClosure ℚ)
  have hcomm : ∀ z : AlgebraicClosure ℚ, ψ (c z) = (starRingEnd ℂ) (ψ z) :=
    fun z => AlgEquiv.restrictNormal_commutes γ (AlgebraicClosure ℚ) z
  have hψinj : Function.Injective ψ := ψ.injective
  refine ⟨c, ?_, ?_⟩
  · -- `c` fixes `K` pointwise: `ψ` maps `K` into `ℝ`
    intro y
    apply hψinj
    show ψ (c (algebraMap K (AlgebraicClosure ℚ) y)) =
      ψ (algebraMap K (AlgebraicClosure ℚ) y)
    rw [hcomm, hψK, hφreal]
  · -- `χ₃(c) = −1`: `c` is an involution moving the cube roots of unity
    have hc2 : c * c = 1 := by
      refine AlgEquiv.ext fun z => ?_
      apply hψinj
      show ψ (c (c z)) = ψ ((1 : (AlgebraicClosure ℚ) ≃ₐ[ℚ]
        (AlgebraicClosure ℚ)) z)
      rw [hcomm, hcomm, Complex.conj_conj]
      rfl
    set t : ℤ_[3] :=
      ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 c.toRingEquiv :
        ℤ_[3]ˣ) : ℤ_[3])
    have hsq : t * t = 1 := by
      have hmul : (c * c).toRingEquiv = c.toRingEquiv * c.toRingEquiv := rfl
      have hone : ((1 : Γ ℚ).toRingEquiv) = 1 := rfl
      have h := congrArg (fun g => ((cyclotomicCharacter
        (AlgebraicClosure ℚ) 3 g : ℤ_[3]ˣ) : ℤ_[3]))
        (hmul.symm.trans (((by rw [hc2]; rfl :
          (c * c).toRingEquiv = (1 : Γ ℚ).toRingEquiv)).trans hone))
      simpa [map_mul] using h
    rcases mul_self_eq_one_iff.mp hsq with ht1 | htm1
    swap
    · exact htm1
    -- rule out `t = 1`: `c` would fix a primitive cube root of unity
    exfalso
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure ℚ) 3
    have hfix : c.toRingEquiv ζ = ζ := by
      have hspec := cyclotomicCharacter.spec 3 (n := 1) c.toRingEquiv ζ
        (by rw [pow_one]; exact hζ.pow_eq_one)
      rw [hspec, show (cyclotomicCharacter (AlgebraicClosure ℚ) 3
        c.toRingEquiv).val = t from rfl, ht1, map_one]
      rw [show ((1 : ZMod (3 ^ 1)).val) = 1 from rfl, pow_one]
    -- so `ψ ζ` is a REAL primitive cube root of unity in `ℂ`
    set z : ℂ := ψ ζ with hzdef
    have hzconj : (starRingEnd ℂ) z = z := by
      rw [hzdef, ← hcomm, show c ζ = c.toRingEquiv ζ from rfl, hfix]
    have hzprim : IsPrimitiveRoot z 3 := hζ.map_of_injective hψinj
    have hzre : ((z.re : ℝ) : ℂ) = z := Complex.conj_eq_iff_re.mp hzconj
    have hz3 : z ^ 3 = 1 := hzprim.pow_eq_one
    have hre3 : (z.re : ℝ) ^ 3 = 1 := by
      have h1 : (((z.re : ℝ) ^ 3 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        push_cast
        rw [hzre, hz3]
      exact_mod_cast h1
    have hre1 : (z.re : ℝ) = 1 := by
      nlinarith [sq_nonneg (z.re - 1), sq_nonneg (z.re + 1)]
    exact hzprim.ne_one (by norm_num) (by rw [← hzre, hre1]; norm_num)

set_option backward.isDefEq.respectTransparency false in
/-- **The kernel field is totally complex** (PROVEN 2026-07-23 — via
the conjugation-at-a-real-place leaf
`exists_conj_fixingSubgroup_of_not_isTotallyComplex` above, now
itself proven): the number field cut out by the
kernel of the matrix form of a mod-3 hardly ramified representation
has no real place. The proven reduction: were `K` not totally
complex, the leaf would produce `c ∈ fixingSubgroup K = ker u` with
`χ₃(c) = −1`; but the determinant of `u c` is the image in
`Dickson.K 3` of `χ₃(c)` (`hρ.det` transported along `hu` and
`LinearMap.det_baseChange`, as in the two-element determinant image
argument of `card_matrixRange_ge_of_exceptional`), so `u c = 1`
forces `1 = −1` in `Dickson.K 3` — impossible in characteristic
`3`. -/
theorem isTotallyComplex_of_kernel_field {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] (hfix : K.fixingSubgroup = u.ker) :
    NumberField.IsTotallyComplex K := by
  classical
  by_contra hK
  obtain ⟨c, hcfix, hcχ⟩ :=
    exists_conj_fixingSubgroup_of_not_isTotallyComplex K hK
  -- `c` kills the matrix form
  have hcker : u c = 1 := by
    have h1 : c ∈ u.ker := by
      rw [← hfix]
      exact hcfix
    exact MonoidHom.mem_ker.mp h1
  -- `2 ≠ 0` in `𝔽̄₃`
  have h2ne : (2 : Dickson.K 3) ≠ 0 := by
    intro h
    have h3ne : ((2 : ℕ) : Dickson.K 3) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (Dickson.K 3) 3]
      omega
    exact h3ne (by push_cast; exact h)
  -- the determinant of `u c` is the image of `χ₃ c`
  have hdet_val :
      ((Matrix.GeneralLinearGroup.det (u c) : (Dickson.K 3)ˣ) : Dickson.K 3) =
        ((e : AlgebraicClosure k →+* Dickson.K 3).comp
          ((algebraMap k (AlgebraicClosure k)).comp (algebraMap ℤ_[3] k)))
          ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 c.toRingEquiv :
            ℤ_[3]ˣ) : ℤ_[3]) := by
    calc ((Matrix.GeneralLinearGroup.det (u c) : (Dickson.K 3)ˣ) : Dickson.K 3)
        = ((u c : GL (Fin 2) (Dickson.K 3)) :
            Matrix (Fin 2) (Fin 2) (Dickson.K 3)).det := rfl
      _ = ((LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
            (MonoidHomClass.toMonoidHom ρ)) c)).map e).det := by rw [hu c]
      _ = e ((LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
            (MonoidHomClass.toMonoidHom ρ)) c)).det) :=
          (RingEquiv.map_det e _).symm
      _ = e (LinearMap.det ((Slop.OddRep.baseChange (AlgebraicClosure k)
            (MonoidHomClass.toMonoidHom ρ)) c)) := by rw [LinearMap.det_toMatrix]
      _ = e (algebraMap k (AlgebraicClosure k)
            (LinearMap.det ((MonoidHomClass.toMonoidHom ρ :
              Representation k (Γ ℚ) V) c))) := by
          rw [show (Slop.OddRep.baseChange (AlgebraicClosure k)
              (MonoidHomClass.toMonoidHom ρ)) c =
            ((MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) c).baseChange
              (AlgebraicClosure k) from rfl, LinearMap.det_baseChange]
      _ = _ := by
          have hdg := hρ.det c
          rw [GaloisRep.det_apply] at hdg
          rw [show LinearMap.det ((MonoidHomClass.toMonoidHom ρ :
              Representation k (Γ ℚ) V) c) = LinearMap.det (ρ c) from rfl, hdg]
          rfl
  -- `u c = 1` forces `1 = −1` in `𝔽̄₃`
  rw [hcker, map_one, Units.val_one, hcχ, map_neg, map_one] at hdet_val
  exact h2ne (by linear_combination hdet_val)

/-- **Unramifiedness of the kernel field outside `{2, 3}`** (PROVEN
2026-07-23): the number field cut out by the kernel of the matrix
form of a mod-3 hardly ramified representation is unramified at every
prime `p ∉ {2, 3}`, stated as `p ∤ d_K`. Proof: at `p ∉ {2, 3}` the
representation is unramified (`hρ.isUnramified`), so the local
inertia at `p` lands in `ker ρ ≤ ker u = K.fixingSubgroup` (the
matrix transport `htriv` of `exists_kernel_field_of_matrixRange`); by
the inertia dictionary `isUnramifiedAt_of_inertia_le_fixingSubgroup`
of `MazurTorsion` every prime of `𝓞 K` over `p` is unramified, and an
everywhere-unramified prime does not divide the discriminant
(`NumberField.not_dvd_discr_iff_forall_mem`). -/
theorem kernel_field_not_dvd_discr {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] (hfix : K.fixingSubgroup = u.ker)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ ((p : ℤ) ∣ NumberField.discr K) := by
  classical
  -- the matrix transport of the identity: `ker ρ ≤ ker u`
  have htriv : ∀ g : Γ ℚ, ρ g = 1 → u g = 1 := by
    intro g hg
    apply Units.ext
    rw [Units.val_one, hu g]
    have h1 : (Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g =
        ((MonoidHomClass.toMonoidHom ρ :
          Representation k (Γ ℚ) V) g).baseChange (AlgebraicClosure k) := rfl
    have h2 : (MonoidHomClass.toMonoidHom ρ :
        Representation k (Γ ℚ) V) g = 1 := hg
    rw [h1, h2, Module.End.one_eq_id, LinearMap.baseChange_id,
      ← Module.End.one_eq_id, LinearMap.toMatrix_one,
      Matrix.map_one _ (map_zero e) (map_one e)]
  -- the local inertia image at `p` kills `u` (through `hρ.isUnramified`)
  have hunram : ∀ σ ∈ localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat,
      u (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
    intro σ hσ
    apply htriv
    have h1 : (ρ.toLocal hp.toHeightOneSpectrumRingOfIntegersRat) σ = 1 :=
      (hρ.isUnramified p hp ⟨hp2, hp3⟩).localInertiaGroup_le hσ
    rw [GaloisRep.toLocal_apply] at h1
    convert h1 using 4
    exact Subsingleton.elim _ _
  -- … so the mapped local inertia fixes `K`
  have hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
      (localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat)
      ≤ K.fixingSubgroup := by
    rintro g ⟨σ, hσ, rfl⟩
    rw [hfix]
    exact MonoidHom.mem_ker.mpr (hunram σ hσ)
  -- every prime of `𝓞 K` over `p` is unramified, so `p ∤ d_K`
  have hpZ : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  rw [NumberField.not_dvd_discr_iff_forall_mem K
    (NumberField.RingOfIntegers K) hpZ]
  intro P hP hmem
  haveI := hP
  exact isUnramifiedAt_of_inertia_le_fixingSubgroup K hp hle P
    (by exact_mod_cast hmem)

open UniqueFactorizationMonoid in
/-- **The discriminant exponent from per-prime different-exponent
bounds** (sorry node, isolated 2026-07-23 from the two discriminant
exponent leaves below): for a number field `K`, a rational prime `p`
and weights `a, b`, if every prime `Q` of `𝓞 K` over `p` satisfies
`a·d_Q ≤ b·e_Q` for its different exponent `d_Q` — stated
multiplicity-free: every `d` with `Q^d ∣ 𝔡_{K/ℚ}` has
`a·d ≤ b·e(Q∣p)` — then `a·v_p(d_K) ≤ b·[K:ℚ]`. Intended proof (norm
bookkeeping, no new arithmetic): `N(𝔡_{K/ℚ}) = |d_K|`
(`NumberField.absNorm_differentIdeal`), so
`v_p(d_K) = Σ_{Q∣p} f_Q·d_Q` by multiplicativity of `Ideal.absNorm`
along the factorization of the different into primes, whence
`a·v_p(d_K) = Σ_{Q∣p} f_Q·(a·d_Q) ≤ b·Σ_{Q∣p} f_Q·e_Q = b·[K:ℚ]`
(`Ideal.sum_ramification_inertia`). PROVEN 2026-07-23 along exactly
that route: the different is factored into `normalizedFactors`, the
norm is pushed through the product (`map_prod`), `Nat.factorization`
distributes over it, primes not over `p` contribute `0`
(`Ideal.exists_isMaximal_dvd_of_dvd_absNorm'`), primes over `p`
contribute `d_Q·f_Q` (`Ideal.absNorm_eq_pow_inertiaDeg'`), and the
per-prime hypothesis plus `Ideal.sum_ramification_inertia` close. -/
theorem discr_factorization_le_of_forall_differentIdeal_pow_dvd
    (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) (a b : ℕ)
    (h : ∀ Q : Ideal (NumberField.RingOfIntegers K), Q.IsPrime →
      ((p : NumberField.RingOfIntegers K) ∈ Q) → ∀ d : ℕ,
      Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K) →
      a * d ≤ b * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) Q) :
    a * (NumberField.discr K).natAbs.factorization p ≤
      b * Module.finrank ℚ K := by
  classical
  set R := NumberField.RingOfIntegers K with hRdef
  set D := differentIdeal ℤ R with hDdef
  have hD0 : D ≠ 0 := by
    rw [hDdef, Submodule.zero_eq_bot]
    exact differentIdeal_ne_bot
  have hnorm : Ideal.absNorm D = (NumberField.discr K).natAbs :=
    NumberField.absNorm_differentIdeal K R
  rw [← hnorm]
  -- the factorization of the different into primes
  have hDprod : D = ∏ Q ∈ (normalizedFactors D).toFinset,
      Q ^ (normalizedFactors D).count Q := by
    conv_lhs => rw [← associated_iff_eq.mp (prod_normalizedFactors hD0)]
    exact Finset.prod_multiset_count _
  have hQprime : ∀ Q ∈ (normalizedFactors D).toFinset, Prime Q := fun Q hQ =>
    prime_of_normalized_factor Q (Multiset.mem_toFinset.mp hQ)
  have habs0 : ∀ Q ∈ (normalizedFactors D).toFinset,
      Ideal.absNorm Q ≠ 0 := fun Q hQ => by
    rw [Ne, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
    exact (hQprime Q hQ).ne_zero
  -- multiplicativity of the norm along the factorization
  have hnormD : Ideal.absNorm D = ∏ Q ∈ (normalizedFactors D).toFinset,
      Ideal.absNorm Q ^ (normalizedFactors D).count Q := by
    conv_lhs => rw [hDprod]
    rw [map_prod]
    exact Finset.prod_congr rfl fun Q _ => map_pow _ _ _
  -- the `p`-adic valuation of the norm, term by term
  have hfact : (Ideal.absNorm D).factorization p
      = ∑ Q ∈ (normalizedFactors D).toFinset,
        (normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p := by
    rw [hnormD, Nat.factorization_prod (fun Q hQ => pow_ne_zero _ (habs0 Q hQ)),
      Finset.sum_apply']
    exact Finset.sum_congr rfl fun Q hQ => by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  -- primes not containing `p` contribute nothing
  have hmem_of_ne : ∀ Q ∈ (normalizedFactors D).toFinset,
      (normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p ≠ 0 →
      ((p : ℕ) : R) ∈ Q := by
    intro Q hQF hne
    by_contra hpnot
    apply hne
    rw [Nat.mul_eq_zero]
    right
    by_contra hne2
    have hdvd : p ∣ Ideal.absNorm Q := Nat.dvd_of_factorization_pos hne2
    obtain ⟨P, hPmax, hPunder, hPdvd⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp Q hdvd
    have hQpr : Q.IsPrime := Ideal.isPrime_of_prime (hQprime Q hQF)
    have hQ0 : Q ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact (hQprime Q hQF).ne_zero
    have hQP : Q = P := (hQpr.isMaximal hQ0).eq_of_le hPmax.ne_top
      (Ideal.le_of_dvd hPdvd)
    apply hpnot
    have hmemP : algebraMap ℤ R ((p : ℕ) : ℤ) ∈ P := by
      have hu : ((p : ℕ) : ℤ) ∈ P.under ℤ := by
        rw [hPunder]
        exact Ideal.mem_span_singleton_self _
      exact hu
    rw [map_natCast] at hmemP
    rw [hQP]
    exact hmemP
  have hsum : (Ideal.absNorm D).factorization p =
      ∑ Q ∈ (normalizedFactors D).toFinset.filter (fun Q => ((p : ℕ) : R) ∈ Q),
        (normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p := by
    rw [hfact]
    exact (Finset.sum_filter_of_ne hmem_of_ne).symm
  -- the setup at `p`
  have hpZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hspan0 : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI hspanMax : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    (((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      hpZ).isMaximal hspan0)
  have hmain := Ideal.sum_ramification_inertia R ℚ K hspan0
  -- the per-prime bound
  have hle : ∀ Q ∈ (normalizedFactors D).toFinset.filter
      (fun Q => ((p : ℕ) : R) ∈ Q),
      a * ((normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p) ≤
      b * (Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q *
        Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q) := by
    intro Q hQ
    obtain ⟨hQF, hpQ⟩ := Finset.mem_filter.mp hQ
    have hQpr : Q.IsPrime := Ideal.isPrime_of_prime (hQprime Q hQF)
    haveI := hQpr
    haveI hlies : Q.LiesOver (Ideal.span {((p : ℕ) : ℤ)}) :=
      (Ideal.liesOver_span_iff hQpr.ne_top hpZ).mpr (by exact_mod_cast hpQ)
    have hf : (Ideal.absNorm Q).factorization p =
        Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q := by
      rw [Ideal.absNorm_eq_pow_inertiaDeg' Q hp, hp.factorization_pow,
        Finsupp.single_eq_same]
    have hdvd : Q ^ (normalizedFactors D).count Q ∣ D := by
      conv_rhs => rw [hDprod]
      exact Finset.dvd_prod_of_mem _ hQF
    have hcntle : a * (normalizedFactors D).count Q ≤
        b * Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q :=
      h Q hQpr hpQ ((normalizedFactors D).count Q) hdvd
    calc a * ((normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p)
        = (a * (normalizedFactors D).count Q) *
          (Ideal.absNorm Q).factorization p := by ring
      _ ≤ (b * Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q) *
          (Ideal.absNorm Q).factorization p :=
        Nat.mul_le_mul_right _ hcntle
      _ = b * (Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q *
          Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q) := by
        rw [hf]; ring
  have hsub : (normalizedFactors D).toFinset.filter
      (fun Q => ((p : ℕ) : R) ∈ Q) ⊆
      IsDedekindDomain.primesOverFinset (Ideal.span {((p : ℕ) : ℤ)}) R := by
    intro Q hQ
    obtain ⟨hQF, hpQ⟩ := Finset.mem_filter.mp hQ
    have hQpr : Q.IsPrime := Ideal.isPrime_of_prime (hQprime Q hQF)
    rw [IsDedekindDomain.mem_primesOverFinset_iff hspan0]
    exact ⟨hQpr, (Ideal.liesOver_span_iff hQpr.ne_top hpZ).mpr
      (by exact_mod_cast hpQ)⟩
  rw [hsum, Finset.mul_sum]
  calc ∑ Q ∈ (normalizedFactors D).toFinset.filter
        (fun Q => ((p : ℕ) : R) ∈ Q),
        a * ((normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p)
      ≤ ∑ Q ∈ (normalizedFactors D).toFinset.filter
        (fun Q => ((p : ℕ) : R) ∈ Q),
        b * (Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q *
          Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q) :=
      Finset.sum_le_sum hle
    _ ≤ ∑ Q ∈ IsDedekindDomain.primesOverFinset
          (Ideal.span {((p : ℕ) : ℤ)}) R,
        b * (Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q *
          Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q) :=
      Finset.sum_le_sum_of_subset hsub
    _ = b * Module.finrank ℚ K := by rw [← Finset.mul_sum, hmain]

open Module in
/-- **Nonvanishing of the trace form of a tame local algebra** (PROVEN
2026-07-23; the residue-theoretic core of the tame different bound
below): the trace form of a finite local algebra `C` over a field `F`
is nonzero as soon as the residue extension is separable and the
residue-field dimension of `C` is invertible in `F` (the tame case).
Proof: a Cohen-style multiplicative section `C ⧸ m →ₐ[F] C` (formal
smoothness of the separable residue extension against the nilpotent
maximal ideal, `Algebra.FormallySmooth.lift`) turns `C` into a
`C ⧸ m`-vector space, and transitivity of the trace evaluates the
trace of a residue scalar `y` as `n • Tr_{(C⧸m)/F}(y)` with
`n = dim_{C⧸m} C`, nonzero for suitable `y` because the separable
residue trace is nonzero (`Algebra.trace_ne_zero`). -/
lemma exists_trace_ne_zero_of_isNilpotent
    (F C : Type*) [Field F] [CommRing C] [Algebra F C] [Module.Finite F C]
    (m : Ideal C) (hm : IsNilpotent m) [hmax : m.IsMaximal]
    [Algebra.IsSeparable F (C ⧸ m)]
    (hd : ∀ n : ℕ, finrank F C = finrank F (C ⧸ m) * n → (n : F) ≠ 0) :
    ∃ w : C, Algebra.trace F C w ≠ 0 := by
  classical
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (C ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m).toLinearMap
      Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ : ∃ y : C ⧸ m, Algebra.trace F (C ⧸ m) y ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero F (C ⧸ m)
  -- the Cohen multiplicative section
  haveI : Algebra.FormallySmooth F (C ⧸ m) := by
    haveI := Algebra.FormallyEtale.of_isSeparable F (C ⧸ m)
    infer_instance
  let σ : (C ⧸ m) →ₐ[F] C :=
    Algebra.FormallySmooth.lift m hm (AlgHom.id F (C ⧸ m))
  letI : Algebra (C ⧸ m) C := σ.toAlgebra
  haveI : IsScalarTower F (C ⧸ m) C :=
    IsScalarTower.of_algebraMap_eq' σ.comp_algebraMap.symm
  haveI : Module.Finite (C ⧸ m) C :=
    Module.Finite.of_restrictScalars_finite F _ _
  refine ⟨algebraMap (C ⧸ m) C y, fun h0 => ?_⟩
  rw [← Algebra.trace_trace (S := C ⧸ m), Algebra.trace_algebraMap,
    map_nsmul, nsmul_eq_mul] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hd _ (Module.finrank_mul_finrank F (C ⧸ m) C).symm h1
  · exact hy h1

open UniqueFactorizationMonoid in
/-- **The tame different bound** (PROVEN 2026-07-23; Serre, *Corps
Locaux* III §6 Prop. 13 / Neukirch III.2.6): if the ramification index
`e = e(Q∣p)` of a prime `Q` of `𝓞 K` over the rational prime `p` is
not divisible by `p` (tame ramification — the residue extension is an
extension of finite fields, hence automatically separable), then the
different exponent of `Q` is at most `e − 1`, stated as `Q^e ∤ 𝔡_{K/ℚ}`
(mathlib has the matching lower half `pow_sub_one_dvd_differentIdeal`).
Proof: write `pO_K = Q^e · J` exactly (`Ideal.eq_prime_pow_mul_coprime`
plus the `normalizedFactors`-count characterization of `e`); the trace
form of the tame factor `O_K ⧸ Q^e` over `𝔽_p` is nonzero
(`exists_trace_ne_zero_of_isNilpotent`, with `dim = e·f` by
`Ideal.Factors.finrank_pow_ramificationIdx` and `p ∤ e`), so the CRT
lift of a trace-nonzero element supported on the `Q^e`-component has
`intTrace ∉ (p)`, and `not_dvd_differentIdeal_of_intTrace_not_mem`
closes. -/
theorem not_pow_ramificationIdx_dvd_differentIdeal
    (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : (p : NumberField.RingOfIntegers K) ∈ Q)
    (htame : ¬ (p ∣ Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) Q)) :
    ¬ Q ^ Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) Q ∣
      differentIdeal ℤ (NumberField.RingOfIntegers K) := by
  classical
  set R := NumberField.RingOfIntegers K with hRdef
  haveI := hQ
  -- the setup at `p`
  have hpZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hspan0 : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI hspanMax : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    (((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      hpZ).isMaximal hspan0)
  haveI hlies : Q.LiesOver (Ideal.span {((p : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff hQ.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have hmap0 : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ R) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hspan0
  have hQ0 : Q ≠ ⊥ := ne_bot_of_le_ne_bot hmap0
    (Ideal.map_le_of_le_comap (Q.over_def (Ideal.span {((p : ℕ) : ℤ)})).le)
  haveI hQmax : Q.IsMaximal := hQ.isMaximal hQ0
  set e := Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q with hedef
  have he0 : e ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q hspan0
  -- the exact factorization `map p = Q ^ e * J` with `Q ⊔ J = ⊤`
  obtain ⟨J, hsup, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hmap0 Q
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
    hmap0 hQ hQ0, ← hedef] at hfac
  have hcop : IsCoprime (Q ^ e) J :=
    (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left
  -- residue-quotient algebra structures
  letI : Algebra (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q ^ e) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp (Ideal.le_of_dvd ⟨J, hfac⟩))
  letI : Algebra (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp (Ideal.le_of_dvd
        ⟨Q ^ e, hfac.trans (mul_comm _ _)⟩))
  -- the CRT decomposition of `R ⧸ pR`
  letI ε : (R ⧸ (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ R))
      ≃ₐ[ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}] ((R ⧸ Q ^ e) × R ⧸ J) :=
    { __ := (Ideal.quotEquivOfEq hfac).trans
        (Ideal.quotientMulEquivQuotientProd (Q ^ e) J hcop),
      commutes' := Quotient.ind fun _ => rfl }
  -- the maximal ideal of `R ⧸ Q ^ e` and its residue field
  set m : Ideal (R ⧸ Q ^ e) := Q.map (Ideal.Quotient.mk (Q ^ e)) with hmdef
  have hnilp : IsNilpotent m := ⟨e, by
    rw [hmdef, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_quotient_self]⟩
  letI ε₂ : ((R ⧸ Q ^ e) ⧸ m) ≃+* R ⧸ Q :=
    DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self he0)
  haveI hmmax : m.IsMaximal := Ideal.Quotient.maximal_of_isField m
    (ε₂.toMulEquiv.isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp hQmax))
  letI ε₂ₐ : ((R ⧸ Q ^ e) ⧸ m) ≃ₐ[ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}] (R ⧸ Q) :=
    { __ := ε₂,
      commutes' := fun x => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }
  haveI hsep : Algebra.IsSeparable (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)})
      ((R ⧸ Q ^ e) ⧸ m) := by
    letI : Field (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) := Ideal.Quotient.field _
    letI : Field (R ⧸ Q) := Ideal.Quotient.field Q
    haveI : Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) :=
      Ring.HasFiniteQuotients.finiteQuotient hspan0
    haveI : Module.Finite ℤ (R ⧸ Q) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ Q).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI : Module.Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q) :=
      Module.Finite.of_restrictScalars_finite ℤ _ _
    haveI : Algebra.IsAlgebraic (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact AlgEquiv.Algebra.isSeparable ε₂ₐ.symm
  -- the dimension bookkeeping: `dim_F (R ⧸ Q^e) = e * f`, `dim_F κ = f`
  have hQmemF : Q ∈ (factors ((Ideal.span {((p : ℕ) : ℤ)}).map
      (algebraMap ℤ R))).toFinset := by
    rw [Multiset.mem_toFinset, factors_eq_normalizedFactors, ← Multiset.count_pos,
      ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 hQ hQ0]
    exact Nat.pos_of_ne_zero he0
  have hEF : Module.finrank (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q ^ e) =
      e * Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q :=
    Ideal.Factors.finrank_pow_ramificationIdx
      (Ideal.span {((p : ℕ) : ℤ)}) ⟨Q, hQmemF⟩
  have hkap : Module.finrank (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) ((R ⧸ Q ^ e) ⧸ m) =
      Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q := by
    rw [Ideal.inertiaDeg'_algebraMap]
    exact ε₂ₐ.toLinearEquiv.finrank_eq
  have hf0 : Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q ≠ 0 :=
    Ideal.inertiaDeg'_ne_zero _ _
  -- the tame trace element on `R ⧸ Q ^ e`
  letI : Field (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) := Ideal.Quotient.field _
  haveI : Module.Finite ℤ (R ⧸ Q ^ e) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ (Q ^ e)).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q ^ e) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨w, hw⟩ := exists_trace_ne_zero_of_isNilpotent
    (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q ^ e) m hnilp
    (fun n hn => by
      rw [hEF, hkap, mul_comm e] at hn
      have hne : n = e := Nat.eq_of_mul_eq_mul_left
        (Nat.pos_of_ne_zero hf0) hn.symm
      rw [hne]
      intro h0
      apply htame
      have hzero : (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : ℤ)}))
          ((e : ℕ) : ℤ) = 0 := by
        rw [map_natCast]
        exact h0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hzero
      exact_mod_cast hzero)
  -- the CRT lift of `(w, 0)` and its trace
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (ε.symm (w, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem ℤ (Q ^ e) J hfac.symm
    y ?_ ?_
  · have h2 := congr((ε $hy).2)
    simp only [AlgEquiv.apply_symm_apply] at h2
    simpa [ε, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.quotientMulEquivQuotientProd] using h2
  · haveI : Module.Finite ℤ (R ⧸ J) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ J).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI : Module.Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ J) :=
      Module.Finite.of_restrictScalars_finite ℤ _ _
    rw [← Ideal.Quotient.eq_zero_iff_mem,
      ← Algebra.trace_quotient_eq_of_isDedekindDomain, hy,
      Algebra.trace_eq_of_algEquiv ε.symm (w, 0),
      Algebra.trace_prod_apply]
    simpa using hw

/-- **The quantitative local-to-global inertia transport** (sorry
node, isolated 2026-07-23 as one of the two halves of the
inertia-order leaf below; the strengthening of `MazurTorsion`'s
`exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup` from
"image trivial ⇒ inertia trivial" to "inertia order divides the image
order"): for a Galois number field `K = (ker u)^fix` and a prime `Q`
of `𝓞 K` over `q`, the order of the ideal-inertia subgroup of
`Gal(K/ℚ)` at `Q` divides any multiple `n` of the order of the image
under `u` of the local inertia at `q`. Intended proof (no
representation content — `u` is just a group homomorphism cutting out
`K`): the restriction `Γ ℚ → Gal(K/ℚ)` has kernel
`K.fixingSubgroup = ker u`, so the image of the mapped local inertia
in `Gal(K/ℚ)` has the same order as its image under `u`; the
Minkowski-style embedding `ι : K → M := ℚ_q(ι K)` of
`exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup` transports
the local ramification of `M/ℚ_q` — bounded by the index data of the
local inertia acting through `u` — onto the ideal-inertia of a
distinguished prime `Q₀`, and Galois conjugacy of the primes over `q`
(`Nat.card` of conjugate inertia subgroups agree) moves the bound to
`Q`. -/
theorem inertia_card_dvd_of_map_localInertiaGroup_card_dvd
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K]
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hfix : K.fixingSubgroup = u.ker)
    {q : ℕ} (hq : q.Prime)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : ((q : ℕ) : NumberField.RingOfIntegers K) ∈ Q)
    (n : ℕ)
    (hn : Nat.card (Subgroup.map u
      (Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat))) ∣ n) :
    Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) ∣ n :=
  sorry

/-- **The local inertia image at `2` has order dividing `3`** (sorry
node, isolated 2026-07-23 as the representation-theoretic half of the
inertia-order leaf below; no ideal theory): the image under the
matrix form `u` of the local inertia at `2` is a subgroup of
`GL₂(𝔽̄₃)` of order dividing `3`. Intended content: by
`hρ.isTameAtTwo` the local representation at `2` is upper triangular
with unramified quotient character `δ` (so `δ = 1` on inertia), and
the determinant `χ₃` is unramified at `2` (so `det = 1` on inertia);
hence every inertia element maps to a unipotent matrix fixing the
common flag — an element of the one-parameter group `(𝔽̄₃, +)`, of
cube `1`. Cyclicity (order `1` or `3`, not merely exponent `3`): the
wild inertia at `2` is pro-`2`, so its image in the `3`-group is
trivial, and the image factors through the procyclic tame quotient —
a topologically monogenic group, whose finite exponent-`3` quotients
have order dividing `3`. -/
theorem card_map_localInertiaGroup_at_two_dvd_three {k : Type u} [Finite k]
    [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e) :
    Nat.card (Subgroup.map u
      (Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) ∣ 3 :=
  sorry

/-- **The inertia order at `2` divides `3`** (DECOMPOSED 2026-07-23
into the two sorry nodes above — the quantitative local-to-global
transport `inertia_card_dvd_of_map_localInertiaGroup_card_dvd` (pure
algebraic number theory) and the representation-theoretic image bound
`card_map_localInertiaGroup_at_two_dvd_three` (pure local
representation theory); the glue is proven here): the ideal-inertia
subgroup in `Gal(K/ℚ)` of any prime `Q` of `𝓞 K` above `2` has order
dividing `3`. -/
theorem kernel_field_inertia_card_at_two_dvd_three {k : Type u} [Finite k]
    [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] (hfix : K.fixingSubgroup = u.ker)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : ((2 : ℕ) : NumberField.RingOfIntegers K) ∈ Q) :
    Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) ∣ 3 :=
  inertia_card_dvd_of_map_localInertiaGroup_card_dvd K u hfix
    Nat.prime_two Q hQ hmem 3
    (card_map_localInertiaGroup_at_two_dvd_three V hV hρ b e u hu)

/-- **The Fontaine different bound at `3`, wild case** (sorry node,
isolated 2026-07-23 as the residual core of the Fontaine-at-`3`
per-prime leaf below after the tame case was closed by the proven
tame different bound `not_pow_ramificationIdx_dvd_differentIdeal`):
for a prime `Q` of `𝓞 K` above `3` with `3 ∣ e(Q∣3)` (wild
ramification), the different exponent `d_Q` satisfies
`2·d_Q ≤ 3·e(Q∣3)`. Intended content: flatness (`hρ.isFlat`)
prolongs the local representation at `3` to a finite flat group
scheme over `ℤ₃` killed by `3`, and Fontaine's ramification bound
(the upper-numbering ramification of `ℚ₃(V)/ℚ₃` vanishes above
`1 + 1/(3−1) = 3/2`) bounds the different exponent of the local
field cut out by (a subquotient of) `V` by `(3/2)·e` per prime; `K`
is fixed by `ker u ⊇ ker ρ̄`, so its completion at `Q` sits inside
`ℚ₃(V)` and inherits the bound. (Fontaine, *Il n'y a pas de variété
abélienne sur ℤ*, Invent. Math. 81 (1985), Thm. A; Moon–Taguchi,
Doc. Math. 2003, §2.) -/
theorem kernel_field_differentIdeal_exponent_at_three_wild {k : Type u}
    [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] (hfix : K.fixingSubgroup = u.ker)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : ((3 : ℕ) : NumberField.RingOfIntegers K) ∈ Q) (d : ℕ)
    (hd : Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K))
    (hwild : (3 : ℕ) ∣ Ideal.ramificationIdx' (Ideal.span {((3 : ℕ) : ℤ)}) Q) :
    2 * d ≤ 3 * Ideal.ramificationIdx' (Ideal.span {((3 : ℕ) : ℤ)}) Q :=
  sorry

/-- **The Fontaine different bound at `3`** (DECOMPOSED 2026-07-23:
the tame case `3 ∤ e(Q∣3)` is PROVEN here from the tame different
bound `not_pow_ramificationIdx_dvd_differentIdeal` — `d ≤ e − 1`
gives `2·d ≤ 2·e − 2 ≤ 3·e` outright — leaving the wild case
`3 ∣ e(Q∣3)` as the single sorry node above,
`kernel_field_differentIdeal_exponent_at_three_wild`, which is where
the flatness input `hρ.isFlat` and Fontaine's ramification bound
genuinely enter): the different exponent `d_Q` of any prime `Q` of
`𝓞 K` above `3` in the kernel field of a mod-3 hardly ramified
representation satisfies `2·d_Q ≤ 3·e(Q∣3)`. -/
theorem kernel_field_differentIdeal_exponent_at_three {k : Type u} [Finite k]
    [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] (hfix : K.fixingSubgroup = u.ker)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : ((3 : ℕ) : NumberField.RingOfIntegers K) ∈ Q) (d : ℕ)
    (hd : Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K)) :
    2 * d ≤ 3 * Ideal.ramificationIdx' (Ideal.span {((3 : ℕ) : ℤ)}) Q := by
  by_cases hwild : (3 : ℕ) ∣ Ideal.ramificationIdx' (Ideal.span {((3 : ℕ) : ℤ)}) Q
  · exact kernel_field_differentIdeal_exponent_at_three_wild V hV hρ b e u hu
      K hfix Q hQ hmem d hd hwild
  · -- tame at `3`: the different exponent is at most `e − 1`
    have hnot := not_pow_ramificationIdx_dvd_differentIdeal K 3 Nat.prime_three
      Q hQ hmem hwild
    have hdlt : d < Ideal.ramificationIdx' (Ideal.span {((3 : ℕ) : ℤ)}) Q := by
      by_contra hge
      push Not at hge
      exact hnot ((pow_dvd_pow Q hge).trans hd)
    omega

/-- **The tame discriminant exponent at `2`** (DECOMPOSED 2026-07-23
into the three sorry nodes above — the norm bookkeeping
`discr_factorization_le_of_forall_differentIdeal_pow_dvd`, the tame
different bound `not_pow_ramificationIdx_dvd_differentIdeal` and the
inertia-order leaf `kernel_field_inertia_card_at_two_dvd_three`; the
per-prime glue is proven here): the `2`-adic valuation of the
discriminant of the kernel field of a mod-3 hardly ramified
representation is at most `(2/3)·[K:ℚ]`, stated integrally as
`3·v₂(d_K) ≤ 2·[K:ℚ]`. The proven reduction: at any prime `Q` over
`2` the ideal-inertia has order `e ∣ 3` (the inertia leaf, converted
to `e(Q∣2)` by mathlib's inertia dictionary), so the ramification is
tame (`2 ∤ e`) and the different exponent is `d_Q ≤ e − 1`; the
arithmetic `3·(e−1) ≤ 2·e` for `e ≤ 3` and the norm bookkeeping
close. -/
theorem kernel_field_discr_two_exponent {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] (hfix : K.fixingSubgroup = u.ker) :
    3 * (NumberField.discr K).natAbs.factorization 2 ≤
      2 * Module.finrank ℚ K := by
  classical
  refine discr_factorization_le_of_forall_differentIdeal_pow_dvd K 2
    Nat.prime_two 3 2 ?_
  intro Q hQprime hQmem d hd
  haveI := hQprime
  -- the instance pack of the inertia dictionary (as in `MazurTorsion`)
  haveI := IsIntegralClosure.isIntegral_algebra ℤ
    (A := NumberField.RingOfIntegers K) K
  have hqZ : Prime (((2 : ℕ) : ℤ)) := Nat.prime_iff_prime_int.mp Nat.prime_two
  have hne : (Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    norm_num
  haveI hsp : (Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr hqZ
  haveI hlies : Q.LiesOver (Ideal.span {((2 : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff hQprime.ne_top hqZ).mpr (by exact_mod_cast hQmem)
  haveI hfinq : Finite (ℤ ⧸ (Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ)) :=
    Ring.HasFiniteQuotients.finiteQuotient hne
  haveI hmaxZ : (Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    hsp.isMaximal_of_ne_bot hne
  have hsurjZ : Function.Surjective
      (algebraMap (ℤ ⧸ (Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ))
        ((Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ).ResidueField)) :=
    IsFractionRing.surjective_iff_isField.mpr
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxZ)
  haveI : Finite ((Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ).ResidueField) :=
    Finite.of_surjective _ hsurjZ
  -- `Gal(K/ℚ)` is a Galois group of `𝓞 K` over `ℤ` (the assembly of
  -- `differentIdeal_eq_top_of_forall_inertia_eq_bot`, against the
  -- vendored action instance)
  haveI : IsGaloisGroup (K ≃ₐ[ℚ] K) ℤ (NumberField.RingOfIntegers K) := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    constructor
    intro x hx
    -- the underlying field element is Galois-fixed, hence rational
    have hfixL : ∀ g : K ≃ₐ[ℚ] K, g (x : K) = (x : K) := fun g =>
      congrArg (algebraMap (NumberField.RingOfIntegers K) K) (hx g)
    have hbot : (x : K) ∈ (⊥ : IntermediateField ℚ K) :=
      (IsGalois.mem_bot_iff_fixed _).mpr hfixL
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
    -- the rational number is integral over `ℤ`, hence an integer
    have hqint : IsIntegral ℤ q := by
      rw [← isIntegral_algebraMap_iff (B := K)
        (algebraMap ℚ K).injective, hq]
      exact x.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
    refine ⟨m, NumberField.RingOfIntegers.ext ?_⟩
    show algebraMap (NumberField.RingOfIntegers K) K
      (algebraMap ℤ (NumberField.RingOfIntegers K) m) = (x : K)
    rw [← hq, ← hm,
      ← IsScalarTower.algebraMap_apply ℤ (NumberField.RingOfIntegers K) K,
      ← IsScalarTower.algebraMap_apply ℤ ℚ K]
  -- `e(Q∣2) = |I(Q)|` divides `3`
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := (K ≃ₐ[ℚ] K)) (Ideal.span {((2 : ℕ) : ℤ)}) Q
  have hIdvd : Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) ∣ 3 :=
    kernel_field_inertia_card_at_two_dvd_three V hV hρ b e u hu K hfix
      Q hQprime hQmem
  have he3 : Ideal.ramificationIdx' (Ideal.span {((2 : ℕ) : ℤ)}) Q ∣ 3 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx
        (Ideal.span {((2 : ℕ) : ℤ)}) Q hne,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx
        (Ideal.span {((2 : ℕ) : ℤ)}) Q (K ≃ₐ[ℚ] K), ← hcard]
    exact hIdvd
  -- the tame bound: `d < e`
  have htame : ¬ ((2 : ℕ) ∣ Ideal.ramificationIdx'
      (Ideal.span {((2 : ℕ) : ℤ)}) Q) := by
    intro h2
    have h23 : (2 : ℕ) ∣ 3 := h2.trans he3
    norm_num at h23
  have hnot := not_pow_ramificationIdx_dvd_differentIdeal K 2 Nat.prime_two
    Q hQprime hQmem htame
  have hdlt : d < Ideal.ramificationIdx' (Ideal.span {((2 : ℕ) : ℤ)}) Q := by
    by_contra hge
    push Not at hge
    exact hnot ((pow_dvd_pow Q hge).trans hd)
  -- arithmetic: `3·d ≤ 3·(e−1) ≤ 2·e` since `e ≤ 3`
  have hele : Ideal.ramificationIdx' (Ideal.span {((2 : ℕ) : ℤ)}) Q ≤ 3 :=
    Nat.le_of_dvd (by norm_num) he3
  omega

/-- **The Fontaine discriminant exponent at `3`** (DECOMPOSED
2026-07-23 into the two sorry nodes above — the norm bookkeeping
`discr_factorization_le_of_forall_differentIdeal_pow_dvd` and the
per-prime Fontaine bound
`kernel_field_differentIdeal_exponent_at_three`; the assembly is
proven here): the `3`-adic
valuation of the discriminant of the kernel field of a mod-3 hardly
ramified representation is at most `(3/2)·[K:ℚ]`, stated integrally
as `2·v₃(d_K) ≤ 3·[K:ℚ]`. Intended content: flatness (`hρ.isFlat`)
prolongs the local representation at `3` to a finite flat group
scheme over `ℤ₃` killed by `3`, and Fontaine's ramification bound
(the upper-numbering ramification of `ℚ₃(V)/ℚ₃` vanishes above
`1 + 1/(3−1) = 3/2`) bounds the different exponent by `3/2` per unit
degree — attained by the peu-ramifié case `ℚ₃(ζ₃, u^{1/3})`, which is
why the bound is stated with `≤`. (Fontaine, *Il n'y a pas de variété
abélienne sur ℤ*, Invent. Math. 81 (1985); Moon–Taguchi, *Refinement
of Tate's discriminant bound…*, Doc. Math. 2003.) -/
theorem kernel_field_discr_three_exponent {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] (hfix : K.fixingSubgroup = u.ker) :
    2 * (NumberField.discr K).natAbs.factorization 3 ≤
      3 * Module.finrank ℚ K := by
  refine discr_factorization_le_of_forall_differentIdeal_pow_dvd K 3
    Nat.prime_three 2 3 ?_
  intro Q hQprime hQmem d hd
  exact kernel_field_differentIdeal_exponent_at_three V hV hρ b e u hu K hfix
    Q hQprime hQmem d hd

/-- **The discriminant bound of the kernel field** (DECOMPOSED
2026-07-23 into the three sorry nodes above — the
unramified-outside-`{2,3}` leaf `kernel_field_not_dvd_discr`, the
tame-at-`2` exponent leaf `kernel_field_discr_two_exponent` and the
Fontaine-at-`3` exponent leaf `kernel_field_discr_three_exponent`;
the factorization assembly `|d_K| = 2^{v₂}·3^{v₃}` and the exponent
arithmetic are proven here): the number field cut out by the kernel
of the matrix form of a mod-3 hardly ramified representation has root
discriminant at most `2^{2/3}·3^{3/2} = 314928^{1/6} = 8.2497…`,
stated integrally as `|d_K|⁶ ≤ 314928^{[K:ℚ]}` (note
`314928 = 2⁴·3⁹`, matching the two exponent leaves). -/
theorem discr_bound_of_kernel_field {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] (hfix : K.fixingSubgroup = u.ker) :
    |NumberField.discr K| ^ 6 ≤ 314928 ^ Module.finrank ℚ K := by
  classical
  have hD0 : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have hN0 : (NumberField.discr K).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
  -- every prime factor of `|d_K|` is `2` or `3`
  have hfac : ∀ q : ℕ, q.Prime → q ∣ (NumberField.discr K).natAbs →
      q = 2 ∨ q = 3 := by
    intro q hq hqN
    by_contra hne
    push Not at hne
    refine kernel_field_not_dvd_discr V hV hρ b e u hu K hfix
      q hq hne.1 hne.2 ?_
    have h1 : (((NumberField.discr K).natAbs : ℤ)) ∣ NumberField.discr K := by
      rw [Int.natCast_natAbs]
      exact (abs_dvd _ _).mpr dvd_rfl
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hqN) h1
  -- the factorization `|d_K| = 2^{v₂}·3^{v₃}`
  have hsupp : (NumberField.discr K).natAbs.factorization.support ⊆
      ({2, 3} : Finset ℕ) := by
    intro q hq
    rw [Nat.support_factorization] at hq
    rcases hfac q (Nat.prime_of_mem_primeFactors hq)
      (Nat.dvd_of_mem_primeFactors hq) with h | h <;> simp [h]
  have hNeq : (NumberField.discr K).natAbs =
      2 ^ (NumberField.discr K).natAbs.factorization 2 *
        3 ^ (NumberField.discr K).natAbs.factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod_of_support_subset _ hsupp (· ^ ·)
      (fun i _ => pow_zero i), Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)]
  -- the two exponent leaves
  have h2exp := kernel_field_discr_two_exponent V hV hρ b e u hu K hfix
  have h3exp := kernel_field_discr_three_exponent V hV hρ b e u hu K hfix
  -- assemble in `ℕ`
  have key : (NumberField.discr K).natAbs ^ 6 ≤
      314928 ^ Module.finrank ℚ K := by
    calc (NumberField.discr K).natAbs ^ 6
        = 2 ^ ((NumberField.discr K).natAbs.factorization 2 * 6) *
          3 ^ ((NumberField.discr K).natAbs.factorization 3 * 6) := by
          conv_lhs => rw [hNeq]
          rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ 2 ^ (4 * Module.finrank ℚ K) * 3 ^ (9 * Module.finrank ℚ K) :=
          Nat.mul_le_mul
            (Nat.pow_le_pow_right (by norm_num) (by omega))
            (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = 314928 ^ Module.finrank ℚ K := by
          rw [show (314928 : ℕ) = 2 ^ 4 * 3 ^ 9 by norm_num, mul_pow,
            ← pow_mul, ← pow_mul]
  -- back to `ℤ`
  have habs : |NumberField.discr K| =
      (((NumberField.discr K).natAbs : ℤ)) := (Int.natCast_natAbs _).symm
  rw [habs]
  exact_mod_cast key

/-- **The hardly ramified number field, from a degree bound**
(DECOMPOSED 2026-07-23 into the three sorry nodes above — the
Galois-correspondence field cut `exists_kernel_field_of_matrixRange`,
the oddness/totally-complex leaf `isTotallyComplex_of_kernel_field`,
and the Fontaine/tame discriminant leaf `discr_bound_of_kernel_field`;
the assembly is proven): a mod-3 hardly ramified representation whose
`𝔽̄₃`-matrix image `u.range` has at least `48` elements cuts out a
number field `K` (the fixed field of `ker u` inside `ℚᵃˡᵍ`) that is
totally complex, has degree `≥ 48` (the degree equals `#u.range`),
and has root discriminant at most `2^{2/3}·3^{3/2} = 314928^{1/6} =
8.2497…`, stated integrally as `|d_K|⁶ ≤ 314928^{[K:ℚ]}`. -/
theorem exists_hardlyRamified_number_field_of_card {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (hcard : 48 ≤ Nat.card u.range) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField K),
      NumberField.IsTotallyComplex K ∧
      48 ≤ Module.finrank ℚ K ∧
      |NumberField.discr K| ^ 6 ≤ 314928 ^ Module.finrank ℚ K := by
  obtain ⟨K, hNF, hgal, hfix, hdeg⟩ :=
    exists_kernel_field_of_matrixRange V hV hρ b e u hu
  haveI := hNF
  haveI := hgal
  exact ⟨K, hNF,
    isTotallyComplex_of_kernel_field V hV hρ b e u hu K hfix,
    hdeg ▸ hcard,
    discr_bound_of_kernel_field V hV hρ b e u hu K hfix⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The hardly ramified number field** (DECOMPOSED 2026-07-22 into
the PROVEN group-theoretic degree bound
`card_matrixRange_ge_of_exceptional` and the field-cutting sorry node
`exists_hardlyRamified_number_field_of_card` above): an absolutely
irreducible mod-3 hardly ramified representation whose projective
image is one of the five exceptional Dickson groups (`A₄`, `S₄`,
`A₅`, `PSL₂(𝔽_{3^m})`, `PGL₂(𝔽_{3^m})`) cuts out a number field `K`
(the fixed field of `ker ρ` inside `ℚᵃˡᵍ`) that is totally complex,
has degree `≥ 48`, and has root discriminant at most
`2^{2/3}·3^{3/2} = 314928^{1/6} = 8.2497…`, stated integrally as
`|d_K|⁶ ≤ 314928^{[K:ℚ]}`. -/
theorem exists_hardlyRamified_number_field {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (_habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase :
      (Nonempty (π.range ≃* alternatingGroup (Fin 4))) ∨
      (Nonempty (π.range ≃* Equiv.Perm (Fin 4))) ∨
      (Nonempty (π.range ≃* alternatingGroup (Fin 5))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 m))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        (GL (Fin 2) (GaloisField 3 m) ⧸
          Subgroup.center (GL (Fin 2) (GaloisField 3 m)))))) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField K),
      NumberField.IsTotallyComplex K ∧
      48 ≤ Module.finrank ℚ K ∧
      |NumberField.discr K| ^ 6 ≤ 314928 ^ Module.finrank ℚ K :=
  exists_hardlyRamified_number_field_of_card V hV hρ b e u hu
    (card_matrixRange_ge_of_exceptional V hV hρ b e u hu π hπ hcase)

/-- **The Fejér–Poitou test function** (introduced 2026-07-23 for the
decomposition of `odlyzko_rootDiscr_totallyComplex`): the triangular
Fejér kernel `x ↦ max (1 - |x|/6) 0` of half-width `6`.  It is even,
nonnegative, satisfies `f 0 = 1`, has compact support `[-6, 6]`,
integral `3` over `(0, ∞)`, and nonnegative Fourier transform
`t ↦ 6·(sin (3t)/(3t))²` — exactly the admissibility conditions of
Poitou's unconditional explicit-formula inequality (G. Poitou, *Sur
les petits discriminants*, Sém. Delange–Pisot–Poitou 18 (1976/77),
exp. 6, inequality (8) and Proposition 5, p. 6-08). -/
noncomputable def odlyzkoTestFn (x : ℝ) : ℝ := max (1 - |x| / 6) 0

/-- **The Poitou–Mellin transform of the Fejér test function**
(introduced 2026-07-23 for the decomposition of
`poitou_explicit_formula_bound`): the pairing
`Φ(s) = ∫_ℝ (f(x)/cosh(x/2))·e^{(s−1/2)x} dx` with `f = odlyzkoTestFn`,
i.e. the Mellin transform (2) of G. Poitou, *Sur les petits
discriminants*, Sém. Delange–Pisot–Poitou 18 (1976/77), exp. 6, at the
test function `F = f/cosh(x/2)` of its Proposition 5.  Since `f` is
supported in `[-6, 6]`, `Φ` is entire and bounded on every vertical
strip; on the boundary lines `Re s ∈ {0, 1}` of the critical strip its
real part is the nonnegative Fejér transform
`∫ f(x)·cos(tx) dx = 2·sin²(3t)/(3t²)`. -/
noncomputable def poitouPhi (s : ℂ) : ℂ :=
  ∫ x : ℝ, ((odlyzkoTestFn x / Real.cosh (x / 2) : ℝ) : ℂ) *
    Complex.exp ((s - 1 / 2) * (x : ℂ))

/-- **The prime-ideal term of Poitou's explicit formula at the Fejér
test function** (introduced 2026-07-23):
`4·Σ_{𝔭, m≥1} log N𝔭 · f(m·log N𝔭)/(1 + N𝔭^m)` over the nonzero prime
ideals `𝔭` of `𝒪_K`, with `f = odlyzkoTestFn` — the ultrametric term
`(4/n)·Σ_{𝔭,m} …` of inequality (8) of Poitou (exp. 6, p. 6-08)
multiplied by `n`.  Every summand is nonnegative
(`poitouPrimeTerm_nonneg` below), which is what legitimizes dropping
this term in the bound; since `f` vanishes beyond `6`, only the
finitely many pairs with `N𝔭^m < e⁶ = 403.42…` contribute. -/
noncomputable def poitouPrimeTerm (K : Type*) [Field K] [NumberField K] : ℝ :=
  4 * ∑' (P : {P : Ideal (NumberField.RingOfIntegers K) // P.IsPrime ∧ P ≠ ⊥})
      (m : ℕ),
    Real.log (Ideal.absNorm P.1) / (1 + (Ideal.absNorm P.1 : ℝ) ^ (m + 1)) *
      odlyzkoTestFn (((m : ℝ) + 1) * Real.log (Ideal.absNorm P.1))

/-- **Nonnegativity of the prime-ideal term** (PROVEN 2026-07-23):
every summand of `poitouPrimeTerm` is a product of nonnegatives
(`log N𝔭 ≥ 0`, a positive denominator, and `odlyzkoTestFn ≥ 0`), so
the sum is nonnegative — `tsum` of a nonnegative family is nonnegative
whether or not it converges.  This is the legitimacy of dropping the
ultrametric term of Poitou's inequality (8). -/
theorem poitouPrimeTerm_nonneg (K : Type*) [Field K] [NumberField K] :
    0 ≤ poitouPrimeTerm K := by
  refine mul_nonneg (by norm_num) (tsum_nonneg fun P => tsum_nonneg fun m => ?_)
  refine mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (by positivity)) ?_
  rw [odlyzkoTestFn]
  exact le_max_right _ _

/-- **Weil's explicit formula for the Dedekind zeta function at the
Fejér–Poitou test function** (sorry node, stated 2026-07-23 — the deep
analytic leaf of the decomposition of `poitou_explicit_formula_bound`):
for a totally complex number field `K` of degree `n` there exist a
zero-multiplicity function `mult : ℂ → ℕ` — the order of vanishing of
the analytically continued Dedekind zeta `ζ_K` on the critical strip
`0 < Re ρ < 1` (the pin's `NumberField.dedekindZeta` is only the
Dirichlet series, so the continuation and its zero data live inside
this existential), supported on the open strip and finite on every
horizontal truncation — and a real number `S` — the
symmetric-truncation limit `lim_{T→∞} Σ_{|Im ρ|≤T} mult(ρ)·Re Φ(ρ)`
of the zero sum, real because the zeros are conjugation-symmetric with
equal multiplicities — such that

`log |d_K| = n(γ + log 4π − ∫₀^∞ (1−f)/sinh x dx) − 4∫₀^∞ f + (P + S)`

with `f = odlyzkoTestFn`, `Φ = poitouPhi`, `P = poitouPrimeTerm K`.
This is the Théorème (A. Weil) of G. Poitou, *Sur les petits
discriminants*, Sém. Delange–Pisot–Poitou 18 (1976/77), exp. 6
(Propositions 1–3; formula (6), third form) evaluated at the test
function `F = f/cosh(x/2)` and specialized to `r₁ = 0`, after the
elementary rewritings `Φ(0) + Φ(1) = 4∫₀^∞ f`,
`2·(log N𝔭/N𝔭^{m/2})·F(m log N𝔭) = 4·log N𝔭·f(m log N𝔭)/(1 + N𝔭^m)`,
and `∫₀^∞ (1−F(x))/(2 sinh(x/2)) dx = ∫₀^∞ (1−f(x))/sinh x dx + log 2`
(which turns `γ + log 8π` into `γ + log 4π`); `F` is admissible by
Proposition 5's conditions (i)–(iii) for `f`.  The eventual proof must
carry the analytic continuation and functional equation of the
completed `Λ_K` and the contour-integral argument of Proposition 1
(Landau's horizontal estimates) — the material the official FLT
project axiomatizes away. -/
theorem dedekind_explicit_formula_fejer (K : Type*) [Field K] [NumberField K]
    (htc : NumberField.IsTotallyComplex K) :
    ∃ (mult : ℂ → ℕ) (S : ℝ),
      (∀ ρ, mult ρ ≠ 0 → 0 < ρ.re ∧ ρ.re < 1) ∧
      (∀ T : ℝ, {ρ : ℂ | mult ρ ≠ 0 ∧ |ρ.im| ≤ T}.Finite) ∧
      Filter.Tendsto (fun T : ℝ =>
          ∑' ρ : {ρ : ℂ // mult ρ ≠ 0 ∧ |ρ.im| ≤ T},
            (mult ρ.1 : ℝ) * (poitouPhi ρ.1).re)
        Filter.atTop (nhds S) ∧
      Real.log |(NumberField.discr K : ℝ)| =
        (Module.finrank ℚ K : ℝ) *
            (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
              ∫ x in Set.Ioi (0 : ℝ), (1 - odlyzkoTestFn x) / Real.sinh x) -
          4 * (∫ x in Set.Ioi (0 : ℝ), odlyzkoTestFn x) +
          (poitouPrimeTerm K + S) := by
  sorry

/-- **`Φ` is entire** (PROVEN 2026-07-23): the integrand
`x ↦ (f(x)/cosh(x/2))·e^{(s−1/2)x}` of `poitouPhi` is supported in
`[-6, 6]` and dominated there, locally uniformly in `s` — on the ball
`‖s − s₀‖ < 1` by the integrable majorant
`𝟙_{[-6,6]}·6·e^{6(‖s₀‖+2)}` — so differentiation under the integral
sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) applies at
every `s₀ ∈ ℂ`. -/
theorem poitouPhi_differentiable : Differentiable ℂ poitouPhi := by
  intro s₀
  have hfcont : Continuous odlyzkoTestFn := by
    rw [show odlyzkoTestFn = fun x : ℝ => max (1 - |x| / 6) 0 from rfl]
    exact (continuous_const.sub (continuous_abs.div_const 6)).max continuous_const
  have hfle : ∀ x : ℝ, 0 ≤ odlyzkoTestFn x ∧ odlyzkoTestFn x ≤ 1 := by
    intro x
    constructor
    · rw [odlyzkoTestFn]; exact le_max_right _ _
    · rw [odlyzkoTestFn]
      exact max_le (by have := abs_nonneg x; linarith) zero_le_one
  have hf0 : ∀ x : ℝ, 6 < |x| → odlyzkoTestFn x = 0 := by
    intro x hx
    rw [odlyzkoTestFn]
    exact max_eq_right (by linarith)
  have hFcont : Continuous (fun x : ℝ => odlyzkoTestFn x / Real.cosh (x / 2)) :=
    hfcont.div (Real.continuous_cosh.comp (continuous_id.div_const 2))
      fun x => (Real.cosh_pos _).ne'
  have hFsupp : HasCompactSupport
      (fun x : ℝ => odlyzkoTestFn x / Real.cosh (x / 2)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-6 : ℝ)) (b := 6)) ?_
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    have h6 : 6 < |x| := by
      rcases hx with h | h
      · have := neg_abs_le x; linarith
      · have := le_abs_self x; linarith
    rw [hf0 x h6, zero_div]
  set F : ℂ → ℝ → ℂ := fun s x =>
    ((odlyzkoTestFn x / Real.cosh (x / 2) : ℝ) : ℂ) *
      Complex.exp ((s - 1 / 2) * (x : ℂ))
  set F' : ℂ → ℝ → ℂ := fun s x =>
    ((odlyzkoTestFn x / Real.cosh (x / 2) : ℝ) : ℂ) *
      ((x : ℂ) * Complex.exp ((s - 1 / 2) * (x : ℂ))) with hF'
  have hFscont : ∀ s : ℂ, Continuous (F s) := fun s =>
    (Complex.continuous_ofReal.comp hFcont).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hF_meas : ∀ᶠ s in nhds s₀,
      MeasureTheory.AEStronglyMeasurable (F s) MeasureTheory.volume :=
    Filter.Eventually.of_forall fun s => (hFscont s).aestronglyMeasurable
  have hF_int : MeasureTheory.Integrable (F s₀) :=
    (hFscont s₀).integrable_of_hasCompactSupport
      ((hFsupp.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_right)
  have hF'_meas : MeasureTheory.AEStronglyMeasurable (F' s₀)
      MeasureTheory.volume :=
    ((Complex.continuous_ofReal.comp hFcont).mul
      (Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)))).aestronglyMeasurable
  have h_bound : ∀ᵐ x : ℝ ∂MeasureTheory.volume, ∀ s ∈ Metric.ball s₀ 1,
      ‖F' s x‖ ≤ Set.indicator (Set.Icc (-6 : ℝ) 6)
        (fun _ => 6 * Real.exp (6 * (‖s₀‖ + 2))) x := by
    refine Filter.Eventually.of_forall fun x => fun s hs => ?_
    rw [hF']
    simp only []
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    rcases le_or_gt |x| 6 with hx | hx
    · rw [Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp hx))]
      have hquot : |odlyzkoTestFn x / Real.cosh (x / 2)| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (hfle x).1 (Real.cosh_pos (x := x / 2)).le)]
        exact div_le_one_of_le₀
          (le_trans (hfle x).2 (Real.one_le_cosh (x / 2))) (Real.cosh_pos _).le
      have hre : ((s - 1 / 2) * (x : ℂ)).re = (s.re - 1 / 2) * x := by
        have h12 : ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
        simp [h12, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
          Complex.ofReal_im]
      rw [hre]
      have hsre : |s.re - 1 / 2| ≤ ‖s₀‖ + 2 := by
        have h1 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
        have h2 : ‖s‖ ≤ ‖s₀‖ + 1 := by
          have := Metric.mem_ball.mp hs
          have h3 : ‖s - s₀‖ < 1 := by rwa [← dist_eq_norm]
          calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by ring_nf
            _ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_add_le _ _
            _ ≤ ‖s₀‖ + 1 := by linarith
        have h4 : |s.re - 1 / 2| ≤ |s.re| + 1 / 2 := by
          calc |s.re - 1 / 2| ≤ |s.re| + |(1 : ℝ) / 2| := abs_sub _ _
            _ = |s.re| + 1 / 2 := by norm_num
        linarith
      have hexp : Real.exp ((s.re - 1 / 2) * x) ≤ Real.exp (6 * (‖s₀‖ + 2)) := by
        refine Real.exp_le_exp.mpr (le_trans (le_abs_self _) ?_)
        rw [abs_mul]
        calc |s.re - 1 / 2| * |x| ≤ (‖s₀‖ + 2) * 6 :=
              mul_le_mul hsre hx (abs_nonneg _) (by positivity)
          _ = 6 * (‖s₀‖ + 2) := by ring
      calc |odlyzkoTestFn x / Real.cosh (x / 2)| *
            (|x| * Real.exp ((s.re - 1 / 2) * x)) ≤
          1 * (6 * Real.exp (6 * (‖s₀‖ + 2))) := by
            refine mul_le_mul hquot ?_ (by positivity) zero_le_one
            exact mul_le_mul hx hexp (Real.exp_pos _).le (by norm_num)
        _ = 6 * Real.exp (6 * (‖s₀‖ + 2)) := one_mul _
    · rw [hf0 x hx, Set.indicator_of_notMem (by
        simp only [Set.mem_Icc, not_and_or, not_le]
        rcases lt_abs.mp hx with h | h
        · exact Or.inr h
        · exact Or.inl (by linarith))]
      simp
  have bound_int : MeasureTheory.Integrable
      (Set.indicator (Set.Icc (-6 : ℝ) 6)
        (fun _ => 6 * Real.exp (6 * (‖s₀‖ + 2)))) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    exact MeasureTheory.integrableOn_const measure_Icc_lt_top.ne
  have h_diff : ∀ᵐ x : ℝ ∂MeasureTheory.volume, ∀ s ∈ Metric.ball s₀ 1,
      HasDerivAt (F · x) (F' s x) s := by
    refine Filter.Eventually.of_forall fun x => fun s _ => ?_
    have hlin : HasDerivAt (fun s : ℂ => (s - 1 / 2) * (x : ℂ)) (x : ℂ) s := by
      simpa using ((hasDerivAt_id s).sub_const ((1 : ℂ) / 2)).mul_const (x : ℂ)
    have hexp : HasDerivAt (fun s : ℂ => Complex.exp ((s - 1 / 2) * (x : ℂ)))
        (Complex.exp ((s - 1 / 2) * (x : ℂ)) * (x : ℂ)) s :=
      (Complex.hasDerivAt_exp ((s - 1 / 2) * (x : ℂ))).comp s hlin
    have hD := hexp.const_mul
      ((odlyzkoTestFn x / Real.cosh (x / 2) : ℝ) : ℂ)
    have heq : ((odlyzkoTestFn x / Real.cosh (x / 2) : ℝ) : ℂ) *
        (Complex.exp ((s - 1 / 2) * (x : ℂ)) * (x : ℂ)) = F' s x := by
      rw [hF']
      ring
    exact heq ▸ hD
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s₀ one_pos) hF_meas hF_int hF'_meas h_bound
    bound_int h_diff
  exact main.2.differentiableAt

/-- **`Φ` is bounded on the closed critical strip** (PROVEN
2026-07-23): for `0 ≤ Re z ≤ 1` the integrand of `poitouPhi` is
bounded by `e³` on its support `[-6, 6]` (`0 ≤ f ≤ 1`, `cosh ≥ 1`,
`|(Re z − 1/2)·x| ≤ 3`), whence `‖Φ(z)‖ ≤ 12·e³`.  This is the
boundedness input of the Phragmén–Lindelöf step below. -/
theorem poitouPhi_norm_le (z : ℂ) (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1) :
    ‖poitouPhi z‖ ≤ 12 * Real.exp 3 := by
  rw [poitouPhi]
  have hfle : ∀ x : ℝ, 0 ≤ odlyzkoTestFn x ∧ odlyzkoTestFn x ≤ 1 := by
    intro x
    constructor
    · rw [odlyzkoTestFn]; exact le_max_right _ _
    · rw [odlyzkoTestFn]
      exact max_le (by have := abs_nonneg x; linarith) zero_le_one
  have hbound : ∀ x : ℝ,
      ‖((odlyzkoTestFn x / Real.cosh (x / 2) : ℝ) : ℂ) *
          Complex.exp ((z - 1 / 2) * (x : ℂ))‖ ≤
        Set.indicator (Set.Icc (-6 : ℝ) 6) (fun _ => Real.exp 3) x := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have h12 : ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    have hre : ((z - 1 / 2) * (x : ℂ)).re = (z.re - 1 / 2) * x := by
      simp [h12, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    rcases le_or_gt |x| 6 with hx | hx
    · rw [Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp hx))]
      have hquot : |odlyzkoTestFn x / Real.cosh (x / 2)| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (hfle x).1 (Real.cosh_pos (x := x / 2)).le)]
        exact div_le_one_of_le₀
          (le_trans (hfle x).2 (Real.one_le_cosh (x / 2))) (Real.cosh_pos _).le
      have hexp : Real.exp ((z.re - 1 / 2) * x) ≤ Real.exp 3 := by
        refine Real.exp_le_exp.mpr (le_trans (le_abs_self _) ?_)
        rw [abs_mul]
        have h2 : |z.re - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
        calc |z.re - 1 / 2| * |x| ≤ 1 / 2 * 6 :=
              mul_le_mul h2 hx (abs_nonneg _) (by norm_num)
          _ = 3 := by norm_num
      calc |odlyzkoTestFn x / Real.cosh (x / 2)| * Real.exp ((z.re - 1 / 2) * x)
          ≤ 1 * Real.exp 3 :=
            mul_le_mul hquot hexp (Real.exp_pos _).le zero_le_one
        _ = Real.exp 3 := one_mul _
    · have hf0 : odlyzkoTestFn x = 0 := by
        rw [odlyzkoTestFn]
        exact max_eq_right (by linarith)
      rw [hf0, Set.indicator_of_notMem (by
        simp only [Set.mem_Icc, not_and_or, not_le]
        rcases lt_abs.mp hx with h | h
        · exact Or.inr h
        · exact Or.inl (by linarith))]
      simp
  have hgint : MeasureTheory.Integrable
      (Set.indicator (Set.Icc (-6 : ℝ) 6) fun _ => Real.exp 3) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    exact MeasureTheory.integrableOn_const measure_Icc_lt_top.ne
  refine le_trans (MeasureTheory.norm_integral_le_of_norm_le hgint
    (Filter.Eventually.of_forall hbound)) ?_
  rw [MeasureTheory.integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
  have hvol : MeasureTheory.volume.real (Set.Icc (-6 : ℝ) 6) = 12 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 - -6)]
    norm_num
  rw [hvol]

/-- **Fejér positivity of the cosine transform of the test function**
(PROVEN 2026-07-23): `∫_ℝ f(x)·cos(tx) dx = (1 − cos 6t)/(3t²) ≥ 0`
for `t ≠ 0` (and `= 6 ≥ 0` at `t = 0`), `f = odlyzkoTestFn` — the
triangle is `1/6` times the autocorrelation `χ_{[-3,3]} ⋆ χ_{[-3,3]}`,
so its Fourier transform `6·(sin 3t/3t)²` is nonnegative.  Proof: the
integral localizes to `[-6, 6]`, folds onto `[0, 6]` by evenness, and
there `y ↦ (1 − y/6)·sin(ty)/t − cos(ty)/(6t²)` is an explicit
antiderivative, so FTC evaluates the integral to
`(1 − cos 6t)/(6t²)` per half. -/
theorem integral_odlyzkoTestFn_mul_cos_nonneg (t : ℝ) :
    0 ≤ ∫ x : ℝ, odlyzkoTestFn x * Real.cos (t * x) := by
  rcases eq_or_ne t 0 with ht | ht
  · refine MeasureTheory.integral_nonneg fun x => ?_
    rw [ht]
    simp only [zero_mul, Real.cos_zero, mul_one]
    rw [odlyzkoTestFn]
    exact le_max_right _ _
  -- reduce to the interval integral on [-6, 6]
  have hcongr : ∀ x : ℝ, odlyzkoTestFn x * Real.cos (t * x) =
      (Set.Ioc (-6 : ℝ) 6).indicator
        (fun y => (1 - |y| / 6) * Real.cos (t * y)) x := by
    intro x
    rcases le_or_gt |x| 6 with hx | hx
    · rcases eq_or_lt_of_le (neg_le_of_abs_le hx) with hx6 | hx6
      · rw [Set.indicator_of_notMem (by simp [← hx6])]
        rw [odlyzkoTestFn, ← hx6]
        norm_num
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx6, le_of_abs_le hx⟩),
          odlyzkoTestFn, max_eq_left (by linarith)]
    · rw [Set.indicator_of_notMem (by
        simp only [Set.mem_Ioc, not_and_or, not_lt, not_le]
        rcases lt_abs.mp hx with h | h
        · exact Or.inr h
        · exact Or.inl (by linarith)),
        odlyzkoTestFn, max_eq_right (by linarith)]
      exact zero_mul _
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-6 : ℝ) ≤ 6)]
  -- split at 0 and fold the negative half by evenness
  have hcont : Continuous fun y : ℝ => (1 - |y| / 6) * Real.cos (t * y) :=
    (continuous_const.sub (continuous_abs.div_const 6)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hsplit : (∫ y in (-6 : ℝ)..6, (1 - |y| / 6) * Real.cos (t * y)) =
      (∫ y in (-6 : ℝ)..0, (1 - |y| / 6) * Real.cos (t * y)) +
        ∫ y in (0 : ℝ)..6, (1 - |y| / 6) * Real.cos (t * y) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hfold : (∫ y in (-6 : ℝ)..0, (1 - |y| / 6) * Real.cos (t * y)) =
      ∫ y in (0 : ℝ)..6, (1 - |y| / 6) * Real.cos (t * y) := by
    have hneg : (∫ y in (0 : ℝ)..6,
        (1 - |(-y)| / 6) * Real.cos (t * (-y))) =
        ∫ y in (-6 : ℝ)..0, (1 - |y| / 6) * Real.cos (t * y) := by
      simpa using intervalIntegral.integral_comp_neg
        (f := fun y => (1 - |y| / 6) * Real.cos (t * y)) (a := 0) (b := 6)
    rw [← hneg]
    congr 1
    funext y
    rw [abs_neg, mul_neg, Real.cos_neg]
  -- the explicit antiderivative on [0, 6]
  have hkey : (∫ y in (0 : ℝ)..6, (1 - |y| / 6) * Real.cos (t * y)) =
      (1 - Real.cos (6 * t)) / (6 * t ^ 2) := by
    have habs : (∫ y in (0 : ℝ)..6, (1 - |y| / 6) * Real.cos (t * y)) =
        ∫ y in (0 : ℝ)..6, (1 - y / 6) * Real.cos (t * y) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 6)] at hy
      rw [abs_of_nonneg hy.1]
    rw [habs]
    have hG : ∀ y ∈ Set.uIcc (0 : ℝ) 6,
        HasDerivAt (fun y => (1 - y / 6) * (Real.sin (t * y) / t) -
          Real.cos (t * y) / (6 * t ^ 2))
          ((1 - y / 6) * Real.cos (t * y)) y := by
      intro y _
      have hlin : HasDerivAt (fun y : ℝ => t * y) t y := by
        simpa using (hasDerivAt_id y).const_mul t
      have hsin : HasDerivAt (fun y : ℝ => Real.sin (t * y))
          (Real.cos (t * y) * t) y := (Real.hasDerivAt_sin (t * y)).comp y hlin
      have hcos : HasDerivAt (fun y : ℝ => Real.cos (t * y))
          (-Real.sin (t * y) * t) y := (Real.hasDerivAt_cos (t * y)).comp y hlin
      have h1 : HasDerivAt (fun y : ℝ => 1 - y / 6) (-(1 / 6)) y := by
        simpa using ((hasDerivAt_id y).div_const 6).const_sub 1
      have hD := (h1.mul (hsin.div_const t)).sub ((hcos.div_const (6 * t ^ 2)))
      have heq : -(1 / 6) * (Real.sin (t * y) / t) +
          (1 - y / 6) * (Real.cos (t * y) * t / t) -
          -Real.sin (t * y) * t / (6 * t ^ 2) =
          (1 - y / 6) * Real.cos (t * y) := by
        field_simp
        ring
      exact heq ▸ hD
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG
      (((continuous_const.sub (continuous_id.div_const 6)).mul
        (Real.continuous_cos.comp
          (continuous_const.mul continuous_id))).intervalIntegrable _ _)]
    rw [mul_zero, Real.sin_zero, Real.cos_zero]
    field_simp
    ring
  rw [hsplit, hfold, hkey]
  have hc1 : Real.cos (6 * t) ≤ 1 := Real.cos_le_one _
  have ht2 : (0 : ℝ) < 6 * t ^ 2 := by positivity
  have h0 : (0 : ℝ) ≤ (1 - Real.cos (6 * t)) / (6 * t ^ 2) :=
    div_nonneg (by linarith) ht2.le
  linarith

/-- **Nonnegativity of `Re Φ` on the boundary lines of the critical
strip** (PROVEN 2026-07-23, consuming the Fejér leaf
`integral_odlyzkoTestFn_mul_cos_nonneg`): for `Re z ∈ {0, 1}`,
`Re Φ(z) = ∫_ℝ (f(x)/cosh(x/2))·e^{∓x/2}·cos((Im z)·x) dx`; the two
sign choices give equal integrals (substituting `x ↦ −x`; the
integrand data are even), and their sum is
`∫_ℝ (f/cosh(x/2))·(e^{x/2}+e^{−x/2})·cos dx = 2∫_ℝ f(x)·cos(tx) dx
≥ 0` by Fejér.  This is condition (iv) of Poitou's Proposition 5
evaluated on the boundary of the strip. -/
theorem poitouPhi_re_nonneg_boundary (z : ℂ) (hz : z.re = 0 ∨ z.re = 1) :
    0 ≤ (poitouPhi z).re := by
  have hfcont : Continuous odlyzkoTestFn := by
    rw [show odlyzkoTestFn = fun x : ℝ => max (1 - |x| / 6) 0 from rfl]
    exact (continuous_const.sub (continuous_abs.div_const 6)).max continuous_const
  have hfsupp : HasCompactSupport odlyzkoTestFn := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-6 : ℝ)) (b := 6)) ?_
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rw [odlyzkoTestFn]
    refine max_eq_right ?_
    rcases hx with h | h
    · have := neg_abs_le x; linarith
    · have := le_abs_self x; linarith
  have hFcont : Continuous (fun x : ℝ => odlyzkoTestFn x / Real.cosh (x / 2)) :=
    hfcont.div (Real.continuous_cosh.comp (continuous_id.div_const 2))
      fun x => (Real.cosh_pos _).ne'
  have hFsupp : HasCompactSupport
      (fun x : ℝ => odlyzkoTestFn x / Real.cosh (x / 2)) := by
    have hEq : (fun x : ℝ => odlyzkoTestFn x / Real.cosh (x / 2)) =
        odlyzkoTestFn * fun x => (Real.cosh (x / 2))⁻¹ := by
      funext x
      rw [Pi.mul_apply, div_eq_mul_inv]
    rw [hEq]
    exact hfsupp.mul_right
  set c : ℝ := z.im with hc
  have hIcont : ∀ e : ℝ, Continuous fun x : ℝ =>
      odlyzkoTestFn x / Real.cosh (x / 2) *
        (Real.exp (e * x) * Real.cos (c * x)) := fun e =>
    hFcont.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  have hIint : ∀ e : ℝ, MeasureTheory.Integrable fun x : ℝ =>
      odlyzkoTestFn x / Real.cosh (x / 2) *
        (Real.exp (e * x) * Real.cos (c * x)) := fun e =>
    (hIcont e).integrable_of_hasCompactSupport hFsupp.mul_right
  have hint : MeasureTheory.Integrable (fun x : ℝ =>
      ((odlyzkoTestFn x / Real.cosh (x / 2) : ℝ) : ℂ) *
        Complex.exp ((z - 1 / 2) * (x : ℂ))) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((Complex.continuous_ofReal.comp hFcont).mul
        (Complex.continuous_exp.comp (continuous_const.mul
          Complex.continuous_ofReal))) ?_
    exact (hFsupp.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_right
  have hre_eq : (poitouPhi z).re = ∫ x : ℝ,
      odlyzkoTestFn x / Real.cosh (x / 2) *
        (Real.exp ((z.re - 1 / 2) * x) * Real.cos (c * x)) := by
    rw [poitouPhi, ← RCLike.re_to_complex, ← integral_re hint]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    have h12 : ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.exp_re]
    congr 2
    · simp [h12, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im]
    · simp [h12, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, hc]
  have hIsymm : (∫ x : ℝ, odlyzkoTestFn x / Real.cosh (x / 2) *
        (Real.exp (-(1 / 2) * x) * Real.cos (c * x))) =
      ∫ x : ℝ, odlyzkoTestFn x / Real.cosh (x / 2) *
        (Real.exp (1 / 2 * x) * Real.cos (c * x)) := by
    rw [← MeasureTheory.integral_neg_eq_self
      (fun x : ℝ => odlyzkoTestFn x / Real.cosh (x / 2) *
        (Real.exp (1 / 2 * x) * Real.cos (c * x))) MeasureTheory.volume]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [odlyzkoTestFn, abs_neg, neg_div, Real.cosh_neg, mul_neg,
      Real.cos_neg, neg_mul]
  have hIadd : (∫ x : ℝ, odlyzkoTestFn x / Real.cosh (x / 2) *
        (Real.exp (-(1 / 2) * x) * Real.cos (c * x))) +
      (∫ x : ℝ, odlyzkoTestFn x / Real.cosh (x / 2) *
        (Real.exp (1 / 2 * x) * Real.cos (c * x))) =
      2 * ∫ x : ℝ, odlyzkoTestFn x * Real.cos (c * x) := by
    rw [← MeasureTheory.integral_add (hIint (-(1 / 2))) (hIint (1 / 2)),
      ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => ?_)
    have hch : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
    have hcosh2 : Real.exp (-(1 / 2) * x) + Real.exp (1 / 2 * x) =
        2 * Real.cosh (x / 2) := by
      rw [Real.cosh_eq]
      have h1 : -(1 / 2 : ℝ) * x = -(x / 2) := by ring
      have h2 : (1 / 2 : ℝ) * x = x / 2 := by ring
      rw [h1, h2]
      ring
    calc odlyzkoTestFn x / Real.cosh (x / 2) *
          (Real.exp (-(1 / 2) * x) * Real.cos (c * x)) +
        odlyzkoTestFn x / Real.cosh (x / 2) *
          (Real.exp (1 / 2 * x) * Real.cos (c * x)) =
        odlyzkoTestFn x / Real.cosh (x / 2) * Real.cos (c * x) *
          (Real.exp (-(1 / 2) * x) + Real.exp (1 / 2 * x)) := by ring
      _ = odlyzkoTestFn x / Real.cosh (x / 2) * Real.cos (c * x) *
          (2 * Real.cosh (x / 2)) := by rw [hcosh2]
      _ = 2 * (odlyzkoTestFn x * Real.cos (c * x)) := by
          field_simp
  have hFejer := integral_odlyzkoTestFn_mul_cos_nonneg c
  rcases hz with h0 | h1
  · have hcase : (poitouPhi z).re = ∫ x : ℝ,
        odlyzkoTestFn x / Real.cosh (x / 2) *
          (Real.exp (-(1 / 2) * x) * Real.cos (c * x)) := by
      rw [hre_eq]
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => ?_)
      rw [h0]
      norm_num
    rw [hcase]
    linarith [hIsymm, hIadd, hFejer]
  · have hcase : (poitouPhi z).re = ∫ x : ℝ,
        odlyzkoTestFn x / Real.cosh (x / 2) *
          (Real.exp (1 / 2 * x) * Real.cos (c * x)) := by
      rw [hre_eq]
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => ?_)
      rw [h1]
      norm_num
    rw [hcase]
    linarith [hIsymm, hIadd, hFejer]

/-- **Positivity of `Re Φ` on the closed critical strip** (PROVEN
2026-07-23, assembled from the PROVEN entirety `poitouPhi_differentiable`,
strip bound `poitouPhi_norm_le`, and boundary positivity
`poitouPhi_re_nonneg_boundary`):
`Re Φ(s) ≥ 0` for `0 ≤ Re s ≤ 1`.  The interior follows from the
boundary by the maximum principle: Phragmén–Lindelöf on the vertical
strip (`PhragmenLindelof.vertical_strip`) applied to `exp(−Φ)`, which
is entire, bounded on the strip by `exp(12·e³)` (so any admissible
growth budget works), and of norm `exp(−Re Φ) ≤ 1` on the boundary
lines.  This is the positivity step of Proposition 5 of Poitou
(exp. 6, p. 6-08): the unconditional replacement for GRH, turning
condition (iv) (Fejér: `f̂ ≥ 0`) into `Re Φ(ρ) ≥ 0` at every
nontrivial zero `ρ`. -/
theorem poitouPhi_re_nonneg (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    0 ≤ (poitouPhi s).re := by
  have key : ‖Complex.exp (-poitouPhi s)‖ ≤ 1 := by
    refine PhragmenLindelof.vertical_strip (a := 0) (b := 1) (C := 1)
      (f := fun z => Complex.exp (-poitouPhi z))
      poitouPhi_differentiable.neg.cexp.diffContOnCl ?_ ?_ ?_ h0 h1
    · refine ⟨1, by rw [sub_zero, div_one]; linarith [Real.pi_gt_three],
        12 * Real.exp 3, Asymptotics.IsBigO.of_bound' ?_⟩
      have hmem : ∀ᶠ w : ℂ in
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo 0 1),
          w ∈ Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1 :=
        Filter.eventually_inf_principal.mpr
          (Filter.Eventually.of_forall fun w hw => hw)
      filter_upwards [hmem] with w hw
      simp only [Set.mem_preimage, Set.mem_Ioo] at hw
      rw [Complex.norm_exp, Complex.neg_re, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
      refine le_trans (le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)) ?_
      refine le_trans (poitouPhi_norm_le w hw.1.le hw.2.le) ?_
      exact le_mul_of_one_le_right (by positivity)
        (Real.one_le_exp (by positivity))
    · intro w hw
      rw [Complex.norm_exp, Complex.neg_re]
      exact Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (poitouPhi_re_nonneg_boundary w (Or.inl hw)))
    · intro w hw
      rw [Complex.norm_exp, Complex.neg_re]
      exact Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (poitouPhi_re_nonneg_boundary w (Or.inr hw)))
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff] at key
  linarith

/-- **Poitou's unconditional explicit-formula inequality at the Fejér
test function** (DECOMPOSED 2026-07-23 into the deep explicit-formula
leaf `dedekind_explicit_formula_fejer`, the strip-positivity leaf
`poitouPhi_re_nonneg`, and the PROVEN `poitouPrimeTerm_nonneg`; the
assembly below is proven — drop the zero term, truncation by
truncation, and the prime term): for a totally complex number field
`K` of degree `n`,

`n·(γ + log 4π − ∫₀^∞ (1 − f x)/sinh x dx) − 4·∫₀^∞ f ≤ log |d_K|`

where `f = odlyzkoTestFn` and `γ` is the Euler–Mascheroni constant.
This is inequality (8) of G. Poitou, *Sur les petits discriminants*,
Sém. Delange–Pisot–Poitou 18 (1976/77), exp. 6 (Proposition 5,
p. 6-08), specialized to `r₁ = 0` (totally complex), with the
everywhere-nonnegative prime-ideal sum
`(4/n)·Σ_{𝔭,m} log N𝔭 · f(m log N𝔭)/(1 + N𝔭^m)` dropped — legitimate
since `odlyzkoTestFn ≥ 0`.  The admissibility conditions of
Proposition 5 hold for `odlyzkoTestFn`: `f 0 = 1`, `∫₀^∞ f` converges
(compact support), `f/cosh(x/2)` and `(1 − f x)/x` are of bounded
variation, and the Fourier transform `t ↦ 6·(sin (3t)/(3t))²` is
nonnegative (Fejér).  Note the official FLT project takes the
analogous statement as a standing AXIOM (`FLT.Assumptions.Odlyzko`,
tracking issue #458) — here it must be proven.  Numerically the left
side at `n = 48` is `log (11.56…ⁿ/e¹²)`, far above the needed
`log 8.25ⁿ`. -/
theorem poitou_explicit_formula_bound (K : Type*) [Field K] [NumberField K]
    (htc : NumberField.IsTotallyComplex K) :
    (Module.finrank ℚ K : ℝ) *
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
          ∫ x in Set.Ioi (0 : ℝ), (1 - odlyzkoTestFn x) / Real.sinh x) -
      4 * ∫ x in Set.Ioi (0 : ℝ), odlyzkoTestFn x ≤
      Real.log |(NumberField.discr K : ℝ)| := by
  obtain ⟨mult, S, hstrip, -, htend, heq⟩ :=
    dedekind_explicit_formula_fejer K htc
  have hP : (0 : ℝ) ≤ poitouPrimeTerm K := poitouPrimeTerm_nonneg K
  have hS : (0 : ℝ) ≤ S :=
    ge_of_tendsto' htend fun T =>
      tsum_nonneg fun ρ =>
        mul_nonneg (Nat.cast_nonneg _)
          (poitouPhi_re_nonneg ρ.1 (hstrip ρ.1 ρ.2.1).1.le
            (hstrip ρ.1 ρ.2.1).2.le)
  linarith [heq, hP, hS]

/-- **Numeric bound on the archimedean integral of the Fejér–Poitou
decomposition** (PROVEN 2026-07-23):
`∫₀^∞ (1 − odlyzkoTestFn x)/sinh x dx ≤ 5/8`.  The true value is
`0.4104…`, so the bound is generous.  Proof: the integrand is `≤ 1/6`
on `(0, 1]` (numerator `≤ x/6` and `x ≤ sinh x`) and
`≤ (7/9)·e^{-1}·e^{-x/2}` on `(1, ∞)` (numerator `≤ x/6`,
`sinh x ≥ (3/7)·eˣ` from `e^{2x} ≥ e² > 7`, and `x ≤ 2e^{x/2-1}` from
`1 + t ≤ eᵗ`); the two pieces integrate to
`1/6 + (14/9)·e^{-3/2} ≤ 1/6 + 14/36 < 5/8` using `e^{3/2} ≥ 4`. -/
theorem integral_one_sub_odlyzkoTestFn_div_sinh_le :
    (∫ x in Set.Ioi (0 : ℝ), (1 - odlyzkoTestFn x) / Real.sinh x) ≤ 5 / 8 := by
  set h : ℝ → ℝ := fun x => (1 - odlyzkoTestFn x) / Real.sinh x with hh
  -- measurability of the integrand
  have hmeas : Measurable h := by
    have hcont : Continuous odlyzkoTestFn := by
      have hrfl : odlyzkoTestFn = fun x : ℝ => max (1 - |x| / 6) 0 := rfl
      rw [hrfl]
      exact (continuous_const.sub (continuous_abs.div_const 6)).max continuous_const
    exact (measurable_const.sub hcont.measurable).div Real.continuous_sinh.measurable
  -- elementary pointwise facts about the numerator
  have hf_le : ∀ x : ℝ, 0 ≤ x → 1 - odlyzkoTestFn x ≤ x / 6 := by
    intro x hx
    have h1 : (1 : ℝ) - x / 6 ≤ odlyzkoTestFn x := by
      rw [odlyzkoTestFn, abs_of_nonneg hx]
      exact le_max_left _ _
    linarith
  have hf_nonneg : ∀ x : ℝ, 0 ≤ 1 - odlyzkoTestFn x := by
    intro x
    have h2 : (0 : ℝ) ≤ |x| / 6 := by positivity
    have h1 : odlyzkoTestFn x ≤ 1 := by
      rw [odlyzkoTestFn]
      exact max_le (by linarith) (by norm_num)
    linarith
  have hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ h x := fun x hx =>
    div_nonneg (hf_nonneg x) (Real.sinh_nonneg_iff.mpr hx.le)
  -- the pointwise bound on `(0, 1]`
  have hpiece1 : ∀ x ∈ Set.Ioc (0 : ℝ) 1, h x ≤ 1 / 6 := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx0
    have hxs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx0.le
    have hnum := hf_le x hx0.le
    calc h x ≤ (x / 6) / Real.sinh x := by
          simp only [hh]
          gcongr
      _ ≤ (x / 6) / x := by gcongr
      _ = 1 / 6 := by field_simp
  -- the pointwise bound on `(1, ∞)`
  have hpiece2 : ∀ x ∈ Set.Ioi (1 : ℝ), h x ≤
      7 / 9 * Real.exp (-1) * Real.exp (-(1 / 2) * x) := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx0
    have hprod : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]; simp
    -- `sinh x ≥ (3/7)·eˣ`, because `e^{2x} ≥ e² > 7`
    have hsinh_ge : 3 / 7 * Real.exp x ≤ Real.sinh x := by
      have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h2 : Real.exp 1 ≤ Real.exp x := Real.exp_le_exp.mpr hx.le
      have h4 : Real.exp (-x) ≤ Real.exp x / 7 := by
        nlinarith [Real.exp_pos (-x)]
      rw [Real.sinh_eq]
      linarith
    -- `x ≤ 2·e^{x/2 - 1}`, from `1 + t ≤ eᵗ`
    have hxle : x ≤ 2 * Real.exp (x / 2 - 1) := by
      have := Real.add_one_le_exp (x / 2 - 1)
      linarith
    have hden : 1 / Real.sinh x ≤ 7 / 3 * Real.exp (-x) := by
      rw [div_le_iff₀ hsinh]
      nlinarith [Real.exp_pos (-x)]
    have hchain : h x ≤ 7 / 18 * (x * Real.exp (-x)) := by
      have hnum := hf_le x hx0.le
      calc h x = (1 - odlyzkoTestFn x) * (1 / Real.sinh x) := by
            simp only [hh]; ring
        _ ≤ (x / 6) * (7 / 3 * Real.exp (-x)) := by
            refine mul_le_mul hnum hden (by positivity) (by positivity)
        _ = 7 / 18 * (x * Real.exp (-x)) := by ring
    have hkey : Real.exp (x / 2 - 1) * Real.exp (-x) =
        Real.exp (-1) * Real.exp (-(1 / 2) * x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    have h5 : x * Real.exp (-x) ≤ 2 * Real.exp (x / 2 - 1) * Real.exp (-x) := by
      have := Real.exp_pos (-x)
      nlinarith
    calc h x ≤ 7 / 18 * (x * Real.exp (-x)) := hchain
      _ ≤ 7 / 18 * (2 * Real.exp (x / 2 - 1) * Real.exp (-x)) := by linarith
      _ = 7 / 9 * (Real.exp (x / 2 - 1) * Real.exp (-x)) := by ring
      _ = 7 / 9 * (Real.exp (-1) * Real.exp (-(1 / 2) * x)) := by rw [hkey]
      _ = 7 / 9 * Real.exp (-1) * Real.exp (-(1 / 2) * x) := by ring
  -- integrability of the two piecewise majorants and hence of the integrand
  have hint_g : MeasureTheory.IntegrableOn
      (fun x : ℝ => 7 / 9 * Real.exp (-1) * Real.exp (-(1 / 2) * x))
      (Set.Ioi (1 : ℝ)) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.exp (-(1 / 2) * x)) (Set.Ioi (1 : ℝ)) :=
      exp_neg_integrableOn_Ioi 1 (by norm_num)
    exact h1.const_mul _
  have hint_h2 : MeasureTheory.IntegrableOn h (Set.Ioi (1 : ℝ)) := by
    refine MeasureTheory.Integrable.mono' hint_g
      hmeas.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x (lt_trans one_pos hx))]
    exact hpiece2 x hx
  have hint_c : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ) / 6)
      (Set.Ioc (0 : ℝ) 1) :=
    MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
  have hint_h1 : MeasureTheory.IntegrableOn h (Set.Ioc (0 : ℝ) 1) := by
    refine MeasureTheory.Integrable.mono' hint_c
      hmeas.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x hx.1)]
    exact hpiece1 x hx
  -- split the integral at `1` and bound the two pieces
  have hsplit : (∫ x in Set.Ioi (0 : ℝ), h x) =
      (∫ x in Set.Ioc (0 : ℝ) 1, h x) + ∫ x in Set.Ioi (1 : ℝ), h x := by
    rw [← MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same
      measurableSet_Ioi hint_h1 hint_h2, Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hb1 : (∫ x in Set.Ioc (0 : ℝ) 1, h x) ≤ 1 / 6 := by
    have h1 : (∫ x in Set.Ioc (0 : ℝ) 1, h x) ≤
        ∫ _ in Set.Ioc (0 : ℝ) 1, (1 / 6 : ℝ) :=
      MeasureTheory.setIntegral_mono_on hint_h1 hint_c measurableSet_Ioc hpiece1
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at h1
    have h2 : MeasureTheory.volume.real (Set.Ioc (0 : ℝ) 1) = 1 := by
      simp [MeasureTheory.measureReal_def, Real.volume_Ioc]
    rw [h2, one_mul] at h1
    exact h1
  have hb2 : (∫ x in Set.Ioi (1 : ℝ), h x) ≤
      7 / 9 * Real.exp (-1) * (2 * Real.exp (-(1 / 2))) := by
    have h1 : (∫ x in Set.Ioi (1 : ℝ), h x) ≤
        ∫ x in Set.Ioi (1 : ℝ), 7 / 9 * Real.exp (-1) * Real.exp (-(1 / 2) * x) :=
      MeasureTheory.setIntegral_mono_on hint_h2 hint_g measurableSet_Ioi hpiece2
    have h2 : (∫ x in Set.Ioi (1 : ℝ), 7 / 9 * Real.exp (-1) *
        Real.exp (-(1 / 2) * x)) =
        7 / 9 * Real.exp (-1) * ∫ x in Set.Ioi (1 : ℝ), Real.exp (-(1 / 2) * x) :=
      MeasureTheory.integral_const_mul _ _
    have h4 := MeasureTheory.integral_comp_mul_left_Ioi
      (fun y : ℝ => Real.exp (-y)) 1 (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))
    simp only [smul_eq_mul] at h4
    have h5 : (∫ x in Set.Ioi (1 : ℝ), Real.exp (-(1 / 2) * x)) =
        2 * Real.exp (-(1 / 2)) := by
      simp only [neg_mul]
      rw [h4, show (1 / 2 : ℝ) * 1 = 1 / 2 by norm_num, integral_exp_neg_Ioi]
      norm_num
    rw [h2, h5] at h1
    exact h1
  -- the numeric endgame: `1/6 + (14/9)·e^{-3/2} ≤ 5/8` via `e^{3/2} ≥ 4`
  have hE : (4 : ℝ) ≤ Real.exp (3 / 2) := by
    have h3 : Real.exp (3 / 2) * Real.exp (3 / 2) = Real.exp 3 := by
      rw [← Real.exp_add]; norm_num
    have h4 : (16 : ℝ) ≤ Real.exp 3 := by
      have h5 : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h5]
      calc (16 : ℝ) ≤ 2.7182818283 ^ (3 : ℕ) := by norm_num
        _ ≤ Real.exp 1 ^ (3 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3
    nlinarith [Real.exp_pos (3 / 2)]
  have hEinv : (Real.exp (3 / 2))⁻¹ ≤ 1 / 4 := by
    have h7 : (0 : ℝ) < Real.exp (3 / 2) := Real.exp_pos _
    have h8 : (Real.exp (3 / 2))⁻¹ * Real.exp (3 / 2) = 1 :=
      inv_mul_cancel₀ (ne_of_gt h7)
    nlinarith [inv_pos.mpr h7]
  have hnum : 7 / 9 * Real.exp (-1) * (2 * Real.exp (-(1 / 2))) ≤ 11 / 24 := by
    have h1 : Real.exp (-1) * Real.exp (-(1 / 2)) = (Real.exp (3 / 2))⁻¹ := by
      rw [← Real.exp_add, ← Real.exp_neg]
      norm_num
    nlinarith [Real.exp_pos (-(1 : ℝ)), Real.exp_pos (-(1 / 2 : ℝ))]
  rw [hsplit]
  linarith [hb1, hb2, hnum]

/-- **The integral of the Fejér–Poitou test function** (PROVEN
2026-07-23): `∫₀^∞ odlyzkoTestFn = 3` (stated as `≤ 3`, which is what
the assembly consumes): on `(0, 6]` the function is `1 − x/6` with
integral `6 − 3 = 3`, and it vanishes beyond `6`. -/
theorem integral_odlyzkoTestFn_le :
    (∫ x in Set.Ioi (0 : ℝ), odlyzkoTestFn x) ≤ 3 := by
  have hcongr : ∀ x ∈ Set.Ioi (0 : ℝ),
      odlyzkoTestFn x = (Set.Ioc (0 : ℝ) 6).indicator (fun y => 1 - y / 6) x := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [odlyzkoTestFn, abs_of_pos hx]
    rcases le_or_gt x 6 with h6 | h6
    · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, h6⟩)]
      exact max_eq_left (by linarith)
    · rw [Set.indicator_of_notMem
        (by simp only [Set.mem_Ioc, not_and, not_le]; exact fun _ => h6)]
      exact max_eq_right (by linarith)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 6),
    intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_id.div_const 6),
    intervalIntegral.integral_div, integral_id,
    intervalIntegral.integral_const]
  norm_num

/-- **The Odlyzko discriminant bound** (DECOMPOSED 2026-07-23 into
the explicit-formula sorry node `poitou_explicit_formula_bound`, the
elementary numeric sorry node
`integral_one_sub_odlyzkoTestFn_div_sinh_le`, and the PROVEN
`integral_odlyzkoTestFn_le`; the assembly below is proven): a totally
complex number field of degree `n ≥ 48` has root discriminant at
least `33/4 = 8.25 > 314928^{1/6} = 8.2497…`, stated integrally as
`33^n ≤ 4^n·|d_K|`.

This is Odlyzko's unconditional discriminant bound (A. M. Odlyzko,
*Lower bounds for discriminants of number fields*, Acta Arith. 29
(1976); G. Poitou, *Sur les petits discriminants*, Sém.
Delange–Pisot–Poitou 18 (1976/77), exp. 6, whose table p. 6-17 gives
`13.77` at degree `48`; the asymptote is `4πe^γ = 22.38…`).
(Minkowski's bound alone, asymptotically `πe²/4 = 5.803…`, does NOT
suffice for this statement, and the plain Stark-lemma bound tops out
near `7` at degree 48 — hence the explicit-formula leaf.)  The
assembly: with `γ > 1/2` (mathlib), `J ≤ 5/8` and `C ≤ 3` (the two
integral leaves), the explicit-formula leaf gives
`log |d_K| ≥ n(γ + log 4π − 5/8) − 12 ≥ n(log 4π − 1/8) − 12`, and
`log 4π − 1/8 − log (33/4) = log (16π/33) − 1/8 ≥ 3/8 − 1/8 = 1/4`
(via `e^{3/8} < 1.46` from `e³ < 1.46⁸` and `33·1.46 < 16·3.14 <
16π`), so `log |d_K| − n·log (33/4) ≥ n/4 − 12 ≥ 0` for `n ≥ 48`. -/
theorem odlyzko_rootDiscr_totallyComplex (K : Type*) [Field K] [NumberField K]
    (htc : NumberField.IsTotallyComplex K)
    (hdeg : 48 ≤ Module.finrank ℚ K) :
    (33 : ℤ) ^ Module.finrank ℚ K ≤
      4 ^ Module.finrank ℚ K * |NumberField.discr K| := by
  set n := Module.finrank ℚ K with hn
  have hA := poitou_explicit_formula_bound K htc
  have hB := integral_one_sub_odlyzkoTestFn_div_sinh_le
  have hC := integral_odlyzkoTestFn_le
  have hγ : (1 : ℝ) / 2 < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  -- `e^{3/8} < 1.46`, via eighth powers: `e³ < 2.7182818286³ < 1.46⁸`
  have hexp : Real.exp (3 / 8) < 1.46 := by
    refine lt_of_pow_lt_pow_left₀ 8 (by norm_num) ?_
    have h8 : Real.exp (3 / 8) ^ (8 : ℕ) = Real.exp 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
      rw [← Real.exp_nat_mul]; norm_num
    calc Real.exp (3 / 8) ^ (8 : ℕ) = Real.exp 1 ^ (3 : ℕ) := by rw [h8, h3]
      _ < 2.7182818286 ^ (3 : ℕ) :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
      _ < 1.46 ^ (8 : ℕ) := by norm_num
  -- the per-degree margin: `3/8 ≤ log (16π/33)`
  have hmargin : (3 : ℝ) / 8 ≤ Real.log (16 * Real.pi / 33) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h146 : (1.46 : ℝ) ≤ 16 * Real.pi / 33 := by
      have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
      linarith
    linarith [hexp]
  -- the logarithmic form of the goal
  have key : (n : ℝ) * Real.log (33 / 4) ≤
      Real.log |(NumberField.discr K : ℝ)| := by
    have hn48 : (48 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdeg
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
    have hJ' : (0 : ℝ) ≤ (n : ℝ) *
        (5 / 8 - ∫ x in Set.Ioi (0 : ℝ), (1 - odlyzkoTestFn x) / Real.sinh x) :=
      mul_nonneg hn0 (by linarith [hB])
    have hγ' : (0 : ℝ) ≤ (n : ℝ) * (Real.eulerMascheroniConstant - 1 / 2) :=
      mul_nonneg hn0 (by linarith [hγ])
    have hM' : (0 : ℝ) ≤ (n : ℝ) * (Real.log (16 * Real.pi / 33) - 3 / 8) :=
      mul_nonneg hn0 (by linarith [hmargin])
    have hsplit : (n : ℝ) * Real.log (16 * Real.pi / 33) =
        (n : ℝ) * Real.log (4 * Real.pi) - (n : ℝ) * Real.log (33 / 4) := by
      rw [show (16 * Real.pi / 33 : ℝ) = (4 * Real.pi) / (33 / 4) by ring,
        Real.log_div (by positivity) (by norm_num)]
      ring
    nlinarith [hA, hC, hn48, hJ', hγ', hM', hsplit]
  -- exponentiate and cast back to `ℤ`
  have hD0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| := by
    rw [abs_pos, Int.cast_ne_zero]
    exact NumberField.discr_ne_zero K
  have hpow : ((33 : ℝ) / 4) ^ n ≤ |(NumberField.discr K : ℝ)| := by
    have h1 : Real.log (((33 : ℝ) / 4) ^ n) ≤
        Real.log |(NumberField.discr K : ℝ)| := by
      rw [Real.log_pow]; exact key
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by positivity), Real.exp_log hD0] at h2
  have hfin : (33 : ℝ) ^ n ≤ (4 : ℝ) ^ n * |(NumberField.discr K : ℝ)| := by
    calc (33 : ℝ) ^ n = (4 : ℝ) ^ n * ((33 : ℝ) / 4) ^ n := by
          rw [← mul_pow]; norm_num
      _ ≤ (4 : ℝ) ^ n * |(NumberField.discr K : ℝ)| :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  exact_mod_cast hfin

/-- **The Odlyzko discriminant bound, sixth-power form** (DECOMPOSED
2026-07-23 into the root-discriminant sorry node
`odlyzko_rootDiscr_totallyComplex` above; the integer arithmetic
`(33/4)⁶ = 315299.79… > 314928` is proven here): a totally complex
number field of degree `n ≥ 48` has root discriminant strictly
greater than `2^{2/3}·3^{3/2} = 314928^{1/6} = 8.2497…`, stated
integrally as `314928^n < |d_K|⁶`. -/
theorem odlyzko_bound_totallyComplex (K : Type*) [Field K] [NumberField K]
    (htc : NumberField.IsTotallyComplex K)
    (hdeg : 48 ≤ Module.finrank ℚ K) :
    (314928 : ℤ) ^ Module.finrank ℚ K < |NumberField.discr K| ^ 6 := by
  have h1 := odlyzko_rootDiscr_totallyComplex K htc hdeg
  have hn0 : Module.finrank ℚ K ≠ 0 := by omega
  -- sixth power of the root-discriminant bound
  have h6 : ((33 : ℤ) ^ Module.finrank ℚ K) ^ 6 ≤
      (4 ^ Module.finrank ℚ K * |NumberField.discr K|) ^ 6 :=
    pow_le_pow_left₀ (by positivity) h1 6
  -- strict comparison of the bases: `314928·4⁶ < 33⁶`
  have hlt : ((314928 : ℤ) * 4 ^ 6) ^ Module.finrank ℚ K <
      ((33 : ℤ) ^ 6) ^ Module.finrank ℚ K :=
    pow_lt_pow_left₀ (by norm_num) (by positivity) hn0
  -- combine and cancel the positive factor `(4^n)⁶`
  have hmain : ((4 : ℤ) ^ Module.finrank ℚ K) ^ 6 *
        (314928 : ℤ) ^ Module.finrank ℚ K <
      ((4 : ℤ) ^ Module.finrank ℚ K) ^ 6 * |NumberField.discr K| ^ 6 := by
    calc ((4 : ℤ) ^ Module.finrank ℚ K) ^ 6 *
          (314928 : ℤ) ^ Module.finrank ℚ K
        = ((314928 : ℤ) * 4 ^ 6) ^ Module.finrank ℚ K := by
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
          exact mul_comm _ _
      _ < ((33 : ℤ) ^ 6) ^ Module.finrank ℚ K := hlt
      _ = ((33 : ℤ) ^ Module.finrank ℚ K) ^ 6 := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (4 ^ Module.finrank ℚ K * |NumberField.discr K|) ^ 6 := h6
      _ = ((4 : ℤ) ^ Module.finrank ℚ K) ^ 6 * |NumberField.discr K| ^ 6 := by
          ring
  exact lt_of_mul_lt_mul_left hmain (by positivity)

set_option backward.isDefEq.respectTransparency false in
/-- **The Serre/Tate elimination, exceptional cases** (DERIVED
2026-07-22 from the two sorry nodes above): the five exceptional
Dickson cases (`A₄`, `S₄`, `A₅`, `PSL₂(𝔽_{3^m})`, `PGL₂(𝔽_{3^m})`)
are eliminated by comparing the hardly-ramified root-discriminant
bound `|d_K|⁶ ≤ 314928^{[K:ℚ]}` of the cut-out number field
(`exists_hardlyRamified_number_field`) with the Odlyzko lower bound
`314928^{[K:ℚ]} < |d_K|⁶` valid in degree `≥ 48`
(`odlyzko_bound_totallyComplex`). -/
theorem serre_elimination_exceptional {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase :
      (Nonempty (π.range ≃* alternatingGroup (Fin 4))) ∨
      (Nonempty (π.range ≃* Equiv.Perm (Fin 4))) ∨
      (Nonempty (π.range ≃* alternatingGroup (Fin 5))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 m))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        (GL (Fin 2) (GaloisField 3 m) ⧸
          Subgroup.center (GL (Fin 2) (GaloisField 3 m)))))) :
    False := by
  obtain ⟨K, _, htc, hdeg, hdisc⟩ :=
    exists_hardlyRamified_number_field V hV hρ habs b e u hu π hπ hcase
  exact absurd hdisc (not_le.mpr (odlyzko_bound_totallyComplex K htc hdeg))

/-- **The quadratic generator of a degree-2 Galois number field**
(PROVEN 2026-07-23 — the Kummer-theoretic half of the quadratic-field
classification): a degree-2 Galois subfield `K ⊆ ℚᵃˡᵍ` has a
two-element automorphism group `{1, σ}` and contains an irrational
element `x` with `σ x = −x` and `x² = d` for a SQUAREFREE integer `d`.
Construction: `α − σ α` is a nonzero anti-fixed irrational for any
irrational `α` (which exists since `[K : ℚ] = 2 > 1`); its square is
Galois-invariant, hence a nonzero rational `r`; scaling by
`den(r)/b` for `n = num(r)·den(r) = b²·a` with `a` squarefree
(`Nat.sq_mul_squarefree`) makes the square the squarefree integer
`d = ±a`. -/
theorem exists_quadratic_generator
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] (hrank : Module.finrank ℚ K = 2) :
    ∃ (σ : K ≃ₐ[ℚ] K) (x : K) (d : ℤ), σ ≠ 1 ∧ σ * σ = 1 ∧
      (∀ g : K ≃ₐ[ℚ] K, g = 1 ∨ g = σ) ∧ σ x = -x ∧
      x ∉ (⊥ : IntermediateField ℚ K) ∧ Squarefree d ∧ x ^ 2 = (d : K) := by
  classical
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 :=
    (IsGalois.card_aut_eq_finrank ℚ K).trans hrank
  haveI : Finite (K ≃ₐ[ℚ] K) := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial (K ≃ₐ[ℚ] K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : K ≃ₐ[ℚ] K)
  have hσ2 : σ * σ = 1 := by
    have h : σ ^ Nat.card (K ≃ₐ[ℚ] K) = 1 := pow_card_eq_one'
    rwa [hcard, pow_two] at h
  -- the automorphism group is exactly `{1, σ}`
  have huniv : ∀ g : K ≃ₐ[ℚ] K, g = 1 ∨ g = σ := by
    intro g
    by_contra hg
    push Not at hg
    have h1 : ({1, σ, g} : Finset (K ≃ₐ[ℚ] K)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨fun h => hσ h.symm, fun h => hg.1 h.symm⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact fun h => hg.2 h.symm)]
      rw [Finset.card_singleton]
    have h3 := Finset.card_le_card
      (Finset.subset_univ ({1, σ, g} : Finset (K ≃ₐ[ℚ] K)))
    rw [h1, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at h3
    omega
  -- an irrational element of `K`
  obtain ⟨α, hα⟩ : ∃ α : K, α ∉ (⊥ : IntermediateField ℚ K) := by
    by_contra h
    push Not at h
    have hbot : (⊥ : IntermediateField ℚ K) = ⊤ :=
      eq_top_iff.mpr fun y _ => h y
    have h1 := IntermediateField.bot_eq_top_iff_finrank_eq_one.mp hbot
    omega
  -- the anti-fixed element `α − σ α`
  set x₁ : K := α - σ α with hx₁def
  have hσσ : ∀ z : K, σ (σ z) = z := by
    intro z
    have h := congrArg (fun g : K ≃ₐ[ℚ] K => g z) hσ2
    simpa [AlgEquiv.mul_apply] using h
  have hx₁σ : σ x₁ = -x₁ := by
    rw [hx₁def, map_sub, hσσ]
    ring
  have hx₁0 : x₁ ≠ 0 := by
    intro h0
    have hσα : σ α = α := (sub_eq_zero.mp (hx₁def ▸ h0)).symm
    have hfixα : ∀ g : K ≃ₐ[ℚ] K, g • α = α := by
      intro g
      rcases huniv g with rfl | rfl
      · rfl
      · exact hσα
    obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := ℚ)
      (G := K ≃ₐ[ℚ] K) α hfixα
    exact hα (IntermediateField.mem_bot.mpr ⟨r, hr⟩)
  have hx₁bot : x₁ ∉ (⊥ : IntermediateField ℚ K) := by
    intro hmem
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hmem
    have h1 : σ x₁ = x₁ := by rw [← hr]; exact σ.commutes r
    rw [hx₁σ] at h1
    have h2 : x₁ + x₁ = 0 := add_eq_zero_iff_eq_neg.mpr h1.symm
    rw [← two_mul] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact two_ne_zero h3
    · exact hx₁0 h3
  -- its square is a nonzero rational
  have hfixsq : ∀ g : K ≃ₐ[ℚ] K, g • (x₁ ^ 2) = x₁ ^ 2 := by
    intro g
    rcases huniv g with rfl | hgσ
    · rfl
    · rw [hgσ]
      show σ (x₁ ^ 2) = x₁ ^ 2
      rw [map_pow, hx₁σ]
      ring
  obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := ℚ)
    (G := K ≃ₐ[ℚ] K) (x₁ ^ 2) hfixsq
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, map_zero] at hr
    exact pow_ne_zero 2 hx₁0 hr.symm
  -- extract a squarefree integer from `num(r)·den(r)`
  have hn0 : r.num * (r.den : ℤ) ≠ 0 :=
    mul_ne_zero (Rat.num_ne_zero.mpr hr0) (by exact_mod_cast r.den_nz)
  obtain ⟨a, b, hab, hasq⟩ := Nat.sq_mul_squarefree (r.num * (r.den : ℤ)).natAbs
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [show ((0 : ℕ) ^ 2 * a) = 0 by ring] at hab
    exact hn0 (Int.natAbs_eq_zero.mp hab.symm)
  obtain ⟨d, hdsq, hbd⟩ : ∃ d : ℤ, Squarefree d ∧
      (b : ℤ) ^ 2 * d = r.num * (r.den : ℤ) := by
    rcases Int.natAbs_eq (r.num * (r.den : ℤ)) with h | h
    · refine ⟨(a : ℤ), Int.squarefree_natCast.mpr hasq, ?_⟩
      rw [h, ← hab]
      push_cast
      ring
    · refine ⟨-(a : ℤ), ?_, ?_⟩
      · intro z hz
        exact (Int.squarefree_natCast.mpr hasq) z (dvd_neg.mp hz)
      · rw [h, ← hab]
        push_cast
        ring
  -- the scaled generator
  set c₀ : ℚ := (r.den : ℚ) / (b : ℚ) with hc₀def
  have hbq : ((b : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hdenq : ((r.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hc₀0 : c₀ ≠ 0 := div_ne_zero hdenq hbq
  refine ⟨σ, algebraMap ℚ K c₀ * x₁, d, hσ, hσ2, huniv, ?_, ?_, hdsq, ?_⟩
  · rw [map_mul, AlgEquiv.commutes, hx₁σ]
    ring
  · intro hmem
    apply hx₁bot
    have h1 : x₁ = algebraMap ℚ K c₀⁻¹ * (algebraMap ℚ K c₀ * x₁) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc₀0, map_one, one_mul]
    rw [h1]
    exact mul_mem (IntermediateField.algebraMap_mem _ c₀⁻¹) hmem
  · rw [mul_pow, ← map_pow, ← hr, ← map_mul]
    have hkey : c₀ ^ 2 * r = (d : ℚ) := by
      have hnum : (r.num : ℚ) = r * ((r.den : ℕ) : ℚ) :=
        (div_eq_iff hdenq).mp (Rat.num_div_den r)
      have hbdq : ((b : ℕ) : ℚ) ^ 2 * (d : ℚ) =
          (r.num : ℚ) * ((r.den : ℕ) : ℚ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hbd
      apply mul_left_cancel₀ (pow_ne_zero 2 hbq)
      have hbc : ((b : ℕ) : ℚ) * c₀ = ((r.den : ℕ) : ℚ) := by
        rw [hc₀def]
        field_simp
      calc ((b : ℕ) : ℚ) ^ 2 * (c₀ ^ 2 * r)
          = (((b : ℕ) : ℚ) * c₀) ^ 2 * r := by ring
        _ = ((r.den : ℕ) : ℚ) ^ 2 * r := by rw [hbc]
        _ = (r.num : ℚ) * ((r.den : ℕ) : ℚ) := by rw [hnum]; ring
        _ = ((b : ℕ) : ℚ) ^ 2 * (d : ℚ) := hbdq.symm
    rw [hkey]
    exact map_intCast (algebraMap ℚ K) d
set_option backward.isDefEq.respectTransparency false in
/-- **Ramified inertia at a prime dividing the radicand** (PROVEN
2026-07-23 — the ramification half of the quadratic-field
classification): in the setting of `exists_quadratic_generator`
(`Gal(K/ℚ) = {1, σ}`, `x² = d ∈ ℤ` squarefree, `σ x = −x`), for any
prime `q ∣ d` and any prime `Q` of `𝓞 K` above `q`, the nontrivial
automorphism `σ` lies in the inertia subgroup of `Q`. Argument, for
`y ∈ 𝓞 K` with `t = σ y − y`: both `t²` and `t·x` are Galois-invariant
(σ negates both `t` and `x`) integral elements, hence rational
integers `s` and `m` with `m² = d·s`; `q ∣ d` squarefree forces
`q ∣ s` (`q ∣ m²` ⇒ `q ∣ m` ⇒ `q² ∣ d·s` ⇒ `q ∣ (d/q)·s`, and
`q ∤ d/q`); so `t² = s ∈ q·𝓞K ⊆ Q` and `t ∈ Q` by primality. -/
theorem mem_inertia_of_dvd_squarefree
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K] (σ : K ≃ₐ[ℚ] K) (hσ2 : σ * σ = 1)
    (huniv : ∀ g : K ≃ₐ[ℚ] K, g = 1 ∨ g = σ)
    (x : K) (hxσ : σ x = -x) {d : ℤ} (hdsq : Squarefree d)
    (hx2 : x ^ 2 = (d : K)) {q : ℕ} (hq : q.Prime) (hqd : (q : ℤ) ∣ d)
    (Q : Ideal (NumberField.RingOfIntegers K)) [Q.IsPrime]
    (hQmem : ((q : ℕ) : NumberField.RingOfIntegers K) ∈ Q) :
    σ ∈ Q.inertia (K ≃ₐ[ℚ] K) := by
  classical
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  -- `d = q·d'` with `q ∤ d'` (squarefreeness)
  obtain ⟨d', hdd'⟩ := hqd
  have hqd' : ¬ (q : ℤ) ∣ d' := by
    rintro ⟨e, he⟩
    exact hqZ.not_unit (hdsq (q : ℤ) ⟨e, by rw [hdd', he]; ring⟩)
  -- `x` is integral (its square is)
  have hxint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hx2, (eq_intCast (algebraMap ℤ K) d).symm]
    exact isIntegral_algebraMap
  rw [show Q.inertia (K ≃ₐ[ℚ] K) = Q.toAddSubgroup.inertia (K ≃ₐ[ℚ] K)
    from rfl, AddSubgroup.mem_inertia]
  intro y
  rw [Submodule.mem_toAddSubgroup]
  -- the anti-fixed difference in `K`
  set yK : K := algebraMap (NumberField.RingOfIntegers K) K y
  set t : K := σ yK - yK with htdef
  have hσσ : ∀ z : K, σ (σ z) = z := by
    intro z
    have h := congrArg (fun g : K ≃ₐ[ℚ] K => g z) hσ2
    simpa [AlgEquiv.mul_apply] using h
  have htσ : σ t = -t := by
    rw [htdef, map_sub, hσσ]
    ring
  have hyint : IsIntegral ℤ yK := y.2
  have htint : IsIntegral ℤ t :=
    (hyint.map (σ.toAlgHom.restrictScalars ℤ)).sub hyint
  -- `t²` is a rational integer
  obtain ⟨s, hs⟩ : ∃ s : ℤ, (s : K) = t ^ 2 := by
    have hfixsq : ∀ g : K ≃ₐ[ℚ] K, g • (t ^ 2) = t ^ 2 := by
      intro g
      rcases huniv g with rfl | hgσ
      · rfl
      · rw [hgσ]
        show σ (t ^ 2) = t ^ 2
        rw [map_pow, htσ]
        ring
    obtain ⟨s₀, hs₀⟩ := Algebra.IsInvariant.isInvariant (A := ℚ)
      (G := K ≃ₐ[ℚ] K) (t ^ 2) hfixsq
    have hs₀int : IsIntegral ℤ s₀ := by
      rw [← isIntegral_algebraMap_iff (algebraMap ℚ K).injective, hs₀]
      exact htint.pow 2
    obtain ⟨s, hsz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hs₀int
    refine ⟨s, ?_⟩
    rw [show ((s : ℤ) : K) = algebraMap ℚ K ((s : ℤ) : ℚ) from
      (map_intCast (algebraMap ℚ K) s).symm,
      show ((s : ℤ) : ℚ) = algebraMap ℤ ℚ s from rfl, hsz, hs₀]
  -- `t·x` is a rational integer
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : K) = t * x := by
    have hfixm : ∀ g : K ≃ₐ[ℚ] K, g • (t * x) = t * x := by
      intro g
      rcases huniv g with rfl | hgσ
      · rfl
      · rw [hgσ]
        show σ (t * x) = t * x
        rw [map_mul, htσ, hxσ]
        ring
    obtain ⟨m₀, hm₀⟩ := Algebra.IsInvariant.isInvariant (A := ℚ)
      (G := K ≃ₐ[ℚ] K) (t * x) hfixm
    have hm₀int : IsIntegral ℤ m₀ := by
      rw [← isIntegral_algebraMap_iff (algebraMap ℚ K).injective, hm₀]
      exact htint.mul hxint
    obtain ⟨m, hmz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hm₀int
    refine ⟨m, ?_⟩
    rw [show ((m : ℤ) : K) = algebraMap ℚ K ((m : ℤ) : ℚ) from
      (map_intCast (algebraMap ℚ K) m).symm,
      show ((m : ℤ) : ℚ) = algebraMap ℤ ℚ m from rfl, hmz, hm₀]
  -- the norm relation `m² = d·s`, and `q ∣ s`
  have hrel : m ^ 2 = d * s := by
    have h1 : ((m ^ 2 : ℤ) : K) = ((d * s : ℤ) : K) := by
      push_cast
      rw [hm, hs, mul_pow, hx2]
      ring
    exact_mod_cast h1
  obtain ⟨s', hs'⟩ : (q : ℤ) ∣ s := by
    have hqm : (q : ℤ) ∣ m := hqZ.dvd_of_dvd_pow (n := 2)
      ⟨d' * s, by rw [hrel, hdd']; ring⟩
    obtain ⟨m', hm'⟩ := hqm
    have hq0 : ((q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h3 : (q : ℤ) * m' ^ 2 = d' * s := by
      apply mul_left_cancel₀ hq0
      have h4 := hrel
      rw [hm', hdd'] at h4
      linear_combination h4
    rcases hqZ.dvd_mul.mp ⟨m' ^ 2, h3.symm⟩ with h5 | h5
    · exact absurd h5 hqd'
    · exact h5
  -- conclude: `t² = q·s'` lands in `Q`, hence so does `t`
  have hT2 : (σ • y - y) * (σ • y - y) =
      ((q : ℕ) : NumberField.RingOfIntegers K) *
        ((s' : ℤ) : NumberField.RingOfIntegers K) := by
    have hgoal : t * t = ((q : ℕ) : K) * ((s' : ℤ) : K) := by
      rw [← pow_two, ← hs, hs']
      push_cast
      ring
    apply NumberField.RingOfIntegers.ext
    push_cast
    exact hgoal
  have hmul : (σ • y - y) * (σ • y - y) ∈ Q := by
    rw [hT2]
    exact Ideal.mul_mem_right _ Q hQmem
  rcases Ideal.IsPrime.mem_or_mem ‹Q.IsPrime› hmul with h | h <;> exact h

/-- **Quadratic fields ramified only at `2` and `3`** (PROVEN
2026-07-23 from the two leaves above — the Kronecker/Minkowski-style
classification input of the dihedral elimination): a surjective
quadratic character
`θ : Γ ℚ → ℤ/2` with open kernel that is unramified outside `{2, 3}`
(the local inertia group at every prime `q ∉ {2, 3}` dies in the
restriction of `θ` to `Γ ℚ_q`) cuts out one of the seven quadratic
fields `ℚ(√d)`, `d ∈ {-1, 2, -2, 3, -3, 6, -6}`: there is a square
root `x` of `d` in `ℚᵃˡᵍ` such that `θ g = 1` exactly when `g` fixes
`x`. Content: the fixed field `K` of `ker θ` is a degree-2 Galois
extension of `ℚ` (the kernel is an open normal subgroup of index `2`
by surjectivity, and the infinite Galois correspondence applies as in
`open_normal_subgroup_eq_top_of_inertia_le`), so `K = ℚ(√d)` for a
unique squarefree integer `d ∉ {0, 1}`; an odd prime `q` dividing `d`
ramifies in `ℚ(√d)` (the different of `ℤ[√d]ₚ` at `q ∣ d` is
divisible by `√d`), so the inertia at `q` acts nontrivially on `K`,
i.e. maps outside `ker θ` — contradicting the unramifiedness
hypothesis unless `q ∈ {3}`; hence the squarefree `d` divides `6`,
giving the seven listed values (`d = 1` is excluded because `θ` is
surjective, so `K ≠ ℚ`). -/
theorem exists_sqrt_of_quadratic_character_unramified_outside_two_three
    (θ : Γ ℚ →* Multiplicative (ZMod 2))
    (hθsurj : Function.Surjective θ)
    (hopen : IsOpen (θ.ker : Set (Γ ℚ)))
    (hunram : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        θ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1) :
    ∃ d : ℤ,
      (d = -1 ∨ d = 2 ∨ d = -2 ∨ d = 3 ∨ d = -3 ∨ d = 6 ∨ d = -6) ∧
      ∃ x : AlgebraicClosure ℚ, x ^ 2 = (d : AlgebraicClosure ℚ) ∧
        ∀ g : Γ ℚ, θ g = 1 ↔ g x = x := by
  classical
  -- the fixed field of `ker θ` is a degree-2 Galois number field
  haveI hnorm : θ.ker.Normal := θ.normal_ker
  have hclosed : IsClosed (θ.ker : Set (Γ ℚ)) :=
    Subgroup.isClosed_of_isOpen θ.ker hopen
  haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  haveI hacQ : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    ⟨inferInstance, halgQ⟩
  haveI hnormQ : Normal ℚ (AlgebraicClosure ℚ) :=
    IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI hsepQ : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hgalQ : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  set K : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.fixedField (E := AlgebraicClosure ℚ) θ.ker
  have hfix : K.fixingSubgroup = θ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨θ.ker, hclosed⟩
  haveI hfd : FiniteDimensional ℚ K :=
    (InfiniteGalois.isOpen_iff_finite K).mp (by rw [hfix]; exact hopen)
  haveI hgalK : IsGalois ℚ K := (InfiniteGalois.normal_iff_isGalois K).mp
    (by rw [hfix]; exact hnorm)
  haveI : NumberField K := ⟨⟩
  have hrank : Module.finrank ℚ K = 2 := by
    have e1 : (Γ ℚ) ⧸ θ.ker ≃* ((IntermediateField.fixedField
        ((⟨θ.ker, hclosed⟩ : ClosedSubgroup (Γ ℚ)) : Subgroup (Γ ℚ))) ≃ₐ[ℚ]
          (IntermediateField.fixedField
            ((⟨θ.ker, hclosed⟩ : ClosedSubgroup (Γ ℚ)) : Subgroup (Γ ℚ)))) :=
      InfiniteGalois.normalAutEquivQuotient ⟨θ.ker, hclosed⟩
    have e2 : (Γ ℚ) ⧸ θ.ker ≃* Multiplicative (ZMod 2) :=
      QuotientGroup.quotientKerEquivOfSurjective θ hθsurj
    have hcard1 : Nat.card (K ≃ₐ[ℚ] K) = Module.finrank ℚ K :=
      IsGalois.card_aut_eq_finrank ℚ K
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      simp [Nat.card_eq_fintype_card]
    rw [← hcard1]
    exact (((Nat.card_congr e1.toEquiv).symm).trans
      (Nat.card_congr e2.toEquiv)).trans h2
  -- the quadratic generator `x` with `x² = d` squarefree
  obtain ⟨σ, x, d, hσ1, hσ2, huniv, hxσ, hxbot, hdsq, hx2⟩ :=
    exists_quadratic_generator K hrank
  -- no prime `q ∉ {2, 3}` divides `d`
  have hprime : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ¬ ((p : ℤ) ∣ d) := by
    intro p hp hp2 hp3 hpd
    -- the local inertia image at `p` fixes `K`
    have hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat)
        ≤ K.fixingSubgroup := by
      rintro g ⟨τ, hτ, rfl⟩
      rw [hfix]
      exact MonoidHom.mem_ker.mpr (hunram p hp hp2 hp3 τ hτ)
    -- a prime of `𝓞 K` above `p`
    haveI := IsIntegralClosure.isIntegral_algebra ℤ
      (A := NumberField.RingOfIntegers K) K
    have hpZ : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
    haveI hPspan : (Ideal.span {((p : ℤ))} : Ideal ℤ).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr hpZ
    have hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers K)) ≤
        Ideal.span {((p : ℤ))} := by
      intro z hz
      have hz0 : algebraMap ℤ (NumberField.RingOfIntegers K) z = 0 := hz
      have hzK : algebraMap ℤ K z = 0 := by
        rw [IsScalarTower.algebraMap_eq ℤ (NumberField.RingOfIntegers K) K,
          RingHom.comp_apply, hz0, map_zero]
      have hz' : (z : ℤ) = 0 := by
        exact_mod_cast (by simpa using hzK : ((z : ℤ) : K) = 0)
      rw [hz']
      exact Ideal.zero_mem _
    obtain ⟨Q, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
        (S := NumberField.RingOfIntegers K) (Ideal.span {((p : ℤ))}) hker
    haveI := hQprime
    have hpQ : ((p : ℕ) : NumberField.RingOfIntegers K) ∈ Q := by
      have hmem : ((p : ℤ)) ∈ Ideal.span {((p : ℤ))} := Ideal.subset_span rfl
      rw [← hQcomap] at hmem
      simpa using Ideal.mem_comap.mp hmem
    -- trivial inertia (the dictionary) vs. nontrivial inertia (the leaf)
    have hbot : Q.inertia (K ≃ₐ[ℚ] K) = ⊥ :=
      inertia_eq_bot_of_le_fixingSubgroup K hp hle Q hpQ
    have hmem : σ ∈ Q.inertia (K ≃ₐ[ℚ] K) :=
      mem_inertia_of_dvd_squarefree K σ hσ2 huniv x hxσ hdsq hx2 hp hpd Q hpQ
    rw [hbot] at hmem
    exact hσ1 (Subgroup.mem_bot.mp hmem)
  -- enumeration: `d` squarefree with prime divisors in `{2,3}`, `d ≠ 1`
  have hd7 : d = -1 ∨ d = 2 ∨ d = -2 ∨ d = 3 ∨ d = -3 ∨ d = 6 ∨ d = -6 := by
    have hd0 : d ≠ 0 := hdsq.ne_zero
    have hd1 : d ≠ 1 := by
      intro h
      rw [h] at hx2
      have h0 : (x - 1) * (x + 1) = 0 := by
        push_cast at hx2
        linear_combination hx2
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact hxbot (by rw [sub_eq_zero.mp h1]; exact one_mem _)
      · exact hxbot (by
          rw [eq_neg_of_add_eq_zero_left h1]
          exact neg_mem (one_mem _))
    set n : ℕ := d.natAbs with hn
    have hsub : n.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      obtain ⟨hpp, hpd, -⟩ := hp
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_contra hne
      push Not at hne
      refine hprime p hpp hne.1 hne.2 ?_
      exact dvd_trans (Int.natCast_dvd_natCast.mpr hpd)
        (Int.natAbs_dvd.mpr dvd_rfl)
    have hdvd6 : n ∣ 6 := by
      have hsqf : Squarefree n := Int.squarefree_natAbs.mpr hdsq
      calc n = ∏ p ∈ n.primeFactors, p :=
            (Nat.prod_primeFactors_of_squarefree hsqf).symm
        _ ∣ ∏ p ∈ ({2, 3} : Finset ℕ), p :=
            Finset.prod_dvd_prod_of_subset _ _ _ hsub
        _ = 6 := by decide
    have habs : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
      have h1 : 0 < n := Int.natAbs_pos.mpr hd0
      have h6 : n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
      interval_cases n <;> revert hdvd6 <;> decide
    have heq : d = (n : ℤ) ∨ d = -(n : ℤ) := Int.natAbs_eq d
    rcases habs with h | h | h | h <;> rw [h] at heq <;> omega
  -- packaging: the square root in `ℚᵃˡᵍ` and the character dictionary
  refine ⟨d, hd7, (x : AlgebraicClosure ℚ), ?_, ?_⟩
  · have h1 := congrArg (algebraMap K (AlgebraicClosure ℚ)) hx2
    rw [map_pow, map_intCast] at h1
    exact h1
  · intro g
    constructor
    · intro hg
      have hgker : g ∈ K.fixingSubgroup := by
        rw [hfix]
        exact MonoidHom.mem_ker.mpr hg
      exact (K.mem_fixingSubgroup_iff g).mp hgker
        (x : AlgebraicClosure ℚ) x.2
    · intro hgx
      -- `K = ℚ(x)`, so fixing `x` fixes `K` pointwise
      have hxQ : IsIntegral ℚ ((x : AlgebraicClosure ℚ)) :=
        Algebra.IsIntegral.isIntegral _
      haveI : FiniteDimensional ℚ
          (IntermediateField.adjoin ℚ {(x : AlgebraicClosure ℚ)}) :=
        IntermediateField.adjoin.finiteDimensional hxQ
      have hadj : IntermediateField.adjoin ℚ {(x : AlgebraicClosure ℚ)} = K := by
        have hle : IntermediateField.adjoin ℚ {(x : AlgebraicClosure ℚ)} ≤ K :=
          IntermediateField.adjoin_le_iff.mpr (by
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            rw [hz]
            exact x.2)
        refine IntermediateField.eq_of_le_of_finrank_le hle ?_
        rw [hrank]
        have hne1 : Module.finrank ℚ
            (IntermediateField.adjoin ℚ {(x : AlgebraicClosure ℚ)}) ≠ 1 := by
          rw [Ne, IntermediateField.finrank_eq_one_iff]
          intro hbot
          have hxmem : (x : AlgebraicClosure ℚ) ∈
              IntermediateField.adjoin ℚ {(x : AlgebraicClosure ℚ)} :=
            IntermediateField.mem_adjoin_simple_self ℚ _
          rw [hbot, IntermediateField.mem_bot] at hxmem
          obtain ⟨r, hr⟩ := hxmem
          apply hxbot
          rw [IntermediateField.mem_bot]
          refine ⟨r, ?_⟩
          apply Subtype.ext
          rw [← hr]
          exact (IsScalarTower.algebraMap_apply ℚ K (AlgebraicClosure ℚ) r).symm
        have hpos : 0 < Module.finrank ℚ
            (IntermediateField.adjoin ℚ {(x : AlgebraicClosure ℚ)}) :=
          Module.finrank_pos
        omega
      have hfixadj : ∀ z ∈ IntermediateField.adjoin ℚ
          {(x : AlgebraicClosure ℚ)}, g z = z := by
        intro z hz
        induction hz using IntermediateField.adjoin_induction with
        | mem u hu =>
          rw [Set.mem_singleton_iff] at hu
          rw [hu]
          exact hgx
        | algebraMap r => exact g.commutes r
        | add a b _ _ ha hb => rw [map_add, ha, hb]
        | mul a b _ _ ha hb => rw [map_mul, ha, hb]
        | inv a _ ha => rw [map_inv₀, ha]
      have hgker : g ∈ K.fixingSubgroup := by
        rw [← hadj]
        exact ((IntermediateField.adjoin ℚ
          {(x : AlgebraicClosure ℚ)}).mem_fixingSubgroup_iff g).mpr hfixadj
      rw [hfix] at hgker
      exact MonoidHom.mem_ker.mp hgker

/-- **One-dimensionality of the kernel of a nonzero singular `2 × 2`
matrix** (helper, PROVEN 2026-07-23): two vectors annihilated by a
nonzero `2 × 2` matrix are proportional (a nonzero one spans the
kernel). Used by the dihedral dichotomy to convert "commutes with a
nonscalar matrix" into "preserves its eigenline": if the cross-product
of the two kernel vectors were nonzero they would form a basis
annihilated by the matrix, forcing it to vanish. -/
theorem exists_smul_eq_of_mulVec_eq_zero {F : Type*} [Field F]
    {M : Matrix (Fin 2) (Fin 2) F} (hM : M ≠ 0)
    {v w : Fin 2 → F} (hv : Matrix.mulVec M v = 0)
    (hw : Matrix.mulVec M w = 0) (hv0 : v ≠ 0) :
    ∃ c : F, w = c • v := by
  classical
  by_cases hcross : v 0 * w 1 - v 1 * w 0 = 0
  · -- proportional: divide by a nonzero coordinate of `v`
    have hvi : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hv0 (funext fun i => ?_)
      fin_cases i
      · exact hcon.1
      · exact hcon.2
    rcases hvi with h0 | h1
    · refine ⟨w 0 / v 0, funext fun i => ?_⟩
      fin_cases i
      · exact (div_mul_cancel₀ (w 0) h0).symm
      · show w 1 = w 0 / v 0 * v 1
        field_simp
        linear_combination hcross
    · refine ⟨w 1 / v 1, funext fun i => ?_⟩
      fin_cases i
      · show w 0 = w 1 / v 1 * v 0
        field_simp
        linear_combination -hcross
      · exact (div_mul_cancel₀ (w 1) h1).symm
  · -- `(v, w)` would be a basis annihilated by `M`
    exfalso
    apply hM
    have hdetN : (Matrix.of ![![v 0, w 0], ![v 1, w 1]]).det ≠ 0 := by
      rw [Matrix.det_fin_two]
      intro h
      exact hcross (by
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one] at h
        linear_combination h)
    have hMN : M * Matrix.of ![![v 0, w 0], ![v 1, w 1]] = 0 := by
      ext i j
      fin_cases j
      · have hvi := congrFun hv i
        rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] at hvi
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.zero_apply]
        simpa using hvi
      · have hwi := congrFun hw i
        rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] at hwi
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.zero_apply]
        simpa using hwi
    have hN := Matrix.mul_nonsing_inv (Matrix.of ![![v 0, w 0], ![v 1, w 1]])
      (isUnit_iff_ne_zero.mpr hdetN)
    calc M = M * (Matrix.of ![![v 0, w 0], ![v 1, w 1]] *
          (Matrix.of ![![v 0, w 0], ![v 1, w 1]])⁻¹) := by rw [hN, mul_one]
      _ = M * Matrix.of ![![v 0, w 0], ![v 1, w 1]] *
          (Matrix.of ![![v 0, w 0], ![v 1, w 1]])⁻¹ := by rw [mul_assoc]
      _ = 0 := by rw [hMN, zero_mul]

/-- **The Klein-four pivot** (sorry node, isolated 2026-07-23 — the
group/matrix-theoretic core of the dihedral dichotomy, needing no
Galois-theoretic context): let `u : G → GL₂(F)` (`F` algebraically
closed, `2 ≠ 0`) be a representation whose composition with the
projection `π` to `PGL₂(F)` is abelian on the kernel of a surjective
quadratic character `θ`, but which does NOT honestly commute on that
kernel. Then there is a trace-zero invertible `f` — a member of the
Klein four-group configuration — that anticommutes with some `u p`
and commutes-or-anticommutes with EVERY `u g`, `g ∈ G` (not only the
kernel!): the pivot whose `±1` conjugation-sign character is the
switched quadratic character of the dihedral argument.

Intended proof (recorded 2026-07-23). (1) By `hπ` and the scalar
characterization of the center of `GL₂`
(`Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar`),
`hcomm` gives for kernel elements `g, h`:
`u h · u g = a • (u g · u h)` with `a² = 1` by determinants, so `±1`:
the commutator pairing. (2) A noncommuting kernel pair `g₀, h₁`
therefore ANTIcommutes: `a := u g₀`, `b := u h₁`, `ab = -(ba)`; both
have trace `0` (conjugating by the partner negates the trace) and
scalar squares `a² = (-det a) • 1` (Cayley–Hamilton). (3) Any matrix
commuting with both `a` and `b` is scalar (it preserves the two
eigenlines of `a`, which `b` swaps) — via the eigen-machinery and
`exists_smul_eq_of_mulVec_eq_zero`. (4) Hence every kernel element is
a scalar multiple of one of `{1, a, b, ab}`: multiply by the inverse
of the member with the matching sign pattern against `(a, b)` and
apply (3). (5) For `σ ∉ ker θ`, `D := u σ`: `σ²  ∈ ker θ`, so
conjugation by `D²` fixes each of the lines `F·a`, `F·b`, `F·(ab)`
(conjugation by any of `{1, a, b, ab}` does, by the pairing table).
If `D a D⁻¹ ∈ F·a`, take `f := a`. If `D a D⁻¹ = c • b`, then
`D b D⁻¹ = (ε/c) • a` (apply conjugation twice), so
`D (ab) D⁻¹ ∈ F·(ab)`: take `f := ab`. If `D a D⁻¹ = c • (ab)`,
then `D (ab) D⁻¹ ∈ F·a` and `D b D⁻¹ = D (a⁻¹·ab) D⁻¹ ∈ F·b⁻¹ = F·b`
(`b⁻¹ = (1/det b?) hmm — b⁻¹ = δ_b⁻¹ • b` since `b² = δ_b • 1`):
take `f := b`. (6) The global dichotomy for `f`: kernel elements are
scalar multiples of `{1, a, b, ab}`, which commute-or-anticommute
with `f` by the pairing table; an element `g ∉ ker θ` factors as
`(g σ⁻¹) · σ` with `g σ⁻¹ ∈ ker θ`, and `D f D⁻¹ = ±f` (determinant
squares again), so the sign multiplies through. -/
theorem exists_klein_pivot_of_noncommuting_kernel {F : Type*} [Field F]
    [IsAlgClosed F] (h2F : (2 : F) ≠ 0) {G : Type*} [Group G]
    (u : G →* GL (Fin 2) F)
    (π : G →* Matrix.ProjGenLinGroup (Fin 2) F)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (θ : G →* Multiplicative (ZMod 2))
    (hθsurj : Function.Surjective θ)
    (hcomm : ∀ g h : G, θ g = 1 → θ h = 1 → π g * π h = π h * π g)
    (hA : ¬∀ g h' : G, θ g = 1 → θ h' = 1 →
      (u g).val * (u h').val = (u h').val * (u g).val) :
    ∃ f : Matrix (Fin 2) (Fin 2) F,
      Matrix.trace f = 0 ∧ Matrix.det f ≠ 0 ∧
      (∃ p : G, (u p).val * f = -(f * (u p).val)) ∧
      ∀ g : G, (u g).val * f = f * (u g).val ∨
        (u g).val * f = -(f * (u g).val) := by
  classical
  push Not at hA
  obtain ⟨g₀, h₁, hg₀, hh₁, hAB⟩ := hA
  -- value-level bookkeeping
  have hmul : ∀ x y : G, (u (x * y)).val = (u x).val * (u y).val := by
    intro x y
    rw [map_mul]
    rfl
  have hinvr : ∀ x : G, (u x).val * (u x⁻¹).val = 1 := by
    intro x
    rw [← hmul, mul_inv_cancel, map_one]
    rfl
  have hinvl : ∀ x : G, (u x⁻¹).val * (u x).val = 1 := by
    intro x
    rw [← hmul, inv_mul_cancel, map_one]
    rfl
  have hdetu : ∀ x : G, Matrix.det ((u x).val) ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (u x).isUnit).ne_zero
  -- (1) the ±1 commutator pairing on the kernel of θ
  have hpm : ∀ g h' : G, θ g = 1 → θ h' = 1 →
      (u h').val * (u g).val = (u g).val * (u h').val ∨
      (u h').val * (u g).val = -((u g).val * (u h').val) := by
    intro g h' hg hh'
    have hc := hcomm g h' hg hh'
    rw [hπ g, hπ h'] at hc
    have hc2 : (QuotientGroup.mk (u g * u h') :
        GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F)) =
        QuotientGroup.mk (u h' * u g) := hc
    have hz := QuotientGroup.eq.mp hc2
    obtain ⟨a, ha⟩ :=
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hz
    have hscal : Matrix.scalar (Fin 2) a =
        a • (1 : Matrix (Fin 2) (Fin 2) F) :=
      (Matrix.scalar_apply a).trans (Matrix.smul_one_eq_diagonal a).symm
    have hz2 : (u h').val * (u g).val = a • ((u g).val * (u h').val) := by
      have h1 : u h' * u g = (u g * u h') * ((u g * u h')⁻¹ * (u h' * u g)) :=
        (mul_inv_cancel_left _ _).symm
      calc (u h').val * (u g).val
          = (u h' * u g).val := rfl
        _ = ((u g * u h') * ((u g * u h')⁻¹ * (u h' * u g))).val := by
            rw [← h1]
        _ = (u g * u h').val * ((u g * u h')⁻¹ * (u h' * u g)).val := rfl
        _ = (u g * u h').val * (a • 1) := by rw [← ha, hscal]
        _ = a • ((u g).val * (u h').val) := by
            rw [mul_smul_comm, mul_one]
            rfl
    have ha2 : a ^ 2 = 1 := by
      have hdet_ne : Matrix.det ((u g).val * (u h').val) ≠ 0 := by
        rw [Matrix.det_mul]
        exact mul_ne_zero (hdetu g) (hdetu h')
      have hd1 : Matrix.det ((u h').val * (u g).val) =
          Matrix.det ((u g).val * (u h').val) := by
        rw [Matrix.det_mul, Matrix.det_mul, mul_comm]
      rw [hz2, Matrix.det_smul, Fintype.card_fin] at hd1
      have h2 : (a ^ 2 - 1) * Matrix.det ((u g).val * (u h').val) = 0 := by
        rw [sub_mul, one_mul, hd1, sub_self]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 hdet_ne
    have ha1 : a = 1 ∨ a = -1 := by
      have h4 : (a - 1) * (a + 1) = 0 := by linear_combination ha2
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact Or.inl (sub_eq_zero.mp h5)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h5)
    rcases ha1 with rfl | rfl
    · left
      rw [hz2, one_smul]
    · right
      rw [hz2, neg_smul, one_smul]
  -- (2) the anticommuting pair and its products
  have hanti : (u g₀).val * (u h₁).val = -((u h₁).val * (u g₀).val) := by
    rcases hpm g₀ h₁ hg₀ hh₁ with h1 | h1
    · exact absurd h1.symm hAB
    · rw [h1, neg_neg]
  have hanti' : (u h₁).val * (u g₀).val = -((u g₀).val * (u h₁).val) := by
    rw [hanti, neg_neg]
  have h_ab_a : ((u g₀).val * (u h₁).val) * (u g₀).val =
      -((u g₀).val * ((u g₀).val * (u h₁).val)) := by
    rw [mul_assoc, hanti', mul_neg]
  have h_a_ab : (u g₀).val * ((u g₀).val * (u h₁).val) =
      -(((u g₀).val * (u h₁).val) * (u g₀).val) := by
    rw [h_ab_a, neg_neg]
  -- (3) trace zero from an anticommuting partner
  have htrace0 : ∀ x y : G,
      (u x).val * (u y).val = -((u y).val * (u x).val) →
      Matrix.trace ((u x).val) = 0 := by
    intro x y hxy
    have h1 : (u x).val * ((u y).val * (u y⁻¹).val) =
        -((u y).val * (u x).val * (u y⁻¹).val) := by
      rw [← mul_assoc, hxy, neg_mul]
    rw [hinvr y, mul_one] at h1
    have h3 := congrArg Matrix.trace h1
    rw [Matrix.trace_neg, mul_assoc, Matrix.trace_mul_comm, mul_assoc,
      hinvl y, mul_one] at h3
    have h4 : (2 : F) • Matrix.trace ((u x).val) = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr h3
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 h2F
    · exact h5
  -- (4) Cayley–Hamilton squares and the remaining pair products
  have hsq : ∀ x : G, Matrix.trace ((u x).val) = 0 →
      (u x).val * (u x).val = (-Matrix.det ((u x).val)) •
        (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro x htr
    have hCH0 := Matrix.aeval_self_charpoly ((u x).val)
    rw [Matrix.charpoly_fin_two, map_add, map_sub, map_pow, Polynomial.aeval_X,
      map_mul, Polynomial.aeval_C, htr, map_zero, zero_mul, sub_zero,
      Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] at hCH0
    rw [← sq, neg_smul]
    exact eq_neg_of_add_eq_zero_left hCH0
  have htra := htrace0 g₀ h₁ hanti
  have htrb := htrace0 h₁ g₀ hanti'
  have htrab : Matrix.trace ((u g₀).val * (u h₁).val) = 0 := by
    have h1 := htrace0 (g₀ * h₁) g₀ (by rw [hmul]; exact h_ab_a)
    rwa [hmul] at h1
  have hsqa := hsq g₀ htra
  have hsqb := hsq h₁ htrb
  have hsqab : ((u g₀).val * (u h₁).val) * ((u g₀).val * (u h₁).val) =
      (-Matrix.det ((u g₀).val * (u h₁).val)) •
        (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 := hsq (g₀ * h₁) (by rw [hmul]; exact htrab)
    rwa [hmul] at h1
  have hδa : (-Matrix.det ((u g₀).val)) ≠ 0 := neg_ne_zero.mpr (hdetu g₀)
  have hδb : (-Matrix.det ((u h₁).val)) ≠ 0 := neg_ne_zero.mpr (hdetu h₁)
  have hδab : (-Matrix.det ((u g₀).val * (u h₁).val)) ≠ 0 := by
    rw [Matrix.det_mul]
    exact neg_ne_zero.mpr (mul_ne_zero (hdetu g₀) (hdetu h₁))
  have h_b_ab : (u h₁).val * ((u g₀).val * (u h₁).val) =
      -(((u g₀).val * (u h₁).val) * (u h₁).val) := by
    rw [← mul_assoc, hanti', neg_mul]
  have h_ab_b : ((u g₀).val * (u h₁).val) * (u h₁).val =
      -((u h₁).val * ((u g₀).val * (u h₁).val)) := by
    rw [h_b_ab, neg_neg]
  have h_abb : ((u g₀).val * (u h₁).val) * (u h₁).val =
      (-Matrix.det ((u h₁).val)) • (u g₀).val := by
    rw [mul_assoc, hsqb, mul_smul_comm, mul_one]
  -- (5) the commutant of the anticommuting pair is scalar
  have hcentral : ∀ M : Matrix (Fin 2) (Fin 2) F,
      M * (u g₀).val = (u g₀).val * M → M * (u h₁).val = (u h₁).val * M →
      ∃ c : F, M = c • 1 := by
    obtain ⟨s, hs2⟩ := IsAlgClosed.exists_pow_nat_eq
      (-Matrix.det ((u g₀).val)) (n := 2) (by norm_num)
    have hfact : ((u g₀).val - s • 1) * ((u g₀).val + s • 1) = 0 := by
      have h1 : ((u g₀).val - s • 1) * ((u g₀).val + s • 1) =
          (u g₀).val * (u g₀).val -
            (s * s) • (1 : Matrix (Fin 2) (Fin 2) F) := by
        simp only [mul_add, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul,
          mul_one, smul_sub, smul_smul]
        abel
      rw [h1, hsqa, ← hs2, sq, sub_self]
    obtain ⟨t, ht2, htdet⟩ : ∃ t : F, t ^ 2 = -Matrix.det ((u g₀).val) ∧
        Matrix.det ((u g₀).val - t • 1) = 0 := by
      have h1 : Matrix.det ((u g₀).val - s • 1) *
          Matrix.det ((u g₀).val + s • 1) = 0 := by
        rw [← Matrix.det_mul, hfact]
        exact Matrix.det_zero
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact ⟨s, hs2, h2⟩
      · refine ⟨-s, by rw [neg_sq]; exact hs2, ?_⟩
        rw [neg_smul, sub_neg_eq_add]
        exact h2
    have htne : t ≠ 0 := by
      intro h0
      apply hdetu g₀
      apply neg_eq_zero.mp
      rw [← ht2, h0]
      exact zero_pow (by norm_num)
    obtain ⟨w, hw0, hwker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr htdet
    have haw : Matrix.mulVec ((u g₀).val) w = t • w := by
      have h1 := hwker
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        sub_eq_zero] at h1
      exact h1
    have haw' : Matrix.mulVec ((u g₀).val)
        (Matrix.mulVec ((u h₁).val) w) =
        (-t) • Matrix.mulVec ((u h₁).val) w := by
      rw [Matrix.mulVec_mulVec, hanti, Matrix.neg_mulVec,
        ← Matrix.mulVec_mulVec, haw, Matrix.mulVec_smul, ← neg_smul]
    have hans : (u g₀).val - t • 1 ≠ 0 := by
      intro h0
      have hax : (u g₀).val = t • 1 := by rwa [sub_eq_zero] at h0
      apply hAB
      rw [hax, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    have hw'ne : Matrix.mulVec ((u h₁).val) w ≠ 0 := by
      intro h0
      apply hw0
      have h2 : Matrix.mulVec ((u h₁⁻¹).val)
          (Matrix.mulVec ((u h₁).val) w) = w := by
        rw [Matrix.mulVec_mulVec, hinvl, Matrix.one_mulVec]
      rw [h0, Matrix.mulVec_zero] at h2
      exact h2.symm
    intro M hMa hMb
    have hMw : ∃ c : F, Matrix.mulVec M w = c • w := by
      apply exists_smul_eq_of_mulVec_eq_zero hans hwker ?_ hw0
      have hswap : ((u g₀).val - t • 1) * M = M * ((u g₀).val - t • 1) := by
        rw [sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
          hMa]
      rw [Matrix.mulVec_mulVec, hswap, ← Matrix.mulVec_mulVec, hwker,
        Matrix.mulVec_zero]
    obtain ⟨α, hα⟩ := hMw
    refine ⟨α, ?_⟩
    by_contra hMne
    have hNne : M - α • 1 ≠ 0 := fun h0 => hMne (by rwa [sub_eq_zero] at h0)
    have hNw : Matrix.mulVec (M - α • 1) w = 0 := by
      rw [Matrix.sub_mulVec, hα, Matrix.smul_mulVec, Matrix.one_mulVec,
        sub_self]
    have hNw' : Matrix.mulVec (M - α • 1)
        (Matrix.mulVec ((u h₁).val) w) = 0 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_mulVec, hMb, ← Matrix.mulVec_mulVec, hα,
        Matrix.mulVec_smul, sub_self]
    obtain ⟨c, hc⟩ := exists_smul_eq_of_mulVec_eq_zero hNne hNw hNw' hw0
    have h1 : (-t) • (c • w) = t • (c • w) := by
      calc (-t) • (c • w)
          = (-t) • Matrix.mulVec ((u h₁).val) w := by rw [← hc]
        _ = Matrix.mulVec ((u g₀).val)
            (Matrix.mulVec ((u h₁).val) w) := haw'.symm
        _ = Matrix.mulVec ((u g₀).val) (c • w) := by rw [hc]
        _ = c • Matrix.mulVec ((u g₀).val) w := by rw [Matrix.mulVec_smul]
        _ = c • (t • w) := by rw [haw]
        _ = t • (c • w) := smul_comm c t w
    have h2 : ((-t) - t) • (c • w) = 0 := by
      rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · have h4 : (2 : F) * t = 0 := by linear_combination -h3
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact h2F h5
      · exact htne h5
    · rw [← hc] at h3
      exact hw'ne h3
  -- (6) the V₄ classification: every kernel element is a scalar
  -- multiple of one of {1, a, b, ab}
  have hV4 : ∀ g : G, θ g = 1 →
      (∃ c : F, (u g).val = c • (1 : Matrix (Fin 2) (Fin 2) F)) ∨
      (∃ c : F, (u g).val = c • (u g₀).val) ∨
      (∃ c : F, (u g).val = c • (u h₁).val) ∨
      (∃ c : F, (u g).val = c • ((u g₀).val * (u h₁).val)) := by
    intro g hg
    rcases hpm g₀ g hg₀ hg with hga | hga <;>
      rcases hpm h₁ g hh₁ hg with hgb | hgb
    · exact Or.inl (hcentral _ hga hgb)
    · -- commutes with a, anticommutes with b: multiple of a
      have hZb : ((u g).val * (u g₀).val) * (u h₁).val =
          (u h₁).val * ((u g).val * (u g₀).val) := by
        rw [mul_assoc, hanti, mul_neg, ← mul_assoc, hgb, neg_mul, neg_neg,
          mul_assoc]
      have hZa : ((u g).val * (u g₀).val) * (u g₀).val =
          (u g₀).val * ((u g).val * (u g₀).val) := by
        calc ((u g).val * (u g₀).val) * (u g₀).val
            = (u g).val * ((u g₀).val * (u g₀).val) := by rw [mul_assoc]
          _ = (-Matrix.det ((u g₀).val)) • ((u g).val * 1) := by
              rw [hsqa, mul_smul_comm]
          _ = (-Matrix.det ((u g₀).val)) • (u g).val := by rw [mul_one]
          _ = (u g₀).val * ((u g).val * (u g₀).val) := by
              rw [← mul_assoc, ← hga, mul_assoc, hsqa, mul_smul_comm, mul_one]
      obtain ⟨c, hcz⟩ := hcentral _ hZa hZb
      have h7 : ((u g).val * (u g₀).val) * (u g₀).val = c • (u g₀).val := by
        rw [hcz, smul_mul_assoc, one_mul]
      rw [mul_assoc, hsqa, mul_smul_comm, mul_one] at h7
      have h8 : (u g).val = (-Matrix.det ((u g₀).val))⁻¹ •
          (c • (u g₀).val) := by
        rw [← h7, inv_smul_smul₀ hδa]
      refine Or.inr (Or.inl ⟨(-Matrix.det ((u g₀).val))⁻¹ * c, ?_⟩)
      rw [h8, smul_smul]
    · -- anticommutes with a, commutes with b: multiple of b
      have hZa : ((u g).val * (u h₁).val) * (u g₀).val =
          (u g₀).val * ((u g).val * (u h₁).val) := by
        rw [mul_assoc, hanti', mul_neg, ← mul_assoc, hga, neg_mul, neg_neg,
          mul_assoc]
      have hZb : ((u g).val * (u h₁).val) * (u h₁).val =
          (u h₁).val * ((u g).val * (u h₁).val) := by
        calc ((u g).val * (u h₁).val) * (u h₁).val
            = (u g).val * ((u h₁).val * (u h₁).val) := by rw [mul_assoc]
          _ = (-Matrix.det ((u h₁).val)) • ((u g).val * 1) := by
              rw [hsqb, mul_smul_comm]
          _ = (-Matrix.det ((u h₁).val)) • (u g).val := by rw [mul_one]
          _ = (u h₁).val * ((u g).val * (u h₁).val) := by
              rw [← mul_assoc, ← hgb, mul_assoc, hsqb, mul_smul_comm, mul_one]
      obtain ⟨c, hcz⟩ := hcentral _ hZa hZb
      have h7 : ((u g).val * (u h₁).val) * (u h₁).val = c • (u h₁).val := by
        rw [hcz, smul_mul_assoc, one_mul]
      rw [mul_assoc, hsqb, mul_smul_comm, mul_one] at h7
      have h8 : (u g).val = (-Matrix.det ((u h₁).val))⁻¹ •
          (c • (u h₁).val) := by
        rw [← h7, inv_smul_smul₀ hδb]
      refine Or.inr (Or.inr (Or.inl ⟨(-Matrix.det ((u h₁).val))⁻¹ * c, ?_⟩))
      rw [h8, smul_smul]
    · -- anticommutes with both: multiple of ab
      have hZa : ((u g).val * ((u g₀).val * (u h₁).val)) * (u g₀).val =
          (u g₀).val * ((u g).val * ((u g₀).val * (u h₁).val)) := by
        rw [mul_assoc, h_ab_a, mul_neg, ← mul_assoc, hga, neg_mul, neg_neg,
          mul_assoc]
      have hgb' : (u h₁).val * (u g).val = -((u g).val * (u h₁).val) := by
        rw [hgb, neg_neg]
      have hZb : ((u g).val * ((u g₀).val * (u h₁).val)) * (u h₁).val =
          (u h₁).val * ((u g).val * ((u g₀).val * (u h₁).val)) := by
        calc ((u g).val * ((u g₀).val * (u h₁).val)) * (u h₁).val
            = (u g).val * (((u g₀).val * (u h₁).val) * (u h₁).val) := by
              rw [mul_assoc]
          _ = (-Matrix.det ((u h₁).val)) • ((u g).val * (u g₀).val) := by
              rw [h_abb, mul_smul_comm]
          _ = -((-Matrix.det ((u h₁).val)) • ((u g₀).val * (u g).val)) := by
              rw [hga, smul_neg]
          _ = (u h₁).val * ((u g).val * ((u g₀).val * (u h₁).val)) := by
              rw [← mul_assoc, hgb', neg_mul, mul_assoc, h_b_ab, mul_neg,
                neg_neg, h_abb, mul_smul_comm, hga, smul_neg]
      obtain ⟨c, hcz⟩ := hcentral _ hZa hZb
      have h7 : ((u g).val * ((u g₀).val * (u h₁).val)) *
          ((u g₀).val * (u h₁).val) =
          c • ((u g₀).val * (u h₁).val) := by
        rw [hcz, smul_mul_assoc, one_mul]
      rw [mul_assoc, hsqab, mul_smul_comm, mul_one] at h7
      have h8 : (u g).val = (-Matrix.det ((u g₀).val * (u h₁).val))⁻¹ •
          (c • ((u g₀).val * (u h₁).val)) := by
        rw [← h7, inv_smul_smul₀ hδab]
      refine Or.inr (Or.inr (Or.inr
        ⟨(-Matrix.det ((u g₀).val * (u h₁).val))⁻¹ * c, ?_⟩))
      rw [h8, smul_smul]
  -- (7) the pairing table over the kernel
  have htable : ∀ g : G, θ g = 1 →
      ∀ X : Matrix (Fin 2) (Fin 2) F,
        (X = (u g₀).val ∨ X = (u h₁).val ∨
          X = (u g₀).val * (u h₁).val) →
        (u g).val * X = X * (u g).val ∨
        (u g).val * X = -(X * (u g).val) := by
    intro g hg X hX
    rcases hV4 g hg with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
    · left
      rw [hc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    · rcases hX with rfl | rfl | rfl
      · left
        rw [hc, smul_mul_assoc, mul_smul_comm]
      · right
        rw [hc, smul_mul_assoc, mul_smul_comm, hanti, smul_neg]
      · right
        rw [hc, smul_mul_assoc, mul_smul_comm, h_a_ab, smul_neg]
    · rcases hX with rfl | rfl | rfl
      · right
        rw [hc, smul_mul_assoc, mul_smul_comm, hanti', smul_neg]
      · left
        rw [hc, smul_mul_assoc, mul_smul_comm]
      · right
        rw [hc, smul_mul_assoc, mul_smul_comm, h_b_ab, smul_neg]
    · rcases hX with rfl | rfl | rfl
      · right
        rw [hc, smul_mul_assoc, mul_smul_comm, h_ab_a, smul_neg]
      · right
        rw [hc, smul_mul_assoc, mul_smul_comm, h_ab_b, smul_neg]
      · left
        rw [hc, smul_mul_assoc, mul_smul_comm]
  -- (8) an element outside the kernel
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : G, θ σ₀ ≠ 1 := by
    obtain ⟨σ₁, hσ₁⟩ := hθsurj (Multiplicative.ofAdd (1 : ZMod 2))
    refine ⟨σ₁, ?_⟩
    rw [hσ₁]
    decide
  -- (9) the conjugation-fixed pivot among {a, b, ab}
  have hDcase : ∃ f : Matrix (Fin 2) (Fin 2) F,
      (f = (u g₀).val ∨ f = (u h₁).val ∨
        f = (u g₀).val * (u h₁).val) ∧
      ((u σ₀).val * f = f * (u σ₀).val ∨
        (u σ₀).val * f = -(f * (u σ₀).val)) := by
    -- un-conjugation and sign extraction helpers
    have hunconj : ∀ Y Z : Matrix (Fin 2) (Fin 2) F,
        (u σ₀).val * Y * (u σ₀⁻¹).val = Z →
        (u σ₀).val * Y = Z * (u σ₀).val := by
      intro Y Z hYZ
      have h5 : (u σ₀).val * Y * ((u σ₀⁻¹).val * (u σ₀).val) =
          Z * (u σ₀).val := by
        rw [← mul_assoc, hYZ]
      rwa [hinvl, mul_one] at h5
    have hsq1 : ∀ e : F, e ^ 2 = 1 → e = 1 ∨ e = -1 := by
      intro e he
      have h4 : (e - 1) * (e + 1) = 0 := by linear_combination he
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact Or.inl (sub_eq_zero.mp h5)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h5)
    have hsign : ∀ (x : G) (e : F),
        (u σ₀).val * (u x).val * (u σ₀⁻¹).val = e • (u x).val →
        (u σ₀).val * (u x).val = (u x).val * (u σ₀).val ∨
        (u σ₀).val * (u x).val = -((u x).val * (u σ₀).val) := by
      intro x e hx
      have h2 : (u σ₀).val * (u x).val = e • ((u x).val * (u σ₀).val) := by
        have h3 := hunconj ((u x).val) (e • (u x).val) hx
        rwa [smul_mul_assoc] at h3
      have he2 : e ^ 2 = 1 := by
        have hd := congrArg Matrix.det h2
        rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin,
          Matrix.det_mul] at hd
        have h4 : (e ^ 2 - 1) * (Matrix.det ((u x).val) *
            Matrix.det ((u σ₀).val)) = 0 := by
          linear_combination -hd
        rcases mul_eq_zero.mp h4 with h5 | h5
        · exact sub_eq_zero.mp h5
        · rcases mul_eq_zero.mp h5 with h6 | h6
          · exact absurd h6 (hdetu x)
          · exact absurd h6 (hdetu σ₀)
      rcases hsq1 e he2 with rfl | rfl
      · left
        rw [h2, one_smul]
      · right
        rw [h2, neg_smul, one_smul]
    -- conjugation bookkeeping
    have hθconj : θ (σ₀ * g₀ * σ₀⁻¹) = 1 := by
      rw [map_mul, map_mul, hg₀, mul_one, map_inv, mul_inv_cancel]
    have hconjval : (u (σ₀ * g₀ * σ₀⁻¹)).val =
        (u σ₀).val * (u g₀).val * (u σ₀⁻¹).val := by
      rw [hmul, hmul]
    have hθσσ : θ (σ₀ * σ₀) = 1 := by
      rw [map_mul]
      exact (by decide : ∀ z : Multiplicative (ZMod 2), z * z = 1) (θ σ₀)
    have hDDi2 : ((u σ₀).val * (u σ₀).val) *
        ((u σ₀⁻¹).val * (u σ₀⁻¹).val) = 1 := by
      rw [mul_assoc, ← mul_assoc ((u σ₀).val) ((u σ₀⁻¹).val) ((u σ₀⁻¹).val),
        hinvr, one_mul, hinvr]
    have hDD_a := htable (σ₀ * σ₀) hθσσ ((u g₀).val) (Or.inl rfl)
    rw [hmul] at hDD_a
    have hDDa2 : ((u σ₀).val * (u σ₀).val) * (u g₀).val *
        ((u σ₀⁻¹).val * (u σ₀⁻¹).val) = (u g₀).val ∨
        ((u σ₀).val * (u σ₀).val) * (u g₀).val *
        ((u σ₀⁻¹).val * (u σ₀⁻¹).val) = -(u g₀).val := by
      rcases hDD_a with h4 | h4
      · left
        rw [h4, mul_assoc, hDDi2, mul_one]
      · right
        rw [h4, neg_mul, mul_assoc, hDDi2, mul_one]
    have hassoc : (u σ₀).val * ((u σ₀).val * (u g₀).val * (u σ₀⁻¹).val) *
        (u σ₀⁻¹).val = ((u σ₀).val * (u σ₀).val) * (u g₀).val *
        ((u σ₀⁻¹).val * (u σ₀⁻¹).val) := by
      simp only [mul_assoc]
    have hmult : ((u σ₀).val * (u g₀).val * (u σ₀⁻¹).val) *
        ((u σ₀).val * (u h₁).val * (u σ₀⁻¹).val) =
        (u σ₀).val * ((u g₀).val * (u h₁).val) * (u σ₀⁻¹).val := by
      simp only [mul_assoc]
      rw [← mul_assoc ((u σ₀⁻¹).val) ((u σ₀).val), hinvl, one_mul]
    -- the case analysis on where conjugation sends `a`
    rcases hV4 (σ₀ * g₀ * σ₀⁻¹) hθconj with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ |
      ⟨c, hc⟩
    · -- `a` conjugates to a scalar: impossible (`a` would be scalar)
      exfalso
      rw [hconjval] at hc
      have h2 := hunconj ((u g₀).val)
        (c • (1 : Matrix (Fin 2) (Fin 2) F)) hc
      rw [smul_mul_assoc, one_mul] at h2
      have h3 : ((u σ₀⁻¹).val * (u σ₀).val) * (u g₀).val =
          c • ((u σ₀⁻¹).val * (u σ₀).val) := by
        rw [mul_assoc, h2, mul_smul_comm]
      rw [hinvl, one_mul] at h3
      apply hAB
      rw [h3, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    · -- `a` conjugates into its own line: the pivot is `a`
      rw [hconjval] at hc
      exact ⟨(u g₀).val, Or.inl rfl, hsign g₀ c hc⟩
    · -- `a` conjugates into the `b`-line: the pivot is `ab`
      rw [hconjval] at hc
      have hcne : c ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hc
        have h4 : (u σ₀).val * (u g₀).val * ((u σ₀⁻¹).val * (u σ₀).val) =
            0 := by
          rw [← mul_assoc, hc, zero_mul]
        rw [hinvl, mul_one] at h4
        have h5 : ((u σ₀⁻¹).val * (u σ₀).val) * (u g₀).val = 0 := by
          rw [mul_assoc, h4, mul_zero]
        rw [hinvl, one_mul] at h5
        apply hdetu g₀
        rw [h5]
        exact Matrix.det_zero
      have hkey : c • ((u σ₀).val * (u h₁).val * (u σ₀⁻¹).val) =
          ((u σ₀).val * (u σ₀).val) * (u g₀).val *
          ((u σ₀⁻¹).val * (u σ₀⁻¹).val) := by
        rw [← hassoc, hc, mul_smul_comm, smul_mul_assoc]
      obtain ⟨ε, hε⟩ : ∃ ε : F, (u σ₀).val * (u h₁).val * (u σ₀⁻¹).val =
          ε • (u g₀).val := by
        rcases hDDa2 with h4 | h4
        · refine ⟨c⁻¹, ?_⟩
          rw [← inv_smul_smul₀ hcne ((u σ₀).val * (u h₁).val *
            (u σ₀⁻¹).val), hkey, h4]
        · refine ⟨-c⁻¹, ?_⟩
          rw [← inv_smul_smul₀ hcne ((u σ₀).val * (u h₁).val *
            (u σ₀⁻¹).val), hkey, h4, smul_neg, neg_smul]
      have hconjab : (u σ₀).val * ((u g₀).val * (u h₁).val) *
          (u σ₀⁻¹).val = (-(c * ε)) • ((u g₀).val * (u h₁).val) := by
        rw [← hmult, hc, hε, smul_mul_assoc, mul_smul_comm, smul_smul,
          hanti', smul_neg, neg_smul]
      have hconjab' : (u σ₀).val * (u (g₀ * h₁)).val * (u σ₀⁻¹).val =
          (-(c * ε)) • (u (g₀ * h₁)).val := by
        rw [hmul]
        exact hconjab
      have hdi := hsign (g₀ * h₁) (-(c * ε)) hconjab'
      rw [hmul] at hdi
      exact ⟨(u g₀).val * (u h₁).val, Or.inr (Or.inr rfl), hdi⟩
    · -- `a` conjugates into the `ab`-line: the pivot is `b`
      rw [hconjval] at hc
      have hcne : c ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hc
        have h4 : (u σ₀).val * (u g₀).val * ((u σ₀⁻¹).val * (u σ₀).val) =
            0 := by
          rw [← mul_assoc, hc, zero_mul]
        rw [hinvl, mul_one] at h4
        have h5 : ((u σ₀⁻¹).val * (u σ₀).val) * (u g₀).val = 0 := by
          rw [mul_assoc, h4, mul_zero]
        rw [hinvl, one_mul] at h5
        apply hdetu g₀
        rw [h5]
        exact Matrix.det_zero
      have hkey : c • ((u σ₀).val * ((u g₀).val * (u h₁).val) *
          (u σ₀⁻¹).val) = ((u σ₀).val * (u σ₀).val) * (u g₀).val *
          ((u σ₀⁻¹).val * (u σ₀⁻¹).val) := by
        rw [← hassoc, hc, mul_smul_comm, smul_mul_assoc]
      obtain ⟨ε, hε⟩ : ∃ ε : F, (u σ₀).val * ((u g₀).val * (u h₁).val) *
          (u σ₀⁻¹).val = ε • (u g₀).val := by
        rcases hDDa2 with h4 | h4
        · refine ⟨c⁻¹, ?_⟩
          rw [← inv_smul_smul₀ hcne ((u σ₀).val * ((u g₀).val *
            (u h₁).val) * (u σ₀⁻¹).val), hkey, h4]
        · refine ⟨-c⁻¹, ?_⟩
          rw [← inv_smul_smul₀ hcne ((u σ₀).val * ((u g₀).val *
            (u h₁).val) * (u σ₀⁻¹).val), hkey, h4, smul_neg, neg_smul]
      have h6 : ((u g₀).val * (u h₁).val) *
          ((u σ₀).val * (u h₁).val * (u σ₀⁻¹).val) =
          (c⁻¹ * ε) • (u g₀).val := by
        have h7 : (c • ((u g₀).val * (u h₁).val)) *
            ((u σ₀).val * (u h₁).val * (u σ₀⁻¹).val) =
            ε • (u g₀).val := by
          rw [← hc, hmult, hε]
        rw [smul_mul_assoc] at h7
        rw [← inv_smul_smul₀ hcne (((u g₀).val * (u h₁).val) *
          ((u σ₀).val * (u h₁).val * (u σ₀⁻¹).val)), h7, smul_smul]
      have h8 : ((u g₀).val * (u g₀).val) * ((u h₁).val *
          ((u σ₀).val * (u h₁).val * (u σ₀⁻¹).val)) =
          (u g₀).val * ((c⁻¹ * ε) • (u g₀).val) := by
        rw [mul_assoc, ← mul_assoc ((u g₀).val) ((u h₁).val)
          ((u σ₀).val * (u h₁).val * (u σ₀⁻¹).val), h6]
      rw [hsqa, smul_mul_assoc, one_mul, mul_smul_comm, hsqa,
        smul_smul] at h8
      have h9 : (u h₁).val * ((u σ₀).val * (u h₁).val * (u σ₀⁻¹).val) =
          ((-Matrix.det ((u g₀).val))⁻¹ * (c⁻¹ * ε *
            (-Matrix.det ((u g₀).val)))) • 1 := by
        rw [← inv_smul_smul₀ hδa ((u h₁).val * ((u σ₀).val * (u h₁).val *
          (u σ₀⁻¹).val)), h8, smul_smul]
      have h10 : ((u h₁).val * (u h₁).val) *
          ((u σ₀).val * (u h₁).val * (u σ₀⁻¹).val) =
          (u h₁).val * (((-Matrix.det ((u g₀).val))⁻¹ * (c⁻¹ * ε *
            (-Matrix.det ((u g₀).val)))) • 1) := by
        rw [mul_assoc, h9]
      rw [hsqb, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h10
      have h11 : (u σ₀).val * (u h₁).val * (u σ₀⁻¹).val =
          ((-Matrix.det ((u h₁).val))⁻¹ * ((-Matrix.det ((u g₀).val))⁻¹ *
            (c⁻¹ * ε * (-Matrix.det ((u g₀).val))))) • (u h₁).val := by
        rw [← inv_smul_smul₀ hδb ((u σ₀).val * (u h₁).val * (u σ₀⁻¹).val),
          h10, smul_smul]
      exact ⟨(u h₁).val, Or.inr (Or.inl rfl), hsign h₁ _ h11⟩
  -- assembly: the pivot has all four required properties
  obtain ⟨f, hfmem, hDsign⟩ := hDcase
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · rcases hfmem with rfl | rfl | rfl
    · exact htra
    · exact htrb
    · exact htrab
  · rcases hfmem with rfl | rfl | rfl
    · exact hdetu g₀
    · exact hdetu h₁
    · rw [Matrix.det_mul]
      exact mul_ne_zero (hdetu g₀) (hdetu h₁)
  · rcases hfmem with rfl | rfl | rfl
    · exact ⟨h₁, hanti'⟩
    · exact ⟨g₀, hanti⟩
    · exact ⟨g₀, h_a_ab⟩
  · intro g
    by_cases hg : θ g = 1
    · exact htable g hg f hfmem
    · have hgk : θ (g * σ₀⁻¹) = 1 := by
        have h1 : ∀ y z : Multiplicative (ZMod 2), y ≠ 1 → z ≠ 1 →
            y * z⁻¹ = 1 := by decide
        rw [map_mul, map_inv]
        exact h1 _ _ hg hσ₀
      have hgfac : (u g).val = (u (g * σ₀⁻¹)).val * (u σ₀).val := by
        rw [← hmul, inv_mul_cancel_right]
      rcases htable (g * σ₀⁻¹) hgk f hfmem with hX | hX <;>
        rcases hDsign with hD | hD
      · left
        rw [hgfac, mul_assoc, hD, ← mul_assoc, hX, mul_assoc]
      · right
        rw [hgfac, mul_assoc, hD, mul_neg, neg_inj, ← mul_assoc, hX,
          mul_assoc]
      · right
        rw [hgfac, mul_assoc, hD, ← mul_assoc, hX, neg_mul, mul_assoc]
      · left
        rw [hgfac, mul_assoc, hD, mul_neg, ← mul_assoc, hX, neg_mul, neg_neg,
          mul_assoc]

set_option maxHeartbeats 1000000 in
/-- **The dihedral dichotomy: a common eigenvector after a possible
field switch** (DERIVED 2026-07-23 from the Klein-four pivot
`exists_klein_pivot_of_noncommuting_kernel` above — the reduction is
PROVEN, and this is the SOUND replacement for the false "common
eigenvector on `ker θ` itself" step): the projective-commutativity
and trace-zero data of the dihedral situation produce a surjective
quadratic character `θ'` — NOT necessarily `θ` — trivial on the
kernel of `ρ`, such that `u` restricted to `ker θ'` has a genuine
common eigenvector.

Soundness note (recorded 2026-07-23; see the 2026-07-23 decomposition
commit): `hcomm` only makes `u (ker θ)` projectively abelian, which
admits the Klein-four sub-case where `u (ker θ)` maps onto an
irreducible `V₄ ⊂ PGL₂` of anticommuting trace-zero
involutions-mod-scalars and `ρ|_{ker θ}` has NO stable line; Serre's
dihedral argument there switches to a different quadratic subfield.
Hence the eigenvector is asserted only after an allowed switch of the
quadratic character, and the consumer re-runs the quadratic-field
classification on `θ'`.

The proven reduction: if all `u h`, `h ∈ ker θ`, pairwise commute,
`θ' = θ` works — `ρ g = 1 → θ g = 1` follows from `htr` since
`tr 1 = 2 ≠ 0` in characteristic `3`, and a commuting family over the
algebraically closed `Dickson.K 3` shares an eigenline (all-scalar
case: any vector; otherwise the eigenline of a nonscalar member,
one-dimensional by `exists_smul_eq_of_mulVec_eq_zero`). Otherwise the
pivot leaf yields a trace-zero invertible `f` anticommuting with some
`u p` and commuting-or-anticommuting with every `u g`; the `±1`-sign
of conjugation on `f` is a `MonoidHom` `θ' : Γ ℚ →* ℤ/2` (the four
sign-composition cases are proven by explicit rewriting), surjective
via `p`, trivial on `ker ρ` (`u g = 1` there), and elements of
`ker θ'` commute with `f` honestly, hence preserve the eigenline of
`f` cut out by a root of `det (f - t • 1)` (Cayley–Hamilton
`f² = (-det f) • 1` and a square root of `-det f`): a common
eigenvector for the SWITCHED quadratic field. -/
theorem exists_index_two_common_eigenvector {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (θ : Γ ℚ →* Multiplicative (ZMod 2))
    (hθsurj : Function.Surjective θ)
    (hcomm : ∀ g h : Γ ℚ, θ g = 1 → θ h = 1 → π g * π h = π h * π g)
    (htr : ∀ g : Γ ℚ, θ g ≠ 1 →
      LinearMap.trace k V
        ((MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g) = 0) :
    ∃ θ' : Γ ℚ →* Multiplicative (ZMod 2),
      Function.Surjective θ' ∧ (∀ g : Γ ℚ, ρ g = 1 → θ' g = 1) ∧
      ∃ v : Fin 2 → Dickson.K 3, v ≠ 0 ∧
        ∀ g : Γ ℚ, θ' g = 1 → ∃ c : Dickson.K 3,
          Matrix.mulVec ((u g : GL (Fin 2) (Dickson.K 3)) :
            Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v = c • v := by
  classical
  by_cases hA : ∀ g h' : Γ ℚ, θ g = 1 → θ h' = 1 →
      (u g).val * (u h').val = (u h').val * (u g).val
  · -- the honestly commuting case: `θ' = θ` works
    have h3k : (3 : k) = 0 := three_eq_zero_of_finite_padicIntThree_algebra
    have h2k : (2 : k) ≠ 0 := fun h =>
      one_ne_zero (α := k) (by linear_combination h3k - h)
    have hfr : Module.finrank k V = 2 :=
      Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
    have htriv : ∀ g : Γ ℚ, ρ g = 1 → θ g = 1 := by
      intro g hg
      by_contra hne
      have h0 := htr g hne
      have h1 : (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g = 1 := hg
      rw [h1, LinearMap.trace_one, hfr] at h0
      exact h2k (by exact_mod_cast h0)
    refine ⟨θ, hθsurj, htriv, ?_⟩
    by_cases hsc : ∀ h' : Γ ℚ, θ h' = 1 → ∃ c : Dickson.K 3,
        (u h').val = c • (1 : Matrix (Fin 2) (Fin 2) (Dickson.K 3))
    · -- every kernel matrix is scalar: any nonzero vector is common
      refine ⟨![1, 0], fun h => one_ne_zero (α := Dickson.K 3)
        (by simpa using congrFun h 0), ?_⟩
      intro g hg
      obtain ⟨c, hc⟩ := hsc g hg
      refine ⟨c, ?_⟩
      rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    · -- some kernel matrix is nonscalar: its eigenline is common
      push Not at hsc
      obtain ⟨h₀, hh₀, hns⟩ := hsc
      obtain ⟨s, hsev⟩ :=
        Module.End.exists_eigenvalue (Matrix.mulVecLin (u h₀).val)
      obtain ⟨v, hv⟩ := hsev.exists_hasEigenvector
      have hfv : Matrix.mulVec (u h₀).val v = s • v := by
        have h1 := Module.End.mem_eigenspace_iff.mp hv.1
        rwa [Matrix.mulVecLin_apply] at h1
      have hM0 : (u h₀).val - s • 1 ≠ 0 := by
        intro h0
        exact hns s (by rwa [sub_eq_zero] at h0)
      have hvker : Matrix.mulVec ((u h₀).val - s • 1) v = 0 := by
        rw [Matrix.sub_mulVec, hfv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
      refine ⟨v, hv.2, ?_⟩
      intro g hg
      have hcg := hA g h₀ hg hh₀
      have hswap : ((u h₀).val - s • 1) * (u g).val =
          (u g).val * ((u h₀).val - s • 1) := by
        rw [sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, hcg]
      have hwker : Matrix.mulVec ((u h₀).val - s • 1)
          (Matrix.mulVec (u g).val v) = 0 := by
        rw [Matrix.mulVec_mulVec, hswap, ← Matrix.mulVec_mulVec, hvker,
          Matrix.mulVec_zero]
      exact exists_smul_eq_of_mulVec_eq_zero hM0 hvker hwker hv.2
  · -- the Klein-four case: switch to the sign character of a fixed
    -- trace-zero involution-mod-scalars
    haveI : CharP (Dickson.K 3) 3 :=
      charP_of_injective_algebraMap
        (algebraMap (ZMod 3) (Dickson.K 3)).injective 3
    have h2F : (2 : Dickson.K 3) ≠ 0 := by
      intro h
      have h3 := (CharP.cast_eq_zero_iff (Dickson.K 3) 3 2).mp h
      norm_num at h3
    -- `u` of a `ρ`-kernel element is the identity matrix
    have huone : ∀ g : Γ ℚ, ρ g = 1 → (u g).val = 1 := by
      intro g hg
      have h2 : (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g = 1 := hg
      have h1 : (Slop.OddRep.baseChange (AlgebraicClosure k)
          (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V)) g = 1 := by
        have h3 : (Slop.OddRep.baseChange (AlgebraicClosure k)
            (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V)) g =
            ((MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g).baseChange
              (AlgebraicClosure k) := rfl
        rw [h3, h2, Module.End.one_eq_id, LinearMap.baseChange_id]
        rfl
      rw [hu g, h1, LinearMap.toMatrix_one]
      exact Matrix.map_one e (map_zero e) (map_one e)
    -- the Klein-four analysis: a trace-zero anticommuting-pair member,
    -- conjugation-fixed up to sign by the whole image
    have hklein :=
      exists_klein_pivot_of_noncommuting_kernel h2F u π hπ θ hθsurj hcomm hA
    obtain ⟨f, htr0, hdetf, ⟨p, hp⟩, hdich⟩ := hklein
    -- commuting and anticommuting with `f` are mutually exclusive
    have hexcl : ∀ g : Γ ℚ, (u g).val * f = f * (u g).val →
        (u g).val * f = -(f * (u g).val) → False := by
      intro g h1 h2
      have h3 : f * (u g).val = -(f * (u g).val) := h1.symm.trans h2
      have h5 : f * (u g).val = 0 := by
        have h6 : (2 : Dickson.K 3) • (f * (u g).val) = 0 := by
          rw [two_smul]
          exact add_eq_zero_iff_eq_neg.mpr h3
        rcases smul_eq_zero.mp h6 with h7 | h7
        · exact absurd h7 h2F
        · exact h7
      have h7 : Matrix.det (f * (u g).val) = 0 := by
        rw [h5]
        exact Matrix.det_zero
      rw [Matrix.det_mul] at h7
      rcases mul_eq_zero.mp h7 with h8 | h8
      · exact hdetf h8
      · exact ((Matrix.isUnit_iff_isUnit_det (u g).val).mp (u g).isUnit).ne_zero h8
    -- Cayley–Hamilton for the trace-zero `f`: `f² = (-det f) • 1`
    have hCH : f * f = (-Matrix.det f) • (1 : Matrix (Fin 2) (Fin 2) (Dickson.K 3)) := by
      have hCH0 := Matrix.aeval_self_charpoly f
      rw [Matrix.charpoly_fin_two, map_add, map_sub, map_pow, Polynomial.aeval_X,
        map_mul, Polynomial.aeval_C, htr0, map_zero, zero_mul, sub_zero,
        Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] at hCH0
      rw [← sq, neg_smul]
      exact eq_neg_of_add_eq_zero_left hCH0
    -- a square root of `-det f` and a singular translate of `f`
    obtain ⟨s, hs2⟩ :=
      IsAlgClosed.exists_pow_nat_eq (-Matrix.det f) (n := 2) (by norm_num)
    have hfact : (f - s • 1) * (f + s • 1) = 0 := by
      have h1 : (f - s • 1) * (f + s • 1) =
          f * f - (s * s) • (1 : Matrix (Fin 2) (Fin 2) (Dickson.K 3)) := by
        simp only [mul_add, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul,
          mul_one, smul_sub, smul_smul]
        abel
      rw [h1, hCH, ← hs2, sq, sub_self]
    have hdet0 : Matrix.det (f - s • 1) = 0 ∨ Matrix.det (f + s • 1) = 0 := by
      have h1 : Matrix.det (f - s • 1) * Matrix.det (f + s • 1) = 0 := by
        rw [← Matrix.det_mul, hfact]
        exact Matrix.det_zero
      exact mul_eq_zero.mp h1
    obtain ⟨t, htdet⟩ : ∃ t : Dickson.K 3, Matrix.det (f - t • 1) = 0 := by
      rcases hdet0 with h1 | h1
      · exact ⟨s, h1⟩
      · refine ⟨-s, ?_⟩
        rw [neg_smul, sub_neg_eq_add]
        exact h1
    obtain ⟨v, hv0, hvker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr htdet
    -- `f` is nonscalar (it has an anticommuting partner)
    have hfns : f - t • 1 ≠ 0 := by
      intro h0
      have hf : f = t • 1 := by rwa [sub_eq_zero] at h0
      apply hexcl p ?_ hp
      rw [hf, mul_smul_comm, mul_one, smul_mul_assoc, one_mul]
    -- multiplicativity data for the sign of conjugation on `f`
    have hmulval : ∀ g h' : Γ ℚ, (u (g * h')).val = (u g).val * (u h').val := by
      intro g h'
      rw [map_mul]
      rfl
    have hcc : ∀ g h' : Γ ℚ, (u g).val * f = f * (u g).val →
        (u h').val * f = f * (u h').val →
        (u (g * h')).val * f = f * (u (g * h')).val := by
      intro g h' hg hh'
      rw [hmulval, mul_assoc, hh', ← mul_assoc, hg, mul_assoc]
    have hca : ∀ g h' : Γ ℚ, (u g).val * f = f * (u g).val →
        (u h').val * f = -(f * (u h').val) →
        (u (g * h')).val * f = -(f * (u (g * h')).val) := by
      intro g h' hg hh'
      rw [hmulval, mul_assoc, hh', mul_neg, neg_inj, ← mul_assoc, hg, mul_assoc]
    have hac : ∀ g h' : Γ ℚ, (u g).val * f = -(f * (u g).val) →
        (u h').val * f = f * (u h').val →
        (u (g * h')).val * f = -(f * (u (g * h')).val) := by
      intro g h' hg hh'
      rw [hmulval, mul_assoc, hh', ← mul_assoc, hg, neg_mul, mul_assoc]
    have haa : ∀ g h' : Γ ℚ, (u g).val * f = -(f * (u g).val) →
        (u h').val * f = -(f * (u h').val) →
        (u (g * h')).val * f = f * (u (g * h')).val := by
      intro g h' hg hh'
      rw [hmulval, mul_assoc, hh', mul_neg, ← mul_assoc, hg, neg_mul, neg_neg,
        mul_assoc]
    -- the switched character: the sign of conjugation on `f`
    let θ' : Γ ℚ →* Multiplicative (ZMod 2) :=
      { toFun := fun g => if (u g).val * f = f * (u g).val then 1
          else Multiplicative.ofAdd (1 : ZMod 2)
        map_one' := by
          have h1 : (u 1).val = 1 := by rw [map_one]; rfl
          rw [h1, one_mul, mul_one]
          exact if_pos rfl
        map_mul' := by
          intro g h'
          rcases hdich g with hg | hg <;> rcases hdich h' with hh' | hh'
          · rw [if_pos hg, if_pos hh', if_pos (hcc g h' hg hh'), one_mul]
          · rw [if_pos hg, if_neg fun hc => hexcl h' hc hh',
              if_neg fun hc => hexcl (g * h') hc (hca g h' hg hh'), one_mul]
          · rw [if_neg fun hc => hexcl g hc hg, if_pos hh',
              if_neg fun hc => hexcl (g * h') hc (hac g h' hg hh'), mul_one]
          · rw [if_neg fun hc => hexcl g hc hg,
              if_neg fun hc => hexcl h' hc hh',
              if_pos (haa g h' hg hh')]
            decide }
    have hθ'apply : ∀ g : Γ ℚ, θ' g =
        if (u g).val * f = f * (u g).val then 1
        else Multiplicative.ofAdd (1 : ZMod 2) := fun g => rfl
    have hω : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
    have hy2 : ∀ y : Multiplicative (ZMod 2),
        y = 1 ∨ y = Multiplicative.ofAdd (1 : ZMod 2) := by decide
    have hsurj' : Function.Surjective θ' := by
      intro y
      rcases hy2 y with rfl | rfl
      · exact ⟨1, map_one θ'⟩
      · refine ⟨p, ?_⟩
        rw [hθ'apply p, if_neg fun hc => hexcl p hc hp]
    have htriv'' : ∀ g : Γ ℚ, ρ g = 1 → θ' g = 1 := by
      intro g hg
      rw [hθ'apply g, if_pos (by rw [huone g hg, one_mul, mul_one])]
    refine ⟨θ', hsurj', htriv'', v, hv0, ?_⟩
    intro g hg
    have hcg : (u g).val * f = f * (u g).val := by
      by_contra hc
      rw [hθ'apply g, if_neg hc] at hg
      exact hω hg
    have hswap : (f - t • 1) * (u g).val = (u g).val * (f - t • 1) := by
      rw [sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, hcg]
    have hwker : Matrix.mulVec (f - t • 1) (Matrix.mulVec (u g).val v) = 0 := by
      rw [Matrix.mulVec_mulVec, hswap, ← Matrix.mulVec_mulVec, hvker,
        Matrix.mulVec_zero]
    exact exists_smul_eq_of_mulVec_eq_zero hfns hvker hwker hv0

/-- **Coordinates from a non-proportional pair** (PROVEN 2026-07-23 —
elementary 2×2 linear algebra for the induced-structure glue of the
dihedral ray-class decomposition): if `v ≠ 0` and `w` is not a scalar
multiple of `v`, then every vector of `Fin 2 → F` is a linear
combination of `v` and `w`. Cramer-style explicit coefficients over
the nonzero cross-determinant `v 0 * w 1 - v 1 * w 0`. -/
theorem exists_smul_add_smul_of_not_proportional {F : Type*} [Field F]
    {v w : Fin 2 → F} (hv : v ≠ 0)
    (hnp : ¬ ∃ c : F, w = c • v) (x : Fin 2 → F) :
    ∃ α β : F, x = α • v + β • w := by
  classical
  have hcross : v 0 * w 1 - v 1 * w 0 ≠ 0 := by
    intro h
    apply hnp
    have hvi : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hv (funext fun i => ?_)
      fin_cases i
      · exact hcon.1
      · exact hcon.2
    rcases hvi with h0 | h1
    · refine ⟨w 0 / v 0, funext fun i => ?_⟩
      fin_cases i
      · exact (div_mul_cancel₀ (w 0) h0).symm
      · show w 1 = w 0 / v 0 * v 1
        field_simp
        linear_combination h
    · refine ⟨w 1 / v 1, funext fun i => ?_⟩
      fin_cases i
      · show w 0 = w 1 / v 1 * v 0
        field_simp
        linear_combination -h
      · exact (div_mul_cancel₀ (w 1) h1).symm
  refine ⟨(x 0 * w 1 - x 1 * w 0) / (v 0 * w 1 - v 1 * w 0),
    (v 0 * x 1 - v 1 * x 0) / (v 0 * w 1 - v 1 * w 0),
    funext fun i => ?_⟩
  fin_cases i
  · show x 0 = (x 0 * w 1 - x 1 * w 0) / (v 0 * w 1 - v 1 * w 0) * v 0 +
      (v 0 * x 1 - v 1 * x 0) / (v 0 * w 1 - v 1 * w 0) * w 0
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      eq_div_iff hcross]
    ring
  · show x 1 = (x 0 * w 1 - x 1 * w 0) / (v 0 * w 1 - v 1 * w 0) * v 1 +
      (v 0 * x 1 - v 1 * x 0) / (v 0 * w 1 - v 1 * w 0) * w 1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      eq_div_iff hcross]
    ring

set_option maxHeartbeats 1000000 in
/-- **No common eigenvector under absolute irreducibility** (PROVEN
2026-07-23 — the transport bridge for the induced-structure glue of
the dihedral ray-class decomposition): if every matrix `u g` of the
transported representation has the SAME eigenvector `v ≠ 0` over
`Dickson.K 3`, then the vector of `(AlgebraicClosure k) ⊗ V` with
`e`-preimage coordinates `v` in the basis `b` spans a stable line,
contradicting absolute irreducibility (`isIrreducible_iff_forall`
plus `finrank_span_singleton = 1 ≠ 2`). -/
theorem no_common_eigenvector_of_absolutelyIrreducible {k : Type u}
    [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (v : Fin 2 → Dickson.K 3) (hv : v ≠ 0)
    (hall : ∀ g : Γ ℚ, ∃ c : Dickson.K 3,
      Matrix.mulVec ((u g : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v = c • v) :
    False := by
  classical
  set L := AlgebraicClosure k with hLdef
  set σρ : Representation L (Γ ℚ) (L ⊗[k] V) :=
    Slop.OddRep.baseChange L (MonoidHomClass.toMonoidHom ρ) with hσρdef
  have hirr : σρ.IsIrreducible := habs
  haveI : Module.Finite L (L ⊗[k] V) := Module.Finite.base_change k L V
  have hfr2 : Module.finrank L (L ⊗[k] V) = 2 := by
    rw [Module.finrank_baseChange]
    exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  obtain ⟨-, hsub⟩ := (Slop.OddRep.isIrreducible_iff_forall σρ).mp hirr
  -- the vector of `L ⊗ V` with `e`-preimage coordinates `v`
  set v'' : Fin 2 → L := fun i => e.symm (v i) with hv''def
  set v' : L ⊗[k] V := b.equivFun.symm v'' with hv'def
  have hreprv' : ⇑(b.repr v') = v'' := by
    have h1 : b.equivFun v' = v'' := by
      rw [hv'def, LinearEquiv.apply_symm_apply]
    exact h1
  have hv'0 : v' ≠ 0 := by
    intro h0
    apply hv
    have h1 : v'' = 0 := by
      rw [← hreprv', h0, map_zero]
      rfl
    funext i
    have h2 : e.symm (v i) = 0 := congrFun h1 i
    have h3 := congrArg e h2
    rwa [RingEquiv.apply_symm_apply, map_zero] at h3
  -- every `σρ g` scales `v'`
  have hstab : ∀ g : Γ ℚ, ∃ c' : L, σρ g v' = c' • v' := by
    intro g
    obtain ⟨c, hc⟩ := hall g
    refine ⟨e.symm c, ?_⟩
    have hcoord : ∀ i,
        Matrix.mulVec (LinearMap.toMatrix b b (σρ g)) (⇑(b.repr v')) i =
        e.symm c * v'' i := by
      intro i
      have hterm : ∀ j, LinearMap.toMatrix b b (σρ g) i j * (b.repr v') j =
          e.symm (((u g : GL (Fin 2) (Dickson.K 3)) :
            Matrix (Fin 2) (Fin 2) (Dickson.K 3)) i j * v j) := by
        intro j
        rw [map_mul]
        congr 1
        · rw [hu g, Matrix.map_apply]
          exact (RingEquiv.symm_apply_apply e _).symm
        · exact congrFun hreprv' j
      calc Matrix.mulVec (LinearMap.toMatrix b b (σρ g)) (⇑(b.repr v')) i
          = ∑ j, LinearMap.toMatrix b b (σρ g) i j * (b.repr v') j :=
            Matrix.mulVec_apply_eq_sum _ _ _
        _ = ∑ j, e.symm (((u g : GL (Fin 2) (Dickson.K 3)) :
              Matrix (Fin 2) (Fin 2) (Dickson.K 3)) i j * v j) :=
            Finset.sum_congr rfl fun j _ => hterm j
        _ = e.symm (∑ j, ((u g : GL (Fin 2) (Dickson.K 3)) :
              Matrix (Fin 2) (Fin 2) (Dickson.K 3)) i j * v j) :=
            (map_sum e.symm _ _).symm
        _ = e.symm ((Matrix.mulVec ((u g : GL (Fin 2) (Dickson.K 3)) :
              Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v) i) := by
            rw [Matrix.mulVec_apply_eq_sum]
        _ = e.symm ((c • v) i) := by rw [hc]
        _ = e.symm (c * v i) := rfl
        _ = e.symm c * e.symm (v i) := map_mul e.symm _ _
        _ = e.symm c * v'' i := rfl
    apply b.repr.injective
    apply DFunLike.coe_injective
    rw [← LinearMap.toMatrix_mulVec_repr b b (σρ g) v', map_smul]
    funext i
    rw [hcoord i, Finsupp.smul_apply,
      show (b.repr v') i = v'' i from congrFun hreprv' i, smul_eq_mul]
  -- the stable line contradicts irreducibility
  have hWinv : ∀ g : Γ ℚ, ∀ x ∈ Submodule.span L {v'},
      σρ g x ∈ Submodule.span L {v'} := by
    intro g x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨c', hc'⟩ := hstab g
    rw [map_smul, hc', Submodule.mem_span_singleton]
    exact ⟨a * c', by rw [smul_smul]⟩
  rcases hsub (Submodule.span L {v'}) hWinv with hW | hW
  · apply hv'0
    have h1 : v' ∈ Submodule.span L {v'} :=
      Submodule.mem_span_singleton_self v'
    rw [hW] at h1
    exact (Submodule.mem_bot L).mp h1
  · have h1 : Module.finrank L (Submodule.span L {v'}) = 1 :=
      finrank_span_singleton hv'0
    rw [hW, finrank_top, hfr2] at h1
    omega

set_option maxHeartbeats 1000000 in
/-- **The induced eigenvalue character is unramified at `2`** (sorry
node, isolated 2026-07-23 — the local-at-`2` half of the dihedral
ray-class core, independent of the at-`3`/ray-class arithmetic): the
inertia at `2` lands in `H := ker θ'` and in the kernel of the
eigenvalue character `χ₀`.

Intended content: by `hρ.det` the determinant of `ρ` is the mod-3
cyclotomic character, trivial on the inertia at `2`
(`cyclotomicCharacter_algebraMap_eq_one_of_inertia_two` after the
bridge `localInertia_two_eq_map_padic` — both PROVEN but stated
LATER in this file, so move or re-derive them when resolving this
node), and by `hρ.isTameAtTwo` the local representation at `2` is an
extension of an unramified quadratic character `δ` by `det/δ`, so
the inertia at `2` acts through `u` by matrices with both
eigenvalues `1` (unipotent up to conjugation). A nontrivial
unipotent has trace `2 = -1 ≠ 0` in characteristic `3`; but a matrix
of an element OUTSIDE `H` maps the line `K·v` to the independent
line `K·(u σ₀ ·ᵥ v)` (`hindep`) and back — antidiagonally in the
basis `(v, u σ₀ ·ᵥ v)` — so it has trace `0`; and `u ι = 1` forces
`ρ ι = 1` through the faithful base change (`hu`), hence `θ' ι = 1`
(`htriv'`). So the inertia at `2` lies in `H`; there its matrices
have `v` as an eigenvector (`hχ₀`) with eigenvalue `χ₀`, and the
only eigenvalue of a unipotent is `1`. -/
theorem induced_character_unramified_at_two {k : Type u}
    [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (θ' : Γ ℚ →* Multiplicative (ZMod 2))
    (htriv' : ∀ g : Γ ℚ, ρ g = 1 → θ' g = 1)
    (v : Fin 2 → Dickson.K 3) (hv : v ≠ 0)
    (σ₀ : Γ ℚ) (hσ₀ : θ' σ₀ ≠ 1)
    (χ₀ : Γ ℚ → Dickson.K 3)
    (hχ₀ : ∀ g : Γ ℚ, θ' g = 1 →
      Matrix.mulVec ((u g : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v = χ₀ g • v)
    (hindep : ¬ ∃ c : Dickson.K 3,
      Matrix.mulVec ((u σ₀ : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v = c • v) :
    ∀ σ ∈ localInertiaGroup
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
      θ' (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 ∧
      χ₀ (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
  sorry

set_option maxHeartbeats 1000000 in
/-- **The induced eigenvalue character is conjugation-symmetric — the
per-quadratic-field ray-class computation** (sorry node, isolated
2026-07-23 from `dihedral_induced_ray_class_of_two_unramified` below,
whose linear-algebra layer — the second eigenline and the determinant
identity — is PROVEN glue there): the eigenvalue character `χ₀` of
`H = ker θ' = Γ_{ℚ(√d)}` agrees with its `σ₀`-conjugate, i.e. the
would-be induced representation is NOT genuinely dihedral. The whole
matrix layer is condensed into the single arithmetic hypothesis
`hχprod`: on `H` the product `χ₀ · χ₀^{σ₀}` is the mod-3 cyclotomic
character (the determinant of the induced representation on the
eigenbasis).

Intended content (Serre's mod-3 analogue, Duke 1987 §5, of Tate's
2-adic letter argument, per fixed `d`). The ratio `ν := χ₀/χ₀^{σ₀}`
is multiplicative on `H` (`hχmul`), trivial on the open normal
subgroup `ker ρ` (`hχker` + normality + `htriv'`), of finite order
prime to `3` (its values are units of `𝔽̄₃ = ⋃ₙ 𝔽_{3ⁿ}`, so of finite
multiplicative order with no `3`-part), and ANTI-equivariant:
`ν(σ₀⁻¹gσ₀) = ν(g)⁻¹`, from `hχmul` alone via `σ₀² ∈ H` and
`H`-conjugation-invariance of the abelian-valued `χ₀`. It is
unramified at `2` (`h2unr` for the `χ₀` factor; `hχprod` plus
triviality of the cyclotomic character on the inertia at `2` — the
PROVEN `cyclotomicCharacter_algebraMap_eq_one_of_inertia_two`, stated
LATER in this file, so move or re-derive it when resolving this
node — for the conjugate factor) and at every prime `q ∉ {2, 3}`
(`hχunr`, same transport), and at the conjugate copies of those
inertia subgroups (conjugation by `h ∈ H` fixes `ν`; conjugation by
`σ₀` inverts it). At `3`: `ρ` is flat (`hρ.isFlat`); Raynaud's
classification over the at-worst-quadratically-ramified completions
of `ℚ(√d)` above `3` (`e ≤ 2 = 3 - 1`) bounds the ramification at `3`
of the splitting field of `ρ` — through which `ν` factors, by
`hχker` — so `ν` has bounded conductor above `3` (tameness is
automatic: `ν` has order prime to `3`, killing the pro-`3` wild
inertia). Ray class, per field: `ν` is then a character of the ray
class group of `ℚ(√d)` with conductor supported in the tame primes
above `3`; the class numbers of the seven fields
`ℚ(√-1), ℚ(√±2), ℚ(√±3), ℚ(√±6)` are `1, 1, 1, 1, 1, 1, 2`, and the
ray class groups modulo the allowed conductor above `3` are generated
by ramified classes on which the anti-equivariant `ν` is forced to
vanish; so `ν = 1`, i.e. `χ₀ = χ₀^{σ₀}` on `H`. References: Serre,
Duke Math. J. 54 (1987) §5; Tate's 1974 letter to Serre (Œuvres III);
Neukirch, ANT VI §6 (ray class groups). -/
theorem dihedral_eigenvalue_character_symmetric_ray_class {k : Type u}
    [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (θ' : Γ ℚ →* Multiplicative (ZMod 2))
    (htriv' : ∀ g : Γ ℚ, ρ g = 1 → θ' g = 1)
    (d : ℤ)
    (hd : d = -1 ∨ d = 2 ∨ d = -2 ∨ d = 3 ∨ d = -3 ∨ d = 6 ∨ d = -6)
    (x : AlgebraicClosure ℚ) (hx : x ^ 2 = (d : AlgebraicClosure ℚ))
    (hθ'x : ∀ g : Γ ℚ, θ' g = 1 ↔ g x = x)
    (σ₀ : Γ ℚ) (hσ₀ : θ' σ₀ ≠ 1)
    (χ₀ : Γ ℚ → Dickson.K 3)
    (hχne0 : ∀ g : Γ ℚ, θ' g = 1 → χ₀ g ≠ 0)
    (hχmul : ∀ g h : Γ ℚ, θ' g = 1 → θ' h = 1 →
      χ₀ (g * h) = χ₀ g * χ₀ h)
    (hχker : ∀ g : Γ ℚ, ρ g = 1 → χ₀ g = 1)
    (hχprod : ∀ g : Γ ℚ, θ' g = 1 →
      χ₀ g * χ₀ (σ₀⁻¹ * g * σ₀) =
        ((e : AlgebraicClosure k →+* Dickson.K 3).comp
          ((algebraMap k (AlgebraicClosure k)).comp (algebraMap ℤ_[3] k)))
          ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) : ℤ_[3]))
    (hχunr : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        χ₀ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1)
    (h2unr : ∀ σ ∈ localInertiaGroup
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
      θ' (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 ∧
      χ₀ (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1) :
    ∀ g : Γ ℚ, θ' g = 1 → χ₀ g = χ₀ (σ₀⁻¹ * g * σ₀) := by
  sorry

set_option maxHeartbeats 1000000 in
/-- **The dihedral ray-class computation given unramifiedness at `2`**
(DECOMPOSED 2026-07-23 into the ray-class sorry node
`dihedral_eigenvalue_character_symmetric_ray_class` above — the
assembly is proven): the linear-algebra layer of the dihedral
contradiction. The second eigenvector `w := u σ₀ ·ᵥ v` carries the
`σ₀`-conjugate eigenvalue on `H` (push `u g` across
`g·σ₀ = σ₀·(σ₀⁻¹gσ₀)`); the pair `(v, w)` has nonvanishing `2 × 2`
determinant `v₀w₁ - w₀v₁` (`hindep` + `hv`), so expanding
`det(u g · (v|w)) = det(u g)·det(v|w)` on the eigen-equations gives
the product formula `χ₀ g · χ₀(σ₀⁻¹gσ₀) = det (u g) = χ₃ g`
(`hρ.det` transported along `hu`, exactly as in
`not_isAbsolutelyIrreducible`). The ray-class leaf then returns
`χ₀ = χ₀^{σ₀}` on `ker θ'`, contradicting `hne`. -/
theorem dihedral_induced_ray_class_of_two_unramified {k : Type u}
    [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (_habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (θ' : Γ ℚ →* Multiplicative (ZMod 2))
    (_hθ'surj : Function.Surjective θ')
    (htriv' : ∀ g : Γ ℚ, ρ g = 1 → θ' g = 1)
    (v : Fin 2 → Dickson.K 3) (hv : v ≠ 0)
    (d : ℤ)
    (hd : d = -1 ∨ d = 2 ∨ d = -2 ∨ d = 3 ∨ d = -3 ∨ d = 6 ∨ d = -6)
    (x : AlgebraicClosure ℚ) (hx : x ^ 2 = (d : AlgebraicClosure ℚ))
    (hθ'x : ∀ g : Γ ℚ, θ' g = 1 ↔ g x = x)
    (σ₀ : Γ ℚ) (hσ₀ : θ' σ₀ ≠ 1)
    (χ₀ : Γ ℚ → Dickson.K 3)
    (hχ₀ : ∀ g : Γ ℚ, θ' g = 1 →
      Matrix.mulVec ((u g : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v = χ₀ g • v)
    (hχne0 : ∀ g : Γ ℚ, θ' g = 1 → χ₀ g ≠ 0)
    (hχmul : ∀ g h : Γ ℚ, θ' g = 1 → θ' h = 1 →
      χ₀ (g * h) = χ₀ g * χ₀ h)
    (hχker : ∀ g : Γ ℚ, ρ g = 1 → χ₀ g = 1)
    (hχunr : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        χ₀ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1)
    (hindep : ¬ ∃ c : Dickson.K 3,
      Matrix.mulVec ((u σ₀ : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v = c • v)
    (h2unr : ∀ σ ∈ localInertiaGroup
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat,
      θ' (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 ∧
      χ₀ (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1)
    (hne : ¬ ∀ g : Γ ℚ, θ' g = 1 → χ₀ g = χ₀ (σ₀⁻¹ * g * σ₀)) :
    False := by
  classical
  -- conjugation by `σ₀` preserves `H = ker θ'`
  have hHconj : ∀ g : Γ ℚ, θ' g = 1 → θ' (σ₀⁻¹ * g * σ₀) = 1 := by
    intro g hg
    rw [map_mul, map_mul, hg, mul_one, map_inv, inv_mul_cancel]
  -- the second eigenvector `w = u σ₀ ·ᵥ v` and its eigen-equation on `H`
  set w : Fin 2 → Dickson.K 3 :=
    Matrix.mulVec ((u σ₀ : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v with hwdef
  have hgw : ∀ g : Γ ℚ, θ' g = 1 →
      Matrix.mulVec ((u g : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) w =
        χ₀ (σ₀⁻¹ * g * σ₀) • w := by
    intro g hg
    have hcomm : u g * u σ₀ = u σ₀ * u (σ₀⁻¹ * g * σ₀) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have hmat : ((u g : GL (Fin 2) (Dickson.K 3)) :
          Matrix (Fin 2) (Fin 2) (Dickson.K 3)) *
        ((u σ₀ : GL (Fin 2) (Dickson.K 3)) :
          Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
        ((u σ₀ : GL (Fin 2) (Dickson.K 3)) :
          Matrix (Fin 2) (Fin 2) (Dickson.K 3)) *
        ((u (σ₀⁻¹ * g * σ₀) : GL (Fin 2) (Dickson.K 3)) :
          Matrix (Fin 2) (Fin 2) (Dickson.K 3)) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm]
    rw [hwdef, Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec,
      hχ₀ _ (hHconj g hg), Matrix.mulVec_smul]
  -- entrywise eigen-equations
  have hAv : ∀ g : Γ ℚ, θ' g = 1 → ∀ i : Fin 2,
      ((u g : GL (Fin 2) (Dickson.K 3)) :
          Matrix (Fin 2) (Fin 2) (Dickson.K 3)) i 0 * v 0 +
        ((u g : GL (Fin 2) (Dickson.K 3)) :
          Matrix (Fin 2) (Fin 2) (Dickson.K 3)) i 1 * v 1 = χ₀ g * v i := by
    intro g hg i
    have hvi := congrFun (hχ₀ g hg) i
    rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] at hvi
    simpa using hvi
  have hAw : ∀ g : Γ ℚ, θ' g = 1 → ∀ i : Fin 2,
      ((u g : GL (Fin 2) (Dickson.K 3)) :
          Matrix (Fin 2) (Fin 2) (Dickson.K 3)) i 0 * w 0 +
        ((u g : GL (Fin 2) (Dickson.K 3)) :
          Matrix (Fin 2) (Fin 2) (Dickson.K 3)) i 1 * w 1 =
        χ₀ (σ₀⁻¹ * g * σ₀) * w i := by
    intro g hg i
    have hwi := congrFun (hgw g hg) i
    rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] at hwi
    simpa using hwi
  -- the eigenpair is honestly independent: nonzero `2 × 2` determinant
  have hdetP : v 0 * w 1 - w 0 * v 1 ≠ 0 := by
    intro h0
    apply hindep
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro hv1
        apply hv
        funext i
        fin_cases i
        · exact hv0
        · exact hv1
      have hw0 : w 0 = 0 := by
        rcases mul_eq_zero.mp (show w 0 * v 1 = 0 by
          linear_combination -h0 + w 1 * hv0) with h | h
        · exact h
        · exact absurd h hv1
      refine ⟨w 1 / v 1, funext fun i => ?_⟩
      fin_cases i
      · show w 0 = w 1 / v 1 * v 0
        rw [hw0, hv0, mul_zero]
      · show w 1 = w 1 / v 1 * v 1
        rw [div_mul_cancel₀ _ hv1]
    · refine ⟨w 0 / v 0, funext fun i => ?_⟩
      fin_cases i
      · show w 0 = w 0 / v 0 * v 0
        rw [div_mul_cancel₀ _ hv0]
      · show w 1 = w 0 / v 0 * v 1
        field_simp
        linear_combination h0
  -- the determinant of the matrix action is the mod-3 cyclotomic
  -- character pushed to `𝔽̄₃` (as in `not_isAbsolutelyIrreducible`)
  have hdet_val : ∀ g : Γ ℚ,
      ((Matrix.GeneralLinearGroup.det (u g) : (Dickson.K 3)ˣ) : Dickson.K 3) =
        ((e : AlgebraicClosure k →+* Dickson.K 3).comp
          ((algebraMap k (AlgebraicClosure k)).comp (algebraMap ℤ_[3] k)))
          ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) : ℤ_[3]) := by
    intro g
    calc ((Matrix.GeneralLinearGroup.det (u g) : (Dickson.K 3)ˣ) : Dickson.K 3)
        = ((u g : GL (Fin 2) (Dickson.K 3)) :
            Matrix (Fin 2) (Fin 2) (Dickson.K 3)).det := rfl
      _ = ((LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
            (MonoidHomClass.toMonoidHom ρ)) g)).map e).det := by rw [hu g]
      _ = e ((LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
            (MonoidHomClass.toMonoidHom ρ)) g)).det) :=
          (RingEquiv.map_det e _).symm
      _ = e (LinearMap.det ((Slop.OddRep.baseChange (AlgebraicClosure k)
            (MonoidHomClass.toMonoidHom ρ)) g)) := by rw [LinearMap.det_toMatrix]
      _ = e (algebraMap k (AlgebraicClosure k)
            (LinearMap.det ((MonoidHomClass.toMonoidHom ρ :
              Representation k (Γ ℚ) V) g))) := by
          rw [show (Slop.OddRep.baseChange (AlgebraicClosure k)
              (MonoidHomClass.toMonoidHom ρ)) g =
            ((MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g).baseChange
              (AlgebraicClosure k) from rfl, LinearMap.det_baseChange]
      _ = _ := by
          have hdg := hρ.det g
          rw [GaloisRep.det_apply] at hdg
          rw [show LinearMap.det ((MonoidHomClass.toMonoidHom ρ :
              Representation k (Γ ℚ) V) g) = LinearMap.det (ρ g) from rfl, hdg]
          rfl
  -- the product formula: `χ₀ · χ₀^{σ₀} = det ∘ u = χ₃` on `H`
  have hχprod : ∀ g : Γ ℚ, θ' g = 1 →
      χ₀ g * χ₀ (σ₀⁻¹ * g * σ₀) =
        ((e : AlgebraicClosure k →+* Dickson.K 3).comp
          ((algebraMap k (AlgebraicClosure k)).comp (algebraMap ℤ_[3] k)))
          ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) : ℤ_[3]) := by
    intro g hg
    have e1 := hAv g hg 0
    have e2 := hAv g hg 1
    have e3 := hAw g hg 0
    have e4 := hAw g hg 1
    have hkey : (((u g : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)).det -
          χ₀ g * χ₀ (σ₀⁻¹ * g * σ₀)) * (v 0 * w 1 - w 0 * v 1) = 0 := by
      rw [Matrix.det_fin_two]
      linear_combination
        (((u g : GL (Fin 2) (Dickson.K 3)) :
            Matrix (Fin 2) (Fin 2) (Dickson.K 3)) 1 0 * w 0 +
          ((u g : GL (Fin 2) (Dickson.K 3)) :
            Matrix (Fin 2) (Fin 2) (Dickson.K 3)) 1 1 * w 1) * e1 +
        (χ₀ g * v 0) * e4 -
        (((u g : GL (Fin 2) (Dickson.K 3)) :
            Matrix (Fin 2) (Fin 2) (Dickson.K 3)) 1 0 * v 0 +
          ((u g : GL (Fin 2) (Dickson.K 3)) :
            Matrix (Fin 2) (Fin 2) (Dickson.K 3)) 1 1 * v 1) * e3 -
        (χ₀ (σ₀⁻¹ * g * σ₀) * w 0) * e2
    rcases mul_eq_zero.mp hkey with h | h
    · calc χ₀ g * χ₀ (σ₀⁻¹ * g * σ₀)
          = ((u g : GL (Fin 2) (Dickson.K 3)) :
              Matrix (Fin 2) (Fin 2) (Dickson.K 3)).det := (sub_eq_zero.mp h).symm
        _ = ((Matrix.GeneralLinearGroup.det (u g) : (Dickson.K 3)ˣ) : Dickson.K 3) :=
            rfl
        _ = _ := hdet_val g
    · exact absurd h hdetP
  -- the ray-class leaf closes the dihedral case
  exact hne (dihedral_eigenvalue_character_symmetric_ray_class V hV hρ e θ'
    htriv' d hd x hx hθ'x σ₀ hσ₀ χ₀ hχne0 hχmul hχker hχprod hχunr h2unr)

set_option maxHeartbeats 1000000 in
/-- **The dihedral ray-class core for the induced eigenvalue
character** (DECOMPOSED 2026-07-23 into the two sorry nodes above —
the local-at-`2` unipotence analysis
`induced_character_unramified_at_two` and the at-`3`/ray-class
computation `dihedral_induced_ray_class_of_two_unramified`; the
assembly is proven): the per-field class-field-theoretic core of the
dihedral case, with the whole induced-representation step hoisted
into PROVEN hypotheses — `χ₀` is the eigenvalue character of the
common eigenline `K·v` of `u` on `H := ker θ' = Γ_{ℚ(√d)}`,
multiplicative (`hχmul`), nonvanishing (`hχne0`), trivial on `ker ρ`
(`hχker`, so its kernel is OPEN), trivial on the inertia of every
prime `q ∉ {2, 3}` (`hχunr`); the second line `K·(u σ₀ ·ᵥ v)` is
independent (`hindep`); and `hne` says that `χ₀` differs from its
`σ₀`-conjugate on `H`, i.e. `ρ ≅ Ind_H^{Γ_ℚ} χ₀` genuinely
dihedrally. -/
theorem dihedral_induced_character_ray_class {k : Type u}
    [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (θ' : Γ ℚ →* Multiplicative (ZMod 2))
    (hθ'surj : Function.Surjective θ')
    (htriv' : ∀ g : Γ ℚ, ρ g = 1 → θ' g = 1)
    (v : Fin 2 → Dickson.K 3) (hv : v ≠ 0)
    (d : ℤ)
    (hd : d = -1 ∨ d = 2 ∨ d = -2 ∨ d = 3 ∨ d = -3 ∨ d = 6 ∨ d = -6)
    (x : AlgebraicClosure ℚ) (hx : x ^ 2 = (d : AlgebraicClosure ℚ))
    (hθ'x : ∀ g : Γ ℚ, θ' g = 1 ↔ g x = x)
    (σ₀ : Γ ℚ) (hσ₀ : θ' σ₀ ≠ 1)
    (χ₀ : Γ ℚ → Dickson.K 3)
    (hχ₀ : ∀ g : Γ ℚ, θ' g = 1 →
      Matrix.mulVec ((u g : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v = χ₀ g • v)
    (hχne0 : ∀ g : Γ ℚ, θ' g = 1 → χ₀ g ≠ 0)
    (hχmul : ∀ g h : Γ ℚ, θ' g = 1 → θ' h = 1 →
      χ₀ (g * h) = χ₀ g * χ₀ h)
    (hχker : ∀ g : Γ ℚ, ρ g = 1 → χ₀ g = 1)
    (hχunr : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        χ₀ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1)
    (hindep : ¬ ∃ c : Dickson.K 3,
      Matrix.mulVec ((u σ₀ : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v = c • v)
    (hne : ¬ ∀ g : Γ ℚ, θ' g = 1 → χ₀ g = χ₀ (σ₀⁻¹ * g * σ₀)) :
    False :=
  dihedral_induced_ray_class_of_two_unramified V hV hρ habs b e u hu θ'
    hθ'surj htriv' v hv d hd x hx hθ'x σ₀ hσ₀ χ₀ hχ₀ hχne0 hχmul hχker
    hχunr hindep
    (induced_character_unramified_at_two V hV hρ b e u hu θ' htriv' v hv
      σ₀ hσ₀ χ₀ hχ₀ hindep)
    hne

set_option maxHeartbeats 1000000 in
/-- **The Serre/Tate elimination, dihedral ray-class computation with
an explicit eigenvector** (DECOMPOSED 2026-07-23 into the ray-class
core sorry node `dihedral_induced_character_ray_class` above — the
whole induced-representation step is PROVEN here as glue; the
character `θ'` is the possibly SWITCHED character produced by
`exists_index_two_common_eigenvector`, and `K = ℚ(x)`, `x = √d`,
`d ∈ {-1, 2, -2, 3, -3, 6, -6}` is ITS quadratic field, re-cut by
`exists_sqrt_of_quadratic_character_unramified_outside_two_three`).

The proven reduction: pick `σ₀ ∉ H := ker θ'` (`hθ'surj`); the
eigenvalue function `χ₀` on `H` is extracted from `heig` by choice
(unique since `v ≠ 0`); it is multiplicative and nonvanishing on `H`
because `u` is; it is trivial on `ker ρ` (`u` descends through the
faithful base change), hence — through `hρ.isUnramified`, with the
`Rat.subsingleton_ringHom` `convert` bridge — trivial on the inertia
of every prime `q ∉ {2, 3}`. The vector `w := u σ₀ ·ᵥ v` is NOT
proportional to `v`: otherwise `K·v` would be a common eigenline for
ALL of `u` (split `g` by `θ' g`), transported by
`no_common_eigenvector_of_absolutelyIrreducible` into a stable line
of the base change, contradicting `habs`. And `χ₀` differs from its
`σ₀`-conjugate on `H`: were they equal, `H` would act by the scalars
`χ₀` on the plane spanned by `v` and `w`
(`exists_smul_add_smul_of_not_proportional`), so ANY eigenvector `y`
of `u σ₀` would again be a common eigenvector for all of `u` — the
same contradiction. The sorried leaf consumes exactly this induced
structure. -/
theorem serre_elimination_dihedral_ray_class_of_eigenvector {k : Type u}
    [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (θ' : Γ ℚ →* Multiplicative (ZMod 2))
    (hθ'surj : Function.Surjective θ')
    (htriv' : ∀ g : Γ ℚ, ρ g = 1 → θ' g = 1)
    (v : Fin 2 → Dickson.K 3) (hv : v ≠ 0)
    (heig : ∀ g : Γ ℚ, θ' g = 1 → ∃ c : Dickson.K 3,
      Matrix.mulVec ((u g : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) v = c • v)
    (d : ℤ)
    (hd : d = -1 ∨ d = 2 ∨ d = -2 ∨ d = 3 ∨ d = -3 ∨ d = 6 ∨ d = -6)
    (x : AlgebraicClosure ℚ) (hx : x ^ 2 = (d : AlgebraicClosure ℚ))
    (hθ'x : ∀ g : Γ ℚ, θ' g = 1 ↔ g x = x) :
    False := by
  classical
  -- an element outside the kernel of `θ'`, and value bookkeeping
  obtain ⟨σ₀, hσ₀eq⟩ := hθ'surj (Multiplicative.ofAdd (1 : ZMod 2))
  have hσ₀ : θ' σ₀ ≠ 1 := by
    rw [hσ₀eq]
    decide
  have hy2 : ∀ y : Multiplicative (ZMod 2),
      y = 1 ∨ y = Multiplicative.ofAdd (1 : ZMod 2) := by decide
  have hmulval : ∀ g h' : Γ ℚ, (u (g * h')).val = (u g).val * (u h').val := by
    intro g h'
    rw [map_mul]
    rfl
  -- the eigenvalue function of the common eigenline
  choose! χ₀ hχ₀ using heig
  have hχ₀' : ∀ g : Γ ℚ, θ' g = 1 →
      Matrix.mulVec (u g).val v = χ₀ g • v := fun g hg => hχ₀ g hg
  have huniq : ∀ c c' : Dickson.K 3, c • v = c' • v → c = c' := by
    intro c c' hcc
    have h1 : (c - c') • v = 0 := by rw [sub_smul, hcc, sub_self]
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv
  -- `u` of a `ρ`-kernel element is the identity matrix
  have huone : ∀ g : Γ ℚ, ρ g = 1 → (u g).val = 1 := by
    intro g hg
    have h2 : (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g = 1 := hg
    have h1 : (Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V)) g = 1 := by
      have h3 : (Slop.OddRep.baseChange (AlgebraicClosure k)
          (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V)) g =
          ((MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g).baseChange
            (AlgebraicClosure k) := rfl
      rw [h3, h2, Module.End.one_eq_id, LinearMap.baseChange_id]
      rfl
    rw [hu g, h1, LinearMap.toMatrix_one]
    exact Matrix.map_one e (map_zero e) (map_one e)
  -- the kernel carrier: `χ₀` is trivial on `ker ρ`
  have hχker : ∀ g : Γ ℚ, ρ g = 1 → χ₀ g = 1 := by
    intro g hg
    have h1 := hχ₀' g (htriv' g hg)
    rw [huone g hg, Matrix.one_mulVec] at h1
    exact huniq (χ₀ g) 1 (by rw [one_smul, ← h1])
  -- unramified outside `{2, 3}` through `ρ`
  have hχunr : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        χ₀ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
    intro q hq hq2 hq3 σ hσ
    apply hχker
    have h1 : (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat) σ = 1 :=
      (hρ.isUnramified q hq ⟨hq2, hq3⟩).localInertiaGroup_le hσ
    rw [GaloisRep.toLocal_apply] at h1
    convert h1 using 4
    exact Subsingleton.elim _ _
  -- nonvanishing on the kernel
  have hχne0 : ∀ g : Γ ℚ, θ' g = 1 → χ₀ g ≠ 0 := by
    intro g hg h0
    apply hv
    have h1 : Matrix.mulVec (u g⁻¹).val (Matrix.mulVec (u g).val v) = v := by
      rw [Matrix.mulVec_mulVec, ← hmulval, inv_mul_cancel,
        show (u (1 : Γ ℚ)).val = 1 by rw [map_one]; rfl]
      exact Matrix.one_mulVec v
    rw [hχ₀' g hg, h0, zero_smul, Matrix.mulVec_zero] at h1
    exact h1.symm
  -- multiplicativity on the kernel
  have hχmul : ∀ g h' : Γ ℚ, θ' g = 1 → θ' h' = 1 →
      χ₀ (g * h') = χ₀ g * χ₀ h' := by
    intro g h' hg hh'
    have hgh' : θ' (g * h') = 1 := by rw [map_mul, hg, hh', mul_one]
    apply huniq
    rw [← hχ₀' (g * h') hgh', hmulval, ← Matrix.mulVec_mulVec,
      hχ₀' h' hh', Matrix.mulVec_smul, hχ₀' g hg, smul_smul,
      mul_comm (χ₀ g) (χ₀ h')]
  -- `u σ₀ ·ᵥ v` is not proportional to `v` (absolute irreducibility)
  have hindep : ¬ ∃ c : Dickson.K 3, Matrix.mulVec (u σ₀).val v = c • v := by
    rintro ⟨c, hcw⟩
    apply no_common_eigenvector_of_absolutelyIrreducible V hV habs b e u hu v hv
    intro g
    by_cases hg : θ' g = 1
    · exact ⟨χ₀ g, hχ₀ g hg⟩
    · have hgω : θ' g = Multiplicative.ofAdd (1 : ZMod 2) := by
        rcases hy2 (θ' g) with h | h
        · exact absurd h hg
        · exact h
      have hker1 : θ' (σ₀⁻¹ * g) = 1 := by
        rw [map_mul, map_inv, hσ₀eq, hgω]
        decide
      refine ⟨χ₀ (σ₀⁻¹ * g) * c, ?_⟩
      show Matrix.mulVec (u g).val v = (χ₀ (σ₀⁻¹ * g) * c) • v
      have hsplit : g = σ₀ * (σ₀⁻¹ * g) := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      calc Matrix.mulVec (u g).val v
          = Matrix.mulVec (u (σ₀ * (σ₀⁻¹ * g))).val v := by rw [← hsplit]
        _ = Matrix.mulVec (u σ₀).val
            (Matrix.mulVec (u (σ₀⁻¹ * g)).val v) := by
            rw [hmulval, ← Matrix.mulVec_mulVec]
        _ = Matrix.mulVec (u σ₀).val (χ₀ (σ₀⁻¹ * g) • v) := by
            rw [hχ₀' _ hker1]
        _ = χ₀ (σ₀⁻¹ * g) • Matrix.mulVec (u σ₀).val v :=
            Matrix.mulVec_smul _ _ _
        _ = χ₀ (σ₀⁻¹ * g) • (c • v) := by rw [hcw]
        _ = (χ₀ (σ₀⁻¹ * g) * c) • v := by rw [smul_smul]
  -- `χ₀` differs from its `σ₀`-conjugate on the kernel
  have hne : ¬ ∀ g : Γ ℚ, θ' g = 1 → χ₀ g = χ₀ (σ₀⁻¹ * g * σ₀) := by
    intro hconj
    -- kernel elements act by the scalar `χ₀` on EVERY vector
    have hkerscal : ∀ h' : Γ ℚ, θ' h' = 1 → ∀ x' : Fin 2 → Dickson.K 3,
        Matrix.mulVec (u h').val x' = χ₀ h' • x' := by
      intro h' hh' x'
      obtain ⟨α, β, hx'⟩ := exists_smul_add_smul_of_not_proportional hv hindep x'
      have hconjker : θ' (σ₀⁻¹ * h' * σ₀) = 1 := by
        rw [map_mul, map_mul, map_inv, hh', mul_one, inv_mul_cancel]
      have hw : Matrix.mulVec (u h').val (Matrix.mulVec (u σ₀).val v) =
          χ₀ h' • Matrix.mulVec (u σ₀).val v := by
        have hsplit : h' * σ₀ = σ₀ * (σ₀⁻¹ * h' * σ₀) := by
          rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
        calc Matrix.mulVec (u h').val (Matrix.mulVec (u σ₀).val v)
            = Matrix.mulVec (u (h' * σ₀)).val v := by
              rw [hmulval, Matrix.mulVec_mulVec]
          _ = Matrix.mulVec (u (σ₀ * (σ₀⁻¹ * h' * σ₀))).val v := by
              rw [← hsplit]
          _ = Matrix.mulVec (u σ₀).val
              (Matrix.mulVec (u (σ₀⁻¹ * h' * σ₀)).val v) := by
              rw [hmulval, ← Matrix.mulVec_mulVec]
          _ = Matrix.mulVec (u σ₀).val (χ₀ (σ₀⁻¹ * h' * σ₀) • v) := by
              rw [hχ₀' _ hconjker]
          _ = χ₀ (σ₀⁻¹ * h' * σ₀) • Matrix.mulVec (u σ₀).val v :=
              Matrix.mulVec_smul _ _ _
          _ = χ₀ h' • Matrix.mulVec (u σ₀).val v := by
              rw [← hconj h' hh']
      rw [hx', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hχ₀' h' hh', hw]
      module
    -- any eigenvector of `u σ₀` is then a common eigenvector
    obtain ⟨s, hsev⟩ :=
      Module.End.exists_eigenvalue (Matrix.mulVecLin (u σ₀).val)
    obtain ⟨y, hy⟩ := hsev.exists_hasEigenvector
    have hyv : Matrix.mulVec (u σ₀).val y = s • y := by
      have h1 := Module.End.mem_eigenspace_iff.mp hy.1
      rwa [Matrix.mulVecLin_apply] at h1
    apply no_common_eigenvector_of_absolutelyIrreducible V hV habs b e u hu
      y hy.2
    intro g
    by_cases hg : θ' g = 1
    · exact ⟨χ₀ g, hkerscal g hg y⟩
    · have hgω : θ' g = Multiplicative.ofAdd (1 : ZMod 2) := by
        rcases hy2 (θ' g) with h | h
        · exact absurd h hg
        · exact h
      have hker2 : θ' (g * σ₀⁻¹) = 1 := by
        rw [map_mul, map_inv, hσ₀eq, hgω]
        decide
      refine ⟨χ₀ (g * σ₀⁻¹) * s, ?_⟩
      show Matrix.mulVec (u g).val y = (χ₀ (g * σ₀⁻¹) * s) • y
      have hsplit : g = g * σ₀⁻¹ * σ₀ := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
      calc Matrix.mulVec (u g).val y
          = Matrix.mulVec (u (g * σ₀⁻¹ * σ₀)).val y := by rw [← hsplit]
        _ = Matrix.mulVec (u (g * σ₀⁻¹)).val
            (Matrix.mulVec (u σ₀).val y) := by
            rw [hmulval, ← Matrix.mulVec_mulVec]
        _ = Matrix.mulVec (u (g * σ₀⁻¹)).val (s • y) := by rw [hyv]
        _ = s • Matrix.mulVec (u (g * σ₀⁻¹)).val y :=
            Matrix.mulVec_smul _ _ _
        _ = s • (χ₀ (g * σ₀⁻¹) • y) := by rw [hkerscal _ hker2 y]
        _ = (χ₀ (g * σ₀⁻¹) * s) • y := by
            rw [smul_smul, mul_comm s (χ₀ (g * σ₀⁻¹))]
  -- the ray-class core (sorried leaf)
  exact dihedral_induced_character_ray_class V hV hρ habs b e u hu θ' hθ'surj
    htriv' v hv d hd x hx hθ'x σ₀ hσ₀ χ₀ hχ₀ hχne0 hχmul hχker hχunr hindep
    hne

set_option maxHeartbeats 1000000 in
/-- **The Serre/Tate elimination, dihedral ray-class computation**
(DECOMPOSED 2026-07-23 into the two sorry nodes above — the
common-eigenvector dichotomy `exists_index_two_common_eigenvector`
(which may SWITCH the quadratic character, as required by the
Klein-four projective sub-case where `ρ|_{ker θ}` is irreducible) and
the eigenvector-explicit per-field ray-class core
`serre_elimination_dihedral_ray_class_of_eigenvector`; the reduction
is proven): the dihedral situation of
`serre_elimination_dihedral_arith`, with the quadratic field made
explicit, is contradictory. The proven reduction: the dichotomy leaf
yields a surjective quadratic character `θ'` trivial on `ker ρ` with
a common eigenvector of `u` on `ker θ'`; `ker θ'` is open (it
contains the open kernel of `ρ`) and unramified outside `{2, 3}`
(through `ρ`, exactly as in `serre_elimination_dihedral_arith`), so
the PROVEN classification
`exists_sqrt_of_quadratic_character_unramified_outside_two_three`
re-cuts the possibly different quadratic field `ℚ(√d')`,
`d' ∈ {-1, ±2, ±3, ±6}`, of `θ'`, and the ray-class leaf applied to
`θ'` yields the contradiction. The original data `d`, `x`, `hθx` of
`θ` itself are not consumed: the field switch may abandon them. -/
theorem serre_elimination_dihedral_ray_class {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (θ : Γ ℚ →* Multiplicative (ZMod 2))
    (hθsurj : Function.Surjective θ)
    (hcomm : ∀ g h : Γ ℚ, θ g = 1 → θ h = 1 → π g * π h = π h * π g)
    (htr : ∀ g : Γ ℚ, θ g ≠ 1 →
      LinearMap.trace k V
        ((MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g) = 0)
    (d : ℤ)
    (_hd : d = -1 ∨ d = 2 ∨ d = -2 ∨ d = 3 ∨ d = -3 ∨ d = 6 ∨ d = -6)
    (x : AlgebraicClosure ℚ) (_hx : x ^ 2 = (d : AlgebraicClosure ℚ))
    (_hθx : ∀ g : Γ ℚ, θ g = 1 ↔ g x = x) :
    False := by
  classical
  -- the dichotomy: a common eigenvector after a possible field switch
  obtain ⟨θ', hθ'surj, htriv', v, hv, heig⟩ :=
    exists_index_two_common_eigenvector V hV b e u hu π hπ θ hθsurj hcomm htr
  -- the kernel of `θ'` is open (it contains the open kernel of `ρ`)
  let Kρ : Subgroup (Γ ℚ) :=
    { carrier := {g | ρ g = 1}
      one_mem' := map_one ρ
      mul_mem' := by
        intro a a' ha ha'
        show ρ (a * a') = 1
        rw [map_mul, ha, ha', mul_one]
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ = 1
        have h1 : ρ a⁻¹ * ρ a = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h1 }
  haveI hfinV : Finite V := Module.finite_of_finite k
  have hKρ_open : IsOpen (Kρ : Set (Γ ℚ)) :=
    isOpen_setOf_galoisRep_eq_one ρ hfinV
  have hker : Kρ ≤ θ'.ker := fun g hg => MonoidHom.mem_ker.mpr (htriv' g hg)
  have hopen : IsOpen (θ'.ker : Set (Γ ℚ)) :=
    Subgroup.isOpen_mono hker hKρ_open
  -- `θ'` is unramified outside `{2, 3}` (through `ρ`)
  have hunram : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        θ' (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
    intro q hq hq2 hq3 σ hσ
    apply htriv'
    have h1 : (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat) σ = 1 :=
      (hρ.isUnramified q hq ⟨hq2, hq3⟩).localInertiaGroup_le hσ
    rw [GaloisRep.toLocal_apply] at h1
    convert h1 using 4
    exact Subsingleton.elim _ _
  -- the classification re-cuts the (possibly switched) quadratic field
  obtain ⟨d', hd', x', hx', hθ'x'⟩ :=
    exists_sqrt_of_quadratic_character_unramified_outside_two_three
      θ' hθ'surj hopen hunram
  -- the per-field ray-class computation on the switched character
  exact serre_elimination_dihedral_ray_class_of_eigenvector V hV hρ habs
    b e u hu θ' hθ'surj htriv' v hv heig d' hd' x' hx' hθ'x'

set_option maxHeartbeats 1000000 in
/-- **The Serre/Tate elimination, dihedral arithmetic** (DECOMPOSED
2026-07-22 into the two sorry nodes above — the quadratic-field
classification
`exists_sqrt_of_quadratic_character_unramified_outside_two_three` and
the per-field ray-class computation
`serre_elimination_dihedral_ray_class`; the reduction is proven): an
absolutely irreducible mod-3 hardly ramified representation admits no
surjective quadratic character `θ` of `Γ ℚ` such that the projective
images of kernel elements commute and every element outside the
kernel has trace zero. The proven reduction: the kernel of `θ` is
open (`ρ g = 1` forces `tr ρ g = 2 ≠ 0` in the characteristic-3 field
`k`, so `ker ρ ≤ ker θ` by the trace hypothesis, and `ker ρ` is open
by continuity — `isOpen_setOf_galoisRep_eq_one`); `θ` is unramified
outside `{2, 3}` (`hρ.isUnramified` kills the local inertia through
`ρ`, hence through `θ` by the same kernel inclusion); so the
classification leaf cuts out `ℚ(√d)`, `d ∈ {-1, ±2, ±3, ±6}`, and
the ray-class leaf yields the contradiction. -/
theorem serre_elimination_dihedral_arith {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (θ : Γ ℚ →* Multiplicative (ZMod 2))
    (hθsurj : Function.Surjective θ)
    (hcomm : ∀ g h : Γ ℚ, θ g = 1 → θ h = 1 → π g * π h = π h * π g)
    (htr : ∀ g : Γ ℚ, θ g ≠ 1 →
      LinearMap.trace k V
        ((MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g) = 0) :
    False := by
  classical
  -- `2 ≠ 0` in `k` (its characteristic is `3`)
  have h3k : (3 : k) = 0 := three_eq_zero_of_finite_padicIntThree_algebra
  have h2k : (2 : k) ≠ 0 := fun h =>
    one_ne_zero (α := k) (by linear_combination h3k - h)
  haveI hfinV : Finite V := Module.finite_of_finite k
  have hfr : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  -- `θ` is trivial wherever the representation is: `tr 1 = 2 ≠ 0`
  have htriv : ∀ g : Γ ℚ, ρ g = 1 → θ g = 1 := by
    intro g hg
    by_contra hne
    have h0 := htr g hne
    have h1 : (MonoidHomClass.toMonoidHom ρ :
        Representation k (Γ ℚ) V) g = 1 := hg
    rw [h1, LinearMap.trace_one, hfr] at h0
    exact h2k (by exact_mod_cast h0)
  -- the kernel of `θ` is open (it contains the open kernel of `ρ`)
  let Kρ : Subgroup (Γ ℚ) :=
    { carrier := {g | ρ g = 1}
      one_mem' := map_one ρ
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) = 1
        rw [map_mul, ha, hb, mul_one]
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ = 1
        have h1 : ρ a⁻¹ * ρ a = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h1 }
  have hKρ_open : IsOpen (Kρ : Set (Γ ℚ)) :=
    isOpen_setOf_galoisRep_eq_one ρ hfinV
  have hker : Kρ ≤ θ.ker := fun g hg => MonoidHom.mem_ker.mpr (htriv g hg)
  have hopen : IsOpen (θ.ker : Set (Γ ℚ)) :=
    Subgroup.isOpen_mono hker hKρ_open
  -- `θ` is unramified outside `{2, 3}` (through `ρ`)
  have hunram : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        θ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 1 := by
    intro q hq hq2 hq3 σ hσ
    apply htriv
    have h1 : (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat) σ = 1 :=
      (hρ.isUnramified q hq ⟨hq2, hq3⟩).localInertiaGroup_le hσ
    rw [GaloisRep.toLocal_apply] at h1
    convert h1 using 4
    exact Subsingleton.elim _ _
  -- the classification of quadratic fields ramified only at `{2, 3}`
  obtain ⟨d, hd, x, hx, hθx⟩ :=
    exists_sqrt_of_quadratic_character_unramified_outside_two_three
      θ hθsurj hopen hunram
  -- the per-field ray-class computation
  exact serre_elimination_dihedral_ray_class V hV hρ habs b e u hu π hπ
    θ hθsurj hcomm htr d hd x hx hθx

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The Serre/Tate elimination, dihedral case** (DECOMPOSED
2026-07-22 into the arithmetic sorry node
`serre_elimination_dihedral_arith` above; the reduction is proven):
the projective image of an absolutely irreducible mod-3 hardly
ramified representation cannot be dihedral. The proven reduction:
composing `π` with the dihedral isomorphism and the parity map
`D_n → ℤ/2` (rotations `↦ 0`, reflections `↦ 1`) yields a surjective
quadratic character `θ` of `Γ ℚ`; kernel elements have projectively
commuting images (rotations commute); and any `g` outside the kernel
maps to a reflection, so `π g ≠ 1` and `(π g)² = 1`, whence
`(σρ g)² = ν • 1` is a scalar while `σρ g` is not, and the `2×2`
Cayley–Hamilton identity forces `tr (σρ g) = 0`, which descends along
the base change to `tr (ρ g) = 0` in `k`. The remaining content — no
such `θ` exists, by the classification of the quadratic fields
`ℚ(√d)`, `d ∈ {-1, ±2, ±3, ±6}` ramified only in `{2, 3}` and the
smallness of their ray class groups — is the sorry node above
(Serre's mod-3 analogue of Tate's 2-adic letter argument). -/
theorem serre_elimination_dihedral {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase : ∃ n : ℕ, n ≥ 2 ∧ Nonempty (π.range ≃* DihedralGroup n)) :
    False := by
  classical
  obtain ⟨n, _, ⟨eiso⟩⟩ := hcase
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := AlgebraicClosure k
  set σρ : Representation L (Γ ℚ) (L ⊗[k] V) :=
    Slop.OddRep.baseChange L (MonoidHomClass.toMonoidHom ρ)
  have hirr : σρ.IsIrreducible := habs
  haveI : Module.Finite L (L ⊗[k] V) := Module.Finite.base_change k L V
  have hfr2 : Module.finrank L (L ⊗[k] V) = 2 := by
    rw [Module.finrank_baseChange]
    exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  haveI : Nontrivial (L ⊗[k] V) :=
    Module.nontrivial_of_finrank_pos (R := L) (by omega)
  obtain ⟨hnt, hsub⟩ := (Slop.OddRep.isIrreducible_iff_forall σρ).mp hirr
  -- transport toolkit (as in the semidirect case)
  have hmap_inj : ∀ M N : Matrix (Fin 2) (Fin 2) (AlgebraicClosure k),
      M.map e = N.map e → M = N := by
    intro M N h
    ext i j
    exact e.injective (congrFun (congrFun (congrArg Matrix.of.symm h) i) j)
  have hmulM : ∀ gg₁ gg₂ : Γ ℚ, LinearMap.toMatrix b b (σρ gg₁) *
      LinearMap.toMatrix b b (σρ gg₂) =
      LinearMap.toMatrix b b (σρ gg₁ * σρ gg₂) :=
    fun gg₁ gg₂ => (LinearMap.toMatrix_comp b b b _ _).symm
  -- commuting with the whole action forces a scalar
  have hscalar_of_comm : ∀ T : Module.End L (L ⊗[k] V),
      (∀ h : Γ ℚ, T * σρ h = σρ h * T) → ∃ ν : L, T = ν • 1 := by
    intro T hT
    obtain ⟨ν, hν⟩ := Module.End.exists_eigenvalue T
    have hEinv : ∀ h : Γ ℚ, ∀ w ∈ Module.End.eigenspace T ν,
        σρ h w ∈ Module.End.eigenspace T ν := by
      intro h w hw
      rw [Module.End.mem_eigenspace_iff] at hw ⊢
      have hc := congrFun (congrArg DFunLike.coe (hT h)) w
      simp only [Module.End.mul_apply] at hc
      rw [hc, hw, map_smul]
    rcases hsub (Module.End.eigenspace T ν) hEinv with hE | hE
    · exact absurd hE hν
    · refine ⟨ν, LinearMap.ext fun v => ?_⟩
      have hv : v ∈ Module.End.eigenspace T ν := hE ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hv
      simpa using hv
  -- a `g` whose projective class is trivial acts by a scalar
  have hscalar_of_pi_one : ∀ g : Γ ℚ, π g = 1 → ∃ ν : L, σρ g = ν • 1 := by
    intro g hg
    refine hscalar_of_comm (σρ g) fun h => ?_
    have hcen : (u g : GL (Fin 2) (Dickson.K 3)) ∈
        Subgroup.center (GL (Fin 2) (Dickson.K 3)) := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center
        (GL (Fin 2) (Dickson.K 3))), MonoidHom.mem_ker]
      exact ((hπ g).symm.trans hg : _)
    have hcommGL : u g * u h = u h * u g :=
      (Subgroup.mem_center_iff.mp hcen (u h)).symm
    have hval := congrArg Units.val hcommGL
    rw [Units.val_mul, Units.val_mul, hu, hu, ← Matrix.map_mul,
      ← Matrix.map_mul] at hval
    have hmat := hmap_inj _ _ hval
    rw [hmulM, hmulM] at hmat
    exact (LinearMap.toMatrix b b).injective hmat
  -- conversely: a scalar action has trivial projective class
  have hpi_one_of_scalar : ∀ g : Γ ℚ, (∃ ν : L, σρ g = ν • 1) → π g = 1 := by
    rintro g ⟨ν, hν⟩
    have hval : ((u g : GL (Fin 2) (Dickson.K 3)) :
        Matrix (Fin 2) (Fin 2) (Dickson.K 3)) = e ν • 1 := by
      rw [hu, hν, map_smul, LinearMap.toMatrix_one]
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.map_apply, Matrix.smul_apply, hij]
    have hcen : (u g : GL (Fin 2) (Dickson.K 3)) ∈
        Subgroup.center (GL (Fin 2) (Dickson.K 3)) := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hval]
      rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    rw [hπ g]
    have : QuotientGroup.mk' (Subgroup.center
        (GL (Fin 2) (Dickson.K 3))) (u g) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hcen
    exact this
  -- the parity map of the dihedral group: rotations ↦ 0, reflections ↦ 1
  let q : DihedralGroup n →* Multiplicative (ZMod 2) :=
    { toFun := fun x => match x with
        | .r _ => 1
        | .sr _ => Multiplicative.ofAdd 1
      map_one' := rfl
      map_mul' := by
        rintro (i | i) (j | j) <;>
          simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
            DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;> decide }
  -- the quadratic character of `Γ ℚ` cut out by the rotation subgroup
  let θ : Γ ℚ →* Multiplicative (ZMod 2) :=
    q.comp (eiso.toMonoidHom.comp π.rangeRestrict)
  have hθ_eval : ∀ g : Γ ℚ, θ g = q (eiso (π.rangeRestrict g)) := fun g => rfl
  -- values of `q`
  have hq_r : ∀ i : ZMod n, q (.r i) = 1 := fun i => rfl
  have hq_sr : ∀ i : ZMod n, q (.sr i) = Multiplicative.ofAdd 1 := fun i => rfl
  have h01 : ∀ y : Multiplicative (ZMod 2),
      y = 1 ∨ y = Multiplicative.ofAdd 1 := by decide
  have hne1 : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  -- surjectivity of `θ`
  have hθsurj : Function.Surjective θ := by
    intro y
    rcases h01 y with rfl | rfl
    · exact ⟨1, map_one θ⟩
    · obtain ⟨x, hx⟩ := π.rangeRestrict_surjective (eiso.symm (.sr 0))
      refine ⟨x, ?_⟩
      rw [hθ_eval, hx, MulEquiv.apply_symm_apply, hq_sr]
  -- kernel elements are rotations, hence commute projectively
  have hrot : ∀ x : Γ ℚ, θ x = 1 →
      ∃ i, eiso (π.rangeRestrict x) = .r i := by
    intro x hx
    rcases hex : eiso (π.rangeRestrict x) with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      rw [hθ_eval, hex, hq_sr] at hx
      exact hne1 hx
  have hcomm : ∀ g h : Γ ℚ, θ g = 1 → θ h = 1 →
      π g * π h = π h * π g := by
    intro g h hg hh
    obtain ⟨i, hi⟩ := hrot g hg
    obtain ⟨j, hj⟩ := hrot h hh
    have hx : π.rangeRestrict g * π.rangeRestrict h =
        π.rangeRestrict h * π.rangeRestrict g := by
      apply eiso.injective
      rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r,
        DihedralGroup.r_mul_r, add_comm]
    have := congrArg Subtype.val hx
    simpa using this
  -- elements outside the kernel are reflections: trace zero
  have htr : ∀ g : Γ ℚ, θ g ≠ 1 →
      LinearMap.trace k V
        ((MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) g) = 0 := by
    intro g hg
    -- the image of `g` is a reflection
    have hsr : ∃ i, eiso (π.rangeRestrict g) = .sr i := by
      rcases hex : eiso (π.rangeRestrict g) with i | i
      · exact absurd (by rw [hθ_eval, hex, hq_r]) hg
      · exact ⟨i, rfl⟩
    obtain ⟨i, hi⟩ := hsr
    -- `π g ≠ 1` and `π (g * g) = 1`
    have hπg_ne : π g ≠ 1 := by
      intro h1
      have hx1 : π.rangeRestrict g = 1 := Subtype.ext (by simpa using h1)
      rw [hx1, map_one] at hi
      rw [DihedralGroup.one_def] at hi
      injection hi
    have hπg2 : π (g * g) = 1 := by
      have hx : π.rangeRestrict (g * g) = 1 := by
        apply eiso.injective
        rw [map_mul, map_mul, map_one, hi, DihedralGroup.sr_mul_sr, sub_self,
          ← DihedralGroup.one_def]
      have := congrArg Subtype.val hx
      simpa using this
    -- `σρ (g * g)` is a scalar while `σρ g` is not
    obtain ⟨ν, hν⟩ := hscalar_of_pi_one (g * g) hπg2
    have hg_ns : ¬ ∃ μ : L, σρ g = μ • 1 := fun hs => hπg_ne
      (hpi_one_of_scalar g hs)
    -- matrix form and the 2×2 Cayley–Hamilton identity
    set A := LinearMap.toMatrix b b (σρ g) with hA
    have hA2 : A * A = ν • 1 := by
      rw [hA, hmulM, ← map_mul, hν, map_smul, LinearMap.toMatrix_one]
    have hCH : A * A = (Matrix.trace A) • A - A.det • 1 := by
      ext i' j'
      fin_cases i' <;> fin_cases j' <;>
        simp [Matrix.mul_apply, Matrix.trace, Matrix.diag, Matrix.det_fin_two,
          Fin.sum_univ_two] <;> ring
    -- if the trace were nonzero, `A` would be scalar
    have htrA : Matrix.trace A = 0 := by
      by_contra htA
      have h1 : (Matrix.trace A) • A =
          (ν + A.det) • (1 : Matrix (Fin 2) (Fin 2) L) := by
        have h := hA2.symm.trans hCH
        rw [eq_sub_iff_add_eq] at h
        rw [← h, add_smul]
      have hAs : A = ((Matrix.trace A)⁻¹ * (ν + A.det)) •
          (1 : Matrix (Fin 2) (Fin 2) L) := by
        rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ htA, one_smul]
      refine hg_ns ⟨(Matrix.trace A)⁻¹ * (ν + A.det),
        (LinearMap.toMatrix b b).injective ?_⟩
      rw [map_smul, LinearMap.toMatrix_one, ← hA]
      exact hAs
    -- descend the trace along the base change
    have h1 : LinearMap.trace L (L ⊗[k] V) (σρ g) = 0 := by
      rw [LinearMap.trace_eq_matrix_trace L b, ← hA]
      exact htrA
    have h2 : σρ g = ((MonoidHomClass.toMonoidHom ρ :
        Representation k (Γ ℚ) V) g).baseChange L := rfl
    rw [h2, LinearMap.trace_baseChange] at h1
    exact (algebraMap k L).injective (by rw [h1, map_zero])
  exact serre_elimination_dihedral_arith V hV hρ habs b e u hu π hπ
    θ hθsurj hcomm htr

/-- **The Serre/Tate elimination, `A₄` case** (DERIVED 2026-07-22
from the shared root-discriminant skeleton
`serre_elimination_exceptional`): the projective image of a mod-3
hardly ramified representation cannot be `A₄` — the cut-out number
field would be totally complex of degree `≥ 48` with root
discriminant `≤ 2^{2/3}·3^{3/2} = 8.2497…`, contradicting the
Odlyzko bound. -/
theorem serre_elimination_alt4 {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase : Nonempty (π.range ≃* alternatingGroup (Fin 4))) :
    False :=
  serre_elimination_exceptional V hV hρ habs b e u hu π hπ (Or.inl hcase)

/-- **The Serre/Tate elimination, `S₄` case** (DERIVED 2026-07-22
from the shared root-discriminant skeleton
`serre_elimination_exceptional`). -/
theorem serre_elimination_sym4 {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase : Nonempty (π.range ≃* Equiv.Perm (Fin 4))) :
    False :=
  serre_elimination_exceptional V hV hρ habs b e u hu π hπ
    (Or.inr (Or.inl hcase))

/-- **The Serre/Tate elimination, `A₅` case** (DERIVED 2026-07-22
from the shared root-discriminant skeleton
`serre_elimination_exceptional`). -/
theorem serre_elimination_alt5 {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase : Nonempty (π.range ≃* alternatingGroup (Fin 5))) :
    False :=
  serre_elimination_exceptional V hV hρ habs b e u hu π hπ
    (Or.inr (Or.inr (Or.inl hcase)))

/-- **The Serre/Tate elimination, `PSL₂(𝔽_{3^m})` case** (DERIVED
2026-07-22 from the shared root-discriminant skeleton
`serre_elimination_exceptional`; `PSL₂(𝔽₃) ≅ A₄` is subsumed in the
degree-`≥ 48` bound of the skeleton). -/
theorem serre_elimination_psl {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase : ∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 m))) :
    False :=
  serre_elimination_exceptional V hV hρ habs b e u hu π hπ
    (Or.inr (Or.inr (Or.inr (Or.inl hcase))))

/-- **The Serre/Tate elimination, `PGL₂(𝔽_{3^m})` case** (DERIVED
2026-07-22 from the shared root-discriminant skeleton
`serre_elimination_exceptional`; `PGL₂(𝔽₃) ≅ S₄` is subsumed in the
degree-`≥ 48` bound of the skeleton). -/
theorem serre_elimination_pgl {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase : ∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
      (GL (Fin 2) (GaloisField 3 m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField 3 m))))) :
    False :=
  serre_elimination_exceptional V hV hρ habs b e u hu π hπ
    (Or.inr (Or.inr (Or.inr (Or.inr hcase))))

/-- **The Serre §5.4/Tate elimination, arithmetic cases** (DECOMPOSED
2026-07-22 into the six per-case sorry nodes above — `dihedral`,
`alt4`, `sym4`, `alt5`, `psl`, `pgl`): with the notation of
`serre_elimination` below, the dihedral, `A₄`, `S₄`, `A₅`,
`PSL₂(𝔽_{3^m})`, `PGL₂(𝔽_{3^m})` cases contradict the hardly-ramified
ramification constraints (cyclotomic determinant, unramified outside
`{2, 3}`, flat at `3`, tame quadratic quotient at `2`) via Serre's
discriminant/conductor bounds over `ℚ` (Serre, Duke 1987, §5.4: no
extension of `ℚ` with these Galois groups and local conditions
exists). -/
theorem serre_elimination_arith {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase :
      (∃ n : ℕ, n ≥ 2 ∧ Nonempty (π.range ≃* DihedralGroup n)) ∨
      (Nonempty (π.range ≃* alternatingGroup (Fin 4))) ∨
      (Nonempty (π.range ≃* Equiv.Perm (Fin 4))) ∨
      (Nonempty (π.range ≃* alternatingGroup (Fin 5))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 m))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        (GL (Fin 2) (GaloisField 3 m) ⧸
          Subgroup.center (GL (Fin 2) (GaloisField 3 m)))))) :
    False := by
  rcases hcase with h | h | h | h | h | h
  · exact serre_elimination_dihedral V hV hρ habs b e u hu π hπ h
  · exact serre_elimination_alt4 V hV hρ habs b e u hu π hπ h
  · exact serre_elimination_sym4 V hV hρ habs b e u hu π hπ h
  · exact serre_elimination_alt5 V hV hρ habs b e u hu π hπ h
  · exact serre_elimination_psl V hV hρ habs b e u hu π hπ h
  · exact serre_elimination_pgl V hV hρ habs b e u hu π hπ h

set_option backward.isDefEq.respectTransparency false in
/-- The seven noncyclic Dickson cases, split into the rep-theoretic
semidirect case (`serre_elimination_semidirect`) and the six arithmetic
cases (`serre_elimination_arith`). -/
theorem serre_elimination_noncyclic {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase :
      (∃ n : ℕ, n ≥ 2 ∧ Nonempty (π.range ≃* DihedralGroup n)) ∨
      (Nonempty (π.range ≃* alternatingGroup (Fin 4))) ∨
      (Nonempty (π.range ≃* Equiv.Perm (Fin 4))) ∨
      (Nonempty (π.range ≃* alternatingGroup (Fin 5))) ∨
      (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t 3) (_ : t ∣ 3 ^ m - 1)
        (φ : Multiplicative (ZMod t) →*
          MulAut (Multiplicative (Fin m → ZMod 3))),
        Nonempty (π.range ≃*
          (Multiplicative (Fin m → ZMod 3)) ⋊[φ] Multiplicative (ZMod t))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 m))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        (GL (Fin 2) (GaloisField 3 m) ⧸
          Subgroup.center (GL (Fin 2) (GaloisField 3 m)))))) :
    False := by
  rcases hcase with h | h | h | h | ⟨m, t, hm, _, _, φ, hiso⟩ | h | h
  · exact serre_elimination_arith V hV hρ habs b e u hu π hπ (Or.inl h)
  · exact serre_elimination_arith V hV hρ habs b e u hu π hπ (Or.inr (Or.inl h))
  · exact serre_elimination_arith V hV hρ habs b e u hu π hπ
      (Or.inr (Or.inr (Or.inl h)))
  · exact serre_elimination_arith V hV hρ habs b e u hu π hπ
      (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact serre_elimination_semidirect V hV hρ habs b e u hu π hπ hm φ hiso
  · exact serre_elimination_arith V hV hρ habs b e u hu π hπ
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact serre_elimination_arith V hV hρ habs b e u hu π hπ
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The Serre §5.4/Tate elimination over the Dickson list** (cyclic
case PROVEN 2026-07-18; the noncyclic cases delegate to the leaf
above): given a mod-3 hardly ramified representation `ρ`, a group
homomorphism `π` from `Γ ℚ` to `PGL₂(𝔽̄₃)` which is the
projectivization of the base change of `ρ` to `𝔽̄₃` (witnessed
explicitly: `u` is the matrix form of the base-changed action in the
basis `b`, transported along the field identification `e`, and `π` is
its class modulo the centre), and the Dickson classification of the
finite image `π.range`, every case is eliminated. -/
theorem serre_elimination {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (habs : Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V))
    (b : Module.Basis (Fin 2) (AlgebraicClosure k)
      ((AlgebraicClosure k) ⊗[k] V))
    (e : AlgebraicClosure k ≃+* Dickson.K 3)
    (u : Γ ℚ →* GL (Fin 2) (Dickson.K 3))
    (hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b ((Slop.OddRep.baseChange (AlgebraicClosure k)
        (MonoidHomClass.toMonoidHom ρ)) g)).map e)
    (π : Γ ℚ →* Dickson.PGL 3)
    (hπ : ∀ g, π g = QuotientGroup.mk (u g))
    (hcase :
      (IsCyclic π.range) ∨
      (∃ n : ℕ, n ≥ 2 ∧ Nonempty (π.range ≃* DihedralGroup n)) ∨
      (Nonempty (π.range ≃* alternatingGroup (Fin 4))) ∨
      (Nonempty (π.range ≃* Equiv.Perm (Fin 4))) ∨
      (Nonempty (π.range ≃* alternatingGroup (Fin 5))) ∨
      (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t 3) (_ : t ∣ 3 ^ m - 1)
        (φ : Multiplicative (ZMod t) →*
          MulAut (Multiplicative (Fin m → ZMod 3))),
        Nonempty (π.range ≃*
          (Multiplicative (Fin m → ZMod 3)) ⋊[φ] Multiplicative (ZMod t))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 m))) ∨
      (∃ m : ℕ, m ≥ 1 ∧ Nonempty (π.range ≃*
        (GL (Fin 2) (GaloisField 3 m) ⧸
          Subgroup.center (GL (Fin 2) (GaloisField 3 m)))))) :
    False := by
  rcases hcase with hcyc | hrest
  · -- **cyclic case, PROVEN**: a cyclic projective image makes the matrix
    -- image abelian (a group with cyclic central quotient is abelian), so
    -- the base-changed action is by commuting operators; over the
    -- algebraically closed field each operator then acts as a scalar (its
    -- eigenspace is invariant, hence everything), and a scalar action on a
    -- `2`-dimensional space has a stable line — contradicting absolute
    -- irreducibility.
    classical
    set L := AlgebraicClosure k
    set σρ : Representation L (Γ ℚ) (L ⊗[k] V) :=
      Slop.OddRep.baseChange L (MonoidHomClass.toMonoidHom ρ)
    have hirr : σρ.IsIrreducible := habs
    -- the image of `π` is the image of `u.range` in the quotient
    have hrange : Subgroup.map
        (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (Dickson.K 3))))
        u.range = π.range := by
      ext x
      simp only [Subgroup.mem_map, MonoidHom.mem_range]
      constructor
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, (hπ g).trans rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨u g, ⟨g, rfl⟩, ((hπ g).trans rfl).symm⟩
    -- the matrix image is abelian
    have hcomm_u : ∀ g₁ g₂ : Γ ℚ, u g₁ * u g₂ = u g₂ * u g₁ := by
      haveI hcyc' : IsCyclic (Subgroup.map
          (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (Dickson.K 3))))
          u.range) := hrange ▸ hcyc
      have hker : ((QuotientGroup.mk'
          (Subgroup.center (GL (Fin 2) (Dickson.K 3)))).subgroupMap
            u.range).ker ≤ Subgroup.center u.range := by
        rintro ⟨x, hx⟩ hmem
        have hx1 : QuotientGroup.mk' (Subgroup.center
            (GL (Fin 2) (Dickson.K 3))) x = 1 := congrArg Subtype.val hmem
        have hxc : x ∈ Subgroup.center (GL (Fin 2) (Dickson.K 3)) := by
          rwa [← QuotientGroup.ker_mk' (Subgroup.center
            (GL (Fin 2) (Dickson.K 3))), MonoidHom.mem_ker]
        exact Subgroup.mem_center_iff.mpr fun y => Subtype.ext
          ((Subgroup.mem_center_iff.mp hxc) y.1)
      haveI h := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        ((QuotientGroup.mk' (Subgroup.center
          (GL (Fin 2) (Dickson.K 3)))).subgroupMap u.range) hker
      intro g₁ g₂
      exact congrArg Subtype.val
        (h.is_comm.comm ⟨u g₁, MonoidHom.mem_range.mpr ⟨g₁, rfl⟩⟩
          ⟨u g₂, MonoidHom.mem_range.mpr ⟨g₂, rfl⟩⟩)
    -- the base-changed operators commute
    have hcomm : ∀ g₁ g₂ : Γ ℚ, σρ g₁ * σρ g₂ = σρ g₂ * σρ g₁ := by
      intro g₁ g₂
      have hmap : ∀ M N : Matrix (Fin 2) (Fin 2) (AlgebraicClosure k),
          M.map e = N.map e → M = N := by
        intro M N h
        ext i j
        exact e.injective (by
          have := congrFun (congrFun (congrArg Matrix.of.symm h) i) j
          exact this)
      have hval := congrArg (Units.val) (hcomm_u g₁ g₂)
      rw [Units.val_mul, Units.val_mul, hu, hu, ← Matrix.map_mul,
        ← Matrix.map_mul] at hval
      have hmat := hmap _ _ hval
      have hmul : ∀ gg₁ gg₂ : Γ ℚ, LinearMap.toMatrix b b (σρ gg₁) *
          LinearMap.toMatrix b b (σρ gg₂) =
          LinearMap.toMatrix b b (σρ gg₁ * σρ gg₂) :=
        fun gg₁ gg₂ => (LinearMap.toMatrix_comp b b b _ _).symm
      rw [hmul, hmul] at hmat
      exact (LinearMap.toMatrix b b).injective hmat
    -- each operator is a scalar
    haveI : Module.Finite L (L ⊗[k] V) := Module.Finite.base_change k L V
    have hfr2 : Module.finrank L (L ⊗[k] V) = 2 := by
      rw [Module.finrank_baseChange]
      exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
    haveI : Nontrivial (L ⊗[k] V) :=
      Module.nontrivial_of_finrank_pos (R := L) (by omega)
    obtain ⟨hnt, hsub⟩ := (Slop.OddRep.isIrreducible_iff_forall σρ).mp hirr
    have hscalar : ∀ g : Γ ℚ, ∃ μ : L, ∀ v : L ⊗[k] V, σρ g v = μ • v := by
      intro g
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (σρ g)
      have hEne : Module.End.eigenspace (σρ g) μ ≠ ⊥ := hμ
      have hEinv : ∀ h : Γ ℚ, ∀ w ∈ Module.End.eigenspace (σρ g) μ,
          σρ h w ∈ Module.End.eigenspace (σρ g) μ := by
        intro h w hw
        rw [Module.End.mem_eigenspace_iff] at hw ⊢
        have hc := congrFun (congrArg DFunLike.coe (hcomm g h)) w
        simp only [Module.End.mul_apply] at hc
        rw [hc, hw, map_smul]
      rcases hsub (Module.End.eigenspace (σρ g) μ) hEinv with hE | hE
      · exact absurd hE hEne
      · refine ⟨μ, fun v => ?_⟩
        have hv : v ∈ Module.End.eigenspace (σρ g) μ :=
          hE ▸ Submodule.mem_top
        rwa [Module.End.mem_eigenspace_iff] at hv
    -- a scalar action on a `2`-dimensional space has a stable line
    obtain ⟨v, hv⟩ := exists_ne (0 : L ⊗[k] V)
    have hWinv : ∀ g : Γ ℚ, ∀ w ∈ Submodule.span L {v},
        σρ g w ∈ Submodule.span L {v} := by
      intro g w hw
      obtain ⟨μ, hμ⟩ := hscalar g
      rw [hμ w]
      exact Submodule.smul_mem _ _ hw
    rcases hsub (Submodule.span L {v}) hWinv with hW | hW
    · exact hv ((Submodule.mem_bot L).mp
        (hW ▸ Submodule.mem_span_singleton_self v))
    · have h1 : Module.finrank L (Submodule.span L {v}) = 1 :=
        finrank_span_singleton hv
      rw [hW, finrank_top, hfr2] at h1
      omega
  · exact serre_elimination_noncyclic V hV hρ habs b e u hu π hπ hrest

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **No absolutely irreducible mod-3 hardly ramified representation**
(DERIVED 2026-07-18 from the Serre-elimination leaf and the vendored
Dickson classification): the base change of an absolutely irreducible
mod-3 representation to `𝔽̄₃` projectivizes to a homomorphism
`π : Γ ℚ →* PGL₂(𝔽̄₃)` with finite image (the action factors through
the finite monoid `End k V`); Dickson's classification
(`Dickson.classification_tame`/`classification_wild`, vendored PROVEN)
puts `π.range` in the eight-case list, and the elimination leaf
refutes every case. -/
theorem not_isAbsolutelyIrreducible {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ¬ Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) := by
  intro habs
  classical
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI h32 : Fact ((3 : ℕ) > 2) := ⟨by norm_num⟩
  haveI : Finite V := Module.finite_of_finite k
  -- `k` has characteristic `3`, so `𝔽̄₃` receives both `k̄` and `K 3`
  haveI hchark : CharP k 3 := charP_three_of_finite_padicIntThree_algebra
  letI : Algebra (ZMod 3) k := ZMod.algebra k 3
  haveI : Algebra.IsAlgebraic (ZMod 3) (AlgebraicClosure k) := by
    haveI : Algebra.IsAlgebraic (ZMod 3) k :=
      Algebra.IsAlgebraic.of_finite (ZMod 3) k
    exact Algebra.IsAlgebraic.trans (ZMod 3) k (AlgebraicClosure k)
  haveI : IsAlgClosure (ZMod 3) (AlgebraicClosure k) :=
    ⟨inferInstance, inferInstance⟩
  let e : AlgebraicClosure k ≃ₐ[ZMod 3] Dickson.K 3 :=
    IsAlgClosure.equiv (ZMod 3) (AlgebraicClosure k) (Dickson.K 3)
  -- the base-changed representation and its matrix form
  set L := AlgebraicClosure k
  set σρ : Representation L (Γ ℚ) (L ⊗[k] V) :=
    Slop.OddRep.baseChange L (MonoidHomClass.toMonoidHom ρ)
  haveI : Module.Finite L (L ⊗[k] V) := Module.Finite.base_change k L V
  have hfr2 : Module.finrank L (L ⊗[k] V) = 2 := by
    rw [Module.finrank_baseChange]
    exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  let b : Module.Basis (Fin 2) L (L ⊗[k] V) :=
    Module.finBasisOfFinrankEq L (L ⊗[k] V) hfr2
  -- the `GL₂(𝔽̄₃)`-valued matrix form of the action
  let u : Γ ℚ →* GL (Fin 2) (Dickson.K 3) :=
    (Units.map (RingHom.toMonoidHom
      (RingHom.mapMatrix (e : AlgebraicClosure k →+* Dickson.K 3)))).comp
      ((Units.mapEquiv
        (LinearMap.toMatrixAlgEquiv b).toMulEquiv).toMonoidHom.comp
        σρ.toHomUnits)
  have hu : ∀ g, ((u g : GL (Fin 2) (Dickson.K 3)) :
      Matrix (Fin 2) (Fin 2) (Dickson.K 3)) =
      (LinearMap.toMatrix b b (σρ g)).map e := by
    intro g
    rfl
  -- the projectivization
  let π : Γ ℚ →* Dickson.PGL 3 :=
    (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (Dickson.K 3)))).comp u
  have hπ : ∀ g, π g = QuotientGroup.mk (u g) := fun g => rfl
  -- the image is finite: the action factors through the finite `End k V`
  haveI hfin : Finite π.range := by
    haveI : Finite (Module.End k V) :=
      Finite.of_injective _ DFunLike.coe_injective
    -- `π g` depends on `g` only through `ρ g` (units with equal values
    -- are equal)
    have hdep : ∀ g₁ g₂ : Γ ℚ, (MonoidHomClass.toMonoidHom ρ) g₁ =
        (MonoidHomClass.toMonoidHom ρ) g₂ → π g₁ = π g₂ := by
      intro g₁ g₂ h12
      have huu : u g₁ = u g₂ := by
        apply Units.ext
        rw [hu, hu]
        show ((LinearMap.toMatrix b b
          (((MonoidHomClass.toMonoidHom ρ) g₁).baseChange L)).map e) =
          ((LinearMap.toMatrix b b
          (((MonoidHomClass.toMonoidHom ρ) g₂).baseChange L)).map e)
        rw [h12]
      rw [hπ, hπ, huu]
    let G' : Module.End k V → Dickson.PGL 3 := fun T =>
      if h : ∃ g, (MonoidHomClass.toMonoidHom ρ) g = T then π h.choose else 1
    have hπG : ∀ g, π g = G' ((MonoidHomClass.toMonoidHom ρ) g) := by
      intro g
      have hex : ∃ g', (MonoidHomClass.toMonoidHom ρ) g' =
          (MonoidHomClass.toMonoidHom ρ) g := ⟨g, rfl⟩
      show π g = dite _ _ _
      rw [dif_pos hex]
      exact (hdep _ _ hex.choose_spec).symm
    have hsub : Set.range π ⊆ Set.range G' := by
      rintro _ ⟨g, rfl⟩
      exact ⟨_, (hπG g).symm⟩
    exact ((Set.finite_range G').subset hsub).to_subtype
  -- Dickson's classification of the finite image, then the elimination
  refine serre_elimination V hV hρ habs b (e : AlgebraicClosure k ≃+* Dickson.K 3)
    u hu π hπ ?_
  by_cases hnt : Nontrivial π.range
  · by_cases hdvd : (3 : ℕ) ∣ Nat.card π.range
    · rcases Dickson.classification_wild 3 π.range hdvd with h | h | h | ⟨_, h⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rcases Dickson.classification_tame 3 π.range hdvd hnt with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · haveI : Subsingleton π.range := not_nontrivial_iff_subsingleton.mp hnt
    exact Or.inl ⟨⟨1, fun x => by
      rw [Subsingleton.elim x 1]; exact Subgroup.mem_zpowers 1⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Mod-3 reducibility** (DERIVED 2026-07-18 from the three leaves
above and the vendored `OddAbsIrred`): a mod-3 hardly ramified
representation has a `Γ ℚ`-stable proper nonzero submodule. If not, the
representation is irreducible; complex conjugation is an involution of
`1`-dimensional fixed space (its determinant is `χ₃(c) = -1` while its
square is `1`, and `2 ≠ 0` in `k` since `3 = 0`), so by
`OddRep.isIrreducible_iff_isAbsolutelyIrreducible` the representation
is absolutely irreducible — contradicting the Serre-elimination leaf
`not_isAbsolutelyIrreducible`. -/
theorem mod_three_reducible {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ W : Submodule k V, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g : Γ ℚ, W.map (ρ g) ≤ W := by
  by_contra hno
  push Not at hno
  -- the representation, as a mathlib `Representation`
  set ρ' : Representation k (Γ ℚ) V := MonoidHomClass.toMonoidHom ρ with hρ'
  -- `2 ≠ 0` in `k` (its characteristic is `3`)
  have h3 : (3 : k) = 0 := three_eq_zero_of_finite_padicIntThree_algebra
  have h2 : (2 : k) ≠ 0 := fun h => one_ne_zero (α := k) (by linear_combination h3 - h)
  -- `V` is nontrivial (rank `2`)
  haveI : Nontrivial V := by
    have : Module.finrank k V = 2 :=
      Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
    exact Module.nontrivial_of_finrank_pos (R := k) (by omega)
  -- irreducibility from the absence of stable submodules
  have hirr : ρ'.IsIrreducible := by
    rw [Slop.OddRep.isIrreducible_iff_forall]
    refine ⟨inferInstance, fun W hW => ?_⟩
    by_contra hWne
    push Not at hWne
    obtain ⟨g, hg⟩ := hno W hWne.1 hWne.2
    exact hg (Submodule.map_le_iff_le_comap.mpr fun v hv =>
      Submodule.mem_comap.mpr (hW g v hv))
  -- complex conjugation: an involution with determinant `-1`
  obtain ⟨c, hc2, hcχ⟩ := exists_conj_cyclotomicCharacter_three
  have hsq : ρ' c * ρ' c = 1 := by
    rw [hρ']
    show ρ c * ρ c = 1
    rw [← map_mul, hc2, map_one]
  have hdetc : LinearMap.det (ρ' c) = -1 := by
    have h := hρ.det c
    rw [GaloisRep.det_apply, hcχ, map_neg, map_one] at h
    exact h
  -- the fixed space of conjugation is a line
  have heig : Module.finrank k (Module.End.eigenspace (ρ' c) 1) = 1 :=
    finrank_eigenspace_one_of_involution hV hsq hdetc h2
  -- irreducible ⇒ absolutely irreducible ⇒ contradiction with Serre
  exact not_isAbsolutelyIrreducible V hV hρ
    ((OddRep.isIrreducible_iff_isAbsolutelyIrreducible ρ' heig).mp hirr)

/-- **No `3`-torsion in the units of a characteristic-`3` field**
(PROVEN 2026-07-23 — glue for the inertia-at-`3` leaves below): in a
field where `3 = 0`, a unit with `a³ = 1` is `1`, since
`X³ − 1 = (X − 1)³`. -/
lemma units_eq_one_of_pow_three_eq_one {k : Type*} [Field k]
    (h3k : (3 : k) = 0) (a : kˣ) (ha : a ^ 3 = 1) : a = 1 := by
  have hval : (a : k) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
  have hcube : ((a : k) - 1) ^ 3 = 0 := by
    have hexp : ((a : k) - 1) ^ 3 =
        (a : k) ^ 3 - 1 - 3 * ((a : k) ^ 2 - (a : k)) := by ring
    rw [hexp, hval, h3k]
    ring
  exact Units.ext (by
    rw [Units.val_one]
    exact sub_eq_zero.mp
      (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hcube))

set_option backward.isDefEq.respectTransparency false in
/-- **Openness of the kernel of a quotient character** (PROVEN
2026-07-23 — shared continuity bookkeeping for the two inertia-at-`3`
leaves below, the same argument as inside `mod_three_of_stable_line`):
the kernel of the quotient character of a proper stable submodule of a
continuous representation on a finite discrete module is open — it
contains the open kernel of the representation. -/
lemma isOpen_ker_of_quotCharacter {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : GaloisRep ℚ k V}
    (W₀ : Submodule k V) (hW₀top : W₀ ≠ ⊤)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v) :
    IsOpen (χ.ker : Set (Γ ℚ)) := by
  haveI hfinV : Finite V := Module.finite_of_finite k
  have htriv : ∀ g, ρ g = 1 → χ g = 1 := by
    intro g hg
    apply Units.ext
    rw [Units.val_one]
    refine quotCharacter_eq_one_of_sq_eq_zero (ρ g) ?_ W₀ hW₀top (hχ g)
    rw [hg, sub_self]
    exact zero_pow two_ne_zero
  let Kρ : Subgroup (Γ ℚ) :=
    { carrier := {g | ρ g = 1}
      one_mem' := map_one ρ
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) = 1
        rw [map_mul, ha, hb, mul_one]
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ = 1
        have h1 : ρ a⁻¹ * ρ a = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h1 }
  have hKρ_open : IsOpen (Kρ : Set (Γ ℚ)) :=
    isOpen_setOf_galoisRep_eq_one ρ hfinV
  have hker : Kρ ≤ χ.ker := fun g hg => MonoidHom.mem_ker.mpr (htriv g hg)
  exact Subgroup.isOpen_mono hker hKρ_open

set_option backward.isDefEq.respectTransparency false in
/-- **Level-one detection of the mod-3 cyclotomic character** (PROVEN
2026-07-23): through `algebraMap ℤ_[3] k` into a field of
characteristic `3`, the `3`-adic cyclotomic character of `g` becomes
`1` exactly when `g` fixes a (hence every) primitive cube root of
unity — the ring map sees only the level-one value `w ∈ {1, 2}` of
the character (`w = 0` is excluded since the character is a unit),
and `w` is detected on `ζ` by `cyclotomicCharacter.spec`. -/
lemma cyclotomicCharacter_algebraMap_eq_one_iff_fix {k : Type*} [Field k]
    [Algebra ℤ_[3] k] (h3k : (3 : k) = 0)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 3) (g : Γ ℚ) :
    algebraMap ℤ_[3] k ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
      g.toRingEquiv : ℤ_[3]ˣ) : ℤ_[3]) = 1 ↔ g ζ = ζ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set w : ℕ := ((PadicInt.toZModPow 1)
    ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) :
      ℤ_[3])).val with hwdef
  have hspec : g.toRingEquiv ζ = ζ ^ w :=
    cyclotomicCharacter.spec 3 (n := 1) g.toRingEquiv ζ
      (by rw [pow_one]; exact hζ.pow_eq_one)
  have hwlt : w < 3 := by
    have h := ZMod.val_lt ((PadicInt.toZModPow 1)
      ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) :
        ℤ_[3]))
    rw [hwdef]
    simpa using h
  have hcast : algebraMap ℤ_[3] k
      ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv : ℤ_[3]ˣ) :
        ℤ_[3]) = (w : k) := by
    have hker : ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv :
        ℤ_[3]ˣ) : ℤ_[3]) - ((w : ℕ) : ℤ_[3]) ∈
        RingHom.ker (PadicInt.toZModPow (p := 3) 1) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hwdef, ZMod.natCast_val,
        ZMod.cast_id, sub_self]
    rw [PadicInt.ker_toZModPow] at hker
    obtain ⟨t3, ht3⟩ := Ideal.mem_span_singleton'.mp hker
    have hu : ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv :
        ℤ_[3]ˣ) : ℤ_[3]) = ((w : ℕ) : ℤ_[3]) + t3 * ((3 : ℕ) : ℤ_[3]) ^ 1 := by
      linear_combination -ht3
    rw [hu, map_add, map_natCast, map_mul, map_pow, map_natCast]
    rw [show ((3 : ℕ) : k) = 0 by exact_mod_cast h3k]
    ring
  constructor
  · intro halg
    rw [hcast] at halg
    have hw1 : w = 1 := by
      have h012 : w = 0 ∨ w = 1 ∨ w = 2 := by omega
      rcases h012 with h | h | h
      · exfalso
        rw [h] at halg
        exact one_ne_zero (α := k) (by exact_mod_cast halg.symm)
      · exact h
      · exfalso
        rw [h] at halg
        refine one_ne_zero (α := k) ?_
        have h2 : (2 : k) = 1 := by exact_mod_cast halg
        linear_combination h2
    have hfix : g.toRingEquiv ζ = ζ := by
      rw [hspec, hw1, pow_one]
    exact hfix
  · intro hfix
    have hw1 : w = 1 := by
      refine hζ.pow_inj hwlt (by norm_num) ?_
      rw [← hspec, pow_one]
      exact hfix
    rw [hcast, hw1]
    norm_num

/-- **The tame generator of the inertia image at `3`** (sorry node,
isolated 2026-07-23 — the SINGLE local-structure input to both
`quotCharacter_inertia_three_sq_one` and
`quotCharacter_inertia_three_dichotomy_of_sq_one`, whose assemblies
are proven): for a character `χ` of `Γ ℚ` with open kernel, valued in
a commutative group without `3`-torsion, the image under
`χ ∘ (Γ ℚ₃ᵥ → Γ ℚ)` of the local inertia at `3` is generated by a
single element whose square is `1`. Intended proof (Serre, *Local
Fields* IV; equivalently local CFT, `I₃ᵃᵇ ≅ ℤ₃ˣ` with prime-to-`3`
quotient `𝔽₃ˣ = {±1}`): the open kernel cuts out a finite Galois
level at which the image of the full local inertia is the
finite-level inertia group `I` (the compactness lifting
`exists_mem_localInertiaGroup_restrictNormalHom_eq` of
`LocalInertiaFixedField` gives the lifting direction); the wild part
`P ⊴ I` is a `3`-group, killed by `χ` (`h3`: no `3`-torsion in the
target); the tame quotient `I/P` is cyclic, so the image of `I` is
generated by the image `a` of a tame generator `t`; and Frobenius
conjugation `φtφ⁻¹ ≡ t³ (mod P)` forces `a³ = χ(φtφ⁻¹) = a` — `χ` is
defined on ALL of `Γ ℚ` with abelian values, so conjugation acts
trivially on it — i.e. `a² = 1`. -/
theorem exists_localInertia_three_generator {A : Type*} [CommGroup A]
    (h3 : ∀ a : A, a ^ 3 = 1 → a = 1)
    (χ : Γ ℚ →* A) (hopen : IsOpen (χ.ker : Set (Γ ℚ))) :
    ∃ t ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) t)) ^ 2 = 1 ∧
      ∀ σ ∈ localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
        ∃ m : ℕ, χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) =
          (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) t)) ^ m := by
  sorry

/-- **`ℚ₃ᵥ` contains no cube root of unity besides `1`** (PROVEN
2026-07-23 — the no-root input to the finite-level leaf below): the
polynomial `X² + X + 1` has no root in the `3`-adic completion. A
root `r` gives `x = 2r + 1` with `x² = −3`; `x` is integral over the
(integrally closed) valuation ring `𝒪ᵥ`, so `x ∈ 𝒪ᵥ`; then
`x² ∈ 𝔪ᵥ = (3)` (`maximalIdeal_adicCompletionIntegers_eq_span`)
forces `x = 3y` by primality, whence `3y² = −1` puts the unit `−1`
in the maximal ideal — absurd. -/
theorem no_root_sq_add_self_add_one_adicCompletion_three
    (r : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) :
    r ^ 2 + r + 1 ≠ 0 := by
  intro hroot
  have hx2 : (2 * r + 1) ^ 2 = -3 := by linear_combination 4 * hroot
  -- `2r + 1` is integral over the valuation ring, hence in it
  have hxint : IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) (2 * r + 1) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C 3,
      Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_ofNat]
    linear_combination hx2
  obtain ⟨X, hX⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxint
  -- the valuation-ring-level equation `X² = −3`
  have hX2 : X ^ 2 = -3 := by
    apply IsFractionRing.injective
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
    rw [map_pow, hX, map_neg, map_ofNat]
    exact hx2
  -- descend along `𝔪ᵥ = (3)`
  have hspan := maximalIdeal_adicCompletionIntegers_eq_span Nat.prime_three
  have hXm : X ∈ IsLocalRing.maximalIdeal
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) := by
    have hsq : X ^ 2 ∈ IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) := by
      rw [hspan, Ideal.mem_span_singleton]
      exact ⟨-1, by rw [hX2]; push_cast; ring⟩
    exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_of_pow_mem _ hsq
  rw [hspan, Ideal.mem_span_singleton] at hXm
  obtain ⟨Y, hY⟩ := hXm
  have h3ne : ((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) h
    rw [map_natCast, map_zero] at h2
    norm_num at h2
  have h3Y : 3 * Y ^ 2 = -1 := by
    have h9 : ((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) * (3 * Y ^ 2) =
        ((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) * (-1) := by
      have h4 := hX2
      rw [hY] at h4
      push_cast at h4 ⊢
      linear_combination h4
    exact mul_left_cancel₀ h3ne h9
  -- the unit `−1` cannot lie in the maximal ideal
  have hunit : (-1 : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ∈
      IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) := by
    rw [hspan, Ideal.mem_span_singleton]
    exact ⟨Y ^ 2, by push_cast; linear_combination -h3Y⟩
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hunit isUnit_one.neg)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The ramified quadratic extension `ℚ₃ᵥ(ζ₃)` at finite level**
(sorry node, isolated 2026-07-23 — the finite-level content of the
ramification witness below; everything profinite is already assembled
on top of it): there are a finite Galois subextension `N` of the
algebraic closure of the `3`-adic completion, a primitive cube root
`ζ ∈ N`, and an automorphism `τ` of `N` with `τ ζ = ζ²` lying in the
finite-level inertia (trivial action modulo the maximal ideal of the
integral closure of `𝒪ᵥ` in `N`). Intended proof: `ζ ∉ ℚ₃ᵥ` — else
`x = 2ζ + 1 ∈ ℚ₃ᵥ` has `x² = −3`, and `𝔪ᵥ = (3)`
(`maximalIdeal_adicCompletionIntegers_eq_span`) gives `x ∈ 𝒪ᵥ`
(integrally closed), `x ∈ 𝔪ᵥ`, `x = 3y`, `3y² = −1`, so `−1 ∈ 𝔪ᵥ`,
absurd — hence `N := ℚ₃ᵥ⟮ζ⟯` is quadratic (minpoly `X² + X + 1`,
irreducible as a rootless quadratic) and Galois (both roots `ζ, ζ²`
lie in `N`); its automorphism group is `{1, τ}` with `τ ζ = ζ²`
(`IsGalois.card_aut_eq_finrank`); and `τ` is inertial: for integral
`y` with `s = τ y − y` one has `τ s = −s`, so `s²` and `s·(2ζ+1)` are
Galois-invariant integral elements of `ℚ₃ᵥ`, hence in `𝒪ᵥ`, with
`(s·(2ζ+1))² = −3 s²`; primality of `𝔪ᵥ = (3)` then forces
`s² ∈ 3𝒪ᵥ ⊆ 𝔪(IntegralClosure)`, and `s ∈ 𝔪` since the maximal
ideal of the (local) integral closure is prime — the local analogue
of the proven `mem_inertia_of_dvd_squarefree`. -/
theorem exists_finite_level_inertia_swap_three :
    ∃ (N : IntermediateField
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)))
      (τ : N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] N)
      (ζ : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
      (hζN : ζ ∈ N),
      FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) N ∧
      IsGalois (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) N ∧
      IsPrimitiveRoot ζ 3 ∧
      ((τ ⟨ζ, hζN⟩ : N) : AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) = ζ ^ 2 ∧
      τ ∈ (IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) N)).inertia
        (N ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat] N) := by
  classical
  -- a primitive cube root of the local closure
  obtain ⟨ζQ, hζQ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure ℚ) 3
  set ζ : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) :=
    AlgebraicClosure.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) ζQ with hζdef
  have hζprim : IsPrimitiveRoot ζ 3 :=
    hζQ.map_of_injective (RingHom.injective _)
  have hζrel : ζ ^ 2 + ζ + 1 = 0 := by
    have h := hζprim.geom_sum_eq_zero (by norm_num)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, pow_zero, pow_one] at h
    linear_combination h
  -- the quadratic `X² + X + 1` over the completion
  set p : Polynomial (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) :=
    Polynomial.X ^ 2 + Polynomial.X + 1 with hpdef
  have hpmonic : p.Monic := by rw [hpdef]; monicity!
  have hpnat : p.natDegree = 2 := by rw [hpdef]; compute_degree!
  have hζaeval : Polynomial.aeval ζ p = 0 := by
    rw [hpdef]
    simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
    exact hζrel
  have hζint : IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ζ :=
    ⟨p, hpmonic, by rwa [← Polynomial.aeval_def]⟩
  have hpirr : Irreducible p := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [hpnat]; decide
    · intro x hx
      have hx0 : x ^ 2 + x + 1 = 0 := by
        have h := hx
        rw [hpdef] at h
        simpa [Polynomial.IsRoot] using h
      exact no_root_sq_add_self_add_one_adicCompletion_three x hx0
  have hmin : minpoly (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ζ = p :=
    (minpoly.eq_of_irreducible_of_monic hpirr hζaeval hpmonic).symm
  -- the quadratic extension `N = ℚ₃ᵥ(ζ)`
  haveI hfd : FiniteDimensional (IsDedekindDomain.HeightOneSpectrum.adicCompletion
      ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hζint
  have hfr2 : Module.finrank (IsDedekindDomain.HeightOneSpectrum.adicCompletion
      ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) = 2 := by
    rw [IntermediateField.adjoin.finrank hζint, hmin, hpnat]
  set A := IntermediateField.AdjoinSimple.gen
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ζ with hAdef
  have hAcoe : (algebraMap _ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))) A = ζ :=
    IntermediateField.AdjoinSimple.algebraMap_gen _ _
  have hArel : A ^ 2 + A + 1 = 0 := by
    apply RingHom.injective (algebraMap _ (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)))
    rw [map_add, map_add, map_pow, map_one, map_zero, hAcoe]
    exact hζrel
  have hAaeval : Polynomial.aeval A p = 0 := by
    rw [hpdef]
    simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
    exact hArel
  -- `p` splits in `N` with roots `A` and `B = −1 − A`
  set B := -1 - A with hBdef
  have hCA : (Polynomial.C A) ^ 2 + Polynomial.C A + 1 = 0 := by
    have h := congrArg Polynomial.C hArel
    rw [map_add, map_add, map_pow, map_one, map_zero] at h
    exact h
  have hfac : p.map (algebraMap _ _) =
      (Polynomial.X - Polynomial.C A) * (Polynomial.X - Polynomial.C B) := by
    have hCB : Polynomial.C B = -1 - Polynomial.C A := by
      rw [hBdef, map_sub, map_neg, map_one]
    rw [hpdef, Polynomial.map_add, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, hCB]
    linear_combination hCA
  have hsplits : (p.map (algebraMap
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}))).Splits := by
    rw [hfac]
    exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)
  have hgenroot : A ∈ p.rootSet
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hpmonic.ne_zero, hAaeval⟩
  have hadj : Algebra.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
      ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (p.rootSet (IntermediateField.adjoin
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) = ⊤ := by
    rw [eq_top_iff, ← PowerBasis.adjoin_gen_eq_top
      (IntermediateField.adjoin.powerBasis hζint)]
    refine Algebra.adjoin_mono ?_
    rw [IntermediateField.adjoin.powerBasis_gen, Set.singleton_subset_iff]
    exact hgenroot
  haveI hsf : Polynomial.IsSplittingField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) p :=
    ⟨hsplits, hadj⟩
  haveI hnorm : Normal (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) :=
    Normal.of_isSplittingField p
  haveI hsep : Algebra.IsSeparable
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hgal : IsGalois (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) := ⟨⟩
  -- the automorphism group has exactly two elements
  have hcard : Nat.card ((IntermediateField.adjoin
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat]
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) = 2 :=
    (IsGalois.card_aut_eq_finrank _ _).trans hfr2
  haveI : Finite ((IntermediateField.adjoin
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat]
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) :=
    Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial ((IntermediateField.adjoin
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat]
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨τ, hτne⟩ := exists_ne (1 : (IntermediateField.adjoin
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) ≃ₐ[
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat]
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}))
  have hτ2 : τ * τ = 1 := by
    have h : τ ^ Nat.card _ = 1 := pow_card_eq_one'
    rwa [hcard, pow_two] at h
  have huniv : ∀ g, g = 1 ∨ g = τ := by
    intro g
    by_contra hg
    push Not at hg
    have h1 : ({1, τ, g} : Finset _).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨fun h => hτne h.symm, fun h => hg.1 h.symm⟩)]
      rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact fun h => hg.2 h.symm)]
      rw [Finset.card_singleton]
    have h3 := Finset.card_le_card
      (Finset.subset_univ ({1, τ, g} : Finset _))
    rw [h1, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at h3
    omega
  have hσσ : ∀ z, τ (τ z) = z := by
    intro z
    have h := congrArg (fun g => g z) hτ2
    simpa [AlgEquiv.mul_apply] using h
  -- `τ` swaps the two roots
  have hτA : τ A = B := by
    have h0 : Polynomial.aeval (τ A) p = 0 := by
      rw [Polynomial.aeval_algHom_apply τ A p, hAaeval, map_zero]
    have h1 : Polynomial.eval (τ A) (p.map (algebraMap _ _)) = 0 := by
      rw [Polynomial.eval_map, ← Polynomial.aeval_def]
      exact h0
    rw [hfac] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exfalso
      apply hτne
      have hAA : τ A = A := sub_eq_zero.mp h
      have hext : τ.toAlgHom = AlgHom.id _ _ := by
        refine PowerBasis.algHom_ext (IntermediateField.adjoin.powerBasis hζint) ?_
        rw [IntermediateField.adjoin.powerBasis_gen]
        simpa using hAA
      refine AlgEquiv.ext fun z => ?_
      have hz := DFunLike.congr_fun hext z
      simpa using hz
    · exact sub_eq_zero.mp h
  -- membership and value of the coerced image
  have hζmem : ζ ∈ IntermediateField.adjoin
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ} :=
    IntermediateField.mem_adjoin_simple_self _ ζ
  have hτζcoe : ((τ ⟨ζ, hζmem⟩ : (IntermediateField.adjoin
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) :
      AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) = ζ ^ 2 := by
    have hcoeB : ((B : (IntermediateField.adjoin
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) :
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) = -1 - ζ := by
      rw [hBdef]
      push_cast
      rw [show ((A : (IntermediateField.adjoin
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) :
          AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) = ζ from hAcoe]
    have hτA' : τ ⟨ζ, hζmem⟩ = B := hτA
    rw [hτA', hcoeB]
    linear_combination -hζrel
  -- `τ` lies in the finite-level inertia
  have hspan := maximalIdeal_adicCompletionIntegers_eq_span Nat.prime_three
  have hτin : τ ∈ (IsLocalRing.maximalIdeal (IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}))).inertia
      _ := by
    rw [show (IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IntermediateField.adjoin
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}))).inertia _ =
      (IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IntermediateField.adjoin
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
          {ζ}))).toAddSubgroup.inertia _ from rfl, AddSubgroup.mem_inertia]
    intro y
    rw [Submodule.mem_toAddSubgroup]
    -- the anti-invariant difference
    set s := τ y.1 - y.1 with hsdef
    have hτs : τ s = -s := by
      rw [hsdef, map_sub, hσσ]
      ring
    have hyint : IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) y.1 := y.2
    have hsint : IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) s := by
      rw [hsdef]
      exact (hyint.map (τ.toAlgHom.restrictScalars
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).sub hyint
    -- the anti-invariant scaled root
    set x := 2 * A + 1 with hxdef
    have hx2 : x ^ 2 = -3 := by
      rw [hxdef]
      linear_combination 4 * hArel
    have hτx : τ x = -x := by
      rw [hxdef, map_add, map_mul, hτA, hBdef, map_one, map_ofNat]
      ring
    have hxint : IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) x := by
      refine ⟨Polynomial.X ^ 2 + Polynomial.C 3,
        Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
      rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, map_ofNat]
      rw [hx2]
      ring
    -- `s²` and `s·x` are Galois-invariant, hence in the base
    obtain ⟨r2, hr2⟩ := Algebra.IsInvariant.isInvariant
      (A := IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (s ^ 2) (by
        intro g
        rcases huniv g with hg | hg
        · rw [hg]
          exact one_smul _ _
        · rw [hg]
          show τ (s ^ 2) = s ^ 2
          rw [map_pow, hτs]
          ring)
    obtain ⟨r1, hr1⟩ := Algebra.IsInvariant.isInvariant
      (A := IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      (s * x) (by
        intro g
        rcases huniv g with hg | hg
        · rw [hg]
          exact one_smul _ _
        · rw [hg]
          show τ (s * x) = s * x
          rw [map_mul, hτs, hτx]
          ring)
    -- descend to the valuation ring
    have hr2int : IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) r2 := by
      rw [← isIntegral_algebraMap_iff (algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IntermediateField.adjoin
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})).injective,
        hr2]
      exact hsint.pow 2
    have hr1int : IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) r1 := by
      rw [← isIntegral_algebraMap_iff (algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IntermediateField.adjoin
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})).injective,
        hr1]
      exact hsint.mul hxint
    obtain ⟨S2, hS2⟩ := IsIntegrallyClosed.isIntegral_iff.mp hr2int
    obtain ⟨M, hM⟩ := IsIntegrallyClosed.isIntegral_iff.mp hr1int
    -- the norm relation `M² = −3·S2` in the valuation ring
    have hMS : M ^ 2 = -(3 * S2) := by
      apply IsFractionRing.injective
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
      apply RingHom.injective (algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
          ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}))
      rw [map_pow, map_pow, hM, hr1, map_neg, map_neg, map_mul, map_mul,
        map_ofNat, map_ofNat, hS2, hr2]
      have hexp : (s * x) ^ 2 = s ^ 2 * x ^ 2 := by ring
      rw [hexp, hx2]
      ring
    -- primality of `𝔪ᵥ = (3)` gives `S2 ∈ 3𝒪ᵥ`
    have hMm : M ∈ IsLocalRing.maximalIdeal
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) := by
      have hsq : M ^ 2 ∈ IsLocalRing.maximalIdeal
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) := by
        rw [hspan, Ideal.mem_span_singleton]
        exact ⟨-S2, by rw [hMS]; push_cast; ring⟩
      exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_of_pow_mem _ hsq
    rw [hspan, Ideal.mem_span_singleton] at hMm
    obtain ⟨M', hM'⟩ := hMm
    have h3ne : ((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
        ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ≠ 0 := by
      intro h
      have h2 := congrArg (algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) h
      rw [map_natCast, map_zero] at h2
      norm_num at h2
    have hS2eq : S2 = -(3 * M' ^ 2) := by
      have h9 : ((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
          ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) * S2 =
          ((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
            ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) *
            -(3 * M' ^ 2) := by
        have h4 := hMS
        rw [hM'] at h4
        push_cast at h4 ⊢
        linear_combination h4
      exact mul_left_cancel₀ h3ne h9
    -- `3` lies in the maximal ideal of the integral closure
    have h3mem : ((3 : ℕ) : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
          ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) ∈
        IsLocalRing.maximalIdeal _ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu1⟩ := hu.exists_right_inv
      have huN : ((3 : ℕ) : (IntermediateField.adjoin
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) *
          u.1 = 1 := by
        exact congrArg (fun z : IntegralClosure _ _ => z.1) hu1
      have hval : u.1 =
          algebraMap _ _ (((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletion
            ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)⁻¹) := by
        have h3N : ((3 : ℕ) : (IntermediateField.adjoin
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) =
            algebraMap _ _ ((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletion
              ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) := by
          rw [map_natCast]
        have h3ne' : ((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletion
            ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ≠ 0 := by
          norm_num
        have h3Nne : ((3 : ℕ) : (IntermediateField.adjoin
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) ≠ 0 := by
          intro h0
          rw [h3N] at h0
          apply h3ne'
          apply RingHom.injective (algebraMap
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
            (IntermediateField.adjoin
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}))
          rw [h0, map_zero]
        have hcalc : ((3 : ℕ) : (IntermediateField.adjoin
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) * u.1 =
            ((3 : ℕ) : (IntermediateField.adjoin
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) *
            algebraMap _ _ (((3 : ℕ) :
              IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
                Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)⁻¹) := by
          rw [huN, h3N, ← map_mul, mul_inv_cancel₀ h3ne', map_one]
        exact mul_left_cancel₀ h3Nne hcalc
      have huint : IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
          ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
          (((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletion
            ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)⁻¹) := by
        rw [← isIntegral_algebraMap_iff (algebraMap
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
          (IntermediateField.adjoin
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})).injective,
          ← hval]
        exact u.2
      obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp huint
      have h3w : ((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
          ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) * w = 1 := by
        apply IsFractionRing.injective
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        rw [map_mul, map_natCast, hw, map_one]
        rw [mul_inv_cancel₀]
        norm_num
      have h3span : ((3 : ℕ) : IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
          ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) ∈
          IsLocalRing.maximalIdeal
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) := by
        rw [hspan]
        exact Ideal.mem_span_singleton_self _
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h3span
          (isUnit_iff_exists.mpr ⟨w, h3w, (mul_comm w _).trans h3w⟩))
    -- assemble: `(τ•y − y)² = 3 · c` in the integral closure
    have hT2 : (τ • y - y) * (τ • y - y) =
        ((3 : ℕ) : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
          (IntermediateField.adjoin
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) *
        (-(algebraMap _ _ M') ^ 2) := by
      apply Subtype.ext
      have h1 : (τ • y - y).1 = τ • y.1 - y.1 := by
        rw [show (τ • y - y).1 = (τ • y).1 - y.1 from rfl,
          IntegralClosure.coe_smul]
      have hlhs : ((τ • y - y) * (τ • y - y)).1 = s * s := by
        rw [show ((τ • y - y) * (τ • y - y)).1 =
          (τ • y - y).1 * (τ • y - y).1 from rfl, h1, hsdef]
        rfl
      rw [hlhs]
      show s * s = ((3 : ℕ) : (IntermediateField.adjoin
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) *
        (-(algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
          (IntermediateField.adjoin
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) M') ^ 2)
      -- `s² = −3·(M')²` in `N`, from `S2 = −3 M'²`
      have hs2 : s * s = algebraMap _ (IntermediateField.adjoin
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}) r2 := by
        rw [hr2]
        ring
      rw [hs2, ← hS2, ← IsScalarTower.algebraMap_apply
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
          ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}), hS2eq,
        map_neg, map_mul, map_ofNat, map_pow]
      push_cast
      ring
    have hmul : (τ • y - y) * (τ • y - y) ∈ IsLocalRing.maximalIdeal
        (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
          ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)
        (IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
          ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ})) := by
      rw [hT2]
      exact Ideal.mul_mem_right _ _ h3mem
    rcases (IsLocalRing.maximalIdeal.isMaximal _).isPrime.mem_or_mem hmul
      with h | h <;> exact h
  exact ⟨IntermediateField.adjoin (IsDedekindDomain.HeightOneSpectrum.adicCompletion
      ℚ Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) {ζ}, τ, ζ, hζmem,
    hfd, hgal, hζprim, hτζcoe, hτin⟩

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
/-- **The inertia at `3` moves the cube roots of unity** (DECOMPOSED
2026-07-23 into the finite-level leaf
`exists_finite_level_inertia_swap_three` above; the profinite
assembly is proven): some element of the local inertia group at `3`
fixes no primitive cube root of unity — `3` ramifies in
`ℚ(ζ₃) = ℚ(√−3)`, and this witness realizes the nontrivial quadratic
character of the tame inertia at `3` as the mod-3 cyclotomic
character. Assembly: the compactness lifting
`exists_mem_localInertiaGroup_restrictNormalHom_eq` produces
`σ ∈ localInertiaGroup` restricting on `N = ℚ₃ᵥ(ζ₃)` to the
finite-level inertia automorphism `τ` with `τ ζ = ζ²`; any primitive
cube root of `ℚᵃˡᵍ` embeds (by
`Field.absoluteGaloisGroup.lift_map`) onto `ζ` or `ζ²` in the local
closure, and `σ` moves both (`σ ζ = ζ²` by
`AlgEquiv.restrictNormal_commutes`, hence `σ ζ² = ζ⁴ = ζ`). -/
theorem exists_localInertia_three_not_fix_primitiveRoot :
    ∃ σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ 3 →
        Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ ζ ≠ ζ := by
  classical
  obtain ⟨N, τ, ζc, hζN, hfd, hgal, hζcprim, hτζ, hτin⟩ :=
    exists_finite_level_inertia_swap_three
  haveI := hfd
  haveI := hgal
  obtain ⟨σ, hσmem, hσres⟩ :=
    exists_mem_localInertiaGroup_restrictNormalHom_eq
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat N τ hτin
  refine ⟨σ, hσmem, ?_⟩
  intro ζ hζ hfix
  -- transport the fixed point through the closure embedding
  set ι := AlgebraicClosure.map (algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) with hιdef
  have hσι : σ (ι ζ) = ι ζ := by
    rw [← Field.absoluteGaloisGroup.lift_map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ ζ, hfix]
  -- `σ` sends `ζc` to `ζc²` (restriction to `N` is `τ`)
  have hσζc : σ ζc = ζc ^ 2 := by
    have hcomm := AlgEquiv.restrictNormal_commutes σ N ⟨ζc, hζN⟩
    rw [show σ.restrictNormal N = τ from hσres] at hcomm
    rw [show (algebraMap N (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)))
        (⟨ζc, hζN⟩ : N) = ζc from rfl] at hcomm
    rw [← hcomm]
    exact hτζ
  -- the embedded root is `ζc` or `ζc²`, and `σ` moves both
  have hιζ3 : (ι ζ) ^ 3 = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨i, hi3, hiζ⟩ := hζcprim.eq_pow_of_pow_eq_one hιζ3
  have hιprim : IsPrimitiveRoot (ι ζ) 3 :=
    hζ.map_of_injective (RingHom.injective ι)
  interval_cases i
  · -- `ι ζ = 1` contradicts primitivity
    rw [pow_zero] at hiζ
    exact hιprim.ne_one (by norm_num) hiζ.symm
  · -- `ι ζ = ζc`, but `σ ζc = ζc² ≠ ζc`
    rw [pow_one] at hiζ
    rw [← hiζ, hσζc] at hσι
    have h21 : (2 : ℕ) = 1 :=
      hζcprim.pow_inj (by norm_num) (by norm_num)
        (by rw [pow_one]; exact hσι)
    exact absurd h21 (by norm_num)
  · -- `ι ζ = ζc²`, but `σ ζc² = ζc⁴ = ζc ≠ ζc²`
    rw [← hiζ] at hσι
    rw [map_pow, hσζc, ← pow_mul] at hσι
    have hζc4 : ζc ^ (2 * 2) = ζc ^ 1 := by
      have h34 : ζc ^ (2 * 2) = ζc ^ 3 * ζc ^ 1 := by ring
      rw [h34, hζcprim.pow_eq_one, one_mul]
    rw [hζc4] at hσι
    exact absurd (hζcprim.pow_inj (by norm_num) (by norm_num) hσι)
      (by norm_num)

/-- **Order two on the inertia at `3`** (DECOMPOSED 2026-07-23 into
the tame-generator leaf `exists_localInertia_three_generator` above;
the assembly is proven — kernel openness is
`isOpen_ker_of_quotCharacter`, `3`-torsion-freeness of `kˣ` is
`units_eq_one_of_pow_three_eq_one`, and any power of the square-one
generator has square one): the
quotient character `χ` of a stable line of a mod-3 hardly ramified
representation SQUARES TO `1` on the inertia at `3` (no flatness
needed — pure local structure, recorded in the leaf's docstring). -/
theorem quotCharacter_inertia_three_sq_one
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (_hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (_hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (_hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v) :
    ∀ g ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) g)) ^ 2 = 1 := by
  intro g hg
  have hfr : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  have hW₀top : W₀ ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, hfr] at hW₀fr
    omega
  have hopen : IsOpen (χ.ker : Set (Γ ℚ)) :=
    isOpen_ker_of_quotCharacter W₀ hW₀top χ hχ
  have h3k : (3 : k) = 0 := three_eq_zero_of_finite_padicIntThree_algebra
  obtain ⟨t, -, htsq, hgen⟩ := exists_localInertia_three_generator
    (units_eq_one_of_pow_three_eq_one h3k) χ hopen
  obtain ⟨m, hm⟩ := hgen g hg
  rw [hm, ← pow_mul, mul_comm m 2, pow_mul, htsq, one_pow]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The unique quadratic quotient of the inertia at `3`**
(DECOMPOSED 2026-07-23 into the tame-generator leaf
`exists_localInertia_three_generator` and the ramification witness
`exists_localInertia_three_not_fix_primitiveRoot` above; the assembly
is proven): a quotient character `χ` of a stable line of a mod-3
hardly ramified representation whose square is trivial on the inertia
at `3` is, on that inertia, either TRIVIAL or the mod-3 CYCLOTOMIC
character. Assembly: apply the generator leaf to the PAIR character
`χ × ε` into `kˣ × kˣ` (`ε` = mod-3 cyclotomic; kernel openness from
`isOpen_ker_of_quotCharacter` and the finite level `ℚ(ζ₃)`); on the
inertia every value `(χσ, εσ)` is a power `(a, b)^m` of the single
generator value; `a² = b² = 1` with values `±1`, `b ≠ 1` by the
ramification witness (via
`cyclotomicCharacter_algebraMap_eq_one_iff_fix`); so either `a = 1`
(`χ` trivial on inertia) or `a = b = −1`, and then
`χσ = (−1)^m = εσ` on all of the inertia. -/
theorem quotCharacter_inertia_three_dichotomy_of_sq_one
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (_hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (_hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (_hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (hsq : ∀ g ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) g)) ^ 2 = 1) :
    (localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) ∨
    (∀ g ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      ((χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) g) : k)) =
        algebraMap ℤ_[3] k (cyclotomicCharacter (AlgebraicClosure ℚ) 3
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
                g).toRingEquiv))) := by
  classical
  set Emb := Field.absoluteGaloisGroup.map (algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
  have h3k : (3 : k) = 0 := three_eq_zero_of_finite_padicIntThree_algebra
  -- the mod-3 cyclotomic character as a `kˣ`-valued character
  set ε : Γ ℚ →* kˣ := MonoidHom.mk'
    (fun g => Units.map (algebraMap ℤ_[3] k).toMonoidHom
      (cyclotomicCharacter (AlgebraicClosure ℚ) 3 g.toRingEquiv))
    (fun a b => by
      have hab : (a * b).toRingEquiv = a.toRingEquiv * b.toRingEquiv :=
        RingEquiv.ext fun x => rfl
      rw [hab, map_mul, map_mul])
  have hεval : ∀ g : Γ ℚ, ((ε g : kˣ) : k) =
      algebraMap ℤ_[3] k ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
        g.toRingEquiv : ℤ_[3]ˣ) : ℤ_[3]) := fun g => rfl
  -- openness of the kernel of the pair character
  have hfr : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  have hW₀top : W₀ ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, hfr] at hW₀fr
    omega
  have hχopen : IsOpen (χ.ker : Set (Γ ℚ)) :=
    isOpen_ker_of_quotCharacter W₀ hW₀top χ hχ
  haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  haveI hacQ : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, halgQ⟩
  haveI hnormQ : Normal ℚ (AlgebraicClosure ℚ) :=
    IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI hsepQ : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hgalQ : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.isIntegral
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure ℚ) 3
  have hζint : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hζint
  have hfixopen : IsOpen
      ((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Set (Γ ℚ)) :=
    (InfiniteGalois.isOpen_iff_finite (IntermediateField.adjoin ℚ {ζ})).mpr
      inferInstance
  have hεker : (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup ≤ ε.ker := by
    intro g hg
    have hgζ : g ζ = ζ := by
      rw [IntermediateField.mem_fixingSubgroup_iff] at hg
      exact hg ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [Units.val_one, hεval g]
    exact (cyclotomicCharacter_algebraMap_eq_one_iff_fix h3k hζ g).mpr hgζ
  have hpairopen : IsOpen ((χ.prod ε).ker : Set (Γ ℚ)) := by
    have hle : χ.ker ⊓ (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup ≤
        (χ.prod ε).ker := by
      intro g hg
      obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
      rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one]
      exact ⟨MonoidHom.mem_ker.mp hg1, MonoidHom.mem_ker.mp (hεker hg2)⟩
    refine Subgroup.isOpen_mono hle ?_
    rw [Subgroup.coe_inf]
    exact hχopen.inter hfixopen
  -- no 3-torsion in `kˣ × kˣ`
  have h3t : ∀ a : kˣ × kˣ, a ^ 3 = 1 → a = 1 := by
    intro a ha
    have h1 : a.1 ^ 3 = 1 := congrArg Prod.fst ha
    have h2 : a.2 ^ 3 = 1 := congrArg Prod.snd ha
    exact Prod.ext (units_eq_one_of_pow_three_eq_one h3k a.1 h1)
      (units_eq_one_of_pow_three_eq_one h3k a.2 h2)
  -- the generator of the inertia image at `3`
  obtain ⟨t, ht, -, hgen⟩ := exists_localInertia_three_generator h3t
    (χ.prod ε) hpairopen
  by_cases ha1 : χ (Emb t) = 1
  · -- `χ` is trivial on the inertia at `3`
    refine Or.inl ?_
    intro σ hσ
    rw [MonoidHom.mem_ker]
    obtain ⟨m, hm⟩ := hgen σ hσ
    have hfst : χ (Emb σ) = χ (Emb t) ^ m := congrArg Prod.fst hm
    show χ (Emb σ) = 1
    rw [hfst, ha1, one_pow]
  · -- `χ` agrees with the mod-3 cyclotomic character on the inertia
    refine Or.inr ?_
    obtain ⟨σ₀, hσ₀, hσ₀fix⟩ := exists_localInertia_three_not_fix_primitiveRoot
    have hεσ₀ : ε (Emb σ₀) ≠ 1 := by
      intro h1
      refine hσ₀fix ζ hζ ?_
      refine (cyclotomicCharacter_algebraMap_eq_one_iff_fix h3k hζ
        (Emb σ₀)).mp ?_
      rw [← hεval (Emb σ₀)]
      exact congrArg Units.val h1
    -- the `χ`-component of the generator value is `−1`
    have haval : ((χ (Emb t) : kˣ) : k) * ((χ (Emb t) : kˣ) : k) = 1 := by
      rw [← pow_two, ← Units.val_pow_eq_pow_val, hsq t ht, Units.val_one]
    have ha : ((χ (Emb t) : kˣ) : k) = -1 := by
      rcases mul_self_eq_one_iff.mp haval with h | h
      · exact absurd (Units.ext (by rw [Units.val_one]; exact h)) ha1
      · exact h
    -- the `ε`-component of the generator value is `−1`
    have hbne : ε (Emb t) ≠ 1 := by
      intro hb1
      obtain ⟨m₀, hm₀⟩ := hgen σ₀ hσ₀
      have hsnd₀ : ε (Emb σ₀) = ε (Emb t) ^ m₀ := congrArg Prod.snd hm₀
      rw [hb1, one_pow] at hsnd₀
      exact hεσ₀ hsnd₀
    have hb : ((ε (Emb t) : kˣ) : k) = -1 := by
      haveI : CharP k 3 := charP_three_of_finite_padicIntThree_algebra
      rcases padic_three_ringHom_pm_one (algebraMap ℤ_[3] k)
        (cyclotomicCharacter (AlgebraicClosure ℚ) 3 (Emb t).toRingEquiv)
        with h | h
      · exact absurd (Units.ext (by
          rw [Units.val_one, hεval (Emb t)]; exact h)) hbne
      · rw [hεval (Emb t)]
        exact h
    -- conclude on every inertia element
    intro σ hσ
    obtain ⟨m, hm⟩ := hgen σ hσ
    have hfst : χ (Emb σ) = χ (Emb t) ^ m := congrArg Prod.fst hm
    have hsnd : ε (Emb σ) = ε (Emb t) ^ m := congrArg Prod.snd hm
    have hval2 : ((χ (Emb σ) : kˣ) : k) = ((ε (Emb σ) : kˣ) : k) := by
      rw [hfst, hsnd, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        ha, hb]
    rw [← hεval (Emb σ)]
    exact hval2

/-- **The Oort–Tate/Raynaud dichotomy at `3`** (DECOMPOSED 2026-07-23
into the two sorry nodes above — the order-two leaf
`quotCharacter_inertia_three_sq_one` (Frobenius conjugation on the
tame quotient; no flatness needed since `χ` is GLOBAL, unlike the
level-2 fundamental characters of Serre's §2.8 prop. 8 setting) and
the unique-quadratic-quotient leaf
`quotCharacter_inertia_three_dichotomy_of_sq_one`; the assembly is
proven): the quotient character `χ` of a stable line of a mod-3
hardly ramified representation, restricted to the inertia at `3`, is
either TRIVIAL or the mod-3 CYCLOTOMIC character — nothing else can
occur. (Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF
102 (1974), 3.3.2; Serre, Duke 1987, §2.8 prop. 8.) -/
theorem quotCharacter_inertia_three_dichotomy
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v) :
    (localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) ∨
    (∀ g ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      ((χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) g) : k)) =
        algebraMap ℤ_[3] k (cyclotomicCharacter (AlgebraicClosure ℚ) 3
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
                g).toRingEquiv))) :=
  quotCharacter_inertia_three_dichotomy_of_sq_one V hV hρ W₀ hW₀fr hstable
    ψ hψ χ hχ
    (quotCharacter_inertia_three_sq_one V hV hρ W₀ hW₀fr hstable ψ hψ χ hχ)

/-- **Raynaud's inertia characters at `3`** (DECOMPOSED 2026-07-23
into the dichotomy sorry node `quotCharacter_inertia_three_dichotomy`
above; the reduction is proven): if the quotient character `χ` of a
stable line of a mod-3 hardly ramified representation is RAMIFIED at
`3`, then on the inertia at `3` it EQUALS the mod-3 cyclotomic
character — the ramifiedness hypothesis excludes the trivial branch
of the Oort–Tate/Raynaud dichotomy. -/
theorem quotCharacter_eq_cyclotomic_on_inertia_three_of_ramified
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (h3 : ¬ (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker)) :
    ∀ g ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      ((χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) g) : k)) =
        algebraMap ℤ_[3] k (cyclotomicCharacter (AlgebraicClosure ℚ) 3
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
                g).toRingEquiv)) := by
  rcases quotCharacter_inertia_three_dichotomy V hV hρ W₀ hW₀fr hstable
    ψ hψ χ hχ with h | h
  · exact absurd h h3
  · exact h

/-- **The Raynaud dichotomy at `3`** (DECOMPOSED 2026-07-22 into the
sorry node `quotCharacter_eq_cyclotomic_on_inertia_three_of_ramified`
above; the determinant bookkeeping is proven): if the quotient
character `χ` of a stable line of a mod-3 hardly ramified
representation is RAMIFIED at `3`, then the sub-character `ψ` is
unramified at `3`. Derivation: on the inertia at `3`,
`ψ·χ = det ρ = χ₃` (the triangular determinant plus `hρ.det`), and by
the Raynaud leaf the ramified `χ` equals `χ₃` there, so cancelling
the unit `χ` gives `ψ = 1` on inertia. -/
theorem subCharacter_unramified_at_three_of_quot_ramified
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (h3 : ¬ (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker)) :
    localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
      (ψ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker := by
  intro g hg
  -- notation: the image of `g` in `Γ ℚ`
  set g' : Γ ℚ := Field.absoluteGaloisGroup.map (algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) g with hg'
  -- the quotient of `V` by the line is a line
  have hfr : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  have hQ1 : Module.finrank k (V ⧸ W₀) = 1 := by
    have hsum := Submodule.finrank_quotient_add_finrank W₀
    omega
  -- the triangular determinant identity at `g'`
  have hdet1 : LinearMap.det (ρ g' : Module.End k V) =
      (ψ g' : k) * (χ g' : k) :=
    det_eq_subCharacter_mul_quotCharacter ρ W₀ hW₀fr hQ1 hstable ψ χ hψ hχ g'
  -- the hardly-ramified determinant is the cyclotomic character
  have hdet2 : LinearMap.det (ρ g' : Module.End k V) =
      algebraMap ℤ_[3] k (cyclotomicCharacter (AlgebraicClosure ℚ) 3
        g'.toRingEquiv) := by
    have h := hρ.det g'
    rwa [GaloisRep.det_apply] at h
  -- the Raynaud leaf: the ramified `χ` is cyclotomic on inertia
  have hcyc := quotCharacter_eq_cyclotomic_on_inertia_three_of_ramified
    V hV hρ W₀ hW₀fr hstable ψ hψ χ hχ h3 g hg
  rw [← hg'] at hcyc
  -- cancel the unit `χ g'`
  have hψ1 : (ψ g' : k) = 1 := by
    have hne : (χ g' : k) ≠ 0 := Units.ne_zero (χ g')
    have h1 : (ψ g' : k) * (χ g' : k) = 1 * (χ g' : k) := by
      rw [one_mul, ← hdet1, hdet2, ← hcyc]
    exact mul_right_cancel₀ hne h1
  -- conclude in the unit group
  rw [MonoidHom.mem_ker]
  exact Units.ext hψ1

/-- **The connected–étale inertia subgroup at `3`** (sorry node — the
finite-flat/Raynaud content of the local splitting, isolated
2026-07-23 from `exists_inertia_eigenvector_complement_at_three`
below, whose eigenvector assembly is proven): the space of a
representation FLAT at `3` (over a finite char-3 coefficient field)
carries an additive subgroup `U` — intended: the points of the
connected part `G⁰` of the finite flat prolongation `G` at `3` —
such that (i) every inertia displacement `ρ(σ)v − v` lies in `U`,
and (ii) `U` contains no nonzero inertia-fixed vector. Intended
proof (Raynaud 1974; Serre, Duke 1987, §5.4): `ρ.IsFlatAt` at the
open ideal `⊥` produces a finite flat Hopf algebra over `𝒪ᵥ ≅ ℤ₃`
whose generic-fibre points are `V`, Galois-equivariantly
(`GaloisRep.HasFlatProlongationAt`). For (i): the étale quotient
`G/G⁰` of the connected–étale sequence is finite étale over the
henselian local `ℤ₃`, so its points are defined over the maximal
unramified extension and inertia fixes them; hence every inertia
displacement dies in the étale points and lands in
`U = ker(V → (G/G⁰)-points)` (left-exactness of points). For (ii):
`G⁰` is killed by `3` (its generic fibre is, and `𝒪(G⁰)` is
`ℤ₃`-free), and the schematic closures of a local-Galois composition
series of its generic fibre filter `G⁰` by finite flat closed
subgroups with CONNECTED simple graded pieces (quotients of the
local ring `𝒪(G⁰)` stay local); a nonzero inertia-fixed vector in
`U` would make the points of some graded piece unramified (the
inertia-fixed points form a local-Galois submodule, so by simplicity
the whole piece), hence the piece étale by Raynaud's criterion at
`e = 1 < 2 = p − 1` — an unramified finite flat group scheme killed
by `p` over `ℤ_p` is étale — contradicting connectedness.
Concretely, at order `3` the Oort–Tate list over `ℤ₃` contains only
`ℤ/3`-forms (étale, unramified points) and `μ₃`-forms (connected,
inertia acting through the nontrivial quadratic tame character
`χ₃ mod 3`). -/
theorem exists_connectedEtale_subgroup_at_three
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    {ρ : GaloisRep ℚ k V}
    (hflat : ρ.IsFlatAt Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ U : AddSubgroup V,
      (∀ σ ∈ localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat, ∀ v : V,
        ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) v - v ∈ U) ∧
      (∀ u ∈ U, (∀ σ ∈ localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
        ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) u = u) →
        u = 0) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The second inertia-stable line at `3`** (DECOMPOSED 2026-07-23
into the connected–étale sorry node
`exists_connectedEtale_subgroup_at_three` above — the finite-flat
content; the eigenvector assembly is proven here): a mod-3 hardly
ramified representation whose stable line `W₀` has quotient character
`χ` RAMIFIED at `3` admits a vector `v' ∉ W₀` on which the inertia at
`3` acts through `χ`. The proven assembly: the leaf provides `U`
containing all inertia displacements `ρ(σ)v − v` and no nonzero
inertia-fixed vector; the inertia fixes `W₀` pointwise
(`subCharacter_unramified_at_three_of_quot_ramified` plus `hψ`), so
`U ∩ W₀ = 0`; the ramification hypothesis `h3` yields `σ₀` with
`χ(σ₀) ≠ 1`, and `ρ(σ₀)` must move some `v₁` (else `hχ` at a vector
outside the line `W₀` would force `χ(σ₀) = 1`); the displacement
`v' := ρ(σ₀)v₁ − v₁` is then a nonzero element of `U`, hence
`v' ∉ W₀`; and for every inertia `σ` the eigen-defect
`ρ(σ)v' − χ(σ)•v'` lies in `W₀` (by `hχ`) and in `U` (it is the
displacement of `v'` plus `(1 − χ(σ))•v'`, where `χ(σ) = ±1` on the
inertia by `quotCharacter_eq_cyclotomic_on_inertia_three_of_ramified`
and `padic_three_ringHom_pm_one`), hence vanishes. -/
theorem exists_inertia_eigenvector_complement_at_three
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (h3 : ¬ (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker)) :
    ∃ v' : V, v' ∉ W₀ ∧ ∀ σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) v' =
        ((χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k)) • v' := by
  classical
  set Emb := Field.absoluteGaloisGroup.map (algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))
  -- the connected–étale subgroup of the flat prolongation (leaf)
  obtain ⟨U, hUaug, hUfix⟩ :=
    exists_connectedEtale_subgroup_at_three V (ρ := ρ) hρ.isFlat
  -- the inertia at `3` fixes the stable line `W₀` pointwise
  have hψun := subCharacter_unramified_at_three_of_quot_ramified
    V hV hρ W₀ hW₀fr hstable ψ hψ χ hχ h3
  have hW₀inv : ∀ τ ∈ localInertiaGroup
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      ∀ w ∈ W₀, ρ (Emb τ) w = w := by
    intro τ hτ w hw
    have h1 : ψ (Emb τ) = 1 := MonoidHom.mem_ker.mp (hψun hτ)
    rw [hψ (Emb τ) w hw, h1, Units.val_one, one_smul]
  -- `U` meets `W₀` trivially
  have hUW : ∀ x ∈ U, x ∈ W₀ → x = 0 := by
    intro x hxU hxW
    exact hUfix x hxU fun τ hτ => hW₀inv τ hτ x hxW
  -- `χ` takes the values `±1` on the inertia at `3`
  have hcyc := quotCharacter_eq_cyclotomic_on_inertia_three_of_ramified
    V hV hρ W₀ hW₀fr hstable ψ hψ χ hχ h3
  haveI : CharP k 3 := charP_three_of_finite_padicIntThree_algebra
  have hpm : ∀ σ ∈ localInertiaGroup
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      ((χ (Emb σ) : kˣ) : k) = 1 ∨ ((χ (Emb σ) : kˣ) : k) = -1 := by
    intro σ hσ
    have hval : ((χ (Emb σ) : kˣ) : k) = algebraMap ℤ_[3] k
        (cyclotomicCharacter (AlgebraicClosure ℚ) 3 ((Emb σ).toRingEquiv)) :=
      hcyc σ hσ
    rw [hval]
    exact padic_three_ringHom_pm_one (algebraMap ℤ_[3] k)
      (cyclotomicCharacter (AlgebraicClosure ℚ) 3 ((Emb σ).toRingEquiv))
  -- a ramified inertia element for `χ`
  obtain ⟨σ₀, hσ₀, hσ₀ker⟩ := SetLike.not_le_iff_exists.mp h3
  have hχσ₀ : χ (Emb σ₀) ≠ 1 := fun h1 => hσ₀ker (MonoidHom.mem_ker.mpr h1)
  -- `ρ (Emb σ₀)` moves some vector
  have hmove : ∃ v₁ : V, ρ (Emb σ₀) v₁ - v₁ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hfr : Module.finrank k V = 2 :=
      Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
    have hW₀top : W₀ ≠ ⊤ := by
      intro htop
      rw [htop, finrank_top, hfr] at hW₀fr
      omega
    obtain ⟨vq, -, hvq⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hW₀top)
    have hvq0 : W₀.mkQ vq ≠ 0 := by
      intro h0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      exact hvq h0
    have hfixq : ρ (Emb σ₀) vq = vq := sub_eq_zero.mp (hall vq)
    have h1 : ((χ (Emb σ₀) : kˣ) : k) • W₀.mkQ vq = W₀.mkQ vq := by
      rw [← hχ (Emb σ₀) vq, hfixq]
    have h2 : (((χ (Emb σ₀) : kˣ) : k) - 1) • W₀.mkQ vq = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with hz | hz
    · exact hχσ₀ (Units.ext (show ((χ (Emb σ₀) : kˣ) : k) = 1 by
        linear_combination hz))
    · exact hvq0 hz
  obtain ⟨v₁, hv₁ne⟩ := hmove
  set u₀ : V := ρ (Emb σ₀) v₁ - v₁
  have hu₀U : u₀ ∈ U := hUaug σ₀ hσ₀ v₁
  have hu₀W : u₀ ∉ W₀ := fun hmem => hv₁ne (hUW u₀ hu₀U hmem)
  refine ⟨u₀, hu₀W, ?_⟩
  intro σ hσ
  -- the eigen-defect lies in `U ∩ W₀ = 0`
  have hdW : ρ (Emb σ) u₀ - ((χ (Emb σ) : kˣ) : k) • u₀ ∈ W₀ := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub,
      map_smul, hχ (Emb σ) u₀, sub_self]
  have hdU : ρ (Emb σ) u₀ - ((χ (Emb σ) : kˣ) : k) • u₀ ∈ U := by
    rcases hpm σ hσ with h1 | h1
    · rw [h1, one_smul]
      exact hUaug σ hσ u₀
    · have he : ρ (Emb σ) u₀ - ((χ (Emb σ) : kˣ) : k) • u₀ =
          (ρ (Emb σ) u₀ - u₀) + (u₀ + u₀) := by
        rw [h1, neg_smul, one_smul, sub_neg_eq_add]
        abel
      rw [he]
      exact U.add_mem (hUaug σ hσ u₀) (U.add_mem hu₀U hu₀U)
  have hd0 : ρ (Emb σ) u₀ - ((χ (Emb σ) : kˣ) : k) • u₀ = 0 := hUW _ hdU hdW
  exact sub_eq_zero.mp hd0

/-- **The local splitting at `3`** (DECOMPOSED 2026-07-23 into the
sorry node `exists_inertia_eigenvector_complement_at_three` above —
the finite-flat/connected–étale content; the coordinate reduction is
proven here): in the coordinates of
`exists_splitting_scalar_of_quot_ramified`, the extension cocycle `c`
is a coboundary already on the inertia at `3`: a single scalar `s`
has `c σ = s·(χ σ − ψ σ)` for every `σ` in the image of the local
inertia at `3`. The proven reduction: the leaf provides `v' ∉ W₀`
with `ρ σ v' = χ σ • v'` on inertia; writing `v' = a•v₁ + bb•w₀` in
the adapted basis (`a ≠ 0` since `v' ∉ W₀`) and comparing
`w₀`-coefficients in the eigenvector equation gives
`a·c σ + bb·ψ σ − χ σ·bb = 0`, i.e. `c σ = (a⁻¹·bb)·(χ σ − ψ σ)`, so
`s := a⁻¹·bb` works. -/
theorem exists_local_splitting_scalar_at_three
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (h3 : ¬ (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker))
    (w₀ : V) (hw₀ : w₀ ∈ W₀) (hw₀ne : w₀ ≠ 0)
    (v₁ : V) (hv₁ : v₁ ∉ W₀)
    (c : Γ ℚ → k)
    (hc : ∀ g : Γ ℚ, ρ g v₁ = (χ g : k) • v₁ + c g • w₀) :
    ∃ s : k, ∀ σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      c (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) =
        s * ((χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) -
          (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k)) := by
  classical
  -- dimensions
  have hfr : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  have hQ1 : Module.finrank k (V ⧸ W₀) = 1 := by
    have hsum := Submodule.finrank_quotient_add_finrank W₀
    omega
  -- the second inertia-stable line (leaf)
  obtain ⟨v', hv', heig⟩ := exists_inertia_eigenvector_complement_at_three
    V hV hρ W₀ hW₀fr hstable ψ hψ χ hχ h3
  -- every element of `W₀` is a multiple of `w₀`
  have hspan : ∀ y ∈ W₀, ∃ a : k, y = a • w₀ := by
    intro y hy
    have hne : (⟨w₀, hw₀⟩ : W₀) ≠ 0 := fun h =>
      hw₀ne (by simpa using congrArg Subtype.val h)
    have h1 : Submodule.span k {(⟨w₀, hw₀⟩ : W₀)} = ⊤ :=
      (finrank_eq_one_iff_of_nonzero _ hne).mp hW₀fr
    have h2 : (⟨y, hy⟩ : W₀) ∈ Submodule.span k {(⟨w₀, hw₀⟩ : W₀)} := by
      rw [h1]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h2
    exact ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  -- coordinates of `v'` in the adapted basis `{v₁, w₀}`
  obtain ⟨a, bb, hv'eq⟩ : ∃ a bb : k, v' = a • v₁ + bb • w₀ := by
    have hv₁ne : W₀.mkQ v₁ ≠ 0 := by
      intro h0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      exact hv₁ h0
    have hspanQ : Submodule.span k {W₀.mkQ v₁} = ⊤ :=
      (finrank_eq_one_iff_of_nonzero _ hv₁ne).mp hQ1
    have hmemQ : W₀.mkQ v' ∈ Submodule.span k {W₀.mkQ v₁} := by
      rw [hspanQ]
      exact Submodule.mem_top
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmemQ
    have hvmem : v' - μ • v₁ ∈ W₀ := by
      have h0 : W₀.mkQ (v' - μ • v₁) = 0 := by
        rw [map_sub, map_smul, hμ, sub_self]
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨bb₀, hbb₀⟩ := hspan _ hvmem
    refine ⟨μ, bb₀, ?_⟩
    have h1 : μ • v₁ + (v' - μ • v₁) = v' := by abel
    rw [hbb₀] at h1
    exact h1.symm
  -- the `v₁`-coordinate is nonzero since `v' ∉ W₀`
  have ha : a ≠ 0 := by
    intro h0
    apply hv'
    rw [hv'eq, h0, zero_smul, zero_add]
    exact W₀.smul_mem bb hw₀
  refine ⟨a⁻¹ * bb, ?_⟩
  intro σ hσ
  set g' : Γ ℚ := Field.absoluteGaloisGroup.map (algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ with hg'def
  have h1 := heig σ hσ
  rw [← hg'def, hv'eq, map_add (ρ g'), map_smul (ρ g'), map_smul (ρ g'),
    hc g', hψ g' w₀ hw₀] at h1
  -- compare `w₀`-coefficients
  have hcoef : (a * c g' + bb * (ψ g' : k) - (χ g' : k) * bb) • w₀ = 0 := by
    linear_combination (norm := module) h1
  rcases smul_eq_zero.mp hcoef with hz | hz
  · have h2 : a * c g' = bb * ((χ g' : k) - (ψ g' : k)) := by
      linear_combination hz
    have h3' : c g' = a⁻¹ * (a * c g') := by
      rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    rw [h3', h2]
    ring
  · exact absurd hz hw₀ne

/-- **Twisted coboundaries from vanishing on the agreement locus**
(PROVEN 2026-07-23 — the inflation–restriction/averaging half of the
global Selmer vanishing, valid over any finite field `k` and any
group `G`): a `(χ, ψ)`-twisted cocycle `c : G → k` (satisfying
`c(gh) = χ(h)·c(g) + ψ(g)·c(h)`) that vanishes on the locus
`{g : ψ g = χ g}` — i.e. on the kernel of the character `η := ψ/χ` —
is a twisted coboundary `c = t·(χ − ψ)`. Proof: `b := c/χ` is an
honest `η`-twisted cocycle which, vanishing on `ker η`, factors
through the FINITE group `η.range ≤ kˣ`; summing the descended
cocycle identity `B(uv) = B(u) + u·B(v)` over `v` gives
`N·B(u) = (1 − u)·T` with `T = ∑ B` and `N = |η.range|`, and `N` is
invertible in `k` because it divides `|kˣ| = |k| − 1`, which is `−1`
in `k`; hence `b = (T/N)·(1 − η)`, i.e. `c = (T/N)·(χ − ψ)`. This is
exactly the vanishing of `H¹` of the prime-to-`char k` quotient
`G/ker η`, done by explicit averaging. -/
theorem exists_twisted_coboundary_scalar_of_agreement_vanishing
    {k : Type u} [Finite k] [Field k] {G : Type*} [Group G]
    (χ ψ : G →* kˣ) (c : G → k)
    (hcocycle : ∀ g h : G, c (g * h) = (χ h : k) * c g + (ψ g : k) * c h)
    (h0 : ∀ g : G, (ψ g : k) = (χ g : k) → c g = 0) :
    ∃ t : k, ∀ g : G, c g = t * ((χ g : k) - (ψ g : k)) := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  -- the untwisted cocycle `b = c/χ` for the character `η = ψ/χ`
  set η : G →* kˣ := ψ / χ with hηdef
  set b : G → k := fun g => c g * ((χ g : k))⁻¹ with hbdef
  have hηval : ∀ g : G, ((η g : kˣ) : k) = (ψ g : k) * ((χ g : k))⁻¹ := by
    intro g
    rw [hηdef]
    simp [div_eq_mul_inv]
  have hχne : ∀ g : G, ((χ g : k)) ≠ 0 := fun g => Units.ne_zero (χ g)
  have hbcocycle : ∀ g h : G, b (g * h) = b g + ((η g : kˣ) : k) * b h := by
    intro g h
    show c (g * h) * ((χ (g * h) : k))⁻¹ =
      c g * ((χ g : k))⁻¹ + ((η g : kˣ) : k) * (c h * ((χ h : k))⁻¹)
    rw [hcocycle g h, hηval g, map_mul, Units.val_mul]
    field_simp [hχne]
  have hb0 : ∀ g : G, η g = 1 → b g = 0 := by
    intro g hg
    have hψχ : (ψ g : k) = (χ g : k) := by
      have h1 : ψ g = χ g := by
        have h2 : ψ g / χ g = 1 := hg
        exact div_eq_one.mp h2
      exact congrArg Units.val h1
    show c g * ((χ g : k))⁻¹ = 0
    rw [h0 g hψχ, zero_mul]
  -- `b` is constant on the fibers of `η`
  have hbwd : ∀ g₁ g₂ : G, η g₁ = η g₂ → b g₁ = b g₂ := by
    intro g₁ g₂ h
    have hker : η (g₁⁻¹ * g₂) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hbcocycle g₁ (g₁⁻¹ * g₂)
    rw [mul_inv_cancel_left, hb0 _ hker, mul_zero, add_zero] at h2
    exact h2.symm
  -- a section of `η` over its range, and the descended cocycle `B`
  have hsecex : ∀ u : η.range, ∃ g : G, η g = (u : kˣ) := fun u =>
    MonoidHom.mem_range.mp u.2
  choose sec hsec using hsecex
  set B : η.range → k := fun u => b (sec u) with hBdef
  have hbB : ∀ g : G, b g = B ⟨η g, ⟨g, rfl⟩⟩ := by
    intro g
    exact hbwd g (sec ⟨η g, ⟨g, rfl⟩⟩) (hsec ⟨η g, ⟨g, rfl⟩⟩).symm
  have hBco : ∀ u v : η.range, B (u * v) = B u + ((u : kˣ) : k) * B v := by
    intro u v
    have h1 : η (sec (u * v)) = η (sec u * sec v) := by
      rw [hsec (u * v), map_mul, hsec u, hsec v, Subgroup.coe_mul]
    have h2 : B (u * v) = b (sec u * sec v) := hbwd _ _ h1
    rw [h2, hbcocycle, hsec u]
  -- average over the finite range of `η`
  letI : Fintype η.range := Fintype.ofFinite _
  set T : k := ∑ u : η.range, B u with hTdef
  set N : ℕ := Fintype.card η.range with hNdef
  have hNne : ((N : k)) ≠ 0 := by
    intro hzero
    have hdvd1 : Nat.card η.range ∣ Nat.card kˣ :=
      Subgroup.card_subgroup_dvd_card _
    obtain ⟨m, hm⟩ := hdvd1
    have hcard : Nat.card kˣ = Fintype.card k - 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units]
    have hcast : ((Nat.card kˣ : ℕ) : k) = -1 := by
      rw [hcard, Nat.cast_sub Fintype.card_pos, Nat.cast_one,
        FiniteField.cast_card_eq_zero, zero_sub]
    rw [hm, Nat.cast_mul] at hcast
    have hz2 : ((Nat.card η.range : ℕ) : k) = 0 := by
      rw [Nat.card_eq_fintype_card, ← hNdef]
      exact hzero
    rw [hz2, zero_mul] at hcast
    exact one_ne_zero (neg_eq_zero.mp hcast.symm)
  have hkey : ∀ u : η.range, (N : k) * B u = (1 - ((u : kˣ) : k)) * T := by
    intro u
    have h1 : ∑ v : η.range, B (u * v) = T := by
      rw [hTdef]
      exact Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun v => rfl)
    have h2 : ∑ v : η.range, B (u * v) = N • B u + ((u : kˣ) : k) * T := by
      calc ∑ v : η.range, B (u * v)
          = ∑ v : η.range, (B u + ((u : kˣ) : k) * B v) :=
            Finset.sum_congr rfl fun v _ => hBco u v
        _ = N • B u + ((u : kˣ) : k) * T := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
              ← Finset.mul_sum, hTdef, hNdef]
    have h3 : T = N • B u + ((u : kˣ) : k) * T := h1.symm.trans h2
    rw [nsmul_eq_mul] at h3
    linear_combination -h3
  refine ⟨(N : k)⁻¹ * T, ?_⟩
  intro g
  have h5 := hkey ⟨η g, ⟨g, rfl⟩⟩
  rw [← hbB g] at h5
  have h6 : c g = b g * (χ g : k) := by
    show c g = c g * ((χ g : k))⁻¹ * (χ g : k)
    field_simp
  have h7 : ((⟨η g, ⟨g, rfl⟩⟩ : η.range) : kˣ) = η g := rfl
  rw [h7] at h5
  have h8 : (N : k) * (b g * (χ g : k)) =
      (N : k) * (((N : k)⁻¹ * T) * ((χ g : k) - (ψ g : k))) := by
    have h9 : ((η g : kˣ) : k) * (χ g : k) = (ψ g : k) := by
      rw [hηval g]
      field_simp
    calc (N : k) * (b g * (χ g : k))
        = ((N : k) * b g) * (χ g : k) := by ring
      _ = ((1 - ((η g : kˣ) : k)) * T) * (χ g : k) := by rw [h5]
      _ = T * (χ g : k) - T * (((η g : kˣ) : k) * (χ g : k)) := by ring
      _ = T * (χ g : k) - T * (ψ g : k) := by rw [h9]
      _ = (N : k) * (((N : k)⁻¹ * T) * ((χ g : k) - (ψ g : k))) := by
          field_simp
  rw [h6]
  exact mul_left_cancel₀ hNne h8

/-- **The agreement additive character is killed by ray-class
arithmetic** (sorry node, isolated 2026-07-24 — the class-field-theory
core of the global Selmer vanishing, restated from
`agreement_cocycle_eq_zero_ray_class` below with the whole cocycle
layer hoisted into an abstract additive character: in the
application `b = c/χ`, and the untwisting bookkeeping is PROVEN glue
there): an additive character `b` of the agreement subgroup
`H = {g | ψ g = χ g} = ker(ψχ⁻¹) = Γ_F` (`hbadd`), trivial on the
open subgroup `ker ρ` (`hker` — so `b` and the agreement locus factor
through the FINITE quotient by `ker ρ`), `ψχ⁻¹`-equivariantly
conjugated (`hconj`), vanishing on the inertia of every prime
`q ∉ {2, 3}` (`hunr`) and on the agreement part of the inertia at `3`
(`h3z`), vanishes identically on `H`.

Intended content (Serre, Duke 1987, §5.4, mod-3 analogue): `b` is an
additive character `H → (k, +)` with `char k = 3`, so it cuts out an
abelian `3`-elementary extension `M/F`, Galois over `ℚ` by the
equivariance `hconj`. Identification of `F`: `χ` is unramified at `2`
(the tame dichotomy `quotCharacter_inertia_two_ker` applied to the
stable line `W₀` — PROVEN but stated LATER in this file, so reprove
or move it when resolving this node), hence so is `ψ = det/χ` since
the determinant is cyclotomic (`hρ.det` +
`cyclotomicCharacter_algebraMap_eq_one_of_inertia_two`, same remark);
both are unramified outside `{2, 3}` (`hunr`); and at `3` the
quotient character `χ` is RAMIFIED (`h3`) with `χ = ω` on inertia
while `ψ` is unramified there, so `η = ψχ⁻¹` is a character ramified
only at `3` whose inertia image has order dividing `2`. Since `ℚ`
admits no unramified extension (Minkowski,
`minkowski_character_trivial`), either `η = 1` and `F = ℚ`, or
`F = ℚ(√-3)`, the quadratic field of conductor `3`. The extension
`M/F` is unramified outside `2` (`hunr` + `h3z` with the
`hconj`-conjugates covering all primes over `3`), split at the primes
over `3`, and automatically TAME at `2`: its degree is a `3`-power
while the residue characteristic is `2`, so the conductor exponent at
each prime over `2` is at most `1`. The ray-class arithmetic kills
`M`: for `F = ℚ` the ray class field of conductor `2^k∞` is the
`2`-power-degree cyclotomic tower, with no `3`-part; for
`F = ℚ(√-3)` — class number `1`, `2` inert — the ray class group of
conductor `(2)` is `(𝒪/2)ˣ/⟨image of 𝒪ˣ⟩ = 𝔽₄ˣ/⟨ζ₆ mod 2⟩ = 1`.
Hence `M = F` and `b` vanishes on `H`. References: Serre, Duke Math.
J. 54 (1987) §5.4; Tate's 1974 letter to Serre (Œuvres III);
Neukirch, ANT VI §6. -/
theorem agreement_additive_character_eq_zero_ray_class
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (h3 : ¬ (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker))
    (b : Γ ℚ → k)
    (hbadd : ∀ g h : Γ ℚ, (ψ g : k) = (χ g : k) → (ψ h : k) = (χ h : k) →
      b (g * h) = b g + b h)
    (hker : ∀ g : Γ ℚ, ρ g = 1 →
      (ψ g : k) = 1 ∧ (χ g : k) = 1 ∧ b g = 0)
    (hunr : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) = 1 ∧
        (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) = 1 ∧
        b (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 0)
    (h3z : ∀ σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) =
        (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) →
      b (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 0)
    (hconj : ∀ g h : Γ ℚ, (ψ h : k) = (χ h : k) →
      (χ g : k) * b (g * h * g⁻¹) = (ψ g : k) * b h) :
    ∀ g : Γ ℚ, (ψ g : k) = (χ g : k) → b g = 0 := by
  sorry

/-- **The agreement homomorphism is killed by ray-class arithmetic**
(DECOMPOSED 2026-07-24 into the additive-character sorry node
`agreement_additive_character_eq_zero_ray_class` above — the assembly
is proven): the untwisting `b := c/χ`. By `hcocycle` the function `b`
is additive on the agreement locus `H = {g | ψ g = χ g}`; the kernel
carrier `hker`, the outside-`{2,3}` inertia vanishing `hunr` and the
agreement-inertia-at-`3` vanishing `h3z` transport from `c` to `b` by
`c = b · χ`; and the twisted conjugation equivariance `hconj`
transports since `χ(ghg⁻¹) = χ(h)` for the abelian-valued
homomorphism `χ`. The ray-class leaf then kills `b` on `H`, hence
`c = b · χ` too. -/
theorem agreement_cocycle_eq_zero_ray_class
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (h3 : ¬ (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker))
    (w₀ : V) (_hw₀ : w₀ ∈ W₀) (_hw₀ne : w₀ ≠ 0)
    (v₁ : V) (_hv₁ : v₁ ∉ W₀)
    (c : Γ ℚ → k)
    (_hc : ∀ g : Γ ℚ, ρ g v₁ = (χ g : k) • v₁ + c g • w₀)
    (hcocycle : ∀ g h : Γ ℚ, c (g * h) = (χ h : k) * c g + (ψ g : k) * c h)
    (s : k)
    (_hs : ∀ σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      c (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) =
        s * ((χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) -
          (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k)))
    (hker : ∀ g : Γ ℚ, ρ g = 1 →
      (ψ g : k) = 1 ∧ (χ g : k) = 1 ∧ c g = 0)
    (hunr : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) = 1 ∧
        (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) = 1 ∧
        c (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 0)
    (h3z : ∀ σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) =
        (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) →
      c (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 0)
    (hconj : ∀ g h : Γ ℚ, (ψ h : k) = (χ h : k) →
      (χ g : k) * c (g * h * g⁻¹) = (ψ g : k) * c h) :
    ∀ g : Γ ℚ, (ψ g : k) = (χ g : k) → c g = 0 := by
  classical
  have hχne : ∀ g : Γ ℚ, ((χ g : k)) ≠ 0 := fun g => Units.ne_zero (χ g)
  -- the untwisted function `b = c/χ`
  set b : Γ ℚ → k := fun g => c g * ((χ g : k))⁻¹
  -- `b` is additive on the agreement locus
  have hbadd : ∀ g h : Γ ℚ, (ψ g : k) = (χ g : k) → (ψ h : k) = (χ h : k) →
      b (g * h) = b g + b h := by
    intro g h hg hh
    show c (g * h) * ((χ (g * h) : k))⁻¹ =
      c g * ((χ g : k))⁻¹ + c h * ((χ h : k))⁻¹
    rw [hcocycle g h, map_mul, Units.val_mul, hg]
    field_simp [hχne]
  -- the kernel carrier transports to `b`
  have hkerb : ∀ g : Γ ℚ, ρ g = 1 →
      (ψ g : k) = 1 ∧ (χ g : k) = 1 ∧ b g = 0 := by
    intro g hg
    obtain ⟨h1, h2, h3'⟩ := hker g hg
    refine ⟨h1, h2, ?_⟩
    show c g * ((χ g : k))⁻¹ = 0
    rw [h3', zero_mul]
  -- the outside-`{2,3}` inertia vanishing transports to `b`
  have hunrb : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) = 1 ∧
        (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) = 1 ∧
        b (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 0 := by
    intro q hq hq2 hq3 σ hσ
    obtain ⟨h1, h2, h3'⟩ := hunr q hq hq2 hq3 σ hσ
    refine ⟨h1, h2, ?_⟩
    show c _ * ((χ _ : k))⁻¹ = 0
    rw [h3', zero_mul]
  -- the agreement-inertia vanishing at `3` transports to `b`
  have hb3 : ∀ σ ∈ localInertiaGroup
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) =
        (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) →
      b (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 0 := by
    intro σ hσ hag
    show c _ * ((χ _ : k))⁻¹ = 0
    rw [h3z σ hσ hag, zero_mul]
  -- the twisted conjugation equivariance transports to `b`
  have hbconj : ∀ g h : Γ ℚ, (ψ h : k) = (χ h : k) →
      (χ g : k) * b (g * h * g⁻¹) = (ψ g : k) * b h := by
    intro g h hh
    have h1 := hconj g h hh
    have hχc : ((χ (g * h * g⁻¹) : k)) = ((χ h : k)) := by
      have h2 : χ (g * h * g⁻¹) = χ h := by
        rw [map_mul, map_mul, map_inv, mul_comm (χ g) (χ h), mul_assoc,
          mul_inv_cancel, mul_one]
      rw [h2]
    show (χ g : k) * (c (g * h * g⁻¹) * ((χ (g * h * g⁻¹) : k))⁻¹) =
      (ψ g : k) * (c h * ((χ h : k))⁻¹)
    rw [hχc]
    field_simp [hχne]
    linear_combination h1
  -- the ray-class leaf kills `b`, hence `c = b · χ`
  intro g hg
  have hb0 := agreement_additive_character_eq_zero_ray_class V hV hρ W₀ hW₀fr
    hstable ψ hψ χ hχ h3 b hbadd hkerb hunrb hb3 hbconj g hg
  have hcb : c g = b g * (χ g : k) := by
    show c g = c g * ((χ g : k))⁻¹ * (χ g : k)
    rw [inv_mul_cancel_right₀ (hχne g)]
  rw [hcb, hb0, zero_mul]

/-- **The cocycle vanishes on the character-agreement locus**
(DECOMPOSED 2026-07-23 into the ray-class core sorry node
`agreement_cocycle_eq_zero_ray_class` above — the local bookkeeping
is PROVEN here as glue): the extension cocycle `c` of a mod-3 hardly
ramified representation, coboundary on the inertia at `3` (`hs`),
vanishes at every `g` where the two characters agree, `ψ g = χ g` —
i.e. on the open normal subgroup `H = ker(ψχ⁻¹) = Gal(ℚ̄/F)`, where
`F` is the finite abelian extension of `ℚ` cut out by `η = ψχ⁻¹`.
The proven reduction: on `ker ρ`, the identity `ρ g v₁ = v₁` forces
`χ g = 1` (else `v₁ ∈ W₀`), then `c g = 0` (`w₀ ≠ 0`), and
`ρ g w₀ = w₀` forces `ψ g = 1` — the kernel carrier; through
`hρ.isUnramified` (with the `Rat.subsingleton_ringHom` `convert`
bridge) this kills `ψ - 1`, `χ - 1` and `c` on the inertia of every
prime `q ∉ {2, 3}`; on the inertia at `3` the coboundary hypothesis
`hs` vanishes on the agreement locus; and the twisted conjugation
equivariance `χ(g)·c(ghg⁻¹) = ψ(g)·c(h)` for `h ∈ H` follows from
two applications of the cocycle identity and commutativity of `kˣ`. -/
theorem cocycle_eq_zero_on_agreement_of_local_at_three
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (h3 : ¬ (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker))
    (w₀ : V) (hw₀ : w₀ ∈ W₀) (hw₀ne : w₀ ≠ 0)
    (v₁ : V) (hv₁ : v₁ ∉ W₀)
    (c : Γ ℚ → k)
    (hc : ∀ g : Γ ℚ, ρ g v₁ = (χ g : k) • v₁ + c g • w₀)
    (hcocycle : ∀ g h : Γ ℚ, c (g * h) = (χ h : k) * c g + (ψ g : k) * c h)
    (s : k)
    (hs : ∀ σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      c (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) =
        s * ((χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) -
          (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k))) :
    ∀ g : Γ ℚ, (ψ g : k) = (χ g : k) → c g = 0 := by
  classical
  -- the kernel carrier: `ψ`, `χ` and `c` are trivial on `ker ρ`
  have hker : ∀ g : Γ ℚ, ρ g = 1 →
      (ψ g : k) = 1 ∧ (χ g : k) = 1 ∧ c g = 0 := by
    intro g hg
    have hgv : ∀ y : V, ρ g y = y := by
      intro y
      rw [hg]
      rfl
    have hψ1 : (ψ g : k) = 1 := by
      have h1 : (ψ g : k) • w₀ = w₀ := by
        rw [← hψ g w₀ hw₀]
        exact hgv w₀
      have h2 : ((ψ g : k) - 1) • w₀ = 0 := by
        rw [sub_smul, one_smul, h1, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hw₀ne
    have hχ1 : (χ g : k) = 1 := by
      by_contra hne1
      apply hv₁
      have h1 : (χ g : k) • v₁ + c g • w₀ = v₁ := by
        rw [← hc g]
        exact hgv v₁
      have h3 : (1 - (χ g : k)) • v₁ = c g • w₀ := by
        rw [sub_smul, one_smul]
        linear_combination (norm := module) -h1
      have h4 : v₁ = ((1 - (χ g : k))⁻¹ * c g) • w₀ := by
        rw [mul_smul, ← h3, smul_smul,
          inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hne1)), one_smul]
      rw [h4]
      exact Submodule.smul_mem W₀ _ hw₀
    refine ⟨hψ1, hχ1, ?_⟩
    have h1 : (χ g : k) • v₁ + c g • w₀ = v₁ := by
      rw [← hc g]
      exact hgv v₁
    rw [hχ1, one_smul] at h1
    have h2 : c g • w₀ = 0 := by
      linear_combination (norm := module) h1
    rcases smul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hw₀ne
  -- vanishing on the inertia of every prime outside `{2, 3}`
  have hunr : ∀ (q : ℕ) (hq : q.Prime), q ≠ 2 → q ≠ 3 →
      ∀ σ ∈ localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat,
        (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) = 1 ∧
        (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) = 1 ∧
        c (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)) σ) = 0 := by
    intro q hq hq2 hq3 σ hσ
    apply hker
    have h1 : (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat) σ = 1 :=
      (hρ.isUnramified q hq ⟨hq2, hq3⟩).localInertiaGroup_le hσ
    rw [GaloisRep.toLocal_apply] at h1
    convert h1 using 4
    exact Subsingleton.elim _ _
  -- vanishing on the inertia at `3` inside the agreement locus
  have h3z : ∀ σ ∈ localInertiaGroup
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) =
        (χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) →
      c (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) = 0 := by
    intro σ hσ hag
    rw [hs σ hσ, hag, sub_self, mul_zero]
  -- the twisted conjugation equivariance
  have hconj : ∀ g h : Γ ℚ, (ψ h : k) = (χ h : k) →
      (χ g : k) * c (g * h * g⁻¹) = (ψ g : k) * c h := by
    intro g h hh
    have h1 := hcocycle (g * h * g⁻¹) g
    rw [inv_mul_cancel_right] at h1
    have h2 := hcocycle g h
    have hψc : (ψ (g * h * g⁻¹) : k) = (ψ h : k) := by
      have h3' : ψ (g * h * g⁻¹) = ψ h := by
        rw [map_mul, map_mul, map_inv, mul_comm (ψ g) (ψ h), mul_assoc,
          mul_inv_cancel, mul_one]
      rw [h3']
    rw [hψc] at h1
    linear_combination h2 - h1 - c g * hh
  -- the ray-class core (sorried leaf)
  exact agreement_cocycle_eq_zero_ray_class V hV hρ W₀ hW₀fr hstable ψ hψ
    χ hχ h3 w₀ hw₀ hw₀ne v₁ hv₁ c hc hcocycle s hs hker hunr h3z hconj

/-- **The global Selmer vanishing** (DECOMPOSED 2026-07-23 into the
agreement-locus sorry node
`cocycle_eq_zero_on_agreement_of_local_at_three` above — the
class-field-theory content — assembled with the PROVEN averaging
lemma `exists_twisted_coboundary_scalar_of_agreement_vanishing`): a
function `c` satisfying the twisted cocycle identity
`c(gh) = χ(h)·c(g) + ψ(g)·c(h)` attached to a mod-3 hardly ramified
representation, which is a coboundary on the inertia at `3` (with
scalar `s`, hypothesis `hs`), is a GLOBAL coboundary. The reduction:
on the agreement locus `{g : ψ g = χ g}` every coboundary
`t·(χ − ψ)` vanishes identically, so the class of `c` vanishes iff
`c` itself vanishes there (restriction to `ker(ψχ⁻¹)` is injective on
`H¹` because the quotient is finite of order prime to `char k` —
the averaging lemma); the sorried leaf supplies that vanishing. -/
theorem splitting_scalar_global_of_local_at_three
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (h3 : ¬ (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker))
    (w₀ : V) (hw₀ : w₀ ∈ W₀) (hw₀ne : w₀ ≠ 0)
    (v₁ : V) (hv₁ : v₁ ∉ W₀)
    (c : Γ ℚ → k)
    (hc : ∀ g : Γ ℚ, ρ g v₁ = (χ g : k) • v₁ + c g • w₀)
    (hcocycle : ∀ g h : Γ ℚ, c (g * h) = (χ h : k) * c g + (ψ g : k) * c h)
    (s : k)
    (hs : ∀ σ ∈ localInertiaGroup
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat,
      c (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) =
        s * ((χ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k) -
          (ψ (Field.absoluteGaloisGroup.map (algebraMap ℚ
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat)) σ) : k))) :
    ∃ t : k, ∀ g : Γ ℚ, c g = t * ((χ g : k) - (ψ g : k)) :=
  exists_twisted_coboundary_scalar_of_agreement_vanishing χ ψ c hcocycle
    (cocycle_eq_zero_on_agreement_of_local_at_three V hV hρ W₀ hW₀fr
      hstable ψ hψ χ hχ h3 w₀ hw₀ hw₀ne v₁ hv₁ c hc hcocycle s hs)

/-- **The Serre swap, cocycle form** (DECOMPOSED 2026-07-23 into the
two sorry nodes above — the connected–étale local splitting
`exists_local_splitting_scalar_at_three` and the global Selmer
vanishing `splitting_scalar_global_of_local_at_three`; the cocycle
identity `c(gh) = χ(h)·c(g) + ψ(g)·c(h)` is proven here as glue):
with a basis adapted to the ramified-quotient situation — `w₀`
spanning the stable line `W₀` and `v₁` a complement vector — the
extension cocycle `c` (defined by `ρ g v₁ = χ g • v₁ + c g • w₀`) is
a coboundary: there is a single scalar `t` with `c g = t·(χ g − ψ g)`
for all `g`. This is exactly the vanishing of the class of the
extension `0 → ψ → V → χ → 0` in `H¹(ℚ, k(ψχ⁻¹))`. -/
theorem exists_splitting_scalar_of_quot_ramified
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (h3 : ¬ (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker))
    (w₀ : V) (hw₀ : w₀ ∈ W₀) (hw₀ne : w₀ ≠ 0)
    (v₁ : V) (hv₁ : v₁ ∉ W₀)
    (c : Γ ℚ → k)
    (hc : ∀ g : Γ ℚ, ρ g v₁ = (χ g : k) • v₁ + c g • w₀) :
    ∃ t : k, ∀ g : Γ ℚ, c g = t * ((χ g : k) - (ψ g : k)) := by
  classical
  -- the twisted cocycle identity for `c` (proven glue)
  have hcocycle : ∀ g h : Γ ℚ, c (g * h) = (χ h : k) * c g + (ψ g : k) * c h := by
    intro g h
    have h1 : ρ (g * h) v₁ = ρ g (ρ h v₁) := by
      rw [map_mul ρ g h]
      rfl
    have hval : ((χ (g * h) : k)) = (χ g : k) * (χ h : k) := by
      rw [map_mul, Units.val_mul]
    rw [hc (g * h), hc h, map_add (ρ g), map_smul (ρ g), map_smul (ρ g),
      hc g, hψ g w₀ hw₀, hval] at h1
    have hcoef : (c (g * h) - ((χ h : k) * c g + (ψ g : k) * c h)) • w₀ = 0 := by
      linear_combination (norm := module) h1
    rcases smul_eq_zero.mp hcoef with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 hw₀ne
  -- the local splitting at `3` (leaf)
  obtain ⟨s, hs⟩ := exists_local_splitting_scalar_at_three V hV hρ W₀ hW₀fr
    hstable ψ hψ χ hχ h3 w₀ hw₀ hw₀ne v₁ hv₁ c hc
  -- the global Selmer vanishing (leaf)
  exact splitting_scalar_global_of_local_at_three V hV hρ W₀ hW₀fr
    hstable ψ hψ χ hχ h3 w₀ hw₀ hw₀ne v₁ hv₁ c hc hcocycle s hs

set_option backward.isDefEq.respectTransparency false in
/-- **The Serre swap: the second stable line** (DECOMPOSED 2026-07-23
into the cocycle-vanishing sorry node
`exists_splitting_scalar_of_quot_ramified` above; the coordinate
reduction is proven): if the quotient character `χ` of a stable line
`W₀` of a mod-3 hardly ramified representation is ramified at `3`,
then the representation has a SECOND stable line whose quotient
character is the sub-character `ψ` of `W₀` — i.e. the extension
`0 → ψ → V → χ → 0` splits. The proven reduction: choose `w₀`
spanning `W₀` and `v₁ ∉ W₀`; since `mkQ (ρ g v₁) = χ g • mkQ v₁`, the
element `ρ g v₁ − χ g • v₁` lies in `W₀ = k·w₀`, defining the cocycle
`c` with `ρ g v₁ = χ g • v₁ + c g • w₀`; the leaf provides `t` with
`c g = t·(χ g − ψ g)`; then `W₁ := k·(v₁ + t • w₀)` is stable with
`ρ g` acting by `χ g` on it (`ρ g (v₁ + t•w₀) = χ g • v₁ +
(t·(χ g − ψ g) + t·ψ g) • w₀ = χ g • (v₁ + t•w₀)`), and since
`{v₁ + t•w₀, w₀}` spans `V` (the quotient `V/W₀` is the line spanned
by `mkQ v₁`), the quotient `V/W₁` is spanned by the image of `w₀`, on
which `ρ` acts through `ψ`. -/
theorem exists_line_with_quotCharacter_eq_subCharacter
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀fr : Module.finrank k W₀ = 1)
    (hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀)
    (ψ : Γ ℚ →* kˣ) (hψ : ∀ g, ∀ v ∈ W₀, ρ g v = (ψ g : k) • v)
    (χ : Γ ℚ →* kˣ)
    (hχ : ∀ g v, W₀.mkQ (ρ g v) = (χ g : k) • W₀.mkQ v)
    (h3 : ¬ (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker)) :
    ∃ W₁ : Submodule k V, Module.finrank k W₁ = 1 ∧
      (∀ g v, v ∈ W₁ → ρ g v ∈ W₁) ∧
      (∀ g v, W₁.mkQ (ρ g v) = (ψ g : k) • W₁.mkQ v) := by
  classical
  -- dimensions
  have hfr : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  have hQ1 : Module.finrank k (V ⧸ W₀) = 1 := by
    have hsum := Submodule.finrank_quotient_add_finrank W₀
    omega
  -- a spanning vector of the line `W₀`
  obtain ⟨w₀, hw₀, hw₀ne⟩ : ∃ w₀ ∈ W₀, w₀ ≠ (0 : V) := by
    by_contra hno
    push Not at hno
    have hbot : W₀ = ⊥ := (Submodule.eq_bot_iff W₀).mpr hno
    rw [hbot, finrank_bot] at hW₀fr
    omega
  -- every element of `W₀` is a multiple of `w₀`
  have hspan : ∀ y ∈ W₀, ∃ a : k, y = a • w₀ := by
    intro y hy
    have hne : (⟨w₀, hw₀⟩ : W₀) ≠ 0 := fun h =>
      hw₀ne (by simpa using congrArg Subtype.val h)
    have h1 : Submodule.span k {(⟨w₀, hw₀⟩ : W₀)} = ⊤ :=
      (finrank_eq_one_iff_of_nonzero _ hne).mp hW₀fr
    have h2 : (⟨y, hy⟩ : W₀) ∈ Submodule.span k {(⟨w₀, hw₀⟩ : W₀)} := by
      rw [h1]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h2
    exact ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  -- a complement vector
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : V, v₁ ∉ W₀ := by
    by_contra hno
    push Not at hno
    have htop : W₀ = ⊤ := Submodule.eq_top_iff'.mpr hno
    rw [htop, finrank_top] at hW₀fr
    omega
  -- the extension cocycle `c`
  have hmem : ∀ g : Γ ℚ, ρ g v₁ - (χ g : k) • v₁ ∈ W₀ := by
    intro g
    have h0 : W₀.mkQ (ρ g v₁ - (χ g : k) • v₁) = 0 := by
      rw [map_sub, map_smul, hχ g v₁, sub_self]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  choose cfun hcfun using fun g => hspan _ (hmem g)
  have hc : ∀ g : Γ ℚ, ρ g v₁ = (χ g : k) • v₁ + cfun g • w₀ := by
    intro g
    have h1 : (χ g : k) • v₁ + (ρ g v₁ - (χ g : k) • v₁) = ρ g v₁ := by
      abel
    rw [hcfun g] at h1
    exact h1.symm
  -- the splitting scalar of the sorried leaf
  obtain ⟨t, ht⟩ := exists_splitting_scalar_of_quot_ramified V hV hρ W₀
    hW₀fr hstable ψ hψ χ hχ h3 w₀ hw₀ hw₀ne v₁ hv₁ cfun hc
  -- the second line and its generator
  set x : V := v₁ + t • w₀ with hxdef
  have hgen : ∀ g : Γ ℚ, ρ g x = (χ g : k) • x := by
    intro g
    have h1 : ρ g x = ρ g v₁ + t • ρ g w₀ := by
      rw [hxdef, map_add, map_smul]
    rw [h1, hc g, hψ g w₀ hw₀, ht g, hxdef, smul_add]
    module
  have hxne : x ≠ 0 := by
    intro h0
    apply hv₁
    have h1 : v₁ = -(t • w₀) := by
      rw [hxdef] at h0
      exact eq_neg_of_add_eq_zero_left h0
    rw [h1]
    exact W₀.neg_mem (W₀.smul_mem t hw₀)
  refine ⟨Submodule.span k {x}, finrank_span_singleton hxne, ?_, ?_⟩
  · -- stability
    intro g v hv
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hgen g]
    exact Submodule.smul_mem _ s (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self x))
  · -- the quotient character is `ψ`: `{x, w₀}` spans `V`
    have hrepr : ∀ v : V, ∃ a bb : k, v = a • x + bb • w₀ := by
      intro v
      -- `mkQ v₁` spans the line `V ⧸ W₀`
      have hv₁ne : W₀.mkQ v₁ ≠ 0 := by
        intro h0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
        exact hv₁ h0
      have hspanQ : Submodule.span k {W₀.mkQ v₁} = ⊤ :=
        (finrank_eq_one_iff_of_nonzero _ hv₁ne).mp hQ1
      have hmemQ : W₀.mkQ v ∈ Submodule.span k {W₀.mkQ v₁} := by
        rw [hspanQ]
        exact Submodule.mem_top
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmemQ
      have hvmem : v - μ • v₁ ∈ W₀ := by
        have h0 : W₀.mkQ (v - μ • v₁) = 0 := by
          rw [map_sub, map_smul, hμ, sub_self]
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      obtain ⟨bb₀, hbb₀⟩ := hspan _ hvmem
      refine ⟨μ, bb₀ - μ * t, ?_⟩
      have hveq : v = μ • v₁ + bb₀ • w₀ := by
        have h1 : μ • v₁ + (v - μ • v₁) = v := by abel
        rw [hbb₀] at h1
        exact h1.symm
      rw [hveq, hxdef]
      module
    intro g v
    obtain ⟨a, bb, rfl⟩ := hrepr v
    have hx0 : (Submodule.span k {x}).mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_span_singleton_self x
    have hL : ρ g (a • x + bb • w₀) =
        a • ((χ g : k) • x) + bb • ((ψ g : k) • w₀) := by
      rw [map_add, map_smul, map_smul, hgen g, hψ g w₀ hw₀]
    rw [hL]
    simp only [map_add, map_smul, hx0, smul_zero, zero_add]
    rw [smul_comm]

/-- **The stable line with unramified-at-`3` quotient character**
(DECOMPOSED 2026-07-22 into the two sorry nodes above — the Raynaud
dichotomy `subCharacter_unramified_at_three_of_quot_ramified` and the
Serre swap `exists_line_with_quotCharacter_eq_subCharacter`): a
reducible mod-3 hardly ramified representation has a stable LINE whose
quotient character is unramified at `3`. Assembly: the given stable
submodule is a line with sub-character `ψ` and quotient character `χ`;
either `χ` is already unramified at `3` (take `W₀`), or the Raynaud
dichotomy makes `ψ` unramified at `3` and the Serre swap provides a
second stable line whose quotient character is `ψ`. -/
theorem exists_line_with_unramified_quotCharacter_at_three
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀0 : W₀ ≠ ⊥) (hW₀top : W₀ ≠ ⊤)
    (hW₀stable : ∀ g : Γ ℚ, W₀.map (ρ g) ≤ W₀) :
    ∃ (W : Submodule k V) (χ₂ : Γ ℚ →* kˣ),
      Module.finrank k W = 1 ∧
      (∀ g v, v ∈ W → ρ g v ∈ W) ∧
      (∀ g v, W.mkQ (ρ g v) = (χ₂ g : k) • W.mkQ v) ∧
      (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) := by
  classical
  -- the given stable submodule is a line with a line quotient
  have hfr : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  have hstable : ∀ g v, v ∈ W₀ → ρ g v ∈ W₀ := fun g v hv =>
    hW₀stable g ⟨v, hv, rfl⟩
  have hW₀fr : Module.finrank k W₀ = 1 := by
    have hle : Module.finrank k W₀ ≤ 2 := hfr ▸ Submodule.finrank_le W₀
    have h0 : Module.finrank k W₀ ≠ 0 := fun h0 =>
      hW₀0 (Submodule.finrank_eq_zero.mp h0)
    have h2 : Module.finrank k W₀ ≠ 2 := fun h2 =>
      hW₀top (Submodule.eq_top_of_finrank_eq (h2.trans hfr.symm))
    omega
  have hQ1 : Module.finrank k (V ⧸ W₀) = 1 := by
    have hsum := Submodule.finrank_quotient_add_finrank W₀
    omega
  obtain ⟨χ, hχ⟩ := exists_quotCharacter ρ W₀ hQ1 hstable
  by_cases h3 : localInertiaGroup
      Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
    (χ.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker
  · -- the quotient character of `W₀` is already unramified at `3`
    exact ⟨W₀, χ, hW₀fr, hstable, hχ, h3⟩
  · -- the Serre swap: the second line, whose quotient character is the
    -- sub-character of `W₀`, unramified at `3` by the Raynaud dichotomy
    obtain ⟨ψ, hψ⟩ := exists_subCharacter ρ W₀ hW₀fr hstable
    obtain ⟨W₁, hW₁fr, hW₁stable, hW₁χ⟩ :=
      exists_line_with_quotCharacter_eq_subCharacter V hV hρ W₀ hW₀fr
        hstable ψ hψ χ hχ h3
    exact ⟨W₁, ψ, hW₁fr, hW₁stable, hW₁χ,
      subCharacter_unramified_at_three_of_quot_ramified V hV hρ W₀ hW₀fr
        hstable ψ hψ χ hχ h3⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The mod-3 cyclotomic character is unramified at `2`** (PROVEN
2026-07-18 — the arithmetic input of the at-`2` bookkeeping): the composite of the
3-adic cyclotomic character with `algebraMap ℤ_[3] k` (which kills the
level-`>1` information since `k` has characteristic `3`) is trivial on
the image of the inertia at `2`. Content: an inertia element fixes the
cube roots of unity in `ℚ_[2]ᵃˡᵍ` (they are units congruent to distinct
residues: `|ζ₃ − 1|₂ = 1` since `3` is a unit at `2`), so by the
`lift_map` commuting square its image in `Γ ℚ` fixes the cube roots in
`ℚᵃˡᵍ`, making `χ₃ ≡ 1` at level one, and `algebraMap ℤ_[3] k` sees
only level one. -/
theorem cyclotomicCharacter_algebraMap_eq_one_of_inertia_two
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    {σ : Γ ℚ_[2]}
    (hσ : σ ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Γ ℚ_[2])) :
    algebraMap ℤ_[3] k
      ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])
          σ).toRingEquiv) : ℤ_[3]ˣ) : ℤ_[3]) = 1 := by
  haveI h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  classical
  set g' : Γ ℚ := Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ
    with hg'
  -- a primitive cube root of unity in `ℚᵃˡᵍ` and its image in `ℚ_[2]ᵃˡᵍ`
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot
    (AlgebraicClosure ℚ) 3
  have hzprim : IsPrimitiveRoot
      (AlgebraicClosure.map (algebraMap ℚ ℚ_[2]) ζ) 3 :=
    hζ.map_of_injective (AlgebraicClosure.map (algebraMap ℚ ℚ_[2])).injective
  set z : AlgebraicClosure ℚ_[2] :=
    AlgebraicClosure.map (algebraMap ℚ ℚ_[2]) ζ
  have hz3 : z ^ 3 = 1 := hzprim.pow_eq_one
  -- roots of unity have valuation `1`
  have hval_of_root : ∀ w : AlgebraicClosure ℚ_[2], w ^ 3 = 1 →
      Valued.v w = 1 := by
    intro w hw
    have h := congrArg Valued.v hw
    rw [map_pow, map_one] at h
    rcases lt_trichotomy (Valued.v w) 1 with hlt | heq | hgt
    · exfalso
      have hcon : Valued.v w ^ 3 < 1 := by
        calc Valued.v w ^ 3 ≤ Valued.v w ^ 1 :=
              pow_le_pow_right_of_le_one' (le_of_lt hlt) (by norm_num)
          _ = Valued.v w := pow_one _
          _ < 1 := hlt
      rw [h] at hcon
      exact lt_irrefl _ hcon
    · exact heq
    · exfalso
      have hcon : 1 < Valued.v w ^ 3 := by
        calc 1 < Valued.v w := hgt
          _ = Valued.v w ^ 1 := (pow_one _).symm
          _ ≤ Valued.v w ^ 3 := pow_le_pow_right' (le_of_lt hgt) (by norm_num)
      rw [h] at hcon
      exact lt_irrefl _ hcon
  have hzval : Valued.v z = 1 := hval_of_root z hz3
  have hzmem : z ∈ Z2bar := by
    rw [Valuation.mem_valuationSubring_iff, hzval]
  -- the inertia element fixes `z`
  have hfix2 : σ z = z := by
    by_contra hne
    -- `σ z` is a cube root of unity, hence a power of `z`
    have hσz3 : (σ z) ^ 3 = 1 := by
      rw [← map_pow, hz3, map_one]
    obtain ⟨i, hi3, hiz⟩ := hzprim.eq_pow_of_pow_eq_one hσz3
    -- the inertia condition: `σ z − z` has valuation `< 1`
    have hdiff := (AddSubgroup.mem_inertia.mp hσ) ⟨z, hzmem⟩
    have hdiffval : Valued.v (σ z - z) < 1 := by
      set y : Z2bar := σ • (⟨z, hzmem⟩ : Z2bar) - ⟨z, hzmem⟩
      have hy1 : (y : AlgebraicClosure ℚ_[2]) = σ z - z := rfl
      have hnu : ¬IsUnit y := by
        have hmem : y ∈ IsLocalRing.maximalIdeal Z2bar := hdiff
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
      have hyval : Valued.v (σ z - z) ≤ 1 := by
        refine le_trans (Valued.v.map_sub _ _) ?_
        rw [show Valued.v (σ z) = 1 from hval_of_root _ hσz3, hzval]
        exact le_of_eq (max_self 1)
      rcases lt_or_eq_of_le hyval with hlt | heq
      · exact hlt
      · exfalso
        apply hnu
        have hne0 : (σ z - z : AlgebraicClosure ℚ_[2]) ≠ 0 := by
          intro h0
          rw [h0, map_zero] at heq
          exact zero_ne_one heq
        have hinvmem : (σ z - z : AlgebraicClosure ℚ_[2])⁻¹ ∈ Z2bar := by
          rw [Valuation.mem_valuationSubring_iff, map_inv₀, heq, inv_one]
        refine isUnit_iff_exists.mpr
          ⟨(⟨(σ z - z)⁻¹, hinvmem⟩ : Z2bar), ?_, ?_⟩
        · apply Subtype.ext
          show (y : AlgebraicClosure ℚ_[2]) * (σ z - z)⁻¹ = 1
          rw [hy1]
          exact mul_inv_cancel₀ hne0
        · apply Subtype.ext
          show (σ z - z)⁻¹ * (y : AlgebraicClosure ℚ_[2]) = 1
          rw [hy1]
          exact inv_mul_cancel₀ hne0
    interval_cases i
    · -- `σ z = 1` forces `z = 1`, impossible for a primitive root
      rw [pow_zero] at hiz
      exact hzprim.ne_one (by norm_num)
        (σ.injective (by rw [← hiz, map_one]))
    · -- `σ z = z` contradicts the assumption
      rw [pow_one] at hiz
      exact hne hiz.symm
    · -- `σ z = z²`: then `z² − z ∈ 𝔪`, but its valuation is `1`
      rw [← hiz] at hdiffval
      -- `z² − z = z (z − 1)` and `(z − 1)² = −3z` since `1 + z + z² = 0`
      have hsum : 1 + z + z ^ 2 = 0 := by
        have h := hzprim.geom_sum_eq_zero (by norm_num)
        rw [Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ, Finset.sum_range_zero] at h
        rw [pow_zero, pow_one] at h
        rw [← h]
        ring
      have hfactor : (z - 1) ^ 2 = -3 * z := by
        have h2 : z ^ 2 = -1 - z := by linear_combination hsum
        calc (z - 1) ^ 2 = z ^ 2 - 2 * z + 1 := by ring
          _ = (-1 - z) - 2 * z + 1 := by rw [h2]
          _ = -3 * z := by ring
      have hval31 : Valued.v (-3 * z : AlgebraicClosure ℚ_[2]) = 1 := by
        rw [map_mul, hzval, mul_one, Valuation.map_neg]
        -- `3` is a unit at `2`
        have h3norm : ‖(3 : ℚ_[2])‖ = 1 := by
          rw [show ((3 : ℚ_[2])) = ((3 : ℕ) : ℚ_[2]) by norm_cast]
          rw [Padic.norm_natCast_eq_one_iff]
          decide
        have h3alg : (3 : AlgebraicClosure ℚ_[2]) =
            algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) 3 := by
          rw [map_ofNat]
        have h3ne : (3 : AlgebraicClosure ℚ_[2]) ≠ 0 := by
          norm_num
        have h3le : Valued.v (3 : AlgebraicClosure ℚ_[2]) ≤ 1 := by
          have hmem : (3 : AlgebraicClosure ℚ_[2]) ∈ Z2bar := by
            rw [h3alg, algebraMap_mem_Z2bar_iff, h3norm]
          rwa [Valuation.mem_valuationSubring_iff] at hmem
        have h3invle : (Valued.v (3 : AlgebraicClosure ℚ_[2]))⁻¹ ≤ 1 := by
          have hmem : (3 : AlgebraicClosure ℚ_[2])⁻¹ ∈ Z2bar := by
            rw [h3alg, ← map_inv₀, algebraMap_mem_Z2bar_iff, norm_inv,
              h3norm, inv_one]
          rw [Valuation.mem_valuationSubring_iff, map_inv₀] at hmem
          exact hmem
        have h3vne : Valued.v (3 : AlgebraicClosure ℚ_[2]) ≠ 0 :=
          (Valuation.ne_zero_iff _).mpr h3ne
        refine le_antisymm h3le ?_
        calc (1 : _) = Valued.v (3 : AlgebraicClosure ℚ_[2]) *
              (Valued.v (3 : AlgebraicClosure ℚ_[2]))⁻¹ :=
            (mul_inv_cancel₀ h3vne).symm
          _ ≤ Valued.v (3 : AlgebraicClosure ℚ_[2]) * 1 :=
            mul_le_mul_right h3invle _
          _ = Valued.v (3 : AlgebraicClosure ℚ_[2]) := mul_one _
      have hvalz1 : Valued.v (z - 1) = 1 := by
        have h := congrArg Valued.v hfactor
        rw [map_pow, hval31] at h
        -- `a² = 1 → a = 1` in the value group
        rcases lt_trichotomy (Valued.v (z - 1)) 1 with hlt | heq | hgt
        · exfalso
          have hcon : Valued.v (z - 1) ^ 2 < 1 := by
            calc Valued.v (z - 1) ^ 2 ≤ Valued.v (z - 1) ^ 1 :=
                  pow_le_pow_right_of_le_one' (le_of_lt hlt) (by norm_num)
              _ = Valued.v (z - 1) := pow_one _
              _ < 1 := hlt
          rw [h] at hcon
          exact lt_irrefl _ hcon
        · exact heq
        · exfalso
          have hcon : 1 < Valued.v (z - 1) ^ 2 := by
            calc 1 < Valued.v (z - 1) := hgt
              _ = Valued.v (z - 1) ^ 1 := (pow_one _).symm
              _ ≤ Valued.v (z - 1) ^ 2 :=
                  pow_le_pow_right' (le_of_lt hgt) (by norm_num)
          rw [h] at hcon
          exact lt_irrefl _ hcon
      have hval_prod : Valued.v (z ^ 2 - z) = 1 := by
        have hfac2 : z ^ 2 - z = z * (z - 1) := by ring
        rw [hfac2, map_mul, hzval, one_mul, hvalz1]
      rw [hval_prod] at hdiffval
      exact lt_irrefl _ hdiffval
  -- transport: `g'` fixes `ζ` in `ℚᵃˡᵍ`
  have hfix : g' ζ = ζ := by
    apply (AlgebraicClosure.map (algebraMap ℚ ℚ_[2])).injective
    rw [hg']
    rw [Field.absoluteGaloisGroup.lift_map (algebraMap ℚ ℚ_[2]) σ ζ]
    exact hfix2
  -- level one of the cyclotomic character is `1`
  have hlevel : (PadicInt.toZModPow 1)
      ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
        (g'.toRingEquiv) : ℤ_[3]ˣ) : ℤ_[3]) = 1 := by
    have hspec := cyclotomicCharacter.spec 3 (n := 1) g'.toRingEquiv ζ
      (by rw [pow_one]; exact hζ.pow_eq_one)
    have hζspec : ζ = ζ ^ ((PadicInt.toZModPow 1)
        ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
          (g'.toRingEquiv) : ℤ_[3]ˣ) : ℤ_[3])).val := by
      rw [← hspec]
      exact hfix.symm
    have hval_lt : ((PadicInt.toZModPow 1)
        ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
          (g'.toRingEquiv) : ℤ_[3]ˣ) : ℤ_[3])).val < 3 ^ 1 :=
      ZMod.val_lt _
    have h1 := hζ.pow_inj (by norm_num : (1 : ℕ) < 3 ^ 1)
      (by exact_mod_cast hval_lt) (by rw [pow_one]; exact hζspec)
    have h2 : ((PadicInt.toZModPow 1)
        ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
          (g'.toRingEquiv) : ℤ_[3]ˣ) : ℤ_[3])).val = 1 := h1.symm
    have h3v : ((1 : ZMod (3 ^ 1))).val = 1 := rfl
    exact ZMod.val_injective _ (h2.trans h3v.symm)
  -- `algebraMap ℤ_[3] k` sees only level one (`k` has characteristic 3)
  haveI hchark : CharP k 3 := charP_three_of_finite_padicIntThree_algebra
  have hker : ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
      (g'.toRingEquiv) : ℤ_[3]ˣ) : ℤ_[3]) - 1 ∈
      RingHom.ker (PadicInt.toZModPow (p := 3) 1) := by
    rw [RingHom.mem_ker, map_sub, hlevel, map_one, sub_self]
  rw [PadicInt.ker_toZModPow] at hker
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hker
  have hx : ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
      (g'.toRingEquiv) : ℤ_[3]ˣ) : ℤ_[3]) =
      1 + t * ((3 : ℕ) : ℤ_[3]) ^ 1 := by
    linear_combination -ht
  rw [hg'] at hx ⊢
  rw [hx, map_add, map_one, map_mul, map_pow, map_natCast]
  rw [show ((3 : ℕ) : k) = 0 from CharP.cast_eq_zero k 3]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 8000000 in
/-- **The inertia bridge at `2`** (FULLY PROVEN 2026-07-18 — completion
bookkeeping, stated up to conjugacy since the two local worlds involve
different choices of embedding of `ℚᵃˡᵍ`): every element of the local
inertia group at the place `prime_two` (phrased at the adic completion
of `ℚ`) has, up to conjugation in `Γ ℚ`, the same image as some element
of the inertia at `2` phrased over `ℚ_[2]` (via `Z2bar`). Content: the
continuous `ℚ`-algebra isomorphism `adicCompletion ℚ v₂ ≃ ℚ_[2]`
(`Rat.HeightOneSpectrum.adicCompletion.padicEquiv`) induces an
isomorphism of the algebraic closures matching the two inertia
subgroups (the spectral valuation is preserved); the two resulting
embeddings of `ℚᵃˡᵍ` differ by an automorphism `c ∈ Γ ℚ`, which
conjugates one image onto the other. The conjugacy slack is harmless
downstream: quotient characters are conjugation-invariant. -/
theorem localInertia_two_eq_map_padic
    {σ : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)}
    (hσ : σ ∈ localInertiaGroup
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :
    ∃ τ ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Γ ℚ_[2]), ∃ c : Γ ℚ,
      Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ =
      c * Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ * c⁻¹ := by
  classical
  haveI h2f : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- (1) the completion at the place of `2` is `ℚ_[2]`
  haveI hfp : Fact ((Rat.HeightOneSpectrum.primesEquiv
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat).2⟩
  have hprime : ((Rat.HeightOneSpectrum.primesEquiv
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) : ℕ) = 2 := by
    show Rat.HeightOneSpectrum.natGenerator _ = 2
    exact natGenerator_toHeightOneSpectrum Nat.prime_two
  have hcastP : ∀ (a b : ℕ) (ha : Fact a.Prime) (hb : Fact b.Prime),
      a = b → { F : (@Padic a ha) ≃A[ℚ] (@Padic b hb) //
        ∀ y, ‖F y‖ = ‖y‖ } := by
    intro a b ha hb hab
    subst hab
    have hinst : ha = hb := Subsingleton.elim _ _
    subst hinst
    exact ⟨ContinuousAlgEquiv.refl ℚ _, fun y => rfl⟩
  obtain ⟨E, hEint⟩ : ∃ E : (IsDedekindDomain.HeightOneSpectrum.adicCompletion
      ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat ≃A[ℚ] ℚ_[2]),
      ∀ x, x ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat ↔ ‖E x‖ ≤ 1 := by
    letI : Algebra ℚ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
      IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion _ _ _
    set h0 := Rat.HeightOneSpectrum.adicCompletion.padicEquiv
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat
    have hbij := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat
    have h0int : ∀ x, x ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
        ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat ↔
        ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat x‖ ≤ 1 := by
      intro x
      constructor
      · intro hx
        exact hbij.mapsTo hx
      · intro hx
        obtain ⟨x', hx', hEx⟩ := hbij.surjOn hx
        have hxx' : x' = x := by
          have h1 := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat).symm hEx
          simpa using h1
        rwa [← hxx']
    have hpair : ∃ E : (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat ≃A[ℚ] ℚ_[2]),
        ∀ x, x ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat ↔ ‖E x‖ ≤ 1 := by
      refine ⟨h0.trans (hcastP _ 2 hfp h2f hprime).1,
        fun x => (h0int x).trans ?_⟩
      have hnorm : ‖(h0.trans (hcastP _ 2 hfp h2f hprime).1) x‖ =
          ‖h0 x‖ := by
        rw [show (h0.trans (hcastP _ 2 hfp h2f hprime).1) x =
          (hcastP _ 2 hfp h2f hprime).1 (h0 x) from rfl]
        exact (hcastP _ 2 hfp h2f hprime).2 (h0 x)
      rw [hnorm]
    have halg : (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (NumberField.RingOfIntegers ℚ) ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) =
        (DivisionRing.toRatAlgebra) := Subsingleton.elim _ _
    exact halg ▸ hpair
  -- (2) the transported element: conjugation through the closure map of
  -- `E.symm`, which is bijective
  set ι₃ : AlgebraicClosure ℚ_[2] →+*
      AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
    AlgebraicClosure.map (E.symm : ℚ_[2] →+*
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) with hι₃
  have hι₃surj : Function.Surjective ι₃ := by
    set g : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) →+*
        AlgebraicClosure ℚ_[2] :=
      AlgebraicClosure.map (E : IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat →+* ℚ_[2]) with hg
    set hcomp : AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion
        ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) →ₐ[
          IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat]
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion
          ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
      { toRingHom := ι₃.comp g
        commutes' := fun x => by
          show ι₃ (g (algebraMap _ _ x)) = algebraMap _ _ x
          rw [hg, AlgebraicClosure.map_algebraMap, hι₃,
            AlgebraicClosure.map_algebraMap]
          congr 1
          exact E.symm_apply_apply x }
    have hbij := Algebra.IsAlgebraic.algHom_bijective hcomp
    intro y
    obtain ⟨x, hx⟩ := hbij.2 y
    exact ⟨g x, hx⟩
  set ι₃e : AlgebraicClosure ℚ_[2] ≃+*
      AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
    RingEquiv.ofBijective ι₃ ⟨ι₃.injective, hι₃surj⟩
  have hι₃e_apply : ∀ y, ι₃e y = ι₃ y := fun y => rfl
  -- `τ := ι₃⁻¹ ∘ σ ∘ ι₃`, an automorphism over `ℚ_[2]`
  set τ₀ : AlgebraicClosure ℚ_[2] ≃+* AlgebraicClosure ℚ_[2] :=
    (ι₃e.trans σ.toRingEquiv).trans ι₃e.symm
  have hτ₀_apply : ∀ y, τ₀ y = ι₃e.symm (σ (ι₃e y)) := fun y => rfl
  set τ : Γ ℚ_[2] := AlgEquiv.ofRingEquiv (f := τ₀) (fun x => by
    rw [hτ₀_apply, RingEquiv.symm_apply_eq]
    show σ (ι₃ ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])) x)) =
      ι₃ ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])) x)
    rw [hι₃, AlgebraicClosure.map_algebraMap]
    exact σ.commutes (E.symm x))
  have hτ_apply : ∀ y, τ y = ι₃e.symm (σ (ι₃e y)) := fun y => rfl
  -- the transport square, by construction
  have hsquare : ∀ y, ι₃ (τ y) = σ (ι₃ y) := by
    intro y
    rw [← hι₃e_apply, hτ_apply, RingEquiv.apply_symm_apply, hι₃e_apply]
  refine ⟨τ, ?_, ?_⟩
  · -- (3) inertia membership: `ι₃` maps `Z2bar` into the integral
    -- closure (integral equations transport through `E.symm` on
    -- coefficients), and nonunits transport forward through the induced
    -- ring hom, so the inertia condition follows from `hσ`
    rw [AddSubgroup.mem_inertia]
    intro x
    have hEsymm_int : ∀ a : ℚ_[2], ‖a‖ ≤ 1 →
        (E.symm : ℚ_[2] →+* IsDedekindDomain.HeightOneSpectrum.adicCompletion
          ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) a ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat := by
      intro a ha
      refine (hEint _).mpr ?_
      rw [show E ((E.symm : ℚ_[2] →+* _) a) = a from E.apply_symm_apply a]
      exact ha
    -- the coefficient transport hom on the `2`-adic unit ball
    set Es : ℚ_[2] →+* IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat :=
      (E.symm : ℚ_[2] →+*
        IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
    set φ : (PadicInt.subring 2) →+*
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
      RingHom.codRestrict (Es.comp (PadicInt.subring 2).subtype)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat).toSubring
        (fun a => hEsymm_int a.1 a.2)
    -- `ι₃` maps `Z2bar` into the integral closure of `𝒪ᵥ₂`
    have hmemIC : ∀ w : AlgebraicClosure ℚ_[2], w ∈ Z2bar →
        IsIntegral (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
          ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) (ι₃ w) := by
      intro w hw
      have hnorm : spectralNorm ℚ_[2] (AlgebraicClosure ℚ_[2]) w ≤ 1 := hw
      -- the minimal polynomial has `2`-adic integer coefficients (as in
      -- `isIntegral_of_spectralNorm_le_one`)
      have hlift : minpoly ℚ_[2] w ∈ Polynomial.lifts
          (PadicInt.subring 2).subtype := by
        refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
        have hterm := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp
          hnorm i
        simp only [spectralValueTerms] at hterm
        split_ifs at hterm with h
        · conv_rhs at hterm => rw [← Real.one_rpow
            (1 / (↑(minpoly ℚ_[2] w).natDegree - ↑i) : ℝ)]
          rw [Real.rpow_le_rpow_iff (by positivity) (by positivity)
            (by aesop)] at hterm
          exact ⟨⟨_, hterm⟩, rfl⟩
        obtain h | h := (le_of_not_gt h).eq_or_lt
        · exact ⟨1, by
            rw [map_one, ← h, (minpoly.monic
              (Algebra.IsAlgebraic.isAlgebraic w).isIntegral).coeff_natDegree]⟩
        · exact ⟨0, by
            rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]⟩
      obtain ⟨P, hP, -, hP'⟩ := Polynomial.lifts_and_degree_eq_and_monic
        hlift (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic w).isIntegral)
      -- transport the integral equation through `φ`
      refine ⟨P.map φ, hP'.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : ((algebraMap
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion
            ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))).comp φ) =
          (ι₃ : AlgebraicClosure ℚ_[2] →+* _).comp
            ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])).comp
              (PadicInt.subring 2).subtype) := by
        ext a
        show algebraMap _ _ (φ a) =
          ι₃ (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) a.1)
        rw [hι₃, AlgebraicClosure.map_algebraMap]
        rw [IsScalarTower.algebraMap_apply
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion
            ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) (φ a)]
        rfl
      rw [hcomp]
      rw [show Polynomial.eval₂ ((ι₃ : AlgebraicClosure ℚ_[2] →+* _).comp
          ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])).comp
            (PadicInt.subring 2).subtype)) (ι₃ w) P =
        ι₃ (Polynomial.eval₂ ((algebraMap ℚ_[2]
          (AlgebraicClosure ℚ_[2])).comp (PadicInt.subring 2).subtype) w P)
        from (Polynomial.hom_eval₂ _ _ _ _).symm]
      have hev : Polynomial.eval₂ ((algebraMap ℚ_[2]
          (AlgebraicClosure ℚ_[2])).comp (PadicInt.subring 2).subtype) w P
          = 0 := by
        rw [← Polynomial.eval₂_map, hP]
        rw [← Polynomial.aeval_def, minpoly.aeval]
      rw [hev, map_zero]
    -- the induced ring hom `Z2bar →+* IntegralClosure`
    set Φ : Z2bar →+* IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion
          ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) :=
      RingHom.codRestrict ((ι₃ : AlgebraicClosure ℚ_[2] →+* _).comp
        Z2bar.subtype)
        (integralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))).toSubring
        (fun z => hmemIC z.1 z.2)
    -- transport the inertia condition
    set y : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion
          ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) :=
      ⟨ι₃ x.1, hmemIC x.1 x.2⟩
    have hIC := (AddSubgroup.mem_inertia.mp hσ) y
    rw [Submodule.mem_toAddSubgroup, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at hIC
    rw [Submodule.mem_toAddSubgroup, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    apply hIC
    have hΦeq : Φ (τ • x - x) = σ • y - y := by
      apply Subtype.ext
      have h1 : (Φ (τ • x - x)).1 =
          ι₃ (τ (x : AlgebraicClosure ℚ_[2]) -
            (x : AlgebraicClosure ℚ_[2])) := rfl
      have h2 : (σ • y - y).1 = σ y.1 - y.1 := by
        rw [show (σ • y - y).1 = (σ • y).1 - y.1 from rfl,
          IntegralClosure.coe_smul]
        rfl
      rw [h1, h2, map_sub, hsquare]
    rw [← hΦeq]
    exact hu.map Φ
  · -- (4) the conjugator, from `Normal.algHomEquivAut`
    set ι₁ := AlgebraicClosure.map ((algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)))
    set ι₂ := AlgebraicClosure.map (algebraMap ℚ ℚ_[2])
    letI : Algebra (AlgebraicClosure ℚ)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) :=
      ι₁.toAlgebra
    haveI : IsScalarTower ℚ (AlgebraicClosure ℚ)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) :=
      IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    set f : AlgebraicClosure ℚ →ₐ[ℚ]
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
      (ι₃.comp ι₂).toRatAlgHom
    set c : Γ ℚ := (Normal.algHomEquivAut (F := ℚ)
      (K₁ := AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))
      (E := AlgebraicClosure ℚ)) f with hc
    have hfc : ∀ x : AlgebraicClosure ℚ, f x = ι₁ (c x) := by
      intro x
      have h : f = (Normal.algHomEquivAut (F := ℚ)
          (K₁ := AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
              Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))
          (E := AlgebraicClosure ℚ)).symm c := by
        rw [hc, Equiv.symm_apply_apply]
      rw [h, Normal.algHomEquivAut_symm_apply]
      rfl
    refine ⟨c, ?_⟩
    -- (5) the square, pointwise through the injective `ι₁`
    apply AlgEquiv.ext
    intro x
    apply ι₁.injective
    have hL := Field.absoluteGaloisGroup.lift_map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ x
    have hR2 := Field.absoluteGaloisGroup.lift_map (algebraMap ℚ ℚ_[2]) τ
      (c⁻¹ x)
    -- LHS
    rw [show ι₁ ((Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) σ) x) =
      σ (ι₁ x) from hL]
    -- RHS
    show σ (ι₁ x) = ι₁ ((c) ((Field.absoluteGaloisGroup.map
      (algebraMap ℚ ℚ_[2]) τ) (c⁻¹ x)))
    rw [← hfc]
    rw [show f ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ)
      (c⁻¹ x)) = ι₃ (ι₂ ((Field.absoluteGaloisGroup.map
        (algebraMap ℚ ℚ_[2]) τ) (c⁻¹ x))) from rfl]
    rw [show ι₂ ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) τ)
      (c⁻¹ x)) = τ (ι₂ (c⁻¹ x)) from hR2]
    rw [hsquare]
    rw [show ι₃ (ι₂ (c⁻¹ x)) = f (c⁻¹ x) from rfl]
    rw [hfc]
    rw [show (c : Γ ℚ) ((c⁻¹ : Γ ℚ) x) = x from by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Quotient characters of stable lines are killed by the `ℚ_[2]`
inertia** (DERIVED 2026-07-18 — the tame dichotomy): for any stable
line `W` of a mod-3 hardly ramified representation with quotient
character `χ₂`, the inertia at `2` (phrased over `ℚ_[2]`, matching
`isTameAtTwo`) lies in the kernel of `χ₂` composed with the local
inclusion. Either `W` maps into the kernel of the tame quotient `π₂` —
then `χ₂` agrees with the unramified `δ` on inertia — or `π₂` is
nonzero on `W` — then the sub-character agrees with `δ`, so it is
trivial on inertia, and `χ₂ = det/χ₁` is trivial there too since the
determinant is the mod-3 cyclotomic character, unramified at `2`. -/
theorem quotCharacter_inertia_two_ker
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W : Submodule k V) (χ₂ : Γ ℚ →* kˣ)
    (hWfr : Module.finrank k W = 1)
    (hWstable : ∀ g v, v ∈ W → ρ g v ∈ W)
    (hχ₂ : ∀ g v, W.mkQ (ρ g v) = (χ₂ g : k) • W.mkQ v) :
    AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Γ ℚ_[2]) ≤
      (χ₂.comp (Field.absoluteGaloisGroup.map
        (algebraMap ℚ ℚ_[2])).toMonoidHom).ker := by
  classical
  intro σ hσ
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  set g' : Γ ℚ := Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) σ
    with hg'
  obtain ⟨π₂, hπsurj, δ, hδ⟩ := hρ.isTameAtTwo
  -- `δ` is trivial on inertia
  have hδσ : δ σ = 1 := by
    have h := (hδ σ 0).2.1 hσ
    rwa [GaloisRep.ker, MonoidHom.mem_ker] at h
  -- the tame relation at `σ`, rewritten through the global action
  have hrel : ∀ v : V, π₂ (ρ g' v) = π₂ v := by
    intro v
    have h := (hδ σ v).1
    rw [GaloisRep.map_apply, ← hg'] at h
    rw [h, hδσ, Module.End.one_apply]
  -- the goal, at the level of `k`
  suffices hval : (χ₂ g' : k) = 1 by
    apply Units.ext
    simpa using hval
  by_cases hcase : W ≤ LinearMap.ker π₂
  · -- `π₂` factors through the quotient, so `χ₂` scales `π₂`
    obtain ⟨v₀, hv₀⟩ := hπsurj 1
    have hfac : ∀ v : V, π₂ v =
        (W.liftQ π₂ hcase) (W.mkQ v) := by
      intro v
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
    have h1 : π₂ (ρ g' v₀) = (χ₂ g' : k) * π₂ v₀ := by
      rw [hfac, hχ₂ g' v₀, map_smul, smul_eq_mul, ← hfac]
    rw [hrel v₀, hv₀, mul_one] at h1
    exact h1.symm
  · -- `π₂` is nonzero on `W`: the sub-character is trivial on inertia
    obtain ⟨w₀, hw₀W, hw₀ne⟩ : ∃ w ∈ W, π₂ w ≠ 0 := by
      by_contra hnone
      push Not at hnone
      exact hcase fun w hw => LinearMap.mem_ker.mpr (hnone w hw)
    obtain ⟨χ₁, hχ₁⟩ := exists_subCharacter ρ W hWfr hWstable
    have hχ₁σ : (χ₁ g' : k) = 1 := by
      have h1 : π₂ (ρ g' w₀) = (χ₁ g' : k) * π₂ w₀ := by
        rw [hχ₁ g' w₀ hw₀W, map_smul, smul_eq_mul]
      rw [hrel w₀] at h1
      have h2 : ((χ₁ g' : k) - 1) * π₂ w₀ = 0 := by
        rw [sub_mul, one_mul, ← h1, sub_self]
      rcases mul_eq_zero.mp h2 with h' | h'
      · linear_combination h'
      · exact absurd h' hw₀ne
    -- the determinant is `χ₁ · χ₂` and also the cyclotomic character
    have hfr : Module.finrank k V = 2 :=
      Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
    have hQ1 : Module.finrank k (V ⧸ W) = 1 := by
      have h := Submodule.finrank_quotient_add_finrank W
      omega
    have hdet := det_eq_subCharacter_mul_quotCharacter ρ W hWfr hQ1
      hWstable χ₁ χ₂ hχ₁ hχ₂ g'
    have hcyc := hρ.det g'
    rw [GaloisRep.det_apply] at hcyc
    rw [hcyc] at hdet
    have hone := cyclotomicCharacter_algebraMap_eq_one_of_inertia_two
      (k := k) hσ
    rw [← hg'] at hone
    rw [hone, hχ₁σ, one_mul] at hdet
    exact hdet.symm

set_option backward.isDefEq.respectTransparency false in
/-- **Quotient characters of stable lines are unramified at `2`**
(DERIVED 2026-07-18 from the `ℚ_[2]` dichotomy and the inertia
bridge): for any stable line `W` of a mod-3 hardly ramified
representation with quotient character `χ₂`, the local inertia at the
place `prime_two` lies in the kernel of `χ₂`. -/
theorem quotCharacter_unramified_at_two
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W : Submodule k V) (χ₂ : Γ ℚ →* kˣ)
    (hWfr : Module.finrank k W = 1)
    (hWstable : ∀ g v, v ∈ W → ρ g v ∈ W)
    (hχ₂ : ∀ g v, W.mkQ (ρ g v) = (χ₂ g : k) • W.mkQ v) :
    localInertiaGroup Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat ≤
      (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker := by
  intro σ hσ
  obtain ⟨τ, hτ, c, heq⟩ := localInertia_two_eq_map_padic hσ
  have h := quotCharacter_inertia_two_ker V hV hρ W χ₂ hWfr hWstable hχ₂ hτ
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h ⊢
  show χ₂ ((Field.absoluteGaloisGroup.map (algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) σ) = 1
  rw [heq]
  -- characters are conjugation-invariant
  rw [map_mul, map_mul, map_inv]
  rw [show χ₂ ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2])) τ) = 1
    from h]
  group

set_option backward.isDefEq.respectTransparency false in
/-- **The stable line with locally-unramified quotient character at
`2` and `3`** (DERIVED 2026-07-18 from the at-`3` Serre-swap leaf and
the at-`2` tame bookkeeping leaf): a reducible mod-3 hardly ramified
representation has a stable LINE whose quotient character is unramified
at `2` AND at `3`. The at-`3` leaf provides the line and its at-`3`
unramifiedness; the at-`2` leaf applies to any stable line. -/
theorem exists_line_with_locally_unramified_quotCharacter
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W₀ : Submodule k V) (hW₀0 : W₀ ≠ ⊥) (hW₀top : W₀ ≠ ⊤)
    (hW₀stable : ∀ g : Γ ℚ, W₀.map (ρ g) ≤ W₀) :
    ∃ (W : Submodule k V) (χ₂ : Γ ℚ →* kˣ),
      Module.finrank k W = 1 ∧
      (∀ g v, v ∈ W → ρ g v ∈ W) ∧
      (∀ g v, W.mkQ (ρ g v) = (χ₂ g : k) • W.mkQ v) ∧
      (localInertiaGroup Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) ∧
      (localInertiaGroup
          Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) := by
  obtain ⟨W, χ₂, hWfr, hWstable, hχ₂, h3⟩ :=
    exists_line_with_unramified_quotCharacter_at_three V hV hρ
      W₀ hW₀0 hW₀top hW₀stable
  exact ⟨W, χ₂, hWfr, hWstable, hχ₂,
    quotCharacter_unramified_at_two V hV hρ W χ₂ hWfr hWstable hχ₂, h3⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Trivial quotient from the stable line** (DERIVED 2026-07-17 from
the local leaf above and the PROVEN character bookkeeping of
`MazurTorsion.lean`): given a `Γ ℚ`-stable proper nonzero submodule of
a mod-3 hardly ramified representation, there is an equivariant
surjection `π` onto the trivial 1-dimensional representation.
Assembly: the leaf provides a stable line whose quotient character
`χ₂` is unramified at `2` and `3`; outside `{2, 3}` the whole
representation is unramified (`IsHardlyRamified.isUnramified`,
transported by `character_localInertia_le_ker_of_isUnramifiedAt` and
the `Rat.subsingleton_ringHom` spelling bridge); the kernel of `χ₂` is
open (it contains the open kernel of `ρ`); Minkowski
(`minkowski_character_trivial`, now target-generic) kills `χ₂`; and
`π` is the coordinate of the rank-1 quotient. -/
theorem mod_three_of_stable_line {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ)
    (W : Submodule k V) (hW0 : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hWstable : ∀ g : Γ ℚ, W.map (ρ g) ≤ W) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v := by
  classical
  obtain ⟨W', χ₂, hW'1, hstab, hχ₂, hun2, hun3⟩ :=
    exists_line_with_locally_unramified_quotCharacter V hV hρ W hW0 hWtop
      hWstable
  haveI hfinV : Finite V := Module.finite_of_finite k
  have hfr : Module.finrank k V = 2 :=
    Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)
  have hW'top : W' ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, hfr] at hW'1
    omega
  -- the quotient character is trivial wherever the representation is
  have htriv : ∀ g, ρ g = 1 → χ₂ g = 1 := by
    intro g hg
    apply Units.ext
    rw [Units.val_one]
    refine quotCharacter_eq_one_of_sq_eq_zero (ρ g) ?_ W' hW'top (hχ₂ g)
    rw [hg, sub_self]
    exact zero_pow two_ne_zero
  -- the kernel of the representation is open, hence so is that of `χ₂`
  let Kρ : Subgroup (Γ ℚ) :=
    { carrier := {g | ρ g = 1}
      one_mem' := map_one ρ
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) = 1
        rw [map_mul, ha, hb, mul_one]
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ = 1
        have h1 : ρ a⁻¹ * ρ a = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h1 }
  have hKρ_open : IsOpen (Kρ : Set (Γ ℚ)) :=
    isOpen_setOf_galoisRep_eq_one ρ hfinV
  have hker₂ : Kρ ≤ χ₂.ker := fun g hg => MonoidHom.mem_ker.mpr (htriv g hg)
  have hopen₂ : IsOpen (χ₂.ker : Set (Γ ℚ)) :=
    Subgroup.isOpen_mono hker₂ hKρ_open
  -- unramified at every finite place, then Minkowski
  have hunram : ∀ (q : ℕ) (hq : q.Prime),
      localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat ≤
        (χ₂.comp (Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker := by
    intro q hq
    by_cases hq2 : q = 2
    · subst hq2
      exact hun2
    · by_cases hq3 : q = 3
      · subst hq3
        exact hun3
      · intro σ hσ
        have h4 := character_localInertia_le_ker_of_isUnramifiedAt ρ
          hq.toHeightOneSpectrumRingOfIntegersRat
          (hρ.isUnramified q hq ⟨hq2, hq3⟩) χ₂ htriv
        have h5 := h4 hσ
        convert h5 using 5
        exact Subsingleton.elim _ _
  have hχtriv : χ₂ = 1 := minkowski_character_trivial χ₂ hopen₂ hunram
  -- the projection onto the rank-1 quotient
  have hQ1 : Module.finrank k (V ⧸ W') = 1 := by
    have hsum := Submodule.finrank_quotient_add_finrank W'
    rw [hfr, hW'1] at hsum
    omega
  let b : Module.Basis (Fin 1) k (V ⧸ W') :=
    Module.finBasisOfFinrankEq k (V ⧸ W') hQ1
  refine ⟨(b.coord 0).comp W'.mkQ, ?_, ?_⟩
  · -- surjectivity: hit `c` with a preimage of `c • b 0`
    intro c
    obtain ⟨v, hv⟩ := W'.mkQ_surjective (c • b 0)
    refine ⟨v, ?_⟩
    rw [LinearMap.comp_apply, hv, map_smul, smul_eq_mul,
      Module.Basis.coord_apply, Module.Basis.repr_self]
    simp
  · -- equivariance from the trivial quotient character
    intro g v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hχ₂, hχtriv]
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]

/-- **Mod-3 classification** (DERIVED 2026-07-16 from the two nodes
above): a mod-3 hardly ramified representation is an extension of the
trivial character by the (mod-3 cyclotomic) character: there is a
`Γ ℚ`-equivariant surjection onto the trivial 1-dimensional
representation. Input to **B6c** (`Threeadic.lean`). Reducibility
(`mod_three_reducible`, the Dickson/discriminant content) produces the
stable line; the quotient-character analysis
(`mod_three_of_stable_line`) produces the surjection. -/
theorem mod_three {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k] --
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v := by
  obtain ⟨W, hW0, hWtop, hWstable⟩ := mod_three_reducible V hV hρ
  exact mod_three_of_stable_line V hV hρ W hW0 hWtop hWstable

end GaloisRepresentation.IsHardlyRamified
