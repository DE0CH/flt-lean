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
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Mod-3 hardly ramified representations

A mod-3 hardly ramified representation is shown to be an extension of
the trivial character by the mod-3 cyclotomic character.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

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
  · set c : Γ ℚ := absoluteGaloisGroup.map (algebraMap ℚ ℝ) σ with hc
    set x : ℤ_[3] :=
      ((cyclotomicCharacter (AlgebraicClosure ℚ) 3 c.toRingEquiv :
        ℤ_[3]ˣ) : ℤ_[3]) with hx
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
      with hz
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
theorem three_eq_zero_of_finite_padicIntThree_algebra
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k] : (3 : k) = 0 := by
  cases nonempty_fintype k
  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI := hchar
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  rcases eq_or_ne p 3 with rfl | hp3
  · exact (CharP.cast_eq_zero k 3)
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

set_option warn.sorry false in
/-- **No absolutely irreducible mod-3 hardly ramified representation**
(sorry node — the Serre §5.4/Tate elimination): the projective image
of an absolutely irreducible mod-3 representation is a finite subgroup
of `PGL₂(𝔽̄₃)` classified by Dickson (vendored PROVEN in
`Slop.PGL2.FiniteSubgroups`, to be reconnected by this node's proof),
and the hardly-ramified ramification constraints (cyclotomic
determinant, unramified outside `{2,3}`, flat at `3`, tame quadratic
quotient at `2`) eliminate every case via discriminant/conductor
bounds over `ℚ`. -/
theorem not_isAbsolutelyIrreducible {k : Type u} [Finite k] [Field k]
    [Algebra ℤ_[3] k] [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ¬ Slop.OddRep.IsAbsolutelyIrreducible
      (MonoidHomClass.toMonoidHom ρ : Representation k (Γ ℚ) V) :=
  sorry

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

set_option warn.sorry false in
/-- **The stable line with locally-unramified quotient character at
`2` and `3`** (sorry node — the local content of Serre's §5.4 mod-3
analysis, isolated from the global bookkeeping, which is DERIVED
below): a reducible mod-3 hardly ramified representation has a stable
LINE whose quotient character is unramified at `2` AND at `3`.
Content: at `3` the flatness condition forces the étale quotient of
the connected-étale sequence of the finite flat prolongation to be
unramified — if the natural stable line has ramified quotient, the
connected-étale splitting provides the OTHER stable line (the Serre
swap); at `2` the tame quadratic quotient condition (`isTameAtTwo`)
makes the quotient character at worst quadratic-unramified. -/
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
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) :=
  sorry

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
