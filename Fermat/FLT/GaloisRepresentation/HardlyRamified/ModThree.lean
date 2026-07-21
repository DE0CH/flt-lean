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
  set L := AlgebraicClosure k with hL
  set σρ : Representation L (Γ ℚ) (L ⊗[k] V) :=
    Slop.OddRep.baseChange L (MonoidHomClass.toMonoidHom ρ) with hσρ
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
      π.rangeRestrict with hr
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
      intro g hg hgns μ hμnil hμne
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
        set B' := σρ g with hB'
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

/-- **The Serre §5.4/Tate elimination, arithmetic cases** (sorry node —
the deep number-theoretic core): with the notation of `serre_elimination`
below, the dihedral, `A₄`, `S₄`, `A₅`, `PSL₂(𝔽_{3^m})`, `PGL₂(𝔽_{3^m})`
cases contradict the hardly-ramified ramification constraints
(cyclotomic determinant, unramified outside `{2, 3}`, flat at `3`, tame
quadratic quotient at `2`) via Serre's discriminant/conductor bounds
over `ℚ` (Serre, Duke 1987, §5.4: no extension of `ℚ` with these Galois
groups and local conditions exists). -/
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
    False :=
  sorry

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
  rcases hcase with h | h | h | h | ⟨m, t, hm, hcop, hdvd, φ, hiso⟩ | h | h
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
    set L := AlgebraicClosure k with hL
    set σρ : Representation L (Γ ℚ) (L ⊗[k] V) :=
      Slop.OddRep.baseChange L (MonoidHomClass.toMonoidHom ρ) with hσρ
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
  set L := AlgebraicClosure k with hL
  set σρ : Representation L (Γ ℚ) (L ⊗[k] V) :=
    Slop.OddRep.baseChange L (MonoidHomClass.toMonoidHom ρ) with hσρ
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

/-- **The stable line with unramified-at-`3` quotient character** (sorry
node — the connected–étale content of Serre's §5.4 mod-3 analysis): a
reducible mod-3 hardly ramified representation has a stable LINE whose
quotient character is unramified at `3`. Content: the flatness
condition (`IsFlatAt` at `3`) prolongs the representation to a finite
flat group scheme over `ℤ₃`; the étale quotient of its connected–étale
sequence is unramified, so if the given stable line has ramified
quotient at `3`, the connected part is multiplicative and the
connected–étale splitting provides the OTHER stable line whose quotient
IS the étale part (the Serre swap). -/
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
            Nat.prime_three.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom).ker) :=
  sorry

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
    AlgebraicClosure.map (algebraMap ℚ ℚ_[2]) ζ with hz
  have hz3 : z ^ 3 = 1 := hzprim.pow_eq_one
  have hz0 : z ≠ 0 := fun h0 => one_ne_zero
    (α := AlgebraicClosure ℚ_[2]) (by rw [← hz3, h0, zero_pow]; norm_num)
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
      set y : Z2bar := σ • (⟨z, hzmem⟩ : Z2bar) - ⟨z, hzmem⟩ with hy
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
      Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat with hh0
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
          exact E.symm_apply_apply x } with hhcomp
    have hbij := Algebra.IsAlgebraic.algHom_bijective hcomp
    intro y
    obtain ⟨x, hx⟩ := hbij.2 y
    exact ⟨g x, hx⟩
  set ι₃e : AlgebraicClosure ℚ_[2] ≃+*
      AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
    RingEquiv.ofBijective ι₃ ⟨ι₃.injective, hι₃surj⟩ with hι₃e
  have hι₃e_apply : ∀ y, ι₃e y = ι₃ y := fun y => rfl
  -- `τ := ι₃⁻¹ ∘ σ ∘ ι₃`, an automorphism over `ℚ_[2]`
  set τ₀ : AlgebraicClosure ℚ_[2] ≃+* AlgebraicClosure ℚ_[2] :=
    (ι₃e.trans σ.toRingEquiv).trans ι₃e.symm with hτ₀
  have hτ₀_apply : ∀ y, τ₀ y = ι₃e.symm (σ (ι₃e y)) := fun y => rfl
  set τ : Γ ℚ_[2] := AlgEquiv.ofRingEquiv (f := τ₀) (fun x => by
    rw [hτ₀_apply, RingEquiv.symm_apply_eq]
    show σ (ι₃ ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])) x)) =
      ι₃ ((algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])) x)
    rw [hι₃, AlgebraicClosure.map_algebraMap]
    exact σ.commutes (E.symm x)) with hτdef
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
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) with hEs
    set φ : (PadicInt.subring 2) →+*
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat) :=
      RingHom.codRestrict (Es.comp (PadicInt.subring 2).subtype)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat).toSubring
        (fun a => hEsymm_int a.1 a.2) with hφ
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
        (fun z => hmemIC z.1 z.2) with hΦ
    -- transport the inertia condition
    set y : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion
          ℚ Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat)) :=
      ⟨ι₃ x.1, hmemIC x.1 x.2⟩ with hy
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
        Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat))) with hι₁
    set ι₂ := AlgebraicClosure.map (algebraMap ℚ ℚ_[2]) with hι₂
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
      (ι₃.comp ι₂).toRatAlgHom with hf
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
