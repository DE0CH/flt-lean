/-
Mathlib/RingTheory/DedekindDomain/LatticeQuotient.lean — own work for the
Fermat project (not vendored from the FLT project).
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Cardinalities of quotients of lattices by ideals

Three purely commutative-algebra facts, all destined for Mathlib, that
together turn a **Betti-number** input — "`H₁` is a lattice of `ℤ`-rank
`2g` carrying an action of `𝒪_D`" — into the torsion counts of an
abelian variety with real multiplication.

* `Module.card_quotient_smul_top_of_isDedekindDomain` — over a Dedekind
  domain, for a finitely generated torsion-free module `M` and a maximal
  ideal `I` of finite index, `#(M/IM) = #(R/I) ^ rank_R M`.  The proof
  is `Ideal.finrank_fiber_eq_finrank`: torsion-free over a Dedekind
  domain is FLAT (a mathlib instance), and for a finite flat module over
  a domain the fibre dimension at every prime equals the generic rank.
  No localisation bookkeeping is needed.

* `Module.card_quotient_natCast_smul_top` — for a `ℤ`-lattice `H` with a
  finite basis, `#(H/NH) = N ^ (rank H)`.

* `Module.finrank_int_eq_finrank_ringOfIntegers_mul` — the RANK BRIDGE:
  for a finitely generated `𝒪_D`-module that is `ℤ`-free of finite rank,
  `rank_ℤ H = [D:ℚ] · rank_{𝒪_D} H`.  This is what converts the Betti
  number `2g` into the `𝒪_D`-rank `2`, and it is the step that makes the
  parity of the residual rank a theorem rather than a hypothesis.

The bridge is proved by localising at `ℤ ∖ {0}`: `D ⊗[𝒪_D] H` is
simultaneously the `𝒪_D⁰`-localisation of `H` (whence its `D`-dimension
is `rank_{𝒪_D} H`) and its `ℤ⁰`-localisation (whence its
`ℚ`-dimension is `rank_ℤ H`, by `Module.Basis.ofIsLocalizedModule`), and
the two are compared by the tower formula over `ℚ ⊆ D`.  That the two
localisations agree is the mathlib instance
`IsLocalization (Algebra.algebraMapSubmonoid (𝒪 D) ℤ⁰) D`.
-/

@[expose] public section

open Module TensorProduct Submodule Pointwise

namespace Module

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.IsTorsionFree R M]

/-- **`#(M/IM) = #(R/I) ^ rank M` at a maximal ideal of a Dedekind domain**,
for `M` finitely generated and torsion-free.

Torsion-free over a Dedekind domain is flat, and for a finite flat module
over a domain the dimension of the fibre `κ(I) ⊗ M` equals the generic
rank `Module.finrank R M` (`Ideal.finrank_fiber_eq_finrank`).  The fibre
is `M/IM` because `I` is maximal, so `κ(I) = R/I`. -/
theorem card_quotient_smul_top_of_isDedekindDomain
    (I : Ideal R) [I.IsMaximal] [Finite (R ⧸ I)] :
    Nat.card (M ⧸ (I • ⊤ : Submodule R M)) = Nat.card (R ⧸ I) ^ Module.finrank R M := by
  classical
  letI : Fintype (R ⧸ I) := Fintype.ofFinite _
  have hbij := I.bijective_algebraMap_quotient_residueField
  let eR : (R ⧸ I) ≃ₐ[R] I.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ I) I.ResidueField) hbij
  haveI : Finite I.ResidueField := Finite.of_equiv _ eR.toEquiv
  letI : Fintype I.ResidueField := Fintype.ofFinite _
  have e1 : (R ⧸ I) ⊗[R] M ≃ₗ[R] M ⧸ (I • ⊤ : Submodule R M) :=
    TensorProduct.quotTensorEquivQuotSMul M I
  have e2 : (R ⧸ I) ⊗[R] M ≃ₗ[R] I.ResidueField ⊗[R] M :=
    TensorProduct.congr eR.toLinearEquiv (LinearEquiv.refl R M)
  have hcard : Nat.card (M ⧸ (I • ⊤ : Submodule R M)) = Nat.card (I.Fiber M) :=
    Nat.card_congr (e1.symm.trans e2).toEquiv
  haveI : Finite (I.Fiber M) := Module.finite_of_finite I.ResidueField
  letI : Fintype (I.Fiber M) := Fintype.ofFinite _
  rw [hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := I.ResidueField) (V := I.Fiber M),
    I.finrank_fiber_eq_finrank]
  congr 1
  exact (Fintype.card_congr eR.toEquiv).symm

end Dedekind

section Lattice

variable {H : Type*} [AddCommGroup H] {ι : Type*} [Fintype ι]

/-- **`#(H/NH) = N ^ (rank H)` for a `ℤ`-lattice `H`.** -/
theorem card_quotient_natCast_smul_top (b : Module.Basis ι ℤ H) (N : ℕ) :
    Nat.card (H ⧸ ((N : ℤ) • (⊤ : Submodule ℤ H))) = N ^ Fintype.card ι := by
  classical
  have e0 : (H ⧸ ((N : ℤ) • (⊤ : Submodule ℤ H))) ≃ₗ[ℤ]
      (ℤ ⧸ Ideal.span {(N : ℤ)}) ⊗[ℤ] H := QuotSMulTop.equivQuotTensor _ _
  have e1 : (ℤ ⧸ Ideal.span {(N : ℤ)}) ⊗[ℤ] H ≃ₗ[ℤ]
      (ℤ ⧸ Ideal.span {(N : ℤ)}) ⊗[ℤ] (ι →₀ ℤ) :=
    TensorProduct.congr (LinearEquiv.refl _ _) b.repr
  have e2 : (ℤ ⧸ Ideal.span {(N : ℤ)}) ⊗[ℤ] (ι →₀ ℤ) ≃ₗ[ℤ]
      (ι →₀ (ℤ ⧸ Ideal.span {(N : ℤ)})) :=
    TensorProduct.finsuppScalarRight ℤ ℤ (ℤ ⧸ Ideal.span {(N : ℤ)}) ι
  have hN : Nat.card (ℤ ⧸ Ideal.span {(N : ℤ)}) = N := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod N).toEquiv, Nat.card_zmod]
  rw [Nat.card_congr (e0.trans (e1.trans e2)).toEquiv,
    Nat.card_congr Finsupp.equivFunOnFinite, Nat.card_fun, hN, Nat.card_eq_fintype_card]

/-- **`#(H/(N)H) = N ^ (rank_ℤ H)`** for a `ℤ`-lattice `H` carrying an
action of a commutative ring `R`.

The point is the change of scalars: the `R`-submodule generated by
`(N : R)·H` and the `ℤ`-submodule `N·H` have the same underlying set,
because `(N : R) • h = N • h` for every `h`.  So the `N`-torsion count of
a lattice is insensitive to which of the two rings it is read over — which
is what lets a Betti number stated over `ℤ` compute an `𝒪_D`-ideal
torsion count. -/
theorem card_quotient_ideal_span_natCast_smul_top
    {R : Type*} [CommRing R] [Module R H] (b : Module.Basis ι ℤ H) (N : ℕ) :
    Nat.card (H ⧸ (Ideal.span {(N : R)} • (⊤ : Submodule R H)))
      = N ^ Fintype.card ι := by
  classical
  have hset : ∀ h : H,
      h ∈ (Ideal.span {(N : R)} • (⊤ : Submodule R H))
        ↔ h ∈ ((N : ℤ) • (⊤ : Submodule ℤ H)) := by
    intro h
    rw [Submodule.ideal_span_singleton_smul]
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, by rw [Nat.cast_smul_eq_nsmul R N s, ← natCast_zsmul]⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, by rw [Nat.cast_smul_eq_nsmul R N s, ← natCast_zsmul]⟩
  rw [← card_quotient_natCast_smul_top b N]
  refine Nat.card_congr (Quotient.congr (Equiv.refl H) ?_)
  intro a c
  simp only [Equiv.refl_apply, Submodule.quotientRel_def]
  exact hset (a - c)

end Lattice

section Bridge

open scoped nonZeroDivisors

/-- **THE RANK BRIDGE.**  For a finitely generated module over the ring of
integers of a number field `D` which is free of finite rank over `ℤ`, the
`ℤ`-rank is `[D:ℚ]` times the `𝒪_D`-rank.

This is what turns the Betti number of an abelian variety with real
multiplication into the `𝒪_D`-rank of its homology: `rank_ℤ H₁ = 2g` and
`g = [D:ℚ]` give `rank_{𝒪_D} H₁ = 2`, hence both the PARITY and the
NONVANISHING of the residual ranks. -/
theorem finrank_int_eq_finrank_ringOfIntegers_mul
    (D : Type*) [Field D] [NumberField D]
    (H : Type*) [AddCommGroup H] [Module (NumberField.RingOfIntegers D) H]
    [Module.Finite (NumberField.RingOfIntegers D) H]
    [Module.Free ℤ H] [Module.Finite ℤ H] :
    Module.finrank ℤ H
      = Module.finrank ℚ D * Module.finrank (NumberField.RingOfIntegers D) H := by
  classical
  set R := NumberField.RingOfIntegers D with hR
  set V := D ⊗[R] H with hV
  haveI hRb : IsLocalizedModule (Algebra.algebraMapSubmonoid R ℤ⁰)
      (TensorProduct.mk R D H 1) :=
    (isLocalizedModule_iff_isBaseChange _ D _).mpr (TensorProduct.isBaseChange R H D)
  let f : H →ₗ[ℤ] V := (TensorProduct.mk R D H 1).restrictScalars ℤ
  haveI hZ : IsLocalizedModule ℤ⁰ f := by
    constructor
    · intro x
      rw [Module.End.isUnit_iff]
      have hx : (algebraMap ℤ D x) ≠ 0 := by
        simp [nonZeroDivisors.coe_ne_zero x]
      constructor
      · intro a b hab
        simp only [Module.algebraMap_end_apply] at hab
        have hab' : (algebraMap ℤ D x) • a = (algebraMap ℤ D x) • b := by
          rw [algebraMap_smul, algebraMap_smul]; exact hab
        exact smul_right_injective V hx hab'
      · intro y
        refine ⟨(algebraMap ℤ D x)⁻¹ • y, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul (R := ℤ) (A := D) (M := V), smul_smul,
          mul_inv_cancel₀ hx, one_smul]
    · intro y
      obtain ⟨⟨h, s⟩, hs⟩ := IsLocalizedModule.surj
        (Algebra.algebraMapSubmonoid R ℤ⁰) (TensorProduct.mk R D H 1) y
      obtain ⟨n, hn, hns⟩ := s.2
      refine ⟨⟨h, ⟨n, hn⟩⟩, ?_⟩
      have h' : (algebraMap ℤ R n) • y = TensorProduct.mk R D H 1 h := by
        rw [hns]; exact hs
      rw [algebraMap_smul] at h'
      exact h'
    · intro x₁ x₂ hx
      obtain ⟨s, hsc⟩ := IsLocalizedModule.exists_of_eq
        (S := Algebra.algebraMapSubmonoid R ℤ⁰) (f := TensorProduct.mk R D H 1) hx
      obtain ⟨n, hn, hns⟩ := s.2
      refine ⟨⟨n, hn⟩, ?_⟩
      have : (s : R) • x₁ = (s : R) • x₂ := hsc
      rw [← hns] at this
      simpa [Int.cast_smul_eq_zsmul] using this
  have h3 : Module.finrank ℚ V = Module.finrank ℤ H := by
    let b := Module.Free.chooseBasis ℤ H
    rw [Module.finrank_eq_card_basis (b.ofIsLocalizedModule ℚ ℤ⁰ f),
      Module.finrank_eq_card_chooseBasisIndex]
  have h1 : Module.finrank D V = Module.finrank R H :=
    (TensorProduct.isBaseChange R H D).finrank_eq
  have h2 : Module.finrank ℚ D * Module.finrank D V = Module.finrank ℚ V :=
    Module.finrank_mul_finrank ℚ D V
  rw [← h3, ← h2, h1]

end Bridge

end Module
