/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Aut
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Fermat.FLT.Mathlib.FieldTheory.AbsoluteHilbert90

/-!
# Composition of variable changes on points, and the quartic twist at `j = 1728`

Material for `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` together with the
`j = 1728` half of the descent argument of `Fermat/FLT/ModularCurve/X0.lean`.

## Main statements

* `WeierstrassCurve.Affine.Point.autMap` : the automorphism of the Mordell–Weil group induced
  by an automorphism `C • W = W` of the curve.  It is *definitionally* the `autPoint` of
  `Fermat/FLT/ModularCurve/X0.lean`, restated here so that the general lemmas about it can be
  developed next to the `Point` API they are about (and in a module that is cheap to compile).
* `WeierstrassCurve.Affine.Point.equivVariableChange_autMap` : conjugating an automorphism of
  `W` by a variable change `C₀` conjugates its action on points by `equivVariableChange W C₀`.
* `WeierstrassCurve.quarticModel` : the curve `y² = x³ + a x`, the normal form at `j = 1728`.
* `WeierstrassCurve.quarticTwistChar` : the descent character `χ(σ) = ±1` according as `σ`
  stabilises `⟨g⟩`, with `quarticTwistChar_mul` (it is a homomorphism) and
  `algebraMap_quarticTwistChar_eq` (it computes `u_σ²`) both PROVEN.
* `WeierstrassCurve.exists_stableCyclic_quarticTwist` : the arithmetic heart at `j = 1728` —
  a cyclic subgroup that is Galois-stable only up to an automorphism becomes genuinely stable
  on a quartic twist.

**`Ω` must be an ALGEBRAIC CLOSURE of `K`** (`[IsAlgClosed Ω]` plus an EXPLICIT
`halg : Algebra.IsAlgebraic K Ω`; see below for why that one is not an instance argument).
Without that, `exists_quarticTwistParameter` is FALSE — its conclusion asks for a fourth root
in `Ω` that need not be there.  The witness (`K = ℚ`, `Ω = ℚ(ζ₈)`, `y² = x³ - 2x`, `g = (√2,0)`
of order `2`) is written out in that theorem's docstring; the instances were added on
2026-07-28 and cost the only call site nothing, since it works over `AlgebraicClosure ℚ`.

**This file is now sorry-free** (2026-07-29).  Its last two leaves —
`WeierstrassCurve.exists_finiteLevel_quarticTwistChar` (the finite Galois level of `χ`) and
`Field.exists_sq_eq_algebraMap_of_quadraticChar` (Hilbert 90 at `n = 2` over a general
algebraic closure) — are proven, the second after generalising the two theorems of
`Fermat/FLT/Mathlib/FieldTheory/AbsoluteHilbert90.lean` from `AlgebraicClosure K` to an
arbitrary `Ω` with `[IsGalois K Ω]`.
-/

@[expose] public section

namespace Field

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- **An open index-`≤ 2` subgroup of `Γ_K` is the stabiliser of a square root** (opened as a
sorry leaf 2026-07-28 while repairing `WeierstrassCurve.exists_quarticTwistParameter`;
**PROVEN 2026-07-29**).

A quadratic character `χ : Gal(Ω/K) → {±1}` that is *inflated from a finite Galois level* `L`
is `σ ↦ σ(s)/s` for a square root `s` of an element `d ∈ Kˣ`.  This is the whole field-theoretic
content of the `j = 1728` descent, and it is what the docstring of
`exists_stableCyclic_twist_of_autStable_of_j_eq_1728` in `Fermat/FLT/ModularCurve/X0.lean`
calls "item 3: the quadratic field cut out by an open index-`2` subgroup of `Γ_ℚ`".

#### The route: this is `n = 2` of the Kummer theorem one module upstream (PROVEN 2026-07-29)

`Field.exists_pow_eq_algebraMap_forall_absoluteGalois_apply_eq_mul`
(`Fermat/FLT/Mathlib/FieldTheory/AbsoluteHilbert90.lean`) is exactly this statement: take
`n := 2` and `c σ := algebraMap K Ω (χ σ)`.  Its four hypotheses are discharged by, in order,
membership of `algebraMap K Ω (χ σ)` in any `L` (`IntermediateField.algebraMap_mem`), `hval`
(`(±1)² = 1`), `hmul` together with `AlgEquiv.commutes` — the cocycle identity
`c (σ * τ) = c σ * σ (c τ)` degenerates to multiplicativity because `χ τ` lies in `K` and is
therefore fixed by `σ` — and `hinfl`.

**The transport that this leaf was cut for no longer exists.**  When it was opened, that
theorem was stated for `Ω = AlgebraicClosure K`, and the leaf's original docstring proposed
either conjugating everything along `IsAlgClosure.equiv K Ω (AlgebraicClosure K)` or
generalising the upstream file.  The second was done instead (2026-07-29): both theorems in
`AbsoluteHilbert90.lean` now take an arbitrary `Ω` with `[IsGalois K Ω]`, since their proofs
only ever used `AlgEquiv.restrictNormalHom_surjective` and
`InfiniteGalois.mem_range_algebraMap_iff_fixed`, both already general.  The generalisation
also *dropped* `[PerfectField K]` there — it had been used only to make `K̄/K` separable.

`[PerfectField K]` and `[IsAlgClosed Ω]` survive HERE because they are what supplies
`IsGalois K Ω` from `halg`, through `Field.isGalois_of_isAlgClosed`.

#### Non-vacuity

`hinfl` is load-bearing and not decoration: `H¹(Γ_K, K̄ˣ) = 1` is FALSE for non-continuous
cochains, and a character of `Gal(Ω/K)` with no finite level need not be `σ ↦ σ(s)/s` for any
`s`.  `hmul` is load-bearing too — a mere `±1`-valued *function* is not a coboundary. -/
theorem exists_sq_eq_algebraMap_of_quadraticChar [PerfectField K] [IsAlgClosed Ω]
    (halg : Algebra.IsAlgebraic K Ω)
    (χ : (Ω ≃ₐ[K] Ω) → K) (hval : ∀ σ, χ σ = 1 ∨ χ σ = -1)
    (hmul : ∀ σ τ, χ (σ * τ) = χ σ * χ τ)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    (hinfl : ∀ σ τ : Ω ≃ₐ[K] Ω, (∀ x ∈ L, σ x = τ x) → χ σ = χ τ) :
    ∃ (d : K) (s : Ω), d ≠ 0 ∧ s ^ 2 = algebraMap K Ω d ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ s = algebraMap K Ω (χ σ) * s := by
  haveI : IsGalois K Ω := isGalois_of_isAlgClosed halg
  have hcmem : ∀ σ : Ω ≃ₐ[K] Ω, algebraMap K Ω (χ σ) ∈ L := fun σ => L.algebraMap_mem (χ σ)
  have hcpow : ∀ σ : Ω ≃ₐ[K] Ω, algebraMap K Ω (χ σ) ^ 2 = 1 := by
    intro σ
    rcases hval σ with h | h <;> rw [h] <;> simp
  have hcoc : ∀ σ τ : Ω ≃ₐ[K] Ω, algebraMap K Ω (χ (σ * τ))
      = algebraMap K Ω (χ σ) * σ (algebraMap K Ω (χ τ)) := by
    intro σ τ
    rw [σ.commutes (χ τ), hmul σ τ, map_mul]
  have hinfl' : ∀ σ τ : Ω ≃ₐ[K] Ω, (∀ x ∈ L, σ x = τ x) →
      algebraMap K Ω (χ σ) = algebraMap K Ω (χ τ) := fun σ τ h => by rw [hinfl σ τ h]
  obtain ⟨γ, d, hγ0, hd, hγ⟩ :=
    exists_pow_eq_algebraMap_forall_absoluteGalois_apply_eq_mul (n := 2) L two_ne_zero
      (fun σ => algebraMap K Ω (χ σ)) hcmem hcpow hcoc hinfl'
  refine ⟨d, γ, ?_, hd, hγ⟩
  intro h0
  rw [h0, map_zero] at hd
  exact hγ0 (pow_eq_zero_iff two_ne_zero |>.mp hd)

end Field

namespace WeierstrassCurve

open scoped WeierstrassCurve.Affine

/-! ### The composition law and conjugation for variable changes acting on points -/

namespace Affine.Point

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The automorphism of the Mordell–Weil group induced by an automorphism of the curve.**

Definitionally the same as `autPoint` in `Fermat/FLT/ModularCurve/X0.lean`. -/
noncomputable def autMap {W : WeierstrassCurve F} [W.IsElliptic] {C : VariableChange F}
    (h : C • W = W) : W.toAffine.Point →+ W.toAffine.Point :=
  (mapVariableChange W C).comp (equivOfEq h.symm).toAddMonoidHom

lemma autMap_apply {W : WeierstrassCurve F} [W.IsElliptic] {C : VariableChange F}
    (h : C • W = W) (P : W.toAffine.Point) :
    autMap h P = mapVariableChangeFun W C (equivOfEq h.symm P) := rfl

omit [DecidableEq F] in
/-- Conjugating an automorphism of `W` by a variable change `C₀` gives an automorphism of
`C₀ • W`. -/
lemma conj_smul_smul (W : WeierstrassCurve F) (C₀ : VariableChange F) {D : VariableChange F}
    (hD : D • W = W) : (C₀ * D * C₀⁻¹) • (C₀ • W) = C₀ • W := by
  rw [← mul_smul, inv_mul_cancel_right, mul_smul, hD]

/-- **Conjugation.**  `equivVariableChange W C₀ : (C₀ • W).Point ≃+ W.Point` intertwines the
action of an automorphism `D` of `W` with the action of its conjugate `C₀ D C₀⁻¹` on `C₀ • W`.

This is the composition law `M(C₀) ∘ M(C₀ D C₀⁻¹) = M((C₀ D C₀⁻¹) * C₀) = M(C₀ * D)
= M(D) ∘ M(C₀)` written out in coordinates. -/
lemma equivVariableChange_autMap (W : WeierstrassCurve F) [W.IsElliptic] (C₀ : VariableChange F)
    {D : VariableChange F} (hD : D • W = W) (Q : (C₀ • W).toAffine.Point) :
    equivVariableChange W C₀ (autMap (conj_smul_smul W C₀ hD) Q)
      = autMap hD (equivVariableChange W C₀ Q) := by
  have hu0 : (C₀.u : F) ≠ 0 := C₀.u.ne_zero
  rcases Q with _ | ⟨x, y, hns⟩
  · show equivVariableChange W C₀ (autMap (conj_smul_smul W C₀ hD) 0)
      = autMap hD (equivVariableChange W C₀ 0)
    simp only [_root_.map_zero]
  · show mapVariableChangeFun W C₀ (mapVariableChangeFun (C₀ • W) (C₀ * D * C₀⁻¹)
      (equivOfEq (conj_smul_smul W C₀ hD).symm (.some x y hns)))
        = mapVariableChangeFun W D (equivOfEq hD.symm
          (mapVariableChangeFun W C₀ (.some x y hns)))
    rw [equivOfEq_some, mapVariableChangeFun_some, mapVariableChangeFun_some,
      mapVariableChangeFun_some, equivOfEq_some, mapVariableChangeFun_some]
    refine some_eq_some W ?_ ?_ <;>
      simp only [VariableChange.mul_def, VariableChange.inv_def, Units.val_mul,
        Units.val_inv_eq_inv_val] <;>
      field_simp <;> ring

/-- Transport of `autMap` along an equality of curves. -/
lemma equivOfEq_autMap {V V' : WeierstrassCurve F} [V.IsElliptic] [V'.IsElliptic] (e : V = V')
    {C : VariableChange F} (h : C • V = V) (h' : C • V' = V') (P : V.toAffine.Point) :
    equivOfEq e (autMap h P) = autMap h' (equivOfEq e P) := by
  subst e; rfl

end Affine.Point

/-! ### The normal form `y² = x³ + a x` at `j = 1728` -/

open Affine.Point

/-- The Weierstrass curve `y² = x³ + a x`, the normal form at `j = 1728`. -/
def quarticModel {R : Type*} [CommRing R] (a : R) : WeierstrassCurve R := ⟨0, 0, 0, a, 0⟩

@[simp] lemma quarticModel_a₁ {R : Type*} [CommRing R] (a : R) : (quarticModel a).a₁ = 0 := rfl
@[simp] lemma quarticModel_a₂ {R : Type*} [CommRing R] (a : R) : (quarticModel a).a₂ = 0 := rfl
@[simp] lemma quarticModel_a₃ {R : Type*} [CommRing R] (a : R) : (quarticModel a).a₃ = 0 := rfl
@[simp] lemma quarticModel_a₄ {R : Type*} [CommRing R] (a : R) : (quarticModel a).a₄ = a := rfl
@[simp] lemma quarticModel_a₆ {R : Type*} [CommRing R] (a : R) : (quarticModel a).a₆ = 0 := rfl

lemma quarticModel_baseChange {R : Type*} [CommRing R] (a : R) (A : Type*) [CommRing A]
    [Algebra R A] : (quarticModel a)⁄A = quarticModel (algebraMap R A a) := by
  ext <;> simp [quarticModel, baseChange, map]

lemma quarticModel_Δ {R : Type*} [CommRing R] (a : R) : (quarticModel a).Δ = -64 * a ^ 3 := by
  simp only [Δ, b₂, b₄, b₆, b₈, quarticModel_a₁, quarticModel_a₂, quarticModel_a₃,
    quarticModel_a₄, quarticModel_a₆]
  ring

lemma isElliptic_quarticModel {F : Type*} [Field F] [CharZero F] {a : F} (ha : a ≠ 0) :
    (quarticModel a).IsElliptic := by
  refine ⟨?_⟩
  rw [quarticModel_Δ]
  exact (isUnit_iff_ne_zero).mpr (mul_ne_zero (by norm_num) (pow_ne_zero 3 ha))

/-- **The normal form at `j = 1728` really has `j = 1728`.**  `y² = x³ + a x` has
`b₂ = b₆ = 0`, hence `c₆ = −b₂³ + 36 b₂ b₄ − 216 b₆ = 0`, and `c₆_eq_zero_iff_j_eq_1728`
does the rest.  This is what lets the quartic twist below record the `j`-invariant of the
curve it produces — the twist is a `quarticModel` by construction, so the value is free. -/
lemma j_quarticModel {F : Type*} [Field F] [CharZero F] {a : F}
    [(quarticModel a).IsElliptic] : (quarticModel a).j = 1728 := by
  refine (quarticModel a).c₆_eq_zero_iff_j_eq_1728.mp ?_
  simp only [c₆, b₂, b₄, b₆, quarticModel_a₁, quarticModel_a₂, quarticModel_a₃,
    quarticModel_a₄, quarticModel_a₆]
  ring


/-- **The normal form at `j = 1728`**: an elliptic curve with `j = 1728` over a field of
characteristic `0` is isomorphic, over that field, to `y² = x³ + a x` for a unique `a ≠ 0`. -/
lemma exists_smul_eq_quarticModel {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K)
    [E.IsElliptic] (hj : E.j = 1728) :
    ∃ (C : VariableChange K) (a : K), a ≠ 0 ∧ C • E = quarticModel a := by
  haveI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : K) := invertibleOfNonzero (by norm_num)
  obtain ⟨C₀, hshort⟩ := E.exists_variableChange_isShortNF
  haveI := hshort
  have hj₀ : (C₀ • E).j = 1728 := by rw [variableChange_j]; exact hj
  have hc6 : (C₀ • E).c₆ = 0 := (C₀ • E).c₆_eq_zero_iff_j_eq_1728.mpr hj₀
  have hc4 : (C₀ • E).c₄ ≠ 0 := (C₀ • E).c₄_ne_zero_of_j_eq_1728 (by norm_num) hj₀
  have ha₁ : (C₀ • E).a₁ = 0 := a₁_of_isShortNF _
  have ha₂ : (C₀ • E).a₂ = 0 := a₂_of_isShortNF _
  have ha₃ : (C₀ • E).a₃ = 0 := a₃_of_isShortNF _
  have ha₆ : (C₀ • E).a₆ = 0 := by
    have hz : (-864 : K) * (C₀ • E).a₆ = 0 := by
      rw [← hc6]
      simp only [c₆, b₂, b₄, b₆, ha₁, ha₂, ha₃]
      ring
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (by norm_num)
    · exact h
  have ha₄ : (C₀ • E).a₄ ≠ 0 := by
    intro h0
    apply hc4
    simp only [c₄, b₂, b₄, ha₁, ha₂, h0]
    ring
  exact ⟨C₀, (C₀ • E).a₄, ha₄, by
    ext <;> simp only [quarticModel_a₁, quarticModel_a₂, quarticModel_a₃, quarticModel_a₄,
      quarticModel_a₆, ha₁, ha₂, ha₃, ha₆]⟩

/-! ### Curves of the form `y² = x³ + a₄ x`, described by their coefficients

The base change `(quarticModel a)⁄Ω` is *not* syntactically `quarticModel (algebraMap a)`, so the
lemmas that have to be applied on the `Ω` side are stated for an arbitrary curve whose
`a₁, a₂, a₃, a₆` vanish rather than for `quarticModel` itself. -/

section Quartic

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

omit [DecidableEq F] in
lemma eq_quarticModel (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) :
    W = quarticModel W.a₄ := by
  ext <;> simp [quarticModel, h₁, h₂, h₃, h₆]

omit [DecidableEq F] in
/-- A diagonal variable change scales `a₄` by `u⁻⁴`. -/
lemma smul_diag_eq (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) (u : Fˣ) :
    (⟨u, 0, 0, 0⟩ : VariableChange F) • W = quarticModel (((u : F) ^ 4)⁻¹ * W.a₄) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  ext <;>
    simp only [variableChange_def, quarticModel_a₁, quarticModel_a₂, quarticModel_a₃,
      quarticModel_a₄, quarticModel_a₆, h₁, h₂, h₃, h₆, Units.val_inv_eq_inv_val] <;>
    field_simp <;> ring

omit [DecidableEq F] in
/-- A fourth root of unity is an automorphism of `y² = x³ + a₄ x`. -/
lemma smul_diag_self (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) {u : Fˣ}
    (hu : (u : F) ^ 4 = 1) : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W := by
  rw [smul_diag_eq h₁ h₂ h₃ h₆, hu, inv_one, one_mul]
  exact (eq_quarticModel h₁ h₂ h₃ h₆).symm

omit [DecidableEq F] in
/-- **The quartic twist.**  If `W'` is `y² = x³ + δ⁴a₄x` then `⟨δ,0,0,0⟩` carries it to `W`. -/
lemma smul_diag_twist {W' : WeierstrassCurve F} (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₆ : W.a₆ = 0) (h₁' : W'.a₁ = 0) (h₂' : W'.a₂ = 0) (h₃' : W'.a₃ = 0) (h₆' : W'.a₆ = 0)
    (δ : Fˣ) (hδ : W'.a₄ = (δ : F) ^ 4 * W.a₄) :
    (⟨δ, 0, 0, 0⟩ : VariableChange F) • W' = W := by
  have hd : (δ : F) ≠ 0 := δ.ne_zero
  rw [smul_diag_eq h₁' h₂' h₃' h₆', hδ,
    show ((δ : F) ^ 4)⁻¹ * ((δ : F) ^ 4 * W.a₄) = W.a₄ by field_simp]
  exact (eq_quarticModel h₁ h₂ h₃ h₆).symm

omit [DecidableEq F] in
/-- **Every automorphism of `y² = x³ + a₄ x` is diagonal**, in characteristic `0`, and its `u`
is a fourth root of unity. -/
lemma aut_eq_diag [CharZero F] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0)
    (ha₄ : W.a₄ ≠ 0) {C : VariableChange F} (h : C • W = W) :
    C = ⟨C.u, 0, 0, 0⟩ ∧ (C.u : F) ^ 4 = 1 := by
  have hc4 : W.c₄ ≠ 0 := by
    have hval : W.c₄ = -48 * W.a₄ := by simp only [c₄, b₂, b₄, h₁, h₂]; ring
    rw [hval]; exact mul_ne_zero (by norm_num) ha₄
  have hu4 : (C.u : F) ^ 4 = 1 := u_pow_four_eq_one_of_smul_eq _ hc4 h
  refine ⟨?_, hu4⟩
  have hDsmul : (⟨C.u, 0, 0, 0⟩ : VariableChange F) • W = W := smul_diag_self h₁ h₂ h₃ h₆ hu4
  have hCD : (C * (⟨C.u, 0, 0, 0⟩ : VariableChange F)⁻¹) • W = W := by
    have h1 : (C * (⟨C.u, 0, 0, 0⟩ : VariableChange F)⁻¹) •
        ((⟨C.u, 0, 0, 0⟩ : VariableChange F) • W) = W := by
      rw [← mul_smul, inv_mul_cancel_right, h]
    rwa [hDsmul] at h1
  have hu1 : (C * (⟨C.u, 0, 0, 0⟩ : VariableChange F)⁻¹).u = 1 := mul_inv_cancel C.u
  have hone := eq_one_of_u_eq_one_of_smul_eq W (by norm_num) (by norm_num) hu1 hCD
  have h2 : C * (⟨C.u, 0, 0, 0⟩ : VariableChange F)⁻¹ * (⟨C.u, 0, 0, 0⟩ : VariableChange F)
      = 1 * (⟨C.u, 0, 0, 0⟩ : VariableChange F) := by rw [hone]
  rwa [inv_mul_cancel_right, one_mul] at h2

/-- `autMap` depends on the variable change only through its value. -/
lemma autMap_congr [W.IsElliptic] {C C' : VariableChange F} (e : C = C') (h : C • W = W)
    (h' : C' • W = W) (P : W.toAffine.Point) : autMap h P = autMap h' P := by
  subst e; rfl

/-- Negating `u` negates the induced automorphism of the Mordell–Weil group: on
`y² = x³ + a₄ x` negation of a point is `(x, y) ↦ (x, -y)`. -/
lemma autMap_diag_neg [W.IsElliptic] (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) {u : Fˣ}
    (h : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W)
    (h' : (⟨-u, 0, 0, 0⟩ : VariableChange F) • W = W) (P : W.toAffine.Point) :
    autMap h' P = - autMap h P := by
  rcases P with _ | ⟨x, y, hns⟩
  · show autMap h' 0 = - autMap h 0
    simp only [_root_.map_zero, _root_.neg_zero]
  · rw [autMap_apply, autMap_apply, equivOfEq_some, equivOfEq_some,
      mapVariableChangeFun_some, mapVariableChangeFun_some, Affine.Point.neg_some]
    refine some_eq_some _ ?_ ?_ <;>
      simp only [Affine.negY, h₁, h₃, Units.val_neg] <;> ring

/-- A diagonal automorphism with `u = 1` acts trivially on points. -/
lemma autMap_diag_one [W.IsElliptic] {u : Fˣ} (hu1 : (u : F) = 1)
    (h : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W) (P : W.toAffine.Point) :
    autMap h P = P := by
  rcases P with _ | ⟨x, y, hns⟩
  · show autMap h 0 = 0
    simp only [_root_.map_zero]
  · rw [autMap_apply, equivOfEq_some, mapVariableChangeFun_some]
    refine some_eq_some W ?_ ?_ <;> simp only [hu1] <;> ring

/-- **An automorphism of `y² = x³ + a₄x` whose `u` squares to `1` acts as `±1` on points.**
This is the reason `A := Aut(E, ⟨g⟩)` contains `μ₂`, and with `hmove` it is what pins
`A = μ₂` exactly. -/
lemma autMap_eq_self_or_neg [CharZero F] [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0)
    (h₃ : W.a₃ = 0) (h₆ : W.a₆ = 0) (ha₄ : W.a₄ ≠ 0) {C : VariableChange F} (h : C • W = W)
    (hsq : (C.u : F) ^ 2 = 1) (P : W.toAffine.Point) :
    autMap h P = P ∨ autMap h P = -P := by
  obtain ⟨hCdiag, hCu4⟩ := aut_eq_diag h₁ h₂ h₃ h₆ ha₄ h
  have hd1 : (⟨(1 : Fˣ), 0, 0, 0⟩ : VariableChange F) • W = W :=
    smul_diag_self h₁ h₂ h₃ h₆ (by norm_num)
  have hdneg : (⟨(-1 : Fˣ), 0, 0, 0⟩ : VariableChange F) • W = W :=
    smul_diag_self h₁ h₂ h₃ h₆ (by norm_num)
  rcases mul_eq_zero.mp (show ((C.u : F) - 1) * ((C.u : F) + 1) = 0 by linear_combination hsq)
    with he | he
  · refine Or.inl ?_
    have hcu : C.u = 1 := Units.ext (by push_cast; linear_combination he)
    rw [autMap_congr (show C = ⟨(1 : Fˣ), 0, 0, 0⟩ by rw [hCdiag, hcu]) h hd1]
    exact autMap_diag_one (by norm_num) hd1 P
  · refine Or.inr ?_
    have hcu : C.u = -1 := Units.ext (by push_cast; linear_combination he)
    rw [autMap_congr (show C = ⟨(-1 : Fˣ), 0, 0, 0⟩ by rw [hCdiag, hcu]) h hdneg,
      autMap_diag_neg h₁ h₃ hd1 hdneg P, autMap_diag_one (by norm_num) hd1 P]

/-- **A diagonal automorphism with `u² = -1` squares to negation on points**: `[i]² = [-1]`,
because `(x, y) ↦ (u²x, u³y)` iterates to `(u⁴x, u⁶y) = (x, -y)`. -/
lemma autMap_diag_sq [W.IsElliptic] (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) {u : Fˣ}
    (hu : (u : F) ^ 2 = -1) (h : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W)
    (P : W.toAffine.Point) : autMap h (autMap h P) = -P := by
  rcases P with _ | ⟨x, y, hns⟩
  · show autMap h (autMap h 0) = -0
    simp only [_root_.map_zero, _root_.neg_zero]
  · rw [autMap_apply h (Affine.Point.some x y hns), equivOfEq_some, mapVariableChangeFun_some,
      autMap_apply, equivOfEq_some, mapVariableChangeFun_some, Affine.Point.neg_some]
    refine some_eq_some W ?_ ?_
    · linear_combination (x * ((u : F) ^ 2 - 1)) * hu
    · simp only [Affine.negY, h₁, h₃]
      linear_combination (y * ((u : F) ^ 4 - (u : F) ^ 2 + 1)) * hu

/-- **Diagonal automorphisms commute with the quartic twist isomorphism.** -/
lemma autMap_twist_comm {W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic] {δ ζ : Fˣ}
    (hψ : (⟨δ, 0, 0, 0⟩ : VariableChange F) • W' = W)
    (hζ : (⟨ζ, 0, 0, 0⟩ : VariableChange F) • W' = W')
    (hζ' : (⟨ζ, 0, 0, 0⟩ : VariableChange F) • W = W) (P : W.toAffine.Point) :
    autMap hζ (mapVariableChangeFun W' ⟨δ, 0, 0, 0⟩ (equivOfEq hψ.symm P))
      = mapVariableChangeFun W' ⟨δ, 0, 0, 0⟩ (equivOfEq hψ.symm (autMap hζ' P)) := by
  rcases P with _ | ⟨x, y, hns⟩
  · show autMap hζ (mapVariableChangeFun W' ⟨δ, 0, 0, 0⟩ (equivOfEq hψ.symm 0))
      = mapVariableChangeFun W' ⟨δ, 0, 0, 0⟩ (equivOfEq hψ.symm (autMap hζ' 0))
    simp only [_root_.map_zero, mapVariableChangeFun_zero]
  · rw [equivOfEq_some, mapVariableChangeFun_some, autMap_apply, equivOfEq_some,
      mapVariableChangeFun_some, autMap_apply, equivOfEq_some, mapVariableChangeFun_some,
      equivOfEq_some, mapVariableChangeFun_some]
    refine some_eq_some W' ?_ ?_ <;> ring

end Quartic

/-- **An injective endomorphism maps a finite cyclic subgroup ONTO itself.**  This is the
upgrade of "maps `⟨g⟩` into `⟨g⟩`" to "maps `⟨g⟩` onto `⟨g⟩`" that the descent argument needs
in both directions, and it is exactly where `hN : N ≠ 0` and `hg : addOrderOf g = N` are
consumed: they make `AddSubgroup.zmultiples g` finite, via `Nat.card_zmultiples`. -/
lemma exists_mem_zmultiples_eq {A : Type*} [AddCommGroup A] {g : A} {N : ℕ} (hN : N ≠ 0)
    (hg : addOrderOf g = N) (f : A →+ A) (hinj : Function.Injective f)
    (hmaps : ∀ x ∈ AddSubgroup.zmultiples g, f x ∈ AddSubgroup.zmultiples g)
    {y : A} (hy : y ∈ AddSubgroup.zmultiples g) :
    ∃ x ∈ AddSubgroup.zmultiples g, f x = y := by
  haveI : Finite (AddSubgroup.zmultiples g) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hg]; exact hN)
  have hFinj : Function.Injective
      (fun x : AddSubgroup.zmultiples g => (⟨f x, hmaps x x.2⟩ : AddSubgroup.zmultiples g)) :=
    fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab))
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hFinj) ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

/-! ### The quartic twist over a Galois extension -/

section BaseChange

variable {K : Type*} [Field K] [CharZero K] {Ω : Type*} [Field Ω] [Algebra K Ω] [DecidableEq Ω]
  [CharZero Ω]

/-- Base change of an elliptic curve is elliptic; `local` because it would otherwise fire in
every statement mentioning a base-changed curve. -/
local instance isEllipticBaseChange {E : WeierstrassCurve K} [E.IsElliptic] : (E⁄Ω).IsElliptic :=
  inferInstanceAs (E.map (algebraMap K Ω)).IsElliptic

omit [CharZero K] [CharZero Ω] in
/-- **The twisting identity.**  With `ψ` the isomorphism `(x, y) ↦ (δ²x, δ³y)` from `E⁄Ω` to the
quartic twist `E'⁄Ω`, and `σ(δ) = ζδ`, one has `σ(ψ P) = [ζ](ψ(σ P))`.  This is the one place
where the twist fails to be defined over `K`, and the failure is exactly the fourth root of
unity `ζ`. -/
lemma map_twist {E E' : WeierstrassCurve K} [E.IsElliptic] [E'.IsElliptic] {δ ζ : Ωˣ}
    (hψ : (⟨δ, 0, 0, 0⟩ : VariableChange Ω) • (E'⁄Ω) = (E⁄Ω))
    (hζ : (⟨ζ, 0, 0, 0⟩ : VariableChange Ω) • (E'⁄Ω) = (E'⁄Ω))
    (σ : Ω ≃ₐ[K] Ω) (hσδ : σ.toAlgHom (δ : Ω) = (ζ : Ω) * (δ : Ω))
    (P : (E⁄Ω).toAffine.Point) :
    Affine.Point.map σ.toAlgHom
        (mapVariableChangeFun (E'⁄Ω) ⟨δ, 0, 0, 0⟩ (equivOfEq hψ.symm P))
      = autMap hζ (mapVariableChangeFun (E'⁄Ω) ⟨δ, 0, 0, 0⟩
          (equivOfEq hψ.symm (Affine.Point.map σ.toAlgHom P))) := by
  rcases P with _ | ⟨x, y, hns⟩
  · show Affine.Point.map σ.toAlgHom
        (mapVariableChangeFun (E'⁄Ω) ⟨δ, 0, 0, 0⟩ (equivOfEq hψ.symm 0))
      = autMap hζ (mapVariableChangeFun (E'⁄Ω) ⟨δ, 0, 0, 0⟩
          (equivOfEq hψ.symm (Affine.Point.map σ.toAlgHom 0)))
    simp only [_root_.map_zero, mapVariableChangeFun_zero]
  · rw [equivOfEq_some, mapVariableChangeFun_some, Affine.Point.map_some,
      Affine.Point.map_some, equivOfEq_some, mapVariableChangeFun_some, autMap_apply,
      equivOfEq_some, mapVariableChangeFun_some]
    refine some_eq_some (E'⁄Ω) ?_ ?_ <;>
      simp only [map_add, map_mul, map_pow, _root_.map_zero, hσδ] <;> ring

omit [CharZero K] [CharZero Ω] in
/-- **Galois conjugation of a diagonal automorphism**: `σ ∘ [u] = [σ u] ∘ σ`.  The curve `E` is
defined over `K`, so `σ` fixes its coefficients and carries the automorphism `⟨u,0,0,0⟩` to
`⟨σu,0,0,0⟩`.  This is the `Γ`-equivariance that makes the descent character multiplicative. -/
lemma map_autMap_diag {E : WeierstrassCurve K} [E.IsElliptic] (σ : Ω ≃ₐ[K] Ω) {u v : Ωˣ}
    (h : (⟨u, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω))
    (h' : (⟨v, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω))
    (hv : (v : Ω) = σ.toAlgHom (u : Ω)) (P : (E⁄Ω).toAffine.Point) :
    Affine.Point.map σ.toAlgHom (autMap h P) = autMap h' (Affine.Point.map σ.toAlgHom P) := by
  rcases P with _ | ⟨x, y, hns⟩
  · show Affine.Point.map σ.toAlgHom (autMap h 0)
      = autMap h' (Affine.Point.map σ.toAlgHom 0)
    simp only [_root_.map_zero]
  · rw [autMap_apply, equivOfEq_some, mapVariableChangeFun_some, Affine.Point.map_some,
      Affine.Point.map_some, autMap_apply, equivOfEq_some, mapVariableChangeFun_some]
    refine some_eq_some (E⁄Ω) ?_ ?_ <;> simp [map_mul, map_pow, hv]

open scoped Classical in
/-- **The descent character at `j = 1728`.**  `χ(σ) = 1` exactly when `σ` stabilises the cyclic
subgroup `⟨g⟩ ⊆ E(Ω)`, and `χ(σ) = -1` otherwise.

It is valued in `K` rather than in `Ω` on purpose: `μ₄/μ₂ ≅ μ₂ = {±1}` carries the TRIVIAL
Galois action, which is exactly why `χ` is a homomorphism (`quarticTwistChar_mul`) and not a
mere `1`-cocycle — the asymmetry with the sextic case at `j = 0`, where `μ₆/μ₂ ≅ μ₃` and the
action is the quadratic character of `K(ζ₃)`. -/
noncomputable def quarticTwistChar {E : WeierstrassCurve K} [E.IsElliptic]
    (g : (E⁄Ω).toAffine.Point) (σ : Ω ≃ₐ[K] Ω) : K :=
  if ∀ x ∈ AddSubgroup.zmultiples g,
      Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g then 1 else -1

omit [CharZero Ω] in
lemma quarticTwistChar_eq_one_iff {E : WeierstrassCurve K} [E.IsElliptic]
    (g : (E⁄Ω).toAffine.Point) (σ : Ω ≃ₐ[K] Ω) :
    quarticTwistChar g σ = 1 ↔ ∀ x ∈ AddSubgroup.zmultiples g,
      Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g := by
  classical
  unfold quarticTwistChar
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun hc => absurd hc (by norm_num), fun hc => absurd hc h⟩

omit [CharZero K] [CharZero Ω] in
lemma quarticTwistChar_eq_one_or {E : WeierstrassCurve K} [E.IsElliptic]
    (g : (E⁄Ω).toAffine.Point) (σ : Ω ≃ₐ[K] Ω) :
    quarticTwistChar g σ = 1 ∨ quarticTwistChar g σ = -1 := by
  classical
  unfold quarticTwistChar
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The descent character is a group homomorphism** (PROVEN 2026-07-28).

The orbit of `⟨g⟩` under `Gal(Ω/K)` has at most two elements — `⟨g⟩` and `[ι]⁻¹⟨g⟩` — because
`haut` says every `σ⟨g⟩` is `[u_σ]⁻¹⟨g⟩` with `u_σ ∈ μ₄`, and `u_σ² = ±1` splits `μ₄` into
`{±1}` (which preserves `⟨g⟩`, `autMap_eq_self_or_neg`) and `{±ι.u}` (which does not, `hmove`).
Multiplicativity is then the four-case check on `(στ)⟨g⟩ = σ(τ⟨g⟩)`, and the two cases where
`σ` has to be moved past `[ι]` use `map_autMap_diag` together with `σ(ι.u) = ±ι.u` — forced
because `σ(ι.u)² = σ(-1) = -1` and a field has only two square roots of `-1`.  The last case
closes with `autMap_diag_sq`: `[ι]² = [-1]`, so applying `[ι]` twice lands back in `⟨g⟩`. -/
theorem quarticTwistChar_mul {N : ℕ} (hN : N ≠ 0) (E : WeierstrassCurve K)
    [E.IsElliptic] (h₁ : (E⁄Ω).a₁ = 0) (h₂ : (E⁄Ω).a₂ = 0) (h₃ : (E⁄Ω).a₃ = 0)
    (h₆ : (E⁄Ω).a₆ = 0) (ha₄ : (E⁄Ω).a₄ ≠ 0)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (haut : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
      ∀ x ∈ AddSubgroup.zmultiples g,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g)
    (ι : VariableChange Ω) (hι : ι • (E⁄Ω) = (E⁄Ω))
    (hmove : ∃ x ∈ AddSubgroup.zmultiples g, autMap hι x ∉ AddSubgroup.zmultiples g)
    (hu : (ι.u : Ω) ^ 2 = -1) (σ τ : Ω ≃ₐ[K] Ω) :
    quarticTwistChar g (σ * τ) = quarticTwistChar g σ * quarticTwistChar g τ := by
  classical
  obtain ⟨hιdiag, hιu4⟩ := aut_eq_diag h₁ h₂ h₃ h₆ ha₄ hι
  have hιd : (⟨ι.u, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) :=
    smul_diag_self h₁ h₂ h₃ h₆ hιu4
  have hmove' : ∃ x ∈ AddSubgroup.zmultiples g, autMap hιd x ∉ AddSubgroup.zmultiples g := by
    obtain ⟨x, hx, hx'⟩ := hmove
    exact ⟨x, hx, by rwa [← autMap_congr hιdiag hι hιd]⟩
  have hcomp : ∀ (ρ π : Ω ≃ₐ[K] Ω) (x : (E⁄Ω).toAffine.Point),
      Affine.Point.map (ρ * π).toAlgHom x
        = Affine.Point.map ρ.toAlgHom (Affine.Point.map π.toAlgHom x) := by
    intro ρ π x
    rw [Affine.Point.map_map]
    rfl
  -- every `ρ` either stabilises `⟨g⟩` or carries it to `[ι]⁻¹⟨g⟩`
  have hAorB : ∀ ρ : Ω ≃ₐ[K] Ω,
      (∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map ρ.toAlgHom x ∈ AddSubgroup.zmultiples g) ∨
      (∀ x ∈ AddSubgroup.zmultiples g,
        autMap hιd (Affine.Point.map ρ.toAlgHom x) ∈ AddSubgroup.zmultiples g) := by
    intro ρ
    obtain ⟨C, hCsmul, hCmem⟩ := haut ρ
    obtain ⟨hCdiag, hCu4⟩ := aut_eq_diag h₁ h₂ h₃ h₆ ha₄ hCsmul
    rcases mul_eq_zero.mp
      (show ((C.u : Ω) ^ 2 - 1) * ((C.u : Ω) ^ 2 + 1) = 0 by linear_combination hCu4) with hq | hq
    · refine Or.inl fun x hx => ?_
      rcases autMap_eq_self_or_neg h₁ h₂ h₃ h₆ ha₄ hCsmul (by linear_combination hq)
        (Affine.Point.map ρ.toAlgHom x) with he | he
      · rw [← he]; exact hCmem x hx
      · have hm := hCmem x hx
        rw [he] at hm
        simpa using neg_mem hm
    · refine Or.inr fun x hx => ?_
      have hsq : (C.u : Ω) ^ 2 = -1 := by linear_combination hq
      have hCd : (⟨C.u, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) :=
        smul_diag_self h₁ h₂ h₃ h₆ hCu4
      rcases mul_eq_zero.mp (show ((ι.u : Ω) - (C.u : Ω)) * ((ι.u : Ω) + (C.u : Ω)) = 0 by
          linear_combination hu - hsq) with he | he
      · have hιC : (⟨ι.u, 0, 0, 0⟩ : VariableChange Ω) = C := by
          rw [show ι.u = C.u from Units.ext (sub_eq_zero.mp he)]; exact hCdiag.symm
        rw [autMap_congr hιC hιd hCsmul]
        exact hCmem x hx
      · have hιneg : (⟨ι.u, 0, 0, 0⟩ : VariableChange Ω) = ⟨-C.u, 0, 0, 0⟩ := by
          rw [show ι.u = -C.u from Units.ext (by push_cast; linear_combination he)]
        have hnegsmul : (⟨-C.u, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) := hιneg ▸ hιd
        rw [autMap_congr hιneg hιd hnegsmul, autMap_diag_neg h₁ h₃ hCd hnegsmul]
        refine neg_mem ?_
        rw [autMap_congr hCdiag.symm hCd hCsmul]
        exact hCmem x hx
  -- the two alternatives are exclusive: `hmove` forbids both
  have hnotAB : ∀ ρ : Ω ≃ₐ[K] Ω,
      (∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map ρ.toAlgHom x ∈ AddSubgroup.zmultiples g) →
      ¬ (∀ x ∈ AddSubgroup.zmultiples g,
        autMap hιd (Affine.Point.map ρ.toAlgHom x) ∈ AddSubgroup.zmultiples g) := by
    intro ρ hA hB
    obtain ⟨x, hx, hx'⟩ := hmove'
    obtain ⟨y, hy, hyx⟩ := exists_mem_zmultiples_eq hN hg (Affine.Point.map ρ.toAlgHom)
      (Affine.Point.map_injective ρ.toAlgHom) hA hx
    exact hx' (by rw [← hyx]; exact hB y hy)
  -- Galois conjugation moves `[ι]` to `±[ι]`
  have hconj : ∀ (ρ : Ω ≃ₐ[K] Ω) (P : (E⁄Ω).toAffine.Point),
      autMap hιd (Affine.Point.map ρ.toAlgHom P)
          = Affine.Point.map ρ.toAlgHom (autMap hιd P) ∨
      autMap hιd (Affine.Point.map ρ.toAlgHom P)
          = -(Affine.Point.map ρ.toAlgHom (autMap hιd P)) := by
    intro ρ P
    have hne : ρ.toAlgHom (ι.u : Ω) ≠ 0 := by
      intro h0
      exact ι.u.ne_zero (ρ.injective (by rw [_root_.map_zero]; exact h0))
    set w : Ωˣ := Units.mk0 (ρ.toAlgHom (ι.u : Ω)) hne with hwdef
    have hw2 : (w : Ω) ^ 2 = -1 := by
      show ρ.toAlgHom (ι.u : Ω) ^ 2 = -1
      rw [← map_pow, hu]
      simp
    have hw4 : (w : Ω) ^ 4 = 1 := by linear_combination ((w : Ω) ^ 2 - 1) * hw2
    have hwd : (⟨w, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) :=
      smul_diag_self h₁ h₂ h₃ h₆ hw4
    have hkey := map_autMap_diag ρ hιd hwd rfl P
    rcases mul_eq_zero.mp (show ((w : Ω) - (ι.u : Ω)) * ((w : Ω) + (ι.u : Ω)) = 0 by
        linear_combination hw2 - hu) with he | he
    · refine Or.inl ?_
      have hweq : (⟨w, 0, 0, 0⟩ : VariableChange Ω) = ⟨ι.u, 0, 0, 0⟩ := by
        rw [show w = ι.u from Units.ext (sub_eq_zero.mp he)]
      rw [hkey]
      exact (autMap_congr hweq hwd hιd _).symm
    · refine Or.inr ?_
      have hweq : (⟨w, 0, 0, 0⟩ : VariableChange Ω) = ⟨-ι.u, 0, 0, 0⟩ := by
        rw [show w = -ι.u from Units.ext (by push_cast; linear_combination he)]
      have hnegsmul : (⟨-ι.u, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) := hweq ▸ hwd
      rw [hkey, autMap_congr hweq hwd hnegsmul, autMap_diag_neg h₁ h₃ hιd hnegsmul, neg_neg]
  -- the four cases
  by_cases hAσ : ∀ x ∈ AddSubgroup.zmultiples g,
      Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g
  · by_cases hAτ : ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map τ.toAlgHom x ∈ AddSubgroup.zmultiples g
    · rw [(quarticTwistChar_eq_one_iff g _).mpr (fun x hx => by
        rw [hcomp]; exact hAσ _ (hAτ x hx)),
        (quarticTwistChar_eq_one_iff g _).mpr hAσ, (quarticTwistChar_eq_one_iff g _).mpr hAτ,
        one_mul]
    · have hBτ := (hAorB τ).resolve_left hAτ
      have hBστ : ∀ x ∈ AddSubgroup.zmultiples g,
          autMap hιd (Affine.Point.map (σ * τ).toAlgHom x) ∈ AddSubgroup.zmultiples g := by
        intro x hx
        rw [hcomp]
        rcases hconj σ (Affine.Point.map τ.toAlgHom x) with he | he
        · rw [he]; exact hAσ _ (hBτ x hx)
        · rw [he]; exact neg_mem (hAσ _ (hBτ x hx))
      have hone := (quarticTwistChar_eq_one_or g (σ * τ)).resolve_left
        (fun hc => hnotAB _ ((quarticTwistChar_eq_one_iff g _).mp hc) hBστ)
      have htwo := (quarticTwistChar_eq_one_or g τ).resolve_left
        (fun hc => hAτ ((quarticTwistChar_eq_one_iff g _).mp hc))
      rw [hone, htwo, (quarticTwistChar_eq_one_iff g _).mpr hAσ, one_mul]
  · have hBσ := (hAorB σ).resolve_left hAσ
    by_cases hAτ : ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map τ.toAlgHom x ∈ AddSubgroup.zmultiples g
    · have hBστ : ∀ x ∈ AddSubgroup.zmultiples g,
          autMap hιd (Affine.Point.map (σ * τ).toAlgHom x) ∈ AddSubgroup.zmultiples g := by
        intro x hx
        rw [hcomp]
        exact hBσ _ (hAτ x hx)
      have hone := (quarticTwistChar_eq_one_or g (σ * τ)).resolve_left
        (fun hc => hnotAB _ ((quarticTwistChar_eq_one_iff g _).mp hc) hBστ)
      have htwo := (quarticTwistChar_eq_one_or g σ).resolve_left
        (fun hc => hAσ ((quarticTwistChar_eq_one_iff g _).mp hc))
      rw [hone, htwo, (quarticTwistChar_eq_one_iff g _).mpr hAτ, mul_one]
    · have hBτ := (hAorB τ).resolve_left hAτ
      have hAστ : ∀ x ∈ AddSubgroup.zmultiples g,
          Affine.Point.map (σ * τ).toAlgHom x ∈ AddSubgroup.zmultiples g := by
        intro x hx
        rw [hcomp]
        set y := Affine.Point.map τ.toAlgHom x with hydef
        have hz : autMap hιd y ∈ AddSubgroup.zmultiples g := hBτ x hx
        have hstep : autMap hιd (autMap hιd (Affine.Point.map σ.toAlgHom y))
            ∈ AddSubgroup.zmultiples g := by
          rcases hconj σ y with he | he
          · rw [he]
            exact hBσ _ hz
          · rw [he, map_neg]
            exact neg_mem (hBσ _ hz)
        rw [autMap_diag_sq h₁ h₃ hu hιd] at hstep
        simpa using neg_mem hstep
      have hone := (quarticTwistChar_eq_one_iff g (σ * τ)).mpr hAστ
      have htwo := (quarticTwistChar_eq_one_or g σ).resolve_left
        (fun hc => hAσ ((quarticTwistChar_eq_one_iff g _).mp hc))
      have hthree := (quarticTwistChar_eq_one_or g τ).resolve_left
        (fun hc => hAτ ((quarticTwistChar_eq_one_iff g _).mp hc))
      rw [hone, htwo, hthree]
      norm_num

/-- **The descent character computes `u_σ²`** (PROVEN 2026-07-28).

`aut_eq_diag` puts `C = ⟨u,0,0,0⟩` with `u⁴ = 1`, so `u² = ±1`.  If `u² = 1` then `[C] = ±1`
(`autMap_eq_self_or_neg`) and `haut`'s conclusion collapses to `σ⟨g⟩ ⊆ ⟨g⟩`, i.e. `χ(σ) = 1`.
If `u² = -1` then `C = ±ι` — a field has two square roots of `-1` — so were `σ` to stabilise
`⟨g⟩` it would stabilise it ONTO (`exists_mem_zmultiples_eq`, using `addOrderOf g = N ≠ 0`) and
`[ι]` would preserve `⟨g⟩`, contradicting `hmove`; hence `χ(σ) = -1`. -/
theorem algebraMap_quarticTwistChar_eq {N : ℕ} (hN : N ≠ 0) (E : WeierstrassCurve K)
    [E.IsElliptic] (h₁ : (E⁄Ω).a₁ = 0) (h₂ : (E⁄Ω).a₂ = 0) (h₃ : (E⁄Ω).a₃ = 0)
    (h₆ : (E⁄Ω).a₆ = 0) (ha₄ : (E⁄Ω).a₄ ≠ 0)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (ι : VariableChange Ω) (hι : ι • (E⁄Ω) = (E⁄Ω))
    (hmove : ∃ x ∈ AddSubgroup.zmultiples g, autMap hι x ∉ AddSubgroup.zmultiples g)
    (hu : (ι.u : Ω) ^ 2 = -1)
    (σ : Ω ≃ₐ[K] Ω) (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω))
    (hC : ∀ x ∈ AddSubgroup.zmultiples g,
      autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g) :
    algebraMap K Ω (quarticTwistChar g σ) = (C.u : Ω) ^ 2 := by
  classical
  obtain ⟨hCdiag, hCu4⟩ := aut_eq_diag h₁ h₂ h₃ h₆ ha₄ h
  obtain ⟨hιdiag, hιu4⟩ := aut_eq_diag h₁ h₂ h₃ h₆ ha₄ hι
  have hCd : (⟨C.u, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) :=
    smul_diag_self h₁ h₂ h₃ h₆ hCu4
  rcases mul_eq_zero.mp
    (show ((C.u : Ω) ^ 2 - 1) * ((C.u : Ω) ^ 2 + 1) = 0 by linear_combination hCu4) with hq | hq
  · have hsq : (C.u : Ω) ^ 2 = 1 := by linear_combination hq
    have hchar : quarticTwistChar g σ = 1 := by
      rw [quarticTwistChar_eq_one_iff]
      intro x hx
      have hax := hC x hx
      rcases autMap_eq_self_or_neg h₁ h₂ h₃ h₆ ha₄ h hsq
        (Affine.Point.map σ.toAlgHom x) with he | he
      · rwa [he] at hax
      · rw [he] at hax
        simpa using neg_mem hax
    rw [hchar, map_one, hsq]
  · have hsq : (C.u : Ω) ^ 2 = -1 := by linear_combination hq
    have hchar : quarticTwistChar g σ = -1 := by
      rcases quarticTwistChar_eq_one_or g σ with hc | hc
      · exfalso
        rw [quarticTwistChar_eq_one_iff] at hc
        have hpres : ∀ y ∈ AddSubgroup.zmultiples g,
            autMap h y ∈ AddSubgroup.zmultiples g := by
          intro y hy
          obtain ⟨x, hx, hxy⟩ := exists_mem_zmultiples_eq hN hg (Affine.Point.map σ.toAlgHom)
            (Affine.Point.map_injective σ.toAlgHom) hc hy
          rw [← hxy]; exact hC x hx
        obtain ⟨x, hx, hxmove⟩ := hmove
        refine hxmove ?_
        rcases mul_eq_zero.mp (show ((ι.u : Ω) - (C.u : Ω)) * ((ι.u : Ω) + (C.u : Ω)) = 0 by
            linear_combination hu - hsq) with he | he
        · have hιC : ι = C := by
            rw [hιdiag, hCdiag, show ι.u = C.u from Units.ext (sub_eq_zero.mp he)]
          rw [autMap_congr hιC hι h]
          exact hpres x hx
        · have hιneg : ι = ⟨-C.u, 0, 0, 0⟩ := by
            rw [hιdiag, show ι.u = -C.u from Units.ext (by push_cast; linear_combination he)]
          have hnegsmul : (⟨-C.u, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) := hιneg ▸ hι
          rw [autMap_congr hιneg hι hnegsmul, autMap_diag_neg h₁ h₃ hCd hnegsmul]
          refine neg_mem ?_
          rw [autMap_congr hCdiag.symm hCd h]
          exact hpres x hx
      · exact hc
    rw [hchar, hsq]
    simp

omit [CharZero Ω] in
/-- **The descent character is inflated from a finite Galois level** (opened as a sorry leaf
2026-07-28 while repairing `exists_quarticTwistParameter`; **PROVEN 2026-07-29**).

`χ` depends only on the action of `σ` on `⟨g⟩`, and `Affine.Point.map σ` is an ADDITIVE
homomorphism (`WeierstrassCurve.Affine.Point.map` is bundled as a `→+` in the pin), so
`σ (n • g) = n • σ g`: the whole of `⟨g⟩` is controlled by the single point `g`.  Adjoining
the (at most two) coordinates of `g` and taking the normal closure —
`FiniteGaloisIntermediateField.adjoin K {x_g, y_g}`, which packages
`IntermediateField.finiteDimensional_adjoin`, `normalClosure.is_finiteDimensional` and
`IsGalois.normalClosure` — gives the required `L`.

#### Two corrections to the docstring this leaf was cut with

*It claimed the proof needs all `N` points of `⟨g⟩` and hence `hN`, `hg`.*  It does not: by
additivity only `g`'s own two coordinates are needed, and the hypotheses `{N} (hN) (hg)` have
accordingly been REMOVED from the statement.  (They were never used by any route; the
finiteness of `⟨g⟩` really is used in `algebraMap_quarticTwistChar_eq`, which is presumably
where the claim drifted in from.)

*It did not say that `Ω` must be normal over `K`.*  `normalClosure K L₀ Ω` is Galois over `K`
only when the conjugates are available inside `Ω` — for `K = ℚ`, `Ω = ℚ(2^{1/3})`,
`L₀ = Ω` the normal closure computed inside `Ω` is `Ω` itself, which is not Galois.  So
`[IsAlgClosed Ω]` has been ADDED, and with `halg` it gives `IsGalois K Ω` through
`Field.isGalois_of_isAlgClosed`.  This costs the one call site
(`exists_quarticTwistParameter`) nothing: it already carries `[IsAlgClosed Ω]`. -/
theorem exists_finiteLevel_quarticTwistChar [IsAlgClosed Ω]
    (halg : Algebra.IsAlgebraic K Ω) (E : WeierstrassCurve K) [E.IsElliptic]
    (g : (E⁄Ω).toAffine.Point) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsGalois K L),
      ∀ σ τ : Ω ≃ₐ[K] Ω, (∀ x ∈ L, σ x = τ x) →
        quarticTwistChar g σ = quarticTwistChar g τ := by
  classical
  haveI : IsGalois K Ω := Field.isGalois_of_isAlgClosed halg
  -- agreement on the coordinates of a single point pins down its Galois conjugate
  have hcoord : ∀ P : (E⁄Ω).toAffine.Point, ∃ S : Set Ω, S.Finite ∧
      ∀ σ τ : Ω ≃ₐ[K] Ω, (∀ z ∈ S, σ z = τ z) →
        Affine.Point.map σ.toAlgHom P = Affine.Point.map τ.toAlgHom P := by
    rintro (_ | ⟨x, y, hns⟩)
    · exact ⟨∅, Set.finite_empty, fun _ _ _ => rfl⟩
    · refine ⟨{x, y}, Set.toFinite _, fun σ τ h => ?_⟩
      rw [Affine.Point.map_some, Affine.Point.map_some]
      exact some_eq_some (E⁄Ω) (h x (by simp)) (h y (by simp))
  obtain ⟨S, hSfin, hSmain⟩ := hcoord g
  haveI : Finite S := hSfin
  -- `Affine.Point.map σ` is additive, so `⟨g⟩` is controlled by `g` alone
  have main : ∀ σ τ : Ω ≃ₐ[K] Ω,
      Affine.Point.map σ.toAlgHom g = Affine.Point.map τ.toAlgHom g →
      quarticTwistChar g σ = quarticTwistChar g τ := by
    intro σ τ hst
    have hpt : ∀ z ∈ AddSubgroup.zmultiples g,
        Affine.Point.map σ.toAlgHom z = Affine.Point.map τ.toAlgHom z := by
      intro z hz
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
      rw [map_zsmul, map_zsmul, hst]
    have hiff : (∀ z ∈ AddSubgroup.zmultiples g,
          Affine.Point.map σ.toAlgHom z ∈ AddSubgroup.zmultiples g) ↔
        (∀ z ∈ AddSubgroup.zmultiples g,
          Affine.Point.map τ.toAlgHom z ∈ AddSubgroup.zmultiples g) :=
      ⟨fun H z hz => hpt z hz ▸ H z hz, fun H z hz => (hpt z hz).symm ▸ H z hz⟩
    unfold quarticTwistChar
    split_ifs with ha hb hc
    · rfl
    · exact absurd (hiff.mp ha) hb
    · exact absurd (hiff.mpr hc) ha
    · rfl
  refine ⟨(FiniteGaloisIntermediateField.adjoin K S).toIntermediateField,
    inferInstance, inferInstance, fun σ τ hστ => ?_⟩
  exact main σ τ (hSmain σ τ fun z hz =>
    hστ z (FiniteGaloisIntermediateField.subset_adjoin K S hz))

/-- **The quartic twisting parameter** (opened as a sorry leaf 2026-07-28 by decomposing
`exists_stableCyclic_twist_of_autStable_of_j_eq_1728`; **REFUTED AS STATED, RESTATED, AND
PROVEN 2026-07-28** over `exists_finiteLevel_quarticTwistChar` and
`Field.exists_sq_eq_algebraMap_of_quadraticChar`).

This is the *only* arithmetic input of the `j = 1728` descent, and it is the whole of it: the
obstruction character is a quadratic character, hence cut out by a square root of an element of
`K`, and a fourth root of that element twists the obstruction away.

#### FALSITY AUDIT (2026-07-28) — the previous statement was FALSE, with an explicit witness

The statement carried NO hypothesis on `Ω` beyond `[Field Ω] [Algebra K Ω] [CharZero Ω]`, and
its conclusion demands a fourth root `δ ∈ Ω` of an element of `K`.  A field that is not big
enough simply has no such `δ`, and no amount of arithmetic input produces one.  Witness:

* `K := ℚ`, `Ω := ℚ(ζ₈) = ℚ(i, √2)` — Galois over `ℚ` with group `(ℤ/8)ˣ = {1, σ₃, σ₅, σ₇}`;
* `E : y² = x³ - 2x`, i.e. `quarticModel (-2)`.  `Δ = -64·(-2)³ = 512 ≠ 0`, so `E` is elliptic
  and `a₁ = a₂ = a₃ = a₆ = 0`, `a₄ = -2 ≠ 0`;
* `N := 2` and `g := (√2, 0) ∈ E(Ω)` — indeed `(√2)³ - 2√2 = 0` — of order `2`;
* `ι := ⟨i, 0, 0, 0⟩`, so `hι` holds (`i⁴ = 1`, `smul_diag_self`) and `hu : i² = -1`.

`hmove` holds: `autMap hι (√2, 0) = (i²·√2, i³·0) = (-√2, 0) ∉ {O, (√2,0)} = ⟨g⟩`.  `haut`
holds: `σ₇` fixes `√2`, so `C := 1` works; `σ₃` and `σ₅` send `√2 ↦ -√2`, and `C := ι` sends
`(-√2, 0)` back to `(√2, 0)`, so `C := ι` works.  Every hypothesis is satisfied.

Now write `ε := δ²`.  The conclusion at `σ₇` with `C = 1` forces `σ₇(ε) = ε`; at `σ₃` with
`C = ι` it forces `σ₃(ε) = -ε`.  So `ε` lies in the `ℚ(√2)` of `ℚ(ζ₈)` and is negated by `σ₃`,
i.e. `ε = q√2` for some `q ∈ ℚˣ`.  But `q√2` is **never** a square in `ℚ(ζ₈)`: if `x² = q√2`
then `σ₇(x)² = x²`, so `x ∈ ℚ(√2)` or `x ∈ ℚ(√2)·i` (the two eigenspaces of `σ₇` over its fixed
field `ℚ(√2)`), and in either case `y² = ±q√2` with `y ∈ ℚ(√2)`, whence
`N_{ℚ(√2)/ℚ}(y)² = N(±q√2) = -2q² < 0` — impossible, a norm of a square being a square in `ℚ`.
So no `δ` exists and the leaf was false.

**The mathematics was never in doubt; the QUANTIFIER over `Ω` was.**  Over `ℚ̄` the descent does
work here: `δ = 2^{3/4}`, `d = 8`, `E' : y² = x³ - 16x`, `ψ g = (4, 0)` — which is even
`ℚ`-rational.  But `2^{3/4} ∉ ℚ(ζ₈)`.

#### The repair, and why it costs the consumers nothing

`Ω` must be an ALGEBRAIC CLOSURE of `K`: `[IsAlgClosed Ω]` together with
`halg : Algebra.IsAlgebraic K Ω`.  `Algebra.IsAlgebraic` is not redundant decoration next to
`IsAlgClosed`: it is what makes `Gal(Ω/K)` an honest absolute Galois group with fixed field
`K`, which Hilbert 90 needs.  The two downstream theorems in this file carry the same two
hypotheses and their proofs are otherwise unchanged.

**Why `halg` is an EXPLICIT argument and not an instance** — this is not a style choice, it is
forced.  `Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` is NOT SYNTHESIZABLE anywhere in this
tree: at the literal base field `ℚ` the two `Algebra ℚ ℚ̄` instances form a DIAMOND, a condition
already documented in `X0.lean`'s own `mem_range_of_fixed` ("at the literal `F = ℚ` the two
`Algebra ℚ ℚ̄` instances form a diamond and `IsAlgClosure ℚ ℚ̄` fails to synthesise") and worked
around by hand in `Fermat/FLT/Modularity/Patching.lean` with
`haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ`.
Verified here rather than assumed: under X0's exact import surface, `IsAlgClosed ℚ̄` synthesises
but `Algebra.IsAlgebraic ℚ ℚ̄` and `IsAlgClosure ℚ ℚ̄` both fail, and RE-DECLARING the mathlib
instance in this file does **not** fix it — the diamond is in the `Algebra` instance itself, so
no re-export can reach it.  Making it an instance argument would therefore hand every consumer
an unsatisfiable obligation.  As an explicit argument it costs the one call site a single extra
token, `AlgebraicClosure.isAlgebraic ℚ`, and it puts the requirement where a consumer must
confront it.  `[IsAlgClosed Ω]` stays an instance because it does synthesise.

#### The route, now that it is proven

`E⁄Ω` is `y² = x³ + a₄x`, so by `aut_eq_diag` every automorphism is `⟨u,0,0,0⟩` with `u⁴ = 1`,
i.e. `Aut(E⁄Ω) ↪ μ₄` with `u` injective; `hu` shows the image is all of `μ₄`.  Write
`A := {C ∈ Aut : C preserves ⟨g⟩}`.  Both `1` and `⟨-1,0,0,0⟩` lie in `A` — they act as the
identity and as negation, `autMap_diag_one` and `autMap_diag_neg` — and `hmove` says `ι ∉ A`,
so `A = μ₂` and `[μ₄ : A] = 2`.

`quarticTwistChar` is the resulting sign `χ(σ) = u_σ² ∈ {±1}`;
`algebraMap_quarticTwistChar_eq` is the statement that it really computes `u_σ²` for EVERY
admissible `C`, and `quarticTwistChar_mul` that it is a group homomorphism — which holds
because `μ₄/μ₂ ≅ μ₂` carries the trivial Galois action.  `exists_finiteLevel_quarticTwistChar`
gives its finite level, and `Field.exists_sq_eq_algebraMap_of_quadraticChar` turns it into
`s ∈ Ω` with `s² = d ∈ Kˣ` and `σ(s) = χ(σ)·s`.  Finally `δ := √s` exists because `Ω` is
algebraically closed, and `δ⁴ = s² = d`, `σ(δ)² = σ(s) = χ(σ)δ² = δ²·u_σ²`.  ∎

**No Kummer theory beyond `n = 2` is used** — only that an open index-`2` subgroup of
`Gal(Ω/K)` is the stabiliser of a square root.  (Its sibling at `j = 0` genuinely needs
`H¹(Γ, μ₃)`; that asymmetry is why the two leaves were split.)

#### Non-vacuity

`hmove` is REQUIRED and is what makes the conclusion satisfiable at all: if some automorphism
with `u² = -1` preserved `⟨g⟩` then, for a single `σ`, both `C` and `C · ι` would satisfy the
hypothesis of the conclusion with values of `(C.u)²` differing by a sign, and no `δ` could
satisfy both.  `hN` and `hg` are consumed twice over — once for the finiteness of `⟨g⟩` that
upgrades "maps into" to "maps onto" in `algebraMap_quarticTwistChar_eq`, and once for the
finite level of `χ`. -/
theorem exists_quarticTwistParameter [IsAlgClosed Ω] (halg : Algebra.IsAlgebraic K Ω)
    {N : ℕ} (hN : N ≠ 0) (E : WeierstrassCurve K)
    [E.IsElliptic] (h₁ : (E⁄Ω).a₁ = 0) (h₂ : (E⁄Ω).a₂ = 0) (h₃ : (E⁄Ω).a₃ = 0)
    (h₆ : (E⁄Ω).a₆ = 0) (ha₄ : (E⁄Ω).a₄ ≠ 0)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (haut : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
      ∀ x ∈ AddSubgroup.zmultiples g,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g)
    (ι : VariableChange Ω) (hι : ι • (E⁄Ω) = (E⁄Ω))
    (hmove : ∃ x ∈ AddSubgroup.zmultiples g, autMap hι x ∉ AddSubgroup.zmultiples g)
    (hu : (ι.u : Ω) ^ 2 = -1) :
    ∃ (d : K) (_ : d ≠ 0) (δ : Ωˣ), (δ : Ω) ^ 4 = algebraMap K Ω d ∧
      ∀ (σ : Ω ≃ₐ[K] Ω) (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
        (∀ x ∈ AddSubgroup.zmultiples g,
          autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g) →
        σ (δ : Ω) ^ 2 = (δ : Ω) ^ 2 * (C.u : Ω) ^ 2 := by
  obtain ⟨L, hLfin, hLgal, hLinfl⟩ := exists_finiteLevel_quarticTwistChar halg E g
  obtain ⟨d, s, hd0, hs2, hs⟩ :=
    Field.exists_sq_eq_algebraMap_of_quadraticChar halg (quarticTwistChar g)
      (quarticTwistChar_eq_one_or g)
      (quarticTwistChar_mul hN E h₁ h₂ h₃ h₆ ha₄ g hg haut ι hι hmove hu) L hLinfl
  have hs0 : s ≠ 0 := by
    intro h0
    apply hd0
    have hz : algebraMap K Ω d = 0 := by rw [← hs2, h0]; ring
    exact (map_eq_zero_iff _ (algebraMap K Ω).injective).mp hz
  obtain ⟨δ0, hδ0⟩ := IsAlgClosed.exists_pow_nat_eq (k := Ω) s (n := 2) two_pos
  have hδ0ne : δ0 ≠ 0 := by
    intro h0
    apply hs0
    rw [← hδ0, h0]; ring
  refine ⟨d, hd0, Units.mk0 δ0 hδ0ne, ?_, ?_⟩
  · show δ0 ^ 4 = algebraMap K Ω d
    rw [show δ0 ^ 4 = (δ0 ^ 2) ^ 2 by ring, hδ0, hs2]
  · intro σ C h hC
    show σ δ0 ^ 2 = δ0 ^ 2 * (C.u : Ω) ^ 2
    rw [← map_pow, hδ0, hs σ, ← hδ0,
      algebraMap_quarticTwistChar_eq hN E h₁ h₂ h₃ h₆ ha₄ g hg ι hι hmove hu σ C h hC]
    ring

/-- **The arithmetic heart at `j = 1728`, in normal form** (PROVEN 2026-07-28 over the single
leaf `exists_quarticTwistParameter`).

Given the twisting parameter `d` and a fourth root `δ` of it, the twist is
`E' : y² = x³ + (a₄d)x`, the isomorphism `ψ : E⁄Ω ≅ E'⁄Ω` is `(x, y) ↦ (δ²x, δ³y)`, and
`g' := ψ g`.  For each `σ`, `map_twist` gives `σ(ψ z) = [ζ_σ](ψ(σ z))` with `σδ = ζ_σδ`, and
`autMap_twist_comm` moves `[ζ_σ]` back across `ψ`, so the goal reduces to
`[ζ_σ](σ z) ∈ ⟨g⟩`.  The leaf says `ζ_σ² = u_σ²`, hence `ζ_σ = ±u_σ`, and `autMap_diag_neg` turns
the `−` case into a negation, which `⟨g⟩` absorbs.  `haut` supplies `[u_σ](σ z) ∈ ⟨g⟩`.

The conclusion records `E'.j = 1728` (added 2026-07-30).  It costs nothing — `E'` IS
`quarticModel (a₄ d)` by construction, so `j_quarticModel` reads the value off — and it is
what lets the `j`-invariant survive the twist all the way up to
`exists_stableCyclic_j_of_gamma0Datum_algClos` in `Fermat/FLT/ModularCurve/X0.lean`, which
cannot even be stated without it. -/
theorem exists_stableCyclic_quarticTwist_of_quartic [IsAlgClosed Ω]
    (halg : Algebra.IsAlgebraic K Ω) {N : ℕ} (hN : N ≠ 0) (E : WeierstrassCurve K)
    [E.IsElliptic] (h₁ : (E⁄Ω).a₁ = 0) (h₂ : (E⁄Ω).a₂ = 0) (h₃ : (E⁄Ω).a₃ = 0)
    (h₆ : (E⁄Ω).a₆ = 0) (ha₄ : (E⁄Ω).a₄ ≠ 0)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (haut : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
      ∀ x ∈ AddSubgroup.zmultiples g,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g)
    (ι : VariableChange Ω) (hι : ι • (E⁄Ω) = (E⁄Ω))
    (hmove : ∃ x ∈ AddSubgroup.zmultiples g, autMap hι x ∉ AddSubgroup.zmultiples g)
    (hu : (ι.u : Ω) ^ 2 = -1) :
    ∃ (E' : WeierstrassCurve K) (_ : E'.IsElliptic) (g' : (E'⁄Ω).toAffine.Point),
      E'.j = 1728 ∧ addOrderOf g' = N ∧
      ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ AddSubgroup.zmultiples g',
        Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g' := by
  obtain ⟨d, hd, δ, hδ4, hrel⟩ :=
    exists_quarticTwistParameter halg hN E h₁ h₂ h₃ h₆ ha₄ g hg haut ι hι hmove hu
  have hδ0 : (δ : Ω) ≠ 0 := δ.ne_zero
  have hEa₄ : (E⁄Ω).a₄ = algebraMap K Ω E.a₄ := rfl
  have hEa₄K : E.a₄ ≠ 0 := fun h0 => ha₄ (by rw [hEa₄, h0, _root_.map_zero])
  obtain ⟨E', hE'⟩ : ∃ E' : WeierstrassCurve K, E' = quarticModel (E.a₄ * d) := ⟨_, rfl⟩
  have hE'₁ : (E'⁄Ω).a₁ = 0 := by rw [hE', quarticModel_baseChange]; simp
  have hE'₂ : (E'⁄Ω).a₂ = 0 := by rw [hE', quarticModel_baseChange]; simp
  have hE'₃ : (E'⁄Ω).a₃ = 0 := by rw [hE', quarticModel_baseChange]; simp
  have hE'₆ : (E'⁄Ω).a₆ = 0 := by rw [hE', quarticModel_baseChange]; simp
  have hE'₄ : (E'⁄Ω).a₄ = (δ : Ω) ^ 4 * (E⁄Ω).a₄ := by
    rw [hE', quarticModel_baseChange, quarticModel_a₄, hδ4, hEa₄, map_mul]; ring
  haveI hqm : (quarticModel (E.a₄ * d)).IsElliptic :=
    isElliptic_quarticModel (mul_ne_zero hEa₄K hd)
  haveI : E'.IsElliptic := hE' ▸ hqm
  have hjE' : E'.j = 1728 := by simp_rw [hE']; exact j_quarticModel
  have hψ : (⟨δ, 0, 0, 0⟩ : VariableChange Ω) • (E'⁄Ω) = (E⁄Ω) :=
    smul_diag_twist h₁ h₂ h₃ h₆ hE'₁ hE'₂ hE'₃ hE'₆ δ hE'₄
  set ψ : (E⁄Ω).toAffine.Point ≃+ (E'⁄Ω).toAffine.Point :=
    (equivOfEq hψ.symm).trans (equivVariableChange (E'⁄Ω) ⟨δ, 0, 0, 0⟩) with hψdef
  have hψapp : ∀ P, ψ P = mapVariableChangeFun (E'⁄Ω) ⟨δ, 0, 0, 0⟩ (equivOfEq hψ.symm P) :=
    fun _ => rfl
  refine ⟨E', inferInstance, ψ g, hjE', ?_, ?_⟩
  · rw [← hg]; exact ψ.addOrderOf_eq g
  intro σ x hx
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  have hxz : x = ψ (n • g) := by rw [← hn, map_zsmul]
  have hzmem : n • g ∈ AddSubgroup.zmultiples g := AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩
  have hσδ0 : σ.toAlgHom (δ : Ω) ≠ 0 := by
    intro h0
    apply hδ0
    exact σ.injective (show σ (δ : Ω) = σ 0 by rw [_root_.map_zero]; exact h0)
  set ζ : Ωˣ := Units.mk0 (σ.toAlgHom (δ : Ω) / (δ : Ω)) (div_ne_zero hσδ0 hδ0) with hζdef
  have hσδ : σ.toAlgHom (δ : Ω) = (ζ : Ω) * (δ : Ω) := by
    show σ.toAlgHom (δ : Ω) = σ.toAlgHom (δ : Ω) / (δ : Ω) * (δ : Ω)
    field_simp
  have hζ4 : (ζ : Ω) ^ 4 = 1 := by
    have hsq : ((ζ : Ω) * (δ : Ω)) ^ 4 = (δ : Ω) ^ 4 := by
      rw [← hσδ, ← map_pow, hδ4, AlgHom.commutes]
    have h4 : (ζ : Ω) ^ 4 * (δ : Ω) ^ 4 = 1 * (δ : Ω) ^ 4 := by
      rw [one_mul, ← mul_pow]; exact hsq
    exact mul_right_cancel₀ (pow_ne_zero 4 hδ0) h4
  have hζE' : (⟨ζ, 0, 0, 0⟩ : VariableChange Ω) • (E'⁄Ω) = (E'⁄Ω) :=
    smul_diag_self hE'₁ hE'₂ hE'₃ hE'₆ hζ4
  have hζE : (⟨ζ, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) :=
    smul_diag_self h₁ h₂ h₃ h₆ hζ4
  have hkey : Affine.Point.map σ.toAlgHom (ψ (n • g))
      = ψ (autMap hζE (Affine.Point.map σ.toAlgHom (n • g))) := by
    rw [hψapp, hψapp, map_twist hψ hζE' σ hσδ, autMap_twist_comm hψ hζE' hζE]
  obtain ⟨C, hC, hCmem⟩ := haut σ
  obtain ⟨hCdiag, hCu4⟩ := aut_eq_diag h₁ h₂ h₃ h₆ ha₄ hC
  have hCdiagsmul : (⟨C.u, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) :=
    smul_diag_self h₁ h₂ h₃ h₆ hCu4
  have hζu : (ζ : Ω) ^ 2 = (C.u : Ω) ^ 2 := by
    have hr : σ.toAlgHom (δ : Ω) ^ 2 = (δ : Ω) ^ 2 * (C.u : Ω) ^ 2 := hrel σ C hC hCmem
    rw [hσδ, mul_pow] at hr
    exact mul_right_cancel₀ (pow_ne_zero 2 hδ0) (by linear_combination hr)
  have hmem : autMap hζE (Affine.Point.map σ.toAlgHom (n • g)) ∈ AddSubgroup.zmultiples g := by
    rcases mul_eq_zero.mp (show ((ζ : Ω) - (C.u : Ω)) * ((ζ : Ω) + (C.u : Ω)) = 0 by
        linear_combination hζu) with he | he
    · have heq : (⟨ζ, 0, 0, 0⟩ : VariableChange Ω) = C := by
        rw [show ζ = C.u from Units.ext (sub_eq_zero.mp he)]; exact hCdiag.symm
      rw [autMap_congr heq hζE hC]
      exact hCmem _ hzmem
    · have hue : ζ = -C.u := Units.ext (by push_cast; linear_combination he)
      have heq : (⟨ζ, 0, 0, 0⟩ : VariableChange Ω) = ⟨-C.u, 0, 0, 0⟩ := by rw [hue]
      have hnegsmul : (⟨-C.u, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) := heq ▸ hζE
      rw [autMap_congr heq hζE hnegsmul, autMap_diag_neg h₁ h₃ hCdiagsmul hnegsmul]
      refine neg_mem ?_
      rw [autMap_congr hCdiag.symm hCdiagsmul hC]
      exact hCmem _ hzmem
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  rw [hxz, hkey, ← hm, map_zsmul]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, rfl⟩

omit [CharZero K] [CharZero Ω] in
/-- **Conjugation of an automorphism across a variable change defined over the base field.**
An automorphism `D` of `E⁄Ω` becomes the automorphism `C₀ D C₀⁻¹` of `(C₀ • E)⁄Ω`, and
`equivVariableChangeBaseChange` intertwines their actions on points. -/
lemma exists_conj_autMap_baseChange (E : WeierstrassCurve K) [E.IsElliptic]
    (C₀ : VariableChange K) {D : VariableChange Ω} (hD : D • (E⁄Ω) = (E⁄Ω)) :
    ∃ h' : (C₀.baseChange Ω * D * (C₀.baseChange Ω)⁻¹) • ((C₀ • E)⁄Ω) = ((C₀ • E)⁄Ω),
      ∀ P, Affine.Point.equivVariableChangeBaseChange E C₀ Ω (autMap h' P)
        = autMap hD (Affine.Point.equivVariableChangeBaseChange E C₀ Ω P) := by
  have e : ((C₀ • E)⁄Ω) = (C₀.baseChange Ω) • (E⁄Ω) :=
    (map_variableChange (C := C₀) (W := E) (φ := algebraMap K Ω)).symm
  have hconj := conj_smul_smul (E⁄Ω) (C₀.baseChange Ω) hD
  refine ⟨by rw [e]; exact hconj, fun P => ?_⟩
  simp only [Affine.Point.equivVariableChangeBaseChange, AddEquiv.trans_apply]
  rw [equivOfEq_autMap e _ hconj, equivVariableChange_autMap]

/-- **The arithmetic heart at `j = 1728`** (PROVEN 2026-07-28 over the single leaf
`exists_quarticTwistParameter`).

A cyclic subgroup of `E(Ω)` that is Galois-stable only up to an automorphism of `E` becomes
genuinely Galois-stable on a QUARTIC TWIST of `E`, which is again defined over `K`.

The proof puts `E` in the normal form `y² = x³ + a x` over `K`
(`exists_smul_eq_quarticModel`), transports `g`, `haut`, `ι` and `hmove` along the resulting
isomorphism — `exists_conj_autMap_baseChange` conjugates the automorphisms and
`equivVariableChangeBaseChange_galois` says the isomorphism is `Gal(Ω/K)`-equivariant, since
`C₀` has coefficients in `K` — and then applies
`exists_stableCyclic_quarticTwist_of_quartic`. -/
theorem exists_stableCyclic_quarticTwist [IsAlgClosed Ω] (halg : Algebra.IsAlgebraic K Ω)
    {N : ℕ} (hN : N ≠ 0) (E : WeierstrassCurve K)
    [E.IsElliptic] (hj : E.j = 1728)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (haut : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
      ∀ x ∈ AddSubgroup.zmultiples g,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g)
    (ι : VariableChange Ω) (hι : ι • (E⁄Ω) = (E⁄Ω))
    (hmove : ∃ x ∈ AddSubgroup.zmultiples g, autMap hι x ∉ AddSubgroup.zmultiples g)
    (hu : (ι.u : Ω) ^ 2 = -1) :
    ∃ (E' : WeierstrassCurve K) (_ : E'.IsElliptic) (g' : (E'⁄Ω).toAffine.Point),
      E'.j = 1728 ∧ addOrderOf g' = N ∧
      ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ AddSubgroup.zmultiples g',
        Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g' := by
  obtain ⟨C₀, a, ha, hC₀⟩ := exists_smul_eq_quarticModel E hj
  have h₁ : ((C₀ • E)⁄Ω).a₁ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₁) = 0
    rw [hC₀]; simp
  have h₂ : ((C₀ • E)⁄Ω).a₂ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₂) = 0
    rw [hC₀]; simp
  have h₃ : ((C₀ • E)⁄Ω).a₃ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₃) = 0
    rw [hC₀]; simp
  have h₆ : ((C₀ • E)⁄Ω).a₆ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₆) = 0
    rw [hC₀]; simp
  have ha₄ : ((C₀ • E)⁄Ω).a₄ ≠ 0 := by
    show algebraMap K Ω ((C₀ • E).a₄) ≠ 0
    rw [hC₀, quarticModel_a₄]
    exact fun h0 => ha ((algebraMap K Ω).injective (by rw [h0, _root_.map_zero]))
  set Θ := Affine.Point.equivVariableChangeBaseChange E C₀ Ω with hΘdef
  set g₁ := Θ.symm g with hg₁def
  have hΘg : Θ g₁ = g := Θ.apply_symm_apply g
  have hmemΘ : ∀ x : ((C₀ • E)⁄Ω).toAffine.Point,
      x ∈ AddSubgroup.zmultiples g₁ ↔ Θ x ∈ AddSubgroup.zmultiples g := by
    intro x
    simp only [AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, map_zsmul, hΘg]⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Θ.injective (by rw [map_zsmul, hΘg, hn])⟩
  have hg₁ : addOrderOf g₁ = N := by rw [← hg, ← hΘg]; exact (Θ.addOrderOf_eq g₁).symm
  have haut₁ : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • ((C₀ • E)⁄Ω) = ((C₀ • E)⁄Ω)),
      ∀ x ∈ AddSubgroup.zmultiples g₁,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g₁ := by
    intro σ
    obtain ⟨C, hC, hCmem⟩ := haut σ
    obtain ⟨h', hconj⟩ := exists_conj_autMap_baseChange E C₀ hC
    refine ⟨_, h', fun x hx => ?_⟩
    rw [hmemΘ, hconj, Affine.Point.equivVariableChangeBaseChange_galois]
    exact hCmem _ ((hmemΘ x).mp hx)
  obtain ⟨hι₁, hιconj⟩ := exists_conj_autMap_baseChange E C₀ hι
  have hu₁ : ((C₀.baseChange Ω * ι * (C₀.baseChange Ω)⁻¹).u : Ω) ^ 2 = -1 := by
    have hval : (C₀.baseChange Ω * ι * (C₀.baseChange Ω)⁻¹).u = ι.u := by
      show (C₀.baseChange Ω).u * ι.u * ((C₀.baseChange Ω).u)⁻¹ = ι.u
      rw [mul_comm ((C₀.baseChange Ω).u) ι.u, mul_assoc, mul_inv_cancel, mul_one]
    rw [hval]; exact hu
  have hmove₁ : ∃ x ∈ AddSubgroup.zmultiples g₁, autMap hι₁ x ∉ AddSubgroup.zmultiples g₁ := by
    obtain ⟨x, hx, hx'⟩ := hmove
    refine ⟨Θ.symm x, (hmemΘ _).mpr (by rw [Θ.apply_symm_apply]; exact hx), ?_⟩
    intro hcon
    exact hx' (by
      have := (hmemΘ _).mp hcon
      rwa [hιconj, Θ.apply_symm_apply] at this)
  exact exists_stableCyclic_quarticTwist_of_quartic halg hN (C₀ • E) h₁ h₂ h₃ h₆ ha₄ g₁ hg₁
    haut₁ _
    hι₁ hmove₁ hu₁

end BaseChange

end WeierstrassCurve

end
