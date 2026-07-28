/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Aut
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

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
* `WeierstrassCurve.exists_stableCyclic_quarticTwist` : the arithmetic heart at `j = 1728` —
  a cyclic subgroup that is Galois-stable only up to an automorphism becomes genuinely stable
  on a quartic twist.  Proven over the single leaf
  `WeierstrassCurve.exists_quarticTwistParameter`.
-/

@[expose] public section

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

/-- **The quartic twisting parameter** (sorry leaf, opened 2026-07-28 by decomposing
`exists_stableCyclic_twist_of_autStable_of_j_eq_1728`).

This is the *only* arithmetic input of the `j = 1728` descent, and it is the whole of it: the
statement below packages "the obstruction character is a quadratic character, hence cut out by a
square root of a rational number".

#### What has to be proven

`E⁄Ω` is `y² = x³ + a₄x`, so by `aut_eq_diag` every automorphism is `⟨u,0,0,0⟩` with `u⁴ = 1`,
i.e. `Aut(E⁄Ω) ↪ μ₄` with `u` injective; `ι` shows the image is all of `μ₄`.  Write
`A := {C ∈ Aut : C preserves ⟨g⟩}`.  Both `1` and `⟨-1,0,0,0⟩` lie in `A` (they act as the
identity and as negation, `autMap_congr` and `autMap_diag_neg`), and `hmove` says `ι ∉ A`, so
`u(A) = {±1}` and `[μ₄ : u(A)] = 2`.

`haut` therefore determines, for each `σ`, the class `u_σ · {±1} ∈ μ₄/{±1} ≅ μ₂`, i.e. the sign
`χ(σ) := u_σ² ∈ {±1}`; and `χ` is a *group homomorphism* because `μ₄/{±1}` carries the trivial
Galois action (`±1 ∈ K`).  Its kernel is the stabiliser of the finite set `⟨g⟩` and is therefore
OPEN, so `χ` cuts out a quadratic extension of `K`, `K(√d)` with `d ∈ Kˣ`; taking `δ` a fourth
root of `d` gives `σ(δ)²/δ² = σ(√d)/√d = χ(σ) = u_σ²`, which is the conclusion.

**No Kummer theory and no `H¹` is used**: only that an open index-`2` subgroup of `Gal(K̄/K)` is
the stabiliser of a square root, which is elementary in characteristic `≠ 2`.  (Its sibling at
`j = 0` genuinely needs `H¹(Γ, μ₃)`; that asymmetry is why the two leaves were split.)

#### Non-vacuity, and what refutes this leaf

`hmove` is REQUIRED and is what makes the conclusion satisfiable at all: if some automorphism
with `u² = -1` preserved `⟨g⟩` then, for a single `σ`, both `C` and `C · ι` would satisfy the
hypothesis of the conclusion with values of `(C.u)²` differing by a sign, and no `δ` could
satisfy both.  A refutation would exhibit such a configuration together with a `σ`; there is
none, since `hmove` puts `ι ∉ A` and `A` is a subgroup.

`hN` and `hg` enter through the finiteness of `⟨g⟩`, which is what makes `ker χ` open. -/
theorem exists_quarticTwistParameter {N : ℕ} (hN : N ≠ 0) (E : WeierstrassCurve K)
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
        σ (δ : Ω) ^ 2 = (δ : Ω) ^ 2 * (C.u : Ω) ^ 2 :=
  sorry

/-- **The arithmetic heart at `j = 1728`, in normal form** (PROVEN 2026-07-28 over the single
leaf `exists_quarticTwistParameter`).

Given the twisting parameter `d` and a fourth root `δ` of it, the twist is
`E' : y² = x³ + (a₄d)x`, the isomorphism `ψ : E⁄Ω ≅ E'⁄Ω` is `(x, y) ↦ (δ²x, δ³y)`, and
`g' := ψ g`.  For each `σ`, `map_twist` gives `σ(ψ z) = [ζ_σ](ψ(σ z))` with `σδ = ζ_σδ`, and
`autMap_twist_comm` moves `[ζ_σ]` back across `ψ`, so the goal reduces to
`[ζ_σ](σ z) ∈ ⟨g⟩`.  The leaf says `ζ_σ² = u_σ²`, hence `ζ_σ = ±u_σ`, and `autMap_diag_neg` turns
the `−` case into a negation, which `⟨g⟩` absorbs.  `haut` supplies `[u_σ](σ z) ∈ ⟨g⟩`. -/
theorem exists_stableCyclic_quarticTwist_of_quartic {N : ℕ} (hN : N ≠ 0) (E : WeierstrassCurve K)
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
      addOrderOf g' = N ∧
      ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ AddSubgroup.zmultiples g',
        Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g' := by
  obtain ⟨d, hd, δ, hδ4, hrel⟩ :=
    exists_quarticTwistParameter hN E h₁ h₂ h₃ h₆ ha₄ g hg haut ι hι hmove hu
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
  haveI : E'.IsElliptic := hE' ▸ isElliptic_quarticModel (mul_ne_zero hEa₄K hd)
  have hψ : (⟨δ, 0, 0, 0⟩ : VariableChange Ω) • (E'⁄Ω) = (E⁄Ω) :=
    smul_diag_twist h₁ h₂ h₃ h₆ hE'₁ hE'₂ hE'₃ hE'₆ δ hE'₄
  set ψ : (E⁄Ω).toAffine.Point ≃+ (E'⁄Ω).toAffine.Point :=
    (equivOfEq hψ.symm).trans (equivVariableChange (E'⁄Ω) ⟨δ, 0, 0, 0⟩) with hψdef
  have hψapp : ∀ P, ψ P = mapVariableChangeFun (E'⁄Ω) ⟨δ, 0, 0, 0⟩ (equivOfEq hψ.symm P) :=
    fun _ => rfl
  refine ⟨E', inferInstance, ψ g, ?_, ?_⟩
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
theorem exists_stableCyclic_quarticTwist {N : ℕ} (hN : N ≠ 0) (E : WeierstrassCurve K)
    [E.IsElliptic] (hj : E.j = 1728)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (haut : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
      ∀ x ∈ AddSubgroup.zmultiples g,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g)
    (ι : VariableChange Ω) (hι : ι • (E⁄Ω) = (E⁄Ω))
    (hmove : ∃ x ∈ AddSubgroup.zmultiples g, autMap hι x ∉ AddSubgroup.zmultiples g)
    (hu : (ι.u : Ω) ^ 2 = -1) :
    ∃ (E' : WeierstrassCurve K) (_ : E'.IsElliptic) (g' : (E'⁄Ω).toAffine.Point),
      addOrderOf g' = N ∧
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
  exact exists_stableCyclic_quarticTwist_of_quartic hN (C₀ • E) h₁ h₂ h₃ h₆ ha₄ g₁ hg₁ haut₁ _
    hι₁ hmove₁ hu₁

end BaseChange

end WeierstrassCurve

end
