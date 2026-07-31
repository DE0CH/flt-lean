/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.QuarticTwist
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The sextic twist at `j = 0`

The companion of `Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/QuarticTwist.lean`,
supplying the `j = 0` half of the descent argument of `Fermat/FLT/ModularCurve/X0.lean`.

Everything that is not specific to the shape of the normal form is imported from
`QuarticTwist.lean` and used verbatim: `Affine.Point.autMap`, `autMap_congr`,
`autMap_diag_neg`, `autMap_twist_comm`, `map_twist` and `exists_conj_autMap_baseChange`
are stated for an arbitrary curve with `a₁ = a₃ = 0` (or for arbitrary diagonal variable
changes) and apply unchanged here.  What is redone is the model itself: at `j = 0` the
normal form is `y² = x³ + b` rather than `y² = x³ + ax`, a diagonal variable change scales
`a₆` by `u⁻⁶` rather than `a₄` by `u⁻⁴`, and automorphisms are the SIXTH roots of unity.

## Main statements

* `WeierstrassCurve.sexticModel` : the curve `y² = x³ + b`, the normal form at `j = 0`.
* `WeierstrassCurve.exists_smul_eq_sexticModel` : an elliptic curve with `j = 0` over a
  field of characteristic `0` is isomorphic over that field to `sexticModel b`, `b ≠ 0`.
* `WeierstrassCurve.aut_eq_diag_sextic` : every automorphism of `y² = x³ + a₆` is
  `⟨u, 0, 0, 0⟩` with `u⁶ = 1`.
* `WeierstrassCurve.exists_stableCyclic_sexticTwist` : the geometric half of the arithmetic
  heart at `j = 0` — given a `μ₃`-valued cocycle `c` recording the `u`-coefficients of the
  automorphisms that make a cyclic subgroup Galois-stable, and a Kummer generator `γ`
  trivialising `c` with `γ³ = d` in the base field, the subgroup becomes genuinely
  Galois-stable on the sextic twist by `d`.

Unlike the `j = 1728` case, the production of the twisting parameter is NOT part of this
file: it is Kummer theory for `μ₃` and is supplied by the caller as `γ`, `hγ` and `hd`.
That is the whole reason the `j = 0` node was cut into an arithmetic half and a geometric
half, and this file is the geometric half.
-/

@[expose] public section

namespace WeierstrassCurve

open scoped WeierstrassCurve.Affine

open Affine.Point

/-! ### The normal form `y² = x³ + b` at `j = 0` -/

/-- The Weierstrass curve `y² = x³ + b`, the normal form at `j = 0`. -/
def sexticModel {R : Type*} [CommRing R] (b : R) : WeierstrassCurve R := ⟨0, 0, 0, 0, b⟩

@[simp] lemma sexticModel_a₁ {R : Type*} [CommRing R] (b : R) : (sexticModel b).a₁ = 0 := rfl
@[simp] lemma sexticModel_a₂ {R : Type*} [CommRing R] (b : R) : (sexticModel b).a₂ = 0 := rfl
@[simp] lemma sexticModel_a₃ {R : Type*} [CommRing R] (b : R) : (sexticModel b).a₃ = 0 := rfl
@[simp] lemma sexticModel_a₄ {R : Type*} [CommRing R] (b : R) : (sexticModel b).a₄ = 0 := rfl
@[simp] lemma sexticModel_a₆ {R : Type*} [CommRing R] (b : R) : (sexticModel b).a₆ = b := rfl

lemma sexticModel_baseChange {R : Type*} [CommRing R] (b : R) (A : Type*) [CommRing A]
    [Algebra R A] : (sexticModel b)⁄A = sexticModel (algebraMap R A b) := by
  ext <;> simp [sexticModel, baseChange, map]

lemma sexticModel_Δ {R : Type*} [CommRing R] (b : R) : (sexticModel b).Δ = -432 * b ^ 2 := by
  simp only [Δ, b₂, b₄, b₆, b₈, sexticModel_a₁, sexticModel_a₂, sexticModel_a₃,
    sexticModel_a₄, sexticModel_a₆]
  ring

lemma isElliptic_sexticModel {F : Type*} [Field F] [CharZero F] {b : F} (hb : b ≠ 0) :
    (sexticModel b).IsElliptic := by
  refine ⟨?_⟩
  rw [sexticModel_Δ]
  exact (isUnit_iff_ne_zero).mpr (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb))

/-- **The normal form at `j = 0` really has `j = 0`.**  `y² = x³ + b` has `b₂ = b₄ = 0`,
hence `c₄ = b₂² − 24 b₄ = 0`, and `WeierstrassCurve.j_eq_zero` does the rest.  The mirror of
`j_quarticModel`, and it plays the same role: the sextic twist below is a `sexticModel` by
construction, so recording the `j`-invariant of the curve it produces is free. -/
lemma j_sexticModel {F : Type*} [Field F] [CharZero F] {b : F}
    [(sexticModel b).IsElliptic] : (sexticModel b).j = 0 := by
  refine WeierstrassCurve.j_eq_zero _ ?_
  simp only [c₄, b₂, b₄, sexticModel_a₁, sexticModel_a₂, sexticModel_a₃, sexticModel_a₄]
  ring

/-- **The normal form at `j = 0`**: an elliptic curve with `j = 0` over a field of
characteristic `0` is isomorphic, over that field, to `y² = x³ + b` for some `b ≠ 0`. -/
lemma exists_smul_eq_sexticModel {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K)
    [E.IsElliptic] (hj : E.j = 0) :
    ∃ (C : VariableChange K) (b : K), b ≠ 0 ∧ C • E = sexticModel b := by
  haveI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : K) := invertibleOfNonzero (by norm_num)
  obtain ⟨C₀, hshort⟩ := E.exists_variableChange_isShortNF
  haveI := hshort
  have hj₀ : (C₀ • E).j = 0 := by rw [variableChange_j]; exact hj
  have hc4 : (C₀ • E).c₄ = 0 := (C₀ • E).j_eq_zero_iff.mp hj₀
  have hc6 : (C₀ • E).c₆ ≠ 0 := (C₀ • E).c₆_ne_zero_of_j_eq_zero (by norm_num) hj₀
  have ha₁ : (C₀ • E).a₁ = 0 := a₁_of_isShortNF _
  have ha₂ : (C₀ • E).a₂ = 0 := a₂_of_isShortNF _
  have ha₃ : (C₀ • E).a₃ = 0 := a₃_of_isShortNF _
  have ha₄ : (C₀ • E).a₄ = 0 := by
    have hz : (-48 : K) * (C₀ • E).a₄ = 0 := by
      rw [← hc4]
      simp only [c₄, b₂, b₄, ha₁, ha₂]
      ring
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (by norm_num)
    · exact h
  have ha₆ : (C₀ • E).a₆ ≠ 0 := by
    intro h0
    apply hc6
    simp only [c₆, b₂, b₄, b₆, ha₁, ha₂, ha₃, h0]
    ring
  exact ⟨C₀, (C₀ • E).a₆, ha₆, by
    ext <;> simp only [sexticModel_a₁, sexticModel_a₂, sexticModel_a₃, sexticModel_a₄,
      sexticModel_a₆, ha₁, ha₂, ha₃, ha₄]⟩

/-! ### Curves of the form `y² = x³ + a₆`, described by their coefficients

As in `QuarticTwist.lean`, the base change `(sexticModel b)⁄Ω` is *not* syntactically
`sexticModel (algebraMap b)`, so the lemmas that have to be applied on the `Ω` side are
stated for an arbitrary curve whose `a₁, a₂, a₃, a₄` vanish rather than for `sexticModel`
itself. -/

section Sextic

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

omit [DecidableEq F] in
lemma eq_sexticModel (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) :
    W = sexticModel W.a₆ := by
  ext <;> simp [sexticModel, h₁, h₂, h₃, h₄]

omit [DecidableEq F] in
/-- A diagonal variable change scales `a₆` by `u⁻⁶`. -/
lemma smul_diag_eq_sextic (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0)
    (u : Fˣ) :
    (⟨u, 0, 0, 0⟩ : VariableChange F) • W = sexticModel (((u : F) ^ 6)⁻¹ * W.a₆) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  ext <;>
    simp only [variableChange_def, sexticModel_a₁, sexticModel_a₂, sexticModel_a₃,
      sexticModel_a₄, sexticModel_a₆, h₁, h₂, h₃, h₄, Units.val_inv_eq_inv_val] <;>
    field_simp <;> ring

omit [DecidableEq F] in
/-- A sixth root of unity is an automorphism of `y² = x³ + a₆`. -/
lemma smul_diag_self_sextic (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0)
    {u : Fˣ} (hu : (u : F) ^ 6 = 1) : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W := by
  rw [smul_diag_eq_sextic h₁ h₂ h₃ h₄, hu, inv_one, one_mul]
  exact (eq_sexticModel h₁ h₂ h₃ h₄).symm

omit [DecidableEq F] in
/-- **The sextic twist.**  If `W'` is `y² = x³ + δ⁶a₆` then `⟨δ,0,0,0⟩` carries it to `W`. -/
lemma smul_diag_twist_sextic {W' : WeierstrassCurve F} (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0)
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₁' : W'.a₁ = 0) (h₂' : W'.a₂ = 0) (h₃' : W'.a₃ = 0)
    (h₄' : W'.a₄ = 0) (δ : Fˣ) (hδ : W'.a₆ = (δ : F) ^ 6 * W.a₆) :
    (⟨δ, 0, 0, 0⟩ : VariableChange F) • W' = W := by
  have hd : (δ : F) ≠ 0 := δ.ne_zero
  rw [smul_diag_eq_sextic h₁' h₂' h₃' h₄', hδ,
    show ((δ : F) ^ 6)⁻¹ * ((δ : F) ^ 6 * W.a₆) = W.a₆ by field_simp]
  exact (eq_sexticModel h₁ h₂ h₃ h₄).symm

omit [DecidableEq F] in
/-- **Every automorphism of `y² = x³ + a₆` is diagonal**, in characteristic `0`, and its `u`
is a sixth root of unity. -/
lemma aut_eq_diag_sextic [CharZero F] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (h₄ : W.a₄ = 0) (ha₆ : W.a₆ ≠ 0) {C : VariableChange F} (h : C • W = W) :
    C = ⟨C.u, 0, 0, 0⟩ ∧ (C.u : F) ^ 6 = 1 := by
  have hc6 : W.c₆ ≠ 0 := by
    have hval : W.c₆ = -864 * W.a₆ := by simp only [c₆, b₂, b₄, b₆, h₁, h₂, h₃]; ring
    rw [hval]; exact mul_ne_zero (by norm_num) ha₆
  have hu6 : (C.u : F) ^ 6 = 1 := u_pow_six_eq_one_of_smul_eq _ hc6 h
  refine ⟨?_, hu6⟩
  have hDsmul : (⟨C.u, 0, 0, 0⟩ : VariableChange F) • W = W :=
    smul_diag_self_sextic h₁ h₂ h₃ h₄ hu6
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

end Sextic

/-! ### The sextic twist over a Galois extension -/

section BaseChange

variable {K : Type*} [Field K] [CharZero K] {Ω : Type*} [Field Ω] [Algebra K Ω] [DecidableEq Ω]
  [CharZero Ω]

/-- Base change of an elliptic curve is elliptic; `local` because it would otherwise fire in
every statement mentioning a base-changed curve. -/
local instance isEllipticBaseChangeSextic {E : WeierstrassCurve K} [E.IsElliptic] :
    (E⁄Ω).IsElliptic :=
  inferInstanceAs (E.map (algebraMap K Ω)).IsElliptic

/-- **The geometric half of the arithmetic heart at `j = 0`, in normal form.**

Given the Kummer generator `γ` trivialising the cocycle `c` and its cube `d ∈ K`, the twist
is `E' : y² = x³ + a₆d`, the isomorphism `ψ : E⁄Ω ≅ E'⁄Ω` is `(x, y) ↦ (δ²x, δ³y)` with
`δ² = γ`, and `g' := ψ g`.

For each `σ`, `map_twist` gives `σ(ψ z) = [ζ_σ](ψ(σ z))` with `σδ = ζ_σδ`, and
`autMap_twist_comm` moves `[ζ_σ]` back across `ψ`, so the goal reduces to `[ζ_σ](σ z) ∈ ⟨g⟩`.
Now `ζ_σ² = σ(δ²)/δ² = σγ/γ = c σ = (C_σ.u)²`, so `ζ_σ = ±C_σ.u`, and `autMap_diag_neg` turns
the `−` case into a negation, which the subgroup `⟨g⟩` absorbs.  `hc` supplies
`[C_σ.u](σ z) ∈ ⟨g⟩`.

Note `ζ_σ⁶ = σ(δ⁶)/δ⁶ = σ(d)/d = 1` because `d` lies in the BASE field `K`; that is why no
hypothesis `c σ ^ 3 = 1` is needed here — the cube-root condition is already carried by
`hd`.

`_hN` is underscored because it is genuinely unconsumed: the order of `g'` is `N` because
`ψ` is an `AddEquiv` and `AddEquiv.addOrderOf_eq` is uniform in `N`, so nothing here needs
`N ≠ 0`.  It is carried only so the statement reads uniformly with its `j = 1728` sibling,
where the twisting parameter really does need `⟨g⟩` finite. -/
theorem exists_stableCyclic_sexticTwist_of_sextic {N : ℕ} (_hN : N ≠ 0) (E : WeierstrassCurve K)
    [E.IsElliptic] (h₁ : (E⁄Ω).a₁ = 0) (h₂ : (E⁄Ω).a₂ = 0) (h₃ : (E⁄Ω).a₃ = 0)
    (h₄ : (E⁄Ω).a₄ = 0) (ha₆ : (E⁄Ω).a₆ ≠ 0)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (c : (Ω ≃ₐ[K] Ω) → Ω)
    (hc : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
      (C.u : Ω) ^ 2 = c σ ∧
      ∀ x ∈ AddSubgroup.zmultiples g,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g)
    (γ : Ω) (δ : Ωˣ) (hδ : (δ : Ω) ^ 2 = γ)
    (hγ : ∀ σ : Ω ≃ₐ[K] Ω, σ.toAlgHom γ = c σ * γ)
    (d : K) (hd : γ ^ 3 = algebraMap K Ω d) :
    ∃ (E' : WeierstrassCurve K) (_ : E'.IsElliptic) (g' : (E'⁄Ω).toAffine.Point),
      E'.j = 0 ∧ addOrderOf g' = N ∧
      ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ AddSubgroup.zmultiples g',
        Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g' := by
  have hδ0 : (δ : Ω) ≠ 0 := δ.ne_zero
  have hδ6 : (δ : Ω) ^ 6 = algebraMap K Ω d := by
    rw [show (δ : Ω) ^ 6 = ((δ : Ω) ^ 2) ^ 3 by ring, hδ, hd]
  have hd0 : d ≠ 0 := by
    intro h0
    exact (pow_ne_zero 6 hδ0) (by rw [hδ6, h0, _root_.map_zero])
  have hEa₆ : (E⁄Ω).a₆ = algebraMap K Ω E.a₆ := rfl
  have hEa₆K : E.a₆ ≠ 0 := fun h0 => ha₆ (by rw [hEa₆, h0, _root_.map_zero])
  obtain ⟨E', hE'⟩ : ∃ E' : WeierstrassCurve K, E' = sexticModel (E.a₆ * d) := ⟨_, rfl⟩
  have hE'₁ : (E'⁄Ω).a₁ = 0 := by rw [hE', sexticModel_baseChange]; simp
  have hE'₂ : (E'⁄Ω).a₂ = 0 := by rw [hE', sexticModel_baseChange]; simp
  have hE'₃ : (E'⁄Ω).a₃ = 0 := by rw [hE', sexticModel_baseChange]; simp
  have hE'₄ : (E'⁄Ω).a₄ = 0 := by rw [hE', sexticModel_baseChange]; simp
  have hE'₆ : (E'⁄Ω).a₆ = (δ : Ω) ^ 6 * (E⁄Ω).a₆ := by
    rw [hE', sexticModel_baseChange, sexticModel_a₆, hδ6, hEa₆, map_mul]; ring
  haveI hsm : (sexticModel (E.a₆ * d)).IsElliptic :=
    isElliptic_sexticModel (mul_ne_zero hEa₆K hd0)
  haveI : E'.IsElliptic := hE' ▸ hsm
  have hjE' : E'.j = 0 := by simp_rw [hE']; exact j_sexticModel
  have hψ : (⟨δ, 0, 0, 0⟩ : VariableChange Ω) • (E'⁄Ω) = (E⁄Ω) :=
    smul_diag_twist_sextic h₁ h₂ h₃ h₄ hE'₁ hE'₂ hE'₃ hE'₄ δ hE'₆
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
  have hζ6 : (ζ : Ω) ^ 6 = 1 := by
    have hsq : ((ζ : Ω) * (δ : Ω)) ^ 6 = (δ : Ω) ^ 6 := by
      rw [← hσδ, ← map_pow, hδ6, AlgHom.commutes]
    have h6 : (ζ : Ω) ^ 6 * (δ : Ω) ^ 6 = 1 * (δ : Ω) ^ 6 := by
      rw [one_mul, ← mul_pow]; exact hsq
    exact mul_right_cancel₀ (pow_ne_zero 6 hδ0) h6
  have hζE' : (⟨ζ, 0, 0, 0⟩ : VariableChange Ω) • (E'⁄Ω) = (E'⁄Ω) :=
    smul_diag_self_sextic hE'₁ hE'₂ hE'₃ hE'₄ hζ6
  have hζE : (⟨ζ, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) :=
    smul_diag_self_sextic h₁ h₂ h₃ h₄ hζ6
  have hkey : Affine.Point.map σ.toAlgHom (ψ (n • g))
      = ψ (autMap hζE (Affine.Point.map σ.toAlgHom (n • g))) := by
    rw [hψapp, hψapp, map_twist hψ hζE' σ hσδ, autMap_twist_comm hψ hζE' hζE]
  obtain ⟨C, hC, hCu, hCmem⟩ := hc σ
  obtain ⟨hCdiag, hCu6⟩ := aut_eq_diag_sextic h₁ h₂ h₃ h₄ ha₆ hC
  have hCdiagsmul : (⟨C.u, 0, 0, 0⟩ : VariableChange Ω) • (E⁄Ω) = (E⁄Ω) :=
    smul_diag_self_sextic h₁ h₂ h₃ h₄ hCu6
  -- `ζ_σ² = σ(δ²)/δ² = σγ/γ = c σ = (C.u)²`
  have hγ0 : γ ≠ 0 := by rw [← hδ]; exact pow_ne_zero 2 hδ0
  have hζu : (ζ : Ω) ^ 2 = (C.u : Ω) ^ 2 := by
    have hsq : ((ζ : Ω) * (δ : Ω)) ^ 2 = c σ * γ := by
      rw [← hσδ, ← map_pow, hδ]; exact hγ σ
    rw [mul_pow, hδ, ← hCu] at hsq
    exact mul_right_cancel₀ hγ0 (by linear_combination hsq)
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

/-- **The geometric half of the arithmetic heart at `j = 0`** (PROVEN 2026-07-28, no leaf).

A cyclic subgroup of `E(Ω)` whose Galois-stability defect is recorded by the `μ₃`-valued
cocycle `c` — `hc` supplies, for each `σ`, an automorphism `C_σ` with `(C_σ.u)² = c σ`
carrying `σ⟨g⟩` into `⟨g⟩` — becomes genuinely Galois-stable on the SEXTIC TWIST by
`d = γ³`, where `γ` trivialises `c`.  The twist is again defined over `K`.

The proof puts `E` in the normal form `y² = x³ + b` over `K` (`exists_smul_eq_sexticModel`),
transports `g` and `hc` along the resulting isomorphism — `exists_conj_autMap_baseChange`
conjugates the automorphisms, which does not change their `u`-coefficient, and
`equivVariableChangeBaseChange_galois` says the isomorphism is `Gal(Ω/K)`-equivariant since
`C₀` has coefficients in `K` — extracts a square root `δ` of `γ` (this is the only use of
`IsAlgClosed Ω`), and applies `exists_stableCyclic_sexticTwist_of_sextic`. -/
theorem exists_stableCyclic_sexticTwist [IsAlgClosed Ω] {N : ℕ} (hN : N ≠ 0)
    (E : WeierstrassCurve K) [E.IsElliptic] (hj : E.j = 0)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (c : (Ω ≃ₐ[K] Ω) → Ω)
    (hc : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
      (C.u : Ω) ^ 2 = c σ ∧
      ∀ x ∈ AddSubgroup.zmultiples g,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g)
    (γ : Ω) (hγ0 : γ ≠ 0)
    (hγ : ∀ σ : Ω ≃ₐ[K] Ω, σ.toAlgHom γ = c σ * γ)
    (d : K) (hd : γ ^ 3 = algebraMap K Ω d) :
    ∃ (E' : WeierstrassCurve K) (_ : E'.IsElliptic) (g' : (E'⁄Ω).toAffine.Point),
      E'.j = 0 ∧ addOrderOf g' = N ∧
      ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ AddSubgroup.zmultiples g',
        Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g' := by
  obtain ⟨C₀, b, hb, hC₀⟩ := exists_smul_eq_sexticModel E hj
  have h₁ : ((C₀ • E)⁄Ω).a₁ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₁) = 0
    rw [hC₀]; simp
  have h₂ : ((C₀ • E)⁄Ω).a₂ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₂) = 0
    rw [hC₀]; simp
  have h₃ : ((C₀ • E)⁄Ω).a₃ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₃) = 0
    rw [hC₀]; simp
  have h₄ : ((C₀ • E)⁄Ω).a₄ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₄) = 0
    rw [hC₀]; simp
  have ha₆ : ((C₀ • E)⁄Ω).a₆ ≠ 0 := by
    show algebraMap K Ω ((C₀ • E).a₆) ≠ 0
    rw [hC₀, sexticModel_a₆]
    exact fun h0 => hb ((algebraMap K Ω).injective (by rw [h0, _root_.map_zero]))
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
  have hc₁ : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • ((C₀ • E)⁄Ω) = ((C₀ • E)⁄Ω)),
      (C.u : Ω) ^ 2 = c σ ∧
      ∀ x ∈ AddSubgroup.zmultiples g₁,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g₁ := by
    intro σ
    obtain ⟨C, hC, hCu, hCmem⟩ := hc σ
    obtain ⟨h', hconj⟩ := exists_conj_autMap_baseChange E C₀ hC
    refine ⟨_, h', ?_, fun x hx => ?_⟩
    · have hval : (C₀.baseChange Ω * C * (C₀.baseChange Ω)⁻¹).u = C.u := by
        show (C₀.baseChange Ω).u * C.u * ((C₀.baseChange Ω).u)⁻¹ = C.u
        rw [mul_comm ((C₀.baseChange Ω).u) C.u, mul_assoc, mul_inv_cancel, mul_one]
      rw [hval]; exact hCu
    · rw [hmemΘ, hconj, Affine.Point.equivVariableChangeBaseChange_galois]
      exact hCmem _ ((hmemΘ x).mp hx)
  obtain ⟨δ₀, hδ₀⟩ := IsAlgClosed.exists_pow_nat_eq (k := Ω) γ (n := 2) (by norm_num)
  have hδ₀0 : δ₀ ≠ 0 := by
    intro h0
    exact hγ0 (by rw [← hδ₀, h0]; ring)
  exact exists_stableCyclic_sexticTwist_of_sextic hN (C₀ • E) h₁ h₂ h₃ h₄ ha₆ g₁ hg₁ c hc₁
    γ (Units.mk0 δ₀ hδ₀0) hδ₀ hγ d hd

end BaseChange

end WeierstrassCurve

end
