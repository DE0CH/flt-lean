/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.Analysis.Analytic.Order

/-!
# The vanishing half of the level-one valence formula

This module proves

  `modularForm_levelOne_eq_zero_of_valence`:  a level-one modular form `F` of weight `k`
  with `ord_∞ F ≥ a`, `ord_ρ F ≥ b`, `ord_i F ≥ c` and `k < 12a + 4b + 6c` is zero,

over TWO residual leaves — that `E₄` has a SIMPLE zero at `ρ` and `E₆` a SIMPLE zero at `i`.
That is the vanishing half of the classical valence formula

  `ord_∞ F + ord_i F / 2 + ord_ρ F / 3 + Σ'_P ord_P F = k / 12`

for `SL(2, ℤ)`, cleared of denominators and with the sum over the remaining points dropped.

## What is proven here, and what is left

PROVEN outright, from mathlib's level-one dimension theory alone:

* `E₄_apply_rhoH`, `E₆_apply_IH` — `E₄(ρ) = 0` and `E₆(i) = 0`, from the automorphy factor at
  the elliptic fixed point (`(ρ+1)⁴ ≠ 1`, `i⁶ ≠ 1`);
* `E₆_apply_rhoH_ne_zero`, `E₄_apply_IH_ne_zero` — the complementary NON-vanishing, from
  `Δ = (E₄³ - E₆²)/1728` (`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`) and `Δ ≠ 0`;
* `exists_eq_E₄_mul`, `exists_eq_E₆_mul` — **the structure-theorem content**: a level-one form
  vanishing at `ρ` is divisible by `E₄`, one vanishing at `i` is divisible by `E₆`.  These are
  proved by strong induction on the weight over `exists_smul_add_delta_mul` (subtract off a
  multiple of a form with constant term `1`, then divide the resulting cusp form by `Δ` using
  mathlib's `CuspForm.discriminantEquiv`).  **No dimension count and no monomial basis is
  needed**;
* `eq_zero_of_valence` — the assembly: a double induction on `b` and `c`, dividing by `E₄` and
  by `E₆`, with mathlib's `ModularForm.sturm_bound_levelOne` as the `b = c = 0` base case.

LEFT AS LEAVES — and they are the whole ANALYTIC content of the valence formula:

* `analyticOrderAt_E₄_rho_le`, `analyticOrderAt_E₆_I_le`.

**Why the two leaves are exactly the residue, and why they cannot be weakened.**  Everything
else here is an identity between modular forms.  What no automorphy relation can give is that
the zero of `E₄` at `ρ` is SIMPLE: writing `e := ord_ρ E₄`, differentiating
`E₄(γ z) = (z+1)⁴ E₄(z)` at the fixed point yields only `e ≡ 1 (mod 3)`, and every algebraic
consequence of the graded ring is invariant under replacing `e` by any member of that class.
Concretely, if `e ≥ 2` then `F = E₄`, `k = 4`, `a = c = 0`, `b = e` satisfies every hypothesis
of the main theorem with `F ≠ 0` — so the main theorem is TRUE if and only if `e = 1`, and
likewise `ord_i E₆ = 1`.

**The recommended route for both leaves** is the SERRE DERIVATIVE, which mathlib has as
`Derivative.serreDerivative` (`Mathlib/NumberTheory/ModularForms/Derivative.lean`) together with
`Derivative.serreDerivative_slash_invariant` and `Derivative.serreDerivative_mdifferentiable`:
`∂₄E₄` is slash-invariant of weight `6` and `MDiff`, so ONCE it is known to be bounded at the
cusp it is an element of `M₆(SL(2,ℤ))`, which is one-dimensional
(`ModularForm.levelOne_weight_six_rank_one`); its constant `q`-coefficient is
`0 - (4/12)·1·1 = -1/3 ≠ 0`, so `∂₄E₄ = (-1/3)·E₆`.  At `ρ`, `E₄(ρ) = 0` kills the `E₂E₄` term,
so `D E₄ (ρ) = (-1/3) E₆(ρ) ≠ 0` by `E₆_apply_rhoH_ne_zero`, i.e. the derivative of
`E₄ ∘ ofComplex` at `ρ` is nonzero, and
`AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero` finishes.  Symmetrically
`∂₆E₆ = (-1/2)·E₄²` in the one-dimensional `M₈`, and `E₄(i) ≠ 0` gives `D E₆ (i) ≠ 0`.

The ONE thing that route still owes is `IsBoundedAtImInfty (Derivative.D E₄)` — mathlib has
`EisensteinSeries.isBoundedAtImInfty_E2` for the other summand, and the missing half is that
`q ↦ q · (cuspFunction 1 E₄)'(q)` is bounded near `q = 0`, which is
`differentiableAt_cuspFunction` plus the chain rule through `UpperHalfPlane.eq_cuspFunction`.
Mathlib's `Derivative.lean` lists "Serre derivative preserves modularity" as an explicit TODO,
so this is a genuine gap in the pin rather than a lemma that was missed.

**The check that refutes either leaf**: an `SL(2, ℤ)`-modular form exhibiting a zero of `E₄` at
`ρ`, or of `E₆` at `i`, of order `≥ 2`.

## Note on `ρ`

`ModularCurve/X0.lean` defines `Fermat.ellipticRho` with the same body as `rho` below, so the
two are `rfl`-equal and the consumer there bridges them with `rfl`.  A future cleanup should
delete one of the two; it is not done here because `Fermat.ellipticRho` has other consumers in
that file and re-pointing them is an interface edit in a heavily contended module.
-/

@[expose] public section

namespace Fermat.LevelOneValence

open UpperHalfPlane ModularForm SlashInvariantForm SlashInvariantFormClass ModularFormClass
  CuspFormClass MatrixGroups OnePoint Filter EisensteinSeries Asymptotics

open scoped Topology

noncomputable section

/-! ### The two elliptic points -/

/-- `ρ = e^{2πi/3}`, the order-3 elliptic point. -/
def rho : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℝ)) / 2

theorem sq_sqrt_three : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  norm_cast
  rw [Real.sq_sqrt]
  norm_num

theorem rho_sq_add : rho ^ 2 + rho + 1 = 0 := by
  have key : rho ^ 2 + rho + 1 = (3 + Complex.I ^ 2 * ((Real.sqrt 3 : ℝ) : ℂ) ^ 2) / 4 := by
    simp only [rho]; ring
  rw [key, sq_sqrt_three, Complex.I_sq]
  norm_num

theorem rho_im : rho.im = Real.sqrt 3 / 2 := by
  simp [rho]

theorem rho_im_pos : 0 < rho.im := by
  rw [rho_im]
  have : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- `ρ` as a point of the upper half plane. -/
def rhoH : ℍ := ⟨rho, rho_im_pos⟩

@[simp] theorem coe_rhoH : (rhoH : ℂ) = rho := rfl

/-- `I` as a point of the upper half plane. -/
def IH : ℍ := ⟨Complex.I, by simp⟩

@[simp] theorem coe_IH : (IH : ℂ) = Complex.I := rfl

/-- The order-3 element `ST` of `SL(2, ℤ)` fixing `ρ`. -/
def gRho : SL(2, ℤ) := ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩

/-- The order-2 element `S` of `SL(2, ℤ)` fixing `i`. -/
def gI : SL(2, ℤ) := ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩

theorem rho_add_one_ne_zero : rho + 1 ≠ 0 := by
  intro h
  have h2 : rho.im = 0 := by
    have := congrArg Complex.im h
    simpa using this
  exact absurd h2 rho_im_pos.ne'

theorem gRho_smul_rhoH : gRho • rhoH = rhoH := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp only [gRho, Matrix.SpecialLinearGroup.coe_mk, coe_rhoH]
  norm_num
  rw [div_eq_iff rho_add_one_ne_zero]
  linear_combination -rho_sq_add

theorem denom_gRho : UpperHalfPlane.denom (gRho : GL (Fin 2) ℝ) (rhoH : ℂ) = rho + 1 := by
  rw [ModularGroup.denom_apply]
  simp [gRho]

theorem gI_smul_IH : gI • IH = IH := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp only [gI, Matrix.SpecialLinearGroup.coe_mk, coe_IH]
  norm_num

theorem denom_gI : UpperHalfPlane.denom (gI : GL (Fin 2) ℝ) (IH : ℂ) = Complex.I := by
  rw [ModularGroup.denom_apply]
  simp [gI]

/-! ### The elementary vanishing facts -/

theorem E₄_apply_rhoH : E₄ rhoH = 0 := by
  have hmem : ((gRho : GL (Fin 2) ℝ)) ∈ 𝒮ℒ := ⟨gRho, rfl⟩
  have h := slash_action_eqn'' E₄ hmem rhoH
  rw [show ((gRho : GL (Fin 2) ℝ)) • rhoH = rhoH from gRho_smul_rhoH, denom_gRho] at h
  have h4 : (rho + 1) ^ (4 : ℤ) = -rho - 1 := by
    rw [show (4:ℤ) = ((4:ℕ):ℤ) from rfl, zpow_natCast]
    linear_combination (rho ^ 2 + 3 * rho + 2) * rho_sq_add
  rw [h4] at h
  have hne : -rho - 1 - 1 ≠ 0 := by
    intro hc
    have h2 : rho.im = 0 := by
      have := congrArg Complex.im hc
      simpa using this
    exact absurd h2 rho_im_pos.ne'
  have : (-rho - 1 - 1) * E₄ rhoH = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hne
  · exact h'

theorem E₆_apply_IH : E₆ IH = 0 := by
  have hmem : ((gI : GL (Fin 2) ℝ)) ∈ 𝒮ℒ := ⟨gI, rfl⟩
  have h := slash_action_eqn'' E₆ hmem IH
  rw [show ((gI : GL (Fin 2) ℝ)) • IH = IH from gI_smul_IH, denom_gI] at h
  have h6 : (Complex.I : ℂ) ^ (6 : ℤ) = -1 := by
    rw [show (6:ℤ) = ((6:ℕ):ℤ) from rfl, zpow_natCast]
    simp [pow_succ, Complex.I_mul_I]
  rw [h6] at h
  have : (2 : ℂ) * E₆ IH = 0 := by linear_combination h
  simpa using this

theorem E₆_apply_rhoH_ne_zero : E₆ rhoH ≠ 0 := by
  intro h
  have hd := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq rhoH
  rw [E₄_apply_rhoH, h] at hd
  simp at hd
  exact ModularForm.discriminant_ne_zero rhoH hd

theorem E₄_apply_IH_ne_zero : E₄ IH ≠ 0 := by
  intro h
  have hd := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq IH
  rw [E₆_apply_IH, h] at hd
  simp at hd
  exact ModularForm.discriminant_ne_zero IH hd

/-! ### Analyticity plumbing -/

theorem analyticAt_comp_ofComplex {k : ℤ} (F : ModularForm 𝒮ℒ k) (z : ℍ) :
    AnalyticAt ℂ (⇑F ∘ ofComplex) (z : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp F.holo').analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

theorem comp_ofComplex_apply {k : ℤ} (F : ModularForm 𝒮ℒ k) (z : ℍ) :
    (⇑F ∘ ofComplex) (z : ℂ) = F z := by
  simp [Function.comp_apply, ofComplex_apply]

/-! ### Consequences of the leaves -/

theorem analyticOrderAt_E₄_I : analyticOrderAt (⇑E₄ ∘ ofComplex) Complex.I = 0 := by
  rw [analyticOrderAt_eq_zero]
  right
  rw [show (Complex.I : ℂ) = ((IH : ℍ) : ℂ) from rfl, comp_ofComplex_apply]
  exact E₄_apply_IH_ne_zero

theorem analyticOrderAt_E₆_rho : analyticOrderAt (⇑E₆ ∘ ofComplex) rho = 0 := by
  rw [analyticOrderAt_eq_zero]
  right
  rw [show (rho : ℂ) = ((rhoH : ℍ) : ℂ) from rfl, comp_ofComplex_apply]
  exact E₆_apply_rhoH_ne_zero

theorem qExpansion_order_E₄ : (qExpansion 1 (⇑E₄)).order = 0 := by
  rw [← not_ne_iff, PowerSeries.order_ne_zero_iff_constCoeff_eq_zero]
  intro hc
  have h1 : PowerSeries.constantCoeff (qExpansion 1 (⇑E₄)) = 1 := by
    simpa using (EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) (by decide))
  rw [hc] at h1
  exact zero_ne_one h1

theorem qExpansion_order_E₆ : (qExpansion 1 (⇑E₆)).order = 0 := by
  rw [← not_ne_iff, PowerSeries.order_ne_zero_iff_constCoeff_eq_zero]
  intro hc
  have h1 : PowerSeries.constantCoeff (qExpansion 1 (⇑E₆)) = 1 := by
    simpa using (EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 6) (by decide))
  rw [hc] at h1
  exact zero_ne_one h1

/-- Splitting the `q`-expansion order along a factorisation `⇑F = ⇑E * ⇑G`. -/
theorem qExpansion_of_eq_mul {k k' : ℤ} (E : ModularForm 𝒮ℒ k') (F : ModularForm 𝒮ℒ k)
    (G : ModularForm 𝒮ℒ (k - k')) (hF : (F : ℍ → ℂ) = (E : ℍ → ℂ) * (G : ℍ → ℂ)) :
    (qExpansion 1 (⇑F)).order = (qExpansion 1 (⇑E)).order + (qExpansion 1 (⇑G)).order := by
  have : (F : ℍ → ℂ) = ⇑(E.mul G) := by rw [hF, ModularForm.coe_mul]
  rw [this, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, PowerSeries.order_mul]

/-- Splitting the analytic order along a factorisation `⇑F = ⇑E * ⇑G`. -/
theorem analyticOrderAt_of_eq_mul {k k' : ℤ} (E : ModularForm 𝒮ℒ k') (F : ModularForm 𝒮ℒ k)
    (G : ModularForm 𝒮ℒ (k - k')) (hF : (F : ℍ → ℂ) = (E : ℍ → ℂ) * (G : ℍ → ℂ)) (z : ℍ) :
    analyticOrderAt (⇑F ∘ ofComplex) (z : ℂ)
      = analyticOrderAt (⇑E ∘ ofComplex) (z : ℂ) + analyticOrderAt (⇑G ∘ ofComplex) (z : ℂ) := by
  have hc : (⇑F ∘ ofComplex) = (⇑E ∘ ofComplex) * (⇑G ∘ ofComplex) := by
    ext w; simp [hF, Function.comp_apply]
  rw [hc, analyticOrderAt_mul (analyticAt_comp_ofComplex E z) (analyticAt_comp_ofComplex G z)]

/-! ### Divisibility by `E₄` and `E₆` -/

/-- `Δ` as a modular form of weight `12`. -/
def deltaMF : ModularForm 𝒮ℒ 12 := CuspForm.toModularFormₗ CuspForm.discriminant

@[simp] theorem coe_deltaMF : (⇑deltaMF : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem deltaMF_apply_ne_zero (z : ℍ) : deltaMF z ≠ 0 := ModularForm.discriminant_ne_zero z

/-- For `j = 0` or `j` even and `≥ 4` there is a level-one form of weight `j` with constant
`q`-expansion coefficient `1`. -/
theorem exists_unitForm (j : ℕ) (hj : j ≠ 2) (hje : Even j) :
    ∃ V : ModularForm 𝒮ℒ (j : ℤ), (PowerSeries.coeff 0) (qExpansion 1 (⇑V)) = 1 := by
  rcases eq_or_ne j 0 with rfl | hj0
  · refine ⟨ModularForm.mcast (by norm_num) (1 : ModularForm 𝒮ℒ 0), ?_⟩
    rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_one]
    simp
  · have h3 : 3 ≤ j := by rcases hje with ⟨t, ht⟩; omega
    exact ⟨E h3, EisensteinSeries.E_qExpansion_coeff_zero h3 hje⟩

/-- Every level-one form splits as `c • W + Δ * H` when `W` has constant term `1`. -/
theorem exists_smul_add_delta_mul {k : ℤ} (F W : ModularForm 𝒮ℒ k)
    (hW : (PowerSeries.coeff 0) (qExpansion 1 (⇑W)) = 1) :
    ∃ (c : ℂ) (H : ModularForm 𝒮ℒ (k - 12)),
      (⇑F : ℍ → ℂ) = c • ⇑W + ⇑deltaMF * ⇑H := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, (PowerSeries.coeff 0) (qExpansion 1 (⇑F)) = c := ⟨_, rfl⟩
  have hW' : PowerSeries.constantCoeff (qExpansion 1 (⇑W)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hW
  have hc' : PowerSeries.constantCoeff (qExpansion 1 (⇑F)) = c := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hc
  have e1 : qExpansion 1 (⇑(F - c • W)) = qExpansion 1 (⇑F) - c • qExpansion 1 (⇑W) := by
    rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL F (c • W),
      IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
  have h0 : (PowerSeries.coeff 0) (qExpansion 1 (⇑(F - c • W))) = 0 := by
    rw [e1]
    simp [hW', hc']
  refine ⟨c, CuspForm.discriminantEquiv (ModularForm.toCuspForm (F - c • W) h0), ?_⟩
  have key := ModularForm.discriminant_mul_discriminantEquiv
    (ModularForm.toCuspForm (F - c • W) h0)
  have hco : (⇑(ModularForm.toCuspForm (F - c • W) h0) : ℍ → ℂ) = ⇑F - c • ⇑W := by
    funext z
    rw [ModularForm.toCuspForm_apply]
    simp
  rw [hco] at key
  rw [coe_deltaMF, key]
  funext z
  simp

/-- **Divisibility by `E₄`.**  Strong induction on the weight. -/
private theorem exists_eq_E₄_mul_aux : ∀ (n : ℕ) {k : ℤ}, k.toNat ≤ n → ∀ (F : ModularForm 𝒮ℒ k),
    F rhoH = 0 → ∃ G : ModularForm 𝒮ℒ (k - 4), (⇑F : ℍ → ℂ) = ⇑E₄ * ⇑G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k hkn F hF
  rcases lt_or_ge k 0 with hneg | hnonneg
  · exact ⟨0, by
      rw [rank_zero_iff_forall_zero.mp (ModularForm.levelOne_neg_weight_rank_zero hneg) F]; simp⟩
  rcases Int.even_or_odd k with hev | hodd
  swap
  · exact ⟨0, by rw [ModularForm.levelOne_odd_weight_eq_zero hodd F]; simp⟩
  rcases eq_or_ne k 2 with rfl | hk2
  · refine ⟨0, ?_⟩
    rw [rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero F]
    funext z
    show (0 : ℂ) = E₄ z * 0
    ring
  by_cases hsmall : k = 0 ∨ k = 6
  · obtain ⟨W, hW, hWrho⟩ : ∃ W : ModularForm 𝒮ℒ k,
        (PowerSeries.coeff 0) (qExpansion 1 (⇑W)) = 1 ∧ W rhoH ≠ 0 := by
      rcases hsmall with rfl | rfl
      · exact ⟨1, by rw [ModularForm.qExpansion_one]; simp, by simp⟩
      · exact ⟨E₆, EisensteinSeries.E_qExpansion_coeff_zero _ (by decide), E₆_apply_rhoH_ne_zero⟩
    obtain ⟨c, H, hFH⟩ := exists_smul_add_delta_mul F W hW
    have hHz : H = 0 := rank_zero_iff_forall_zero.mp
      (ModularForm.levelOne_neg_weight_rank_zero
        (by rcases hsmall with rfl | rfl <;> norm_num)) H
    have hF0 : (⇑F : ℍ → ℂ) = c • ⇑W := by rw [hFH, hHz]; funext z; simp
    have hcW : c * W rhoH = 0 := by
      have h2 := congrFun hF0 rhoH
      rw [hF] at h2
      simpa using h2.symm
    rcases mul_eq_zero.mp hcW with rfl | h'
    · exact ⟨0, by rw [hF0]; funext z; simp⟩
    · exact absurd h' hWrho
  simp only [not_or] at hsmall
  obtain ⟨hk0, hk6⟩ := hsmall
  have hk4 : 4 ≤ k := by rw [Int.even_iff] at hev; omega
  have hjk : (((k - 4).toNat : ℕ) : ℤ) = k - 4 := by omega
  have hje : Even ((k - 4).toNat) := by
    rw [Nat.even_iff]; rw [Int.even_iff] at hev; omega
  have hj2 : (k - 4).toNat ≠ 2 := by omega
  obtain ⟨V, hV⟩ := exists_unitForm ((k - 4).toNat) hj2 hje
  let V' : ModularForm 𝒮ℒ (k - 4) := ModularForm.mcast hjk V
  have hV'c : (PowerSeries.coeff 0) (qExpansion 1 (⇑V')) = 1 := by
    rw [show (⇑V' : ℍ → ℂ) = ⇑V from rfl]; exact hV
  let W : ModularForm 𝒮ℒ k := ModularForm.mcast (by ring) (E₄.mul V')
  have hcoeW : (⇑W : ℍ → ℂ) = ⇑E₄ * ⇑V' := rfl
  have hWc : (PowerSeries.coeff 0) (qExpansion 1 (⇑W)) = 1 := by
    have he4 : (PowerSeries.coeff 0) (qExpansion 1 (⇑E₄)) = 1 :=
      EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
    rw [hcoeW, show (⇑E₄ * ⇑V' : ℍ → ℂ) = ⇑(E₄.mul V') from (ModularForm.coe_mul _ _).symm,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [hV'c, he4]
  obtain ⟨c, H, hFH⟩ := exists_smul_add_delta_mul F W hWc
  have hWrho : W rhoH = 0 := by
    have : W rhoH = E₄ rhoH * V' rhoH := congrFun hcoeW rhoH
    rw [this, E₄_apply_rhoH, zero_mul]
  have hHrho : H rhoH = 0 := by
    have h2 := congrFun hFH rhoH
    rw [hF] at h2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h2
    rw [hWrho, mul_zero, zero_add] at h2
    rcases mul_eq_zero.mp h2.symm with h' | h'
    · exact absurd h' (deltaMF_apply_ne_zero rhoH)
    · exact h'
  have hlt : (k - 12).toNat < n := by omega
  obtain ⟨H', hH'⟩ := ih ((k - 12).toNat) hlt (le_refl _) H hHrho
  refine ⟨c • V' + ModularForm.mcast (by ring : (12 : ℤ) + (k - 12 - 4) = k - 4)
    (deltaMF.mul H'), ?_⟩
  rw [hFH, hcoeW]
  funext z
  have hz := congrFun hH' z
  simp only [ModularForm.coe_add, IsGLPos.coe_smul, ModularForm.coe_mcast, ModularForm.coe_mul,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  simp only [Pi.mul_apply] at hz
  rw [hz]
  ring

/-- **A level-one form vanishing at `ρ` is divisible by `E₄`.** -/
theorem exists_eq_E₄_mul {k : ℤ} (F : ModularForm 𝒮ℒ k) (h : F rhoH = 0) :
    ∃ G : ModularForm 𝒮ℒ (k - 4), (⇑F : ℍ → ℂ) = ⇑E₄ * ⇑G :=
  exists_eq_E₄_mul_aux k.toNat (le_refl _) F h

/-- **Divisibility by `E₆`.**  Strong induction on the weight. -/
private theorem exists_eq_E₆_mul_aux : ∀ (n : ℕ) {k : ℤ}, k.toNat ≤ n → ∀ (F : ModularForm 𝒮ℒ k),
    F IH = 0 → ∃ G : ModularForm 𝒮ℒ (k - 6), (⇑F : ℍ → ℂ) = ⇑E₆ * ⇑G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k hkn F hF
  rcases lt_or_ge k 0 with hneg | hnonneg
  · exact ⟨0, by
      rw [rank_zero_iff_forall_zero.mp (ModularForm.levelOne_neg_weight_rank_zero hneg) F]; simp⟩
  rcases Int.even_or_odd k with hev | hodd
  swap
  · exact ⟨0, by rw [ModularForm.levelOne_odd_weight_eq_zero hodd F]; simp⟩
  rcases eq_or_ne k 2 with rfl | hk2
  · refine ⟨0, ?_⟩
    rw [rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero F]
    funext z
    show (0 : ℂ) = E₆ z * 0
    ring
  by_cases hsmall : k = 0 ∨ k = 4 ∨ k = 8
  · obtain ⟨W, hW, hWI⟩ : ∃ W : ModularForm 𝒮ℒ k,
        (PowerSeries.coeff 0) (qExpansion 1 (⇑W)) = 1 ∧ W IH ≠ 0 := by
      rcases hsmall with rfl | rfl | rfl
      · exact ⟨1, by rw [ModularForm.qExpansion_one]; simp, by simp⟩
      · exact ⟨E₄, EisensteinSeries.E_qExpansion_coeff_zero _ (by decide), E₄_apply_IH_ne_zero⟩
      · refine ⟨ModularForm.mcast (by norm_num) (E₄.mul E₄), ?_, ?_⟩
        · have he4 : (PowerSeries.coeff 0) (qExpansion 1 (⇑E₄)) = 1 :=
            EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
          rw [ModularForm.qExpansion_mcast,
            ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
            PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
            ← PowerSeries.coeff_zero_eq_constantCoeff]
          simp [he4]
        · show E₄ IH * E₄ IH ≠ 0
          exact mul_ne_zero E₄_apply_IH_ne_zero E₄_apply_IH_ne_zero
    obtain ⟨c, H, hFH⟩ := exists_smul_add_delta_mul F W hW
    have hHz : H = 0 := rank_zero_iff_forall_zero.mp
      (ModularForm.levelOne_neg_weight_rank_zero
        (by rcases hsmall with rfl | rfl | rfl <;> norm_num)) H
    have hF0 : (⇑F : ℍ → ℂ) = c • ⇑W := by rw [hFH, hHz]; funext z; simp
    have hcW : c * W IH = 0 := by
      have h2 := congrFun hF0 IH
      rw [hF] at h2
      simpa using h2.symm
    rcases mul_eq_zero.mp hcW with rfl | h'
    · exact ⟨0, by rw [hF0]; funext z; simp⟩
    · exact absurd h' hWI
  simp only [not_or] at hsmall
  obtain ⟨hk0, hk4, hk8⟩ := hsmall
  have hk6 : 6 ≤ k := by rw [Int.even_iff] at hev; omega
  have hjk : (((k - 6).toNat : ℕ) : ℤ) = k - 6 := by omega
  have hje : Even ((k - 6).toNat) := by
    rw [Nat.even_iff]; rw [Int.even_iff] at hev; omega
  have hj2 : (k - 6).toNat ≠ 2 := by omega
  obtain ⟨V, hV⟩ := exists_unitForm ((k - 6).toNat) hj2 hje
  let V' : ModularForm 𝒮ℒ (k - 6) := ModularForm.mcast hjk V
  have hV'c : (PowerSeries.coeff 0) (qExpansion 1 (⇑V')) = 1 := by
    rw [show (⇑V' : ℍ → ℂ) = ⇑V from rfl]; exact hV
  let W : ModularForm 𝒮ℒ k := ModularForm.mcast (by ring) (E₆.mul V')
  have hcoeW : (⇑W : ℍ → ℂ) = ⇑E₆ * ⇑V' := rfl
  have hWc : (PowerSeries.coeff 0) (qExpansion 1 (⇑W)) = 1 := by
    have he6 : (PowerSeries.coeff 0) (qExpansion 1 (⇑E₆)) = 1 :=
      EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
    rw [hcoeW, show (⇑E₆ * ⇑V' : ℍ → ℂ) = ⇑(E₆.mul V') from (ModularForm.coe_mul _ _).symm,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [hV'c, he6]
  obtain ⟨c, H, hFH⟩ := exists_smul_add_delta_mul F W hWc
  have hWI : W IH = 0 := by
    have h3 : W IH = E₆ IH * V' IH := congrFun hcoeW IH
    rw [h3, E₆_apply_IH, zero_mul]
  have hHI : H IH = 0 := by
    have h2 := congrFun hFH IH
    rw [hF] at h2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h2
    rw [hWI, mul_zero, zero_add] at h2
    rcases mul_eq_zero.mp h2.symm with h' | h'
    · exact absurd h' (deltaMF_apply_ne_zero IH)
    · exact h'
  have hlt : (k - 12).toNat < n := by omega
  obtain ⟨H', hH'⟩ := ih ((k - 12).toNat) hlt (le_refl _) H hHI
  refine ⟨c • V' + ModularForm.mcast (by ring : (12 : ℤ) + (k - 12 - 6) = k - 6)
    (deltaMF.mul H'), ?_⟩
  rw [hFH, hcoeW]
  funext z
  have hz := congrFun hH' z
  simp only [ModularForm.coe_add, IsGLPos.coe_smul, ModularForm.coe_mcast, ModularForm.coe_mul,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  simp only [Pi.mul_apply] at hz
  rw [hz]
  ring

/-- **A level-one form vanishing at `i` is divisible by `E₆`.** -/
theorem exists_eq_E₆_mul {k : ℤ} (F : ModularForm 𝒮ℒ k) (h : F IH = 0) :
    ∃ G : ModularForm 𝒮ℒ (k - 6), (⇑F : ℍ → ℂ) = ⇑E₆ * ⇑G :=
  exists_eq_E₆_mul_aux k.toNat (le_refl _) F h

/-! ### The two residual leaves: the elliptic zeros are SIMPLE -/

/-- **THE ZERO OF `E₄` AT `ρ` IS SIMPLE** (sorry leaf, new 2026-07-31).

TRUE: it is the valence formula for `SL(2, ℤ)` read at the weight-`4` Eisenstein series, and
also the classical statement that `j = E₄³/Δ` has a TRIPLE zero at `ρ`.  Combined with
`E₄_apply_rhoH` (which gives `1 ≤ analyticOrderAt (⇑E₄ ∘ ofComplex) rho` for free) it says the
order is exactly `1`; only the `≤` half is asserted here, because that is all
`eq_zero_of_valence` below consumes.

**SHARP, and the whole theorem depends on it.**  If the order were `e ≥ 2` then
`modularForm_levelOne_eq_zero_of_valence` would be FALSE, witnessed by `F = E₄`, `k = 4`,
`a = c = 0`, `b = e`: every order hypothesis holds, `hk` reads `4 < 4e`, and `E₄ ≠ 0`.

**Route** (see the module docstring for the full account): `Derivative.serreDerivative 4 E₄` is
slash-invariant of weight `6` and `MDiff`; granted `IsBoundedAtImInfty` it is a member of the
one-dimensional `M₆`, hence `-1/3` times `E₆` by its constant `q`-coefficient; at `ρ` the
`E₂E₄` term dies because `E₄(ρ) = 0`, so `deriv (⇑E₄ ∘ ofComplex) rho ≠ 0`, and
`AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero` closes it.  What that route still
owes is `IsBoundedAtImInfty (Derivative.D E₄)`; mathlib's `Derivative.lean` records
"Serre derivative preserves modularity" as a TODO.

**The check that refutes it**: a zero of `E₄` at `ρ` of order `≥ 2`. -/
theorem analyticOrderAt_E₄_rho_le : analyticOrderAt (⇑E₄ ∘ ofComplex) rho ≤ 1 :=
  sorry

/-- **THE ZERO OF `E₆` AT `i` IS SIMPLE** (sorry leaf, new 2026-07-31) — the order-`2` companion
of `analyticOrderAt_E₄_rho_le`, and equally sharp: at order `e ≥ 2` the witness `F = E₆`,
`k = 6`, `a = b = 0`, `c = e` refutes `modularForm_levelOne_eq_zero_of_valence`.

Same route with `∂₆E₆ = (-1/2)·E₄²` inside the one-dimensional `M₈` and `E₄_apply_IH_ne_zero`
in place of `E₆_apply_rhoH_ne_zero`.

**The check that refutes it**: a zero of `E₆` at `i` of order `≥ 2`. -/
theorem analyticOrderAt_E₆_I_le : analyticOrderAt (⇑E₆ ∘ ofComplex) Complex.I ≤ 1 :=
  sorry

/-! ### The induction -/

theorem eq_zero_of_valence_aux (b : ℕ) : ∀ {k : ℤ} (F : ModularForm 𝒮ℒ k) (a : ℕ),
    (a : ℕ∞) ≤ (qExpansion 1 (⇑F)).order →
    (b : ℕ∞) ≤ analyticOrderAt (⇑F ∘ ofComplex) rho →
    k < 12 * a + 4 * b → (F : ℍ → ℂ) = 0 := by
  induction b with
  | zero =>
    intro k F a hinf _ hk
    rcases lt_or_ge k 0 with hneg | hpos
    · have hz : F = 0 := rank_zero_iff_forall_zero.mp
        (ModularForm.levelOne_neg_weight_rank_zero hneg) F
      rw [hz]; rfl
    · have hlt : ((k.toNat / 12 : ℕ) : ℕ∞) < (qExpansion 1 (⇑F)).order := by
        refine lt_of_lt_of_le ?_ hinf
        have hlt' : k.toNat / 12 < a := by
          have : k.toNat < 12 * a := by omega
          omega
        exact_mod_cast hlt'
      have hz : F = 0 := ModularForm.sturm_bound_levelOne hlt
      rw [hz]; rfl
  | succ b ih =>
    intro k F a hinf hrho hk
    have hne : analyticOrderAt (⇑F ∘ ofComplex) rho ≠ 0 := by
      intro h0
      rw [h0, nonpos_iff_eq_zero] at hrho
      simp at hrho
    have hF0 : F rhoH = 0 := by
      have h := apply_eq_zero_of_analyticOrderAt_ne_zero hne
      rwa [show (rho : ℂ) = ((rhoH : ℍ) : ℂ) from rfl, comp_ofComplex_apply] at h
    obtain ⟨G, hG⟩ := exists_eq_E₄_mul F hF0
    have hordinf := qExpansion_of_eq_mul E₄ F G hG
    rw [qExpansion_order_E₄, zero_add] at hordinf
    have hordrho := analyticOrderAt_of_eq_mul E₄ F G hG rhoH
    rw [show ((rhoH : ℍ) : ℂ) = rho from rfl] at hordrho
    have hGrho : (b : ℕ∞) ≤ analyticOrderAt (⇑G ∘ ofComplex) rho := by
      rw [hordrho] at hrho
      have h1 : analyticOrderAt (⇑E₄ ∘ ofComplex) rho + analyticOrderAt (⇑G ∘ ofComplex) rho
          ≤ 1 + analyticOrderAt (⇑G ∘ ofComplex) rho :=
        add_le_add analyticOrderAt_E₄_rho_le (le_refl _)
      have h2 : (b : ℕ∞) + 1 ≤ analyticOrderAt (⇑G ∘ ofComplex) rho + 1 := by
        rw [add_comm (analyticOrderAt (⇑G ∘ ofComplex) rho) 1]
        exact_mod_cast le_trans hrho h1
      exact (WithTop.add_le_add_iff_right ENat.one_ne_top).mp h2
    have hGzero : (G : ℍ → ℂ) = 0 := by
      refine ih G a (hordinf ▸ hinf) hGrho ?_
      push_cast at hk ⊢
      omega
    rw [hG, hGzero, mul_zero]

theorem eq_zero_of_valence (c : ℕ) : ∀ {k : ℤ} (F : ModularForm 𝒮ℒ k) (a b : ℕ),
    (a : ℕ∞) ≤ (qExpansion 1 (⇑F)).order →
    (b : ℕ∞) ≤ analyticOrderAt (⇑F ∘ ofComplex) rho →
    (c : ℕ∞) ≤ analyticOrderAt (⇑F ∘ ofComplex) Complex.I →
    k < 12 * a + 4 * b + 6 * c → (F : ℍ → ℂ) = 0 := by
  induction c with
  | zero =>
    intro k F a b hinf hrho _ hk
    refine eq_zero_of_valence_aux b F a hinf hrho ?_
    push_cast at hk ⊢
    omega
  | succ c ih =>
    intro k F a b hinf hrho hI hk
    have hne : analyticOrderAt (⇑F ∘ ofComplex) Complex.I ≠ 0 := by
      intro h0
      rw [h0, nonpos_iff_eq_zero] at hI
      simp at hI
    have hF0 : F IH = 0 := by
      have h := apply_eq_zero_of_analyticOrderAt_ne_zero hne
      rwa [show (Complex.I : ℂ) = ((IH : ℍ) : ℂ) from rfl, comp_ofComplex_apply] at h
    obtain ⟨G, hG⟩ := exists_eq_E₆_mul F hF0
    have hordinf := qExpansion_of_eq_mul E₆ F G hG
    rw [qExpansion_order_E₆, zero_add] at hordinf
    have hordI := analyticOrderAt_of_eq_mul E₆ F G hG IH
    rw [show ((IH : ℍ) : ℂ) = Complex.I from rfl] at hordI
    have hordrho := analyticOrderAt_of_eq_mul E₆ F G hG rhoH
    rw [show ((rhoH : ℍ) : ℂ) = rho from rfl, analyticOrderAt_E₆_rho, zero_add] at hordrho
    have hGI : (c : ℕ∞) ≤ analyticOrderAt (⇑G ∘ ofComplex) Complex.I := by
      rw [hordI] at hI
      have h1 : analyticOrderAt (⇑E₆ ∘ ofComplex) Complex.I
            + analyticOrderAt (⇑G ∘ ofComplex) Complex.I
          ≤ 1 + analyticOrderAt (⇑G ∘ ofComplex) Complex.I :=
        add_le_add analyticOrderAt_E₆_I_le (le_refl _)
      have h2 : (c : ℕ∞) + 1 ≤ analyticOrderAt (⇑G ∘ ofComplex) Complex.I + 1 := by
        rw [add_comm (analyticOrderAt (⇑G ∘ ofComplex) Complex.I) 1]
        exact_mod_cast le_trans hI h1
      exact (WithTop.add_le_add_iff_right ENat.one_ne_top).mp h2
    have hGzero : (G : ℍ → ℂ) = 0 := by
      refine ih G a b (hordinf ▸ hinf) (hordrho ▸ hrho) hGI ?_
      push_cast at hk ⊢
      omega
    rw [hG, hGzero, mul_zero]

/-! ### The theorem, in the shape `ModularCurve/X0.lean` consumes -/

/-- **THE VANISHING HALF OF THE LEVEL-ONE VALENCE FORMULA.**  A level-one modular form whose
weight is beaten by its own zeros at `i∞`, `ρ` and `i` is zero.

Proven over `analyticOrderAt_E₄_rho_le` and `analyticOrderAt_E₆_I_le` (the two elliptic zeros
are simple) and nothing else; see the module docstring. -/
theorem modularForm_levelOne_eq_zero_of_valence {k : ℤ} (F : ModularForm 𝒮ℒ k) (a b c : ℕ)
    (hinf : (a : ℕ∞) ≤ (qExpansion 1 (⇑F)).order)
    (hrho : (b : ℕ∞) ≤ analyticOrderAt (⇑F ∘ ofComplex) rho)
    (hI : (c : ℕ∞) ≤ analyticOrderAt (⇑F ∘ ofComplex) Complex.I)
    (hk : k < 12 * a + 4 * b + 6 * c) : (⇑F : ℍ → ℂ) = 0 :=
  eq_zero_of_valence c F a b hinf hrho hI hk

end

end Fermat.LevelOneValence

end
