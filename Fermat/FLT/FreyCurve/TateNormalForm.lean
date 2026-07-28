/-
TateNormalForm.lean — own work for the Fermat project (not vendored from the
FLT project).

The **Tate normal form** of an elliptic curve with a marked rational point of
order at least `4`, and the level-`7` (Kubert) parametrisation built on it.

This module exists to give the level-structure leaves of `MazurTorsion.lean`
— `not_order_two_and_order_seven_point` (`X_1(14)`) and its siblings at levels
`15`, `16`, `18` — a common, explicitly computable substrate. The classical
route to every one of them starts by normalising `(E, Q)`, and that
normalisation is what mathlib does not have.

The material is split off into its own module deliberately:
`MazurTorsion.lean` is 7k lines and is edited concurrently by many owners, and
the file is the unit of elaboration, so a shared brick belongs beside it, not
inside it.
-/
module

public import Fermat.FLT.EllipticCurve.MordellWeil
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

/-! ## The Tate normal form -/

/-- The **Tate normal form** `E(b, c) : y² + (1 − c) x y − b y = x³ − b x²`.

This is the universal Weierstrass curve carrying a marked point at the origin
whose order is at least `4`: the marked point is `(0, 0)`, and `b ≠ 0` is
exactly the condition that it is not `2`-torsion, `c` the remaining modulus.
(Tate; Kubert, *Universal bounds on the torsion of elliptic curves*, §2;
Silverman–Tate, *Rational Points on Elliptic Curves*, IV.4.) -/
def tateNormalForm (b c : ℚ) : WeierstrassCurve ℚ :=
  ⟨1 - c, -b, -b, 0, 0⟩

@[simp] lemma tateNormalForm_a₁ (b c : ℚ) : (tateNormalForm b c).a₁ = 1 - c := rfl
@[simp] lemma tateNormalForm_a₂ (b c : ℚ) : (tateNormalForm b c).a₂ = -b := rfl
@[simp] lemma tateNormalForm_a₃ (b c : ℚ) : (tateNormalForm b c).a₃ = -b := rfl
@[simp] lemma tateNormalForm_a₄ (b c : ℚ) : (tateNormalForm b c).a₄ = 0 := rfl
@[simp] lemma tateNormalForm_a₆ (b c : ℚ) : (tateNormalForm b c).a₆ = 0 := rfl

/-- The origin lies on the Tate normal form: `a₆ = 0`. -/
lemma tateNormalForm_equation_zero (b c : ℚ) :
    (tateNormalForm b c).toAffine.Equation 0 0 :=
  (Affine.equation_zero (W := tateNormalForm b c)).mpr rfl

/-- The marked point `(0, 0)` of the Tate normal form is nonsingular. -/
lemma tateNormalForm_nonsingular_zero (b c : ℚ) [(tateNormalForm b c).IsElliptic] :
    (tateNormalForm b c).toAffine.Nonsingular 0 0 :=
  Affine.equation_iff_nonsingular.mp (tateNormalForm_equation_zero b c)

/-- The marked point `(0, 0)` of the Tate normal form, as a point of the
Mordell–Weil group. -/
noncomputable def tateMarkedPoint (b c : ℚ) [(tateNormalForm b c).IsElliptic] :
    (tateNormalForm b c).toAffine.Point :=
  .some 0 0 (tateNormalForm_nonsingular_zero b c)

/-- **The origin is a flex when `a₂` vanishes** (PROVEN): on a curve
`y² + a₁ x y + a₃ y = x³ + a₂ x² + a₄ x` with `a₂ = a₄ = 0` and
`a₃ ≠ 0`, the origin is a point of order dividing `3`.

`a₄ = 0` makes the tangent slope at `(0,0)` equal `a₄/a₃ = 0`, so the
tangent is the line `y = 0`; it meets the curve where `x³ + a₂ x² = 0`,
which with `a₂ = 0` is `x³ = 0` — a triple contact. Concretely the
doubling formulas give `addX = −a₂ = 0` and `negAddY = 0`, so
`P + P = −P`. The hypothesis `a₃ ≠ 0` is what makes the tangent
non-vertical, i.e. `P` not `2`-torsion.

(Written by the owner of the level-`ℓ ≥ 11` nodes and relocated here from
`MazurTorsion.lean` on 2026-07-25, when the two independently-built copies of
the Tate normal form were merged into this module.) -/
lemma three_nsmul_origin_eq_zero (V : WeierstrassCurve ℚ)
    (h2 : V.a₂ = 0) (h4 : V.a₄ = 0) (h3 : V.a₃ ≠ 0)
    (h00 : V.toAffine.Nonsingular 0 0) :
    Affine.Point.some 0 0 h00 + Affine.Point.some 0 0 h00 +
      Affine.Point.some 0 0 h00 = 0 := by
  have hne : (0 : ℚ) ≠ V.toAffine.negY 0 0 := by
    simp only [Affine.negY]
    intro h
    exact h3 (by linarith)
  have hslope : V.toAffine.slope 0 0 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hne]
    simp only [Affine.negY, h2, h4]
    ring_nf
  have key : Affine.Point.some 0 0 h00 + Affine.Point.some 0 0 h00 =
      -Affine.Point.some 0 0 h00 := by
    rw [Affine.Point.add_self_of_Y_ne' hne]
    congr 1
    refine Affine.Point.some_eq_some V ?_ ?_
    · simp only [Affine.addX, hslope, h2]; ring
    · simp only [Affine.negAddY, Affine.addX, hslope, h2]; ring
  rw [key, neg_add_cancel]

/-- **Tate normal form** (PROVEN 2026-07-25 — the normalisation that mathlib
lacks): an elliptic curve `W` over `ℚ` together with a rational point `Q` with
`2Q ≠ 0` and `3Q ≠ 0` is `ℚ`-isomorphic to a curve `E(b, c)` in Tate normal
form, by an isomorphism carrying `Q` to the marked point `(0, 0)`; moreover
`b ≠ 0`.

The classical three-step normalisation (Silverman–Tate IV.4; Kubert §2), which
is what the proof below implements:

1. *Translate `Q` to the origin and flatten the tangent there.* Writing
   `Q = (X, Y)`, the admissible change `(u, r, s, t) = (1, X, s₀, Y)` with
   `s₀ = (a₄ + 2 X a₂ − Y a₁ + 3 X²) / (2 Y + a₁ X + a₃)` sends `(0, 0)` to
   `Q`, kills `a₆` (because `Q` is on the curve) and kills `a₄` (by the choice
   of `s₀`). The denominator `2 Y + a₁ X + a₃` is nonzero precisely because
   `2Q ≠ 0`. The curve is now `y² + A₁ x y + A₃ y = x³ + A₂ x²` with
   `A₃ = 2 Y + a₁ X + a₃ ≠ 0`.
2. *`A₂ ≠ 0` is exactly `3Q ≠ 0`.* On `y² + A₁ x y + A₃ y = x³ + A₂ x²` the
   tangent at `(0, 0)` is `y = 0` (its slope is `0` since `A₃ ≠ 0`), and it
   meets the curve again where `x²(x + A₂) = 0`; so `2Q = −(−A₂, 0)`, which
   collapses back to `±Q` exactly when `A₂ = 0`.
3. *Scale.* The change `(u, r, s, t) = (A₃ / A₂, 0, 0, 0)` rescales
   `A₂ ↦ A₂ u⁻²`, `A₃ ↦ A₃ u⁻³`, so it makes the two equal; calling the common
   value `−b` and the resulting `a₁` coefficient `1 − c` gives
   `b = −A₂³ / A₃²` (nonzero, since `A₂ ≠ 0`) and `c = 1 − A₁ A₂ / A₃`. The
   origin is fixed by a pure scaling, so `Q` lands on `(0, 0)`.

Two implementation notes, both of which cost a verification cycle. The
coefficient `s₀` of step 1 is introduced by its DEFINING IDENTITY
`a₄ + 2Xa₂ − Ya₁ + 3X² = s₀ (2Y + a₁X + a₃)` rather than as a quotient, so no
division appears anywhere in step 1 and each coefficient identity is a
`linear_combination`. And the two variable changes must be unfolded with `rw`,
not `simp only`: `variableChange_a₁` and friends apply at BOTH levels of
`C₂ • (C₁ • W)`, so `simp only` silently rewrites the inner change as well and
destroys the shape. -/
theorem exists_tateNormalForm_of_ne (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (Q : W.toAffine.Point) (h2 : Q + Q ≠ 0) (h3 : Q + Q + Q ≠ 0) :
    ∃ (b c : ℚ) (_ : b ≠ 0) (_ : (tateNormalForm b c).IsElliptic)
      (Ψ : W.toAffine.Point ≃+ (tateNormalForm b c).toAffine.Point),
      Ψ Q = tateMarkedPoint b c := by
  rcases Q with _ | ⟨X, Y, hns⟩
  · exact absurd (add_zero (0 : W.toAffine.Point)) h2
  have hA₃ : 2 * Y + W.a₁ * X + W.a₃ ≠ 0 := by
    intro h0
    refine h2 (Affine.Point.add_self_of_Y_eq ?_)
    show Y = -Y - W.a₁ * X - W.a₃
    linarith
  have hEq : Y ^ 2 + W.a₁ * X * Y + W.a₃ * Y
      = X ^ 3 + W.a₂ * X ^ 2 + W.a₄ * X + W.a₆ := by
    have h : W.toAffine.Equation X Y := Affine.equation_iff_nonsingular.mpr hns
    rwa [Affine.equation_iff] at h
  -- STEP 1: translate `Q` to the origin and flatten the tangent there.
  obtain ⟨s₀, hs₀⟩ : ∃ s : ℚ, W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2
      = s * (2 * Y + W.a₁ * X + W.a₃) :=
    ⟨(W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2) / (2 * Y + W.a₁ * X + W.a₃),
      (div_mul_cancel₀ _ hA₃).symm⟩
  set C₁ : VariableChange ℚ := ⟨1, X, s₀, Y⟩ with hC₁
  have hV₄ : (C₁ • W).a₄ = 0 := by
    simp only [hC₁, variableChange_a₄, Units.val_one, inv_one, one_pow, one_mul]
    linear_combination hs₀
  have hV₆ : (C₁ • W).a₆ = 0 := by
    simp only [hC₁, variableChange_a₆, Units.val_one, inv_one, one_pow, one_mul]
    linear_combination -hEq
  have hV₃ : (C₁ • W).a₃ = 2 * Y + W.a₁ * X + W.a₃ := by
    simp only [hC₁, variableChange_a₃, Units.val_one, inv_one, one_pow, one_mul]
    ring
  have hV₃ne : (C₁ • W).a₃ ≠ 0 := hV₃ ▸ hA₃
  have h00V : (C₁ • W).toAffine.Nonsingular 0 0 :=
    Affine.equation_iff_nonsingular.mp ((Affine.equation_zero (W := C₁ • W)).mpr hV₆)
  have hmapV : (Affine.Point.equivVariableChange W C₁) (Affine.Point.some 0 0 h00V)
      = Affine.Point.some X Y hns := by
    rw [Affine.Point.equivVariableChange_some]
    exact Affine.Point.some_eq_some W (by simp [hC₁]) (by simp [hC₁])
  have h3V : Affine.Point.some 0 0 h00V + Affine.Point.some 0 0 h00V
      + Affine.Point.some 0 0 h00V ≠ 0 := by
    intro h
    refine h3 ?_
    have h' := congrArg (Affine.Point.equivVariableChange W C₁) h
    rwa [map_add, map_add, map_zero, hmapV] at h'
  -- STEP 2: on the normalised curve, `a₂ ≠ 0` is exactly `3Q ≠ 0`.
  have hV₂ne : (C₁ • W).a₂ ≠ 0 := fun h0 =>
    h3V (three_nsmul_origin_eq_zero _ h0 hV₄ hV₃ne h00V)
  -- STEP 3: scale so that `a₂` and `a₃` coincide.
  set C₂ : VariableChange ℚ :=
    ⟨Units.mk0 ((C₁ • W).a₃ / (C₁ • W).a₂) (div_ne_zero hV₃ne hV₂ne), 0, 0, 0⟩ with hC₂
  have hinv : ((C₂.u⁻¹ : ℚˣ) : ℚ) = (C₁ • W).a₂ / (C₁ • W).a₃ := by
    rw [Units.val_inv_eq_inv_val]
    simp only [hC₂, Units.val_mk0]
    rw [inv_div]
  have hUeq : C₂ • (C₁ • W)
      = tateNormalForm (-((C₁ • W).a₂ ^ 3 / (C₁ • W).a₃ ^ 2))
          (1 - (C₁ • W).a₁ * (C₁ • W).a₂ / (C₁ • W).a₃) := by
    ext
    · rw [variableChange_a₁, hinv, tateNormalForm_a₁]
      simp only [hC₂]
      ring
    · rw [variableChange_a₂, hinv, tateNormalForm_a₂]
      simp only [hC₂]
      ring
    · rw [variableChange_a₃, hinv, tateNormalForm_a₃]
      simp only [hC₂]
      field_simp
      ring
    · rw [variableChange_a₄, hinv, tateNormalForm_a₄, hV₄]
      simp only [hC₂]
      ring
    · rw [variableChange_a₆, hinv, tateNormalForm_a₆, hV₆, hV₄]
      simp only [hC₂]
      ring
  have hbne : -((C₁ • W).a₂ ^ 3 / (C₁ • W).a₃ ^ 2) ≠ 0 := by
    simp [hV₂ne, hV₃ne]
  haveI hell : (tateNormalForm (-((C₁ • W).a₂ ^ 3 / (C₁ • W).a₃ ^ 2))
      (1 - (C₁ • W).a₁ * (C₁ • W).a₂ / (C₁ • W).a₃)).IsElliptic :=
    hUeq ▸ (inferInstance : (C₂ • (C₁ • W)).IsElliptic)
  have h00U : (C₂ • (C₁ • W)).toAffine.Nonsingular 0 0 :=
    Affine.equation_iff_nonsingular.mp ((Affine.equation_zero (W := C₂ • (C₁ • W))).mpr
      (by rw [variableChange_a₆, hV₆, hV₄]; simp only [hC₂]; ring))
  have hmapU : (Affine.Point.equivVariableChange (C₁ • W) C₂) (Affine.Point.some 0 0 h00U)
      = Affine.Point.some 0 0 h00V := by
    rw [Affine.Point.equivVariableChange_some]
    exact Affine.Point.some_eq_some (C₁ • W) (by simp [hC₂]) (by simp [hC₂])
  refine ⟨_, _, hbne, hell,
    (Affine.Point.equivVariableChange W C₁).symm.trans
      ((Affine.Point.equivVariableChange (C₁ • W) C₂).symm.trans
        (Affine.Point.equivOfEq hUeq)), ?_⟩
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, ← hmapV, AddEquiv.symm_apply_apply,
    ← hmapU, AddEquiv.symm_apply_apply, Affine.Point.equivOfEq_some]
  rfl

/-- **Tate normal form for a point of order `≥ 4`** (PROVEN 2026-07-25;
no mathlib counterpart): an elliptic curve `W` over `ℚ` carrying a
rational point `P` with `4 ≤ addOrderOf P` is `ℚ`-isomorphic to
`tateNormalForm b c` for some `b, c ∈ ℚ`, by an isomorphism of
Mordell–Weil groups carrying `P` to `(0, 0)`.

This is the corollary of `exists_tateNormalForm_of_ne` in which the two
nonvanishing hypotheses are supplied by an order bound; `4` is the threshold
precisely because `2P ≠ 0` licenses the shear and `3P ≠ 0` the rescaling. It
is stated in exactly the form the level-`ℓ ≥ 11` nodes consume
(`no_torsion_order_of_tateNormalForm` in `MazurTorsion.lean`), and is kept
separate because the hypothesis `4 ≤ addOrderOf P` is strictly stronger than
what the theorem needs: `exists_tateNormalForm_of_ne` also applies to points
of INFINITE order, where `addOrderOf P = 0`.

Silverman ATAEC / Husemöller "Elliptic Curves" Ch. 4; the form is due to
Tate. -/
theorem exists_tateNormalForm (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : W.toAffine.Point) (h4 : 4 ≤ addOrderOf P) :
    ∃ (b c : ℚ) (_ : (tateNormalForm b c).IsElliptic)
      (h00 : (tateNormalForm b c).toAffine.Nonsingular 0 0)
      (Ψ : W.toAffine.Point ≃+ (tateNormalForm b c).toAffine.Point),
      Ψ P = Affine.Point.some 0 0 h00 := by
  have hPP : P + P ≠ 0 := by
    intro h
    rw [← two_nsmul] at h
    have := Nat.le_of_dvd (by norm_num) (addOrderOf_dvd_of_nsmul_eq_zero h)
    omega
  have hPPP : P + P + P ≠ 0 := by
    intro h
    have h3 : (3 : ℕ) • P = 0 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul]; exact h
    have := Nat.le_of_dvd (by norm_num) (addOrderOf_dvd_of_nsmul_eq_zero h3)
    omega
  obtain ⟨b, c, -, hell, Ψ, hΨ⟩ := exists_tateNormalForm_of_ne W P hPP hPPP
  exact ⟨b, c, hell, tateNormalForm_nonsingular_zero b c, Ψ, hΨ⟩

/-! ## The level-`7` parametrisation -/

/-- The discriminant of the Tate normal form, exhibited with its factor `b³`.
In particular the curve is singular when `b = 0`. -/
theorem tateNormalForm_Δ (b c : ℚ) :
    (tateNormalForm b c).Δ = b ^ 3 * (((1 - c) ^ 2 - 4 * b) ^ 2 + 8 * (1 - c) ^ 3
      - 27 * b - 9 * (1 - c) * ((1 - c) ^ 2 - 4 * b)) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, tateNormalForm_a₁, tateNormalForm_a₂,
    tateNormalForm_a₃, tateNormalForm_a₄, tateNormalForm_a₆]
  ring

/-- On an elliptic Tate normal form, `b ≠ 0`: this is exactly the statement
that the marked point is not `2`-torsion. -/
theorem tateNormalForm_b_ne_zero (b c : ℚ) [(tateNormalForm b c).IsElliptic] : b ≠ 0 := by
  intro hb
  have hΔ := (isUnit_Δ (W := tateNormalForm b c)).ne_zero
  rw [tateNormalForm_Δ, hb] at hΔ
  exact hΔ (by ring)

/-- **Kubert's parametrisation of `X_1(7)`** (PROVEN 2026-07-25): if the marked point
`(0, 0)` of the Tate normal form `E(b, c)` has exact order `7`, then

  `b = d³ − d²`,  `c = d² − d`

for a rational `d ∉ {0, 1}` — namely `d = b / c`.

`X_1(7)` has genus `0`, and this is its rational parametrisation: conversely
every `d ∉ {0, 1}` with `d³ − 8d² + 5d + 1 ≠ 0` gives a curve on which `(0, 0)`
has order exactly `7`. (Kubert, *Universal bounds on the torsion of elliptic
curves*, Table 3; Silverman–Tate IV.4.) The discriminant of the resulting curve
is `d⁷ (d − 1)⁷ (d³ − 8d² + 5d + 1)`, verified symbolically 2026-07-25, and the
exact order of `(0, 0)` was confirmed to be `7` at
`d = 2, 3, −1, 1/2, −3, 5, 7/3` by direct computation of the group law
(untrusted searcher, never a proof).

The proof computes the multiples of `Q = (0, 0)` by the affine group law — the
classical chain `2Q = (b, bc)`, `3Q = (c, b − c)` — and then imposes
`4Q = −3Q`, which is what `7Q = 0` says. Only the ABSCISSAE need to be
compared, and `x(4Q) = x(3Q) = c` is, after clearing denominators, exactly

  `b² − b c − c³ = 0`,

which is the Kubert relation: with `d = b / c` it reads `c = d² − d`, and then
`b = d c = d³ − d²`. The side conditions come out of the same computation:
`b ≠ 0` is nonsingularity (`tateNormalForm_b_ne_zero`), and `c ≠ 0` holds
because `c = 0` would make `3Q = (0, b) = −Q`, i.e. `4Q = 0`, so the order
would divide `4` rather than being `7`. Finally `d ≠ 0` since `b ≠ 0` and
`d ≠ 1` since `b = c` would force `c³ = 0`. -/
theorem exists_kubert_param_seven (b c : ℚ) [(tateNormalForm b c).IsElliptic]
    (h7 : addOrderOf (tateMarkedPoint b c) = 7) :
    ∃ d : ℚ, d ≠ 0 ∧ d ≠ 1 ∧ b = d ^ 3 - d ^ 2 ∧ c = d ^ 2 - d := by
  have hb : b ≠ 0 := tateNormalForm_b_ne_zero b c
  have h00 : (tateNormalForm b c).toAffine.Nonsingular 0 0 :=
    tateNormalForm_nonsingular_zero b c
  set Q : (tateNormalForm b c).toAffine.Point := Affine.Point.some 0 0 h00 with hQ
  have hQm : Q = tateMarkedPoint b c := rfl
  have hnegY0 : (tateNormalForm b c).toAffine.negY 0 0 = b := by
    show -0 - (1 - c) * 0 - -b = b
    ring
  have hne0 : (0 : ℚ) ≠ (tateNormalForm b c).toAffine.negY 0 0 := by
    rw [hnegY0]; exact fun h => hb h.symm
  -- `2Q = (b, bc)`
  have e2 : (tateNormalForm b c).toAffine.Equation b (b * c) := by
    rw [Affine.equation_iff]
    show (b * c) ^ 2 + (1 - c) * b * (b * c) + -b * (b * c)
      = b ^ 3 + -b * b ^ 2 + 0 * b + 0
    ring
  have h2ns : (tateNormalForm b c).toAffine.Nonsingular b (b * c) :=
    Affine.equation_iff_nonsingular.mp e2
  have h2Q : Q + Q = Affine.Point.some b (b * c) h2ns := by
    rw [hQ, Affine.Point.add_self_of_Y_ne hne0]
    refine Affine.Point.some_eq_some (tateNormalForm b c) ?_ ?_
    · rw [Affine.slope_of_Y_ne rfl hne0]
      simp only [Affine.addX, Affine.negY, tateNormalForm_a₁, tateNormalForm_a₂,
        tateNormalForm_a₃, tateNormalForm_a₄]
      field_simp
      ring
    · rw [Affine.slope_of_Y_ne rfl hne0]
      simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, tateNormalForm_a₁,
        tateNormalForm_a₂, tateNormalForm_a₃, tateNormalForm_a₄]
      field_simp
      ring
  -- `3Q = (c, b − c)`
  have e3 : (tateNormalForm b c).toAffine.Equation c (b - c) := by
    rw [Affine.equation_iff]
    show (b - c) ^ 2 + (1 - c) * c * (b - c) + -b * (b - c)
      = c ^ 3 + -b * c ^ 2 + 0 * c + 0
    ring
  have h3ns : (tateNormalForm b c).toAffine.Nonsingular c (b - c) :=
    Affine.equation_iff_nonsingular.mp e3
  have h3Q : Q + Q + Q = Affine.Point.some c (b - c) h3ns := by
    rw [h2Q, hQ, Affine.Point.add_of_X_ne hb]
    refine Affine.Point.some_eq_some (tateNormalForm b c) ?_ ?_
    · rw [Affine.slope_of_X_ne hb]
      simp only [Affine.addX, tateNormalForm_a₁, tateNormalForm_a₂]
      field_simp
      ring
    · rw [Affine.slope_of_X_ne hb]
      simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, tateNormalForm_a₁,
        tateNormalForm_a₂, tateNormalForm_a₃]
      field_simp
      ring
  -- `7Q = 0`
  have h7' : addOrderOf Q = 7 := hQm ▸ h7
  have h7Q : Q + Q + Q + Q + (Q + Q + Q) = 0 := by
    have h := addOrderOf_nsmul_eq_zero Q
    rw [h7'] at h
    rw [← h]; abel
  -- `c ≠ 0`: otherwise `3Q = −Q`, so `4Q = 0` and the order would divide `4`.
  have hc : c ≠ 0 := by
    intro hc0
    have h4 : Q + Q + Q + Q = 0 := by
      rw [h3Q, hQ]
      refine Affine.Point.add_of_Y_eq ?_ ?_
      · rw [hc0]
      · show b - c = -0 - (1 - c) * 0 - -b
        rw [hc0]; ring
    have hdvd : addOrderOf Q ∣ 4 := by
      refine addOrderOf_dvd_of_nsmul_eq_zero ?_
      rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl]
      simp only [add_nsmul, one_nsmul]
      exact h4
    rw [h7'] at hdvd
    exact absurd hdvd (by decide)
  -- `4Q = −3Q`; comparing abscissae gives `b² − bc − c³ = 0`.
  have hsum : Q + Q + Q + Q = -(Q + Q + Q) := by
    rw [add_eq_zero_iff_eq_neg] at h7Q
    exact h7Q
  rw [h3Q, hQ, Affine.Point.add_of_X_ne hc, Affine.Point.neg_some] at hsum
  injection hsum with hx4 _
  rw [Affine.slope_of_X_ne hc] at hx4
  simp only [Affine.addX, tateNormalForm_a₁, tateNormalForm_a₂] at hx4
  field_simp at hx4
  refine ⟨b / c, div_ne_zero hb hc, ?_, ?_, ?_⟩
  · intro h1
    rw [div_eq_one_iff_eq hc] at h1
    refine hc ?_
    have hc3 : c ^ 3 = 0 := by linear_combination (-1 : ℚ) * hx4 + b * h1
    have hcc : c * (c * c) = 0 := by linear_combination hc3
    rcases mul_eq_zero.mp hcc with h | h
    · exact h
    · exact (mul_eq_zero.mp h).elim id id
  · field_simp
    linear_combination -hx4
  · field_simp
    linear_combination -hx4

/-! ## The `2`-division cubic -/

/-- A rational point of order `2` gives a rational root of the `2`-division
cubic `4x³ + b₂x² + 2b₄x + b₆` (PROVEN).

A point `P = (x₀, y₀)` satisfies `P + P = 0` exactly when `y₀` equals
`negY x₀ y₀ = −y₀ − a₁x₀ − a₃`, i.e. `2y₀ + a₁x₀ + a₃ = 0`; eliminating `y₀`
between that and the Weierstrass equation leaves the displayed cubic
(Silverman *AEC* III.2.3). -/
theorem exists_two_division_root (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : W.toAffine.Point) (hP : addOrderOf P = 2) :
    ∃ x₀ : ℚ, 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ = 0 := by
  have hPP : P + P = 0 := by
    have h := addOrderOf_nsmul_eq_zero P
    rw [hP, two_nsmul] at h
    exact h
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hP
    exact absurd hP (by norm_num)
  rcases P with _ | ⟨x₀, y₀, hns⟩
  · exact absurd rfl hP0
  -- `P + P = 0` forces `y₀ = negY x₀ y₀`.
  have hy : y₀ = W.toAffine.negY x₀ y₀ := by
    by_contra hy'
    exact Affine.Point.some_ne_zero _ ((Affine.Point.add_self_of_Y_ne hy').symm.trans hPP)
  have hy2 : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
    have : y₀ = -y₀ - W.a₁ * x₀ - W.a₃ := hy
    linarith
  -- State the Weierstrass equation over the atoms `W.aᵢ`, not `W.toAffine.aᵢ`:
  -- the two are definitionally equal but `ring` treats them as distinct atoms.
  have hEq : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      = x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆ := by
    have h : W.toAffine.Equation x₀ y₀ := Affine.equation_iff_nonsingular.mpr hns
    rwa [Affine.equation_iff] at h
  refine ⟨x₀, ?_⟩
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination (-4 : ℚ) * hEq + (2 * y₀ + W.a₁ * x₀ + W.a₃) * hy2

/-! ## The `X_1(14)` Diophantine core -/

/-- **`X_1(14)` has no non-cuspidal rational point** (sorry node — the
irreducible arithmetic core of `not_order_two_and_order_seven_point`, restated
as an elementary Diophantine statement over `ℚ`).

Combining the two preceding nodes turns "an elliptic curve over `ℚ` with a
rational point of order `2` and one of order `7`" into: a rational `d ∉ {0, 1}`
(the level-`7` modulus) and a rational root `x` of the `2`-division cubic of
`E(d³ − d², d² − d)`, which is the displayed polynomial.

THE SAME EQUATION IN ITS DESCENT SHAPE. Writing `A = 1 + d − d²` (the
coefficient `1 − c`) and `b = d³ − d² = d²(d − 1)`, and normalising the
abscissa by `x = −b u`, the cubic becomes `b²` times

  `(A u + 1)² = 4 b u² (u + 1)`,

which is the affine equation of `X_1(14)`. Two consequences a descent will
want, both immediate from that shape: `(d − 1)(u + 1)` must be a rational
SQUARE (namely `w²` with `w = (A u + 1) / (2 d u)`), and eliminating `u` in
favour of `w` gives the plane quartic

  `d³ − d² (w² − 2w + 2) − d (2w − 1)(w² + 1) + w² = 0`.

`X_1(14)` has genus `1` and its Jacobian has Mordell–Weil rank `0` over `ℚ`;
its only rational points are the rational cusps, which are exactly the excluded
loci `d ∈ {0, 1}` (where `b = 0` and the cubic degenerates to `x²(4x + 1)`)
together with the points at infinity.

WHY THIS SHAPE IS PROGRESS. The statement above mentions no elliptic curve, no
modular curve and no torsion: it is a question about rational solutions of one
explicit polynomial equation in two variables, so it can be attacked — and
must be attacked — by descent, with none of the modular machinery that is
absent at this pin. The reduction to it is the content of this module, and it
is what the earlier "IRREDUCIBLE at this mathlib pin" audit of the leaf could
not say.

EVIDENCE (untrusted searchers, never proofs): an exhaustive rational-root scan
over every `d = p/q` in lowest terms with `|p|, q ≤ 40` (about `2000` moduli,
solving the cubic exactly by the rational root theorem at each) found NO
solution with `d ∉ {0, 1}`, and correctly recovered the two degenerate
solutions `(d, u) = (0, −1)` and `(1, −1)` when the exclusion was lifted — so
the scan is not vacuously silent.

WHAT A PROOF NEEDS, IN DEPENDENCY ORDER (surveyed 2026-07-25; every claim
below was checked, not assumed). This curve has rational `2`-torsion, so the
classical route is descent by `2`-isogeny. NO local obstruction can exist —
the curve HAS rational points, the cusps — so nothing purely congruential can
work and the argument must be global.

*Already PROVEN in this development*, and directly reusable:
* `exists_normalForm_pointEquiv_of_rational_two_torsion` — the normal form
  `y² = x³ + a x² + b x` with the `2`-torsion point at `(0,0)`;
* `twoIsogenyFun`, `twoIsogenyFun_add`,
  `exists_quotient_isogeny_of_normalForm_two_torsion` — the isogeny
  `φ(x,y) = (y²/x², y(b−x²)/x²)` onto `y² = x³ − 2a x² + (a²−4b) x`, and its
  additivity. So `φ` and its target curve are in hand.

*Missing, in the order they are needed*:
1. The DESCENT MAP `α : E(ℚ) → ℚ*/(ℚ*)²`, `α(O) = 1`, `α(0,0) = b`,
   `α(x,y) = x` otherwise, and the proof that it is a HOMOMORPHISM. This is
   the first brick and it is elementary and self-contained: it amounts to the
   identity that `x₁x₂x₃` is a square whenever `P₁ + P₂ + P₃ = 0` with all
   `xᵢ ≠ 0`, which is pure group-law algebra of the same kind as
   `MazurFourTorsion.cubic_vieta` and `halving_square` already in
   `MazurTorsion.lean`.
2. `ker α = ψ(E'(ℚ))` for the dual isogeny `ψ`, giving
   `E(ℚ)/ψ(E'(ℚ)) ↪ ℚ*/(ℚ*)²`.
3. The image lands in the `S`-Selmer group for `S` the bad primes, which
   bounds it: mathlib HAS this codomain as
   `IsDedekindDomain.selmerGroup` (`K⟮S,n⟯`), with the exact-sequence API
   `valuation_ker_eq` / `fromUnit_ker` / `fromUnitLift_injective`.
4. MORDELL–WEIL finite generation (canonical heights), to pass from "rank `0`"
   to "`E(ℚ)` is finite". **This is the genuinely large missing theory: it is
   absent from mathlib entirely** — there is no Mordell–Weil, no rank, no
   height machinery — so it must be built or the last step routed around it.

   **CORRECTION (2026-07-28), and it is exactly the sweep this note would
   have misled.** "No height machinery" is FALSE at pin `a3364fa`, and so
   is the implied absence of the abstract descent step. Mathlib has
   `Mathlib/NumberTheory/Height/` — six modules, with `Height.mulHeight` /
   `logHeight` on tuples, `AdmissibleAbsValues` for every number field
   (hence `ℚ`), Northcott as a real instance, the height machine for
   homogeneous forms in BOTH directions, and
   `Height/EllipticCurve.lean`'s
   `abs_logHeight_addSubMap_sub_two_mul_logHeight_le` — and
   `Mathlib/GroupTheory/Descent.lean`, whose
   `AddCommGroup.fg_of_descent'` is precisely "parallelogram law +
   Northcott + `G/2G` finite ⟹ finitely generated". The reason this reads
   as absent is that `WeilHeight`, `NeronTate` and `MordellWeil` occur
   NOWHERE in those files, so any grep for them returns nothing.

   What genuinely remains on this axis is narrower than the item claims:
   the *canonical* (Néron–Tate) height, the naive height as a function on
   `E(ℚ)` together with its parallelogram law (all three are `TODO`s in
   `Height/EllipticCurve.lean`), and weak Mordell–Weil. The abstract
   descent step and the underlying height theory are not among them.
   Full correction: the CORRECTION section of
   `Fermat/FLT/Mathlib/GroupTheory/Descent.lean`.
5. The concrete computation for this curve: both descent images trivial, then
   the torsion determination.

For calibration: `~/cs/FLT`, the reference project, does not prove Mazur at
all — it takes `axiom Mazur_statement`. So nothing here can be vendored, and
this node sits past the frontier of what is formalized in either project.

**RESOLVED 2026-07-26 — this is no longer a leaf.** The survey above stands as
a description of the mathematics, and its item 4 was right that Mordell–Weil is
the load-bearing absence; what it got wrong is that the descent has to be built
HERE. It does not: level `11` had already routed its plane model to the named
Cremona curve `11a3` in `Fermat/FLT/EllipticCurve/MordellWeil.lean`, and the
same architecture applies verbatim at level `14`. This node is now PROVEN over
`curve14a4_points` and `curve14a4_finite` there, so the Mordell–Weil input is
SHARED with level `11` instead of duplicated, and items 1–3 and 5 of the survey
above are simply not needed — the descent they were preparing is the one that
`curve14a4_isTorsion` states.

THE PROOF, in four steps, all of them PROVEN here.

1. *The chart.* `x = 0` forces `(d³ − d²)² = 0`, i.e. `d ∈ {0, 1}`, which the
   hypotheses exclude. So `x ≠ 0` and the map below is defined.
2. *The birational map to `14a4`.* With `Nx` and `Ny` the two explicit
   polynomials written in the proof,

       X = Nx / x³,   Y = Ny / x³

   is a point of `y² + xy + y = x³ − x` whenever `(d, x)` lies on the sextic.
   The identity is a single `linear_combination` against the sextic with an
   explicit degree-`9` cofactor (Magma exact division, then checked by `ring`
   in Lean — the CAS supplies the certificate, the kernel verifies it).
3. *Mordell–Weil at `14a4`.* `curve14a4_points` lists the five affine rational
   points; their `x`-coordinates take only the three values `0`, `1`, `−1`.
4. *Pulling the three fibres back.* For each value `c ∈ {0, 1, −1}` the pair of
   equations `sextic = 0`, `Nx = c·x³` forces `x⁶·d·(d − 1) = 0` — an ideal
   membership with a small explicit certificate (Singular `lift`, again checked
   by `ring`). Since `x ≠ 0`, this gives `d ∈ {0, 1}`, contradicting the
   hypotheses.

WHY THE CERTIFICATES ARE SMALL, which is the only delicate point. Taken
literally the elimination ideals are generated by `d⁹(d−1)⁵`, `d¹⁰(d−1)⁵` and
`d⁹(d−1)⁷`, whose cofactors run to 60–90 terms with fractions. SATURATING BY
`x` — legitimate here precisely because step 1 established `x ≠ 0` — replaces
the target by `x⁶·d·(d − 1)` and collapses the cofactors to between 1 and 10
terms each. That is the difference between a proof that fits on a screen and
one that does not.

IDENTIFICATION OF THE CURVE (Magma 2026-07-26, untrusted searcher; classical to
Kubert and Ligozat). The projective closure of this sextic has `Genus = 1`;
`EllipticCurve` + `MinimalModel` return `y² + xy + y = x³ − x`, with
`Conductor = 14` and `CremonaReference = 14a4`; `RankBound = 0` with proof flag
`true`; and `MordellWeilGroup ≅ ℤ/6`, listing exactly six points. Those six
account for every rational point of the curve, and the four AFFINE ones are
`(d, x) = (1, −1/4), (0, 0), (0, −1/4), (1, 0)` — so the excluded loci `d = 0`
and `d = 1` are EXACTLY the rational points, and the two remaining points are at
infinity. The statement is therefore neither false nor vacuous, and it is
SHARP: dropping either hypothesis makes it false, with the witness listed above.
This supersedes the earlier evidence in this docstring (an exhaustive scan over
`|p|, q ≤ 40`), which was consistent with the truth but did not identify the
curve or exhibit the obstruction. -/
theorem x1_fourteen_no_rational_point (d x : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1) :
    4 * x ^ 3 + ((1 + d - d ^ 2) ^ 2 - 4 * (d ^ 3 - d ^ 2)) * x ^ 2
        - 2 * (1 + d - d ^ 2) * (d ^ 3 - d ^ 2) * x + (d ^ 3 - d ^ 2) ^ 2 ≠ 0 := by
  intro h
  -- Step 1: the chart `x ≠ 0`.  At `x = 0` the sextic reads `(d²(d − 1))² = 0`.
  have hx : x ≠ 0 := by
    rintro rfl
    have h2 : (d ^ 2 * (d - 1)) ^ 2 = 0 := by linear_combination h
    have h3 : d ^ 2 * (d - 1) = 0 := pow_eq_zero_iff two_ne_zero |>.mp h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact hd0 (pow_eq_zero_iff two_ne_zero |>.mp h4)
    · exact hd1 (by linarith)
  have hx3 : x ^ 3 ≠ 0 := pow_ne_zero _ hx
  -- The contradiction every branch of step 4 lands on.
  have hcontra : x ^ 6 * d * (d - 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx) hd0) ?_
    intro hc; exact hd1 (by linarith)
  -- Step 2: `(Nx / x³, Ny / x³)` is a rational point of `14a4`.
  have heq : curve14a4.toAffine.Equation
      ((d^4*x + 2*d^3*x^2 + d^2*x^3 - d^3*x - 2*d^2*x^2 - 5*d*x^3 - d*x^2) / x^3)
      ((-d^5*x - 2*d^4*x^2 - d^3*x^3 + d^5 + 5*d^4*x + 7*d^3*x^2 + 7*d^2*x^3
        - d^4 - 3*d^3*x - 5*d^2*x^2 - 7*d*x^3 - 2*d^2*x - 4*d*x^2 - 4*x^3 - x^2) / x^3) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [curve14a4]
    field_simp
    linear_combination (-d^6 - 4*d^5*x + d^5 - 5*d^4*x^2 + 2*d^4*x + d^4 - 2*d^3*x^3
      + 5*d^3*x^2 + 8*d^3*x + 8*d^2*x^3 + 15*d^2*x^2 + 2*d^2*x + 16*d*x^3 + 7*d*x^2
      + 3*x^3 + x^2) * h
  have hns := WeierstrassCurve.Affine.equation_iff_nonsingular.mp heq
  -- Step 3: Mordell–Weil at `14a4` — five affine points, three `x`-values.
  -- Step 4: each fibre pulls back into `d ∈ {0, 1}`.
  rcases curve14a4_points curve14a4_finite _ _ hns with h5 | h5 | h5 | h5 | h5
  · rw [Prod.mk.injEq] at h5
    have hg := (div_eq_iff hx3).mp h5.1
    refine hcontra ?_
    linear_combination
      (1/4*d^3*x^2 + 1/4*d^2*x^3 - 1/4*d^2*x^2 - 1/4*d*x^3) * h
      + (-1/4*d^5*x - 1/4*d^4*x^2 + 1/2*d^4*x + 1/2*d^3*x^2 - 1/4*d^3*x - 1/4*d*x^2) * hg
  · rw [Prod.mk.injEq] at h5
    have hg := (div_eq_iff hx3).mp h5.1
    refine hcontra ?_
    linear_combination
      (d*x^3) * h + (-d^3*x^2 + d^2*x^2 + x^3) * hg
  · rw [Prod.mk.injEq] at h5
    have hg := (div_eq_iff hx3).mp h5.1
    refine hcontra ?_
    linear_combination
      (1/4*d^3*x + 3/4*d^2*x^2 + d*x^3 + 1/4*d*x^2 - 1/4*x^3) * h
      + (-1/4*d^5 - 3/4*d^4*x - d^3*x^2 + 1/4*d^4 + 1/2*d^3*x + 5/4*d^2*x^2 + 1/2*d^2*x
        + 3/4*d*x^2 + x^3 + 1/4*x^2) * hg
  · rw [Prod.mk.injEq] at h5
    have hg := (div_eq_iff hx3).mp h5.1
    refine hcontra ?_
    linear_combination
      (d*x^3) * h + (-d^3*x^2 + d^2*x^2 + x^3) * hg
  · rw [Prod.mk.injEq] at h5
    have hg := (div_eq_iff hx3).mp h5.1
    refine hcontra ?_
    linear_combination
      (1/4*d^3*x^2 + 1/4*d^2*x^3 - 1/4*d^2*x^2 - 1/4*d*x^3) * h
      + (-1/4*d^5*x - 1/4*d^4*x^2 + 1/2*d^4*x + 1/2*d^3*x^2 - 1/4*d^3*x - 1/4*d*x^2) * hg

end WeierstrassCurve

end
