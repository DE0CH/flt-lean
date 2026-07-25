/-
PointReduction.lean — own work for the Fermat project (not vendored from the
FLT project).

# Reduction of the POINTS of a Weierstrass curve

mathlib's `Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` reduces the
CURVE — it produces `W.reduction R : WeierstrassCurve (ResidueField R)` from a
minimal model — but it says nothing about the POINTS. This file supplies the
missing half, Silverman *AEC* VII.2: for a valuation subring `A` of a field `F`,
a local ring homomorphism `ρ : A →+* κ` into a field, and a Weierstrass curve
`W` over `F` with `A`-integral coefficients reducing to `Wred` over `κ`, the map

  `red : W.Point → Wred.Point`,   `(x, y) ↦ (ρ x, ρ y)` if `x ∈ A`, else `O`

is a group homomorphism whose kernel is exactly the non-integral locus.

The reduction datum is packaged as `WeierstrassCurve.IsReductionAlong`: five
integrality conditions on the coefficients of `W` and five equations saying that
`Wred` carries their images. Nothing here asks `κ` to BE the residue field of
`A` — only that `ρ` be local (`IsLocalHom`) — so the target may be any field
receiving the residue field, which is what the applications need.

The mathematical content is concentrated in one lemma,
`WeierstrassCurve.IsReductionAlong.exists_slope_res`: the slope of the
chord/tangent through two integral points is itself integral and reduces to the
slope of the reduced points, PROVIDED the two reduced points are not vertically
opposite. The delicate case is `x₁ ≠ x₂` upstairs but `ρ x₁ = ρ x₂` downstairs,
where the chord slope `(y₁ - y₂)/(x₁ - x₂)` is a quotient of two elements of the
maximal ideal: subtracting the two Weierstrass equations factors it as `G/U`
with

  `U = y₁ - negY x₂ y₂`  a UNIT (this is exactly the non-vertical hypothesis)

and `G` integral, and the images of `G` and `U` are precisely the numerator and
denominator of the TANGENT slope downstairs — which is what the reduced addition
uses, since `ρ x₁ = ρ x₂` and `ρ y₁ ≠ negY (ρ x₂) (ρ y₂)` force `ρ y₁ = ρ y₂`.

Once the slope is under control, `addX`, `addY` and `negY` reduce term by term,
because they are polynomial in the coordinates and the coefficients.
-/
module

public import Fermat.FLT.KnownIn1980s.EllipticCurves.Flat

@[expose] public section

open scoped WeierstrassCurve.Affine

open IsLocalRing

namespace ValuationSubring

variable {F : Type*} [Field F] {A : ValuationSubring F} {κ : Type*} [Field κ]

/-- Under a local homomorphism into a field, an element of the valuation subring
with nonzero image is a unit. -/
theorem isUnit_of_map_ne_zero (ρ : A →+* κ) [IsLocalHom ρ] {a : A} (h : ρ a ≠ 0) :
    IsUnit a :=
  IsLocalHom.map_nonunit (f := ρ) a (isUnit_iff_ne_zero.mpr h)

/-- The coercion `A → F` of a unit of a valuation subring is nonzero. -/
theorem coe_ne_zero_of_isUnit {b : A} (hb : IsUnit b) : (b : F) ≠ 0 := fun h =>
  hb.ne_zero (Subtype.ext (by simpa using h))

/-- **Division by a unit stays integral, and commutes with the reduction map**:
if `b` is a unit of the valuation subring `A`, the quotient `a / b` computed in
`F` is the image of an element of `A` whose reduction is `ρ a / ρ b`. -/
theorem exists_div_eq_of_isUnit (ρ : A →+* κ) (a : A) {b : A} (hb : IsUnit b) :
    ∃ L : A, (a : F) / (b : F) = (L : F) ∧ ρ L = ρ a / ρ b := by
  obtain ⟨u, rfl⟩ := hb
  have h0 : ((u : A) : F) ≠ 0 := coe_ne_zero_of_isUnit ⟨u, rfl⟩
  have hu1 : (((u⁻¹ : Aˣ) : A) : F) * (((u : Aˣ) : A) : F) = 1 := by
    have hmul : ((((u⁻¹ : Aˣ) : A) * ((u : Aˣ) : A) : A) : F)
        = (((u⁻¹ : Aˣ) : A) : F) * (((u : Aˣ) : A) : F) := by push_cast; ring
    rw [← hmul, u.inv_mul]
    exact OneMemClass.coe_one A
  refine ⟨a * ((u⁻¹ : Aˣ) : A), ?_, ?_⟩
  · rw [div_eq_iff h0]
    push_cast
    rw [mul_assoc, hu1, mul_one]
  · rw [map_mul, div_eq_mul_inv]
    congr 1
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)

/-- **Reduction to zero is exactly small valuation**: under a local homomorphism into a
field, an element of the valuation subring is killed exactly when its valuation is `< 1`.
This is the bridge between the residue-map language used here and the valuation language
of the kernel-of-reduction helpers in `Flat.lean`. -/
theorem map_eq_zero_iff (ρ : A →+* κ) [IsLocalHom ρ] (a : A) :
    ρ a = 0 ↔ A.valuation (a : F) < 1 := by
  rw [← ValuationSubring.valuation_lt_one_iff A a, IsLocalRing.mem_maximalIdeal,
    _root_.mem_nonunits_iff]
  refine ⟨fun h0 hu => ?_, fun hnu => ?_⟩
  · exact not_isUnit_zero (h0 ▸ hu.map ρ)
  · by_contra h0
    exact hnu (isUnit_of_map_ne_zero ρ h0)

/-- Valuation form of `map_eq_zero_iff`, phrased on a member of the ambient field. -/
theorem valuation_lt_one_of_res_eq_zero (ρ : A →+* κ) [IsLocalHom ρ] {a : F} (ha : a ∈ A)
    (h0 : ρ (⟨a, ha⟩ : A) = 0) : A.valuation a < 1 := by
  simpa using (map_eq_zero_iff ρ _).mp h0

/-- Valuation form of `isUnit_of_map_ne_zero`, phrased on a member of the ambient field. -/
theorem valuation_eq_one_of_res_ne_zero (ρ : A →+* κ) [IsLocalHom ρ] {a : F} (ha : a ∈ A)
    (h0 : ρ (⟨a, ha⟩ : A) ≠ 0) : A.valuation a = 1 := by
  have : IsUnit (⟨a, ha⟩ : A) := isUnit_of_map_ne_zero ρ h0
  rw [ValuationSubring.valuation_eq_one_iff] at this
  simpa using this

end ValuationSubring

namespace WeierstrassCurve

/-! ## The reduction datum -/

/-- **`Wred` is the reduction of `W` along `ρ`**: the coefficients of the
Weierstrass curve `W` over `F` lie in the valuation subring `A`, and the
Weierstrass curve `Wred` over `κ` has their images under `ρ` as coefficients.

Packaged as a structure so that the ten conditions do not have to be threaded
through every statement by hand. The membership proofs are named because the
coefficient equations mention them. -/
structure IsReductionAlong {F κ : Type*} [Field F] [Field κ] (A : ValuationSubring F)
    (ρ : A →+* κ) (W : WeierstrassCurve F) (Wred : WeierstrassCurve κ) : Prop where
  /-- `a₁` is integral. -/
  a₁_mem : W.a₁ ∈ A
  /-- `a₂` is integral. -/
  a₂_mem : W.a₂ ∈ A
  /-- `a₃` is integral. -/
  a₃_mem : W.a₃ ∈ A
  /-- `a₄` is integral. -/
  a₄_mem : W.a₄ ∈ A
  /-- `a₆` is integral. -/
  a₆_mem : W.a₆ ∈ A
  /-- the reduced `a₁`. -/
  a₁_eq : Wred.a₁ = ρ ⟨W.a₁, a₁_mem⟩
  /-- the reduced `a₂`. -/
  a₂_eq : Wred.a₂ = ρ ⟨W.a₂, a₂_mem⟩
  /-- the reduced `a₃`. -/
  a₃_eq : Wred.a₃ = ρ ⟨W.a₃, a₃_mem⟩
  /-- the reduced `a₄`. -/
  a₄_eq : Wred.a₄ = ρ ⟨W.a₄, a₄_mem⟩
  /-- the reduced `a₆`. -/
  a₆_eq : Wred.a₆ = ρ ⟨W.a₆, a₆_mem⟩

/-! ## Integral points and the constructor congruence -/

/-- Two affine points of a Weierstrass curve with equal coordinates are equal (the
nonsingularity witnesses are propositions, hence irrelevant). -/
theorem Affine.Point.eq_of_coords_eq {κ : Type*} [Field κ] {V : WeierstrassCurve κ}
    {x y x' y' : κ} {hns : V.toAffine.Nonsingular x y} {hns' : V.toAffine.Nonsingular x' y'}
    (hx : x = x') (hy : y = y') :
    (Affine.Point.some x y hns : V.toAffine.Point) = Affine.Point.some x' y' hns' := by
  subst hx
  subst hy
  rfl

/-- **`A`-integrality of an affine point**: the point at infinity is integral, and an
affine point is integral exactly when its ABSCISSA lies in the valuation subring `A`
(the ordinate is then automatic, by `ordinate_mem_of_abscissa_mem`). The complement of
this predicate is the kernel of reduction. -/
def IsIntegralPoint {F : Type*} [Field F] (A : ValuationSubring F) {W : WeierstrassCurve F} :
    W.toAffine.Point → Prop
  | .zero => True
  | .some x _ _ => x ∈ A

section IsIntegralPoint

variable {F : Type*} [Field F] {A : ValuationSubring F} {W : WeierstrassCurve F}

@[simp]
theorem isIntegralPoint_zero : IsIntegralPoint A (0 : W.toAffine.Point) := trivial

@[simp]
theorem isIntegralPoint_some {x y : F} (hns : W.toAffine.Nonsingular x y) :
    IsIntegralPoint A (Affine.Point.some x y hns) ↔ x ∈ A := Iff.rfl

theorem isIntegralPoint_neg {P : W.toAffine.Point} :
    IsIntegralPoint A (-P) ↔ IsIntegralPoint A P := by
  cases P with
  | zero => exact Iff.rfl
  | some x y hns => exact Iff.rfl

end IsIntegralPoint

namespace IsReductionAlong

-- The whole API below shares one `variable` block, so that every statement reads the
-- same way and successor proofs can be moved between them without re-deriving
-- signatures; the three decidability/locality instances are genuinely needed by the
-- slope and additivity half and merely carried by the rest.
set_option linter.unusedSectionVars false

variable {F κ : Type*} [Field F] [Field κ] {A : ValuationSubring F} {ρ : A →+* κ}
  {W : WeierstrassCurve F} {Wred : WeierstrassCurve κ} (h : IsReductionAlong A ρ W Wred)

/-- The reduction of an integral element only depends on its value. -/
theorem res_of_eq {a : A} {x : F} (hx : x ∈ A) (hax : (a : F) = x) :
    ρ (⟨x, hx⟩ : A) = ρ a :=
  congrArg ρ (Subtype.ext hax.symm)

include h

/-! ### Integrality and reduction of the Weierstrass formulas -/

/-- `negY` of integral coordinates is integral. -/
theorem negY_mem {x y : F} (hx : x ∈ A) (hy : y ∈ A) : W.toAffine.negY x y ∈ A := by
  simp only [Affine.negY]
  exact sub_mem (sub_mem (neg_mem hy) (mul_mem h.a₁_mem hx)) h.a₃_mem

/-- `negY` reduces to `negY`. -/
theorem res_negY {x y : F} (hx : x ∈ A) (hy : y ∈ A) :
    ρ (⟨W.toAffine.negY x y, h.negY_mem hx hy⟩ : A) =
      Wred.toAffine.negY (ρ ⟨x, hx⟩) (ρ ⟨y, hy⟩) := by
  have hrw : (⟨W.toAffine.negY x y, h.negY_mem hx hy⟩ : A) =
      -(⟨y, hy⟩ : A) - (⟨W.a₁, h.a₁_mem⟩ : A) * ⟨x, hx⟩ - ⟨W.a₃, h.a₃_mem⟩ := by
    apply Subtype.ext
    push_cast
    simp only [Affine.negY]
  rw [hrw, Affine.negY, h.a₁_eq, h.a₃_eq]
  simp only [map_neg, map_sub, map_mul]

/-- `addX` of integral data is integral. -/
theorem addX_mem {x₁ x₂ L : F} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hL : L ∈ A) :
    W.toAffine.addX x₁ x₂ L ∈ A := by
  simp only [Affine.addX]
  exact sub_mem (sub_mem (sub_mem (add_mem (pow_mem hL 2) (mul_mem h.a₁_mem hL)) h.a₂_mem) hx₁) hx₂

/-- `addX` reduces to `addX`. -/
theorem res_addX {x₁ x₂ L : F} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hL : L ∈ A) :
    ρ (⟨W.toAffine.addX x₁ x₂ L, h.addX_mem hx₁ hx₂ hL⟩ : A) =
      Wred.toAffine.addX (ρ ⟨x₁, hx₁⟩) (ρ ⟨x₂, hx₂⟩) (ρ ⟨L, hL⟩) := by
  have hrw : (⟨W.toAffine.addX x₁ x₂ L, h.addX_mem hx₁ hx₂ hL⟩ : A) =
      (⟨L, hL⟩ : A) ^ 2 + (⟨W.a₁, h.a₁_mem⟩ : A) * ⟨L, hL⟩ - ⟨W.a₂, h.a₂_mem⟩
        - ⟨x₁, hx₁⟩ - ⟨x₂, hx₂⟩ := by
    apply Subtype.ext
    push_cast
    simp only [Affine.addX]
  rw [hrw, Affine.addX, h.a₁_eq, h.a₂_eq]
  simp only [map_add, map_sub, map_mul, map_pow]

/-- `negAddY` of integral data is integral. -/
theorem negAddY_mem {x₁ x₂ y₁ L : F} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∈ A)
    (hL : L ∈ A) : W.toAffine.negAddY x₁ x₂ y₁ L ∈ A := by
  simp only [Affine.negAddY]
  exact add_mem (mul_mem hL (sub_mem (h.addX_mem hx₁ hx₂ hL) hx₁)) hy₁

/-- `addY` of integral data is integral. -/
theorem addY_mem {x₁ x₂ y₁ L : F} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∈ A)
    (hL : L ∈ A) : W.toAffine.addY x₁ x₂ y₁ L ∈ A :=
  h.negY_mem (h.addX_mem hx₁ hx₂ hL) (h.negAddY_mem hx₁ hx₂ hy₁ hL)

/-- `addY` reduces to `addY`. -/
theorem res_addY {x₁ x₂ y₁ L : F} (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₁ : y₁ ∈ A) (hL : L ∈ A) :
    ρ (⟨W.toAffine.addY x₁ x₂ y₁ L, h.addY_mem hx₁ hx₂ hy₁ hL⟩ : A) =
      Wred.toAffine.addY (ρ ⟨x₁, hx₁⟩) (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₁, hy₁⟩) (ρ ⟨L, hL⟩) := by
  have hrwX : ρ (⟨W.toAffine.addX x₁ x₂ L, h.addX_mem hx₁ hx₂ hL⟩ : A) =
      Wred.toAffine.addX (ρ ⟨x₁, hx₁⟩) (ρ ⟨x₂, hx₂⟩) (ρ ⟨L, hL⟩) := h.res_addX hx₁ hx₂ hL
  have hrwN : ρ (⟨W.toAffine.negAddY x₁ x₂ y₁ L, h.negAddY_mem hx₁ hx₂ hy₁ hL⟩ : A) =
      Wred.toAffine.negAddY (ρ ⟨x₁, hx₁⟩) (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₁, hy₁⟩) (ρ ⟨L, hL⟩) := by
    have hrw : (⟨W.toAffine.negAddY x₁ x₂ y₁ L, h.negAddY_mem hx₁ hx₂ hy₁ hL⟩ : A) =
        (⟨L, hL⟩ : A) * ((⟨W.toAffine.addX x₁ x₂ L, h.addX_mem hx₁ hx₂ hL⟩ : A) - ⟨x₁, hx₁⟩)
          + ⟨y₁, hy₁⟩ := by
      apply Subtype.ext
      push_cast
      simp only [Affine.negAddY]
    rw [hrw]
    simp only [map_add, map_sub, map_mul, Affine.negAddY]
    rw [hrwX]
  have hstep : ρ (⟨W.toAffine.addY x₁ x₂ y₁ L, h.addY_mem hx₁ hx₂ hy₁ hL⟩ : A)
      = Wred.toAffine.negY (ρ (⟨W.toAffine.addX x₁ x₂ L, h.addX_mem hx₁ hx₂ hL⟩ : A))
          (ρ (⟨W.toAffine.negAddY x₁ x₂ y₁ L, h.negAddY_mem hx₁ hx₂ hy₁ hL⟩ : A)) :=
    h.res_negY (h.addX_mem hx₁ hx₂ hL) (h.negAddY_mem hx₁ hx₂ hy₁ hL)
  rw [hstep, hrwX, hrwN]
  rfl

/-- An integral point of `W` reduces to a point of `Wred`. -/
theorem equation_res {x y : F} (hx : x ∈ A) (hy : y ∈ A) (hE : W.toAffine.Equation x y) :
    Wred.toAffine.Equation (ρ ⟨x, hx⟩) (ρ ⟨y, hy⟩) := by
  rw [Affine.equation_iff] at hE ⊢
  have hA : (⟨y, hy⟩ : A) ^ 2 + (⟨W.a₁, h.a₁_mem⟩ : A) * ⟨x, hx⟩ * ⟨y, hy⟩
        + (⟨W.a₃, h.a₃_mem⟩ : A) * ⟨y, hy⟩ =
      (⟨x, hx⟩ : A) ^ 3 + (⟨W.a₂, h.a₂_mem⟩ : A) * (⟨x, hx⟩ : A) ^ 2
        + (⟨W.a₄, h.a₄_mem⟩ : A) * ⟨x, hx⟩ + ⟨W.a₆, h.a₆_mem⟩ := by
    apply Subtype.ext
    push_cast
    exact hE
  have := congrArg ρ hA
  simp only [map_add, map_mul, map_pow] at this
  rw [h.a₁_eq, h.a₂_eq, h.a₃_eq, h.a₄_eq, h.a₆_eq]
  exact this

/-! ### The slope -/

variable [DecidableEq F] [DecidableEq κ] [IsLocalHom ρ]

/-- **The chord–tangent slope reduces** (the analytic heart of the reduction
map, Silverman *AEC* VII.2.1): for two points of `W` with integral coordinates
whose reductions are NOT vertically opposite, the slope of the line joining them
lies in `A` and reduces to the slope of the reduced points.

The two cases where `ρ x₁ = ρ x₂` are the content: if `x₁ = x₂` the slope is the
tangent formula whose denominator `y₁ - negY x₁ y₁` is a unit; if `x₁ ≠ x₂` the
chord slope `(y₁ - y₂)/(x₁ - x₂)` is a `𝔪/𝔪` indeterminate form which the
subtracted Weierstrass equations rewrite as `G/U` with `U` a unit, and `ρG/ρU`
is exactly the tangent slope downstairs. -/
theorem exists_slope_res {x₁ y₁ x₂ y₂ : F} (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A)
    (hx₂ : x₂ ∈ A) (hy₂ : y₂ ∈ A)
    (hE₁ : W.toAffine.Equation x₁ y₁) (hE₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(ρ (⟨x₁, hx₁⟩ : A) = ρ ⟨x₂, hx₂⟩ ∧
      ρ (⟨y₁, hy₁⟩ : A) = Wred.toAffine.negY (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₂, hy₂⟩))) :
    ∃ (L : F) (hL : L ∈ A), W.toAffine.slope x₁ x₂ y₁ y₂ = L ∧
      ρ (⟨L, hL⟩ : A) = Wred.toAffine.slope (ρ ⟨x₁, hx₁⟩) (ρ ⟨x₂, hx₂⟩)
        (ρ ⟨y₁, hy₁⟩) (ρ ⟨y₂, hy₂⟩) := by
  have hr₁ := h.equation_res hx₁ hy₁ hE₁
  have hr₂ := h.equation_res hx₂ hy₂ hE₂
  by_cases hx : ρ (⟨x₁, hx₁⟩ : A) = ρ ⟨x₂, hx₂⟩
  · -- the reduced abscissas agree, so the reduced addition is a DOUBLING
    have hy : ρ (⟨y₁, hy₁⟩ : A) ≠
        Wred.toAffine.negY (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₂, hy₂⟩) := fun hh => hxy ⟨hx, hh⟩
    have hyy : ρ (⟨y₁, hy₁⟩ : A) = ρ ⟨y₂, hy₂⟩ := Affine.Y_eq_of_Y_ne hr₁ hr₂ hx hy
    have hy' : ρ (⟨y₁, hy₁⟩ : A) ≠
        Wred.toAffine.negY (ρ ⟨x₁, hx₁⟩) (ρ ⟨y₁, hy₁⟩) := by
      rw [hx]
      intro hh
      exact hy (hh.trans (by rw [hyy]))
    -- the numerator and denominator of the reduced tangent slope, as elements of `A`
    have hNmem : 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ ∈ A := by
      refine sub_mem (add_mem (add_mem (mul_mem ?_ (pow_mem hx₁ 2))
        (mul_mem (mul_mem ?_ h.a₂_mem) hx₁)) h.a₄_mem) (mul_mem h.a₁_mem hy₁)
      · exact_mod_cast (by norm_num : ((3 : ℕ) : F) ∈ A.toSubring)
      · exact_mod_cast (by norm_num : ((2 : ℕ) : F) ∈ A.toSubring)
    have hDmem : y₁ - W.toAffine.negY x₁ y₁ ∈ A := sub_mem hy₁ (h.negY_mem hx₁ hy₁)
    have hrD : ρ (⟨y₁ - W.toAffine.negY x₁ y₁, hDmem⟩ : A) =
        ρ (⟨y₁, hy₁⟩ : A) - Wred.toAffine.negY (ρ ⟨x₁, hx₁⟩) (ρ ⟨y₁, hy₁⟩) := by
      rw [← h.res_negY hx₁ hy₁, ← map_sub]
      exact res_of_eq _ rfl
    have hDunit : IsUnit (⟨y₁ - W.toAffine.negY x₁ y₁, hDmem⟩ : A) :=
      ValuationSubring.isUnit_of_map_ne_zero ρ (by rw [hrD, sub_ne_zero]; exact hy')
    have hrN : ρ (⟨3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁, hNmem⟩ : A) =
        3 * ρ (⟨x₁, hx₁⟩ : A) ^ 2 + 2 * Wred.a₂ * ρ ⟨x₁, hx₁⟩ + Wred.a₄
          - Wred.a₁ * ρ ⟨y₁, hy₁⟩ := by
      rw [h.a₁_eq, h.a₂_eq, h.a₄_eq]
      have hrw : (⟨3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁, hNmem⟩ : A) =
          (⟨x₁, hx₁⟩ : A) ^ 2 + (⟨x₁, hx₁⟩ : A) ^ 2 + (⟨x₁, hx₁⟩ : A) ^ 2
            + ((⟨W.a₂, h.a₂_mem⟩ : A) * ⟨x₁, hx₁⟩ + (⟨W.a₂, h.a₂_mem⟩ : A) * ⟨x₁, hx₁⟩)
            + ⟨W.a₄, h.a₄_mem⟩ - (⟨W.a₁, h.a₁_mem⟩ : A) * ⟨y₁, hy₁⟩ := by
        apply Subtype.ext
        push_cast
        ring
      rw [hrw]
      simp only [map_add, map_sub, map_mul, map_pow]
      ring
    have hslopeRed : Wred.toAffine.slope (ρ ⟨x₁, hx₁⟩) (ρ ⟨x₂, hx₂⟩)
          (ρ ⟨y₁, hy₁⟩) (ρ ⟨y₂, hy₂⟩) =
        ρ (⟨3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁, hNmem⟩ : A) /
          ρ (⟨y₁ - W.toAffine.negY x₁ y₁, hDmem⟩ : A) := by
      rw [Affine.slope_of_Y_ne hx hy, hrN, hrD]
    by_cases hX : x₁ = x₂
    · -- upstairs the addition is a doubling as well
      have hYne : y₁ ≠ W.toAffine.negY x₂ y₂ := by
        intro hh
        refine hy ?_
        rw [← h.res_negY hx₂ hy₂]
        exact res_of_eq _ hh.symm
      have hslope : W.toAffine.slope x₁ x₂ y₁ y₂ =
          (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.toAffine.negY x₁ y₁) :=
        Affine.slope_of_Y_ne hX hYne
      obtain ⟨L, hL1, hL2⟩ := ValuationSubring.exists_div_eq_of_isUnit ρ
        (⟨3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁, hNmem⟩ : A) hDunit
      refine ⟨(L : F), L.2, by rw [hslope]; exact hL1, ?_⟩
      have hLL : ρ (⟨(L : F), L.2⟩ : A) = ρ L := res_of_eq _ rfl
      rw [hLL, hslopeRed]
      exact hL2
    · -- upstairs a chord, but a `𝔪/𝔪` one: use the factorisation
      have hUmem : y₁ - W.toAffine.negY x₂ y₂ ∈ A := sub_mem hy₁ (h.negY_mem hx₂ hy₂)
      have hGmem : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁ ∈ A :=
        sub_mem (add_mem (add_mem (add_mem (add_mem (pow_mem hx₁ 2) (mul_mem hx₁ hx₂))
          (pow_mem hx₂ 2)) (mul_mem h.a₂_mem (add_mem hx₁ hx₂))) h.a₄_mem)
          (mul_mem h.a₁_mem hy₁)
      have hfact : (y₁ - y₂) * (y₁ - W.toAffine.negY x₂ y₂) =
          (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) := by
        simp only [Affine.negY]
        rw [Affine.equation_iff] at hE₁ hE₂
        linear_combination hE₁ - hE₂
      have hrU : ρ (⟨y₁ - W.toAffine.negY x₂ y₂, hUmem⟩ : A) =
          ρ (⟨y₁, hy₁⟩ : A) - Wred.toAffine.negY (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₂, hy₂⟩) := by
        rw [← h.res_negY hx₂ hy₂, ← map_sub]
        exact res_of_eq _ rfl
      have hUunit : IsUnit (⟨y₁ - W.toAffine.negY x₂ y₂, hUmem⟩ : A) :=
        ValuationSubring.isUnit_of_map_ne_zero ρ (by rw [hrU, sub_ne_zero]; exact hy)
      have hrUD : ρ (⟨y₁ - W.toAffine.negY x₂ y₂, hUmem⟩ : A) =
          ρ (⟨y₁ - W.toAffine.negY x₁ y₁, hDmem⟩ : A) := by
        rw [hrU, hrD, hx, hyy]
      have hrGN : ρ (⟨x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁,
            hGmem⟩ : A) =
          ρ (⟨3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁, hNmem⟩ : A) := by
        have hrwG : (⟨x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁,
              hGmem⟩ : A) =
            (⟨x₁, hx₁⟩ : A) ^ 2 + (⟨x₁, hx₁⟩ : A) * ⟨x₂, hx₂⟩ + (⟨x₂, hx₂⟩ : A) ^ 2
              + (⟨W.a₂, h.a₂_mem⟩ : A) * ((⟨x₁, hx₁⟩ : A) + ⟨x₂, hx₂⟩) + ⟨W.a₄, h.a₄_mem⟩
              - (⟨W.a₁, h.a₁_mem⟩ : A) * ⟨y₁, hy₁⟩ := by
          apply Subtype.ext; push_cast; ring
        have hrwN : (⟨3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁, hNmem⟩ : A) =
            (⟨x₁, hx₁⟩ : A) ^ 2 + (⟨x₁, hx₁⟩ : A) ^ 2 + (⟨x₁, hx₁⟩ : A) ^ 2
              + ((⟨W.a₂, h.a₂_mem⟩ : A) * ⟨x₁, hx₁⟩ + (⟨W.a₂, h.a₂_mem⟩ : A) * ⟨x₁, hx₁⟩)
              + ⟨W.a₄, h.a₄_mem⟩ - (⟨W.a₁, h.a₁_mem⟩ : A) * ⟨y₁, hy₁⟩ := by
          apply Subtype.ext; push_cast; ring
        rw [hrwG, hrwN]
        simp only [map_add, map_sub, map_mul, map_pow]
        rw [hx]
        ring
      have hXne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hX
      have hslope : W.toAffine.slope x₁ x₂ y₁ y₂ =
          (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) /
            (y₁ - W.toAffine.negY x₂ y₂) := by
        rw [Affine.slope_of_X_ne hX]
        rw [div_eq_div_iff hXne
          (ValuationSubring.coe_ne_zero_of_isUnit (b := (⟨_, hUmem⟩ : A)) hUunit)]
        linear_combination hfact
      obtain ⟨L, hL1, hL2⟩ := ValuationSubring.exists_div_eq_of_isUnit ρ
        (⟨x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁, hGmem⟩ : A) hUunit
      refine ⟨(L : F), L.2, by rw [hslope]; exact hL1, ?_⟩
      have hLL : ρ (⟨(L : F), L.2⟩ : A) = ρ L := res_of_eq _ rfl
      rw [hLL, hslopeRed, ← hrGN, ← hrUD]
      exact hL2
  · -- the reduced abscissas differ: the chord denominator is already a unit
    have hX : x₁ ≠ x₂ := fun hh => hx (res_of_eq _ hh.symm)
    have hDmem : x₁ - x₂ ∈ A := sub_mem hx₁ hx₂
    have hrD : ρ (⟨x₁ - x₂, hDmem⟩ : A) = ρ (⟨x₁, hx₁⟩ : A) - ρ ⟨x₂, hx₂⟩ := by
      rw [← map_sub]; exact res_of_eq _ rfl
    have hDunit : IsUnit (⟨x₁ - x₂, hDmem⟩ : A) :=
      ValuationSubring.isUnit_of_map_ne_zero ρ (by rw [hrD, sub_ne_zero]; exact hx)
    have hNmem : y₁ - y₂ ∈ A := sub_mem hy₁ hy₂
    obtain ⟨L, hL1, hL2⟩ := ValuationSubring.exists_div_eq_of_isUnit ρ
      (⟨y₁ - y₂, hNmem⟩ : A) hDunit
    refine ⟨(L : F), L.2, by rw [Affine.slope_of_X_ne hX]; exact hL1, ?_⟩
    have hNres : ρ (⟨y₁ - y₂, hNmem⟩ : A) = ρ (⟨y₁, hy₁⟩ : A) - ρ ⟨y₂, hy₂⟩ := by
      rw [← map_sub]; exact res_of_eq _ rfl
    have hLL : ρ (⟨(L : F), L.2⟩ : A) = ρ L := res_of_eq _ rfl
    rw [Affine.slope_of_X_ne hx, hLL, hL2, hNres, hrD]

/-! ### The tangent numerator at a reduced two-torsion point -/

/-- The tangent numerator of an integral point is integral. -/
theorem tangentNum_mem {x y : F} (hx : x ∈ A) (hy : y ∈ A) :
    3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y ∈ A := by
  have h2A : (2 : F) ∈ A := by
    rw [show (2 : F) = 1 + 1 from by norm_num]
    exact add_mem (one_mem A) (one_mem A)
  have h3A : (3 : F) ∈ A := by
    rw [show (3 : F) = 1 + 1 + 1 from by norm_num]
    exact add_mem (add_mem (one_mem A) (one_mem A)) (one_mem A)
  exact sub_mem (add_mem (add_mem (mul_mem h3A (pow_mem hx 2))
    (mul_mem (mul_mem h2A h.a₂_mem) hx)) h.a₄_mem) (mul_mem h.a₁_mem hy)

/-- The tangent numerator reduces to the tangent numerator of the reduced point. -/
theorem res_tangentNum {x y : F} (hx : x ∈ A) (hy : y ∈ A) :
    ρ (⟨3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y, h.tangentNum_mem hx hy⟩ : A) =
      3 * ρ (⟨x, hx⟩ : A) ^ 2 + 2 * Wred.a₂ * ρ (⟨x, hx⟩ : A) + Wred.a₄
        - Wred.a₁ * ρ (⟨y, hy⟩ : A) := by
  have hrw : (⟨3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y, h.tangentNum_mem hx hy⟩ : A) =
      (⟨x, hx⟩ : A) ^ 2 + (⟨x, hx⟩ : A) ^ 2 + (⟨x, hx⟩ : A) ^ 2
        + ((⟨W.a₂, h.a₂_mem⟩ : A) * ⟨x, hx⟩ + (⟨W.a₂, h.a₂_mem⟩ : A) * ⟨x, hx⟩)
        + ⟨W.a₄, h.a₄_mem⟩ - (⟨W.a₁, h.a₁_mem⟩ : A) * ⟨y, hy⟩ := by
    apply Subtype.ext
    push_cast
    ring
  rw [hrw, h.a₁_eq, h.a₂_eq, h.a₄_eq]
  simp only [map_add, map_sub, map_mul, map_pow]
  ring

/-- **The tangent numerator is a unit at a reduced two-torsion point.** If an integral
point of `W` reduces to a point of `Wred` fixed by `negY` — i.e. a point where the
tangent is vertical — then the OTHER partial derivative is a unit, because the reduced
curve is nonsingular (`Δ ≠ 0`). This is the generic form of `val_tangent_numerator_eq_one`
in `Flat.lean`, with the good-reduction input replaced by `hΔ`. -/
theorem res_tangentNum_ne_zero (hΔ : Wred.Δ ≠ 0) {x y : F} (hx : x ∈ A) (hy : y ∈ A)
    (hE : W.toAffine.Equation x y)
    (hψ : ρ (⟨y, hy⟩ : A) = Wred.toAffine.negY (ρ ⟨x, hx⟩) (ρ ⟨y, hy⟩)) :
    3 * ρ (⟨x, hx⟩ : A) ^ 2 + 2 * Wred.a₂ * ρ (⟨x, hx⟩ : A) + Wred.a₄
      - Wred.a₁ * ρ (⟨y, hy⟩ : A) ≠ 0 := by
  have hr : Wred.toAffine.Equation (ρ (⟨x, hx⟩ : A)) (ρ ⟨y, hy⟩) := h.equation_res hx hy hE
  have hns : Wred.toAffine.Nonsingular (ρ (⟨x, hx⟩ : A)) (ρ ⟨y, hy⟩) :=
    (Wred.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hr
  rw [Affine.nonsingular_iff'] at hns
  have hY : 2 * ρ (⟨y, hy⟩ : A) + Wred.a₁ * ρ (⟨x, hx⟩ : A) + Wred.a₃ = 0 := by
    simp only [Affine.negY] at hψ
    linear_combination hψ
  have hX0 := hns.2.resolve_right (not_not.mpr hY)
  intro hh
  exact hX0 (by linear_combination -hh)

/-! ### The slope through two reduced-opposite integral points -/

/-- **The slope through two reduced-opposite integral points is steep** (the generic
form of the congruent-points half of Silverman *AEC* VII.2.2): if two integral affine
points of `W` reduce to points of `Wred` that are vertically opposite, but are NOT
themselves vertically opposite upstairs, then the chord–tangent slope joining them has
valuation `> 1`. Consequently their sum leaves the integral locus.

Three cases. If the reduced ordinates DIFFER, the abscissae differ upstairs while their
difference lies in the maximal ideal, and the chord slope `(y₁-y₂)/(x₁-x₂)` is a unit
over a nonunit. If the reduced ordinates AGREE, the reduced point is two-torsion, so the
tangent numerator there is a unit (`res_tangentNum_ne_zero`) while the denominator —
either the tangent denominator `y₁ - negY x₁ y₁` (equal abscissae) or the factorized
chord denominator `y₁ - negY x₂ y₂` (distinct abscissae) — lies in the maximal ideal. -/
theorem one_lt_valuation_slope_of_res_opposite (hΔ : Wred.Δ ≠ 0) {x₁ y₁ x₂ y₂ : F}
    (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₂ : y₂ ∈ A)
    (hE₁ : W.toAffine.Equation x₁ y₁) (hE₂ : W.toAffine.Equation x₂ y₂)
    (hrx : ρ (⟨x₁, hx₁⟩ : A) = ρ ⟨x₂, hx₂⟩)
    (hry : ρ (⟨y₁, hy₁⟩ : A) = Wred.toAffine.negY (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₂, hy₂⟩))
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    1 < A.valuation (W.toAffine.slope x₁ x₂ y₁ y₂) := by
  have hxxmem : x₁ - x₂ ∈ A := sub_mem hx₁ hx₂
  have hyymem : y₁ - y₂ ∈ A := sub_mem hy₁ hy₂
  have hresxx : ρ (⟨x₁ - x₂, hxxmem⟩ : A) = ρ (⟨x₁, hx₁⟩ : A) - ρ ⟨x₂, hx₂⟩ := by
    rw [← map_sub]; exact res_of_eq _ rfl
  have hresyy : ρ (⟨y₁ - y₂, hyymem⟩ : A) = ρ (⟨y₁, hy₁⟩ : A) - ρ ⟨y₂, hy₂⟩ := by
    rw [← map_sub]; exact res_of_eq _ rfl
  have hvxx : A.valuation (x₁ - x₂) < 1 :=
    ValuationSubring.valuation_lt_one_of_res_eq_zero ρ hxxmem
      (by rw [hresxx, hrx, sub_self])
  by_cases hyy : ρ (⟨y₁, hy₁⟩ : A) = ρ ⟨y₂, hy₂⟩
  · -- the reduced point is two-torsion
    have h2t : ρ (⟨y₁, hy₁⟩ : A) = Wred.toAffine.negY (ρ ⟨x₁, hx₁⟩) (ρ ⟨y₁, hy₁⟩) := by
      have hh := hry
      rw [← hrx, ← hyy] at hh
      exact hh
    have hNne := h.res_tangentNum_ne_zero hΔ hx₁ hy₁ hE₁ h2t
    by_cases hX : x₁ = x₂
    · -- the two points coincide: the tangent line
      have hy12 : y₁ = y₂ :=
        (Affine.Y_eq_of_X_eq hE₁ hE₂ hX).resolve_right (fun hz => hxy ⟨hX, hz⟩)
      have hYne : y₁ ≠ W.toAffine.negY x₂ y₂ := fun hz => hxy ⟨hX, hz⟩
      have hDmem : y₁ - W.toAffine.negY x₁ y₁ ∈ A := sub_mem hy₁ (h.negY_mem hx₁ hy₁)
      have hresD : ρ (⟨y₁ - W.toAffine.negY x₁ y₁, hDmem⟩ : A) =
          ρ (⟨y₁, hy₁⟩ : A) - Wred.toAffine.negY (ρ ⟨x₁, hx₁⟩) (ρ ⟨y₁, hy₁⟩) := by
        rw [← h.res_negY hx₁ hy₁, ← map_sub]
        exact res_of_eq _ rfl
      have hvD : A.valuation (y₁ - W.toAffine.negY x₁ y₁) < 1 :=
        ValuationSubring.valuation_lt_one_of_res_eq_zero ρ hDmem
          (by rw [hresD, ← h2t, sub_self])
      have hDne : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := by
        rw [sub_ne_zero]
        intro hz
        exact hYne (hz.trans (by rw [hX, hy12]))
      have hslope : W.toAffine.slope x₁ x₂ y₁ y₂ * (y₁ - W.toAffine.negY x₁ y₁)
          = 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ := by
        rw [Affine.slope_of_Y_ne hX hYne]
        exact div_mul_cancel₀ _ hDne
      refine ValuationSubring.one_lt_val_of_val_mul_eq_one A hvD ?_
      rw [hslope]
      exact ValuationSubring.valuation_eq_one_of_res_ne_zero ρ (h.tangentNum_mem hx₁ hy₁)
        (by rw [h.res_tangentNum hx₁ hy₁]; exact hNne)
    · -- distinct abscissae: the factorized chord
      have hXne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hX
      have hUmem : y₁ - W.toAffine.negY x₂ y₂ ∈ A := sub_mem hy₁ (h.negY_mem hx₂ hy₂)
      have hresU : ρ (⟨y₁ - W.toAffine.negY x₂ y₂, hUmem⟩ : A) =
          ρ (⟨y₁, hy₁⟩ : A) - Wred.toAffine.negY (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₂, hy₂⟩) := by
        rw [← h.res_negY hx₂ hy₂, ← map_sub]
        exact res_of_eq _ rfl
      have hvU : A.valuation (y₁ - W.toAffine.negY x₂ y₂) < 1 :=
        ValuationSubring.valuation_lt_one_of_res_eq_zero ρ hUmem
          (by rw [hresU, ← hry, sub_self])
      have hGmem : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁ ∈ A :=
        sub_mem (add_mem (add_mem (add_mem (add_mem (pow_mem hx₁ 2) (mul_mem hx₁ hx₂))
          (pow_mem hx₂ 2)) (mul_mem h.a₂_mem (add_mem hx₁ hx₂))) h.a₄_mem)
          (mul_mem h.a₁_mem hy₁)
      have hfact : (y₁ - y₂) * (y₁ - W.toAffine.negY x₂ y₂) =
          (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁) := by
        simp only [Affine.negY]
        rw [Affine.equation_iff] at hE₁ hE₂
        linear_combination hE₁ - hE₂
      have hslope : W.toAffine.slope x₁ x₂ y₁ y₂ * (y₁ - W.toAffine.negY x₂ y₂)
          = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁ := by
        rw [Affine.slope_of_X_ne hX, div_mul_eq_mul_div, hfact,
          mul_div_cancel_left₀ _ hXne]
      have hresG : ρ (⟨x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁,
            hGmem⟩ : A) =
          3 * ρ (⟨x₁, hx₁⟩ : A) ^ 2 + 2 * Wred.a₂ * ρ (⟨x₁, hx₁⟩ : A) + Wred.a₄
            - Wred.a₁ * ρ (⟨y₁, hy₁⟩ : A) := by
        have hrw : (⟨x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁,
              hGmem⟩ : A) =
            (⟨x₁, hx₁⟩ : A) ^ 2 + (⟨x₁, hx₁⟩ : A) * ⟨x₂, hx₂⟩ + (⟨x₂, hx₂⟩ : A) ^ 2
              + (⟨W.a₂, h.a₂_mem⟩ : A) * ((⟨x₁, hx₁⟩ : A) + ⟨x₂, hx₂⟩) + ⟨W.a₄, h.a₄_mem⟩
              - (⟨W.a₁, h.a₁_mem⟩ : A) * ⟨y₁, hy₁⟩ := by
          apply Subtype.ext
          push_cast
          ring
        rw [hrw, h.a₁_eq, h.a₂_eq, h.a₄_eq]
        simp only [map_add, map_sub, map_mul, map_pow]
        rw [hrx]
        ring
      refine ValuationSubring.one_lt_val_of_val_mul_eq_one A hvU ?_
      rw [hslope]
      exact ValuationSubring.valuation_eq_one_of_res_ne_zero ρ hGmem
        (by rw [hresG]; exact hNne)
  · -- the reduced ordinates differ: a plain chord over a congruence
    have hX : x₁ ≠ x₂ := by
      intro hh
      refine hyy ?_
      have hy12 : y₁ = y₂ :=
        (Affine.Y_eq_of_X_eq hE₁ hE₂ hh).resolve_right (fun hz => hxy ⟨hh, hz⟩)
      exact res_of_eq hy₁ hy12.symm
    have hvyy : A.valuation (y₁ - y₂) = 1 :=
      ValuationSubring.valuation_eq_one_of_res_ne_zero ρ hyymem
        (by rw [hresyy]; exact sub_ne_zero.mpr hyy)
    have hslope : W.toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
      rw [Affine.slope_of_X_ne hX]
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr hX)
    exact ValuationSubring.one_lt_val_of_val_mul_eq_one A hvxx (by rw [hslope]; exact hvyy)

/-- **The sum of two reduced-opposite integral points is non-integral**: it leaves the
integral locus, i.e. lands in the kernel of reduction. -/
theorem addX_notMem_of_res_opposite (hΔ : Wred.Δ ≠ 0) {x₁ y₁ x₂ y₂ : F}
    (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₂ : y₂ ∈ A)
    (hE₁ : W.toAffine.Equation x₁ y₁) (hE₂ : W.toAffine.Equation x₂ y₂)
    (hrx : ρ (⟨x₁, hx₁⟩ : A) = ρ ⟨x₂, hx₂⟩)
    (hry : ρ (⟨y₁, hy₁⟩ : A) = Wred.toAffine.negY (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₂, hy₂⟩))
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ∉ A :=
  WeierstrassCurve.addX_notMem_of_one_lt_val_slope A W h.a₁_mem h.a₂_mem hx₁ hx₂
    (h.one_lt_valuation_slope_of_res_opposite hΔ hx₁ hy₁ hx₂ hy₂ hE₁ hE₂ hrx hry hxy)

/-! ### The kernel of reduction is closed under addition -/

/-- **Two non-integral points add to a non-integral point, coordinate form** (the generic
form of `kernel_add_abscissa_notMem` in `Flat.lean`, obtained from the same two
characteristic-free helpers: the chord–tangent line through two kernel points is deep,
and an affine point on a deep line has non-integral abscissa). -/
theorem addX_notMem_of_notMem {x₁ y₁ x₂ y₂ : F}
    (hE₁ : W.toAffine.Equation x₁ y₁) (hE₂ : W.toAffine.Equation x₂ y₂)
    (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ∉ A := by
  set L := W.toAffine.slope x₁ x₂ y₁ y₂ with hLdef
  obtain ⟨_, hvLc, hvc⟩ := WeierstrassCurve.kernel_slope_facts A W
    h.a₁_mem h.a₂_mem h.a₃_mem h.a₄_mem h.a₆_mem hE₁ hE₂ hx₁ hx₂ hxy hLdef rfl
  have hE₃ : W.toAffine.Equation (W.toAffine.addX x₁ x₂ L)
      (L * W.toAffine.addX x₁ x₂ L + (y₁ - L * x₁)) := by
    have h0 := WeierstrassCurve.Affine.equation_negAdd hE₁ hE₂ hxy
    rw [← hLdef] at h0
    simp only [Affine.negAddY] at h0
    rwa [show L * (W.toAffine.addX x₁ x₂ L - x₁) + y₁
        = L * W.toAffine.addX x₁ x₂ L + (y₁ - L * x₁) from by ring] at h0
  exact WeierstrassCurve.abscissa_notMem_of_line_deep A W
    h.a₁_mem h.a₂_mem h.a₃_mem h.a₄_mem h.a₆_mem hE₃ hvLc hvc

/-- **The kernel of reduction is closed under addition**, point form. -/
theorem not_isIntegralPoint_add {P Q : W.toAffine.Point}
    (hP : ¬ IsIntegralPoint A P) (hQ : ¬ IsIntegralPoint A Q) (hne : P + Q ≠ 0) :
    ¬ IsIntegralPoint A (P + Q) := by
  cases P with
  | zero => exact absurd trivial hP
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => exact absurd trivial hQ
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · exact absurd (Affine.Point.add_of_Y_eq hxy.1 hxy.2) hne
      · rw [Affine.Point.add_some hxy]
        exact h.addX_notMem_of_notMem h₁.1 h₂.1 hP hQ hxy

/-! ## The reduction homomorphism -/

open scoped Classical in
/-- **The reduction map on the points of `W`** (Silverman *AEC* VII.2): an affine point
with integral abscissa goes to the reduction of its coordinates — its ordinate is then
automatically integral, and the reduced coordinates satisfy the reduced Weierstrass
equation, hence are nonsingular because `Wred.Δ ≠ 0` — and every other point, including
the point at infinity, goes to `O`. -/
noncomputable def redFun (hΔ : Wred.Δ ≠ 0) : W.toAffine.Point → Wred.toAffine.Point
  | .zero => 0
  | .some x y hns =>
      if hx : x ∈ A then
        Affine.Point.some
          (ρ ⟨x, hx⟩)
          (ρ ⟨y, W.ordinate_mem_of_abscissa_mem A h.a₁_mem h.a₂_mem h.a₃_mem h.a₄_mem
            h.a₆_mem hns.1 hx⟩)
          ((Wred.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
            (h.equation_res hx (W.ordinate_mem_of_abscissa_mem A h.a₁_mem h.a₂_mem h.a₃_mem
              h.a₄_mem h.a₆_mem hns.1 hx) hns.1))
      else 0

@[simp]
theorem redFun_zero (hΔ : Wred.Δ ≠ 0) : h.redFun hΔ (0 : W.toAffine.Point) = 0 := rfl

theorem redFun_some_of_mem (hΔ : Wred.Δ ≠ 0) {x y : F} (hns : W.toAffine.Nonsingular x y)
    (hx : x ∈ A) (hy : y ∈ A) :
    h.redFun hΔ (Affine.Point.some x y hns) =
      Affine.Point.some (ρ ⟨x, hx⟩) (ρ ⟨y, hy⟩)
        ((Wred.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
          (h.equation_res hx hy hns.1)) := by
  classical
  simp only [redFun, dif_pos hx]

theorem redFun_some_of_notMem (hΔ : Wred.Δ ≠ 0) {x y : F} (hns : W.toAffine.Nonsingular x y)
    (hx : x ∉ A) : h.redFun hΔ (Affine.Point.some x y hns) = 0 := by
  classical
  simp only [redFun, dif_neg hx]

theorem redFun_eq_zero_of_not_isIntegralPoint (hΔ : Wred.Δ ≠ 0) {P : W.toAffine.Point}
    (hP : ¬ IsIntegralPoint A P) : h.redFun hΔ P = 0 := by
  cases P with
  | zero => exact absurd trivial hP
  | some x y hns => exact h.redFun_some_of_notMem hΔ hns hP

/-- **The kernel of reduction is exactly the non-integral locus**: an affine point
reduces to `O` precisely when its abscissa is not integral. -/
theorem redFun_eq_zero_iff (hΔ : Wred.Δ ≠ 0) {x y : F} (hns : W.toAffine.Nonsingular x y) :
    h.redFun hΔ (Affine.Point.some x y hns) = 0 ↔ x ∉ A := by
  by_cases hx : x ∈ A
  · have hy : y ∈ A := W.ordinate_mem_of_abscissa_mem A h.a₁_mem h.a₂_mem h.a₃_mem
      h.a₄_mem h.a₆_mem hns.1 hx
    rw [h.redFun_some_of_mem hΔ hns hx hy]
    exact ⟨fun hz => absurd hz (Affine.Point.some_ne_zero _), fun hz => absurd hx hz⟩
  · exact ⟨fun _ => hx, fun _ => h.redFun_some_of_notMem hΔ hns hx⟩

/-- Reduction commutes with negation. -/
theorem redFun_neg (hΔ : Wred.Δ ≠ 0) (P : W.toAffine.Point) :
    h.redFun hΔ (-P) = - h.redFun hΔ P := by
  cases P with
  | zero => rfl
  | some x y hns =>
    rw [Affine.Point.neg_some]
    by_cases hx : x ∈ A
    · have hy : y ∈ A := W.ordinate_mem_of_abscissa_mem A h.a₁_mem h.a₂_mem h.a₃_mem
        h.a₄_mem h.a₆_mem hns.1 hx
      rw [h.redFun_some_of_mem hΔ _ hx (h.negY_mem hx hy),
        h.redFun_some_of_mem hΔ hns hx hy, Affine.Point.neg_some]
      exact Affine.Point.eq_of_coords_eq rfl (h.res_negY hx hy)
    · rw [h.redFun_some_of_notMem hΔ _ hx, h.redFun_some_of_notMem hΔ hns hx, neg_zero]

/-- **Reduction is additive on integral points** — the coordinate-wise half of Silverman
*AEC* VII.2.1. Either the two reduced points are vertically opposite, in which case the
reduced sum is `O` and the sum upstairs is either `O` as well or has non-integral
abscissa (`addX_notMem_of_res_opposite`); or they are not, in which case the slope of the
chord/tangent upstairs is integral and reduces to the slope downstairs
(`exists_slope_res`), so `addX` and `addY` reduce term by term. -/
theorem redFun_add_of_mem (hΔ : Wred.Δ ≠ 0) {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) :
    h.redFun hΔ (Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂)
      = h.redFun hΔ (Affine.Point.some x₁ y₁ h₁)
        + h.redFun hΔ (Affine.Point.some x₂ y₂ h₂) := by
  have hy₁ : y₁ ∈ A := W.ordinate_mem_of_abscissa_mem A h.a₁_mem h.a₂_mem h.a₃_mem
    h.a₄_mem h.a₆_mem h₁.1 hx₁
  have hy₂ : y₂ ∈ A := W.ordinate_mem_of_abscissa_mem A h.a₁_mem h.a₂_mem h.a₃_mem
    h.a₄_mem h.a₆_mem h₂.1 hx₂
  rw [h.redFun_some_of_mem hΔ h₁ hx₁ hy₁, h.redFun_some_of_mem hΔ h₂ hx₂ hy₂]
  by_cases hred : ρ (⟨x₁, hx₁⟩ : A) = ρ ⟨x₂, hx₂⟩ ∧
      ρ (⟨y₁, hy₁⟩ : A) = Wred.toAffine.negY (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₂, hy₂⟩)
  · rw [Affine.Point.add_of_Y_eq hred.1 hred.2]
    by_cases hup : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hup.1 hup.2]
      exact h.redFun_zero hΔ
    · rw [Affine.Point.add_some hup]
      exact h.redFun_some_of_notMem hΔ _
        (h.addX_notMem_of_res_opposite hΔ hx₁ hy₁ hx₂ hy₂ h₁.1 h₂.1 hred.1 hred.2 hup)
  · have hup : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := by
      rintro ⟨hxx, hyy⟩
      refine hred ⟨res_of_eq hx₁ hxx.symm, ?_⟩
      rw [← h.res_negY hx₂ hy₂]
      exact res_of_eq hy₁ hyy.symm
    rw [Affine.Point.add_some hup]
    obtain ⟨L, hLmem, hLeq, hLres⟩ := h.exists_slope_res hx₁ hy₁ hx₂ hy₂ h₁.1 h₂.1 hred
    have haddXmem : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
      rw [hLeq]; exact h.addX_mem hx₁ hx₂ hLmem
    have haddYmem : W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
      rw [hLeq]; exact h.addY_mem hx₁ hx₂ hy₁ hLmem
    have hXres : ρ (⟨W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂), haddXmem⟩ : A)
        = Wred.toAffine.addX (ρ ⟨x₁, hx₁⟩) (ρ ⟨x₂, hx₂⟩)
            (Wred.toAffine.slope (ρ ⟨x₁, hx₁⟩) (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₁, hy₁⟩) (ρ ⟨y₂, hy₂⟩)) := by
      rw [← hLres, ← h.res_addX hx₁ hx₂ hLmem]
      exact res_of_eq _ (by rw [hLeq])
    have hYres : ρ (⟨W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂), haddYmem⟩ : A)
        = Wred.toAffine.addY (ρ ⟨x₁, hx₁⟩) (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₁, hy₁⟩)
            (Wred.toAffine.slope (ρ ⟨x₁, hx₁⟩) (ρ ⟨x₂, hx₂⟩) (ρ ⟨y₁, hy₁⟩) (ρ ⟨y₂, hy₂⟩)) := by
      rw [← hLres, ← h.res_addY hx₁ hx₂ hy₁ hLmem]
      exact res_of_eq _ (by rw [hLeq])
    rw [h.redFun_some_of_mem hΔ _ haddXmem haddYmem, Affine.Point.add_some hred]
    exact Affine.Point.eq_of_coords_eq hXres hYres

/-- **Reduction is additive on integral points**, point form. -/
theorem redFun_add_of_isIntegralPoint (hΔ : Wred.Δ ≠ 0) {P Q : W.toAffine.Point}
    (hP : IsIntegralPoint A P) (hQ : IsIntegralPoint A Q) :
    h.redFun hΔ (P + Q) = h.redFun hΔ P + h.redFun hΔ Q := by
  cases P with
  | zero =>
    show h.redFun hΔ (0 + Q) = h.redFun hΔ 0 + h.redFun hΔ Q
    rw [zero_add, h.redFun_zero hΔ, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show h.redFun hΔ (Affine.Point.some x₁ y₁ h₁ + 0)
        = h.redFun hΔ (Affine.Point.some x₁ y₁ h₁) + h.redFun hΔ 0
      rw [add_zero, h.redFun_zero hΔ, add_zero]
    | some x₂ y₂ h₂ => exact h.redFun_add_of_mem hΔ h₁ h₂ hP hQ

/-- **Reduction is a group homomorphism** (Silverman *AEC* VII.2.1), the general case.

The two cases where one summand lies in the kernel are reduced to the integral case:
if `P` is integral and `Q` is not, then `R = P + Q` is nonzero (otherwise `Q = -P` would
be integral) and integral (otherwise `R` and `-Q` would be two kernel points whose sum
`P` is integral, contradicting `not_isIntegralPoint_add`); the integral case applied to
`R` and `-P` then reads `0 = red Q = red R - red P`. If both summands lie in the kernel,
so does their sum unless it is `O`, and both sides vanish. -/
theorem redFun_add (hΔ : Wred.Δ ≠ 0) (P Q : W.toAffine.Point) :
    h.redFun hΔ (P + Q) = h.redFun hΔ P + h.redFun hΔ Q := by
  -- the case where `P` is integral and `Q` is not, isolated so it can be used twice
  have key : ∀ P Q : W.toAffine.Point, IsIntegralPoint A P → ¬ IsIntegralPoint A Q →
      h.redFun hΔ (P + Q) = h.redFun hΔ P + h.redFun hΔ Q := by
    intro P Q hP hQ
    rw [h.redFun_eq_zero_of_not_isIntegralPoint hΔ hQ, add_zero]
    by_cases hP0 : P = 0
    · rw [hP0, zero_add, h.redFun_zero hΔ]
      exact h.redFun_eq_zero_of_not_isIntegralPoint hΔ hQ
    have hR0 : P + Q ≠ 0 := by
      intro hz
      have hPQ : P = -Q := add_eq_zero_iff_eq_neg.mp hz
      rw [hPQ] at hP
      exact hQ (isIntegralPoint_neg.mp hP)
    have hRint : IsIntegralPoint A (P + Q) := by
      by_contra hRint
      have hsum : (P + Q) + -Q = P := by abel
      have hne : (P + Q) + -Q ≠ 0 := by rw [hsum]; exact hP0
      have hcontra := h.not_isIntegralPoint_add hRint (isIntegralPoint_neg.not.mpr hQ) hne
      rw [hsum] at hcontra
      exact hcontra hP
    have hsplit := h.redFun_add_of_isIntegralPoint hΔ hRint (isIntegralPoint_neg.mpr hP)
    rw [show P + Q + -P = Q from by abel, h.redFun_neg hΔ,
      h.redFun_eq_zero_of_not_isIntegralPoint hΔ hQ] at hsplit
    refine eq_of_sub_eq_zero ?_
    rw [sub_eq_add_neg]
    exact hsplit.symm
  cases P with
  | zero =>
    show h.redFun hΔ (0 + Q) = h.redFun hΔ 0 + h.redFun hΔ Q
    rw [zero_add, h.redFun_zero hΔ, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show h.redFun hΔ (Affine.Point.some x₁ y₁ h₁ + 0)
        = h.redFun hΔ (Affine.Point.some x₁ y₁ h₁) + h.redFun hΔ 0
      rw [add_zero, h.redFun_zero hΔ, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hx₁ : x₁ ∈ A
      · by_cases hx₂ : x₂ ∈ A
        · exact h.redFun_add_of_mem hΔ h₁ h₂ hx₁ hx₂
        · exact key _ _ hx₁ hx₂
      · by_cases hx₂ : x₂ ∈ A
        · have hcomm := key (Affine.Point.some x₂ y₂ h₂) (Affine.Point.some x₁ y₁ h₁) hx₂ hx₁
          rw [add_comm (Affine.Point.some x₂ y₂ h₂ : W.toAffine.Point)] at hcomm
          exact hcomm.trans (add_comm _ _)
        · rw [h.redFun_some_of_notMem hΔ h₁ hx₁, h.redFun_some_of_notMem hΔ h₂ hx₂, add_zero]
          by_cases hR0 : (Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point)
              + Affine.Point.some x₂ y₂ h₂ = 0
          · rw [hR0]; exact h.redFun_zero hΔ
          · exact h.redFun_eq_zero_of_not_isIntegralPoint hΔ
              (h.not_isIntegralPoint_add hx₁ hx₂ hR0)

/-- **The reduction homomorphism on points** (Silverman *AEC* VII.2.1): the map sending
an affine point with integral abscissa to the reduction of its coordinates, and every
other point to `O`, is a homomorphism of abelian groups `W(F) → Wred(κ)`. -/
noncomputable def redHom (hΔ : Wred.Δ ≠ 0) : W.toAffine.Point →+ Wred.toAffine.Point where
  toFun := h.redFun hΔ
  map_zero' := h.redFun_zero hΔ
  map_add' := h.redFun_add hΔ

@[simp]
theorem redHom_apply (hΔ : Wred.Δ ≠ 0) (P : W.toAffine.Point) :
    h.redHom hΔ P = h.redFun hΔ P := rfl

end IsReductionAlong

end WeierstrassCurve
