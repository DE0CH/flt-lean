/-
WeilPairingDescent.lean — bricks for the nondegeneracy descent of the
Weil pairing (HLEG-NOTES.md §4(B), stages L4-1..9), consumed by the
`hclass` skeleton of `WeilPairing.weilValueProp_all_one_torsion_trivial`
in `WeilPairing.lean`:

* `pointIdeal` / `pointIdeal'`: the (integral / unit fractional) point
  ideal `⟨X − x, Y − y⟩` of an affine point, `⊤` / `1` at `O` — the
  divisor bookkeeping device of the descent, matching mathlib's
  `XYIdeal`-encoding of affine divisors (the place at infinity is
  implicit throughout).

* `exists_span_eq_prod_pointIdeal` (L4-3, PROVEN): **multiset zero-sum
  principality** — any multiset of points summing to `O` in the group
  law has principal point-ideal product, with nonzero generator.  This
  generalizes the pair-peeling extraction inside the μ-theorem to
  arbitrary multisets, replacing the induction by pure class-group
  algebra: the class of the product is the `toClass`-sum of the points
  (`mk_prod_pointIdeal'`), which vanishes by additivity, and an
  integral generator is extracted through
  `ClassGroup.mk_eq_one_of_coe_ideal`.

The descent consumes this at the multiset
`Σ_{κ ∈ E[p]} (T'⊕κ) + (⊖κ)` (for `p•T' = P`), whose generator is the
Silverman III.8.1(c) auxiliary function `g` with
`div g = Σ_{κ ∈ E[p]} (T'⊕κ) − (κ)` (up to the vertical fibers
`∏ XClass x_κ`), i.e. `g = [p]^* f_P`-material for the `g = h∘[p]`
descent.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

namespace WeilPairing

open WeierstrassCurve WeierstrassCurve.Affine
open scoped nonZeroDivisors

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

/-- The integral point ideal of a point of a Weierstrass curve: the
maximal ideal `⟨X − x, Y − y⟩` of the coordinate ring at an affine
point, and `⊤` at `O` (which carries no affine divisor). -/
noncomputable def pointIdeal (W : WeierstrassCurve.Affine F) :
    W.Point → Ideal W.CoordinateRing
  | .zero => ⊤
  | .some x y _ => CoordinateRing.XYIdeal W x (Polynomial.C y)

omit [DecidableEq F] in
@[simp] lemma pointIdeal_some {x y : F} (h : W.Nonsingular x y) :
    pointIdeal W (.some x y h) = CoordinateRing.XYIdeal W x (Polynomial.C y) :=
  rfl

/-- The unit fractional point ideal of a point: mathlib's `XYIdeal'`
at an affine point, `1` at `O`. -/
noncomputable def pointIdeal' (W : WeierstrassCurve.Affine F) :
    W.Point → (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ
  | .zero => 1
  | .some _ _ h => CoordinateRing.XYIdeal' h

omit [DecidableEq F] in
lemma coe_pointIdeal' (P : W.Point) :
    (pointIdeal' W P : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      pointIdeal W P := by
  cases P with
  | zero => simp [pointIdeal', pointIdeal]
  | some x y h => rw [pointIdeal', pointIdeal_some, CoordinateRing.XYIdeal'_eq]

/-- The class of the unit fractional point ideal is the point's
`toClass` image. -/
lemma mk_pointIdeal' (P : W.Point) :
    ClassGroup.mk W.FunctionField (pointIdeal' W P) =
      Additive.toMul (Point.toClass P) := by
  cases P with
  | zero => rw [pointIdeal', map_one]; rfl
  | some x y h => rfl

omit [DecidableEq F] in
/-- The unit fractional point-ideal product coincides with the integral
point-ideal product as a fractional ideal. -/
lemma coe_prod_pointIdeal' (D : Multiset W.Point) :
    (((D.map (pointIdeal' W)).prod :
      (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      (((D.map (pointIdeal W)).prod : Ideal W.CoordinateRing) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
  induction D using Multiset.induction with
  | empty => simp
  | cons P D ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, Units.val_mul, ih, coe_pointIdeal',
      FractionalIdeal.coeIdeal_mul]

/-- The class of a point-ideal product is the `toClass`-sum of the
points. -/
lemma mk_prod_pointIdeal' (D : Multiset W.Point) :
    ClassGroup.mk W.FunctionField (D.map (pointIdeal' W)).prod =
      Additive.toMul (D.map Point.toClass).sum := by
  induction D using Multiset.induction with
  | empty => simp
  | cons P D ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, ih, mk_pointIdeal',
      Multiset.map_cons, Multiset.sum_cons]
    rfl

/-- **Multiset zero-sum principality** (L4-3 of the nondegeneracy
descent, HLEG-NOTES.md §4(B)): a multiset of points of a Weierstrass
curve summing to `O` in the group law has principal point-ideal
product, with a nonzero generator.  The generator is the "Miller
function" of the zero-sum affine divisor `Σ_D (P) − deg·(O)`-ish datum;
for the descent it is applied to `Σ_{κ ∈ E[p]} (T'⊕κ) + (⊖κ)` to
produce the auxiliary function of Silverman III.8.1(c). -/
theorem exists_span_eq_prod_pointIdeal (D : Multiset W.Point)
    (hD : D.sum = 0) :
    ∃ a : W.CoordinateRing, a ≠ 0 ∧
      Ideal.span {a} = (D.map (pointIdeal W)).prod := by
  classical
  have hmk : ClassGroup.mk W.FunctionField (D.map (pointIdeal' W)).prod = 1 := by
    rw [mk_prod_pointIdeal', ← map_multiset_sum, hD, map_zero]
    rfl
  obtain ⟨a, ha0, haspan⟩ :=
    (ClassGroup.mk_eq_one_of_coe_ideal (coe_prod_pointIdeal' D)).mp hmk
  exact ⟨a, ha0, haspan.symm⟩

/-!
## The τ/[p]-substrate (L4-4) and the L4-8/9 stage decomposition

The descent core `hres` of `weilValueProp_all_one_torsion_trivial`
(WeilPairing.lean) factors through the **translation character** of the
Miller generator: base-change the curve to its own function field
`K = Frac F[W]` (`curveK`), where it carries the **tautological point**
`(tautX, tautY)` (the generic point); for a torsion point `κ`, the
affine coordinates of `κ ⊕ taut` give the evaluation map
`τ_κ^* : F[W] →+* K` (`pointEval`), realizing "compose with translation
by `κ`".  The auxiliary function `g = a / ∏ XClass x_κ` of Silverman
III.8.1(c) then has translation character `χ(κ) = τ_κ^*(g)/g`, a
constant `p`-th root of unity (`exists_translationChar`, L4-8, via the
pullback factorization L4-7); if `χ ≡ 1` the function descends through
the fixed field of the translation action (`Fix E[p] = [p]^*K`,
L4-5/6) to `g = h∘[p]` with `div h = (P) − (O)`, so the class of `P`
vanishes (`toClass_eq_zero_of_translationChar_trivial`, L4-9 first
branch).  The proven dichotomy glue
`descent_toClass_eq_zero_or_translationChar` packages the two stages;
the second branch's nontrivial character data is consumed in
WeilPairing.lean by the bridge lemma (Silverman Ex. 3.16(c)) producing
a nontrivial admissible Weil value.
-/

section TautSubstrate

omit [DecidableEq F] in
/-- Equality on the function field of a Weierstrass curve, decided
classically (mathlib's point group law demands `DecidableEq`). -/
noncomputable instance instDecidableEqFunctionField :
    DecidableEq W.FunctionField :=
  Classical.decEq _

/-- The constants embedding `F → K = Frac F[W]` of the function field
of a Weierstrass curve. -/
noncomputable def constHom (W : WeierstrassCurve.Affine F) :
    F →+* W.FunctionField :=
  (algebraMap W.CoordinateRing W.FunctionField).comp
    ((CoordinateRing.mk W).comp
      ((Polynomial.C : Polynomial F →+* Polynomial (Polynomial F)).comp
        (Polynomial.C : F →+* Polynomial F)))

/-- The tautological `x`-coordinate: the image of `X` in the function
field. -/
noncomputable def tautX (W : WeierstrassCurve.Affine F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField
    (CoordinateRing.mk W (Polynomial.C Polynomial.X))

/-- The tautological `y`-coordinate: the image of `Y` in the function
field. -/
noncomputable def tautY (W : WeierstrassCurve.Affine F) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Polynomial.X)

/-- The Weierstrass curve base-changed to its own function field. -/
noncomputable def curveK (W : WeierstrassCurve.Affine F) :
    WeierstrassCurve.Affine W.FunctionField :=
  (W.map (constHom W)).toAffine

omit [DecidableEq F] in
/-- The tautological point satisfies the Weierstrass equation over the
function field. -/
theorem taut_equation (W : WeierstrassCurve.Affine F) :
    (curveK W).Equation (tautX W) (tautY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h : (algebraMap W.CoordinateRing W.FunctionField) (CoordinateRing.mk W
      (Polynomial.X ^ 2 + Polynomial.C (Polynomial.C W.a₁ * Polynomial.X +
        Polynomial.C W.a₃) * Polynomial.X -
      Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2 +
        Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆))) = 0 := by
    show (algebraMap W.CoordinateRing W.FunctionField)
      (CoordinateRing.mk W W.polynomial) = 0
    rw [AdjoinRoot.mk_self, map_zero]
  simp only [map_add, map_sub, map_mul, map_pow] at h
  show tautY W ^ 2 + (curveK W).a₁ * tautX W * tautY W + (curveK W).a₃ * tautY W =
    tautX W ^ 3 + (curveK W).a₂ * tautX W ^ 2 + (curveK W).a₄ * tautX W +
      (curveK W).a₆
  simp only [curveK, WeierstrassCurve.map, constHom, RingHom.coe_comp,
    Function.comp_apply, tautX, tautY] at h ⊢
  linear_combination h

omit [DecidableEq F] in
/-- The base-changed curve inherits a nonzero discriminant. -/
theorem curveK_Δ_ne_zero (W : WeierstrassCurve.Affine F) (hΔ : W.Δ ≠ 0) :
    (curveK W).Δ ≠ 0 := by
  intro hc
  rw [curveK, WeierstrassCurve.map_Δ] at hc
  exact hΔ ((constHom W).injective (hc.trans (map_zero (constHom W)).symm))

omit [DecidableEq F] in
/-- **The tautological point is nonsingular** (for a curve of nonzero
discriminant). -/
theorem taut_nonsingular (W : WeierstrassCurve.Affine F) (hΔ : W.Δ ≠ 0) :
    (curveK W).Nonsingular (tautX W) (tautY W) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (curveK_Δ_ne_zero W hΔ)).mp (taut_equation W)

/-- The tautological point of the curve over its own function field. -/
noncomputable def tautPoint (W : WeierstrassCurve.Affine F) (hΔ : W.Δ ≠ 0) :
    (curveK W).Point :=
  WeierstrassCurve.Affine.Point.some _ _ (taut_nonsingular W hΔ)

/-- The base-change of a rational point to the function field. -/
noncomputable def constPoint (W : WeierstrassCurve.Affine F) :
    W.Point → (curveK W).Point
  | .zero => .zero
  | .some x y h => WeierstrassCurve.Affine.Point.some _ _
      ((W.map_nonsingular (constHom W).injective x y).mpr h)

/-- **Evaluation of coordinate-ring elements at a point with
coordinates in an extension**: the ring homomorphism
`F[W] →+* K'` induced by a `K'`-point of the base-changed curve
(L4-4's evaluation substrate — at `κ ⊕ taut` it realizes composition
with the translation `τ_κ`). -/
noncomputable def pointEval {K' : Type*} [Field K'] (φ : F →+* K')
    {x₀ y₀ : K'} (h : ((W.map φ).toAffine).Equation x₀ y₀) :
    W.CoordinateRing →+* K' :=
  AdjoinRoot.lift ((Polynomial.evalRingHom x₀).comp (Polynomial.mapRingHom φ))
    y₀ (by
      have h' : ((W.map φ).toAffine.polynomial).evalEval x₀ y₀ = 0 := h
      rw [WeierstrassCurve.Affine.map_polynomial] at h'
      rwa [← Polynomial.eval₂_evalRingHom, Polynomial.eval₂_map] at h')

/-- The vertical coordinate function of a point: `X − x` at an affine
point, `1` at `O`. -/
noncomputable def pointXClass (W : WeierstrassCurve.Affine F) :
    W.Point → W.CoordinateRing
  | .zero => 1
  | .some x _ _ => CoordinateRing.XClass W x

/-- The product of the vertical coordinate functions over an
enumeration of points: the denominator turning the Miller generator
`a` of `∏ I_{T'⊕κ}·I_{⊖κ}` into the descent function
`g = a / ∏ (X − x_κ)` with `div g = Σ_κ (T'⊕κ) − (κ)`. -/
noncomputable def enumVertical {ι : Type*} [Fintype ι]
    (W : WeierstrassCurve.Affine F) (val : ι → W.Point) : W.CoordinateRing :=
  (Finset.univ.val.map fun i => pointXClass W (val i)).prod

/-!
### Evaluation and translation substrate for L4-8

The bricks consumed by the proof of `exists_translationChar`:
computation rules for `pointEval` on the generators of the coordinate
ring, the ring-hom extensionality principle they support, the
nonconstancy of the tautological (and generic-translate) `x`-coordinate,
and a `RingHom`-level additive point map (mathlib's `Point.map` is
`AlgHom`-based, which does not fit the constants embedding `constHom`
nor the fraction-field endomorphism extending `τ_κ^*`).
-/

omit [DecidableEq F] in
/-- `pointEval` on the image of a univariate polynomial `r(X)`:
evaluation of `r` at the point's `x`-coordinate. -/
lemma pointEval_ofPoly {K' : Type*} [Field K'] (φ : F →+* K') {x₀ y₀ : K'}
    (h : ((W.map φ).toAffine).Equation x₀ y₀) (r : Polynomial F) :
    pointEval φ h (CoordinateRing.mk W (Polynomial.C r)) =
      (r.map φ).eval x₀ := by
  rw [pointEval, AdjoinRoot.lift_mk, Polynomial.eval₂_C]
  rfl

omit [DecidableEq F] in
/-- `pointEval` fixes the constants: `τ_κ^*` restricted to `F` is `φ`. -/
lemma pointEval_C {K' : Type*} [Field K'] (φ : F →+* K') {x₀ y₀ : K'}
    (h : ((W.map φ).toAffine).Equation x₀ y₀) (d : F) :
    pointEval φ h (CoordinateRing.mk W (Polynomial.C (Polynomial.C d))) =
      φ d := by
  rw [pointEval_ofPoly, Polynomial.map_C, Polynomial.eval_C]

omit [DecidableEq F] in
/-- `pointEval` sends the coordinate function `X` to the point's
`x`-coordinate. -/
lemma pointEval_X {K' : Type*} [Field K'] (φ : F →+* K') {x₀ y₀ : K'}
    (h : ((W.map φ).toAffine).Equation x₀ y₀) :
    pointEval φ h (CoordinateRing.mk W (Polynomial.C Polynomial.X)) = x₀ := by
  rw [pointEval_ofPoly, Polynomial.map_X, Polynomial.eval_X]

omit [DecidableEq F] in
/-- `pointEval` sends the coordinate function `Y` to the point's
`y`-coordinate. -/
lemma pointEval_Y {K' : Type*} [Field K'] (φ : F →+* K') {x₀ y₀ : K'}
    (h : ((W.map φ).toAffine).Equation x₀ y₀) :
    pointEval φ h (CoordinateRing.mk W Polynomial.X) = y₀ :=
  AdjoinRoot.lift_root _

omit [DecidableEq F] in
/-- Ring homomorphisms out of the coordinate ring are determined by
their values on the constants and the two coordinate functions. -/
theorem coordinateRing_ringHom_ext {S : Type*} [CommRing S]
    {φ₁ φ₂ : W.CoordinateRing →+* S}
    (hC : ∀ d : F, φ₁ (CoordinateRing.mk W (Polynomial.C (Polynomial.C d))) =
      φ₂ (CoordinateRing.mk W (Polynomial.C (Polynomial.C d))))
    (hX : φ₁ (CoordinateRing.mk W (Polynomial.C Polynomial.X)) =
      φ₂ (CoordinateRing.mk W (Polynomial.C Polynomial.X)))
    (hY : φ₁ (CoordinateRing.mk W Polynomial.X) =
      φ₂ (CoordinateRing.mk W Polynomial.X)) :
    φ₁ = φ₂ := by
  have hpoly : ∀ r : Polynomial F,
      φ₁ (CoordinateRing.mk W (Polynomial.C r)) =
        φ₂ (CoordinateRing.mk W (Polynomial.C r)) := by
    intro r
    induction r using Polynomial.induction_on with
    | C d => exact hC d
    | add f g hf hg => rw [Polynomial.C_add, map_add, map_add, map_add, hf, hg]
    | monomial n d _ =>
      simp only [map_mul, map_pow]
      rw [hC d, hX]
  refine RingHom.ext fun z => ?_
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  induction f using Polynomial.induction_on with
  | C r => exact hpoly r
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | monomial n r _ =>
    simp only [map_mul, map_pow]
    rw [hpoly r, hY]

omit [DecidableEq F] in
/-- **The tautological `x`-coordinate is not a constant**: its
difference with any constant is the image of the nonzero vertical
class `X − c`. -/
theorem tautX_ne_constHom (c : F) : tautX W ≠ constHom W c := by
  intro hc
  have hXC : CoordinateRing.XClass W c =
      CoordinateRing.mk W (Polynomial.C Polynomial.X) -
        CoordinateRing.mk W (Polynomial.C (Polynomial.C c)) := by
    rw [CoordinateRing.XClass, ← map_sub, ← Polynomial.C_sub]
  have h0 : algebraMap W.CoordinateRing W.FunctionField
      (CoordinateRing.XClass W c) = 0 := by
    rw [hXC, map_sub]
    show tautX W - constHom W c = 0
    rw [hc, sub_self]
  exact CoordinateRing.XClass_ne_zero c
    ((map_eq_zero_iff _
      (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mp h0)

/-- Transport of rational points along an equality of Weierstrass
curves (the group structures correspond definitionally under
`subst`). -/
def castPoint {W₁ W₂ : WeierstrassCurve.Affine F} (h : W₁ = W₂) :
    W₁.Point → W₂.Point :=
  fun P => h ▸ P

omit [DecidableEq F] in
lemma castPoint_zero {W₁ W₂ : WeierstrassCurve.Affine F} (h : W₁ = W₂) :
    castPoint h 0 = 0 := by subst h; rfl

omit [DecidableEq F] in
lemma castPoint_some {W₁ W₂ : WeierstrassCurve.Affine F} (h : W₁ = W₂)
    {x y : F} (hn : W₁.Nonsingular x y) :
    castPoint h (.some x y hn) = .some x y (h ▸ hn) := by subst h; rfl

lemma castPoint_add {W₁ W₂ : WeierstrassCurve.Affine F} (h : W₁ = W₂)
    (P R : W₁.Point) :
    castPoint h (P + R) = castPoint h P + castPoint h R := by subst h; rfl

/-- The map on rational points induced by a field homomorphism — the
`RingHom`-level counterpart of mathlib's `AlgHom`-based `Point.map`,
matching `constPoint` at the constants embedding and applicable to the
fraction-field endomorphisms extending the translation evaluations. -/
noncomputable def pointMap {K' : Type*} [Field K'] (φ : F →+* K') :
    W.Point → (W.map φ).toAffine.Point
  | .zero => .zero
  | .some x y h => .some _ _ ((W.map_nonsingular φ.injective x y).mpr h)

omit [DecidableEq F] in
lemma pointMap_zero {K' : Type*} [Field K'] (φ : F →+* K') :
    pointMap (W := W) φ 0 = 0 :=
  rfl

omit [DecidableEq F] in
lemma pointMap_some {K' : Type*} [Field K'] (φ : F →+* K') {x y : F}
    (h : W.Nonsingular x y) :
    pointMap φ (.some x y h) =
      .some (φ x) (φ y) ((W.map_nonsingular φ.injective x y).mpr h) :=
  rfl

/-- **Additivity of the point map** (`RingHom`-level transplant of
mathlib's `Point.map.map_add'`). -/
theorem pointMap_add {K' : Type*} [Field K'] [DecidableEq K']
    (φ : F →+* K') (P R : W.Point) :
    pointMap φ (P + R) = pointMap φ P + pointMap φ R := by
  rcases P, R with ⟨_ | ⟨x₁, y₁, h₁⟩, _ | ⟨x₂, y₂, h₂⟩⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.left hxy.right, pointMap_zero, pointMap_some,
      pointMap_some,
      Point.add_of_Y_eq (congr_arg φ hxy.left) (by rw [hxy.right, map_negY])]
  · have hxy' : ¬(φ x₁ = φ x₂ ∧
        φ y₁ = (W.map φ).toAffine.negY (φ x₂) (φ y₂)) := fun hc =>
      hxy ⟨φ.injective hc.1, φ.injective (by
        have := hc.2
        rw [map_negY] at this
        exact this)⟩
    rw [Point.add_some hxy, pointMap_some, pointMap_some, pointMap_some,
      Point.add_some hxy']
    simp only [Point.some.injEq]
    exact ⟨by rw [map_slope, map_addX], by rw [map_slope, map_addY]⟩

omit [DecidableEq F] in
/-- `constPoint` is the point map of the constants embedding. -/
lemma constPoint_eq_pointMap (P : W.Point) :
    constPoint W P = pointMap (constHom W) P := by
  cases P <;> rfl

/-- The base change of rational points to the function field, as an
additive group homomorphism. -/
noncomputable def constPointHom (W : WeierstrassCurve.Affine F) :
    W.Point →+ (curveK W).Point where
  toFun := constPoint W
  map_zero' := rfl
  map_add' P R := by
    rw [constPoint_eq_pointMap, constPoint_eq_pointMap, constPoint_eq_pointMap,
      pointMap_add]
    rfl

omit [DecidableEq F] in
/-- **Units of the coordinate ring are the nonzero constants** (the
affine curve is integral with only the place at infinity removed):
generic-field transplant of the μ-proof's `hCunits` extraction
(`coordRing_isUnit_constant` in WeilPairing.lean), via the norm to
`F[X]` having degree zero. -/
theorem coordinateRing_isUnit_eq_const {u : W.CoordinateRing}
    (hu : IsUnit u) :
    ∃ c : F, c ≠ 0 ∧
      u = CoordinateRing.mk W (Polynomial.C (Polynomial.C c)) := by
  obtain ⟨pp, qq, rfl⟩ := CoordinateRing.exists_smul_basis_eq u
  obtain ⟨v, hv⟩ := hu
  have hnu : IsUnit (Algebra.norm (Polynomial F)
      (pp • (1 : W.CoordinateRing) +
        qq • CoordinateRing.mk W Polynomial.X)) := by
    refine isUnit_iff_exists.mpr ⟨Algebra.norm (Polynomial F)
      ((v⁻¹ : W.CoordinateRingˣ) : W.CoordinateRing), ?_, ?_⟩
    · rw [← map_mul,
        show (pp • (1 : W.CoordinateRing) +
            qq • CoordinateRing.mk W Polynomial.X) *
            ((v⁻¹ : W.CoordinateRingˣ) : W.CoordinateRing) =
          ((v * v⁻¹ : W.CoordinateRingˣ) : W.CoordinateRing) from by
            rw [Units.val_mul, hv],
        mul_inv_cancel, Units.val_one, map_one]
    · rw [← map_mul,
        show ((v⁻¹ : W.CoordinateRingˣ) : W.CoordinateRing) *
            (pp • (1 : W.CoordinateRing) +
              qq • CoordinateRing.mk W Polynomial.X) =
          ((v⁻¹ * v : W.CoordinateRingˣ) : W.CoordinateRing) from by
            rw [Units.val_mul, hv],
        inv_mul_cancel, Units.val_one, map_one]
  have hdeg0 : (Algebra.norm (Polynomial F)
      (pp • (1 : W.CoordinateRing) +
        qq • CoordinateRing.mk W Polynomial.X)).degree = 0 :=
    Polynomial.degree_eq_zero_of_isUnit hnu
  rw [CoordinateRing.degree_norm_smul_basis] at hdeg0
  have hqq : qq = 0 := by
    by_contra hqq0
    have h1 : (2 • qq.degree + 3 : WithBot ℕ) ≤ 0 := by
      rw [← hdeg0]
      exact le_max_right _ _
    have h3 : (0 : WithBot ℕ) ≤ qq.degree :=
      Polynomial.zero_le_degree_iff.mpr hqq0
    have h2 : (0 : WithBot ℕ) < 2 • qq.degree + 3 := by
      refine lt_of_lt_of_le (by norm_num : (0 : WithBot ℕ) < 3) ?_
      refine le_add_of_nonneg_left ?_
      rw [two_nsmul]
      exact le_trans h3 (le_add_of_nonneg_left h3)
    exact absurd (le_antisymm h1 (le_of_lt h2)) (ne_of_gt h2)
  have hpp : pp.degree = 0 := by
    rw [hqq] at hdeg0
    simp only [Polynomial.degree_zero] at hdeg0
    have h4 : (2 • pp.degree : WithBot ℕ) = 0 := by
      rw [← hdeg0, max_eq_left]
      rw [show (2 : ℕ) • (⊥ : WithBot ℕ) + 3 = ⊥ from by rfl]
      exact bot_le
    rw [two_nsmul, Nat.WithBot.add_eq_zero_iff] at h4
    exact h4.1
  have hppC : pp = Polynomial.C (pp.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (le_of_eq hpp)
  refine ⟨pp.coeff 0, ?_, ?_⟩
  · intro h0
    have hppz : pp = 0 := by rw [hppC, h0, Polynomial.C_0]
    have hz : (pp • (1 : W.CoordinateRing) +
        qq • CoordinateRing.mk W Polynomial.X) = 0 := by
      rw [hppz, hqq, zero_smul, zero_smul, add_zero]
    exact Units.ne_zero v (hv.trans hz)
  · conv_lhs => rw [hqq, zero_smul, add_zero, hppC]
    rw [Algebra.smul_def, mul_one]
    rfl

/-- **The `x`-coordinate of a generic translate is not a constant**
(L4-4 substrate): were `x(Q ⊕ taut)` a constant, `y(Q ⊕ taut)` would
satisfy a monic quadratic with constant coefficients, hence — the
constants being algebraically closed — the whole translate would be a
constant point, forcing the tautological point to be constant against
`tautX_ne_constHom`. -/
theorem xCoord_ne_constHom [IsAlgClosed F] (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xκ yκ : W.FunctionField} {hκ : (curveK W).Nonsingular xκ yκ}
    (hpt : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ) (c : F) :
    xκ ≠ constHom W c := by
  intro hxc
  subst hxc
  have heq : yκ ^ 2 + constHom W (W.a₁ * c + W.a₃) * yκ -
      constHom W (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) = 0 := by
    have h := ((curveK W).equation_iff (constHom W c) yκ).mp hκ.left
    simp only [curveK, WeierstrassCurve.map] at h
    simp only [map_add, map_mul, map_pow]
    linear_combination h
  obtain ⟨r₁, hr₁⟩ := IsAlgClosed.exists_root
    (p := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * c + W.a₃) * Polynomial.X -
      Polynomial.C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆)) (by
      rw [show (Polynomial.X ^ 2 +
          Polynomial.C (W.a₁ * c + W.a₃) * Polynomial.X -
          Polynomial.C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) :
            Polynomial F) =
          Polynomial.C 1 * Polynomial.X ^ 2 +
            Polynomial.C (W.a₁ * c + W.a₃) * Polynomial.X +
            Polynomial.C (-(c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆)) from by
          rw [Polynomial.C_1, one_mul, Polynomial.C_neg]; ring,
        Polynomial.degree_quadratic one_ne_zero]
      norm_num)
  have hr₁' : r₁ ^ 2 + (W.a₁ * c + W.a₃) * r₁ -
      (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) = 0 := by
    simpa using hr₁
  have hfac : (yκ - constHom W r₁) *
      (yκ - (-constHom W (W.a₁ * c + W.a₃) - constHom W r₁)) = 0 := by
    have himg : constHom W r₁ ^ 2 +
        constHom W (W.a₁ * c + W.a₃) * constHom W r₁ -
        constHom W (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) = 0 := by
      have h2 := congrArg (constHom W) hr₁'
      simpa [map_add, map_sub, map_mul, map_pow] using h2
    linear_combination heq - himg
  have hy : ∃ r : F, yκ = constHom W r := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact ⟨r₁, sub_eq_zero.mp h⟩
    · exact ⟨-(W.a₁ * c + W.a₃) - r₁, by
        rw [map_sub, map_neg]; exact sub_eq_zero.mp h⟩
  obtain ⟨r, rfl⟩ := hy
  have hns : W.Nonsingular c r :=
    (W.map_nonsingular (constHom W).injective c r).mp hκ
  have hR : constPoint W (.some c r hns) =
      WeierstrassCurve.Affine.Point.some (constHom W c) (constHom W r) hκ :=
    rfl
  rw [← hR] at hpt
  have htaut : tautPoint W hΔ = constPoint W (-Q + .some c r hns) := by
    have h1 : tautPoint W hΔ =
        -constPoint W Q + constPoint W (.some c r hns) := by
      rw [← hpt, neg_add_cancel_left]
    have h2 : constPoint W (-Q + .some c r hns) =
        -constPoint W Q + constPoint W (.some c r hns) := by
      rw [show constPoint W = ⇑(constPointHom W) from rfl, map_add, map_neg]
    rw [h1, h2]
  rcases hcase : -Q + WeierstrassCurve.Affine.Point.some c r hns
    with _ | ⟨x', y', h'⟩
  · rw [hcase] at htaut
    exact Point.some_ne_zero (taut_nonsingular W hΔ) htaut
  · rw [hcase] at htaut
    have htaut' : WeierstrassCurve.Affine.Point.some (tautX W) (tautY W)
        (taut_nonsingular W hΔ) =
        WeierstrassCurve.Affine.Point.some (constHom W x') (constHom W y')
          ((W.map_nonsingular (constHom W).injective x' y').mpr h') := htaut
    injection htaut' with hx' hy'
    exact tautX_ne_constHom x' hx'

/-- **Generic-translate transcendence** (L4-4 substrate): evaluation at
the `x`-coordinate of `Q ⊕ taut` kills no nonzero univariate
polynomial — over the algebraically closed constants a root would make
that coordinate a constant, against `xCoord_ne_constHom`. -/
theorem eval_map_ne_zero_of_ne_zero [IsAlgClosed F] (hΔ : W.Δ ≠ 0)
    {Q : W.Point} {xκ yκ : W.FunctionField}
    {hκ : (curveK W).Nonsingular xκ yκ}
    (hpt : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ)
    {q : Polynomial F} (hq : q ≠ 0) :
    (q.map (constHom W)).eval xκ ≠ 0 := by
  intro h0
  set ev : Polynomial F →+* W.FunctionField :=
    (Polynomial.evalRingHom xκ).comp (Polynomial.mapRingHom (constHom W))
    with hev
  have h0' : ev q = 0 := h0
  rw [(IsAlgClosed.splits q).eq_prod_roots, map_mul,
    map_multiset_prod, Multiset.map_map] at h0'
  rcases mul_eq_zero.mp h0' with h1 | h1
  · have h2 : ev (Polynomial.C q.leadingCoeff) =
        constHom W q.leadingCoeff := by
      simp [hev]
    rw [h2] at h1
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
      ((map_eq_zero_iff _ (constHom W).injective).mp h1)
  · obtain ⟨a, _, h2⟩ := Multiset.mem_map.mp
      (Multiset.prod_eq_zero_iff.mp h1)
    have h3 : ev (Polynomial.X - Polynomial.C a) = xκ - constHom W a := by
      simp [hev]
    rw [Function.comp_apply, h3] at h2
    exact xCoord_ne_constHom hΔ hpt a (sub_eq_zero.mp h2)

/-- **Injectivity of evaluation at a generic translate** (L4-4
substrate, the `τ_κ^*`-injectivity feeding both the nonvanishing
conclusions of L4-8 and the extension of `τ_κ^*` to the function
field): a relation `p(xκ) + q(xκ)·yκ = 0` forces the norm
`p² − pq·(a₁X + a₃) − q²·(X³ + a₂X² + a₄X + a₆)` to vanish at `xκ`,
hence to vanish identically, hence `p = q = 0` by the degree
formula. -/
theorem pointEval_injective [IsAlgClosed F] (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xκ yκ : W.FunctionField} {hκ : (curveK W).Nonsingular xκ yκ}
    (hpt : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ) :
    Function.Injective (pointEval (constHom W) hκ.left) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨pp, qq, rfl⟩ := CoordinateRing.exists_smul_basis_eq f
  have h1 : pointEval (constHom W) hκ.left
      (pp • (1 : W.CoordinateRing) + qq • CoordinateRing.mk W Polynomial.X) =
      (pp.map (constHom W)).eval xκ + (qq.map (constHom W)).eval xκ * yκ := by
    rw [CoordinateRing.smul, CoordinateRing.smul, mul_one, map_add, map_mul,
      pointEval_ofPoly, pointEval_ofPoly, pointEval_Y]
  rw [h1] at hf
  have heqc : yκ ^ 2 + constHom W W.a₁ * xκ * yκ + constHom W W.a₃ * yκ =
      xκ ^ 3 + constHom W W.a₂ * xκ ^ 2 + constHom W W.a₄ * xκ +
        constHom W W.a₆ := by
    have h := ((curveK W).equation_iff xκ yκ).mp hκ.left
    simpa only [curveK, WeierstrassCurve.map] using h
  have hnorm0 : ((Algebra.norm (Polynomial F)
      (pp • (1 : W.CoordinateRing) +
        qq • CoordinateRing.mk W Polynomial.X)).map (constHom W)).eval xκ =
      0 := by
    rw [CoordinateRing.norm_smul_basis]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination ((pp.map (constHom W)).eval xκ -
        (qq.map (constHom W)).eval xκ * yκ -
        (qq.map (constHom W)).eval xκ *
          (constHom W W.a₁ * xκ + constHom W W.a₃)) * hf +
      ((qq.map (constHom W)).eval xκ) ^ 2 * heqc
  have hN : Algebra.norm (Polynomial F)
      (pp • (1 : W.CoordinateRing) +
        qq • CoordinateRing.mk W Polynomial.X) = 0 := by
    by_contra hN0
    exact eval_map_ne_zero_of_ne_zero hΔ hpt hN0 hnorm0
  have hdeg := congrArg Polynomial.degree hN
  rw [CoordinateRing.degree_norm_smul_basis, Polynomial.degree_zero,
    max_eq_bot] at hdeg
  have hqq : qq = 0 := by
    rcases WithBot.add_eq_bot.mp hdeg.2 with h3 | h3
    · rw [two_nsmul] at h3
      rcases WithBot.add_eq_bot.mp h3 with h4 | h4 <;>
        exact Polynomial.degree_eq_bot.mp h4
    · exact absurd h3 (by norm_num)
  have hpp : pp = 0 := by
    rw [two_nsmul] at hdeg
    rcases WithBot.add_eq_bot.mp hdeg.1 with h4 | h4 <;>
      exact Polynomial.degree_eq_bot.mp h4
  rw [hpp, hqq, zero_smul, zero_smul, add_zero]

variable {p : ℕ} [Fact p.Prime] [IsAlgClosed F]

/-- **L4-8 (sorry node): the translation character of the Miller
generator.**  Let `val : ι → W.Point` enumerate the `p`-torsion
subgroup, `T'` a `p`-division point of `P`, and `a` a generator of the
point-ideal product of the zero-sum divisor multiset
`Σ_i (T'⊕κᵢ) + (⊖κᵢ)`, so that `g := a / ∏ (X − x_κ)` has divisor
`Σ_κ (T'⊕κ) − (κ) = [p]^*((P) − (O))`.  For a torsion index `i₀` with
`κ₀ ⊕ taut = (xκ, yκ)`, composition with the translation `τ_{κ₀}` is
evaluation at `(xκ, yκ)` (`pointEval`), and the ratio
`χ(κ₀) = τ_{κ₀}^*(g)/g` has divisor
`τ_{−κ₀}(div g) − div g = 0` (the divisor of `g` is invariant under
translation by `E[p]` — reindex the two sums), hence is a nonzero
CONSTANT `c ∈ F` (units of the coordinate ring are constants over an
algebraically closed field); moreover `c^p = 1` by the pullback
factorization `f_P∘[p] = c'·g^p` (L4-7: `g^p` and the `[p]`-pullback
of the generator of `I_P^p·I_{P'}^{-p}`-data span the same ideal, and
`f_P∘[p]` is exactly `τ`-invariant since `[p]∘τ_κ = [p]`).  The
conclusion is stated multiplied out in `K` (no field extension of the
evaluation map needed): `τ(a)·v = c·a·τ(v)` for `v = ∏ (X − x_κ)`,
together with the nonvanishing of `τ(a)` and `τ(v)` (evaluation at the
generic translate `κ₀ ⊕ taut` kills no nonzero coordinate-ring
element).  See HLEG-NOTES.md §4(B), stages L4-4..8. -/
theorem exists_translationChar {ι : Type*} [Fintype ι] {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {P T' : W.Point} (hT : (p : ℤ) • T' = P) (hPtor : (p : ℤ) • P = 0)
    {a : W.CoordinateRing} (ha : a ≠ 0)
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (i₀ : ι) {xκ yκ : W.FunctionField}
    (hκ : (curveK W).Nonsingular xκ yκ)
    (hpt : constPoint W (val i₀) + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ) :
    ∃ c : F, c ^ p = 1 ∧
      pointEval (constHom W) hκ.left a ≠ 0 ∧
      pointEval (constHom W) hκ.left (enumVertical W val) ≠ 0 ∧
      pointEval (constHom W) hκ.left a *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
        constHom W c * algebraMap W.CoordinateRing W.FunctionField a *
          pointEval (constHom W) hκ.left (enumVertical W val) := by
  sorry

/-- **L4-9, first branch (sorry node): trivial translation character
forces a trivial class.**  If the translation character of the Miller
generator is identically `1` — i.e. `g = a/∏(X − x_κ)` satisfies
`τ_{κ}^*(g) = g` for every `p`-torsion `κ` — then `g` lies in the
fixed field of the translation action of `E[p]` on `K`; by the Galois
theory of the finite faithful action (`[K : Fix E[p]] = p²`, L4-5) and
the degree bound `[K : [p]^*K] ≤ p²` (the tautological `x`-coordinate
is a root of `Φ_p − ([p]^*x)·Ψ_p²`, L4-6), `Fix E[p] = [p]^*K`, so
`g = h ∘ [p]` for some `h ∈ K`; comparing divisors,
`div h = (P) − (O)` (the `[p]`-pullback of `div h` is
`div g = Σ_κ (T'⊕κ) − (κ)`, with multiplicity one by separability of
`[p]`, `(p : F) ≠ 0`), so the point ideal of `P` is principal and its
class vanishes.  (For `P = 0` the conclusion is immediate.)  See
HLEG-NOTES.md §4(B), stages L4-5/6/9. -/
theorem toClass_eq_zero_of_translationChar_trivial {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {P T' : W.Point} (hT : (p : ℤ) • T' = P) (hPtor : (p : ℤ) • P = 0)
    {a : W.CoordinateRing} (ha : a ≠ 0)
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    (htriv : ∀ (i₀ : ι) (xκ yκ : W.FunctionField)
      (hκ : (curveK W).Nonsingular xκ yκ),
      constPoint W (val i₀) + tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ →
      pointEval (constHom W) hκ.left a *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
        algebraMap W.CoordinateRing W.FunctionField a *
          pointEval (constHom W) hκ.left (enumVertical W val)) :
    WeierstrassCurve.Affine.Point.toClass P = 0 := by
  sorry

/-- **The L4-9 dichotomy** (proven glue over the two stage nodes): the
Miller generator of the `[p]^*`-divisor multiset either witnesses a
trivial class for `P` (trivial translation character, first branch) or
carries a NONTRIVIAL translation character value `c ≠ 1`, `c^p = 1` at
some torsion index (second branch) — the data consumed by the bridge
lemma (Silverman Ex. 3.16(c)) in WeilPairing.lean to produce a
nontrivial admissible Weil value. -/
theorem descent_toClass_eq_zero_or_translationChar {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {P T' : W.Point} (hT : (p : ℤ) • T' = P) (hPtor : (p : ℤ) • P = 0)
    {a : W.CoordinateRing} (ha : a ≠ 0)
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod) :
    WeierstrassCurve.Affine.Point.toClass P = 0 ∨
    ∃ (i₀ : ι) (xκ yκ : W.FunctionField)
      (hκ : (curveK W).Nonsingular xκ yκ),
      constPoint W (val i₀) + tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ ∧
      ∃ c : F, c ≠ 1 ∧ c ^ p = 1 ∧
        pointEval (constHom W) hκ.left a ≠ 0 ∧
        pointEval (constHom W) hκ.left (enumVertical W val) ≠ 0 ∧
        pointEval (constHom W) hκ.left a *
            algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
          constHom W c * algebraMap W.CoordinateRing W.FunctionField a *
            pointEval (constHom W) hκ.left (enumVertical W val) := by
  classical
  by_cases htriv : ∀ (i₀ : ι) (xκ yκ : W.FunctionField)
      (hκ : (curveK W).Nonsingular xκ yκ),
      constPoint W (val i₀) + tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ →
      pointEval (constHom W) hκ.left a *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
        algebraMap W.CoordinateRing W.FunctionField a *
          pointEval (constHom W) hκ.left (enumVertical W val)
  · exact Or.inl (toClass_eq_zero_of_translationChar_trivial hΔ hp hval_inj
      hval_tor hval_surj hcard hT hPtor ha hspan htriv)
  · push Not at htriv
    obtain ⟨i₀, xκ, yκ, hκ, hpt, hne⟩ := htriv
    obtain ⟨c, hcp, hτa, hτv, heq⟩ := exists_translationChar hΔ hp hval_inj
      hval_tor hval_surj hcard hT hPtor ha hspan i₀ hκ hpt
    exact Or.inr ⟨i₀, xκ, yκ, hκ, hpt, c,
      fun hc1 => hne (by rw [hc1, map_one, one_mul] at heq; exact heq),
      hcp, hτa, hτv, heq⟩

end TautSubstrate

end WeilPairing
