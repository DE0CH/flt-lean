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
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Fermat.FLT.EllipticCurve.TorsionCard

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

omit [DecidableEq F] in
/-- No vertical coordinate function vanishes: `pointXClass` is `1` at
`O` and the nonzero `XClass` at an affine point. -/
lemma pointXClass_ne_zero (W : WeierstrassCurve.Affine F) (P : W.Point) :
    pointXClass W P ≠ 0 := by
  cases P with
  | zero => exact one_ne_zero
  | some x y h => exact CoordinateRing.XClass_ne_zero x

omit [DecidableEq F] in
/-- The vertical enumeration product is nonzero (the coordinate ring
is a domain and no `pointXClass` factor vanishes). -/
lemma enumVertical_ne_zero {ι : Type*} [Fintype ι]
    (W : WeierstrassCurve.Affine F) (val : ι → W.Point) :
    enumVertical W val ≠ 0 := by
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp h0
  exact pointXClass_ne_zero W (val i) hi
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

omit [DecidableEq F] in
/-- The span of a multiset product is the product of the spans. -/
lemma span_singleton_multiset_prod (s : Multiset W.CoordinateRing) :
    Ideal.span {s.prod} = (s.map fun z => Ideal.span {z}).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      ← ih, Ideal.span_singleton_mul_span_singleton]

omit [DecidableEq F] in
/-- **The vertical denominator's divisor**: `∏ (X − x_κ)` spans the
point-ideal product of the multiset `Σ_κ (κ) + (⊖κ)` (mathlib's
`XYIdeal_neg_mul` pointwise, `O`-entries contributing `⊤`). -/
lemma span_enumVertical {ι : Type*} [Fintype ι] (val : ι → W.Point) :
    Ideal.span {enumVertical W val} =
      (((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i).map (pointIdeal W)).prod := by
  rw [enumVertical, span_singleton_multiset_prod, Multiset.map_map,
    Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map,
    ← Multiset.prod_map_mul]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
  show Ideal.span {pointXClass W (val i)} =
    pointIdeal W (val i) * pointIdeal W (-val i)
  cases hvi : val i with
  | zero =>
    show Ideal.span {(1 : W.CoordinateRing)} = (⊤ : Ideal W.CoordinateRing) * ⊤
    simp
  | some x y h =>
    calc Ideal.span {CoordinateRing.XClass W x} = CoordinateRing.XIdeal W x :=
        rfl
      _ = CoordinateRing.XYIdeal W x (Polynomial.C (W.negY x y)) *
          CoordinateRing.XYIdeal W x (Polynomial.C y) :=
        (CoordinateRing.XYIdeal_neg_mul h).symm
      _ = pointIdeal W (.some x y h) * pointIdeal W (-.some x y h) := by
        rw [Point.neg_some, pointIdeal_some, pointIdeal_some, mul_comm]

omit [DecidableEq F] in
/-- The pointwise-coerced unit point-ideal product coincides with the
coerced integral point-ideal product. -/
lemma prod_coe_pointIdeal' (D : Multiset W.Point) :
    (D.map fun R => (pointIdeal' W R :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod =
      (((D.map (pointIdeal W)).prod : Ideal W.CoordinateRing) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
  induction D using Multiset.induction with
  | empty => simp
  | cons P D ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, ih, coe_pointIdeal', FractionalIdeal.coeIdeal_mul]

omit [DecidableEq F] in
/-- A principal point-ideal product, coerced pointwise to fractional
ideals, is the span of its generator's image. -/
lemma prod_coe_pointIdeal'_eq_spanSingleton {z : W.CoordinateRing}
    {D : Multiset W.Point}
    (hsp : Ideal.span {z} = (D.map (pointIdeal W)).prod) :
    (D.map fun R => (pointIdeal' W R :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField z) := by
  rw [prod_coe_pointIdeal', ← hsp, FractionalIdeal.coeIdeal_span_singleton]

/-- Reindexing a universe multiset map along a self-equivalence. -/
lemma map_univ_comp_equiv {ι' β : Type*} [Fintype ι'] (e : ι' ≃ ι')
    (g : ι' → β) :
    Finset.univ.val.map (fun i => g (e i)) = Finset.univ.val.map g := by
  rw [show (fun i => g (e i)) = g ∘ ⇑e from rfl, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

omit [DecidableEq F] in
/-- Congruence for affine points from coordinate equalities (the
nonsingularity proof transports). -/
lemma point_some_congr {W' : WeierstrassCurve.Affine F} {x₁ y₁ x₂ y₂ : F}
    {h₁ : W'.Nonsingular x₁ y₁} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ =
      WeierstrassCurve.Affine.Point.some x₂ y₂ (hx ▸ hy ▸ h₁) := by
  subst hx
  subst hy
  rfl

/-!
### The endomorphism action on points of the base-changed curve

A field endomorphism `σ` of `K = Frac F[W]` fixing the constants fixes
the coefficients of `curveK`, hence acts on its points directly (no
curve cast, unlike the generic `pointMap` whose target is the mapped
curve): the substrate for iterating the translation evaluation. -/

section EndoMap

variable {σ : W.FunctionField →+* W.FunctionField}

omit [DecidableEq F] in
/-- Nonsingularity transports along a coefficient-fixing endomorphism. -/
theorem endo_nonsingular (hcv : (curveK W).map σ = W.map (constHom W))
    {x y : W.FunctionField} (h : (curveK W).Nonsingular x y) :
    (curveK W).Nonsingular (σ x) (σ y) := by
  have h1 := ((curveK W).map_nonsingular σ.injective x y).mpr h
  rw [hcv] at h1
  exact h1

/-- The action of a coefficient-fixing endomorphism of the function
field on the points of the base-changed curve. -/
noncomputable def endoMap (hcv : (curveK W).map σ = W.map (constHom W)) :
    (curveK W).Point → (curveK W).Point
  | .zero => .zero
  | .some _ _ h => .some _ _ (endo_nonsingular hcv h)

omit [DecidableEq F] in
lemma endoMap_some (hcv : (curveK W).map σ = W.map (constHom W))
    {x y : W.FunctionField} (h : (curveK W).Nonsingular x y) :
    endoMap hcv (.some x y h) = .some (σ x) (σ y) (endo_nonsingular hcv h) :=
  rfl

omit [DecidableEq F] in
lemma endo_negY (hcv : (curveK W).map σ = W.map (constHom W))
    (x y : W.FunctionField) :
    (curveK W).negY (σ x) (σ y) = σ ((curveK W).negY x y) := by
  have h1 : ((curveK W).map σ).toAffine.negY (σ x) (σ y) =
      σ ((curveK W).negY x y) := by rw [map_negY]
  rw [hcv] at h1
  exact h1

omit [DecidableEq F] in
lemma endo_addX (hcv : (curveK W).map σ = W.map (constHom W))
    (x₁ x₂ ℓ : W.FunctionField) :
    (curveK W).addX (σ x₁) (σ x₂) (σ ℓ) = σ ((curveK W).addX x₁ x₂ ℓ) := by
  have h1 : ((curveK W).map σ).toAffine.addX (σ x₁) (σ x₂) (σ ℓ) =
      σ ((curveK W).addX x₁ x₂ ℓ) := by rw [map_addX]
  rw [hcv] at h1
  exact h1

omit [DecidableEq F] in
lemma endo_addY (hcv : (curveK W).map σ = W.map (constHom W))
    (x₁ x₂ y₁ ℓ : W.FunctionField) :
    (curveK W).addY (σ x₁) (σ x₂) (σ y₁) (σ ℓ) =
      σ ((curveK W).addY x₁ x₂ y₁ ℓ) := by
  have h1 : ((curveK W).map σ).toAffine.addY (σ x₁) (σ x₂) (σ y₁) (σ ℓ) =
      σ ((curveK W).addY x₁ x₂ y₁ ℓ) := by rw [map_addY]
  rw [hcv] at h1
  exact h1

omit [DecidableEq F] in
lemma endo_slope (hcv : (curveK W).map σ = W.map (constHom W))
    (x₁ x₂ y₁ y₂ : W.FunctionField) :
    (curveK W).slope (σ x₁) (σ x₂) (σ y₁) (σ y₂) =
      σ ((curveK W).slope x₁ x₂ y₁ y₂) := by
  have h1 : ((curveK W).map σ).toAffine.slope (σ x₁) (σ x₂) (σ y₁) (σ y₂) =
      σ ((curveK W).slope x₁ x₂ y₁ y₂) := by rw [map_slope]
  rw [hcv] at h1
  exact h1

omit [DecidableEq F] in
/-- **Additivity of the endomorphism action** (transplant of the
`pointMap_add` argument staying on the base-changed curve). -/
theorem endoMap_add (hcv : (curveK W).map σ = W.map (constHom W))
    (P R : (curveK W).Point) :
    endoMap hcv (P + R) = endoMap hcv P + endoMap hcv R := by
  rcases P, R with ⟨_ | ⟨x₁, y₁, h₁⟩, _ | ⟨x₂, y₂, h₂⟩⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curveK W).negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.left hxy.right,
      show endoMap hcv 0 = 0 from rfl, endoMap_some, endoMap_some,
      Point.add_of_Y_eq (congr_arg σ hxy.left)
        (by rw [hxy.right, endo_negY hcv])]
  · have hxy' : ¬(σ x₁ = σ x₂ ∧
        σ y₁ = (curveK W).negY (σ x₂) (σ y₂)) := fun hc =>
      hxy ⟨σ.injective hc.1, σ.injective (by
        have h3 := hc.2
        rw [endo_negY hcv] at h3
        exact h3)⟩
    rw [Point.add_some hxy, endoMap_some, endoMap_some, endoMap_some,
      Point.add_some hxy']
    simp only [Point.some.injEq]
    exact ⟨by rw [endo_slope hcv, endo_addX hcv],
      by rw [endo_slope hcv, endo_addY hcv]⟩

end EndoMap

/-!
### The L4-8 transport bricks: verticals, lines, and their numerators

`spanSingleton_pointEval_translate` is proven by a Miller-style strong
induction on the divisor multiset: mathlib's group-law ideal
identities (`XYIdeal_neg_mul`, `XYIdeal_mul_XYIdeal`) peel two points
off the divisor at the cost of one vertical class `X − x` or one line
class `Y − (λ(X − x₁) + y₁)`, and the transported spans of these
explicit generators are the two *bricks*
(`spanSingleton_pointEval_XClass` / `spanSingleton_pointEval_YClass`).
Each brick reduces, by the explicit chord formula for `Q ⊕ taut` (the
generic slope `(q₂ − Y)/(q₁ − X)` never degenerates: `tautX` is not a
constant), to a τ-free integral divisor computation for an explicit
*numerator* element of the coordinate ring — the leaves
`span_vertNumerator` / `span_lineNumerator`.
-/

/-- The coordinate function `X` as an element of the coordinate ring. -/
noncomputable def coordX (W : WeierstrassCurve.Affine F) : W.CoordinateRing :=
  CoordinateRing.mk W (Polynomial.C Polynomial.X)

/-- The coordinate function `Y` as an element of the coordinate ring. -/
noncomputable def coordY (W : WeierstrassCurve.Affine F) : W.CoordinateRing :=
  CoordinateRing.mk W Polynomial.X

/-- The constant `d` as an element of the coordinate ring. -/
noncomputable def coordC (W : WeierstrassCurve.Affine F) (d : F) :
    W.CoordinateRing :=
  CoordinateRing.mk W (Polynomial.C (Polynomial.C d))

omit [DecidableEq F] in
@[simp] lemma algebraMap_coordX :
    algebraMap W.CoordinateRing W.FunctionField (coordX W) = tautX W := rfl

omit [DecidableEq F] in
@[simp] lemma algebraMap_coordY :
    algebraMap W.CoordinateRing W.FunctionField (coordY W) = tautY W := rfl

omit [DecidableEq F] in
@[simp] lemma algebraMap_coordC (d : F) :
    algebraMap W.CoordinateRing W.FunctionField (coordC W d) =
      constHom W d := rfl

omit [DecidableEq F] in
/-- The vertical class `X − x` in terms of the coordinate atoms. -/
lemma XClass_eq (x : F) :
    CoordinateRing.XClass W x = coordX W - coordC W x := by
  rw [coordX, coordC, ← map_sub, ← Polynomial.C_sub]
  rfl

omit [DecidableEq F] in
/-- The line class `Y − (ℓ(X − x₁) + y₁)` in terms of the coordinate
atoms. -/
lemma YClass_line_eq (x₁ y₁ ℓ : F) :
    CoordinateRing.YClass W (linePolynomial x₁ y₁ ℓ) =
      coordY W - (coordC W ℓ * (coordX W - coordC W x₁) + coordC W y₁) := by
  simp only [CoordinateRing.YClass, WeierstrassCurve.Affine.linePolynomial,
    coordX, coordY, coordC, ← map_sub, ← map_add, ← map_mul]

/-- The numerator of the translated vertical `τ_Q^*(X − x)`: the
explicit conic
`(q₂ − Y)² + a₁(q₂ − Y)(q₁ − X) − (a₂ + q₁ + x + X)(q₁ − X)²`,
equal to `(x(Q ⊕ taut) − x) · (tautX − q₁)²` in the function field
(clearing the square of the chord denominator), with affine divisor
`2(Q) + (P ⊖ Q) + (⊖P ⊖ Q)` for `P = (x, ·)`, `Q = (q₁, q₂)`. -/
noncomputable def vertNumerator (W : WeierstrassCurve.Affine F)
    (q₁ q₂ x : F) : W.CoordinateRing :=
  (coordC W q₂ - coordY W) ^ 2 +
    coordC W W.a₁ * (coordC W q₂ - coordY W) * (coordC W q₁ - coordX W) -
    (coordC W W.a₂ + coordC W q₁ + coordC W x + coordX W) *
      (coordC W q₁ - coordX W) ^ 2

/-- The numerator of the translated line
`τ_Q^*(Y − (ℓ(X − x₁) + y₁))`: the explicit cubic-type element equal to
`(y(Q ⊕ taut) − (ℓ·(x(Q ⊕ taut) − x₁) + y₁)) · (tautX − q₁)³` in the
function field (clearing the cube of the chord denominator), with
affine divisor `3(Q) + (P ⊖ Q) + (R ⊖ Q) + (⊖(P ⊕ R) ⊖ Q)` for
`P = (x₁, y₁)`, a second point `R` and the slope `ℓ` of the chord
`P R`.  Written via the abbreviation
`A := (Y − q₂)² + a₁(Y − q₂)(X − q₁) − (a₂ + q₁ + X)(X − q₁)²`
(the cleared `addX`), following the chord evaluation of the group
law. -/
noncomputable def lineNumerator (W : WeierstrassCurve.Affine F)
    (q₁ q₂ x₁ y₁ ℓ : F) : W.CoordinateRing :=
  -((coordY W - coordC W q₂) *
      ((coordY W - coordC W q₂) ^ 2 +
        coordC W W.a₁ * (coordY W - coordC W q₂) *
          (coordX W - coordC W q₁) -
        (coordC W W.a₂ + coordC W q₁ + coordX W) *
          (coordX W - coordC W q₁) ^ 2 -
        coordC W q₁ * (coordX W - coordC W q₁) ^ 2) +
      coordC W q₂ * (coordX W - coordC W q₁) ^ 3) -
    coordC W W.a₁ *
      ((coordY W - coordC W q₂) ^ 2 +
        coordC W W.a₁ * (coordY W - coordC W q₂) *
          (coordX W - coordC W q₁) -
        (coordC W W.a₂ + coordC W q₁ + coordX W) *
          (coordX W - coordC W q₁) ^ 2) *
      (coordX W - coordC W q₁) -
    coordC W W.a₃ * (coordX W - coordC W q₁) ^ 3 -
    coordC W ℓ *
      ((coordY W - coordC W q₂) ^ 2 +
        coordC W W.a₁ * (coordY W - coordC W q₂) *
          (coordX W - coordC W q₁) -
        (coordC W W.a₂ + coordC W q₁ + coordX W) *
          (coordX W - coordC W q₁) ^ 2 -
        coordC W x₁ * (coordX W - coordC W q₁) ^ 2) *
      (coordX W - coordC W q₁) -
    coordC W y₁ * (coordX W - coordC W q₁) ^ 3

/-- The **conjugate line numerator**: the same cleared line value taken
at the *hyperelliptic conjugate* `⊖Q ⊖ taut` of `Q ⊕ taut` instead of at
`Q ⊕ taut`, i.e. equal to
`(y(⊖Q ⊖ taut) − (ℓ·(x(Q ⊕ taut) − x₁) + y₁)) · (tautX − q₁)³`
in the function field (note `x(⊖Q ⊖ taut) = x(Q ⊕ taut)`).  Writing
`A := (Y − q₂)² + a₁(Y − q₂)(X − q₁) − (a₂ + q₁ + X)(X − q₁)²` for the
cleared `addX` and `T := X − q₁`, the two `Y`-values of the translate
have cleared forms
`y(Q ⊕ taut)·T³ = −(Y − q₂)(A − q₁T²) − q₂T³ − a₁AT − a₃T³` (this is the
first half of `lineNumerator`) and
`y(⊖Q ⊖ taut)·T³ = (Y − q₂)(A − q₁T²) + q₂T³` (used here), their sum
being `−a₁AT − a₃T³ = (−a₁x(Q ⊕ taut) − a₃)T³` as it must be.

Its affine divisor is the mirror image of `lineNumerator`'s:
`3(Q) + (⊖P ⊖ Q) + (⊖R ⊖ Q) + ((P ⊕ R) ⊖ Q)`.  It is introduced solely
so that the product `lineNumerator · lineNumeratorNeg` collapses, by the
`addPolynomial` factorization, to the product of the three vertical
numerators (`lineNumerator_mul_lineNumeratorNeg`) — which turns the
divisor identity for the line into a *cancellation* against the already
available `span_vertNumerator`, with no colength or valuation input. -/
noncomputable def lineNumeratorNeg (W : WeierstrassCurve.Affine F)
    (q₁ q₂ x₁ y₁ ℓ : F) : W.CoordinateRing :=
  (coordY W - coordC W q₂) *
      ((coordY W - coordC W q₂) ^ 2 +
        coordC W W.a₁ * (coordY W - coordC W q₂) *
          (coordX W - coordC W q₁) -
        (coordC W W.a₂ + coordC W q₁ + coordX W) *
          (coordX W - coordC W q₁) ^ 2 -
        coordC W q₁ * (coordX W - coordC W q₁) ^ 2) +
    coordC W q₂ * (coordX W - coordC W q₁) ^ 3 -
    coordC W ℓ *
      ((coordY W - coordC W q₂) ^ 2 +
        coordC W W.a₁ * (coordY W - coordC W q₂) *
          (coordX W - coordC W q₁) -
        (coordC W W.a₂ + coordC W q₁ + coordX W) *
          (coordX W - coordC W q₁) ^ 2 -
        coordC W x₁ * (coordX W - coordC W q₁) ^ 2) *
      (coordX W - coordC W q₁) -
    coordC W y₁ * (coordX W - coordC W q₁) ^ 3

omit [DecidableEq F] in
/-- A nonzero element of the function field spans an invertible
fractional ideal. -/
lemma isUnit_spanSingleton_of_ne_zero {z : W.FunctionField} (hz : z ≠ 0) :
    IsUnit (FractionalIdeal.spanSingleton W.CoordinateRing⁰ z) :=
  isUnit_iff_exists.mpr
    ⟨FractionalIdeal.spanSingleton W.CoordinateRing⁰ z⁻¹,
      by rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
        mul_inv_cancel₀ hz, FractionalIdeal.spanSingleton_one],
      by rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
        inv_mul_cancel₀ hz, FractionalIdeal.spanSingleton_one]⟩

omit [DecidableEq F] in
/-- Peeling a principal factor off a principal ideal: if
`⟨b⟩ = ⟨v⟩ · J` with `v ≠ 0` then `b = v · b'` with `⟨b'⟩ = J`. -/
lemma exists_span_factor {v b : W.CoordinateRing} (hv : v ≠ 0)
    {J : Ideal W.CoordinateRing}
    (h : Ideal.span {b} = Ideal.span {v} * J) :
    ∃ b', b = v * b' ∧ Ideal.span {b'} = J := by
  obtain ⟨b', hb'J, hvb'⟩ := Ideal.mem_span_singleton_mul.mp
    (h ▸ Ideal.mem_span_singleton_self b)
  refine ⟨b', hvb'.symm, ?_⟩
  rw [← Ideal.span_singleton_mul_right_inj hv, ← h, ← hvb',
    Ideal.span_singleton_mul_span_singleton]

omit [DecidableEq F] in
/-- The constants embedding into the coordinate ring is multiplicative. -/
lemma coordC_mul (c d : F) : coordC W (c * d) = coordC W c * coordC W d := by
  rw [coordC, coordC, coordC, ← map_mul, ← Polynomial.C_mul, ← Polynomial.C_mul]

omit [DecidableEq F] in
/-- The constants embedding into the coordinate ring is unital. -/
lemma coordC_one : coordC W (1 : F) = 1 := by
  rw [coordC, Polynomial.C_1, Polynomial.C_1, map_one]

omit [DecidableEq F] in
/-- A nonzero constant is a unit of the coordinate ring, so it does not
change the ideal it spans. -/
lemma isUnit_coordC {c : F} (hc : c ≠ 0) : IsUnit (coordC W c) :=
  isUnit_iff_exists.mpr ⟨coordC W c⁻¹,
    by rw [← coordC_mul, mul_inv_cancel₀ hc, coordC_one],
    by rw [← coordC_mul, inv_mul_cancel₀ hc, coordC_one]⟩

/-- **The integral span of a line**: the line through two affine points
`P`, `R` (not opposite) spans `I_P · I_R · I_{⊖(P⊕R)}` — mathlib's
`XYIdeal_mul_XYIdeal` combined with `XYIdeal_neg_mul` at the sum,
cancelling the invertible `I_{P⊕R}` in the fractional-ideal monoid and
descending along `coeIdeal_inj`.  (The fractional-ideal form of the same
identity is `coe_YIdeal_line` below, which the L4-8 line brick uses; this
integral form is what the numerator leaves need.) -/
lemma YIdeal_eq_prod_pointIdeal {x₁ y₁ x₂ y₂ : F} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    CoordinateRing.YIdeal W (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) =
      pointIdeal W (.some x₁ y₁ h₁) * (pointIdeal W (.some x₂ y₂ h₂) *
        pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂))) := by
  have key : ((CoordinateRing.YIdeal W
        (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) : Ideal W.CoordinateRing) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      (pointIdeal' W (.some x₁ y₁ h₁) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
        ((pointIdeal' W (.some x₂ y₂ h₂) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
          (pointIdeal' W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂)) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) := by
    have hadd := Point.add_some (h₁ := h₁) (h₂ := h₂) hxy
    have hMul := CoordinateRing.XYIdeal_mul_XYIdeal (W := W) h₁.left h₂.left hxy
    have hu : IsUnit ((pointIdeal' W (WeierstrassCurve.Affine.Point.some _ _
          (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy)) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) :=
      (pointIdeal' W _).isUnit
    apply hu.mul_left_cancel
    rw [show (-(WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) : W.Point) =
        WeierstrassCurve.Affine.Point.some
          (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
          (W.negY (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
            (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)))
          ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr
            (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy)) from by
        rw [hadd, Point.neg_some],
      coe_pointIdeal', coe_pointIdeal', coe_pointIdeal', coe_pointIdeal',
      pointIdeal_some, pointIdeal_some, pointIdeal_some, pointIdeal_some,
      ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
      ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_inj, mul_comm, ← hMul,
      ← CoordinateRing.XYIdeal_neg_mul
        (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy)]
    ring
  refine (FractionalIdeal.coeIdeal_inj (R := W.CoordinateRing)
    (K := W.FunctionField)).mp ?_
  rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, ← coe_pointIdeal',
    ← coe_pointIdeal', ← coe_pointIdeal']
  exact key

/-- **The cleared chord identity for the vertical numerator** (the
generic case `q₁ ≠ x`): multiplying `vertNumerator` by the vertical
`X − x` turns it into the product of the two chords `ℓ(Q, P)` and
`ℓ(Q, ⊖P)`, up to the nonzero constant `q₁ − x`.  Divisor check:
`[2(Q) + (P⊖Q) + (⊖P⊖Q)] + [(P) + (⊖P)] =
[(Q) + (P) + (⊖P⊖Q)] + [(Q) + (⊖P) + (P⊖Q)]`.  The identity is a ring
identity in `F[W]`, verified in the function field (where `algebraMap`
is injective) from the Weierstrass equation at the tautological point,
at `Q` and at `P`, together with the two cleared slope relations. -/
lemma vertNumerator_mul_XClass {q₁ q₂ x y : F} (hq : W.Equation q₁ q₂)
    (hP : W.Equation x y) (hx : q₁ ≠ x) :
    vertNumerator W q₁ q₂ x * CoordinateRing.XClass W x =
      coordC W (q₁ - x) *
        (CoordinateRing.YClass W (linePolynomial q₁ q₂ (W.slope q₁ x q₂ y)) *
          CoordinateRing.YClass W
            (linePolynomial q₁ q₂ (W.slope q₁ x q₂ (W.negY x y)))) := by
  have hd : q₁ - x ≠ 0 := sub_ne_zero.mpr hx
  have hinj : Function.Injective (algebraMap W.CoordinateRing W.FunctionField) :=
    IsFractionRing.injective W.CoordinateRing W.FunctionField
  have hl₁ : (q₁ - x) * W.slope q₁ x q₂ y = q₂ - y := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]; field_simp [hd]
  have hl₂ : (q₁ - x) * W.slope q₁ x q₂ (W.negY x y) =
      q₂ + y + W.a₁ * x + W.a₃ := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, WeierstrassCurve.Affine.negY]
    field_simp [hd]
    ring
  have hl₁K := congrArg (constHom W) hl₁
  have hl₂K := congrArg (constHom W) hl₂
  have hQK := congrArg (constHom W) ((WeierstrassCurve.Affine.equation_iff ..).mp hq)
  have hPK := congrArg (constHom W) ((WeierstrassCurve.Affine.equation_iff ..).mp hP)
  simp only [map_add, map_mul, map_sub, map_pow] at hl₁K hl₂K hQK hPK
  have hT : tautY W ^ 2 + constHom W W.a₁ * tautX W * tautY W +
      constHom W W.a₃ * tautY W =
      tautX W ^ 3 + constHom W W.a₂ * tautX W ^ 2 + constHom W W.a₄ * tautX W +
        constHom W W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff ..).mp (taut_equation W)
  have he : constHom W q₁ - constHom W x ≠ 0 :=
    sub_ne_zero.mpr fun hc => hx ((constHom W).injective hc)
  apply hinj
  simp only [vertNumerator, XClass_eq, YClass_line_eq, map_add, map_sub, map_mul,
    map_pow, algebraMap_coordX, algebraMap_coordY, algebraMap_coordC]
  refine mul_left_cancel₀ he ?_
  linear_combination
      (-((constHom W q₁ - constHom W x) * (constHom W q₁ - tautX W))) * hT +
      ((constHom W q₁ - constHom W x) * (constHom W q₁ - tautX W) -
        (constHom W q₁ - tautX W) ^ 2) * hQK +
      (constHom W q₁ - tautX W) ^ 2 * hPK +
      ((constHom W q₁ - constHom W x) * (constHom W q₂ - tautY W) *
          (constHom W q₁ - tautX W) -
        ((constHom W q₁ - constHom W x) *
            constHom W (W.slope q₁ x q₂ (W.negY x y))) *
          (constHom W q₁ - tautX W) ^ 2) * hl₁K +
      ((constHom W q₁ - constHom W x) * (constHom W q₂ - tautY W) *
          (constHom W q₁ - tautX W) -
        (constHom W q₂ - constHom W y) * (constHom W q₁ - tautX W) ^ 2) * hl₂K

/-- **The degenerate vertical numerator at `x = q₁` with `2Q ≠ O`**: one
zero escapes to infinity and `vertNumerator q₁ q₂ q₁` becomes the
tangent line at `Q` (divisor `2(Q) + (⊖2Q)`), up to the nonzero constant
`−(2q₂ + a₁q₁ + a₃)`. -/
lemma vertNumerator_self_tangent {q₁ q₂ : F} (hq : W.Equation q₁ q₂)
    (hy : q₂ ≠ W.negY q₁ q₂) :
    vertNumerator W q₁ q₂ q₁ =
      coordC W (-(2 * q₂ + W.a₁ * q₁ + W.a₃)) *
        CoordinateRing.YClass W (linePolynomial q₁ q₂ (W.slope q₁ q₁ q₂ q₂)) := by
  have hnY : W.negY q₁ q₂ = -q₂ - W.a₁ * q₁ - W.a₃ := rfl
  have hd : 2 * q₂ + W.a₁ * q₁ + W.a₃ ≠ 0 := fun hc =>
    hy (by rw [hnY]; linear_combination hc)
  have hden : q₂ - (-q₂ - W.a₁ * q₁ - W.a₃) ≠ 0 := fun hc =>
    hd (by linear_combination hc)
  have hinj : Function.Injective (algebraMap W.CoordinateRing W.FunctionField) :=
    IsFractionRing.injective W.CoordinateRing W.FunctionField
  have hlam : (2 * q₂ + W.a₁ * q₁ + W.a₃) * W.slope q₁ q₁ q₂ q₂ =
      3 * q₁ ^ 2 + 2 * W.a₂ * q₁ + W.a₄ - W.a₁ * q₂ := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hnY]
    field_simp [hden]
    ring
  have hlamK := congrArg (constHom W) hlam
  have hQK := congrArg (constHom W) ((WeierstrassCurve.Affine.equation_iff ..).mp hq)
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat] at hlamK hQK
  have hT : tautY W ^ 2 + constHom W W.a₁ * tautX W * tautY W +
      constHom W W.a₃ * tautY W =
      tautX W ^ 3 + constHom W W.a₂ * tautX W ^ 2 + constHom W W.a₄ * tautX W +
        constHom W W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff ..).mp (taut_equation W)
  apply hinj
  simp only [vertNumerator, YClass_line_eq, map_add, map_sub, map_mul, map_neg,
    map_pow, map_ofNat, algebraMap_coordX, algebraMap_coordY, algebraMap_coordC]
  linear_combination hT - hQK + (constHom W q₁ - tautX W) * hlamK

omit [DecidableEq F] in
/-- **The degenerate vertical numerator at `x = q₁` with `2Q = O`**: two
zeros escape to infinity and `vertNumerator q₁ q₂ q₁` becomes the
vertical `X − q₁` (divisor `(Q) + (⊖Q) = 2(Q)`), up to the constant
`3q₁² + 2a₂q₁ + a₄ − a₁q₂`, which is nonzero exactly by the
nonsingularity of `Q` (its other partial derivative vanishes here). -/
lemma vertNumerator_self_vertical {q₁ q₂ : F} (hq : W.Equation q₁ q₂)
    (hy : q₂ = W.negY q₁ q₂) :
    vertNumerator W q₁ q₂ q₁ =
      coordC W (3 * q₁ ^ 2 + 2 * W.a₂ * q₁ + W.a₄ - W.a₁ * q₂) *
        CoordinateRing.XClass W q₁ := by
  have hnY : W.negY q₁ q₂ = -q₂ - W.a₁ * q₁ - W.a₃ := rfl
  have hz : 2 * q₂ + W.a₁ * q₁ + W.a₃ = 0 := by
    rw [hnY] at hy; linear_combination hy
  have hinj : Function.Injective (algebraMap W.CoordinateRing W.FunctionField) :=
    IsFractionRing.injective W.CoordinateRing W.FunctionField
  have hzK := congrArg (constHom W) hz
  have hQK := congrArg (constHom W) ((WeierstrassCurve.Affine.equation_iff ..).mp hq)
  simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at hzK hQK
  have hT : tautY W ^ 2 + constHom W W.a₁ * tautX W * tautY W +
      constHom W W.a₃ * tautY W =
      tautX W ^ 3 + constHom W W.a₂ * tautX W ^ 2 + constHom W W.a₄ * tautX W +
        constHom W W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff ..).mp (taut_equation W)
  apply hinj
  simp only [vertNumerator, XClass_eq, map_add, map_sub, map_mul, map_pow,
    map_ofNat, algebraMap_coordX, algebraMap_coordY, algebraMap_coordC]
  linear_combination hT - hQK + (constHom W q₂ - tautY W) * hzK

/-!
### The line-numerator substrate: the hyperelliptic involution and
point evaluation

Two devices carry the line-numerator leaves.

* The **hyperelliptic involution** `involHom` of `F[W]` (`coordX ↦ coordX`,
  `coordY ↦ negY(coordX, coordY)`) is the comorphism of `⊖`, so it
  transports `I_S` to `I_{⊖S}` (`map_involHom_pointIdeal`) and carries
  `lineNumerator` at `⊖Q` to `lineNumeratorNeg` at `Q`
  (`involHom_lineNumerator`).  That reduces the conjugate membership leaf
  to the plain one, with no second case analysis.

* **Point evaluation** `coordEval` (`AdjoinRoot.evalEval` at an affine
  point of `W` itself) turns vanishing at a point into membership in its
  point ideal (`mem_pointIdeal_of_coordEval_eq_zero`), which is how the
  three simple factors of the line-numerator divisor are obtained from
  the group law `Q ⊕ (P ⊖ Q) = P`.
-/

omit [DecidableEq F] in
/-- The constants embedding into the coordinate ring is additive. -/
lemma coordC_add (c d : F) : coordC W (c + d) = coordC W c + coordC W d := by
  rw [coordC, coordC, coordC, ← map_add, ← Polynomial.C_add, ← Polynomial.C_add]

omit [DecidableEq F] in
/-- The constants embedding into the coordinate ring respects negation. -/
lemma coordC_neg (c : F) : coordC W (-c) = -coordC W c := by
  rw [coordC, coordC, ← map_neg, ← Polynomial.C_neg, ← Polynomial.C_neg]

omit [DecidableEq F] in
/-- The constants embedding into the coordinate ring respects
subtraction. -/
lemma coordC_sub (c d : F) : coordC W (c - d) = coordC W c - coordC W d := by
  rw [coordC, coordC, coordC, ← map_sub, ← Polynomial.C_sub, ← Polynomial.C_sub]

omit [DecidableEq F] in
/-- The Weierstrass relation, read inside the coordinate ring. -/
lemma coord_equation (W : WeierstrassCurve.Affine F) :
    coordY W ^ 2 + coordC W W.a₁ * coordX W * coordY W + coordC W W.a₃ * coordY W =
      coordX W ^ 3 + coordC W W.a₂ * coordX W ^ 2 + coordC W W.a₄ * coordX W +
        coordC W W.a₆ := by
  have h : CoordinateRing.mk W (Polynomial.X ^ 2 +
      Polynomial.C (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) *
        Polynomial.X -
      Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2 +
        Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆)) = 0 := by
    show CoordinateRing.mk W W.polynomial = 0
    rw [AdjoinRoot.mk_self]
  simp only [map_add, map_sub, map_mul, map_pow] at h
  simp only [coordX, coordY, coordC]
  linear_combination h

omit [DecidableEq F] in
/-- The class `Y − y` for a constant `y` in terms of the coordinate
atoms. -/
lemma YClass_C_eq (y : F) :
    CoordinateRing.YClass W (Polynomial.C y) = coordY W - coordC W y := by
  rw [CoordinateRing.YClass, coordY, coordC, ← map_sub]

/-- **The hyperelliptic involution of the coordinate ring**: the
`F[X]`-algebra endomorphism of `F[W]` fixing `coordX` and sending
`coordY` to `negY(coordX, coordY) = −coordY − a₁·coordX − a₃`.  It is the
comorphism of `⊖ : W → W`, and transports the divisor bookkeeping of a
point to that of its negative (`map_involHom_pointIdeal`). -/
noncomputable def involHom (W : WeierstrassCurve.Affine F) :
    W.CoordinateRing →+* W.CoordinateRing :=
  AdjoinRoot.lift ((CoordinateRing.mk W).comp Polynomial.C)
    (-coordY W - coordC W W.a₁ * coordX W - coordC W W.a₃) (by
      have hR := coord_equation W
      simp only [coordX, coordY, coordC] at hR
      show Polynomial.eval₂ ((CoordinateRing.mk W).comp Polynomial.C)
        (-coordY W - coordC W W.a₁ * coordX W - coordC W W.a₃)
        (Polynomial.X ^ 2 +
          Polynomial.C (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) *
            Polynomial.X -
          Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2 +
            Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆)) = 0
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, RingHom.coe_comp,
        Function.comp_apply, map_add, map_mul, map_pow, coordX, coordY, coordC]
      linear_combination hR)

omit [DecidableEq F] in
/-- The involution fixes the image of `F[X]`. -/
@[simp] lemma involHom_ofPoly (r : Polynomial F) :
    involHom W (CoordinateRing.mk W (Polynomial.C r)) =
      CoordinateRing.mk W (Polynomial.C r) := by
  rw [involHom, AdjoinRoot.lift_mk, Polynomial.eval₂_C]
  rfl

omit [DecidableEq F] in
/-- The involution fixes `coordX`. -/
@[simp] lemma involHom_coordX : involHom W (coordX W) = coordX W :=
  involHom_ofPoly Polynomial.X

omit [DecidableEq F] in
/-- The involution fixes the constants. -/
@[simp] lemma involHom_coordC (d : F) : involHom W (coordC W d) = coordC W d :=
  involHom_ofPoly (Polynomial.C d)

omit [DecidableEq F] in
/-- The involution sends `coordY` to `negY(coordX, coordY)`. -/
@[simp] lemma involHom_coordY :
    involHom W (coordY W) =
      -coordY W - coordC W W.a₁ * coordX W - coordC W W.a₃ :=
  AdjoinRoot.lift_root _

omit [DecidableEq F] in
/-- The involution transports the point ideal of `S` to that of `⊖S`. -/
lemma map_involHom_pointIdeal (S : W.Point) :
    Ideal.map (involHom W) (pointIdeal W S) = pointIdeal W (-S) := by
  cases S with
  | zero =>
    rw [show pointIdeal W (-Point.zero : W.Point) = ⊤ from rfl,
      show pointIdeal W (Point.zero : W.Point) = ⊤ from rfl, Ideal.map_top]
  | some x y h =>
    rw [Point.neg_some, pointIdeal_some, pointIdeal_some, CoordinateRing.XYIdeal,
      CoordinateRing.XYIdeal, Ideal.map_span, Set.image_pair, XClass_eq, YClass_C_eq,
      YClass_C_eq, map_sub, map_sub, involHom_coordX, involHom_coordC,
      involHom_coordY, involHom_coordC,
      show W.negY x y = -y - W.a₁ * x - W.a₃ from rfl, coordC_sub, coordC_sub,
      coordC_neg, coordC_mul]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_) <;>
      rw [Set.insert_subset_iff, Set.singleton_subset_iff] <;>
      exact ⟨Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩,
        Ideal.mem_span_pair.mpr ⟨-coordC W W.a₁, -1, by ring⟩⟩

omit [DecidableEq F] in
/-- **The conjugate line numerator is the involution transport of the
line numerator at `⊖Q`.**  Purely formal: the involution fixes the
cleared `addX` (`A` is `σ`-invariant, since `σ` flips `U = coordY − q₂`
to `−(U + a₁T)`), and the constant terms recombine. -/
lemma involHom_lineNumerator (q₁ q₂ x₁ y₁ ℓ : F) :
    involHom W (lineNumerator W q₁ (W.negY q₁ q₂) x₁ y₁ ℓ) =
      lineNumeratorNeg W q₁ q₂ x₁ y₁ ℓ := by
  simp only [lineNumerator, lineNumeratorNeg, map_add, map_sub, map_mul, map_neg,
    map_pow, involHom_coordX, involHom_coordC, involHom_coordY,
    show W.negY q₁ q₂ = -q₂ - W.a₁ * q₁ - W.a₃ from rfl, coordC_sub, coordC_neg,
    coordC_mul]
  ring

omit [DecidableEq F] in
/-- `T = coordX − q₁` lies in the point ideal of `Q`. -/
lemma sub_coordX_mem_pointIdeal {q₁ q₂ : F} (hq : W.Nonsingular q₁ q₂) :
    coordX W - coordC W q₁ ∈ pointIdeal W (.some q₁ q₂ hq) := by
  rw [pointIdeal_some, CoordinateRing.XYIdeal, ← XClass_eq]
  exact Ideal.subset_span (Set.mem_insert _ _)

omit [DecidableEq F] in
/-- `U = coordY − q₂` lies in the point ideal of `Q`. -/
lemma sub_coordY_mem_pointIdeal {q₁ q₂ : F} (hq : W.Nonsingular q₁ q₂) :
    coordY W - coordC W q₂ ∈ pointIdeal W (.some q₁ q₂ hq) := by
  rw [pointIdeal_some, CoordinateRing.XYIdeal, ← YClass_C_eq]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

omit [DecidableEq F] in
/-- **Distinct points have coprime point ideals.**  No maximality input
is needed: if the `x`-coordinates differ, the difference of the two
`X`-classes is a nonzero constant, hence a unit of `F[W]`; if they agree,
the `y`-coordinates differ and the difference of the two `Y`-classes is.
The convention `I_O = ⊤` settles the cases involving `O`. -/
lemma isCoprime_pointIdeal {S T : W.Point} (hST : S ≠ T) :
    IsCoprime (pointIdeal W S) (pointIdeal W T) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  cases S with
  | zero => rw [show pointIdeal W (Point.zero : W.Point) = ⊤ from rfl, top_sup_eq]
  | some x₁ y₁ h₁ =>
    cases T with
    | zero => rw [show pointIdeal W (Point.zero : W.Point) = ⊤ from rfl, sup_top_eq]
    | some x₂ y₂ h₂ =>
      by_cases hx : x₁ = x₂
      · subst hx
        have hy : y₂ - y₁ ≠ 0 := by
          refine sub_ne_zero.mpr fun hc => hST ?_
          subst hc
          rfl
        refine Ideal.eq_top_of_isUnit_mem _ ?_ (isUnit_coordC (W := W) hy)
        rw [coordC_sub, show coordC W y₂ - coordC W y₁ =
          (coordY W - coordC W y₁) - (coordY W - coordC W y₂) from by ring]
        exact sub_mem (Submodule.mem_sup_left (sub_coordY_mem_pointIdeal h₁))
          (Submodule.mem_sup_right (sub_coordY_mem_pointIdeal h₂))
      · refine Ideal.eq_top_of_isUnit_mem _ ?_
          (isUnit_coordC (W := W) (sub_ne_zero.mpr (Ne.symm hx)))
        rw [coordC_sub, show coordC W x₂ - coordC W x₁ =
          (coordX W - coordC W x₁) - (coordX W - coordC W x₂) from by ring]
        exact sub_mem (Submodule.mem_sup_left (sub_coordX_mem_pointIdeal h₁))
          (Submodule.mem_sup_right (sub_coordX_mem_pointIdeal h₂))

omit [DecidableEq F] in
/-- **The certificate-free half of the line-numerator membership**:
`lineNumerator` lies in `I_Q³`.  With `T = coordX − q₁`, `U = coordY − q₂`
the cleared `addX` is `A = U² + a₁UT − (a₂ + 2q₁)T² − T³ ∈ ⟨T, U⟩²`, and
every summand of `lineNumerator` is `U · (A − q₁T²)`, a multiple of `T³`,
or `(A − cT²) · T` — all in `⟨T, U⟩³`. -/
lemma lineNumerator_mem_pointIdeal_pow_three {q₁ q₂ : F} (hq : W.Nonsingular q₁ q₂)
    (x₁ y₁ ℓ : F) :
    lineNumerator W q₁ q₂ x₁ y₁ ℓ ∈ pointIdeal W (.some q₁ q₂ hq) ^ 3 := by
  have hT := sub_coordX_mem_pointIdeal hq
  have hU := sub_coordY_mem_pointIdeal hq
  have h2 : pointIdeal W (.some q₁ q₂ hq) ^ 2 =
      pointIdeal W (.some q₁ q₂ hq) * pointIdeal W (.some q₁ q₂ hq) := sq _
  have h3l : pointIdeal W (.some q₁ q₂ hq) ^ 3 =
      pointIdeal W (.some q₁ q₂ hq) * pointIdeal W (.some q₁ q₂ hq) ^ 2 := by ring
  have h3r : pointIdeal W (.some q₁ q₂ hq) ^ 3 =
      pointIdeal W (.some q₁ q₂ hq) ^ 2 * pointIdeal W (.some q₁ q₂ hq) := by ring
  have hT2 : (coordX W - coordC W q₁) ^ 2 ∈ pointIdeal W (.some q₁ q₂ hq) ^ 2 := by
    rw [h2, pow_two (coordX W - coordC W q₁)]; exact Ideal.mul_mem_mul hT hT
  have hT3 : (coordX W - coordC W q₁) ^ 3 ∈ pointIdeal W (.some q₁ q₂ hq) ^ 3 := by
    rw [show (coordX W - coordC W q₁) ^ 3 =
      (coordX W - coordC W q₁) ^ 2 * (coordX W - coordC W q₁) from by ring, h3r]
    exact Ideal.mul_mem_mul hT2 hT
  have hA : (coordY W - coordC W q₂) ^ 2 +
      coordC W W.a₁ * (coordY W - coordC W q₂) * (coordX W - coordC W q₁) -
      (coordC W W.a₂ + coordC W q₁ + coordX W) * (coordX W - coordC W q₁) ^ 2 ∈
        pointIdeal W (.some q₁ q₂ hq) ^ 2 := by
    refine sub_mem (add_mem ?_ ?_) (Ideal.mul_mem_left _ _ hT2)
    · rw [h2, pow_two (coordY W - coordC W q₂)]; exact Ideal.mul_mem_mul hU hU
    · rw [mul_assoc, h2]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hU hT)
  have hAq : (coordY W - coordC W q₂) ^ 2 +
      coordC W W.a₁ * (coordY W - coordC W q₂) * (coordX W - coordC W q₁) -
      (coordC W W.a₂ + coordC W q₁ + coordX W) * (coordX W - coordC W q₁) ^ 2 -
      coordC W q₁ * (coordX W - coordC W q₁) ^ 2 ∈
        pointIdeal W (.some q₁ q₂ hq) ^ 2 :=
    sub_mem hA (Ideal.mul_mem_left _ _ hT2)
  have hAx : (coordY W - coordC W q₂) ^ 2 +
      coordC W W.a₁ * (coordY W - coordC W q₂) * (coordX W - coordC W q₁) -
      (coordC W W.a₂ + coordC W q₁ + coordX W) * (coordX W - coordC W q₁) ^ 2 -
      coordC W x₁ * (coordX W - coordC W q₁) ^ 2 ∈
        pointIdeal W (.some q₁ q₂ hq) ^ 2 :=
    sub_mem hA (Ideal.mul_mem_left _ _ hT2)
  rw [lineNumerator]
  refine sub_mem (sub_mem (sub_mem (sub_mem (neg_mem (add_mem ?_ ?_)) ?_) ?_) ?_) ?_
  · rw [h3l]; exact Ideal.mul_mem_mul hU hAq
  · exact Ideal.mul_mem_left _ _ hT3
  · rw [h3r]; exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hA) hT
  · exact Ideal.mul_mem_left _ _ hT3
  · rw [h3r]; exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hAx) hT
  · exact Ideal.mul_mem_left _ _ hT3

omit [DecidableEq F] in
/-- Membership in the point ideal of `(x, y)` from vanishing of a
polynomial lift at `(x, y)`. -/
lemma mem_XYIdeal_of_evalEval {x y : F} (f : Polynomial (Polynomial F))
    (hf : f.evalEval x y = 0) :
    CoordinateRing.mk W f ∈ CoordinateRing.XYIdeal W x (Polynomial.C y) := by
  have hmem : f ∈ Ideal.span {Polynomial.C (Polynomial.X - Polynomial.C x),
      (Polynomial.X : Polynomial (Polynomial F)) - Polynomial.C (Polynomial.C y)} :=
    Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr hf
  have himg := Ideal.mem_map_of_mem (CoordinateRing.mk W) hmem
  simp only [CoordinateRing.XYIdeal, CoordinateRing.XClass, CoordinateRing.YClass]
  rwa [Ideal.map_span, Set.image_pair] at himg

/-- Evaluation of coordinate-ring elements at an affine point of `W`
itself: the `AdjoinRoot`-level `evalEval` of the Weierstrass
polynomial. -/
noncomputable def coordEval (W : WeierstrassCurve.Affine F) {x y : F}
    (h : W.Equation x y) : W.CoordinateRing →+* F :=
  AdjoinRoot.evalEval (p := W.polynomial) h

omit [DecidableEq F] in
lemma coordEval_mk {x y : F} (h : W.Equation x y) (g : Polynomial (Polynomial F)) :
    coordEval W h (CoordinateRing.mk W g) = g.evalEval x y :=
  AdjoinRoot.evalEval_mk (p := W.polynomial) h g

omit [DecidableEq F] in
@[simp] lemma coordEval_coordC {x y : F} (h : W.Equation x y) (d : F) :
    coordEval W h (coordC W d) = d := by
  rw [coordC, coordEval_mk]; simp [Polynomial.evalEval]

omit [DecidableEq F] in
@[simp] lemma coordEval_coordX {x y : F} (h : W.Equation x y) :
    coordEval W h (coordX W) = x := by
  rw [coordX, coordEval_mk]; simp [Polynomial.evalEval]

omit [DecidableEq F] in
@[simp] lemma coordEval_coordY {x y : F} (h : W.Equation x y) :
    coordEval W h (coordY W) = y := by
  rw [coordY, coordEval_mk]; simp [Polynomial.evalEval]

omit [DecidableEq F] in
/-- A coordinate-ring element vanishing at an affine point lies in its
point ideal. -/
lemma mem_pointIdeal_of_coordEval_eq_zero {x y : F} (h : W.Nonsingular x y)
    {z : W.CoordinateRing} (hz : coordEval W h.left z = 0) :
    z ∈ pointIdeal W (.some x y h) := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [coordEval_mk] at hz
  exact mem_XYIdeal_of_evalEval f hz

/-- The cleared slope relation `ℓ·(x₁ − x₂) = y₁ − y₂` for the group-law
slope, uniformly in the chord and the tangent case. -/
lemma slope_mul_sub {x₁ y₁ x₂ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    W.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
  by_cases hx : x₁ = x₂
  · have hyy : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ hx fun hc => hxy ⟨hx, hc⟩
    rw [hx, hyy]; ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    field_simp

omit [DecidableEq F] in
/-- **The line numerator only depends on the line, not on the base point
used to write it down**: replacing `(x, y)` by any other point `(x', y')`
of the line of slope `ℓ` through it leaves `lineNumerator` unchanged.
This is what makes ONE simple-factor lemma serve all three points of the
chord. -/
lemma lineNumerator_congr {q₁ q₂ x y x' y' ℓ : F} (hl : ℓ * (x - x') = y - y') :
    lineNumerator W q₁ q₂ x y ℓ = lineNumerator W q₁ q₂ x' y' ℓ := by
  have h1 : coordC W ℓ * (coordC W x - coordC W x') = coordC W y - coordC W y' := by
    rw [← coordC_sub, ← coordC_mul, ← coordC_sub, hl]
  simp only [lineNumerator]
  linear_combination (coordX W - coordC W q₁) ^ 3 * h1

/-- **The simple factor of the line-numerator membership** (PROVEN): the
cleared line value at the translate vanishes at `P ⊖ Q`, for *any* slope
`ℓ`.

Indeed `lineNumerator/T³` is the line function `L` read at `Q ⊕ taut`, so
at `taut = P ⊖ Q` it is `L(P) = 0`.  Formally: `P ⊖ Q` is either `O` (and
`I_O = ⊤`) or an affine point `(α, β)`, and then the group law
`Q ⊕ (α, β) = P` gives `addX q₁ α λ = x`, `addY q₁ α q₂ λ = y` for
`λ = slope q₁ α q₂ β`; with `T = α − q₁`, `U = β − q₂ = −λ(q₁ − α)` the
cleared `addX` is `A = T²·addX q₁ α λ = T²x` and the `Y`-part of
`lineNumerator` is `T³·addY q₁ α q₂ λ = T³y`, so the whole value is
`T³y − ℓ·T³(x − x) − T³y = 0`.  The degenerate configuration `α = q₁`
forces `β = q₂` (the other sign is `P = O`) and makes every summand
vanish outright. -/
lemma lineNumerator_mem_pointIdeal_sub {q₁ q₂ x y : F} (hq : W.Nonsingular q₁ q₂)
    (h : W.Nonsingular x y) (ℓ : F) :
    lineNumerator W q₁ q₂ x y ℓ ∈
      pointIdeal W (.some x y h - .some q₁ q₂ hq) := by
  rcases hd : ((.some x y h : W.Point) - .some q₁ q₂ hq) with _ | ⟨α, β, hαβ⟩
  · rw [hd, show pointIdeal W (Point.zero : W.Point) = ⊤ from rfl]
    exact Submodule.mem_top
  · have hsum : (Point.some q₁ q₂ hq : W.Point) + Point.some α β hαβ =
        Point.some x y h := by rw [← hd]; abel
    rw [hd]
    refine mem_pointIdeal_of_coordEval_eq_zero hαβ ?_
    by_cases hQA : q₁ = α ∧ q₂ = W.negY α β
    · exact absurd (by rw [← hsum, Point.add_of_Y_eq hQA.1 hQA.2] :
        (Point.some x y h : W.Point) = 0) (Point.some_ne_zero h)
    · rw [Point.add_some hQA] at hsum
      rw [Point.some.injEq] at hsum
      obtain ⟨hX, hY⟩ := hsum
      simp only [lineNumerator, map_sub, map_add, map_mul, map_neg, map_pow,
        coordEval_coordX, coordEval_coordY, coordEval_coordC]
      by_cases hxa : q₁ = α
      · have hβ : q₂ = β :=
          Y_eq_of_Y_ne hq.left hαβ.left hxa fun hc => hQA ⟨hxa, hc⟩
        rw [← hxa, ← hβ]; ring
      · have hl : W.slope q₁ α q₂ β * (q₁ - α) = q₂ - β :=
          slope_mul_sub hq.left hαβ.left fun hc => hQA hc
        have hU : β - q₂ = -(W.slope q₁ α q₂ β * (q₁ - α)) := by
          linear_combination hl
        simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
          WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX] at hX hY
        rw [hU]
        linear_combination (-(q₁ - α) ^ 3) * hY + (ℓ * (q₁ - α) ^ 3) * hX

variable {p : ℕ} [Fact p.Prime] [IsAlgClosed F]

-- `[IsAlgClosed F]` is not needed for this leaf (nor is `hΔ`), but the
-- signature is kept as the consumer `spanSingleton_pointEval_XClass`
-- states it, so the unused-section-variable linter is silenced here
-- rather than propagating an `omit` into that theorem.
set_option linter.unusedSectionVars false in
/-- **L4-8 numerator leaf (PROVEN): the divisor of the vertical
numerator.**  `vertNumerator q₁ q₂ x` spans
`I_Q² · I_{P⊖Q} · I_{⊖P⊖Q}` for `P = (x, y)`, `Q = (q₁, q₂)` — its
affine divisor is `2(Q) + (P⊖Q) + (⊖P⊖Q)` (which sums to `O`, so the
span is principal, consistently).  The `O`-convention `I_O = ⊤` makes
the statement uniform in the degenerate configurations `P = ±Q`
(a zero escapes to infinity and the corresponding factor is `⊤`).
CAS-checked numerically (PARI/GP: `y² = x³ − x + 1`, `Q = (1,1)`,
`P = (3,5)`: vanishing at `Q` to second order and at `P⊖Q = (5,−11)`,
`⊖P⊖Q = (0,−1)`).

PROOF (chord bookkeeping, no colength squeeze — the recommended
norm-degree route turned out to be unnecessary).  The brick is the
*integral* line-span identity `YIdeal_eq_prod_pointIdeal`:
`I_S · I_T · I_{⊖(S⊕T)} = ⟨ℓ(S,T)⟩` (mathlib's `XYIdeal_mul_XYIdeal`
with the invertible `I_{S⊕T}` cancelled off).  Two configurations:

* `q₁ ≠ x`.  Take the chords through `Q, P` (third point `⊖P⊖Q`) and
  through `Q, ⊖P` (third point `P⊖Q`) — both written with the
  coordinates of `Q` and `P` only, no coordinates of `P⊖Q`/`⊖P⊖Q`
  needed.  Their product has divisor
  `2(Q) + (P⊖Q) + (⊖P⊖Q) + (P) + (⊖P)`, and the explicit ring identity
  `vertNumerator · (X − x) = (q₁ − x) · ℓ(Q,P) · ℓ(Q,⊖P)`
  (`vertNumerator_mul_XClass`) realizes it; cancelling the principal
  `⟨X − x⟩ = I_P · I_{⊖P}` (`XYIdeal_neg_mul`, cancellable by
  `Ideal.span_singleton_mul_right_inj` in the domain `F[W]`) gives the
  claim.
* `q₁ = x`, so `P = ±Q` and one of the two factors is `⊤`; both signs
  reduce to `⟨n⟩ = I_Q² · I_{⊖2Q}`.  If `2Q ≠ O` the numerator *is* the
  tangent at `Q` up to the constant `−(2q₂+a₁q₁+a₃)`
  (`vertNumerator_self_tangent`); if `2Q = O` it is the vertical
  `X − q₁` up to `3q₁²+2a₂q₁+a₄−a₁q₂`, nonzero by nonsingularity of `Q`
  (`vertNumerator_self_vertical`), and `I_Q² = I_Q · I_{⊖Q} = ⟨X−q₁⟩`.

The three ring identities are each verified in the function field
(where `algebraMap F[W] → K` is injective) by `linear_combination`
against the Weierstrass equation at the tautological point, at `Q` and
at `P`, plus the cleared slope relations.  The discriminant hypothesis
is not needed. -/
theorem span_vertNumerator (_hΔ : W.Δ ≠ 0) {q₁ q₂ x y : F}
    (hq : W.Nonsingular q₁ q₂) (h : W.Nonsingular x y) :
    Ideal.span {vertNumerator W q₁ q₂ x} =
      pointIdeal W (.some q₁ q₂ hq) ^ 2 *
        (pointIdeal W (.some x y h - .some q₁ q₂ hq) *
          pointIdeal W (-.some x y h - .some q₁ q₂ hq)) := by
  by_cases hx : q₁ = x
  · subst hx
    have hcommon : Ideal.span {vertNumerator W q₁ q₂ q₁} =
        pointIdeal W (.some q₁ q₂ hq) ^ 2 *
          pointIdeal W (-(.some q₁ q₂ hq) - .some q₁ q₂ hq) := by
      have hnY : W.negY q₁ q₂ = -q₂ - W.a₁ * q₁ - W.a₃ := rfl
      by_cases hy2 : q₂ = W.negY q₁ q₂
      · have h2Q : (WeierstrassCurve.Affine.Point.some q₁ q₂ hq +
            WeierstrassCurve.Affine.Point.some q₁ q₂ hq : W.Point) = 0 :=
          Point.add_of_Y_eq rfl hy2
        have hzero : (-(WeierstrassCurve.Affine.Point.some q₁ q₂ hq) -
            WeierstrassCurve.Affine.Point.some q₁ q₂ hq : W.Point) = 0 := by
          rw [sub_eq_add_neg, ← neg_add, h2Q, neg_zero]
        have hz0 : 2 * q₂ + W.a₁ * q₁ + W.a₃ = 0 := by
          rw [hnY] at hy2; linear_combination hy2
        have hc₁ : 3 * q₁ ^ 2 + 2 * W.a₂ * q₁ + W.a₄ - W.a₁ * q₂ ≠ 0 := by
          rcases ((WeierstrassCurve.Affine.nonsingular_iff' ..).mp hq).2 with hX | hY
          · exact fun hc => hX (by linear_combination -hc)
          · exact absurd hz0 hY
        have hV := CoordinateRing.XYIdeal_neg_mul hq
        rw [← hy2] at hV
        rw [hzero, show pointIdeal W (0 : W.Point) = ⊤ from rfl, Ideal.mul_top,
          vertNumerator_self_vertical hq.left hy2,
          Ideal.span_singleton_mul_left_unit (isUnit_coordC hc₁), pow_two,
          pointIdeal_some, hV]
        rfl
      · have hxy : ¬(q₁ = q₁ ∧ q₂ = W.negY q₁ q₂) := fun hc => hy2 hc.2
        have hL := YIdeal_eq_prod_pointIdeal hq hq hxy
        have hdd : -(2 * q₂ + W.a₁ * q₁ + W.a₃) ≠ 0 := by
          refine neg_ne_zero.mpr fun hc => hy2 ?_
          rw [hnY]; linear_combination hc
        rw [vertNumerator_self_tangent hq.left hy2,
          Ideal.span_singleton_mul_left_unit (isUnit_coordC hdd),
          show Ideal.span
              {CoordinateRing.YClass W
                (linePolynomial q₁ q₂ (W.slope q₁ q₁ q₂ q₂))} =
            CoordinateRing.YIdeal W
              (linePolynomial q₁ q₂ (W.slope q₁ q₁ q₂ q₂)) from rfl,
          hL, show (-(WeierstrassCurve.Affine.Point.some q₁ q₂ hq +
              WeierstrassCurve.Affine.Point.some q₁ q₂ hq) : W.Point) =
            -(WeierstrassCurve.Affine.Point.some q₁ q₂ hq) -
              WeierstrassCurve.Affine.Point.some q₁ q₂ hq from by abel,
          pow_two, mul_assoc]
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h.left hq.left rfl with hyy | hyy
    · have hPQ : (WeierstrassCurve.Affine.Point.some q₁ y h : W.Point) =
          WeierstrassCurve.Affine.Point.some q₁ q₂ hq := by subst hyy; rfl
      rw [hPQ, sub_self, show pointIdeal W (0 : W.Point) = ⊤ from rfl,
        Ideal.top_mul]
      exact hcommon
    · have hPQ : (WeierstrassCurve.Affine.Point.some q₁ y h : W.Point) =
          -(WeierstrassCurve.Affine.Point.some q₁ q₂ hq) := by subst hyy; rfl
      rw [hPQ, neg_neg, sub_self, show pointIdeal W (0 : W.Point) = ⊤ from rfl,
        Ideal.mul_top]
      exact hcommon
  · have hny : W.Nonsingular x (W.negY x y) :=
      (WeierstrassCurve.Affine.nonsingular_neg ..).mpr h
    have hxy₁ : ¬(q₁ = x ∧ q₂ = W.negY x y) := fun hc => hx hc.1
    have hxy₂ : ¬(q₁ = x ∧ q₂ = W.negY x (W.negY x y)) := fun hc => hx hc.1
    have h1 := YIdeal_eq_prod_pointIdeal hq h hxy₁
    have h2 := YIdeal_eq_prod_pointIdeal hq hny hxy₂
    rw [show (WeierstrassCurve.Affine.Point.some x (W.negY x y) hny : W.Point) =
      -(WeierstrassCurve.Affine.Point.some x y h) from rfl,
      show (-(WeierstrassCurve.Affine.Point.some q₁ q₂ hq +
          -(WeierstrassCurve.Affine.Point.some x y h)) : W.Point) =
        WeierstrassCurve.Affine.Point.some x y h -
          WeierstrassCurve.Affine.Point.some q₁ q₂ hq from by abel] at h2
    rw [show (-(WeierstrassCurve.Affine.Point.some q₁ q₂ hq +
          WeierstrassCurve.Affine.Point.some x y h) : W.Point) =
        -WeierstrassCurve.Affine.Point.some x y h -
          WeierstrassCurve.Affine.Point.some q₁ q₂ hq from by abel] at h1
    have hV : pointIdeal W (-(WeierstrassCurve.Affine.Point.some x y h)) *
        pointIdeal W (WeierstrassCurve.Affine.Point.some x y h) =
        CoordinateRing.XIdeal W x := by
      rw [Point.neg_some, pointIdeal_some, pointIdeal_some]
      exact CoordinateRing.XYIdeal_neg_mul h
    refine (Ideal.span_singleton_mul_right_inj
      (CoordinateRing.XClass_ne_zero (W' := W) x)).mp ?_
    calc Ideal.span {CoordinateRing.XClass W x} *
          Ideal.span {vertNumerator W q₁ q₂ x}
        = Ideal.span {vertNumerator W q₁ q₂ x * CoordinateRing.XClass W x} := by
          rw [Ideal.span_singleton_mul_span_singleton, mul_comm]
      _ = Ideal.span {CoordinateRing.YClass W
              (linePolynomial q₁ q₂ (W.slope q₁ x q₂ y)) *
            CoordinateRing.YClass W
              (linePolynomial q₁ q₂ (W.slope q₁ x q₂ (W.negY x y)))} := by
          rw [vertNumerator_mul_XClass hq.left h.left hx,
            Ideal.span_singleton_mul_left_unit (isUnit_coordC (sub_ne_zero.mpr hx))]
      _ = CoordinateRing.YIdeal W (linePolynomial q₁ q₂ (W.slope q₁ x q₂ y)) *
            CoordinateRing.YIdeal W
              (linePolynomial q₁ q₂ (W.slope q₁ x q₂ (W.negY x y))) := by
          rw [CoordinateRing.YIdeal, CoordinateRing.YIdeal,
            Ideal.span_singleton_mul_span_singleton]
      _ = (pointIdeal W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
            (pointIdeal W (WeierstrassCurve.Affine.Point.some x y h) *
              pointIdeal W (-WeierstrassCurve.Affine.Point.some x y h -
                WeierstrassCurve.Affine.Point.some q₁ q₂ hq))) *
          (pointIdeal W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
            (pointIdeal W (-(WeierstrassCurve.Affine.Point.some x y h)) *
              pointIdeal W (WeierstrassCurve.Affine.Point.some x y h -
                WeierstrassCurve.Affine.Point.some q₁ q₂ hq))) := by
          rw [h1, h2]
      _ = Ideal.span {CoordinateRing.XClass W x} *
            (pointIdeal W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) ^ 2 *
              (pointIdeal W (WeierstrassCurve.Affine.Point.some x y h -
                  WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
                pointIdeal W (-WeierstrassCurve.Affine.Point.some x y h -
                  WeierstrassCurve.Affine.Point.some q₁ q₂ hq))) := by
          rw [show Ideal.span {CoordinateRing.XClass W x} =
            CoordinateRing.XIdeal W x from rfl, ← hV]
          ring

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The cancellation squeeze** (PROVEN): the elementary replacement of
the colength/norm-degree argument for divisor identities of the shape
"`n` spans the point-ideal product `I`".

Suppose `I` and `J` are principal with nonzero generators (as the
point-ideal product of *any* zero-sum multiset is, by
`exists_span_eq_prod_pointIdeal`), that `n ∈ I` and `ñ ∈ J`, and that
the *product* identity `⟨n · ñ⟩ = I · J` is already known.  Then
`⟨n⟩ = I` exactly — no sharp degree count, no case analysis on
degenerate configurations.

Indeed `n = u₁m₁` and `ñ = u₂m₂`, so `⟨m₁m₂ · u₁u₂⟩ = ⟨n·ñ⟩ = ⟨m₁m₂⟩`;
in a domain that makes `u₁u₂` — hence `u₁` — a unit, and `⟨n⟩ = ⟨m₁⟩`.

This is the workhorse behind `span_lineNumerator`: the "conjugate"
partner `ñ = lineNumeratorNeg` supplies the second membership, and the
product identity comes for free from `span_vertNumerator` through
`lineNumerator_mul_lineNumeratorNeg`.  The virtue over the colength
route is uniformity: the degenerate configurations (`P = ±Q`, `P = ±2Q`,
`2P = O`, small torsion) make *both* sides drop in lockstep, so nothing
in this argument has to see them. -/
lemma span_eq_of_mem_of_span_mul_eq {n ñ : W.CoordinateRing}
    {I J : Ideal W.CoordinateRing}
    (hI : ∃ a : W.CoordinateRing, a ≠ 0 ∧ Ideal.span {a} = I)
    (hJ : ∃ a : W.CoordinateRing, a ≠ 0 ∧ Ideal.span {a} = J)
    (hn : n ∈ I) (hñ : ñ ∈ J) (hmul : Ideal.span {n * ñ} = I * J) :
    Ideal.span {n} = I := by
  obtain ⟨m₁, hm₁0, hm₁⟩ := hI
  obtain ⟨m₂, hm₂0, hm₂⟩ := hJ
  obtain ⟨u₁, hu₁⟩ := Ideal.mem_span_singleton'.mp (show n ∈ Ideal.span {m₁} by rwa [hm₁])
  obtain ⟨u₂, hu₂⟩ := Ideal.mem_span_singleton'.mp (show ñ ∈ Ideal.span {m₂} by rwa [hm₂])
  have hkey : Ideal.span {m₁ * m₂ * (u₁ * u₂)} = Ideal.span {m₁ * m₂} := by
    rw [show m₁ * m₂ * (u₁ * u₂) = u₁ * m₁ * (u₂ * m₂) from by ring, hu₁, hu₂, hmul,
      ← hm₁, ← hm₂, Ideal.span_singleton_mul_span_singleton]
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hkey
  have hw' : m₁ * m₂ * (u₁ * u₂ * (w : W.CoordinateRing)) = m₁ * m₂ * 1 := by
    rw [mul_one]; linear_combination hw
  have hu : IsUnit (u₁ * u₂) :=
    IsUnit.of_mul_eq_one _ (mul_left_cancel₀ (mul_ne_zero hm₁0 hm₂0) hw')
  rw [← hu₁, Ideal.span_singleton_mul_left_unit (isUnit_of_mul_isUnit_left hu), hm₁]

omit [IsAlgClosed F] in
/-- **L4-8 line-numerator sub-leaf (sorry): the cleared conjugate
product.**  The two cleared line values at the translate multiply to the
product of the three vertical numerators at the three `X`-coordinates
cut out by the chord:

`lineNumerator · lineNumeratorNeg = −(vertNum x₁ · vertNum x₂ · vertNum x₃)`,
`x₃ = addX x₁ x₂ ℓ`.

ROUTE (certificate-free, no case analysis).  Write `T := X − q₁`,
`U := Y − q₂`, `A := U² + a₁UT − (a₂ + q₁ + X)T²` (so `A = x(Q ⊕ taut)T²`
and `vertNumerator W q₁ q₂ x = A − xT²` by `ring`), and
`Λ := ℓ(A − x₁T²)T + y₁T³` (the cleared line value `L(x(Q ⊕ taut))T³`).
By construction
`lineNumerator = 𝔶 − Λ` and `lineNumeratorNeg = 𝔶' − Λ`, where
`𝔶 := −U(A − q₁T²) − q₂T³ − a₁AT − a₃T³` and `𝔶' := U(A − q₁T²) + q₂T³`,
so `𝔶 + 𝔶' = −a₁AT − a₃T³` is formal.  The whole content is therefore
the single identity
`𝔶 · 𝔶' = −(A³ + a₂A²T² + a₄AT⁴ + a₆T⁶)`,
which is the Weierstrass relation `y·negY y = −(x³ + a₂x² + a₄x + a₆)`
at the point `Q ⊕ taut`, cleared by `T⁶`; in the coordinate ring it
follows from the two scalar relations
`coordY² + a₁·coordX·coordY + a₃·coordY = coordX³ + a₂coordX² + a₄coordX + a₆`
(from `AdjoinRoot.mk_self` on `W.polynomial`) and `W.Equation q₁ q₂`,
by `linear_combination` with polynomial cofactors.  Granting it,
`lineNumerator · lineNumeratorNeg = 𝔶𝔶' − Λ(𝔶 + 𝔶') + Λ²`
`= −(A³ + a₂A²T² + a₄AT⁴ + a₆T⁶) + Λ(a₁AT + a₃T³) + Λ²`,
which is precisely the `T`-homogenization (in `A`, `T²`) of
`W.addPolynomial x₁ y₁ ℓ = L² + (a₁X + a₃)L − (X³ + a₂X² + a₄X + a₆)`
evaluated at `X = A/T²`; mathlib's `addPolynomial_slope` factors that
cubic as `−(X − x₁)(X − x₂)(X − x₃)`, and the homogenization of the
factored form is exactly `−(A − x₁T²)(A − x₂T²)(A − x₃T²)`.  Practical
recipe: take `addPolynomial_slope h₁ h₂ hxy`, read off its four `X`-
coefficients with `Polynomial.coeff`/`Cubic`, and feed them to
`linear_combination` with the cofactors `T⁰, T², T⁴, T⁶` against the
expanded goal.  CAS-checkable in one `Singular`/`gp` line. -/
theorem lineNumerator_mul_lineNumeratorNeg {q₁ q₂ x₁ y₁ x₂ y₂ : F}
    (hq : W.Equation q₁ q₂) (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) *
        lineNumeratorNeg W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) =
      -(vertNumerator W q₁ q₂ x₁ *
        (vertNumerator W q₁ q₂ x₂ *
          vertNumerator W q₁ q₂ (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)))) := by
  sorry

/-- **L4-8 line-numerator sub-leaf (sorry): the comaximal assembly in the
COINCIDENT configurations — the whole residual coincidence zoo.**

The four separate memberships of `lineNumerator` in `I_Q³`, `I_{P⊖Q}`,
`I_{R⊖Q}`, `I_{⊖(P⊕R)⊖Q}` are all PROVEN (see
`lineNumerator_mem_prod_pointIdeal`), and in *general position* they
assemble into the product by pure comaximality
(`lineNumerator_mem_prod_of_mem_factors`).  What is left is exactly the
configurations where two of the four factors are supported at the SAME
point, so that separate memberships no longer suffice: `P = 2Q`,
`R = 2Q`, `⊖(P ⊕ R) = 2Q` (a translated point equals `Q`, so `n ∈ I_Q⁴`
is needed), `P = R` (then `P⊖Q = R⊖Q` and `n ∈ I_{P⊖Q}²` is needed),
`P = ⊖(P ⊕ R)`, `R = ⊖(P ⊕ R)`.  Note a translated point equal to `O`
is NOT a coincidence: its factor is `⊤`, and `isCoprime_pointIdeal`
covers it.

TWO ROUTES FOR THE ZOO.
* *Higher-order vanishing directly.*  `n ∈ I_S²` is a Taylor condition at
  `S`; a lift of `n` to `F[X][Y]` must lie in
  `⟨(X − α)², (X − α)(Y − β), (Y − β)², W.polynomial⟩`, which is a
  Gröbner cofactor certificate (Singular can produce it, `ring` verifies
  it) — but it is parametric in `q₁, q₂, x₁, y₁, ℓ`, hence large.
* *The non-vanishing squeeze* (recommended).  The multiplicity is forced
  by the already-known product identity: `⟨n⟩·⟨ñ⟩ = RHS·RHS'` exactly
  (`hmul` in `span_lineNumerator`), so at each maximal ideal the two
  vanishing orders SUM to the known total.  Hence `v_𝔭(n) = v_𝔭(RHS)`
  follows from `v_𝔭(ñ) = v_𝔭(RHS')`, and in every coincidence case the
  partner order is `0`, i.e. what has to be proven is a *non-vanishing*
  statement `ñ ∉ I_𝔭` — a single evaluation `≠ 0` (available through
  `coordEval` / `mem_pointIdeal_of_coordEval_eq_zero`), not a
  higher-order vanishing.  E.g. at `A = P ⊖ Q` one computes
  `ñ(A) = −(2y₁ + a₁x₁ + a₃)·(α − q₁)³`, nonzero exactly when `2P ≠ O`
  and `A ≠ ±Q`.  The cost is the valuation/unique-factorization layer for
  ideals of the Dedekind domain `F[W]`. -/
theorem lineNumerator_mem_prod_of_mem_factors_coincident (hΔ : W.Δ ≠ 0)
    {q₁ q₂ x₁ y₁ x₂ y₂ : F}
    (hq : W.Nonsingular q₁ q₂) (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂))
    (hcoin :
      (Point.some x₁ y₁ h₁ : W.Point) = .some q₁ q₂ hq + .some q₁ q₂ hq ∨
      (Point.some x₂ y₂ h₂ : W.Point) = .some q₁ q₂ hq + .some q₁ q₂ hq ∨
      (-(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) : W.Point) =
        .some q₁ q₂ hq + .some q₁ q₂ hq ∨
      (Point.some x₁ y₁ h₁ : W.Point) = .some x₂ y₂ h₂ ∨
      (Point.some x₁ y₁ h₁ : W.Point) =
        -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) ∨
      (Point.some x₂ y₂ h₂ : W.Point) =
        -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂))
    (hQ3 : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some q₁ q₂ hq) ^ 3)
    (hA : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq))
    (hB : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq))
    (hC : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) - .some q₁ q₂ hq)) :
    lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some q₁ q₂ hq) ^ 3 *
        (pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
          (pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
            pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) -
              .some q₁ q₂ hq))) := by
  sorry

/-- **L4-8 line-numerator sub-leaf: the comaximal assembly.**  The four
separate memberships of `lineNumerator` in `I_Q³`, `I_{P⊖Q}`, `I_{R⊖Q}`,
`I_{⊖(P⊕R)⊖Q}` combine into membership in the *product*.

In general position this is pure comaximality: distinct points have
coprime point ideals (`isCoprime_pointIdeal` — elementary, a difference
of `X`- or `Y`-classes is a nonzero constant, hence a unit), coprimality
passes to products and powers (`IsCoprime.mul_right`, `IsCoprime.pow_left`),
and for coprime ideals the product IS the intersection
(`Ideal.mul_eq_inf_of_isCoprime`), so the four memberships intersect into
the product membership.  The coincident configurations — where two
factors share a support point — are isolated in
`lineNumerator_mem_prod_of_mem_factors_coincident`. -/
theorem lineNumerator_mem_prod_of_mem_factors (hΔ : W.Δ ≠ 0)
    {q₁ q₂ x₁ y₁ x₂ y₂ : F}
    (hq : W.Nonsingular q₁ q₂) (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂))
    (hQ3 : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some q₁ q₂ hq) ^ 3)
    (hA : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq))
    (hB : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq))
    (hC : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) - .some q₁ q₂ hq)) :
    lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some q₁ q₂ hq) ^ 3 *
        (pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
          (pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
            pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) -
              .some q₁ q₂ hq))) := by
  by_cases hcoin :
      (Point.some x₁ y₁ h₁ : W.Point) = .some q₁ q₂ hq + .some q₁ q₂ hq ∨
      (Point.some x₂ y₂ h₂ : W.Point) = .some q₁ q₂ hq + .some q₁ q₂ hq ∨
      (-(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) : W.Point) =
        .some q₁ q₂ hq + .some q₁ q₂ hq ∨
      (Point.some x₁ y₁ h₁ : W.Point) = .some x₂ y₂ h₂ ∨
      (Point.some x₁ y₁ h₁ : W.Point) =
        -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) ∨
      (Point.some x₂ y₂ h₂ : W.Point) =
        -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂)
  · exact lineNumerator_mem_prod_of_mem_factors_coincident hΔ hq h₁ h₂ hxy hcoin
      hQ3 hA hB hC
  · have cQA := isCoprime_pointIdeal (W := W)
      (S := Point.some q₁ q₂ hq) (T := Point.some x₁ y₁ h₁ - Point.some q₁ q₂ hq)
      (by intro hc; rw [eq_comm, sub_eq_iff_eq_add] at hc
          exact hcoin (Or.inl hc))
    have cQB := isCoprime_pointIdeal (W := W)
      (S := Point.some q₁ q₂ hq) (T := Point.some x₂ y₂ h₂ - Point.some q₁ q₂ hq)
      (by intro hc; rw [eq_comm, sub_eq_iff_eq_add] at hc
          exact hcoin (Or.inr (Or.inl hc)))
    have cQC := isCoprime_pointIdeal (W := W)
      (S := Point.some q₁ q₂ hq)
      (T := -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) - Point.some q₁ q₂ hq)
      (by intro hc; rw [eq_comm, sub_eq_iff_eq_add] at hc
          exact hcoin (Or.inr (Or.inr (Or.inl hc))))
    have cAB := isCoprime_pointIdeal (W := W)
      (S := Point.some x₁ y₁ h₁ - Point.some q₁ q₂ hq)
      (T := Point.some x₂ y₂ h₂ - Point.some q₁ q₂ hq)
      (by intro hc; rw [sub_left_inj] at hc
          exact hcoin (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
    have cAC := isCoprime_pointIdeal (W := W)
      (S := Point.some x₁ y₁ h₁ - Point.some q₁ q₂ hq)
      (T := -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) - Point.some q₁ q₂ hq)
      (by intro hc; rw [sub_left_inj] at hc
          exact hcoin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))
    have cBC := isCoprime_pointIdeal (W := W)
      (S := Point.some x₂ y₂ h₂ - Point.some q₁ q₂ hq)
      (T := -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) - Point.some q₁ q₂ hq)
      (by intro hc; rw [sub_left_inj] at hc
          exact hcoin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))))
    have hBC : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
        pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
          pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) -
            .some q₁ q₂ hq) := by
      rw [Ideal.mul_eq_inf_of_isCoprime cBC]
      exact ⟨hB, hC⟩
    have hABC : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
        pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
          (pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
            pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) -
              .some q₁ q₂ hq)) := by
      rw [Ideal.mul_eq_inf_of_isCoprime (cAB.mul_right cAC)]
      exact ⟨hA, hBC⟩
    rw [Ideal.mul_eq_inf_of_isCoprime
      (cQA.mul_right (cQB.mul_right cQC)).pow_left]
    exact ⟨hQ3, hABC⟩

/-- **L4-8 line-numerator sub-leaf: membership of the line numerator in
its divisor ideal.**  `lineNumerator q₁ q₂ x₁ y₁ ℓ` lies in
`I_Q³ · I_{P⊖Q} · I_{R⊖Q} · I_{⊖(P⊕R)⊖Q}`.

This is the *inclusion* half of `span_lineNumerator`; the reverse is
supplied by the cancellation squeeze `span_eq_of_mem_of_span_mul_eq`, so
only membership has to be established here.

PROOF.  The four factor memberships are all proven:

* `I_Q³` is CERTIFICATE-FREE (`lineNumerator_mem_pointIdeal_pow_three`):
  with `T = coordX − q₁`, `U = coordY − q₂` the cleared `addX` is
  `A = U² + a₁UT − (a₂ + 2q₁)T² − T³ ∈ ⟨T, U⟩²`, and every summand of
  `lineNumerator` is `U·(A − q₁T²)`, a multiple of `T³`, or `(A − cT²)·T`.
* the three simple factors all come from the SINGLE lemma
  `lineNumerator_mem_pointIdeal_sub` (`n` vanishes at `P ⊖ Q`, for any
  slope), because `lineNumerator` depends only on the *line* and not on
  which of its points is used to write it down (`lineNumerator_congr`,
  fed by the cleared slope relation `slope_mul_sub` for `R` and by
  `negAddY = ℓ(x₃ − x₁) + y₁` for the third intersection point).  So no
  separate case analysis at `R` or at `⊖(P ⊕ R)`.

What remains is only the comaximal assembly of the four memberships into
the product, isolated as `lineNumerator_mem_prod_of_mem_factors` — that
is where the coincidence zoo lives, and nowhere else. -/
theorem lineNumerator_mem_prod_pointIdeal (hΔ : W.Δ ≠ 0) {q₁ q₂ x₁ y₁ x₂ y₂ : F}
    (hq : W.Nonsingular q₁ q₂) (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some q₁ q₂ hq) ^ 3 *
        (pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
          (pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
            pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) -
              .some q₁ q₂ hq))) := by
  have h₃ : W.Nonsingular (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
      (W.negY (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
        (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂))) :=
    (nonsingular_neg ..).mpr (nonsingular_add h₁ h₂ hxy)
  have hS : (-(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) : W.Point) =
      Point.some _ _ h₃ := by rw [Point.add_some hxy, Point.neg_some]
  have hQ3 := lineNumerator_mem_pointIdeal_pow_three hq x₁ y₁ (W.slope x₁ x₂ y₁ y₂)
  have hA := lineNumerator_mem_pointIdeal_sub hq h₁ (W.slope x₁ x₂ y₁ y₂)
  have hB : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) := by
    rw [lineNumerator_congr (slope_mul_sub h₁.left h₂.left hxy)]
    exact lineNumerator_mem_pointIdeal_sub hq h₂ _
  have hC : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) - .some q₁ q₂ hq) := by
    have hl3 : W.slope x₁ x₂ y₁ y₂ *
        (x₁ - W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) =
        y₁ - W.negY (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
          (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)) := by
      simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX]
      ring
    rw [hS, lineNumerator_congr hl3]
    exact lineNumerator_mem_pointIdeal_sub hq h₃ _
  exact lineNumerator_mem_prod_of_mem_factors hΔ hq h₁ h₂ hxy hQ3 hA hB hC

/-- **L4-8 line-numerator sub-leaf (PROVEN by involution transport):
membership of the conjugate line numerator in its divisor ideal.**  The
mirror image of `lineNumerator_mem_prod_pointIdeal`:
`lineNumeratorNeg q₁ q₂ x₁ y₁ ℓ` lies in
`I_Q³ · I_{⊖P⊖Q} · I_{⊖R⊖Q} · I_{(P⊕R)⊖Q}`.

The transport claim of the previous owner CHECKS OUT and no second case
analysis is needed.  The hyperelliptic involution `σ = involHom` of
`F[W]` (`coordX ↦ coordX`, `coordY ↦ negY(coordX, coordY)`) satisfies
`σ (lineNumerator W q₁ (negY q₁ q₂) x₁ y₁ ℓ) = lineNumeratorNeg W q₁ q₂ x₁ y₁ ℓ`
(`involHom_lineNumerator`, a pure ring identity: `σ` fixes the cleared
`addX` and flips `U = coordY − q₂` to `−(U + a₁T)`) and
`Ideal.map σ (I_S) = I_{⊖S}` (`map_involHom_pointIdeal`).  So applying
`lineNumerator_mem_prod_pointIdeal` at `⊖Q = (q₁, negY q₁ q₂)` and
pushing the membership through `Ideal.map σ` — which is multiplicative
(`Ideal.map_mul`, `Ideal.map_pow`) — turns the four factors
`I_{⊖Q}³ · I_{P⊖⊖Q} · I_{R⊖⊖Q} · I_{⊖(P⊕R)⊖⊖Q}` into exactly
`I_Q³ · I_{⊖P⊖Q} · I_{⊖R⊖Q} · I_{(P⊕R)⊖Q}`. -/
theorem lineNumeratorNeg_mem_prod_pointIdeal (hΔ : W.Δ ≠ 0) {q₁ q₂ x₁ y₁ x₂ y₂ : F}
    (hq : W.Nonsingular q₁ q₂) (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    lineNumeratorNeg W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some q₁ q₂ hq) ^ 3 *
        (pointIdeal W (-.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
          (pointIdeal W (-.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
            pointIdeal W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ -
              .some q₁ q₂ hq))) := by
  have hq' : W.Nonsingular q₁ (W.negY q₁ q₂) := (nonsingular_neg ..).mpr hq
  have hQ' : (Point.some q₁ (W.negY q₁ q₂) hq' : W.Point) =
      -(Point.some q₁ q₂ hq) := rfl
  have e1 : (-(Point.some q₁ (W.negY q₁ q₂) hq') : W.Point) =
      Point.some q₁ q₂ hq := by rw [hQ', neg_neg]
  have e2 : (-(Point.some x₁ y₁ h₁ - Point.some q₁ (W.negY q₁ q₂) hq') : W.Point) =
      -Point.some x₁ y₁ h₁ - Point.some q₁ q₂ hq := by rw [hQ']; abel
  have e3 : (-(Point.some x₂ y₂ h₂ - Point.some q₁ (W.negY q₁ q₂) hq') : W.Point) =
      -Point.some x₂ y₂ h₂ - Point.some q₁ q₂ hq := by rw [hQ']; abel
  have e4 : (-(-(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) -
      Point.some q₁ (W.negY q₁ q₂) hq') : W.Point) =
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ - Point.some q₁ q₂ hq := by
    rw [hQ']; abel
  have hmem := Ideal.mem_map_of_mem (involHom W)
    (lineNumerator_mem_prod_pointIdeal hΔ hq' h₁ h₂ hxy)
  rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_mul, Ideal.map_mul,
    map_involHom_pointIdeal, map_involHom_pointIdeal, map_involHom_pointIdeal,
    map_involHom_pointIdeal, involHom_lineNumerator, e1, e2, e3, e4] at hmem
  exact hmem

/-- **L4-8 numerator leaf (sorry): the divisor of the line
numerator.**  `lineNumerator q₁ q₂ x₁ y₁ ℓ` (at the group-law slope
`ℓ` of the pair `P = (x₁,y₁)`, `R = (x₂,y₂)`) spans
`I_Q³ · I_{P⊖Q} · I_{R⊖Q} · I_{⊖(P⊕R)⊖Q}` — its affine divisor is the
`⊖Q`-translate of the divisor `(P) + (R) + (⊖(P⊕R)) − 3(O)` of the
line through `P` and `R`, cleared by `3(Q)`.  CAS-checked numerically
(PARI/GP: `y² = x³ − x + 1`, `Q = (1,1)`, `P = (3,5)`, `R = (0,1)`:
vanishing at `Q` to third order and at the three translated points).
PROVEN, over three sub-leaves, by the **cancellation squeeze** rather
than by the colength recipe of `span_vertNumerator`'s docstring: the
partner element `lineNumeratorNeg` (the same cleared line value read at
the hyperelliptic conjugate `⊖Q ⊖ taut`) has the mirror divisor
`3(Q) + (⊖P⊖Q) + (⊖R⊖Q) + ((P⊕R)⊖Q)`, and the two numerators multiply to
minus the product of the three vertical numerators
(`lineNumerator_mul_lineNumeratorNeg`), whose spans are already known
from `span_vertNumerator`.  So `⟨n·ñ⟩ = (RHS)·(RHS')` *exactly*, both
`RHS` and `RHS'` are principal by `exists_span_eq_prod_pointIdeal` (both
multisets have zero sum), and the two memberships `n ∈ RHS`, `ñ ∈ RHS'`
then force the two cofactors to be units simultaneously
(`span_eq_of_mem_of_span_mul_eq`).  No norm degrees, no quotient
colengths, and — decisively — no coincidence zoo in the closing step:
every degeneracy makes both factors drop in lockstep.  The remaining
sorries are `lineNumerator_mul_lineNumeratorNeg` (one cleared
`addPolynomial` identity) and — inside the membership leaf, whose four
factor memberships are proven — the comaximal assembly
`lineNumerator_mem_prod_of_mem_factors`; the conjugate membership leaf
is proven from the plain one by involution transport. -/
theorem span_lineNumerator (hΔ : W.Δ ≠ 0) {q₁ q₂ x₁ y₁ x₂ y₂ : F}
    (hq : W.Nonsingular q₁ q₂) (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    Ideal.span {lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂)} =
      pointIdeal W (.some q₁ q₂ hq) ^ 3 *
        (pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
          (pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
            pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) -
              .some q₁ q₂ hq))) := by
  classical
  -- the third intersection point of the chord, `S = ⊖(P ⊕ R)`, is affine
  have h₃ : W.Nonsingular (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
      (W.negY (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
        (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂))) :=
    (nonsingular_neg ..).mpr (nonsingular_add h₁ h₂ hxy)
  have hS : -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) =
      Point.some _ _ h₃ := by
    rw [Point.add_some hxy, Point.neg_some]
  -- the two zero-sum divisors and their principal generators
  have hprod : ∃ a : W.CoordinateRing, a ≠ 0 ∧
      Ideal.span {a} =
        pointIdeal W (.some q₁ q₂ hq) ^ 3 *
          (pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
            (pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
              pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) -
                .some q₁ q₂ hq))) := by
    obtain ⟨a, ha0, ha⟩ := exists_span_eq_prod_pointIdeal
      ((.some q₁ q₂ hq) ::ₘ (.some q₁ q₂ hq) ::ₘ (.some q₁ q₂ hq) ::ₘ
        (.some x₁ y₁ h₁ - .some q₁ q₂ hq) ::ₘ
        (.some x₂ y₂ h₂ - .some q₁ q₂ hq) ::ₘ
        ({-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) - .some q₁ q₂ hq} :
          Multiset W.Point))
      (by simp only [Multiset.sum_cons, Multiset.sum_singleton]; abel)
    refine ⟨a, ha0, ?_⟩
    rw [ha]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
      Multiset.prod_singleton]
    ring
  have hprod' : ∃ a : W.CoordinateRing, a ≠ 0 ∧
      Ideal.span {a} =
        pointIdeal W (.some q₁ q₂ hq) ^ 3 *
          (pointIdeal W (-.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
            (pointIdeal W (-.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
              pointIdeal W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ -
                .some q₁ q₂ hq))) := by
    obtain ⟨a, ha0, ha⟩ := exists_span_eq_prod_pointIdeal
      ((.some q₁ q₂ hq) ::ₘ (.some q₁ q₂ hq) ::ₘ (.some q₁ q₂ hq) ::ₘ
        (-.some x₁ y₁ h₁ - .some q₁ q₂ hq) ::ₘ
        (-.some x₂ y₂ h₂ - .some q₁ q₂ hq) ::ₘ
        ({.some x₁ y₁ h₁ + .some x₂ y₂ h₂ - .some q₁ q₂ hq} :
          Multiset W.Point))
      (by simp only [Multiset.sum_cons, Multiset.sum_singleton]; abel)
    refine ⟨a, ha0, ?_⟩
    rw [ha]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
      Multiset.prod_singleton]
    ring
  -- the vertical numerator at the third intersection point
  have hv₃ : Ideal.span {vertNumerator W q₁ q₂
        (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))} =
      pointIdeal W (.some q₁ q₂ hq) ^ 2 *
        (pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) -
            .some q₁ q₂ hq) *
          pointIdeal W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ -
            .some q₁ q₂ hq)) := by
    have hv := span_vertNumerator hΔ hq h₃
    rwa [← hS, neg_neg] at hv
  -- the product of the two numerators is the product of the two divisors
  have hmul : Ideal.span {lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) *
        lineNumeratorNeg W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂)} =
      (pointIdeal W (.some q₁ q₂ hq) ^ 3 *
          (pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
            (pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
              pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) -
                .some q₁ q₂ hq)))) *
        (pointIdeal W (.some q₁ q₂ hq) ^ 3 *
          (pointIdeal W (-.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
            (pointIdeal W (-.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
              pointIdeal W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ -
                .some q₁ q₂ hq)))) := by
    rw [lineNumerator_mul_lineNumeratorNeg hq.left h₁.left h₂.left hxy,
      Ideal.span_singleton_neg, ← Ideal.span_singleton_mul_span_singleton,
      ← Ideal.span_singleton_mul_span_singleton,
      span_vertNumerator hΔ hq h₁, span_vertNumerator hΔ hq h₂, hv₃]
    ring
  exact span_eq_of_mem_of_span_mul_eq hprod hprod'
    (lineNumerator_mem_prod_pointIdeal hΔ hq h₁ h₂ hxy)
    (lineNumeratorNeg_mem_prod_pointIdeal hΔ hq h₁ h₂ hxy) hmul

/-- **L4-8 vertical brick: divisor transport of a vertical class.**
The translated vertical `τ_Q^*(X − x)` spans
`I_{P⊖Q} · I_{⊖P⊖Q} · I_{⊖Q}⁻²` for `P = (x, y)`: the `⊖Q`-translate
of the divisor `(P) + (⊖P) − 2(O)` of `X − x`. -/
theorem spanSingleton_pointEval_XClass (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xκ yκ : W.FunctionField} {hκ : (curveK W).Nonsingular xκ yκ}
    (hpt : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ)
    {x y : F} (h : W.Nonsingular x y) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hκ.left (CoordinateRing.XClass W x)) *
      (pointIdeal' W (-Q) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 2 =
    (pointIdeal' W (.some x y h - Q) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
      (pointIdeal' W (-.some x y h - Q) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
  cases Q with
  | zero =>
    -- at `Q = O` the evaluation is the canonical embedding and the
    -- statement is `XYIdeal_neg_mul`, coerced
    rw [← Point.zero_def] at hpt ⊢
    rw [show constPoint W 0 = 0 from rfl, zero_add] at hpt
    have hpt2 : WeierstrassCurve.Affine.Point.some (tautX W) (tautY W)
        (taut_nonsingular W hΔ) =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ := hpt
    injection hpt2 with hx hy
    subst hx
    subst hy
    have hτ : pointEval (constHom W) hκ.left =
        algebraMap W.CoordinateRing W.FunctionField := by
      refine coordinateRing_ringHom_ext (fun d => ?_) ?_ ?_
      · rw [pointEval_C]; rfl
      · rw [pointEval_X]; rfl
      · rw [pointEval_Y]; rfl
    rw [hτ, neg_zero, sub_zero, sub_zero,
      show pointIdeal' W (0 : W.Point) = 1 from rfl, Units.val_one, one_pow,
      mul_one, Point.neg_some, coe_pointIdeal', coe_pointIdeal',
      pointIdeal_some, pointIdeal_some, ← FractionalIdeal.coeIdeal_mul,
      ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_inj,
      mul_comm, CoordinateRing.XYIdeal_neg_mul h]
    rfl
  | some q₁ q₂ hq =>
    -- the generic translate is computed by the chord formula
    have hqx : constHom W q₁ ≠ tautX W := fun hc =>
      tautX_ne_constHom q₁ hc.symm
    have hne : ¬(constHom W q₁ = tautX W ∧
        constHom W q₂ = (curveK W).negY (tautX W) (tautY W)) :=
      fun hc => hqx hc.1
    have hadd := Point.add_some (W := curveK W)
      (h₁ := (W.map_nonsingular (constHom W).injective q₁ q₂).mpr hq)
      (h₂ := taut_nonsingular W hΔ) hne
    have hpt2 := hadd.symm.trans hpt
    injection hpt2 with hxκ hyκ
    have hsl : (curveK W).slope (constHom W q₁) (tautX W)
        (constHom W q₂) (tautY W) =
        (constHom W q₂ - tautY W) / (constHom W q₁ - tautX W) :=
      WeierstrassCurve.Affine.slope_of_X_ne hqx
    have hδ' : constHom W q₁ - tautX W ≠ 0 := sub_ne_zero.mpr hqx
    have ha₁ : (curveK W).a₁ = constHom W W.a₁ := rfl
    have ha₂ : (curveK W).a₂ = constHom W W.a₂ := rfl
    -- the translated vertical and the cleared numerator
    have hτX : pointEval (constHom W) hκ.left (CoordinateRing.XClass W x) =
        xκ - constHom W x := by
      rw [XClass_eq, map_sub]
      simp only [coordX, coordC]
      rw [pointEval_X, pointEval_C]
    have hXCq : algebraMap W.CoordinateRing W.FunctionField
        (CoordinateRing.XClass W q₁) = tautX W - constHom W q₁ := by
      rw [XClass_eq, map_sub, algebraMap_coordX, algebraMap_coordC]
    have hkey : (xκ - constHom W x) * (tautX W - constHom W q₁) ^ 2 =
        algebraMap W.CoordinateRing W.FunctionField
          (vertNumerator W q₁ q₂ x) := by
      rw [← hxκ, hsl]
      simp only [vertNumerator, map_sub, map_add, map_mul, map_pow,
        algebraMap_coordX, algebraMap_coordY, algebraMap_coordC,
        WeierstrassCurve.Affine.addX, ha₁, ha₂]
      field_simp [hδ']
      ring
    -- the vertical at `Q` spans `I_{⊖Q} · I_Q`
    have hVQ : (pointIdeal' W
          (-WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
        (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField
            (CoordinateRing.XClass W q₁)) := by
      rw [Point.neg_some, coe_pointIdeal', coe_pointIdeal', pointIdeal_some,
        pointIdeal_some, ← FractionalIdeal.coeIdeal_mul,
        CoordinateRing.XYIdeal_neg_mul hq,
        show CoordinateRing.XIdeal W q₁ =
          Ideal.span {CoordinateRing.XClass W q₁} from rfl,
        FractionalIdeal.coeIdeal_span_singleton]
    -- cancel `I_Q²` against the numerator's span
    have hu : IsUnit ((pointIdeal' W
          (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 2) :=
      (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq)).isUnit.pow 2
    apply hu.mul_left_cancel
    calc (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 2 *
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hκ.left (CoordinateRing.XClass W x)) *
          (pointIdeal' W (-WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 2)
        = FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hκ.left (CoordinateRing.XClass W x)) *
          (((pointIdeal' W
                (-WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
            (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) *
            ((pointIdeal' W
                (-WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
            (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField))) := by
          ring
      _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hκ.left (CoordinateRing.XClass W x)) *
          (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField
                (CoordinateRing.XClass W q₁)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField
                (CoordinateRing.XClass W q₁))) := by rw [hVQ]
      _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hκ.left (CoordinateRing.XClass W x) *
              (algebraMap W.CoordinateRing W.FunctionField
                  (CoordinateRing.XClass W q₁) *
                algebraMap W.CoordinateRing W.FunctionField
                  (CoordinateRing.XClass W q₁))) := by
          rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
            FractionalIdeal.spanSingleton_mul_spanSingleton]
      _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (algebraMap W.CoordinateRing W.FunctionField
              (vertNumerator W q₁ q₂ x)) := by
          rw [hτX, hXCq, show (xκ - constHom W x) *
              ((tautX W - constHom W q₁) * (tautX W - constHom W q₁)) =
            (xκ - constHom W x) * (tautX W - constHom W q₁) ^ 2 from by
              ring, hkey]
      _ = ((Ideal.span {vertNumerator W q₁ q₂ x} : Ideal W.CoordinateRing) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) :=
          (FractionalIdeal.coeIdeal_span_singleton _).symm
      _ = ((pointIdeal W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
              pointIdeal W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
              (pointIdeal W (WeierstrassCurve.Affine.Point.some x y h -
                  WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
                pointIdeal W (-WeierstrassCurve.Affine.Point.some x y h -
                  WeierstrassCurve.Affine.Point.some q₁ q₂ hq)) :
            Ideal W.CoordinateRing) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
          rw [span_vertNumerator hΔ hq h, pow_two]
      _ = (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 2 *
          ((pointIdeal' W (WeierstrassCurve.Affine.Point.some x y h -
              WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
          (pointIdeal' W (-WeierstrassCurve.Affine.Point.some x y h -
              WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) := by
          rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul,
            FractionalIdeal.coeIdeal_mul, ← coe_pointIdeal',
            ← coe_pointIdeal', ← coe_pointIdeal']
          ring

omit [IsAlgClosed F] in
/-- **The fractional span of a line**: the line through two affine
points `P`, `R` (not opposite) spans `I_P · I_R · I_{⊖(P⊕R)}` — from
`XYIdeal_mul_XYIdeal` and `XYIdeal_neg_mul` at the sum, cancelling the
invertible `I_{P⊕R}`. -/
lemma coe_YIdeal_line {x₁ y₁ x₂ y₂ : F} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    ((CoordinateRing.YIdeal W (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) :
        Ideal W.CoordinateRing) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
    (pointIdeal' W (.some x₁ y₁ h₁) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
      ((pointIdeal' W (.some x₂ y₂ h₂) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
        (pointIdeal' W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂)) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) := by
  have hadd := Point.add_some (h₁ := h₁) (h₂ := h₂) hxy
  have hMul := CoordinateRing.XYIdeal_mul_XYIdeal (W := W)
    h₁.left h₂.left hxy
  have hu : IsUnit ((pointIdeal' W (WeierstrassCurve.Affine.Point.some _ _
        (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy)) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) :=
    (pointIdeal' W _).isUnit
  apply hu.mul_left_cancel
  rw [show (-(WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) : W.Point) =
      WeierstrassCurve.Affine.Point.some
        (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
        (W.negY (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
          (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)))
        ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr
          (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy)) from by
      rw [hadd, Point.neg_some],
    coe_pointIdeal', coe_pointIdeal', coe_pointIdeal', coe_pointIdeal',
    pointIdeal_some, pointIdeal_some, pointIdeal_some, pointIdeal_some,
    ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
    ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_inj, mul_comm, ← hMul,
    ← CoordinateRing.XYIdeal_neg_mul
      (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy)]
  ring

/-- **L4-8 line brick: divisor transport of a line class.**  The
translated line `τ_Q^*(Y − (ℓ(X − x₁) + y₁))` (at the group-law slope
`ℓ` of the pair `P R`) spans
`I_{P⊖Q} · I_{R⊖Q} · I_{⊖(P⊕R)⊖Q} · I_{⊖Q}⁻³`: the `⊖Q`-translate of
the divisor `(P) + (R) + (⊖(P⊕R)) − 3(O)` of the line through `P` and
`R`. -/
theorem spanSingleton_pointEval_YClass (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xκ yκ : W.FunctionField} {hκ : (curveK W).Nonsingular xκ yκ}
    (hpt : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ)
    {x₁ y₁ x₂ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hκ.left
          (CoordinateRing.YClass W
            (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)))) *
      (pointIdeal' W (-Q) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 3 =
    (pointIdeal' W (.some x₁ y₁ h₁ - Q) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
      ((pointIdeal' W (.some x₂ y₂ h₂ - Q) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
        (pointIdeal' W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) - Q) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) := by
  cases Q with
  | zero =>
    -- at `Q = O` the evaluation is the canonical embedding and the
    -- statement is the fractional span of the line
    rw [← Point.zero_def] at hpt ⊢
    rw [show constPoint W 0 = 0 from rfl, zero_add] at hpt
    have hpt2 : WeierstrassCurve.Affine.Point.some (tautX W) (tautY W)
        (taut_nonsingular W hΔ) =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ := hpt
    injection hpt2 with hx hy
    subst hx
    subst hy
    have hτ : pointEval (constHom W) hκ.left =
        algebraMap W.CoordinateRing W.FunctionField := by
      refine coordinateRing_ringHom_ext (fun d => ?_) ?_ ?_
      · rw [pointEval_C]; rfl
      · rw [pointEval_X]; rfl
      · rw [pointEval_Y]; rfl
    rw [hτ, neg_zero, sub_zero, sub_zero, sub_zero,
      show pointIdeal' W (0 : W.Point) = 1 from rfl, Units.val_one, one_pow,
      mul_one, ← FractionalIdeal.coeIdeal_span_singleton,
      show Ideal.span {CoordinateRing.YClass W
          (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))} =
        CoordinateRing.YIdeal W
          (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) from rfl]
    exact coe_YIdeal_line h₁ h₂ hxy
  | some q₁ q₂ hq =>
    -- the generic translate is computed by the chord formula
    have hqx : constHom W q₁ ≠ tautX W := fun hc =>
      tautX_ne_constHom q₁ hc.symm
    have hne : ¬(constHom W q₁ = tautX W ∧
        constHom W q₂ = (curveK W).negY (tautX W) (tautY W)) :=
      fun hc => hqx hc.1
    have hadd := Point.add_some (W := curveK W)
      (h₁ := (W.map_nonsingular (constHom W).injective q₁ q₂).mpr hq)
      (h₂ := taut_nonsingular W hΔ) hne
    have hpt2 := hadd.symm.trans hpt
    injection hpt2 with hxκ hyκ
    have hsl : (curveK W).slope (constHom W q₁) (tautX W)
        (constHom W q₂) (tautY W) =
        (constHom W q₂ - tautY W) / (constHom W q₁ - tautX W) :=
      WeierstrassCurve.Affine.slope_of_X_ne hqx
    have hδ' : constHom W q₁ - tautX W ≠ 0 := sub_ne_zero.mpr hqx
    have ha₁ : (curveK W).a₁ = constHom W W.a₁ := rfl
    have ha₂ : (curveK W).a₂ = constHom W W.a₂ := rfl
    have ha₃ : (curveK W).a₃ = constHom W W.a₃ := rfl
    -- the translated line and the cleared numerator
    have hτY : pointEval (constHom W) hκ.left
        (CoordinateRing.YClass W
          (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))) =
        yκ - (constHom W (W.slope x₁ x₂ y₁ y₂) * (xκ - constHom W x₁) +
          constHom W y₁) := by
      rw [YClass_line_eq]
      simp only [map_sub, map_add, map_mul, coordX, coordY, coordC,
        pointEval_X, pointEval_Y, pointEval_C]
    have hXCq : algebraMap W.CoordinateRing W.FunctionField
        (CoordinateRing.XClass W q₁) = tautX W - constHom W q₁ := by
      rw [XClass_eq, map_sub, algebraMap_coordX, algebraMap_coordC]
    have hkey : (yκ - (constHom W (W.slope x₁ x₂ y₁ y₂) *
          (xκ - constHom W x₁) + constHom W y₁)) *
        (tautX W - constHom W q₁) ^ 3 =
        algebraMap W.CoordinateRing W.FunctionField
          (lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) := by
      rw [← hxκ, ← hyκ, hsl]
      simp only [lineNumerator, map_sub, map_add, map_mul, map_pow, map_neg,
        algebraMap_coordX, algebraMap_coordY, algebraMap_coordC,
        WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        ha₁, ha₂, ha₃]
      field_simp [hδ']
      ring
    -- the vertical at `Q` spans `I_{⊖Q} · I_Q`
    have hVQ : (pointIdeal' W
          (-WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
        (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField
            (CoordinateRing.XClass W q₁)) := by
      rw [Point.neg_some, coe_pointIdeal', coe_pointIdeal', pointIdeal_some,
        pointIdeal_some, ← FractionalIdeal.coeIdeal_mul,
        CoordinateRing.XYIdeal_neg_mul hq,
        show CoordinateRing.XIdeal W q₁ =
          Ideal.span {CoordinateRing.XClass W q₁} from rfl,
        FractionalIdeal.coeIdeal_span_singleton]
    -- cancel `I_Q³` against the numerator's span
    have hu : IsUnit ((pointIdeal' W
          (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 3) :=
      (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq)).isUnit.pow 3
    apply hu.mul_left_cancel
    calc (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 3 *
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hκ.left
              (CoordinateRing.YClass W
                (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)))) *
          (pointIdeal' W (-WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 3)
        = FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hκ.left
              (CoordinateRing.YClass W
                (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)))) *
          (((pointIdeal' W
                (-WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
            (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) *
            (((pointIdeal' W
                  (-WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
              (pointIdeal' W
                  (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) *
              ((pointIdeal' W
                  (-WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
              (pointIdeal' W
                  (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)))) := by
          ring
      _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hκ.left
              (CoordinateRing.YClass W
                (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)))) *
          (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField
                (CoordinateRing.XClass W q₁)) *
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (algebraMap W.CoordinateRing W.FunctionField
                  (CoordinateRing.XClass W q₁)) *
              FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (algebraMap W.CoordinateRing W.FunctionField
                  (CoordinateRing.XClass W q₁)))) := by rw [hVQ]
      _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hκ.left
              (CoordinateRing.YClass W
                (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))) *
              (algebraMap W.CoordinateRing W.FunctionField
                  (CoordinateRing.XClass W q₁) *
                (algebraMap W.CoordinateRing W.FunctionField
                    (CoordinateRing.XClass W q₁) *
                  algebraMap W.CoordinateRing W.FunctionField
                    (CoordinateRing.XClass W q₁)))) := by
          rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
            FractionalIdeal.spanSingleton_mul_spanSingleton,
            FractionalIdeal.spanSingleton_mul_spanSingleton]
      _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (algebraMap W.CoordinateRing W.FunctionField
              (lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂))) := by
          rw [hτY, hXCq, show (yκ - (constHom W (W.slope x₁ x₂ y₁ y₂) *
                (xκ - constHom W x₁) + constHom W y₁)) *
              ((tautX W - constHom W q₁) * ((tautX W - constHom W q₁) *
                (tautX W - constHom W q₁))) =
            (yκ - (constHom W (W.slope x₁ x₂ y₁ y₂) *
                (xκ - constHom W x₁) + constHom W y₁)) *
              (tautX W - constHom W q₁) ^ 3 from by ring, hkey]
      _ = ((Ideal.span {lineNumerator W q₁ q₂ x₁ y₁
              (W.slope x₁ x₂ y₁ y₂)} : Ideal W.CoordinateRing) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) :=
          (FractionalIdeal.coeIdeal_span_singleton _).symm
      _ = ((pointIdeal W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
              (pointIdeal W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
                pointIdeal W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq)) *
              (pointIdeal W (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ -
                  WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
                (pointIdeal W (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ -
                    WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
                  pointIdeal W
                    (-(WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
                      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) -
                      WeierstrassCurve.Affine.Point.some q₁ q₂ hq))) :
            Ideal W.CoordinateRing) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
          rw [span_lineNumerator hΔ hq h₁ h₂ hxy,
            show pointIdeal W (WeierstrassCurve.Affine.Point.some q₁ q₂
                hq) ^ 3 =
              pointIdeal W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
                (pointIdeal W
                    (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) *
                  pointIdeal W
                    (WeierstrassCurve.Affine.Point.some q₁ q₂ hq)) from by
              ring]
      _ = (pointIdeal' W (WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 3 *
          ((pointIdeal' W (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ -
              WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
          ((pointIdeal' W (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ -
              WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
          (pointIdeal' W (-(WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
              WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) -
              WeierstrassCurve.Affine.Point.some q₁ q₂ hq) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField))) := by
          rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul,
            FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul,
            FractionalIdeal.coeIdeal_mul, ← coe_pointIdeal',
            ← coe_pointIdeal', ← coe_pointIdeal', ← coe_pointIdeal']
          ring

/-- **L4-8 core (PROVEN over the two numerator leaves): divisor
transport along evaluation at a generic translate.**  Let `b ∈ F[W]`
generate the point-ideal product
of the affine divisor multiset `D` (so `div b = Σ_{R ∈ D} (R)` away
from `O`; the class-group argument of `mk_prod_pointIdeal'` then
forces `Σ_D R = O` in the group law), and let
`(xκ, yκ) = Q ⊕ taut` be the generic translate of `Q` on the
base-changed curve.  The evaluation `τ_Q^*(b) = b(Q ⊕ taut) ∈ K` is
the composite `b ∘ τ_Q`, whose divisor is the `⊖Q`-translate of the
full divisor `Σ_{R ∈ D} (R) − |D|·(O)` of `b`; as fractional ideals of
`F[W]`,
`(τ_Q^* b) · I_{⊖Q}^{|D|} = ∏_{R ∈ D} I_{R ⊖ Q}`.
The convention `I_O = 1` makes the statement invariant under
`O`-padding of `D`: an entry `R = Q` (translated into `O`) contributes
`1` on the right against one surviving `I_{⊖Q}`-factor on the left,
matching the vanishing of `b ∘ τ_Q` at infinity.

PROOF (Miller-style reduction to lines, implemented below).  Strong
induction on `card D`: an `O`-entry contributes `⊤`/`I_{⊖Q}` to the
two sides trivially; the empty divisor makes `b` a unit constant
(`coordinateRing_isUnit_eq_const`) of trivial span; a single affine
point is impossible (its class is nontrivial —
`ClassGroup.mk_eq_one_of_coe_ideal` + `toClass_eq_zero`); and a pair
of affine points at the head is peeled off by the group-law ideal
calculus — `XYIdeal_neg_mul` extracts a vertical class `X − x` from
an opposite pair, `XYIdeal_mul_XYIdeal` trades a generic pair for the
sum point at the cost of a line class `Y − (λ(X − x₁) + y₁)` — with
`exists_span_factor` dividing the extracted class out of `b` and the
transported spans of the two explicit classes supplied by the bricks
`spanSingleton_pointEval_XClass` / `spanSingleton_pointEval_YClass`
(both PROVEN over the numerator leaves `span_vertNumerator` /
`span_lineNumerator`, the remaining sorries of this stage).  See
HLEG-NOTES.md §4(B), stage L4-8. -/
theorem spanSingleton_pointEval_translate (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xκ yκ : W.FunctionField} {hκ : (curveK W).Nonsingular xκ yκ}
    (hpt : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ)
    {b : W.CoordinateRing} (hb : b ≠ 0) {D : Multiset W.Point}
    (hspan : Ideal.span {b} = (D.map (pointIdeal W)).prod) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hκ.left b) *
      (pointIdeal' W (-Q) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
          Multiset.card D =
    (D.map fun R => (pointIdeal' W (R - Q) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
  classical
  suffices H : ∀ (n : ℕ) (E : Multiset W.Point), Multiset.card E = n →
      ∀ a : W.CoordinateRing, a ≠ 0 →
      Ideal.span {a} = (E.map (pointIdeal W)).prod →
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hκ.left a) *
        (pointIdeal' W (-Q) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
            Multiset.card E =
      (E.map fun R => (pointIdeal' W (R - Q) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod by
    exact H (Multiset.card D) D rfl b hb hspan
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro E hcard a ha haspan
  by_cases h0 : (0 : W.Point) ∈ E
  · -- an `O` entry contributes `⊤` to the span and `I_{⊖Q}` to both sides
    obtain ⟨E', rfl⟩ := Multiset.exists_cons_of_mem h0
    have hlt : Multiset.card E' < n := by
      rw [← hcard, Multiset.card_cons]; omega
    have haspan' : Ideal.span {a} = (E'.map (pointIdeal W)).prod := by
      rwa [Multiset.map_cons, Multiset.prod_cons,
        show pointIdeal W 0 = ⊤ from rfl, Ideal.top_mul] at haspan
    have hIH := IH (Multiset.card E') hlt E' rfl a ha haspan'
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ,
      ← mul_assoc, hIH, zero_sub, mul_comm]
  · by_cases hE0 : E = 0
    · -- empty divisor: `a` is a unit, hence a nonzero constant
      subst hE0
      rw [show Multiset.card (0 : Multiset W.Point) = 0 from rfl, pow_zero,
        mul_one, Multiset.map_zero, Multiset.prod_zero]
      have hatop : Ideal.span {a} = ⊤ := by
        rw [haspan, Multiset.map_zero, Multiset.prod_zero, Ideal.one_eq_top]
      obtain ⟨c, -, rfl⟩ :=
        coordinateRing_isUnit_eq_const (Ideal.span_singleton_eq_top.mp hatop)
      rw [pointEval_C,
        show constHom W c = algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (Polynomial.C (Polynomial.C c))) from rfl,
        ← FractionalIdeal.coeIdeal_span_singleton, hatop,
        FractionalIdeal.coeIdeal_top]
    · obtain ⟨P, hP⟩ := Multiset.exists_mem_of_ne_zero hE0
      obtain ⟨E₁, rfl⟩ := Multiset.exists_cons_of_mem hP
      rcases P with _ | ⟨x₁, y₁, h₁⟩
      · exact absurd (Multiset.mem_cons_self _ _) h0
      by_cases hE₁0 : E₁ = 0
      · -- a single affine point cannot span a principal ideal
        exfalso
        subst hE₁0
        have haspan1 : Ideal.span {a} =
            CoordinateRing.XYIdeal W x₁ (Polynomial.C y₁) := by
          simpa using haspan
        have htc : Point.toClass (W := W)
            (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0 := by
          rw [Point.toClass_some]
          exact (ClassGroup.mk_eq_one_of_coe_ideal
            (CoordinateRing.XYIdeal'_eq h₁)).mpr ⟨a, ha, haspan1.symm⟩
        exact Point.some_ne_zero h₁ ((Point.toClass_eq_zero _).mp htc)
      obtain ⟨R, hR⟩ := Multiset.exists_mem_of_ne_zero hE₁0
      obtain ⟨E₂, rfl⟩ := Multiset.exists_cons_of_mem hR
      rcases R with _ | ⟨x₂, y₂, h₂⟩
      · exact absurd
          (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)) h0
      rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
        Multiset.prod_cons, pointIdeal_some, pointIdeal_some] at haspan
      have hτinj := pointEval_injective hΔ hpt
      have hτne : ∀ z : W.CoordinateRing, z ≠ 0 →
          pointEval (constHom W) hκ.left z ≠ 0 := fun z hz h0' =>
        hz (hτinj (by rw [h0', map_zero]))
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
      · -- opposite points at the head: peel a vertical `X − x`
        obtain ⟨rfl, rfl⟩ := hxy
        rw [← mul_assoc, CoordinateRing.XYIdeal_neg_mul h₂,
          show CoordinateRing.XIdeal W x₁ =
            Ideal.span {CoordinateRing.XClass W x₁} from rfl] at haspan
        obtain ⟨a', rfl, haspan'⟩ :=
          exists_span_factor (CoordinateRing.XClass_ne_zero x₁) haspan
        have ha' : a' ≠ 0 := right_ne_zero_of_mul ha
        have hlt : Multiset.card E₂ < n := by
          rw [← hcard, Multiset.card_cons, Multiset.card_cons]; omega
        have hIH := IH (Multiset.card E₂) hlt E₂ rfl a' ha' haspan'
        have hV := spanSingleton_pointEval_XClass hΔ hpt h₂
        rw [Multiset.card_cons, Multiset.card_cons, Multiset.map_cons,
          Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, map_mul,
          ← FractionalIdeal.spanSingleton_mul_spanSingleton,
          show (WeierstrassCurve.Affine.Point.some x₁ (W.negY x₁ y₂) h₁ :
              W.Point) = -WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ from
            (Point.neg_some h₂).symm]
        calc FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left
                (CoordinateRing.XClass W x₁)) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left a') *
            (pointIdeal' W (-Q) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                (Multiset.card E₂ + 1 + 1)
            = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hκ.left
                  (CoordinateRing.XClass W x₁)) *
                (pointIdeal' W (-Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 2) *
              (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                  (pointEval (constHom W) hκ.left a') *
                (pointIdeal' W (-Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                    Multiset.card E₂) := by ring
          _ = ((pointIdeal' W
                  (WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ - Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
                (pointIdeal' W
                    (-WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ - Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) *
              (E₂.map fun R => (pointIdeal' W (R - Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
            rw [hV, hIH]
          _ = (pointIdeal' W
                (-WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ - Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
              ((pointIdeal' W
                  (WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ - Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
                (E₂.map fun R => (pointIdeal' W (R - Q) :
                  FractionalIdeal W.CoordinateRing⁰
                    W.FunctionField)).prod) := by ring
      · -- generic pair at the head: peel the line through the two points
        have hadd := Point.add_some (h₁ := h₁) (h₂ := h₂) hxy
        have hMul := CoordinateRing.XYIdeal_mul_XYIdeal (W := W)
          h₁.left h₂.left hxy
        have haspan2 : Ideal.span
            {a * CoordinateRing.XClass W
              (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))} =
            Ideal.span {CoordinateRing.YClass W
              (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))} *
            ((WeierstrassCurve.Affine.Point.some _ _
                (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy) ::ₘ
                E₂).map (pointIdeal W)).prod := by
          rw [← Ideal.span_singleton_mul_span_singleton, haspan,
            Multiset.map_cons, Multiset.prod_cons, pointIdeal_some]
          calc (CoordinateRing.XYIdeal W x₁ (Polynomial.C y₁) *
                (CoordinateRing.XYIdeal W x₂ (Polynomial.C y₂) *
                  (E₂.map (pointIdeal W)).prod)) *
              Ideal.span {CoordinateRing.XClass W
                (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))}
              = (CoordinateRing.XIdeal W
                  (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) *
                  (CoordinateRing.XYIdeal W x₁ (Polynomial.C y₁) *
                    CoordinateRing.XYIdeal W x₂ (Polynomial.C y₂))) *
                (E₂.map (pointIdeal W)).prod := by
                rw [show Ideal.span {CoordinateRing.XClass W
                    (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))} =
                  CoordinateRing.XIdeal W
                    (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) from rfl]
                ring
            _ = (CoordinateRing.YIdeal W
                  (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) *
                  CoordinateRing.XYIdeal W
                    (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
                    (Polynomial.C (W.addY x₁ x₂ y₁
                      (W.slope x₁ x₂ y₁ y₂)))) *
                (E₂.map (pointIdeal W)).prod := by rw [hMul]
            _ = Ideal.span {CoordinateRing.YClass W
                  (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))} *
                (CoordinateRing.XYIdeal W
                    (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
                    (Polynomial.C (W.addY x₁ x₂ y₁
                      (W.slope x₁ x₂ y₁ y₂))) *
                  (E₂.map (pointIdeal W)).prod) := by
                rw [show CoordinateRing.YIdeal W
                    (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) =
                  Ideal.span {CoordinateRing.YClass W
                    (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))} from rfl]
                ring
        obtain ⟨a', hfact, haspan'⟩ :=
          exists_span_factor (CoordinateRing.YClass_ne_zero _) haspan2
        have ha' : a' ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hfact
          exact mul_ne_zero ha
            (CoordinateRing.XClass_ne_zero
              (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))) hfact
        have hlt : Multiset.card
            (WeierstrassCurve.Affine.Point.some _ _
              (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy) ::ₘ E₂) <
            n := by
          rw [← hcard, Multiset.card_cons, Multiset.card_cons,
            Multiset.card_cons]
          omega
        have hIH := IH _ hlt _ rfl a' ha' haspan'
        rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons,
          ← hadd] at hIH
        have hV := spanSingleton_pointEval_XClass hΔ hpt
          (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy)
        rw [← hadd] at hV
        have hL := spanSingleton_pointEval_YClass hΔ hpt h₁ h₂ hxy
        have hsS : FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left
                (CoordinateRing.XClass W
                  (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)))) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left a) =
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left
                (CoordinateRing.YClass W
                  (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)))) *
            FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left a') := by
          rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
            FractionalIdeal.spanSingleton_mul_spanSingleton, ← map_mul,
            ← map_mul, mul_comm
              (CoordinateRing.XClass W
                (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))) a, hfact]
        rw [Multiset.card_cons, Multiset.card_cons, Multiset.map_cons,
          Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons]
        have hu : IsUnit (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left
                (CoordinateRing.XClass W
                  (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)))) *
            (pointIdeal' W (-Q) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 2) :=
          (isUnit_spanSingleton_of_ne_zero
            (hτne _ (CoordinateRing.XClass_ne_zero
              (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))))).mul
            ((pointIdeal' W (-Q)).isUnit.pow 2)
        apply hu.mul_left_cancel
        calc (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hκ.left
                (CoordinateRing.XClass W
                  (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)))) *
            (pointIdeal' W (-Q) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 2) *
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hκ.left a) *
              (pointIdeal' W (-Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                  (Multiset.card E₂ + 1 + 1))
            = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                  (pointEval (constHom W) hκ.left
                    (CoordinateRing.XClass W
                      (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)))) *
                FractionalIdeal.spanSingleton W.CoordinateRing⁰
                  (pointEval (constHom W) hκ.left a)) *
              ((pointIdeal' W (-Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 3 *
                (pointIdeal' W (-Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                    (Multiset.card E₂ + 1)) := by ring
          _ = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                  (pointEval (constHom W) hκ.left
                    (CoordinateRing.YClass W
                      (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)))) *
                FractionalIdeal.spanSingleton W.CoordinateRing⁰
                  (pointEval (constHom W) hκ.left a')) *
              ((pointIdeal' W (-Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 3 *
                (pointIdeal' W (-Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                    (Multiset.card E₂ + 1)) := by rw [hsS]
          _ = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                  (pointEval (constHom W) hκ.left
                    (CoordinateRing.YClass W
                      (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)))) *
                (pointIdeal' W (-Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 3) *
              (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                  (pointEval (constHom W) hκ.left a') *
                (pointIdeal' W (-Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
                    (Multiset.card E₂ + 1)) := by ring
          _ = ((pointIdeal' W
                  (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ - Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
                ((pointIdeal' W
                    (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ - Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
                  (pointIdeal' W
                      (-(WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
                        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) - Q) :
                    FractionalIdeal W.CoordinateRing⁰ W.FunctionField))) *
              ((pointIdeal' W
                  ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
                    WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) - Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
                (E₂.map fun R => (pointIdeal' W (R - Q) :
                  FractionalIdeal W.CoordinateRing⁰
                    W.FunctionField)).prod) := by
            rw [hL, hIH]
          _ = ((pointIdeal' W
                  ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
                    WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) - Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
                (pointIdeal' W
                    (-(WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
                      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) - Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) *
              ((pointIdeal' W
                  (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ - Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
                ((pointIdeal' W
                    (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ - Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
                  (E₂.map fun R => (pointIdeal' W (R - Q) :
                    FractionalIdeal W.CoordinateRing⁰
                      W.FunctionField)).prod)) := by ring
          _ = (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hκ.left
                  (CoordinateRing.XClass W
                    (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)))) *
              (pointIdeal' W (-Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ 2) *
              ((pointIdeal' W
                  (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ - Q) :
                FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
                ((pointIdeal' W
                    (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ - Q) :
                  FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
                  (E₂.map fun R => (pointIdeal' W (R - Q) :
                    FractionalIdeal W.CoordinateRing⁰
                      W.FunctionField)).prod)) := by
            rw [← hV]

omit [Fact p.Prime] in
/-- **L4-8: the translation character of the Miller generator**
(PROVEN over the transport brick `spanSingleton_pointEval_translate`).
Let `val : ι → W.Point` enumerate the `p`-torsion subgroup, `T'` a
`p`-division point of `P`, and `a` a generator of the point-ideal
product of the zero-sum divisor multiset `Σ_i (T'⊕κᵢ) + (⊖κᵢ)`, so
that `g := a / ∏ (X − x_κ)` has divisor
`Σ_κ (T'⊕κ) − (κ) = [p]^*((P) − (O))`.  For a torsion index `i₀` with
`κ₀ ⊕ taut = (xκ, yκ)`, composition with the translation `τ_{κ₀}` is
evaluation at `(xκ, yκ)` (`pointEval`), and the ratio
`χ(κ₀) = τ_{κ₀}^*(g)/g` has divisor
`τ_{−κ₀}(div g) − div g = 0` — by the transport brick and reindexing
the two sums along the torsion-translation bijections — hence is a
nonzero CONSTANT `c ∈ F` (units of the coordinate ring are constants:
`coordinateRing_isUnit_eq_const`).  `c^p = 1` because the extension
`σ` of `τ_{κ₀}^*` to the function field satisfies `σⁿ(g) = cⁿ·g` by
iteration (`σ` fixes constants), while `σ^p` fixes the whole
coordinate ring: the `n`-th iterate of the tautological point is
`(n•κ₀) ⊕ taut` (`endoMap` induction), and `p•κ₀ = O`.  The
conclusion is stated multiplied out in `K` (no field extension of the
evaluation map needed): `τ(a)·v = c·a·τ(v)` for `v = ∏ (X − x_κ)`,
together with the nonvanishing of `τ(a)` and `τ(v)`
(`pointEval_injective`).  See HLEG-NOTES.md §4(B), stages L4-4..8. -/
theorem exists_translationChar {ι : Type*} [Fintype ι] {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (_hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (_hcard : Fintype.card ι = p ^ 2)
    {P T' : W.Point} (_hT : (p : ℤ) • T' = P) (_hPtor : (p : ℤ) • P = 0)
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
  classical
  -- ── the vertical denominator and its images are nonzero
  have hv0 : enumVertical W val ≠ 0 := by
    refine Multiset.prod_ne_zero fun h0 => ?_
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp h0
    cases hvi : val i with
    | zero => rw [hvi] at hi; simp [pointXClass] at hi
    | some x y h => rw [hvi] at hi; exact CoordinateRing.XClass_ne_zero x hi
  have hτinj := pointEval_injective hΔ hpt
  have hτa : pointEval (constHom W) hκ.left a ≠ 0 := fun h0 =>
    ha (hτinj (by rw [h0, map_zero]))
  have hτv : pointEval (constHom W) hκ.left (enumVertical W val) ≠ 0 :=
    fun h0 => hv0 (hτinj (by rw [h0, map_zero]))
  have haa0 : algebraMap W.CoordinateRing W.FunctionField a ≠ 0 := fun h0 =>
    ha ((map_eq_zero_iff _
      (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mp h0)
  have hva0 : algebraMap W.CoordinateRing W.FunctionField
      (enumVertical W val) ≠ 0 := fun h0 =>
    hv0 ((map_eq_zero_iff _
      (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mp h0)
  -- ── divisor transport for the generator and the vertical denominator
  set Da := (Finset.univ.val.map fun i => T' + val i) +
    Finset.univ.val.map fun i => -val i with hDadef
  set Dv := (Finset.univ.val.map fun i => val i) +
    Finset.univ.val.map fun i => -val i with hDvdef
  have hVspan : Ideal.span {enumVertical W val} =
      (Dv.map (pointIdeal W)).prod := by
    rw [hDvdef]
    exact span_enumVertical (W := W) val
  have hbrickA := spanSingleton_pointEval_translate hΔ hpt ha hspan
  have hbrickV := spanSingleton_pointEval_translate hΔ hpt hv0 hVspan
  -- ── the translated divisor multisets are the originals (reindexing
  --    by the torsion-translation bijections)
  have hf₁ex : ∀ i : ι, ∃ j, val j = val i - val i₀ := fun i =>
    hval_surj _ (by rw [smul_sub, hval_tor, hval_tor, sub_zero])
  choose f₁ hf₁ using hf₁ex
  have hf₁inj : Function.Injective f₁ := by
    intro i j hij
    apply hval_inj
    have h1 : val i - val i₀ = val j - val i₀ := by
      rw [← hf₁ i, ← hf₁ j, hij]
    have h2 := congrArg (fun z => z + val i₀) h1
    simpa using h2
  let e₁ : ι ≃ ι :=
    Equiv.ofBijective f₁ (Finite.injective_iff_bijective.mp hf₁inj)
  have hf₂ex : ∀ i : ι, ∃ j, val j = val i + val i₀ := fun i =>
    hval_surj _ (by rw [smul_add, hval_tor, hval_tor, add_zero])
  choose f₂ hf₂ using hf₂ex
  have hf₂inj : Function.Injective f₂ := by
    intro i j hij
    apply hval_inj
    have h1 : val i + val i₀ = val j + val i₀ := by
      rw [← hf₂ i, ← hf₂ j, hij]
    have h2 := congrArg (fun z => z - val i₀) h1
    simpa using h2
  let e₂ : ι ≃ ι :=
    Equiv.ofBijective f₂ (Finite.injective_iff_bijective.mp hf₂inj)
  have hnegpiece : (Finset.univ.val.map fun i => -val i).map
      (fun R => R - val i₀) = Finset.univ.val.map fun i => -val i := by
    calc (Finset.univ.val.map fun i => -val i).map (fun R => R - val i₀)
        = Finset.univ.val.map (fun i => -val i - val i₀) :=
          Multiset.map_map _ _ _
      _ = Finset.univ.val.map (fun i => -val (e₂ i)) :=
          Multiset.map_congr rfl fun i _ => by
            rw [show val (e₂ i) = val i + val i₀ from hf₂ i]
            abel
      _ = Finset.univ.val.map fun i => -val i :=
          map_univ_comp_equiv e₂ fun j => -val j
  have hpospiece : (Finset.univ.val.map fun i => T' + val i).map
      (fun R => R - val i₀) = Finset.univ.val.map fun i => T' + val i :=
    calc (Finset.univ.val.map fun i => T' + val i).map (fun R => R - val i₀)
        = Finset.univ.val.map (fun i => T' + val i - val i₀) :=
          Multiset.map_map _ _ _
      _ = Finset.univ.val.map (fun i => T' + val (e₁ i)) :=
          Multiset.map_congr rfl fun i _ => by
            rw [show val (e₁ i) = val i - val i₀ from hf₁ i]
            abel
      _ = Finset.univ.val.map fun i => T' + val i :=
          map_univ_comp_equiv e₁ fun j => T' + val j
  have hvalpiece : (Finset.univ.val.map fun i => val i).map
      (fun R => R - val i₀) = Finset.univ.val.map fun i => val i :=
    calc (Finset.univ.val.map fun i => val i).map (fun R => R - val i₀)
        = Finset.univ.val.map (fun i => val i - val i₀) :=
          Multiset.map_map _ _ _
      _ = Finset.univ.val.map (fun i => val (e₁ i)) :=
          Multiset.map_congr rfl fun i _ => (hf₁ i).symm
      _ = Finset.univ.val.map fun i => val i :=
          map_univ_comp_equiv e₁ fun j => val j
  have hDa : Da.map (fun R => R - val i₀) = Da := by
    rw [hDadef, Multiset.map_add, hpospiece, hnegpiece]
  have hDv : Dv.map (fun R => R - val i₀) = Dv := by
    rw [hDvdef, Multiset.map_add, hvalpiece, hnegpiece]
  -- ── the two spanSingleton comparisons
  have hshiftA : (Da.map fun R => (pointIdeal' W (R - val i₀) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField a) := by
    have hmm : ((Da.map (fun R => R - val i₀)).map fun R =>
        (pointIdeal' W R :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) =
        Da.map fun R => (pointIdeal' W (R - val i₀) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) :=
      Multiset.map_map _ _ _
    rw [← hmm, hDa]
    exact prod_coe_pointIdeal'_eq_spanSingleton hspan
  have hshiftV : (Dv.map fun R => (pointIdeal' W (R - val i₀) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) := by
    have hmm : ((Dv.map (fun R => R - val i₀)).map fun R =>
        (pointIdeal' W R :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) =
        Dv.map fun R => (pointIdeal' W (R - val i₀) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) :=
      Multiset.map_map _ _ _
    rw [← hmm, hDv]
    exact prod_coe_pointIdeal'_eq_spanSingleton hVspan
  have hA := hbrickA.trans hshiftA
  have hV := hbrickV.trans hshiftV
  have hcards : Multiset.card Da = Multiset.card Dv := by
    rw [hDadef, hDvdef]
    simp
  have hXsv : FractionalIdeal.spanSingleton W.CoordinateRing⁰
      (pointEval (constHom W) hκ.left a *
        algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hκ.left (enumVertical W val) *
          algebraMap W.CoordinateRing W.FunctionField a) := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← hA, ← hV, hcards]
    ring
  -- ── unit extraction: the two products differ by a unit constant
  have hmem1 : pointEval (constHom W) hκ.left a *
      algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) ∈
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hκ.left (enumVertical W val) *
          algebraMap W.CoordinateRing W.FunctionField a) := by
    rw [← hXsv]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  rw [FractionalIdeal.mem_spanSingleton] at hmem1
  obtain ⟨z, hz⟩ := hmem1
  have hmem2 : pointEval (constHom W) hκ.left (enumVertical W val) *
      algebraMap W.CoordinateRing W.FunctionField a ∈
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hκ.left a *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) := by
    rw [hXsv]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  rw [FractionalIdeal.mem_spanSingleton] at hmem2
  obtain ⟨w, hw⟩ := hmem2
  have h7 : (z * w) • (pointEval (constHom W) hκ.left a *
      algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) =
      pointEval (constHom W) hκ.left a *
        algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) := by
    rw [mul_smul, hw, hz]
  have h8 : algebraMap W.CoordinateRing W.FunctionField (z * w) = 1 := by
    rw [Algebra.smul_def] at h7
    have h10 : (algebraMap W.CoordinateRing W.FunctionField (z * w) - 1) *
        (pointEval (constHom W) hκ.left a *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) =
        0 := by
      linear_combination h7
    rcases mul_eq_zero.mp h10 with h11 | h11
    · exact sub_eq_zero.mp h11
    · exact absurd h11 (mul_ne_zero hτa hva0)
  have hzw : z * w = 1 := by
    apply IsFractionRing.injective W.CoordinateRing W.FunctionField
    rw [h8, map_one]
  obtain ⟨c, hc0, hcz⟩ :=
    coordinateRing_isUnit_eq_const (IsUnit.of_mul_eq_one w hzw)
  -- ── the character equation
  have hmain : pointEval (constHom W) hκ.left a *
      algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
      constHom W c * algebraMap W.CoordinateRing W.FunctionField a *
        pointEval (constHom W) hκ.left (enumVertical W val) := by
    rw [← hz, hcz, Algebra.smul_def]
    show constHom W c *
        (pointEval (constHom W) hκ.left (enumVertical W val) *
          algebraMap W.CoordinateRing W.FunctionField a) =
      constHom W c * algebraMap W.CoordinateRing W.FunctionField a *
        pointEval (constHom W) hκ.left (enumVertical W val)
    ring
  refine ⟨c, ?_, hτa, hτv, hmain⟩
  -- ── c^p = 1: iterate the extension σ of τ to the function field;
  --    σ^p fixes the coordinate ring since p•κ₀ = O
  set σ : W.FunctionField →+* W.FunctionField := IsFractionRing.lift hτinj
  have hσalg : ∀ z' : W.CoordinateRing,
      σ (algebraMap W.CoordinateRing W.FunctionField z') =
        pointEval (constHom W) hκ.left z' := fun z' =>
    IsFractionRing.lift_algebraMap hτinj z'
  have hσc : ∀ d : F, σ (constHom W d) = constHom W d := fun d => by
    have h1 : constHom W d = algebraMap W.CoordinateRing W.FunctionField
        (CoordinateRing.mk W (Polynomial.C (Polynomial.C d))) := rfl
    rw [h1, hσalg, pointEval_C]
    exact h1
  let σpow : ℕ → (W.FunctionField →+* W.FunctionField) := fun n =>
    Nat.rec (RingHom.id _) (fun _ ih => σ.comp ih) n
  have hσpow_c : ∀ (n : ℕ) (d : F), σpow n (constHom W d) = constHom W d := by
    intro n d
    induction n with
    | zero => rfl
    | succ n ihn =>
      show σ (σpow n (constHom W d)) = constHom W d
      rw [ihn, hσc]
  have hcv : (curveK W).map σ = W.map (constHom W) := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;> exact hσc _
  have hend_taut : endoMap hcv (tautPoint W hΔ) =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ := by
    have hx : σ (tautX W) = xκ := by
      have h1 : tautX W = algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (Polynomial.C Polynomial.X)) := rfl
      rw [h1, hσalg, pointEval_X]
    have hy : σ (tautY W) = yκ := by
      have h1 : tautY W = algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W Polynomial.X) := rfl
      rw [h1, hσalg, pointEval_Y]
    rw [show tautPoint W hΔ = WeierstrassCurve.Affine.Point.some (tautX W)
        (tautY W) (taut_nonsingular W hΔ) from rfl, endoMap_some]
    exact point_some_congr hx hy
  have hend_const : ∀ R : W.Point,
      endoMap hcv (constPoint W R) = constPoint W R := by
    intro R
    cases R with
    | zero => rfl
    | some x y h => exact point_some_congr (hσc x) (hσc y)
  have hiter : ∀ n : ℕ, ∃ hn : (curveK W).Nonsingular
      (σpow n (tautX W)) (σpow n (tautY W)),
      WeierstrassCurve.Affine.Point.some (σpow n (tautX W))
        (σpow n (tautY W)) hn =
        constPoint W ((n : ℤ) • val i₀) + tautPoint W hΔ := by
    intro n
    induction n with
    | zero =>
      refine ⟨taut_nonsingular W hΔ, ?_⟩
      rw [show ((0 : ℕ) : ℤ) • val i₀ = (0 : W.Point) from by
          rw [Nat.cast_zero, zero_zsmul],
        show constPoint W (0 : W.Point) = 0 from rfl, zero_add]
      rfl
    | succ n ihn =>
      obtain ⟨hn, hEq⟩ := ihn
      have h2 := congrArg (endoMap hcv) hEq
      rw [endoMap_some, endoMap_add hcv, hend_const, hend_taut, ← hpt] at h2
      refine ⟨endo_nonsingular hcv hn, h2.trans ?_⟩
      rw [← add_assoc,
        show constPoint W ((n : ℤ) • val i₀) + constPoint W (val i₀) =
          constPoint W ((n : ℤ) • val i₀ + val i₀) from
          (map_add (constPointHom W) _ _).symm,
        show (n : ℤ) • val i₀ + val i₀ = ((n + 1 : ℕ) : ℤ) • val i₀ from by
          push_cast
          rw [add_zsmul, one_zsmul]]
  obtain ⟨hp', hEqp⟩ := hiter p
  rw [hval_tor i₀, show constPoint W (0 : W.Point) = 0 from rfl,
    zero_add] at hEqp
  have hEqp' : WeierstrassCurve.Affine.Point.some (σpow p (tautX W))
      (σpow p (tautY W)) hp' = WeierstrassCurve.Affine.Point.some (tautX W)
        (tautY W) (taut_nonsingular W hΔ) := hEqp
  injection hEqp' with hfixX hfixY
  have hfixhom : (σpow p).comp
      (algebraMap W.CoordinateRing W.FunctionField) =
      (algebraMap W.CoordinateRing W.FunctionField :
        W.CoordinateRing →+* W.FunctionField) :=
    coordinateRing_ringHom_ext
      (fun d => hσpow_c p d)
      (by show σpow p (tautX W) = tautX W; exact hfixX)
      (by show σpow p (tautY W) = tautY W; exact hfixY)
  have hfix : ∀ z' : W.CoordinateRing,
      σpow p (algebraMap W.CoordinateRing W.FunctionField z') =
        algebraMap W.CoordinateRing W.FunctionField z' := fun z' =>
    RingHom.congr_fun hfixhom z'
  have hR1 : σ (algebraMap W.CoordinateRing W.FunctionField a) *
      algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
      constHom W c * algebraMap W.CoordinateRing W.FunctionField a *
        σ (algebraMap W.CoordinateRing W.FunctionField
          (enumVertical W val)) := by
    rw [hσalg, hσalg]
    exact hmain
  have hσv0 : σ (algebraMap W.CoordinateRing W.FunctionField
      (enumVertical W val)) ≠ 0 := by
    rw [hσalg]
    exact hτv
  have hrel : ∀ n : ℕ,
      σpow n (algebraMap W.CoordinateRing W.FunctionField a) *
        algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
      constHom W c ^ n * algebraMap W.CoordinateRing W.FunctionField a *
        σpow n (algebraMap W.CoordinateRing W.FunctionField
          (enumVertical W val)) := by
    intro n
    induction n with
    | zero =>
      show algebraMap W.CoordinateRing W.FunctionField a *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) =
        constHom W c ^ 0 * algebraMap W.CoordinateRing W.FunctionField a *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)
      rw [pow_zero, one_mul]
    | succ n ihn =>
      have hstep := congrArg σ ihn
      simp only [map_mul, map_pow] at hstep
      rw [hσc] at hstep
      have hgoal' : (σpow (n + 1)
            (algebraMap W.CoordinateRing W.FunctionField a) *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) *
          σ (algebraMap W.CoordinateRing W.FunctionField
            (enumVertical W val)) =
          (constHom W c ^ (n + 1) *
            algebraMap W.CoordinateRing W.FunctionField a *
            σpow (n + 1) (algebraMap W.CoordinateRing W.FunctionField
              (enumVertical W val))) *
          σ (algebraMap W.CoordinateRing W.FunctionField
            (enumVertical W val)) := by
        show (σ (σpow n (algebraMap W.CoordinateRing W.FunctionField a)) *
            algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) *
            σ (algebraMap W.CoordinateRing W.FunctionField
              (enumVertical W val)) =
          (constHom W c ^ (n + 1) *
            algebraMap W.CoordinateRing W.FunctionField a *
            σ (σpow n (algebraMap W.CoordinateRing W.FunctionField
              (enumVertical W val)))) *
          σ (algebraMap W.CoordinateRing W.FunctionField
            (enumVertical W val))
        linear_combination
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) *
            hstep +
          constHom W c ^ n * σ (σpow n (algebraMap W.CoordinateRing
            W.FunctionField (enumVertical W val))) * hR1
      exact mul_right_cancel₀ hσv0 hgoal'
  have hfin := hrel p
  rw [hfix, hfix] at hfin
  have hone : constHom W c ^ p = 1 := by
    have h5 : (constHom W c ^ p - 1) *
        (algebraMap W.CoordinateRing W.FunctionField a *
          algebraMap W.CoordinateRing W.FunctionField (enumVertical W val)) =
        0 := by
      linear_combination -hfin
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact sub_eq_zero.mp h6
    · exact absurd h6 (mul_ne_zero haa0 hva0)
  exact (constHom W).injective (by rw [map_pow, map_one, hone])

/-!
### The `p • taut` substrate for L4-5/6

The descent through the fixed field needs the generic multiple
`p • taut` as an explicit affine point: `TorsionCard`'s
division-polynomial multiplication formula, applied to the
constants-mapped curve over its own function field, gives the affine
coordinates together with the algebraicity relation
`xp · ΨSq_p(tautX) = Φ_p(tautX)` — the witness making `tautX` a root
of the monic degree-`p²` polynomial `Φ_p − xp·ΨSq_p` over the
`[p]`-pullback subfield (L4-6). -/

omit [DecidableEq F] in
/-- **Transcendence at a nonconstant element** (generalization of
`eval_map_ne_zero_of_ne_zero` from generic-translate coordinates to an
abstract nonconstancy hypothesis — applied at the generic multiple
`p • taut`, which is not itself a translate of `taut`): evaluation at
an element of the function field avoiding all constants kills no
nonzero univariate polynomial over the algebraically closed
constants. -/
theorem eval_map_ne_zero_of_forall_ne_constHom {x₀ : W.FunctionField}
    (hxc : ∀ c : F, x₀ ≠ constHom W c)
    {q : Polynomial F} (hq : q ≠ 0) :
    (q.map (constHom W)).eval x₀ ≠ 0 := by
  intro h0
  set ev : Polynomial F →+* W.FunctionField :=
    (Polynomial.evalRingHom x₀).comp (Polynomial.mapRingHom (constHom W))
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
    have h3 : ev (Polynomial.X - Polynomial.C a) = x₀ - constHom W a := by
      simp [hev]
    rw [Function.comp_apply, h3] at h2
    exact hxc a (sub_eq_zero.mp h2)

omit [DecidableEq F] [IsAlgClosed F] in
/-- Base-changing the constants-mapped curve along the identity of the
function field is the identity — the bridge letting the
`(E⁄k)`-phrased multiplication machinery of `TorsionCard` apply to the
tautological point of `curveK`. -/
lemma map_constHom_baseChange_self (W : WeierstrassCurve.Affine F) :
    (W.map (constHom W)).baseChange W.FunctionField = W.map (constHom W) :=
  WeierstrassCurve.map_id _

/-- `castPoint` commutes with integer scalar multiplication (the group
structures correspond definitionally under `subst`). -/
lemma castPoint_zsmul {F' : Type*} [Field F'] [DecidableEq F']
    {W₁ W₂ : WeierstrassCurve.Affine F'} (h : W₁ = W₂) (n : ℤ)
    (P : W₁.Point) :
    castPoint h (n • P) = n • castPoint h P := by subst h; rfl

omit [DecidableEq F] in
/-- **The generic multiple `p • taut` is an affine point satisfying
the division-polynomial `x`-relation** (L4-5/6 substrate): `p • taut`
has affine coordinates `(xp, yp)` with
`xp · ΨSq_p(tautX) = Φ_p(tautX)`, obtained from `TorsionCard`'s
multiplication formula on the constants-mapped curve over its own
function field; the required nonvanishing `ΨSq_p(tautX) ≠ 0` holds by
transcendence of `tautX` over the constants
(`eval_map_ne_zero_of_forall_ne_constHom`), since `ΨSq_p ≠ 0` over `F`
for `(p : F) ≠ 0`. -/
theorem exists_smul_tautPoint_eq (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0) :
    ∃ (xp yp : W.FunctionField) (hpn : (curveK W).Nonsingular xp yp),
      (p : ℤ) • tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xp yp hpn ∧
      xp * ((W.ΨSq (p : ℤ)).map (constHom W)).eval (tautX W) =
        ((W.Φ (p : ℤ)).map (constHom W)).eval (tautX W) := by
  classical
  haveI : (W.map (constHom W)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (curveK_Δ_ne_zero W hΔ)⟩
  have hpZ : (p : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpF : ((p : ℤ) : F) ≠ 0 := by exact_mod_cast hp
  have hcast : ((W.map (constHom W)).baseChange W.FunctionField).toAffine =
      curveK W := map_constHom_baseChange_self W
  have hΨbridge :
      ((W.map (constHom W)).baseChange W.FunctionField).ΨSq (p : ℤ) =
        (W.ΨSq (p : ℤ)).map (constHom W) := by
    rw [map_constHom_baseChange_self W, WeierstrassCurve.map_ΨSq]
  have hΦbridge :
      ((W.map (constHom W)).baseChange W.FunctionField).Φ (p : ℤ) =
        (W.Φ (p : ℤ)).map (constHom W) := by
    rw [map_constHom_baseChange_self W, WeierstrassCurve.map_Φ]
  have hnsE : ((W.map (constHom W)).baseChange
      W.FunctionField).toAffine.Nonsingular (tautX W) (tautY W) := by
    rw [hcast]
    exact taut_nonsingular W hΔ
  have hΨx : ((((W.map (constHom W)).baseChange W.FunctionField).ΨSq
      (p : ℤ)).eval (tautX W)) ≠ 0 := by
    rw [hΨbridge]
    exact eval_map_ne_zero_of_forall_ne_constHom tautX_ne_constHom
      (W.ΨSq_ne_zero hpF)
  obtain ⟨xp, yp, hpn', heq, hx⟩ :=
    TorsionCard.exists_smul_some_eq (W.map (constHom W)) hpZ hnsE hΨx
  have hpn : (curveK W).Nonsingular xp yp := hcast ▸ hpn'
  refine ⟨xp, yp, hpn, ?_, ?_⟩
  · have h1 := congrArg (castPoint hcast) heq
    rw [castPoint_zsmul, castPoint_some, castPoint_some] at h1
    exact h1
  · rw [hΨbridge, hΦbridge] at hx
    exact hx

omit [DecidableEq F] in
/-- **The `x`-coordinate of the generic multiple `p • taut` is not a
constant**: a constant value `c` would make `tautX` a root of the
nonzero polynomial `Φ_p − c·ΨSq_p` over the constants (coefficient `1`
in degree `p²` against `ΨSq_p` of degree `≤ p² − 1`), contradicting
the transcendence of `tautX` over the constants. -/
theorem smul_taut_xCoord_ne_constHom {xp : W.FunctionField}
    (hxrel : xp * ((W.ΨSq (p : ℤ)).map (constHom W)).eval (tautX W) =
      ((W.Φ (p : ℤ)).map (constHom W)).eval (tautX W)) (c : F) :
    xp ≠ constHom W c := by
  intro hxc
  subst hxc
  have hq0 : W.Φ (p : ℤ) - Polynomial.C c * W.ΨSq (p : ℤ) ≠ 0 := by
    intro h0
    have hΦc : (W.Φ (p : ℤ)).coeff (p ^ 2) = 1 := by
      have h1 := W.coeff_Φ (p : ℤ)
      rwa [Int.natAbs_natCast] at h1
    have hΨc : (W.ΨSq (p : ℤ)).coeff (p ^ 2) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      apply lt_of_le_of_lt (W.natDegree_ΨSq_le (p : ℤ))
      rw [Int.natAbs_natCast]
      exact Nat.sub_lt (pow_pos (Fact.out : p.Prime).pos 2) one_pos
    have hcoeff : (W.Φ (p : ℤ) -
        Polynomial.C c * W.ΨSq (p : ℤ)).coeff (p ^ 2) = 1 := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hΦc, hΨc, mul_zero,
        sub_zero]
    rw [h0, Polynomial.coeff_zero] at hcoeff
    exact zero_ne_one hcoeff
  have heval : (((W.Φ (p : ℤ) - Polynomial.C c * W.ΨSq (p : ℤ)).map
      (constHom W)).eval (tautX W)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination -hxrel
  exact eval_map_ne_zero_of_forall_ne_constHom tautX_ne_constHom hq0 heval

omit [DecidableEq F] in
/-- **Injectivity of evaluation at a point with nonconstant
`x`-coordinate** (generalization of `pointEval_injective` from generic
translates to an abstract nonconstancy hypothesis — applied at the
generic multiple `p • taut`, which is not itself a translate): a
relation `p(x₀) + q(x₀)·y₀ = 0` forces the norm
`p² − pq·(a₁X + a₃) − q²·(X³ + a₂X² + a₄X + a₆)` to vanish at `x₀`,
hence to vanish identically, hence `p = q = 0` by the degree
formula. -/
theorem pointEval_injective_of_forall_ne_constHom
    {x₀ y₀ : W.FunctionField} (hns : (curveK W).Nonsingular x₀ y₀)
    (hxc : ∀ c : F, x₀ ≠ constHom W c) :
    Function.Injective (pointEval (constHom W) hns.left) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  obtain ⟨pp, qq, rfl⟩ := CoordinateRing.exists_smul_basis_eq f
  have h1 : pointEval (constHom W) hns.left
      (pp • (1 : W.CoordinateRing) + qq • CoordinateRing.mk W Polynomial.X) =
      (pp.map (constHom W)).eval x₀ + (qq.map (constHom W)).eval x₀ * y₀ := by
    rw [CoordinateRing.smul, CoordinateRing.smul, mul_one, map_add, map_mul,
      pointEval_ofPoly, pointEval_ofPoly, pointEval_Y]
  rw [h1] at hf
  have heqc : y₀ ^ 2 + constHom W W.a₁ * x₀ * y₀ + constHom W W.a₃ * y₀ =
      x₀ ^ 3 + constHom W W.a₂ * x₀ ^ 2 + constHom W W.a₄ * x₀ +
        constHom W W.a₆ := by
    have h2 := ((curveK W).equation_iff x₀ y₀).mp hns.left
    simpa only [curveK, WeierstrassCurve.map] using h2
  have hnorm0 : ((Algebra.norm (Polynomial F)
      (pp • (1 : W.CoordinateRing) +
        qq • CoordinateRing.mk W Polynomial.X)).map (constHom W)).eval x₀ =
      0 := by
    rw [CoordinateRing.norm_smul_basis]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination ((pp.map (constHom W)).eval x₀ -
        (qq.map (constHom W)).eval x₀ * y₀ -
        (qq.map (constHom W)).eval x₀ *
          (constHom W W.a₁ * x₀ + constHom W W.a₃)) * hf +
      ((qq.map (constHom W)).eval x₀) ^ 2 * heqc
  have hN : Algebra.norm (Polynomial F)
      (pp • (1 : W.CoordinateRing) +
        qq • CoordinateRing.mk W Polynomial.X) = 0 := by
    by_contra hN0
    exact eval_map_ne_zero_of_forall_ne_constHom hxc hN0 hnorm0
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

/-- **Degree squeeze against a finite group of automorphisms** (the
pure field-theoretic core of the L4-5/6 descent — Artin's fixed-field
theorem in the form `[K : Fix H] = |H|`): if `K/L` is a finite
extension of degree at most the order of a group `H` of
`L`-automorphisms of `K`, then every `H`-fixed element of `K` already
lies in `L`.  Indeed `L ⊆ Fix H` and
`[Fix H : L]·|H| = [Fix H : L]·[K : Fix H] = [K : L] ≤ |H|` forces
`[Fix H : L] = 1`, i.e. `Fix H = L`. -/
theorem mem_range_algebraMap_of_fixed_of_finrank_le
    {L K : Type*} [Field L] [Field K] [Algebra L K] [FiniteDimensional L K]
    (H : Subgroup (K ≃ₐ[L] K)) (hle : Module.finrank L K ≤ Nat.card H)
    (z : K) (hz : ∀ g ∈ H, g z = z) : ∃ w : L, algebraMap L K w = z := by
  have hzmem : z ∈ IntermediateField.fixedField H := fun g => hz g g.2
  have hcard : Module.finrank (IntermediateField.fixedField H) K = Nat.card H :=
    IntermediateField.finrank_fixedField_eq_card H
  have htower : Module.finrank L (IntermediateField.fixedField H) *
      Module.finrank (IntermediateField.fixedField H) K = Module.finrank L K :=
    Module.finrank_mul_finrank _ _ _
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h1 : Module.finrank L (IntermediateField.fixedField H) = 1 := by
    refine le_antisymm (Nat.le_of_mul_le_mul_right ?_ hpos) Module.finrank_pos
    calc Module.finrank L (IntermediateField.fixedField H) * Nat.card H
        = Module.finrank L (IntermediateField.fixedField H) *
            Module.finrank (IntermediateField.fixedField H) K := by rw [hcard]
      _ = Module.finrank L K := htower
      _ ≤ Nat.card H := hle
      _ = 1 * Nat.card H := (one_mul _).symm
  have hbot : IntermediateField.fixedField H = ⊥ :=
    IntermediateField.finrank_eq_one_iff.mp h1
  rw [hbot] at hzmem
  exact IntermediateField.mem_bot.mp hzmem

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Base change of rational points is injective** (the constants
embedding is): the `p`-torsion enumeration stays an enumeration after
base change to the function field. -/
lemma constPoint_injective (W : WeierstrassCurve.Affine F) :
    Function.Injective (constPoint W) := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hn =>
      exact absurd h.symm (Point.some_ne_zero
        ((W.map_nonsingular (constHom W).injective x y).mpr hn))
  | some x y hn =>
    cases Q with
    | zero =>
      exact absurd h (Point.some_ne_zero
        ((W.map_nonsingular (constHom W).injective x y).mpr hn))
    | some x' y' hn' =>
      have h' : (WeierstrassCurve.Affine.Point.some (constHom W x) (constHom W y)
          ((W.map_nonsingular (constHom W).injective x y).mpr hn) :
            (curveK W).Point) =
          WeierstrassCurve.Affine.Point.some (constHom W x') (constHom W y')
            ((W.map_nonsingular (constHom W).injective x' y').mpr hn') := h
      injection h' with hx hy
      have hx' : x = x' := (constHom W).injective hx
      have hy' : y = y' := (constHom W).injective hy
      subst hx'
      subst hy'
      rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The generic translate is affine** (L4-5/6 substrate): `Q ⊕ taut`
is never the point at infinity — otherwise `constPoint Q = ⊖taut` would
make the tautological `x`-coordinate the constant `x(Q)`, against
`tautX_ne_constHom`.  This supplies the affine presentation demanded by
the translation-evaluation substrate at every torsion point. -/
theorem exists_translate_some (hΔ : W.Δ ≠ 0) (Q : W.Point) :
    ∃ (xκ yκ : W.FunctionField) (hκ : (curveK W).Nonsingular xκ yκ),
      constPoint W Q + tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ := by
  rcases hsum : constPoint W Q + tautPoint W hΔ with _ | ⟨xκ, yκ, hκ⟩
  · exfalso
    have hsum0 : constPoint W Q + tautPoint W hΔ = 0 := hsum
    cases Q with
    | zero =>
      rw [show constPoint W (WeierstrassCurve.Affine.Point.zero : W.Point) = 0
        from rfl, zero_add] at hsum0
      exact Point.some_ne_zero (taut_nonsingular W hΔ) hsum0
    | some x y hn =>
      have hneg : (WeierstrassCurve.Affine.Point.some (constHom W x)
          (constHom W y) ((W.map_nonsingular (constHom W).injective x y).mpr hn) :
            (curveK W).Point) = -tautPoint W hΔ :=
        add_eq_zero_iff_eq_neg.mp hsum0
      rw [tautPoint, Point.neg_some] at hneg
      injection hneg with hx _
      exact tautX_ne_constHom x hx.symm
  · exact ⟨xκ, yκ, hκ, rfl⟩

omit [DecidableEq F] [IsAlgClosed F] in
/-- A fraction-field lift of the canonical embedding is the identity
(the lift is the unique ring endomorphism of `K` restricting to the
given map on `F[W]`). -/
lemma lift_eq_self_of_eq_algebraMap
    {g : W.CoordinateRing →+* W.FunctionField} (hg : Function.Injective g)
    (hgeq : g = algebraMap W.CoordinateRing W.FunctionField)
    (w : W.FunctionField) : IsFractionRing.lift hg w = w := by
  have h : IsFractionRing.lift hg = RingHom.id W.FunctionField := by
    refine IsLocalization.ringHom_ext W.CoordinateRing⁰ (RingHom.ext fun a => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      IsFractionRing.lift_algebraMap, hgeq]
  rw [h, RingHom.id_apply]

/-- **The translation evaluation at the zero torsion point is the
identity**: `O ⊕ taut = taut`, so the evaluation is the canonical
embedding `F[W] → K` and its fraction-field lift is `id`. -/
theorem lift_pointEval_eq_self_of_eq_zero (hΔ : W.Δ ≠ 0) {Q : W.Point}
    (hQ : Q = 0) {xκ yκ : W.FunctionField}
    {hκ : (curveK W).Nonsingular xκ yκ}
    (hpt : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ) (w : W.FunctionField) :
    IsFractionRing.lift (pointEval_injective hΔ hpt) w = w := by
  have hc : constPoint W Q = 0 := by rw [hQ]; rfl
  have h0 : (WeierstrassCurve.Affine.Point.some (tautX W) (tautY W)
      (taut_nonsingular W hΔ) : (curveK W).Point) =
      WeierstrassCurve.Affine.Point.some xκ yκ hκ := by
    rw [← hpt, hc, zero_add]
    rfl
  injection h0 with hx hy
  refine lift_eq_self_of_eq_algebraMap (pointEval_injective hΔ hpt) ?_ w
  refine coordinateRing_ringHom_ext (fun d => ?_) ?_ ?_
  · rw [pointEval_C]; rfl
  · rw [pointEval_X, ← hx]; rfl
  · rw [pointEval_Y, ← hy]; rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- Congruence for affine points of the base-changed curve from
coordinate equalities (the nonsingularity proof transports). -/
lemma point_some_congr' {x₁ y₁ x₂ y₂ : W.FunctionField}
    {h₁ : (curveK W).Nonsingular x₁ y₁} {h₂ : (curveK W).Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : (curveK W).Point) =
      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
  subst hx
  subst hy
  rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- **A constants-fixing endomorphism of the function field fixes the
coefficients of the base-changed curve** — the hypothesis under which
`endoMap` acts on `(curveK W).Point`. -/
lemma curveK_map_eq_of_constHom {σ : W.FunctionField →+* W.FunctionField}
    (hσ : ∀ d : F, σ (constHom W d) = constHom W d) :
    (curveK W).map σ = W.map (constHom W) := by
  simp only [curveK, WeierstrassCurve.map, WeierstrassCurve.mk.injEq]
  exact ⟨hσ _, hσ _, hσ _, hσ _, hσ _⟩

omit [DecidableEq F] [IsAlgClosed F] in
/-- A constants-fixing endomorphism fixes the base-changed rational
points. -/
lemma endoMap_constPoint {σ : W.FunctionField →+* W.FunctionField}
    (hcv : (curveK W).map σ = W.map (constHom W))
    (hσ : ∀ d : F, σ (constHom W d) = constHom W d) (R : W.Point) :
    endoMap hcv (constPoint W R) = constPoint W R := by
  cases R with
  | zero => rfl
  | some x y h => exact point_some_congr' (hσ x) (hσ y)

omit [DecidableEq F] [IsAlgClosed F] in
/-- The endomorphism action commutes with integer multiples (it is
additive). -/
lemma endoMap_zsmul {σ : W.FunctionField →+* W.FunctionField}
    (hcv : (curveK W).map σ = W.map (constHom W)) (n : ℤ)
    (P : (curveK W).Point) :
    endoMap hcv (n • P) = n • endoMap hcv P :=
  map_zsmul (AddMonoidHom.mk' (endoMap hcv) (endoMap_add hcv)) n P

/-- The lifted translation evaluation fixes the constants. -/
lemma lift_pointEval_constHom (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xQ yQ : W.FunctionField} {hQn : (curveK W).Nonsingular xQ yQ}
    (hptQ : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQn) (d : F) :
    IsFractionRing.lift (pointEval_injective hΔ hptQ) (constHom W d) =
      constHom W d := by
  show IsFractionRing.lift (pointEval_injective hΔ hptQ)
    (algebraMap W.CoordinateRing W.FunctionField
      (CoordinateRing.mk W (Polynomial.C (Polynomial.C d)))) = constHom W d
  rw [IsFractionRing.lift_algebraMap, pointEval_C]

/-- The lifted translation evaluation sends the tautological
`x`-coordinate to the `x`-coordinate of the translate. -/
lemma lift_pointEval_tautX (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xQ yQ : W.FunctionField} {hQn : (curveK W).Nonsingular xQ yQ}
    (hptQ : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQn) :
    IsFractionRing.lift (pointEval_injective hΔ hptQ) (tautX W) = xQ := by
  rw [tautX, IsFractionRing.lift_algebraMap, pointEval_X]

/-- The lifted translation evaluation sends the tautological
`y`-coordinate to the `y`-coordinate of the translate. -/
lemma lift_pointEval_tautY (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xQ yQ : W.FunctionField} {hQn : (curveK W).Nonsingular xQ yQ}
    (hptQ : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQn) :
    IsFractionRing.lift (pointEval_injective hΔ hptQ) (tautY W) = yQ := by
  rw [tautY, IsFractionRing.lift_algebraMap, pointEval_Y]

/-- **The endomorphism action of a lifted translation evaluation moves
the tautological point by the translation**:
`endoMap σ_Q taut = Q ⊕ taut`. -/
lemma endoMap_tautPoint (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xQ yQ : W.FunctionField} {hQn : (curveK W).Nonsingular xQ yQ}
    (hptQ : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQn) :
    endoMap (curveK_map_eq_of_constHom (lift_pointEval_constHom hΔ hptQ))
        (tautPoint W hΔ) = constPoint W Q + tautPoint W hΔ := by
  rw [hptQ, tautPoint, endoMap_some]
  exact point_some_congr' (lift_pointEval_tautX hΔ hptQ)
    (lift_pointEval_tautY hΔ hptQ)

/-- **L4-5/6 sub-leaf: the composition law of the lifted
translation evaluations.**  Writing `σ_Q` for the fraction-field
extension of evaluation at `Q ⊕ taut` (i.e. `f ↦ f ∘ τ_Q`), applying
`σ_Q` inside `σ_R` substitutes `taut ↦ Q ⊕ taut`, so
`σ_Q ∘ σ_R = σ_{Q ⊕ R}`.

Both sides are fraction-field lifts, so by `IsLocalization.ringHom_ext`
it suffices to compare them on the image of `F[W]`, where
`coordinateRing_ringHom_ext` reduces the claim to the constants (all
three restrict to `constHom`) and the two coordinate functions — there
the statement is the coordinate identity
`(x, y)(R ⊕ (Q ⊕ taut)) = (x, y)((Q ⊕ R) ⊕ taut)`, i.e. the `endoMap`
transport of the group law along `σ_Q` (`endoMap_add`, whose
coefficient hypothesis `(curveK W).map σ_Q = W.map (constHom W)` holds
because `σ_Q` fixes the constants). -/
theorem lift_pointEval_comp (hΔ : W.Δ ≠ 0) {Q R S : W.Point}
    (hQRS : Q + R = S)
    {xQ yQ : W.FunctionField} {hQn : (curveK W).Nonsingular xQ yQ}
    (hptQ : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQn)
    {xR yR : W.FunctionField} {hRn : (curveK W).Nonsingular xR yR}
    (hptR : constPoint W R + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xR yR hRn)
    {xS yS : W.FunctionField} {hSn : (curveK W).Nonsingular xS yS}
    (hptS : constPoint W S + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xS yS hSn)
    (w : W.FunctionField) :
    IsFractionRing.lift (pointEval_injective hΔ hptQ)
        (IsFractionRing.lift (pointEval_injective hΔ hptR) w) =
      IsFractionRing.lift (pointEval_injective hΔ hptS) w := by
  have hS : constPoint W S = constPoint W Q + constPoint W R := by
    rw [← hQRS]
    exact map_add (constPointHom W) Q R
  have h1 : endoMap (curveK_map_eq_of_constHom (lift_pointEval_constHom hΔ hptQ))
      (constPoint W R + tautPoint W hΔ) = constPoint W S + tautPoint W hΔ := by
    rw [endoMap_add, endoMap_constPoint _ (lift_pointEval_constHom hΔ hptQ),
      endoMap_tautPoint hΔ hptQ, hS]
    abel
  rw [hptR, endoMap_some, hptS] at h1
  injection h1 with hxS hyS
  have hcomp2 : (IsFractionRing.lift (pointEval_injective hΔ hptQ)).comp
      (pointEval (constHom W) hRn.left) = pointEval (constHom W) hSn.left := by
    refine coordinateRing_ringHom_ext (fun d => ?_) ?_ ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, pointEval_C]
      exact lift_pointEval_constHom hΔ hptQ d
    · simp only [RingHom.coe_comp, Function.comp_apply, pointEval_X]
      exact hxS
    · simp only [RingHom.coe_comp, Function.comp_apply, pointEval_Y]
      exact hyS
  have hring : ((IsFractionRing.lift (pointEval_injective hΔ hptQ)).comp
      (IsFractionRing.lift (pointEval_injective hΔ hptR)) :
        W.FunctionField →+* W.FunctionField) =
      IsFractionRing.lift (pointEval_injective hΔ hptS) := by
    refine IsLocalization.ringHom_ext W.CoordinateRing⁰ (RingHom.ext fun a => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply,
      IsFractionRing.lift_algebraMap]
    exact RingHom.congr_fun hcomp2 a
  exact RingHom.congr_fun hring w

omit [Fact p.Prime] in
/-- **L4-5/6 sub-leaf: the lifted translation evaluations fix
the `[p]`-pullback subfield pointwise** — `[p]^*K ⊆ Fix E[p]`.  For a
`p`-torsion point `Q`, the lifted translation `σ_Q` fixes every
`[p]^*(w) = IsFractionRing.lift hinj w`.

`σ_Q ∘ [p]^*` and `[p]^*` are fraction-field lifts, so by
`IsLocalization.ringHom_ext` and `coordinateRing_ringHom_ext` the claim
reduces to the constants (both restrict to `constHom`) and to
`σ_Q xp = xp`, `σ_Q yp = yp` — which is the `endoMap` computation
`endoMap σ_Q (p • taut) = p • (Q ⊕ taut) =
constPoint ((p : ℤ) • Q) + p • taut = p • taut`, the last step by the
torsion hypothesis `hQtor`. -/
theorem lift_pointEval_pullback_eq (hΔ : W.Δ ≠ 0) {Q : W.Point}
    (hQtor : (p : ℤ) • Q = 0)
    {xQ yQ : W.FunctionField} {hQn : (curveK W).Nonsingular xQ yQ}
    (hptQ : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQn)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hsmul : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    (hinj : Function.Injective (pointEval (constHom W) hpn.left))
    (w : W.FunctionField) :
    IsFractionRing.lift (pointEval_injective hΔ hptQ)
        (IsFractionRing.lift hinj w) = IsFractionRing.lift hinj w := by
  have hconst : ((p : ℤ) • constPoint W Q : (curveK W).Point) = 0 := by
    have h2 : (constPointHom W) ((p : ℤ) • Q) =
        (p : ℤ) • (constPointHom W) Q := map_zsmul _ _ _
    rw [hQtor, map_zero] at h2
    exact h2.symm
  have hsplit : ((p : ℤ) • (constPoint W Q + tautPoint W hΔ) : (curveK W).Point) =
      (p : ℤ) • constPoint W Q + (p : ℤ) • tautPoint W hΔ := zsmul_add _ _ _
  have hfix : endoMap (curveK_map_eq_of_constHom (lift_pointEval_constHom hΔ hptQ))
      ((p : ℤ) • tautPoint W hΔ) = (p : ℤ) • tautPoint W hΔ := by
    rw [endoMap_zsmul, endoMap_tautPoint hΔ hptQ, hsplit, hconst, zero_add]
  rw [hsmul, endoMap_some] at hfix
  injection hfix with hxp hyp
  have hcomp2 : (IsFractionRing.lift (pointEval_injective hΔ hptQ)).comp
      (pointEval (constHom W) hpn.left) = pointEval (constHom W) hpn.left := by
    refine coordinateRing_ringHom_ext (fun d => ?_) ?_ ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, pointEval_C]
      exact lift_pointEval_constHom hΔ hptQ d
    · simp only [RingHom.coe_comp, Function.comp_apply, pointEval_X]
      exact hxp
    · simp only [RingHom.coe_comp, Function.comp_apply, pointEval_Y]
      exact hyp
  have hring : ((IsFractionRing.lift (pointEval_injective hΔ hptQ)).comp
      (IsFractionRing.lift hinj) : W.FunctionField →+* W.FunctionField) =
      IsFractionRing.lift hinj := by
    refine IsLocalization.ringHom_ext W.CoordinateRing⁰ (RingHom.ext fun a => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply,
      IsFractionRing.lift_algebraMap]
    exact RingHom.congr_fun hcomp2 a
  exact RingHom.congr_fun hring w

/-- **L4-5/6 sub-leaf (sorry): the `[p]`-pullback subfield has index at
most `p²`** — `[K : [p]^*K] ≤ p²`.  The subfield
`L := (IsFractionRing.lift hinj).fieldRange` contains the constants
(`[p]^*` fixes them) and the coordinates `xp, yp` of `p • taut`.

Proof plan: `tautX` is a root of the monic degree-`p²` polynomial
`Φ_p − xp·ΨSq_p ∈ L[T]` (that is exactly `hxrel`, with the leading
coefficient computed as in `smul_taut_xCoord_ne_constHom`), so
`[L(tautX) : L] ≤ p²`; and `tautY ∈ L(tautX)` by the `y`-bookkeeping
(the nontrivial `L(tautX)`-automorphism of `K` would be the
hyperelliptic involution, which moves `yp ∈ L` because `2p • taut ≠ 0`
for `hp : (p : F) ≠ 0`).  Since `K = F(tautX, tautY)` — every element
of `F[W]` is `pp(tautX) + qq(tautX)·tautY` by
`CoordinateRing.exists_smul_basis_eq`, and `K` is its fraction field —
the extension `K/L` is finite of degree at most `p²`. -/
theorem finiteDimensional_and_finrank_le_pullback (hΔ : W.Δ ≠ 0)
    (hp : (p : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hsmul : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    (hxrel : xp * ((W.ΨSq (p : ℤ)).map (constHom W)).eval (tautX W) =
      ((W.Φ (p : ℤ)).map (constHom W)).eval (tautX W))
    (hinj : Function.Injective (pointEval (constHom W) hpn.left)) :
    FiniteDimensional
        ↥(IsFractionRing.lift (K := W.FunctionField) hinj).fieldRange
        W.FunctionField ∧
      Module.finrank
        ↥(IsFractionRing.lift (K := W.FunctionField) hinj).fieldRange
        W.FunctionField ≤ p ^ 2 := by
  sorry

/-- **L4-5/6 Galois core (PROVEN over the single remaining sub-leaf
`finiteDimensional_and_finrank_le_pullback`): every element of the
function field fixed by all lifted translation evaluations lies in the
range of the `[p]`-pullback embedding — `Fix E[p] ⊆ [p]^*K`.**  Let
`val : ι → W.Point` enumerate the `p`-torsion subgroup
(`card ι = p²`), `(xp, yp)` the affine coordinates of the generic
multiple `p • taut` with the division-polynomial relation `hxrel`, and
`hinj` the injectivity of evaluation at `(xp, yp)`; suppose
`z ∈ K = Frac F[W]` is fixed by the fraction-field extension of every
translation evaluation (`hz`, quantified over all coordinate
presentations of the translates `κ ⊕ taut`).  Then `z = σ_p(h)` for
some `h ∈ K`, where `σ_p = IsFractionRing.lift hinj : K →+* K`
realizes `h ↦ h ∘ [p]`.

The proof (HLEG-NOTES.md §4(B), stages L4-5/6) is the degree squeeze
`mem_range_algebraMap_of_fixed_of_finrank_le` applied to
`L := (IsFractionRing.lift hinj).fieldRange` and the group
`H = {σ_κ : κ ∈ E[p]}`, assembled here from three stages (the first two
proven, the third the remaining leaf):

* every translate `κ ⊕ taut` is affine (`exists_translate_some`), so
  every `σ_κ` is defined; `σ_O = id`
  (`lift_pointEval_eq_self_of_eq_zero`) and `σ_κ ∘ σ_λ = σ_{κ⊕λ}`
  (`lift_pointEval_comp`), whence each `σ_κ` is bijective with inverse
  `σ_{⊖κ}` and `H` is a subgroup of `Aut K` of order `p²` — the order
  because `κ ↦ σ_κ` is injective (`σ_κ tautX = x(κ ⊕ taut)` and
  `σ_κ tautY = y(κ ⊕ taut)` recover the translate, hence `κ`, from
  `σ_κ` through `constPoint_injective` and `hval_inj`);
* each `σ_κ` fixes `L` pointwise (`lift_pointEval_pullback_eq`), so
  `H` is a group of `L`-automorphisms;
* `[K : L] ≤ p²` (`finiteDimensional_and_finrank_le_pullback`).

The squeeze then gives `Fix H = L ∋ z`. -/
theorem mem_range_pullback_of_translation_lift_fixed {ι : Type*}
    [Fintype ι] {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hsmul : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    (hxrel : xp * ((W.ΨSq (p : ℤ)).map (constHom W)).eval (tautX W) =
      ((W.Φ (p : ℤ)).map (constHom W)).eval (tautX W))
    (hinj : Function.Injective (pointEval (constHom W) hpn.left))
    (z : W.FunctionField)
    (hz : ∀ (i : ι) (xκ yκ : W.FunctionField)
      (hκ : (curveK W).Nonsingular xκ yκ)
      (hpt : constPoint W (val i) + tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ),
      IsFractionRing.lift (pointEval_injective hΔ hpt) z = z) :
    ∃ h : W.FunctionField, IsFractionRing.lift hinj h = z := by
  classical
  obtain ⟨hfd, hfr⟩ :=
    finiteDimensional_and_finrank_le_pullback hΔ hp hsmul hxrel hinj
  haveI : FiniteDimensional
    ↥(IsFractionRing.lift (K := W.FunctionField) hinj).fieldRange
    W.FunctionField := hfd
  choose xv yv hv hptv using fun i : ι => exists_translate_some hΔ (val i)
  -- the lifted translation evaluations, on the two coordinate functions
  have hτX : ∀ i : ι,
      IsFractionRing.lift (pointEval_injective hΔ (hptv i)) (tautX W) = xv i :=
    fun i => lift_pointEval_tautX hΔ (hptv i)
  have hτY : ∀ i : ι,
      IsFractionRing.lift (pointEval_injective hΔ (hptv i)) (tautY W) = yv i :=
    fun i => lift_pointEval_tautY hΔ (hptv i)
  -- the torsion group structure carried by the index type
  obtain ⟨i₀, hi₀⟩ := hval_surj 0 (smul_zero _)
  have hnegex : ∀ i : ι, ∃ j : ι, val j = -val i := by
    intro i
    exact hval_surj (-val i) (by rw [smul_neg, hval_tor i, neg_zero])
  choose jinv hjinv using hnegex
  have hid : ∀ i : ι, val i = 0 → ∀ w : W.FunctionField,
      IsFractionRing.lift (pointEval_injective hΔ (hptv i)) w = w :=
    fun i hi w => lift_pointEval_eq_self_of_eq_zero hΔ hi (hptv i) w
  have hcomp : ∀ i j k : ι, val i + val j = val k → ∀ w : W.FunctionField,
      IsFractionRing.lift (pointEval_injective hΔ (hptv i))
          (IsFractionRing.lift (pointEval_injective hΔ (hptv j)) w) =
        IsFractionRing.lift (pointEval_injective hΔ (hptv k)) w :=
    fun i j k hijk w =>
      lift_pointEval_comp hΔ hijk (hptv i) (hptv j) (hptv k) w
  -- each lift is an automorphism over the pullback subfield
  have hpack : ∀ i : ι, ∃ e : W.FunctionField ≃ₐ[↥(IsFractionRing.lift
      (K := W.FunctionField) hinj).fieldRange] W.FunctionField,
      ∀ w, e w = IsFractionRing.lift (pointEval_injective hΔ (hptv i)) w := by
    intro i
    have hri : (IsFractionRing.lift (pointEval_injective hΔ (hptv i))).comp
        (IsFractionRing.lift (pointEval_injective hΔ (hptv (jinv i)))) =
        RingHom.id W.FunctionField := by
      refine RingHom.ext fun w => ?_
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [hcomp i (jinv i) i₀ (by rw [hjinv i, add_neg_cancel, hi₀])]
      exact hid i₀ hi₀ w
    have hri' : (IsFractionRing.lift (pointEval_injective hΔ (hptv (jinv i)))).comp
        (IsFractionRing.lift (pointEval_injective hΔ (hptv i))) =
        RingHom.id W.FunctionField := by
      refine RingHom.ext fun w => ?_
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [hcomp (jinv i) i i₀ (by rw [hjinv i, neg_add_cancel, hi₀])]
      exact hid i₀ hi₀ w
    refine ⟨AlgEquiv.ofRingEquiv
      (f := RingEquiv.ofRingHom _ _ hri hri') ?_, fun w => rfl⟩
    intro x
    obtain ⟨v, hv'⟩ := RingHom.mem_fieldRange.mp x.2
    show IsFractionRing.lift (pointEval_injective hΔ (hptv i))
      (x : W.FunctionField) = (x : W.FunctionField)
    rw [← hv']
    exact lift_pointEval_pullback_eq hΔ (hval_tor i) (hptv i) hsmul hinj v
  choose e he using hpack
  -- distinct torsion points give distinct automorphisms
  have heinj : Function.Injective e := by
    intro i j hij
    have hx : xv i = xv j := by
      rw [← hτX i, ← hτX j, ← he i, ← he j, hij]
    have hy : yv i = yv j := by
      rw [← hτY i, ← hτY j, ← he i, ← he j, hij]
    refine hval_inj (constPoint_injective W
      (add_right_cancel (b := tautPoint W hΔ) ?_))
    rw [hptv i, hptv j]
    exact point_some_congr' hx hy
  -- the automorphism group
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (W.FunctionField ≃ₐ[↥(IsFractionRing.lift
      (K := W.FunctionField) hinj).fieldRange] W.FunctionField),
      ∀ g, g ∈ H ↔ ∃ i : ι, e i = g := by
    refine ⟨{ carrier := Set.range e
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := hval_surj (val i + val j)
        (by rw [smul_add, hval_tor i, hval_tor j, add_zero])
      refine ⟨k, AlgEquiv.ext fun w => ?_⟩
      show e k w = e i (e j w)
      rw [he i, he j, he k, hcomp i j k hk.symm w]
    · refine ⟨i₀, AlgEquiv.ext fun w => ?_⟩
      show e i₀ w = w
      rw [he i₀]
      exact hid i₀ hi₀ w
    · rintro a ⟨i, rfl⟩
      refine ⟨jinv i, ?_⟩
      refine inv_eq_of_mul_eq_one_right (AlgEquiv.ext fun w => ?_) |>.symm
      show e i (e (jinv i) w) = w
      rw [he i, he (jinv i),
        hcomp i (jinv i) i₀ (by rw [hjinv i, add_neg_cancel, hi₀])]
      exact hid i₀ hi₀ w
  have hHcard : Nat.card H = p ^ 2 := by
    have hbij : Function.Bijective
        (fun i : ι => (⟨e i, (hH (e i)).mpr ⟨i, rfl⟩⟩ : H)) := by
      refine ⟨fun i j hij => heinj (congrArg Subtype.val hij), ?_⟩
      rintro ⟨g, hg⟩
      obtain ⟨i, rfl⟩ := (hH g).mp hg
      exact ⟨i, rfl⟩
    rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, hcard]
  -- the degree squeeze
  obtain ⟨w, hw⟩ := mem_range_algebraMap_of_fixed_of_finrank_le H
    (by rw [hHcard]; exact hfr) z (by
      intro g hg
      obtain ⟨i, rfl⟩ := (hH g).mp hg
      rw [he i]
      exact hz i (xv i) (yv i) (hv i) (hptv i))
  obtain ⟨v, hv'⟩ := RingHom.mem_fieldRange.mp w.2
  exact ⟨v, hv'.trans hw⟩

/-- **L4-5/6 membership core (PROVEN glue over the Galois core
`mem_range_pullback_of_translation_lift_fixed`): a
translation-invariant ratio lies in the range of the `[p]`-pullback
embedding.**  Let
`val : ι → W.Point` enumerate the `p`-torsion subgroup
(`card ι = p²`), `(xp, yp)` the affine coordinates of the generic
multiple `p • taut` with the division-polynomial relation `hxrel`, and
`hinj` the injectivity of evaluation at `(xp, yp)` (supplied by
`pointEval_injective_of_forall_ne_constHom`); suppose the ratio
`g = g₁/g₂ ∈ K` is invariant under every translation evaluation
(`hfix`, multiplied out at the generic translate).  Then `g = σ_p(h)`
for some `h ∈ K`, where `σ_p = IsFractionRing.lift hinj : K →+* K` is
the fraction-field extension of evaluation at `p • taut` — the
realization of `h ↦ h ∘ [p]`, so `g` descends through the pullback.

Proof plan (HLEG-NOTES.md §4(B), stages L4-5/6): each `τ_κ^*` extends
to a field automorphism `σ_κ` of `K` fixing the constants
(injectivity from `pointEval_injective` at the generic translate,
lifted to `K` by `IsFractionRing.lift`; surjectivity from
`σ_κ ∘ σ_{⊖κ} = id`, the composition law coming from `endoMap`
additivity and the group law `(taut ⊖ κ) ⊕ κ = taut`); `κ ↦ σ_κ` is a
faithful action of the order-`p²` torsion group on `K` (faithfulness:
`σ_κ tautX = tautX` forces `x(κ ⊕ taut) = x(taut)`, so
`κ ⊕ taut = ±taut`; the minus branch would make `x(2•taut)` a
constant, against the `n = 2` instance of
`smul_taut_xCoord_ne_constHom`-style nonconstancy), so Artin's theorem
(mathlib's `FixedPoints.finrank_eq_card`) gives `[K : Fix E[p]] = p²`.
The pullback subfield `L := (IsFractionRing.lift hinj).fieldRange`
lies inside `Fix E[p]`: `σ_κ` fixes `xp` and `yp` because
`endoMap σ_κ (p•taut) = p•(κ ⊕ taut) = constPoint ((p:ℤ)•κ) + p•taut =
p•taut` by `hval_tor`, hence `σ_κ` fixes `L` pointwise
(`coordinateRing_ringHom_ext` on the coordinate ring, then
`IsFractionRing`-uniqueness of the extension).  And `[K : L] ≤ p²`:
`constHom F ⊆ L` and `xp, yp ∈ L`; `tautX` is a root of the monic
degree-`p²` polynomial `Φ_p − xp·ΨSq_p` over `L` (`hxrel`), and
`tautY ∈ L(tautX)` by the `y`-bookkeeping (the nontrivial
`L(tautX)`-automorphism of `K` would have to be the hyperelliptic
involution, which moves `yp ∈ L` since `2p • taut ≠ 0`).  The degree
squeeze `L ⊆ Fix E[p]`, `[K : Fix E[p]] = p² ≥ [K : L]` forces
`Fix E[p] = L ∋ g`.  Finally `g` IS fixed: `hfix` says exactly
`σ_κ(ḡ₁)·ḡ₂ = ḡ₁·σ_κ(ḡ₂)`, i.e. `σ_κ(g) = g`.  DECOMPOSE along these
stages when opening this node. -/
theorem translation_fixed_mem_range_pullback {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hsmul : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    (hxrel : xp * ((W.ΨSq (p : ℤ)).map (constHom W)).eval (tautX W) =
      ((W.Φ (p : ℤ)).map (constHom W)).eval (tautX W))
    (hinj : Function.Injective (pointEval (constHom W) hpn.left))
    {g₁ g₂ : W.CoordinateRing} (_hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hfix : ∀ (i₀ : ι) (xκ yκ : W.FunctionField)
      (hκ : (curveK W).Nonsingular xκ yκ),
      constPoint W (val i₀) + tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ →
      pointEval (constHom W) hκ.left g₁ *
          algebraMap W.CoordinateRing W.FunctionField g₂ =
        algebraMap W.CoordinateRing W.FunctionField g₁ *
          pointEval (constHom W) hκ.left g₂) :
    ∃ h : W.FunctionField, IsFractionRing.lift hinj h =
      algebraMap W.CoordinateRing W.FunctionField g₁ /
        algebraMap W.CoordinateRing W.FunctionField g₂ := by
  classical
  have hg₂a : algebraMap W.CoordinateRing W.FunctionField g₂ ≠ 0 := fun h0 =>
    hg₂ ((map_eq_zero_iff _
      (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mp h0)
  refine mem_range_pullback_of_translation_lift_fixed hΔ hp hval_inj
    hval_tor hval_surj hcard hsmul hxrel hinj _ ?_
  intro i xκ yκ hκ hpt
  have hσalg : ∀ w : W.CoordinateRing,
      IsFractionRing.lift (pointEval_injective hΔ hpt)
        (algebraMap W.CoordinateRing W.FunctionField w) =
      pointEval (constHom W) hκ.left w := fun w =>
    IsFractionRing.lift_algebraMap (pointEval_injective hΔ hpt) w
  have hτg₂ : pointEval (constHom W) hκ.left g₂ ≠ 0 := fun h0 =>
    hg₂ (pointEval_injective hΔ hpt (by rw [h0, map_zero]))
  rw [map_div₀, hσalg, hσalg, div_eq_div_iff hτg₂ hg₂a]
  exact hfix i xκ yκ hκ hpt

/-- **L4-5/6 (PROVEN glue over the membership core
`translation_fixed_mem_range_pullback`): descent of a
translation-invariant ratio through `Fix E[p] = [p]^*K`, coordinates
of `p • taut` given.**
Let `val : ι → W.Point` enumerate the `p`-torsion subgroup
(`card ι = p²`), `(xp, yp)` the affine coordinates of the generic
multiple `p • taut` with the division-polynomial relation
`xp·ΨSq_p(tautX) = Φ_p(tautX)`, and `g₁, g₂` nonzero coordinate-ring
elements whose ratio `g = g₁/g₂ ∈ K = Frac F[W]` is invariant under
every translation evaluation (`hfix`, multiplied out at the generic
translate).  Then `g` lies in the `[p]`-pullback subfield: there are
`b, c ≠ 0` with `[p]^*(c) ≠ 0` and `g₁·[p]^*(c) = g₂·[p]^*(b)`, where
`[p]^* = pointEval` at `(xp, yp)`.

Proof plan (HLEG-NOTES.md §4(B), stages L4-5/6): each `τ_κ^*` extends
to a field automorphism `σ_κ` of `K` fixing the constants
(injectivity from `pointEval_injective`, lifted to `K` by
`IsFractionRing.lift`; surjectivity from `σ_κ ∘ σ_{⊖κ} = id`, the
composition law coming from `endoMap` additivity and the group law
`(taut ⊖ κ) ⊕ κ = taut`); `κ ↦ σ_κ` is a faithful action of the
order-`p²` torsion group on `K` (faithfulness: `σ_κ tautX = tautX`
forces `x(κ ⊕ taut) = x(taut)`, so `κ ⊕ taut = ±taut`; the minus
branch would make `x(2•taut)` a constant, against the `n = 2` instance
of the division-polynomial nonconstancy), so Artin's theorem
(mathlib's `FixedPoints.finrank_eq_card`) gives `[K : Fix E[p]] = p²`.
The pullback subfield `L := (IsFractionRing.lift (pointEval-injective
at (xp, yp))).fieldRange` lies inside `Fix E[p]`: `σ_κ` fixes `xp` and
`yp` because `endoMap σ_κ (p•taut) = p•(κ ⊕ taut) =
constPoint ((p:ℤ)•κ) + p•taut = p•taut` by `hval_tor`, hence `σ_κ`
fixes `L` pointwise (`coordinateRing_ringHom_ext` on the coordinate
ring, then `IsFractionRing`-uniqueness).  And `[K : L] ≤ p²`:
`constHom F ⊆ L` and `xp, yp ∈ L`; `tautX` is a root of the monic
degree-`p²` polynomial `Φ_p − xp·ΨSq_p` over `L` (`hxrel`), and
`tautY ∈ L(tautX)` by the `y`-bookkeeping (the nontrivial
`L(tautX)`-automorphism of `K` would have to be the hyperelliptic
involution, which moves `yp ∈ L` since `2p • taut ≠ 0`).  The degree
squeeze `L ⊆ Fix E[p]`, `[K : Fix E[p]] = p² ≥ [K : L]` forces
`Fix E[p] = L ∋ g`, and clearing denominators through
`IsFractionRing.div_surjective` yields `b, c`.  DECOMPOSE along these
stages when opening this node. -/
theorem exists_pullback_pair_of_translation_fixed {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hsmul : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    (hxrel : xp * ((W.ΨSq (p : ℤ)).map (constHom W)).eval (tautX W) =
      ((W.Φ (p : ℤ)).map (constHom W)).eval (tautX W))
    {g₁ g₂ : W.CoordinateRing} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hfix : ∀ (i₀ : ι) (xκ yκ : W.FunctionField)
      (hκ : (curveK W).Nonsingular xκ yκ),
      constPoint W (val i₀) + tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ →
      pointEval (constHom W) hκ.left g₁ *
          algebraMap W.CoordinateRing W.FunctionField g₂ =
        algebraMap W.CoordinateRing W.FunctionField g₁ *
          pointEval (constHom W) hκ.left g₂) :
    ∃ b c : W.CoordinateRing, b ≠ 0 ∧ c ≠ 0 ∧
      pointEval (constHom W) hpn.left c ≠ 0 ∧
      algebraMap W.CoordinateRing W.FunctionField g₁ *
          pointEval (constHom W) hpn.left c =
        algebraMap W.CoordinateRing W.FunctionField g₂ *
          pointEval (constHom W) hpn.left b := by
  classical
  have hg₁a : algebraMap W.CoordinateRing W.FunctionField g₁ ≠ 0 := fun h0 =>
    hg₁ ((map_eq_zero_iff _
      (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mp h0)
  have hg₂a : algebraMap W.CoordinateRing W.FunctionField g₂ ≠ 0 := fun h0 =>
    hg₂ ((map_eq_zero_iff _
      (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mp h0)
  have hinj : Function.Injective (pointEval (constHom W) hpn.left) :=
    pointEval_injective_of_forall_ne_constHom hpn
      (smul_taut_xCoord_ne_constHom hxrel)
  obtain ⟨h, hh⟩ := translation_fixed_mem_range_pullback hΔ hp hval_inj
    hval_tor hval_surj hcard hsmul hxrel hinj hg₁ hg₂ hfix
  obtain ⟨b, c, hcmem, hbc⟩ :=
    IsFractionRing.div_surjective (A := W.CoordinateRing) h
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hcmem
  have hτ : ∀ z : W.CoordinateRing,
      IsFractionRing.lift hinj (algebraMap W.CoordinateRing
        W.FunctionField z) = pointEval (constHom W) hpn.left z := fun z =>
    IsFractionRing.lift_algebraMap hinj z
  have hτc : pointEval (constHom W) hpn.left c ≠ 0 := fun h0 =>
    hc0 (hinj (by rw [h0, map_zero]))
  have hστ : pointEval (constHom W) hpn.left b /
      pointEval (constHom W) hpn.left c =
      algebraMap W.CoordinateRing W.FunctionField g₁ /
        algebraMap W.CoordinateRing W.FunctionField g₂ := by
    rw [← hτ b, ← hτ c, ← map_div₀ (IsFractionRing.lift hinj), hbc]
    exact hh
  have hmain : algebraMap W.CoordinateRing W.FunctionField g₁ *
      pointEval (constHom W) hpn.left c =
      algebraMap W.CoordinateRing W.FunctionField g₂ *
        pointEval (constHom W) hpn.left b := by
    have h1 := (div_eq_div_iff hτc hg₂a).mp hστ
    linear_combination -h1
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb, map_zero, mul_zero] at hmain
    exact mul_ne_zero hg₁a hτc hmain
  exact ⟨b, c, hb0, hc0, hτc, hmain⟩

/-- **L4-5/6 (PROVEN glue over the `p • taut` substrate
`exists_smul_tautPoint_eq` and the descent core
`exists_pullback_pair_of_translation_fixed`): the fixed field of the
translation action is the `[p]^*`-pullback subfield — descent of a
translation-invariant ratio.**  Let `val : ι → W.Point` enumerate the
`p`-torsion subgroup
(`card ι = p²`) and let `g₁, g₂` be nonzero coordinate-ring elements
whose ratio `g = g₁/g₂ ∈ K = Frac F[W]` is invariant under every
translation `τ_κ`, `κ ∈ E[p]` — stated multiplied out at the generic
translate: `τ(g₁)·g₂ = g₁·τ(g₂)` in `K`, where `τ = τ_{κ}^*` is
`pointEval` at the affine coordinates of `κ ⊕ taut` (every such
translate IS affine: a constant point can never be the negative of the
tautological point, whose `x`-coordinate `tautX` is no constant since
`X − C x₀` is a nonzero element of the coordinate ring).  Then `g`
descends through the fixed field: `g = h ∘ [p]` for some `h ∈ K`.

Proof plan (HLEG-NOTES.md §4(B), stages L4-5/6): each `τ_κ^*` extends
to a field automorphism `σ_κ` of `K` fixing the constants
(injectivity of `pointEval` at a generic translate via composition
with `τ_{⊖κ}^*` and the group law `(taut ⊖ κ) ⊕ κ = taut`; surjective
since `σ_κ ∘ σ_{⊖κ} = id`); `κ ↦ σ_κ` is a faithful action of the
order-`p²` group `E[p]` on `K` (faithfulness: `σ_κ` fixes `tautX` iff
the translate `κ ⊕ taut` has the same `x`-coordinate iff `κ = O`,
using `hval_inj`), so by Artin's theorem `[K : Fix E[p]] = p²`.  The
pullback subfield `[p]^*K` — the range of `pointEval` at `p • taut`
extended to `K` — lies inside `Fix E[p]` (from `[p]∘τ_κ = [p]`, i.e.
`p•(κ ⊕ taut) = p•taut` by `hval_tor`), and `[K : [p]^*K] ≤ p²` since
`tautX` is a root of the degree-`p²` polynomial `Φ_p − ([p]^*x)·Ψ_p²`
over `[p]^*K` (division-polynomial pullback of a vertical, separable
as `(p : F) ≠ 0`) and `tautY` is quadratic over `[p]^*K(tautX)` while
the `y`-halving `[2]`-bookkeeping keeps the total at `p²`.  Hence
`Fix E[p] = [p]^*K ∋ g`.  The conclusion is stated multiplied out:
`p • taut` is affine with coordinates `(xp, yp)`, `pointEval` there
realizes `h ↦ h∘[p]`, and `g₁·[p]^*(c) = g₂·[p]^*(b)` for `h = b/c`
with `[p]^*(c) ≠ 0` (evaluation at the generic point `p • taut` kills
no nonzero element — `[p]` is surjective on points).  See
HLEG-NOTES.md §4(B), stages L4-5/6. -/
theorem exists_pullback_of_translation_fixed {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {g₁ g₂ : W.CoordinateRing} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hfix : ∀ (i₀ : ι) (xκ yκ : W.FunctionField)
      (hκ : (curveK W).Nonsingular xκ yκ),
      constPoint W (val i₀) + tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xκ yκ hκ →
      pointEval (constHom W) hκ.left g₁ *
          algebraMap W.CoordinateRing W.FunctionField g₂ =
        algebraMap W.CoordinateRing W.FunctionField g₁ *
          pointEval (constHom W) hκ.left g₂) :
    ∃ (xp yp : W.FunctionField) (hpn : (curveK W).Nonsingular xp yp),
      (p : ℤ) • tautPoint W hΔ =
        WeierstrassCurve.Affine.Point.some xp yp hpn ∧
      ∃ b c : W.CoordinateRing, b ≠ 0 ∧ c ≠ 0 ∧
        pointEval (constHom W) hpn.left c ≠ 0 ∧
        algebraMap W.CoordinateRing W.FunctionField g₁ *
            pointEval (constHom W) hpn.left c =
          algebraMap W.CoordinateRing W.FunctionField g₂ *
            pointEval (constHom W) hpn.left b := by
  obtain ⟨xp, yp, hpn, hsmul, hxrel⟩ := exists_smul_tautPoint_eq hΔ hp
  obtain ⟨b, c, hb, hc, hcnz, heq⟩ :=
    exists_pullback_pair_of_translation_fixed hΔ hp hval_inj hval_tor
      hval_surj hcard hsmul hxrel hg₁ hg₂ hfix
  exact ⟨xp, yp, hpn, hsmul, b, c, hb, hc, hcnz, heq⟩

/-!
### L4-7 substrate: `[p]`-fibers as point-ideal products

The multiplicity-one pullback comparison of stage L4-7 is organized
around the **fiber product**
`fiberProd val T = ∏_{κ ∈ E[p]} I'_{T ⊕ κ}`, the unit fractional ideal
of the pullback divisor `[p]^*(R) = Σ_{p•S = R} (S)` for any preimage
`p • T = R` — the fiber of `[p]` over `R` is the coset `T ⊕ E[p]`, and
`[p]` being separable (`(p : F) ≠ 0`) it is reduced, so each of its
`p²` points occurs with multiplicity one.

Over this device the comparison splits into three geometric bricks —
the affine divisor of a coordinate function
(`exists_multiset_span_eq_prod_pointIdeal`), the pullback formula
(`spanSingleton_pointEval_mul_fiberProd_pow`), and injectivity of the
fiber-product map on divisors (`fiberProd_prod_inj`) — and a purely
formal assembly, which is the proof of
`span_eq_pointIdeal_mul_of_pullback` below.  All three bricks rest on
the (still unformalized, in mathlib as here) Dedekind property of the
affine coordinate ring `F[W]` of a smooth affine curve: `F[W]` is
noetherian, one-dimensional and integrally closed when `W.Δ ≠ 0`, so
its nonzero fractional ideals factor uniquely into maximal ideals,
which — `F` being algebraically closed — are exactly the point ideals
`pointIdeal W R` of the affine points `R`. -/

/-- The `[p]`-fiber point-ideal product over a preimage `T`: the
product `∏_{κ} I'_{T ⊕ κ}` of the unit fractional point ideals over the
enumeration `val` of `E[p]`.  When `p • T = R` this is the unit
fractional ideal of the pullback divisor `[p]^*(R)`; it depends on `T`
only through `p • T`, because the fiber `T ⊕ E[p]` does. -/
noncomputable def fiberProd {ι : Type*} [Fintype ι]
    (W : WeierstrassCurve.Affine F) (val : ι → W.Point) (T : W.Point) :
    FractionalIdeal W.CoordinateRing⁰ W.FunctionField :=
  ((Finset.univ.val.map fun i => T + val i).map fun R =>
    (pointIdeal' W R :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod

omit [DecidableEq F] [IsAlgClosed F] in
/-- The point ideal at `O` is the whole ring (the origin carries no
affine divisor). -/
@[simp] lemma pointIdeal_zero : pointIdeal W (0 : W.Point) = ⊤ := rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- A product of coerced unit point ideals is a unit fractional
ideal. -/
lemma isUnit_prod_coe_pointIdeal' (D : Multiset W.Point) :
    IsUnit ((D.map fun R =>
      (pointIdeal' W R :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) := by
  refine Multiset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isUnit_one ?_
  intro x hx
  obtain ⟨R, -, rfl⟩ := Multiset.mem_map.mp hx
  exact (pointIdeal' W R).isUnit

omit [Fact p.Prime] in
/-- **Divisibility of the point group**: `[p]` is surjective on the
points of a nonsingular Weierstrass curve over an algebraically closed
field of characteristic prime to `p` (`TorsionCard.smul_surjective`,
transported along the trivial base change `W⁄F = W`). -/
theorem exists_zsmul_eq (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0) (R : W.Point) :
    ∃ T : W.Point, (p : ℤ) • T = R := by
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hbc : (WeierstrassCurve.Affine.baseChange W F) = W :=
    WeierstrassCurve.map_id _
  have hsurj := TorsionCard.smul_surjective W hp
  rw [hbc] at hsurj
  exact hsurj R

omit [Fact p.Prime] [IsAlgClosed F] in
/-- **The `p`-torsion enumeration is translation invariant**: for a
`p`-torsion point `T`, translating the enumeration `val` of `E[p]` by
`T` permutes it, so the two multisets agree. -/
lemma map_add_torsion_eq {ι : Type*} [Fintype ι] {val : ι → W.Point}
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    {T : W.Point} (hT : (p : ℤ) • T = 0) :
    (Finset.univ.val.map fun i => T + val i) =
      Finset.univ.val.map fun i => val i := by
  classical
  have hex : ∀ i : ι, ∃ j : ι, val j = T + val i := fun i =>
    hval_surj _ (by rw [smul_add, hT, hval_tor i, add_zero])
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro i j hij
    have h1 : T + val i = T + val j := by rw [← hf i, ← hf j, hij]
    exact hval_inj (add_left_cancel h1)
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  have h2 : (Finset.univ.val.map
      fun i => val (Equiv.ofBijective f hbij i)) =
      Finset.univ.val.map fun i => val i :=
    map_univ_comp_equiv (Equiv.ofBijective f hbij) val
  rw [← h2]
  exact Multiset.map_congr rfl fun i _ => (hf i).symm

/-- **L4-7 brick (sorry): the affine divisor of a nonzero coordinate
function.**  Every nonzero `z ∈ F[W]` has `Ideal.span {z}` equal to a
product of point ideals at affine points — the affine part of `div z`,
`Σ_R v_R(z)·(R)`, read as a multiset of affine points.

Proof plan: `W.Δ ≠ 0` makes the affine curve smooth, so `F[W]` is a
Dedekind domain (noetherian — a finite `F[X]`-algebra; dimension one;
integrally closed at every smooth point), whence `Ideal.span {z}`
factors uniquely into maximal ideals.  `F` being algebraically closed,
the weak Nullstellensatz identifies the maximal ideals of
`F[X, Y]/⟨W⟩` with the affine points of `W`: a maximal ideal `m` has
`F[W]/m = F` (Zariski's lemma), and the images of `X`, `Y` are the
coordinates `(x, y)` of a point of `W`, so `m ⊇ ⟨X − x, Y − y⟩` and
equality follows since `⟨X − x, Y − y⟩ = pointIdeal W (some x y _)` is
already maximal (`CoordinateRing.quotientXYIdealEquiv`).  The point
`O` never occurs, `pointIdeal W 0 = ⊤` being the unit ideal. -/
theorem exists_multiset_span_eq_prod_pointIdeal (hΔ : W.Δ ≠ 0)
    {z : W.CoordinateRing} (hz : z ≠ 0) :
    ∃ D : Multiset W.Point, (0 : W.Point) ∉ D ∧
      Ideal.span {z} = (D.map (pointIdeal W)).prod := by
  sorry

/-- **L4-7 brick (sorry): the multiplicity-one `[p]`-pullback formula
for a coordinate function.**  Let `val` enumerate `E[p]`, let
`(xp, yp)` be the affine coordinates of the generic multiple
`p • taut` — so that `pointEval (constHom W) hpn.left` realizes the
pullback `z ↦ z ∘ [p]` on `F[W]` with values in `K = Frac F[W]` — and
let `sec` be a section of `[p]` on points.  If the nonzero `z ∈ F[W]`
has affine divisor `D` (a multiset of affine points), then

`([p]^*z) · [p]^*(O)^{#D} = ∏_{R ∈ D} [p]^*(R)`

as fractional ideals, with `[p]^*(R) = fiberProd val (sec R)`.

Proof plan (HLEG-NOTES.md §4(B), stage L4-7): the full divisor of `z`
is `Σ_{R ∈ D} (R) − #D·(O)` (the pole order at the unique place at
infinity equals the affine degree, `deg div z = 0`), and pullback along
a finite morphism is a homomorphism of divisor groups.  For the fiber
multiplicities: the fiber of the vertical `X − x_R` under `[p]` is cut
out by the division-polynomial pullback `Φ_p − x_R·Ψ_p²` (mathlib's
`WeierstrassCurve.Φ` / `ΨSq`; `Φ_p` is monic of degree `p²` by
`natDegree_Φ`/`coeff_Φ`), which is separable because `(p : F) ≠ 0` —
so each of the `p²` fiber points occurs with multiplicity one, i.e.
`[p]^*(R) = Σ_{S ∈ sec R ⊕ E[p]} (S)` = `fiberProd val (sec R)`; and
the fiber over `O` is `E[p]` itself, `[p]^*(O) = Σ_κ (κ)`.  Reading
the resulting divisor identity through the Dedekind factorization of
`F[W]` gives the displayed fractional-ideal identity (the affine part
is all a fractional ideal sees). -/
theorem spanSingleton_pointEval_mul_fiberProd_pow {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {sec : W.Point → W.Point} (hsec : ∀ R : W.Point, (p : ℤ) • sec R = R)
    {z : W.CoordinateRing} (hz : z ≠ 0)
    (hzev : pointEval (constHom W) hpn.left z ≠ 0)
    {D : Multiset W.Point} (hD0 : (0 : W.Point) ∉ D)
    (hD : Ideal.span {z} = (D.map (pointIdeal W)).prod) :
    (D.map fun R => fiberProd W val (sec R)).prod =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left z) *
        fiberProd W val (sec 0) ^ Multiset.card D := by
  sorry

/-- **L4-7 substrate brick (sorry): point-adic multiplicities on the
unit fractional ideals of `F[W]`.**  For a nonsingular affine
Weierstrass curve (`W.Δ ≠ 0`) over an algebraically closed field there
is an integer-valued *multiplicity* `mult S` — one for every affine
point `S ≠ O` — on the fractional ideals of `F[W]`, additive on
products of unit (equivalently, invertible) fractional ideals and
normalized so that the point ideal of `S` has multiplicity one while
the point ideal of every other point has multiplicity zero.  This is
the exponent of the maximal ideal `pointIdeal W S` in the unique
factorization of an invertible fractional ideal; it is the only input
the fiber-counting brick `fiberProd_prod_inj` needs from the Dedekind
property of `F[W]`.

Proof plan: `W.Δ ≠ 0` makes the affine curve smooth, so `F[W]` is a
Dedekind domain — noetherian (a finite `F[X]`-algebra, mathlib's
`CoordinateRing.instModuleFinite`-style presentation), of dimension one
(a nonzero prime of a one-dimensional affine domain is maximal), and
integrally closed (regular at every point since `Δ ≠ 0`).  `F` being
algebraically closed, the weak Nullstellensatz identifies the maximal
ideals of `F[X, Y]/⟨W⟩` with the affine points of `W`: `pointIdeal W S`
is maximal for `S ≠ O` because
`CoordinateRing.quotientXYIdealEquiv` exhibits `F[W]/pointIdeal W S ≃ F`,
and distinct points give distinct ideals since `pointIdeal W S` cuts
out exactly `S`.  Take `mult S I` to be the `(pointIdeal W S)`-adic
valuation of `I` (`IsDedekindDomain.HeightOneSpectrum.valuation`, or
equivalently the multiplicity of `pointIdeal W S` in the factorization
of `I` as a `FractionalIdeal`): it is a group homomorphism on the units
of the fractional-ideal monoid, sends `pointIdeal' W S` to `1`, sends
`pointIdeal' W R` for an affine `R ≠ S` to `0` (distinct maximal
ideals), and sends `pointIdeal' W O = 1` to `0`. -/
theorem exists_pointMult (hΔ : W.Δ ≠ 0) :
    ∃ mult : W.Point → FractionalIdeal W.CoordinateRing⁰ W.FunctionField → ℤ,
      (∀ (S : W.Point)
          (I J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField),
          IsUnit I → IsUnit J → mult S (I * J) = mult S I + mult S J) ∧
      (∀ S : W.Point, S ≠ 0 →
        mult S (pointIdeal' W S :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = 1) ∧
      (∀ S R : W.Point, S ≠ 0 → R ≠ S →
        mult S (pointIdeal' W R :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = 0) := by
  sorry

/-- **L4-7 brick (PROVEN over `exists_pointMult`): the fiber-product
map is injective on divisors.**  Distinct base points have disjoint
`[p]`-fibers (if `p • S = R₁` and `p • S = R₂` then `R₁ = R₂`), each
fiber is a set of `p²` distinct points, and at most one of them (the
origin, in the fiber over `O`) has trivial point ideal; so
`fiberProd val (sec R)` is a product of at least `p² − 1 ≥ 3` pairwise
distinct maximal ideals, and these supports are pairwise disjoint as
`R` varies.  Unique factorization of fractional ideals over the
Dedekind domain `F[W]` therefore recovers the multiset `D` from
`∏_{R ∈ D} fiberProd val (sec R)`.

The formalized proof reads off the multiplicity `mult S`
(`exists_pointMult`) of the maximal ideal `pointIdeal W S` on both
sides, for each affine `S ≠ O`.  Because `i ↦ T + val i` is injective
with image the whole `[p]`-fiber through `T`, the fiber product
contributes `mult S (fiberProd val T) = 1` when `p • S = p • T` and `0`
otherwise; summing over the multiset gives
`mult S (∏_{R ∈ D} fiberProd val (sec R)) = Multiset.count (p • S) D`.
So `count R D₁ = count R D₂` for every `R` of the form `p • S` with
`S ≠ O` — which is every point, since `[p]` is surjective
(`exists_zsmul_eq`) and `E[p]` contains a nonzero point (`#E[p] = p²`),
available as a nonzero preimage of `O`. -/
theorem fiberProd_prod_inj {ι : Type*} [Fintype ι] {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {sec : W.Point → W.Point} (hsec : ∀ R : W.Point, (p : ℤ) • sec R = R)
    {D₁ D₂ : Multiset W.Point}
    (h : (D₁.map fun R => fiberProd W val (sec R)).prod =
      (D₂.map fun R => fiberProd W val (sec R)).prod) :
    D₁ = D₂ := by
  classical
  obtain ⟨mult, hmul, hself, hother⟩ := exists_pointMult (W := W) hΔ
  -- ── `mult S` kills the trivial unit fractional ideal
  have hone : ∀ S : W.Point, mult S 1 = 0 := by
    intro S
    have h1 := hmul S 1 1 isUnit_one isUnit_one
    rw [one_mul] at h1
    omega
  -- ── `mult S` of a point-ideal product counts the copies of `S`
  have hcountM : ∀ S : W.Point, S ≠ 0 → ∀ M : Multiset W.Point,
      mult S ((M.map fun R =>
        (pointIdeal' W R :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) =
        (Multiset.count S M : ℤ) := by
    intro S hS M
    induction M using Multiset.induction with
    | empty => simpa using hone S
    | cons R M ih =>
      have hR : mult S (pointIdeal' W R :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
          (if S = R then (1 : ℤ) else 0) := by
        by_cases hRS : S = R
        · subst hRS
          rw [hself S hS, if_pos rfl]
        · rw [hother S R hS fun hc => hRS hc.symm, if_neg hRS]
      rw [Multiset.map_cons, Multiset.prod_cons,
        hmul S _ _ (pointIdeal' W R).isUnit (isUnit_prod_coe_pointIdeal' M),
        ih, Multiset.count_cons, hR]
      split_ifs with hRS
      · push_cast
        ring
      · push_cast
        ring
  -- ── the fiber products are unit fractional ideals
  have hufib : ∀ T : W.Point, IsUnit (fiberProd W val T) := by
    intro T
    exact isUnit_prod_coe_pointIdeal' _
  have huprod : ∀ D : Multiset W.Point,
      IsUnit ((D.map fun R => fiberProd W val (sec R)).prod) := by
    intro D
    refine Multiset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro x hx
    obtain ⟨R, -, rfl⟩ := Multiset.mem_map.mp hx
    exact hufib _
  -- ── `mult S` of a fiber product: `1` exactly on the fiber through `S`
  have hfib : ∀ S T : W.Point, S ≠ 0 →
      mult S (fiberProd W val T) =
        (if (p : ℤ) • S = (p : ℤ) • T then (1 : ℤ) else 0) := by
    intro S T hS
    have hmem : S ∈ (Finset.univ.val.map fun i => T + val i) ↔
        (p : ℤ) • S = (p : ℤ) • T := by
      constructor
      · intro hin
        obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hin
        rw [← hi, smul_add, hval_tor i, add_zero]
      · intro hpS
        obtain ⟨i, hi⟩ := hval_surj (S - T) (by rw [smul_sub, hpS, sub_self])
        exact Multiset.mem_map.mpr
          ⟨i, Finset.mem_val.mpr (Finset.mem_univ i), by rw [hi]; abel⟩
    have hunf : fiberProd W val T =
        ((Finset.univ.val.map fun i => T + val i).map fun R =>
          (pointIdeal' W R :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := rfl
    rw [hunf, hcountM S hS]
    by_cases hpST : (p : ℤ) • S = (p : ℤ) • T
    · have hnd : (Finset.univ.val.map fun i => T + val i).Nodup :=
        Multiset.Nodup.map (fun i j hij => hval_inj (add_left_cancel hij))
          Finset.univ.nodup
      simp [hpST, Multiset.count_eq_one_of_mem hnd (hmem.mpr hpST)]
    · rw [if_neg hpST]
      exact_mod_cast Multiset.count_eq_zero_of_notMem fun hc => hpST (hmem.mp hc)
  -- ── `mult S` of the whole product counts the copies of `p • S`
  have hbig : ∀ S : W.Point, S ≠ 0 → ∀ D : Multiset W.Point,
      mult S ((D.map fun R => fiberProd W val (sec R)).prod) =
        (Multiset.count ((p : ℤ) • S) D : ℤ) := by
    intro S hS D
    induction D using Multiset.induction with
    | empty => simpa using hone S
    | cons R D ih =>
      rw [Multiset.map_cons, Multiset.prod_cons,
        hmul S _ _ (hufib (sec R)) (huprod D), ih, hfib S (sec R) hS,
        Multiset.count_cons]
      simp only [hsec]
      split_ifs with hc
      · push_cast
        ring
      · push_cast
        ring
  -- ── a nonzero `p`-torsion point exists, since `#E[p] = p² > 1`
  obtain ⟨i₀, hi₀⟩ := hval_surj 0 (smul_zero _)
  have h1lt : 1 < Fintype.card ι := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h4 : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
    rw [hcard]
    exact lt_of_lt_of_le (by norm_num) h4
  obtain ⟨i₁, hi₁⟩ := Fintype.exists_ne_of_one_lt_card h1lt i₀
  have hval_ne : val i₁ ≠ 0 := fun h0 => hi₁ (hval_inj (h0.trans hi₀.symm))
  -- ── every point is `p • S` for some NONZERO `S`
  have hpre : ∀ R : W.Point, ∃ S : W.Point, S ≠ 0 ∧ (p : ℤ) • S = R := by
    intro R
    obtain ⟨S, hS⟩ := exists_zsmul_eq (W := W) hΔ hp R
    by_cases hS0 : S = 0
    · refine ⟨val i₁, hval_ne, ?_⟩
      rw [hval_tor i₁, ← hS, hS0, smul_zero]
    · exact ⟨S, hS0, hS⟩
  -- ── compare the two multisets count by count
  refine Multiset.ext.mpr fun R => ?_
  obtain ⟨S, hS0, hS⟩ := hpre R
  have h₁ := hbig S hS0 D₁
  have h₂ := hbig S hS0 D₂
  rw [h, h₂, hS] at h₁
  exact_mod_cast h₁.symm

/-- **L4-7 (PROVEN over the three fiber bricks): multiplicity-one
`[p]^*`-comparison — a divisor relation between pullbacks descends to
the base.**  Let
`val : ι → W.Point` enumerate the `p`-torsion subgroup
(`card ι = p²`, `(p : F) ≠ 0`, so `[p]` is a separable isogeny whose
fibers are the `p²` torsion translates), let `(xp, yp)` be the affine
coordinates of the generic point `p • taut` — where `pointEval`
realizes `z ↦ z ∘ [p]` — and let `b, c` be nonzero coordinate-ring
elements with nonvanishing pullbacks `[p]^*(b), [p]^*(c)` satisfying
the fractional-ideal comparison

`∏_{R ∈ Σ(T'⊕κᵢ)+(⊖κᵢ)} I'_R · ([p]^*c) = ∏_{R ∈ Σ(κᵢ)+(⊖κᵢ)} I'_R · ([p]^*b)`

(unit point-ideal products against `spanSingleton`s of the
evaluations — the multiplied-out form of "`[p]^*(b/c)` has the divisor
`Σ_κ (T'⊕κ) − (κ) = [p]^*((P) − (O))` of the Miller ratio `a/v`").
Then the downstairs spans compare with exactly ONE copy of the point
ideal of `P = p•T'`:  `(b) = I_P · (c)`.

Proof plan (HLEG-NOTES.md §4(B), stage L4-7): the affine divisor of
`[p]^*(z)` for `z ∈ F[W]` is the `[p]`-pullback of the full divisor
of `z`: writing `div z = Σ_R m_R·(R) − n·(O)` (`n = Σ m_R`), each
affine `(R)` pulls back to its fiber `Σ_{p•S = R} (S)` WITH
MULTIPLICITY ONE — the fiber of a vertical `X − x_R` is cut out by
the division-polynomial pullback `Φ_p − x_R·Ψ_p²` (mathlib's
`WeierstrassCurve.Φ`/`ΨSq`; `Φ_p` is monic of degree `p²` by
`natDegree_Φ`/`coeff_Φ`), separable since `(p : F) ≠ 0` — and the
pole `(O)` pulls back to `Σ_i (val i)` away from infinity.  Fibers
over distinct base points are disjoint (`hval_inj` plus the group
law: `p•S = p•S'` iff `S' ⊖ S ∈ E[p]`), so matching pointIdeal
multiplicities on the two sides of `hcmp` — via unique factorization
of fractional ideals once `IsDedekindDomain F[W]` is established (the
affine curve is nonsingular since `Δ ≠ 0`, and its maximal ideals are
exactly the point ideals, `F` being algebraically closed) — forces
`div(b) − div(c) = (P) − (O)`, i.e. `(b) = I_P·(c)` on affine parts.
In the degenerate case `P = O` the two fiber products coincide, the
comparison gives `(b) = (c)`, and `I_O = ⊤` keeps the statement
uniform.  See HLEG-NOTES.md §4(B), stage L4-7.

The formalized assembly runs over the three fiber bricks above.  Write
`J_R := fiberProd val (sec R)` for a section `sec` of `[p]` on points
(`exists_zsmul_eq`) normalized by `sec P = T'`, and note
`J_0 = ∏_i I'_{val i}` because the fiber over `O` is `E[p]` whatever
preimage is chosen (`map_add_torsion_eq`).  Cancelling the unit factor
`∏_i I'_{⊖val i}` from `hcmp` gives `J_P·([p]^*c) = J_0·([p]^*b)`.
The divisor brick supplies affine divisors `D_b`, `D_c` of `b`, `c`,
the pullback brick turns them into
`∏_{R ∈ D_z} J_R = ([p]^*z)·J_0^{#D_z}`, and multiplying the cancelled
comparison by `J_0^{#D_b + #D_c}` yields
`∏_{R ∈ P ::ₘ D_c + #D_b·(O)} J_R = ∏_{R ∈ D_b + (#D_c+1)·(O)} J_R`.
Injectivity of the fiber-product map then equates the two multisets;
counting copies of `O` gives `#D_b = #D_c + 1` (resp. `#D_b = #D_c`
when `P = O`) and cancellation leaves `D_b = P ::ₘ D_c` (resp.
`D_b = D_c`), which is the asserted span identity. -/
theorem span_eq_pointIdeal_mul_of_pullback {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {P T' : W.Point} (hT : (p : ℤ) • T' = P)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {b c : W.CoordinateRing} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbev : pointEval (constHom W) hpn.left b ≠ 0)
    (hcev : pointEval (constHom W) hpn.left c ≠ 0)
    (hcmp : ((((Finset.univ.val.map fun i => T' + val i) +
          Finset.univ.val.map fun i => -val i)).map fun R =>
          (pointIdeal' W R :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod *
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left c) =
      ((((Finset.univ.val.map fun i => val i) +
          Finset.univ.val.map fun i => -val i)).map fun R =>
          (pointIdeal' W R :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod *
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left b)) :
    Ideal.span {b} = pointIdeal W P * Ideal.span {c} := by
  classical
  -- ── a section of `[p]` on points, normalized to send `P` to `T'`
  obtain ⟨sec, hsec, hsecP⟩ : ∃ s : W.Point → W.Point,
      (∀ R : W.Point, (p : ℤ) • s R = R) ∧ s P = T' := by
    choose s hs using exists_zsmul_eq (W := W) hΔ hp
    refine ⟨fun R => if R = P then T' else s R, fun R => ?_, by simp⟩
    show (p : ℤ) • (if R = P then T' else s R) = R
    by_cases h : R = P
    · rw [if_pos h, hT]
      exact h.symm
    · rw [if_neg h]
      exact hs R
  -- ── the two fiber products occurring in `hcmp`
  have hAfib : ((Finset.univ.val.map fun i => T' + val i).map fun R =>
      (pointIdeal' W R :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod =
      fiberProd W val (sec P) := by
    unfold fiberProd
    rw [hsecP]
  have hBfib : ((Finset.univ.val.map fun i => val i).map fun R =>
      (pointIdeal' W R :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod =
      fiberProd W val (sec 0) := by
    unfold fiberProd
    rw [map_add_torsion_eq hval_inj hval_tor hval_surj (hsec 0)]
  -- ── cancel the common unit factor `∏ I'_{⊖val i}` from `hcmp`
  simp only [Multiset.map_add, Multiset.prod_add] at hcmp
  rw [hAfib, hBfib] at hcmp
  have hunitN : IsUnit (((Finset.univ.val.map fun i => -val i).map fun R =>
      (pointIdeal' W R :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) :=
    isUnit_prod_coe_pointIdeal' _
  have hA : fiberProd W val (sec P) *
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left c) =
      fiberProd W val (sec 0) *
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left b) := by
    refine hunitN.mul_right_cancel ?_
    rw [mul_right_comm, hcmp, mul_right_comm]
  -- ── the affine divisors of `b` and `c`, and their `[p]`-pullbacks
  obtain ⟨Db, hDb0, hDb⟩ := exists_multiset_span_eq_prod_pointIdeal hΔ hb
  obtain ⟨Dc, hDc0, hDc⟩ := exists_multiset_span_eq_prod_pointIdeal hΔ hc
  have hSb := spanSingleton_pointEval_mul_fiberProd_pow (val := val) hΔ hp
    hval_inj hval_tor hval_surj hcard hptaut hsec hb hbev hDb0 hDb
  have hSc := spanSingleton_pointEval_mul_fiberProd_pow (val := val) hΔ hp
    hval_inj hval_tor hval_surj hcard hptaut hsec hc hcev hDc0 hDc
  -- ── the comparison, multiplied out over the fiber products
  have hkey : ((P ::ₘ (Dc + Multiset.replicate (Multiset.card Db) 0)).map
        fun R => fiberProd W val (sec R)).prod =
      ((Db + Multiset.replicate (Multiset.card Dc + 1) 0).map
        fun R => fiberProd W val (sec R)).prod := by
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_add,
      Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
    rw [hSb, hSc, ← mul_assoc, ← mul_assoc, hA]
    ring
  have hmulti := fiberProd_prod_inj (val := val) hΔ hp hval_inj hval_tor
    hval_surj hcard hsec hkey
  by_cases hP0 : P = 0
  · -- ── degenerate case `P = O`: the divisors of `b` and `c` agree
    subst hP0
    have hcount := congrArg (Multiset.count (0 : W.Point)) hmulti
    simp only [Multiset.count_cons_self, Multiset.count_add,
      Multiset.count_replicate_self, Multiset.count_eq_zero_of_notMem hDc0,
      Multiset.count_eq_zero_of_notMem hDb0, zero_add] at hcount
    have hmn : Multiset.card Db = Multiset.card Dc := by omega
    rw [hmn, show (0 : W.Point) ::ₘ
        (Dc + Multiset.replicate (Multiset.card Dc) 0) =
        Dc + Multiset.replicate (Multiset.card Dc + 1) 0 from by
      rw [Multiset.replicate_succ, ← Multiset.singleton_add,
        ← Multiset.singleton_add, add_left_comm]] at hmulti
    have hDbc := add_right_cancel hmulti
    rw [hDb, hDc, pointIdeal_zero, Ideal.top_mul, hDbc]
  · -- ── generic case: the divisor of `b` is `(P)` plus that of `c`
    have hcount := congrArg (Multiset.count (0 : W.Point)) hmulti
    simp only [Multiset.count_cons_of_ne (fun h : (0 : W.Point) = P =>
        hP0 h.symm), Multiset.count_add, Multiset.count_replicate_self,
      Multiset.count_eq_zero_of_notMem hDc0,
      Multiset.count_eq_zero_of_notMem hDb0, zero_add] at hcount
    rw [← hcount, ← Multiset.cons_add] at hmulti
    have hDbc := add_right_cancel hmulti
    rw [hDb, hDc, ← hDbc, Multiset.map_cons, Multiset.prod_cons]

/-- **L4-9 divisor comparison (PROVEN glue over the L4-7 brick
`span_eq_pointIdeal_mul_of_pullback`): a `[p]^*`-descended Miller
generator forces a trivial class.**  Let `a` be the Miller generator
(`span {a} = ∏ pointIdeal (T'⊕κᵢ) · pointIdeal (⊖κᵢ)`, so
`g := a/∏(X − x_κ)` has divisor `Σ_κ (T'⊕κ) − (κ) = [p]^*((P) − (O))`
for `p•T' = P`), and suppose `g = h∘[p]` for `h = b/c ∈ K` — stated
multiplied out at the affine coordinates `(xp, yp)` of the generic
point `p • taut`, where `pointEval` realizes `h ↦ h∘[p]`:
`ā·[p]^*(c) = v̄·[p]^*(b)` with `v = enumVertical` and `[p]^*(c) ≠ 0`.
Then `toClass P = 0`.

Proof plan (HLEG-NOTES.md §4(B), stages L4-7/9): the `[p]`-pullback of
divisors is injective and `[p]^*((P) − (O)) = div g = [p]^*(div h)`,
so `div h = (P) − (O)` — concretely, the `[p]`-pullback of a vertical
`X − x₀` is the explicit polynomial `Φ_p − x₀·Ψ_p²` whose root multiset
is the `p²`-fiber with multiplicity one (separability from
`(p : F) ≠ 0`, `separable_preΨ'` machinery), so comparing the span
`hspan` against the pullback of the span-encoding of `div h` fiber by
fiber (torsion enumeration `hval_*`, `p•T' = P`, `p•P = 0`) forces
`span-level (b)·I_P-data = (c)`-data with multiplicity one; hence the
unit fractional ideal `pointIdeal' P` is principal (`spanSingleton` of
the descended function) and `toClass P = mk (pointIdeal' P) = 0` by
`mk_pointIdeal'`.  (For `P = O` the conclusion is `toClass 0 = 0`.)
See HLEG-NOTES.md §4(B), stages L4-7/9. -/
theorem toClass_eq_zero_of_pullback {ι : Type*} [Fintype ι]
    {val : ι → W.Point}
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    (hcard : Fintype.card ι = p ^ 2)
    {P T' : W.Point} (hT : (p : ℤ) • T' = P) (_hPtor : (p : ℤ) • P = 0)
    {a : W.CoordinateRing} (ha : a ≠ 0)
    (hspan : Ideal.span {a} =
      ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map (pointIdeal W)).prod)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {b c : W.CoordinateRing} (hb : b ≠ 0) (hc : c ≠ 0)
    (hcnz : pointEval (constHom W) hpn.left c ≠ 0)
    (heq : algebraMap W.CoordinateRing W.FunctionField a *
        pointEval (constHom W) hpn.left c =
      algebraMap W.CoordinateRing W.FunctionField (enumVertical W val) *
        pointEval (constHom W) hpn.left b) :
    WeierstrassCurve.Affine.Point.toClass P = 0 := by
  classical
  have hinj := IsFractionRing.injective W.CoordinateRing W.FunctionField
  -- ── the pullback of `b` is nonzero (from `heq`, since `ā·[p]^*(c) ≠ 0`)
  have haa0 : algebraMap W.CoordinateRing W.FunctionField a ≠ 0 := fun h0 =>
    ha ((map_eq_zero_iff _ hinj).mp h0)
  have hbev : pointEval (constHom W) hpn.left b ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at heq
    exact mul_ne_zero haa0 hcnz heq
  -- ── `heq` as the fractional-ideal comparison of the two point-ideal
  --    products (the span factorizations of `a` and `enumVertical`)
  have hcmp : ((((Finset.univ.val.map fun i => T' + val i) +
        Finset.univ.val.map fun i => -val i)).map fun R =>
        (pointIdeal' W R :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod *
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left c) =
      ((((Finset.univ.val.map fun i => val i) +
        Finset.univ.val.map fun i => -val i)).map fun R =>
        (pointIdeal' W R :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod *
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left b) := by
    rw [prod_coe_pointIdeal'_eq_spanSingleton hspan,
      prod_coe_pointIdeal'_eq_spanSingleton (span_enumVertical (W := W) val),
      FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, heq]
  -- ── the descended span relation `(b) = I_P·(c)` (the L4-7 brick)
  have hspanbc := span_eq_pointIdeal_mul_of_pullback hΔ hp hval_inj hval_tor
    hval_surj hcard hT hptaut hb hc hbev hcnz hcmp
  -- ── hence `I'_P` is the principal fractional ideal of `b̄/c̄`
  have hcc0 : algebraMap W.CoordinateRing W.FunctionField c ≠ 0 := fun h0 =>
    hc ((map_eq_zero_iff _ hinj).mp h0)
  have hfrac : FractionalIdeal.spanSingleton W.CoordinateRing⁰
      (algebraMap W.CoordinateRing W.FunctionField b) =
      (pointIdeal' W P :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField c) := by
    have h4 := congrArg (fun I : Ideal W.CoordinateRing =>
      (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) hspanbc
    simp only [FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_span_singleton] at h4
    rw [← coe_pointIdeal'] at h4
    exact h4
  have hIP : (pointIdeal' W P :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField b *
          (algebraMap W.CoordinateRing W.FunctionField c)⁻¹) := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, hfrac, mul_assoc,
      FractionalIdeal.spanSingleton_mul_spanSingleton,
      mul_inv_cancel₀ hcc0, FractionalIdeal.spanSingleton_one, mul_one]
  -- ── the class of `P` vanishes
  have hsub : ((pointIdeal' W P :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField) :
      Submodule W.CoordinateRing W.FunctionField) =
      Submodule.span W.CoordinateRing
        {algebraMap W.CoordinateRing W.FunctionField b *
          (algebraMap W.CoordinateRing W.FunctionField c)⁻¹} := by
    rw [hIP, FractionalIdeal.coe_spanSingleton]
  have hmk1 : ClassGroup.mk W.FunctionField (pointIdeal' W P) = 1 :=
    ClassGroup.mk_eq_one_iff.mpr ⟨⟨_, hsub⟩⟩
  exact Additive.toMul.injective
    (((mk_pointIdeal' P).symm.trans hmk1).trans toMul_zero.symm)

/-- **L4-9, first branch (PROVEN glue over the two stage nodes):
trivial translation character forces a trivial class.**  If the translation character of the Miller
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
  obtain ⟨xp, yp, hpn, hptaut, b, c, hb, hc, hcnz, heq⟩ :=
    exists_pullback_of_translation_fixed hΔ hp hval_inj hval_tor hval_surj
      hcard ha (enumVertical_ne_zero W val) htriv
  exact toClass_eq_zero_of_pullback hΔ hp hval_inj hval_tor hval_surj hcard
    hT hPtor ha hspan hptaut hb hc hcnz heq

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
