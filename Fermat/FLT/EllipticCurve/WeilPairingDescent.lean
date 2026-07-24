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

variable {p : ℕ} [Fact p.Prime] [IsAlgClosed F]

/-- **L4-8 numerator leaf (sorry): the divisor of the vertical
numerator.**  `vertNumerator q₁ q₂ x` spans
`I_Q² · I_{P⊖Q} · I_{⊖P⊖Q}` for `P = (x, y)`, `Q = (q₁, q₂)` — its
affine divisor is `2(Q) + (P⊖Q) + (⊖P⊖Q)` (which sums to `O`, so the
span is principal, consistently).  The `O`-convention `I_O = ⊤` makes
the statement uniform in the degenerate configurations `P = ±Q`
(a zero escapes to infinity and the corresponding factor is `⊤`).
CAS-checked numerically (PARI/GP: `y² = x³ − x + 1`, `Q = (1,1)`,
`P = (3,5)`: vanishing at `Q` to second order and at `P⊖Q = (5,−11)`,
`⊖P⊖Q = (0,−1)`).  Provable by the span-pair calculus of mathlib's
`XYIdeal_mul_XYIdeal` (membership certificates, e.g. found with
Singular/PARI), or by valuation comparison after
`IsDedekindDomain F[W]`. -/
theorem span_vertNumerator (hΔ : W.Δ ≠ 0) {q₁ q₂ x y : F}
    (hq : W.Nonsingular q₁ q₂) (h : W.Nonsingular x y) :
    Ideal.span {vertNumerator W q₁ q₂ x} =
      pointIdeal W (.some q₁ q₂ hq) ^ 2 *
        (pointIdeal W (.some x y h - .some q₁ q₂ hq) *
          pointIdeal W (-.some x y h - .some q₁ q₂ hq)) := by
  sorry

/-- **L4-8 numerator leaf (sorry): the divisor of the line
numerator.**  `lineNumerator q₁ q₂ x₁ y₁ ℓ` (at the group-law slope
`ℓ` of the pair `P = (x₁,y₁)`, `R = (x₂,y₂)`) spans
`I_Q³ · I_{P⊖Q} · I_{R⊖Q} · I_{⊖(P⊕R)⊖Q}` — its affine divisor is the
`⊖Q`-translate of the divisor `(P) + (R) + (⊖(P⊕R)) − 3(O)` of the
line through `P` and `R`, cleared by `3(Q)`.  CAS-checked numerically
(PARI/GP: `y² = x³ − x + 1`, `Q = (1,1)`, `P = (3,5)`, `R = (0,1)`:
vanishing at `Q` to third order and at the three translated points).
Same proof routes as `span_vertNumerator`. -/
theorem span_lineNumerator (hΔ : W.Δ ≠ 0) {q₁ q₂ x₁ y₁ x₂ y₂ : F}
    (hq : W.Nonsingular q₁ q₂) (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    Ideal.span {lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂)} =
      pointIdeal W (.some q₁ q₂ hq) ^ 3 *
        (pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
          (pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
            pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) -
              .some q₁ q₂ hq))) := by
  sorry

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
  sorry

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
  sorry

/-- **L4-8 core (sorry node): divisor transport along evaluation at a
generic translate.**  Let `b ∈ F[W]` generate the point-ideal product
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

PROOF PLAN (Miller-style reduction to lines).  Both sides are
multiplicative in `(b, D)` (`spanSingleton` of a product splits, and
the span hypothesis composes multiset-additively), and any generator
of a point-ideal product reduces, by the group-law ideal calculus
(`XYIdeal_mul_XYIdeal`, `XYIdeal_neg_mul` — the engine already
extracted at `F`-points in WeilPairing.lean's `MillerEngine`), to a
product of line classes `Y − (λX + ν)` (span `I_P·I_R·I_{⊖(P⊕R)}`,
`|D| = 3`) and vertical classes `X − x_P` (span `I_P·I_{⊖P}`,
`|D| = 2`) and unit constants (`|D| = 0`, evaluation is a constant of
trivial divisor — `coordinateRing_isUnit_eq_const`).  For a vertical,
`τ_Q^*(X − x_P) = x(Q ⊕ taut) − x_P` is an explicit rational function
of `(tautX, tautY)` by the addition formula, with numerator span
`I_{P⊖Q}·I_{⊖P⊖Q}·(vertical correction)` and denominator `I_{⊖Q}²`
(the double pole of `x` at `O` pulled back through the translation) —
computed by the same `C_simp`/`linear_combination` ideal calculus as
the mathlib group-law lemmas; a line is analogous with `I_{⊖Q}³`.
Alternatively: establish `IsDedekindDomain F[W]` (the affine curve is
nonsingular for `Δ ≠ 0`) and compare the two sides
valuation-by-valuation at height-one primes.  See HLEG-NOTES.md §4(B),
stage L4-8. -/
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

/-- **L4-5/6 Galois core (sorry node): every element of the function
field fixed by all lifted translation evaluations lies in the range of
the `[p]`-pullback embedding — `Fix E[p] ⊆ [p]^*K`.**  Let
`val : ι → W.Point` enumerate the `p`-torsion subgroup
(`card ι = p²`), `(xp, yp)` the affine coordinates of the generic
multiple `p • taut` with the division-polynomial relation `hxrel`, and
`hinj` the injectivity of evaluation at `(xp, yp)`; suppose
`z ∈ K = Frac F[W]` is fixed by the fraction-field extension of every
translation evaluation (`hz`, quantified over all coordinate
presentations of the translates `κ ⊕ taut`).  Then `z = σ_p(h)` for
some `h ∈ K`, where `σ_p = IsFractionRing.lift hinj : K →+* K`
realizes `h ↦ h ∘ [p]`.

Proof plan (HLEG-NOTES.md §4(B), stages L4-5/6): each lifted
evaluation `σ_κ` is a field automorphism of `K` fixing the constants
(surjectivity from `σ_κ ∘ σ_{⊖κ} = id`, the composition law coming
from `endoMap` additivity and the group law `(taut ⊖ κ) ⊕ κ = taut`);
`κ ↦ σ_κ` is a faithful action of the order-`p²` torsion group on `K`
(faithfulness: `σ_κ tautX = tautX` forces `x(κ ⊕ taut) = x(taut)`, so
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
`Fix E[p] = L ∋ z`.  DECOMPOSE along these stages when opening this
node. -/
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
  sorry

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

/-- **L4-7 (sorry node): multiplicity-one `[p]^*`-comparison — a
divisor relation between pullbacks descends to the base.**  Let
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
uniform.  See HLEG-NOTES.md §4(B), stage L4-7. -/
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
  sorry

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
