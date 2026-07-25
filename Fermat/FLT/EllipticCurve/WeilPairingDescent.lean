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
import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.DedekindDomain.Factorization
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
/-- The constants embedding is the structure map of the `F`-algebra
`F[W]`; through it `map_add`/`map_mul`/`map_pow`/`map_ofNat` expand a
`coordC` of a composite scalar into the coordinate-ring atoms, which is
what `ring`/`linear_combination` need. -/
lemma coordC_eq_algebraMap (d : F) :
    coordC W d = algebraMap F W.CoordinateRing d := rfl

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
lemma coord_equation_coordC (W : WeierstrassCurve.Affine F) :
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
      have hR := coord_equation_coordC W
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
/-- **L4-8 line-numerator sub-leaf (PROVEN): the cleared conjugate
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
expanded goal.

That is exactly how it is proven below, in a *single*
`linear_combination`, with the four cofactors read off a PARI/GP
reduction (the CAS is used only as a searcher; the kernel checks the
certificate).  Writing `EX := W_X(Q)`, `EY := W_Y(Q)`,
`RQ := W(q₁, q₂)` and `R0` for the coordinate-ring relation
`coord_equation_coordC`, the certificate is

* `−T³·(A − q₁T² − RQ)` against `coord_equation_coordC`, *after* it has
  been normalized by `simp only [coordC_eq_algebraMap]`.  ATOM
  CONSTRAINT, and the one thing to preserve when touching this proof:
  the certificate's atoms are `algebraMap F W.CoordinateRing`
  applications, and `ring` does NOT identify `coordC W c` with
  `algebraMap F W.CoordinateRing c` — the two are `rfl`-equal, yet
  `ring`'s normalizer treats them as *distinct atoms*, so a `coordC`-
  spelled hypothesis leaves unconvertible `coordC W W.a₂/a₄/a₆` in the
  residual and the `linear_combination` fails.  This bit once: a
  de-duplication of the two same-content `coord_equation` lemmas
  repointed `hcr` across spellings and broke the build.  Normalizing the
  hypothesis at the point of use (rather than depending on *which*
  spelling the name `coord_equation` happens to resolve to) is what
  makes this robust to the eventual collapse of the two lemmas,
  whichever spelling survives.  Note the failure does not present as a
  `ring` error: the certificate is large enough that the mismatched
  normal form exhausts the default `maxRecDepth` first, so it surfaces
  as "maximum recursion depth has been reached" inside `simp`.  Raising
  the depth is a diagnostic step only — it reveals the real `ring`
  failure and must not be left in as a fix,
* `−T³·(EY·U + EX·T + T³ + RQ)` against `W.Equation q₁ q₂` (transported
  into `F[W]` along `algebraMap`),
* `−T⁴·A` against the `Cubic.c` coefficient of `addPolynomial_slope`
  (the identity `Σ xᵢxⱼ = a₄ − a₁c − a₃ℓ − 2ℓc`, `c = y₁ − ℓx₁`),
* `−T⁶` against its `Cubic.d` coefficient (`x₁x₂x₃ = c² + a₃c − a₆`).

The `Cubic.b` coefficient (`x₁ + x₂ + x₃ = ℓ² + a₁ℓ − a₂`) needs no
cofactor: it is `ring`-true once `W.addX` is unfolded. -/
theorem lineNumerator_mul_lineNumeratorNeg {q₁ q₂ x₁ y₁ x₂ y₂ : F}
    (hq : W.Equation q₁ q₂) (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) *
        lineNumeratorNeg W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) =
      -(vertNumerator W q₁ q₂ x₁ *
        (vertNumerator W q₁ q₂ x₂ *
          vertNumerator W q₁ q₂ (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)))) := by
  -- the three symmetric-function identities of the chord cubic
  have hAP := WeierstrassCurve.Affine.addPolynomial_slope h₁ h₂ hxy
  rw [WeierstrassCurve.Affine.addPolynomial_eq, neg_inj,
    Cubic.prod_X_sub_C_eq] at hAP
  have hc2 := Cubic.c_of_eq hAP
  have hc3 := Cubic.d_of_eq hAP
  -- the two relations, transported into `F[W]`.  `coord_equation_coordC` is
  -- stated in the `coordC` atoms; `ring` must see the SAME atoms as the
  -- `algebraMap`-shaped hypotheses below, so normalize it first.
  have hcr := coord_equation_coordC W
  simp only [coordC_eq_algebraMap] at hcr
  rw [WeierstrassCurve.Affine.equation_iff'] at hq
  have hqW := congrArg (algebraMap F W.CoordinateRing) hq
  have hc2W := congrArg (algebraMap F W.CoordinateRing) hc2
  have hc3W := congrArg (algebraMap F W.CoordinateRing) hc3
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero,
    WeierstrassCurve.Affine.addX] at hqW hc2W hc3W
  simp only [lineNumerator, lineNumeratorNeg, vertNumerator, coordC_eq_algebraMap,
    WeierstrassCurve.Affine.addX, map_add, map_sub, map_mul, map_pow]
  linear_combination
    (-((coordX W - algebraMap F W.CoordinateRing q₁) ^ 3 *
        (((coordY W - algebraMap F W.CoordinateRing q₂) ^ 2 +
              algebraMap F W.CoordinateRing W.a₁ *
                (coordY W - algebraMap F W.CoordinateRing q₂) *
                (coordX W - algebraMap F W.CoordinateRing q₁) -
              (algebraMap F W.CoordinateRing W.a₂ +
                  algebraMap F W.CoordinateRing q₁ + coordX W) *
                (coordX W - algebraMap F W.CoordinateRing q₁) ^ 2) -
          algebraMap F W.CoordinateRing q₁ *
            (coordX W - algebraMap F W.CoordinateRing q₁) ^ 2 -
          (algebraMap F W.CoordinateRing q₂ ^ 2 +
              algebraMap F W.CoordinateRing W.a₁ *
                algebraMap F W.CoordinateRing q₁ *
                algebraMap F W.CoordinateRing q₂ +
              algebraMap F W.CoordinateRing W.a₃ *
                algebraMap F W.CoordinateRing q₂ -
            (algebraMap F W.CoordinateRing q₁ ^ 3 +
              algebraMap F W.CoordinateRing W.a₂ *
                algebraMap F W.CoordinateRing q₁ ^ 2 +
              algebraMap F W.CoordinateRing W.a₄ *
                algebraMap F W.CoordinateRing q₁ +
              algebraMap F W.CoordinateRing W.a₆))))) * hcr +
    (-((coordX W - algebraMap F W.CoordinateRing q₁) ^ 3 *
        ((2 * algebraMap F W.CoordinateRing q₂ +
              algebraMap F W.CoordinateRing W.a₁ *
                algebraMap F W.CoordinateRing q₁ +
              algebraMap F W.CoordinateRing W.a₃) *
            (coordY W - algebraMap F W.CoordinateRing q₂) +
          (algebraMap F W.CoordinateRing W.a₁ *
                algebraMap F W.CoordinateRing q₂ -
              (3 * algebraMap F W.CoordinateRing q₁ ^ 2 +
                2 * algebraMap F W.CoordinateRing W.a₂ *
                  algebraMap F W.CoordinateRing q₁ +
                algebraMap F W.CoordinateRing W.a₄)) *
            (coordX W - algebraMap F W.CoordinateRing q₁) +
          (coordX W - algebraMap F W.CoordinateRing q₁) ^ 3 +
          (algebraMap F W.CoordinateRing q₂ ^ 2 +
              algebraMap F W.CoordinateRing W.a₁ *
                algebraMap F W.CoordinateRing q₁ *
                algebraMap F W.CoordinateRing q₂ +
              algebraMap F W.CoordinateRing W.a₃ *
                algebraMap F W.CoordinateRing q₂ -
            (algebraMap F W.CoordinateRing q₁ ^ 3 +
              algebraMap F W.CoordinateRing W.a₂ *
                algebraMap F W.CoordinateRing q₁ ^ 2 +
              algebraMap F W.CoordinateRing W.a₄ *
                algebraMap F W.CoordinateRing q₁ +
              algebraMap F W.CoordinateRing W.a₆))))) * hqW +
    (-((coordX W - algebraMap F W.CoordinateRing q₁) ^ 4 *
        ((coordY W - algebraMap F W.CoordinateRing q₂) ^ 2 +
          algebraMap F W.CoordinateRing W.a₁ *
            (coordY W - algebraMap F W.CoordinateRing q₂) *
            (coordX W - algebraMap F W.CoordinateRing q₁) -
          (algebraMap F W.CoordinateRing W.a₂ +
              algebraMap F W.CoordinateRing q₁ + coordX W) *
            (coordX W - algebraMap F W.CoordinateRing q₁) ^ 2))) * hc2W +
    (-((coordX W - algebraMap F W.CoordinateRing q₁) ^ 6)) * hc3W

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

section DedekindFactorization

open Polynomial

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The affine coordinate ring is noetherian**: `F[W]` is free of
rank two over `F[X]` (`CoordinateRing.basis`), hence a finite algebra
over a noetherian ring. -/
lemma isNoetherianRing_coordinateRing (W : WeierstrassCurve.Affine F) :
    IsNoetherianRing W.CoordinateRing :=
  have : Module.Finite F[X] W.CoordinateRing := Module.Finite.of_basis (CoordinateRing.basis W)
  IsNoetherianRing.of_finite F[X] W.CoordinateRing

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Point ideals are maximal**: `F[W]/⟨X − x, Y − y⟩ ≃ F` at a point
of the curve (`CoordinateRing.quotientXYIdealEquiv`), and a quotient by
a field is a maximal ideal. -/
lemma xyIdeal_isMaximal {x y : F} (h : W.Equation x y) :
    (CoordinateRing.XYIdeal W x (C y)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((CoordinateRing.quotientXYIdealEquiv (W' := W) (x := x) (y := C y)
      h).toMulEquiv.isField (Field.toIsField F))

omit [DecidableEq F] in
/-- **Every maximal ideal of `F[W]` contains a vertical**: `F[W]` is
integral over `F[X]` (finite of rank two), so the contraction
`m ∩ F[X]` of a maximal ideal is maximal
(`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`); over the
algebraically closed `F` a maximal ideal of `F[X]` is `⟨X − x₀⟩` (its
generator is a nonunit, hence of nonzero degree, hence has a root), and
`X − x₀` maps to `CoordinateRing.XClass W x₀`. -/
lemma exists_xClass_mem {m : Ideal W.CoordinateRing} (hm : m.IsMaximal) :
    ∃ x : F, CoordinateRing.XClass W x ∈ m := by
  haveI : Module.Finite F[X] W.CoordinateRing := Module.Finite.of_basis (CoordinateRing.basis W)
  haveI : Algebra.IsIntegral F[X] W.CoordinateRing := Algebra.IsIntegral.of_finite _ _
  haveI := hm
  set pc := m.comap (algebraMap F[X] W.CoordinateRing) with hpdef
  have hpmax : pc.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal pc)
  rw [Ideal.submodule_span_eq] at hq
  have hqu : ¬ IsUnit q := fun hu => hpmax.ne_top (by rw [hq, Ideal.span_singleton_eq_top.mpr hu])
  have hqdeg : q.degree ≠ 0 := fun h => hqu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root q hqdeg
  have hdvd : (X - C x₀) ∣ q := dvd_iff_isRoot.mpr hx₀
  have hle : pc ≤ Ideal.span {X - C x₀} := by
    rw [hq, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Ideal.mem_span_singleton]
    exact hdvd
  have hne : Ideal.span ({X - C x₀} : Set F[X]) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h2 := Polynomial.isUnit_iff_degree_eq_zero.mp hu
    rw [Polynomial.degree_X_sub_C] at h2
    exact one_ne_zero h2
  have hpeq : pc = Ideal.span {X - C x₀} := hpmax.eq_of_le hne hle
  refine ⟨x₀, ?_⟩
  have hmem : (X - C x₀) ∈ pc := by rw [hpeq]; exact Ideal.subset_span rfl
  have hmem' := hpdef ▸ hmem
  rw [Ideal.mem_comap] at hmem'
  have hXalg : CoordinateRing.XClass W x₀ = algebraMap F[X] W.CoordinateRing (X - C x₀) := by
    rw [CoordinateRing.XClass]
    rfl
  rwa [hXalg]

omit [DecidableEq F] in
/-- **Every abscissa carries a point**: over an algebraically closed
field the quadratic `Y² + (a₁x₀ + a₃)Y − (x₀³ + a₂x₀² + a₄x₀ + a₆)` has
a root, i.e. the fiber of `W` over `x₀` is nonempty. -/
lemma exists_equation (W : WeierstrassCurve.Affine F) (x₀ : F) :
    ∃ y : F, W.Equation x₀ y := by
  have hdeg : (C (1 : F) * X ^ 2 + C (W.a₁ * x₀ + W.a₃) * X +
      C (-(x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))).degree = 2 :=
    Polynomial.degree_quadratic one_ne_zero
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root
    (C (1 : F) * X ^ 2 + C (W.a₁ * x₀ + W.a₃) * X +
      C (-(x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))) (by rw [hdeg]; norm_num)
  refine ⟨y₀, ?_⟩
  rw [Polynomial.IsRoot.def] at hy₀
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X] at hy₀
  rw [WeierstrassCurve.Affine.equation_iff]
  linear_combination hy₀

omit [DecidableEq F] in
/-- **Maximal ideals are point ideals** (the Nullstellensatz for the
affine curve, in the form the divisor bookkeeping needs).  A maximal
`m` contains some vertical `X − x₀` (`exists_xClass_mem`); the fiber
over `x₀` carries a point `(x₀, y₁)` (`exists_equation`), and mathlib's
`CoordinateRing.XYIdeal_neg_mul` factors that vertical as the product
`I_{(x₀, −y₁)}·I_{(x₀, y₁)}` of the two point ideals in the fiber.  As
`m` is prime it contains one of the two factors, and both factors are
maximal (`xyIdeal_isMaximal`), so `m` IS that point ideal. -/
lemma exists_point_pointIdeal_eq (hΔ : W.Δ ≠ 0) {m : Ideal W.CoordinateRing}
    (hm : m.IsMaximal) : ∃ R : W.Point, R ≠ 0 ∧ pointIdeal W R = m := by
  obtain ⟨x₀, hx₀⟩ := exists_xClass_mem hm
  obtain ⟨y₁, hy₁⟩ := exists_equation W x₀
  have hns : W.Nonsingular x₀ y₁ :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hy₁
  have hprod : CoordinateRing.XYIdeal W x₀ (C (W.negY x₀ y₁)) *
      CoordinateRing.XYIdeal W x₀ (C y₁) = CoordinateRing.XIdeal W x₀ :=
    CoordinateRing.XYIdeal_neg_mul hns
  have hXle : CoordinateRing.XIdeal W x₀ ≤ m := by
    rw [CoordinateRing.XIdeal, Ideal.span_le, Set.singleton_subset_iff]
    exact hx₀
  rw [← hprod] at hXle
  rcases hm.isPrime.mul_le.mp hXle with h | h
  · have hns' : W.Nonsingular x₀ (W.negY x₀ y₁) :=
      (WeierstrassCurve.Affine.nonsingular_neg (W' := W) x₀ y₁).mpr hns
    refine ⟨.some x₀ (W.negY x₀ y₁) hns', WeierstrassCurve.Affine.Point.some_ne_zero hns', ?_⟩
    exact (xyIdeal_isMaximal hns'.left).eq_of_le hm.ne_top h
  · refine ⟨.some x₀ y₁ hns, WeierstrassCurve.Affine.Point.some_ne_zero hns, ?_⟩
    exact (xyIdeal_isMaximal hy₁).eq_of_le hm.ne_top h

omit [DecidableEq F] in
/-- **Every nonzero ideal of `F[W]` is a product of point ideals at
affine points** — the factorization the affine divisor of a function is
read off from, obtained WITHOUT a Dedekind-domain instance for `F[W]`
(which the pin does not have): noetherian induction on the ideal, using
only that point ideals are *invertible* as fractional ideals (mathlib's
`CoordinateRing.XYIdeal'`, packaged here as `pointIdeal'`).

Induction step: a proper nonzero `I` sits inside a maximal `m`, which
is a point ideal `I_R` (`exists_point_pointIdeal_eq`).  Since `I ≤ m`
and `m` is invertible, `↑I·↑I_R⁻¹ ≤ 1` is an integral ideal `J` with
`I = J·m`, so `I ≤ J`; and `I = J` would give `I = m·I`, whence
Nakayama (`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`,
applicable as `F[W]` is noetherian) produces `r` with `r − 1 ∈ m`
annihilating the nonzero `I`, forcing `r = 0` and `m = ⊤` — absurd.  So
`I < J` and the induction hypothesis factors `J`. -/
lemma exists_multiset_ideal_eq_prod_pointIdeal (hΔ : W.Δ ≠ 0)
    (I : Ideal W.CoordinateRing) (hI : I ≠ ⊥) :
    ∃ D : Multiset W.Point, (0 : W.Point) ∉ D ∧ I = (D.map (pointIdeal W)).prod := by
  haveI hnoeth : IsNoetherianRing W.CoordinateRing := isNoetherianRing_coordinateRing W
  induction I using IsNoetherian.induction with
  | _ I ih =>
    by_cases hItop : I = ⊤
    · exact ⟨0, by simp, by simp [hItop]⟩
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hItop
    haveI := hm
    obtain ⟨R, hR0, hRm⟩ := exists_point_pointIdeal_eq hΔ hm
    have hcoe : ((m : Ideal W.CoordinateRing) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
        ((pointIdeal' W R : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
      rw [coe_pointIdeal', hRm]
    have hIle : ((I : Ideal W.CoordinateRing) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ≤
        ((pointIdeal' W R : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
      rw [← hcoe]
      exact FractionalIdeal.coeIdeal_le_coeIdeal _ |>.mpr hIm
    have hle1 : ((I : Ideal W.CoordinateRing) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
        ((pointIdeal' W R)⁻¹ : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) ≤ 1 := by
      calc ((I : Ideal W.CoordinateRing) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
            ((pointIdeal' W R)⁻¹ : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ)
          ≤ ((pointIdeal' W R : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
            ((pointIdeal' W R)⁻¹ : (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ) :=
            mul_le_mul_left hIle _
        _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle1
    have hIJ : I = J * m := by
      have hcast : ((I : Ideal W.CoordinateRing) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
          ((J * m : Ideal W.CoordinateRing) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
        rw [FractionalIdeal.coeIdeal_mul, hJ, hcoe, mul_assoc, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, mul_one]
      exact FractionalIdeal.coeIdeal_injective hcast
    have hJ0 : J ≠ ⊥ := by
      rintro rfl
      rw [Ideal.bot_mul] at hIJ
      exact hI hIJ
    have hIltJ : I < J := by
      refine lt_of_le_of_ne (by rw [hIJ]; exact Ideal.mul_le_right) ?_
      rintro rfl
      rw [mul_comm] at hIJ
      have hfg : (I : Submodule W.CoordinateRing W.CoordinateRing).FG := IsNoetherian.noetherian I
      have hsm : (I : Submodule W.CoordinateRing W.CoordinateRing) ≤
          m • (I : Submodule W.CoordinateRing W.CoordinateRing) := by
        rw [Ideal.smul_eq_mul]
        exact hIJ.le
      obtain ⟨r, hr1, hr2⟩ :=
        Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m _ hfg hsm
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      have hrz : r * z = 0 := by simpa [smul_eq_mul] using hr2 z hz
      rcases mul_eq_zero.mp hrz with h | h
      · rw [h, zero_sub] at hr1
        exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hr1 (isUnit_one.neg))
      · exact hz0 h
    obtain ⟨D, hD0, hD⟩ := ih J hIltJ hJ0
    refine ⟨R ::ₘ D, ?_, ?_⟩
    · simp only [Multiset.mem_cons, not_or]
      exact ⟨fun h => hR0 h.symm, hD0⟩
    · rw [Multiset.map_cons, Multiset.prod_cons, hIJ, hD, hRm, mul_comm]

end DedekindFactorization

omit [DecidableEq F] in
/-- **L4-7 substrate brick (PROVEN): the affine coordinate ring of a
nonsingular Weierstrass curve over an algebraically closed field is a
Dedekind domain.**

The point of the exercise is that the instance comes for free from the
point-ideal factorization proven above, and needs NO integral-closedness
and NO smoothness argument: by `isDedekindDomain_iff_isDedekindDomainInv`
it suffices that every nonzero fractional ideal be invertible, and
writing `I = a⁻¹·J` (`FractionalIdeal.exists_eq_spanSingleton_mul`)
reduces that to the integral `J`, which
`exists_multiset_ideal_eq_prod_pointIdeal` factors into point ideals —
each invertible (`pointIdeal'`), so `↑J` is a unit
(`isUnit_prod_coe_pointIdeal'`), and so is the principal factor.  Thus
noetherianity plus invertibility of the point ideals, the two inputs of
the factorization brick, already carry the whole Dedekind property. -/
lemma isDedekindDomain_coordinateRing (hΔ : W.Δ ≠ 0) :
    IsDedekindDomain W.CoordinateRing := by
  classical
  -- every nonzero fractional ideal of `F[W]` is invertible: reduce to an
  -- integral ideal and factor it into (invertible) point ideals
  have hcancel : ∀ I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField,
      I ≠ 0 → I * I⁻¹ = 1 := by
    intro I hI
    obtain ⟨a, J, ha, haJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
    have hane : (algebraMap W.CoordinateRing W.FunctionField) a ≠ 0 := fun hc =>
      ha ((injective_iff_map_eq_zero _).mp
        (IsFractionRing.injective W.CoordinateRing W.FunctionField) a hc)
    have hJ : J ≠ ⊥ := by
      rintro rfl
      rw [FractionalIdeal.coeIdeal_bot, mul_zero] at haJ
      exact hI haJ
    obtain ⟨D, -, hD⟩ := exists_multiset_ideal_eq_prod_pointIdeal hΔ J hJ
    have huJ : IsUnit ((J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) := by
      rw [hD, ← prod_coe_pointIdeal' D]
      exact isUnit_prod_coe_pointIdeal' D
    have hmul : FractionalIdeal.spanSingleton W.CoordinateRing⁰
          ((algebraMap W.CoordinateRing W.FunctionField a)⁻¹) *
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          ((algebraMap W.CoordinateRing W.FunctionField) a) = 1 := by
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hane,
        FractionalIdeal.spanSingleton_one]
    have husp : IsUnit (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        ((algebraMap W.CoordinateRing W.FunctionField a)⁻¹)) :=
      ⟨⟨_, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
    rw [FractionalIdeal.mul_inv_cancel_iff_isUnit W.FunctionField, haJ]
    exact husp.mul huJ
  exact isDedekindDomain_iff_isDedekindDomainInv.mpr
    ((isDedekindDomainInv_iff (K := W.FunctionField)).mpr fun I hI =>
      hcancel I (by rwa [← FractionalIdeal.bot_eq_zero]))

omit [DecidableEq F] [IsAlgClosed F] in
/-- Point ideals of affine points are nonzero: they contain the nonzero
vertical class `X − x`. -/
lemma pointIdeal_ne_bot {x y : F} (h : W.Nonsingular x y) :
    pointIdeal W (.some x y h) ≠ ⊥ := by
  intro hc
  have hmem : CoordinateRing.XClass W x ∈ pointIdeal W (.some x y h) := by
    rw [pointIdeal_some, CoordinateRing.XYIdeal]
    exact Ideal.subset_span (Set.mem_insert _ _)
  rw [hc, Ideal.mem_bot] at hmem
  exact CoordinateRing.XClass_ne_zero (W' := W) x hmem

omit [DecidableEq F] in
/-- **Point ideals of affine points are prime elements of the ideal
monoid** of the Dedekind domain `F[W]` (`isDedekindDomain_coordinateRing`):
they are maximal (`xyIdeal_isMaximal`) and nonzero. -/
lemma prime_pointIdeal (hΔ : W.Δ ≠ 0) {x y : F} (h : W.Nonsingular x y) :
    Prime (pointIdeal W (.some x y h)) := by
  haveI := isDedekindDomain_coordinateRing hΔ
  exact Ideal.prime_of_isPrime (pointIdeal_ne_bot h)
    (by rw [pointIdeal_some]; exact (xyIdeal_isMaximal h.left).isPrime)

omit [DecidableEq F] in
/-- **The prime-power squeeze** (the mechanism that turns the *product*
identity `⟨n · ñ⟩ = RHS · RHS'` into a *factorwise* statement): if `z · w`
spans an ideal divisible by `I_Z^k` and the partner `w` does not vanish at
`Z`, then `z` alone lies in `I_Z^k`.  This is `Prime.pow_dvd_of_dvd_mul_right`
in the ideal monoid, where divisibility is containment
(`Ideal.dvd_iff_le`). -/
lemma mem_pointIdeal_pow_of_dvd_of_notMem (hΔ : W.Δ ≠ 0) {x y : F}
    (h : W.Nonsingular x y) {z w : W.CoordinateRing} {k : ℕ}
    (hdvd : pointIdeal W (.some x y h) ^ k ∣ Ideal.span {z * w})
    (hw : w ∉ pointIdeal W (.some x y h)) :
    z ∈ pointIdeal W (.some x y h) ^ k := by
  haveI := isDedekindDomain_coordinateRing hΔ
  have hz : pointIdeal W (.some x y h) ^ k ∣ Ideal.span {z} := by
    refine (prime_pointIdeal hΔ h).pow_dvd_of_dvd_mul_right
      (b := Ideal.span {w}) k ?_ ?_
    · rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
      exact hw
    · rwa [Ideal.span_singleton_mul_span_singleton]
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff] at hz
  exact hz

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Multiplicity-wise assembly**: an element lying in `I_Z` to the
multiplicity of `Z` in a multiset `E` of points, *for every* `Z`, lies in
the product of the point ideals of `E`.  This is the coincidence-proof
replacement for the naive comaximal assembly: distinct points have coprime
point ideals (`isCoprime_pointIdeal`), so peeling off all copies of one
point at a time turns the product over the *distinct* points into an
intersection, while the repeated point contributes a genuine prime
power. -/
lemma mem_prod_map_pointIdeal [DecidableEq W.Point] :
    ∀ (E : Multiset W.Point) {z : W.CoordinateRing},
      (∀ Z : W.Point, z ∈ pointIdeal W Z ^ E.count Z) →
      z ∈ (E.map (pointIdeal W)).prod := by
  intro E
  induction E using Multiset.strongInductionOn with
  | _ E ih =>
    intro z h
    rcases Multiset.empty_or_exists_mem E with rfl | ⟨Z, hZ⟩
    · simp
    · have hsplit : Multiset.replicate (E.count Z) Z +
          E.filter (fun a => ¬ a = Z) = E := by
        conv_rhs => rw [← Multiset.filter_add_not (fun a => a = Z) E]
        rw [Multiset.filter_eq' E Z]
      have hE'lt : E.filter (fun a => ¬ a = Z) < E := by
        refine lt_of_le_of_ne (Multiset.filter_le _ _) ?_
        intro hcon
        have hmem : Z ∈ E.filter (fun a => ¬ a = Z) := by rw [hcon]; exact hZ
        exact (Multiset.of_mem_filter hmem) rfl
      have hcount' : ∀ Y : W.Point,
          z ∈ pointIdeal W Y ^ (E.filter (fun a => ¬ a = Z)).count Y := by
        intro Y
        by_cases hY : Y = Z
        · subst hY
          have hz0 : (E.filter (fun a => ¬ a = Y)).count Y = 0 := by
            rw [Multiset.count_eq_zero]
            exact fun hc => (Multiset.of_mem_filter hc) rfl
          rw [hz0, pow_zero, Ideal.one_eq_top]
          exact Submodule.mem_top
        · rw [Multiset.count_filter_of_pos (p := fun a => ¬ a = Z) hY]
          exact h Y
      have hrec := ih _ hE'lt hcount'
      have hcop : IsCoprime (pointIdeal W Z ^ E.count Z)
          (((E.filter (fun a => ¬ a = Z)).map (pointIdeal W)).prod) := by
        refine IsCoprime.pow_left ?_
        refine Multiset.prod_induction _ _ (fun a b ha hb => ha.mul_right hb)
          isCoprime_one_right ?_
        intro J hJ
        obtain ⟨Y, hYmem, rfl⟩ := Multiset.mem_map.mp hJ
        exact isCoprime_pointIdeal (fun hc => (Multiset.of_mem_filter hYmem) hc.symm)
      have hprod : (E.map (pointIdeal W)).prod =
          pointIdeal W Z ^ E.count Z *
            ((E.filter (fun a => ¬ a = Z)).map (pointIdeal W)).prod := by
        conv_lhs => rw [← hsplit]
        rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
          Multiset.prod_replicate]
      rw [hprod, Ideal.mul_eq_inf_of_isCoprime hcop]
      exact ⟨h Z, hrec⟩

omit [DecidableEq F] [IsAlgClosed F] in
/-- A coordinate-ring element of the point ideal of an affine point
vanishes there: the point ideal is contained in the kernel of `coordEval`.
(The converse is `mem_pointIdeal_of_coordEval_eq_zero`.) -/
lemma coordEval_eq_zero_of_mem {x y : F} (h : W.Nonsingular x y)
    {z : W.CoordinateRing} (hz : z ∈ pointIdeal W (.some x y h)) :
    coordEval W h.left z = 0 := by
  have hX : CoordinateRing.XClass W x ∈ RingHom.ker (coordEval W h.left) := by
    rw [RingHom.mem_ker, XClass_eq, map_sub, coordEval_coordX, coordEval_coordC,
      sub_self]
  have hY : CoordinateRing.YClass W (Polynomial.C y) ∈
      RingHom.ker (coordEval W h.left) := by
    rw [RingHom.mem_ker, YClass_C_eq, map_sub, coordEval_coordY, coordEval_coordC,
      sub_self]
  have hle : pointIdeal W (.some x y h) ≤ RingHom.ker (coordEval W h.left) := by
    rw [pointIdeal_some, CoordinateRing.XYIdeal, Ideal.span_le, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    exact ⟨hX, hY⟩
  exact hle hz

omit [DecidableEq F] [IsAlgClosed F] in
/-- The conjugate line numerator, like the line numerator
(`lineNumerator_congr`), depends only on the line and not on the base
point used to write it down. -/
lemma lineNumeratorNeg_congr {q₁ q₂ x y x' y' ℓ : F} (hl : ℓ * (x - x') = y - y') :
    lineNumeratorNeg W q₁ q₂ x y ℓ = lineNumeratorNeg W q₁ q₂ x' y' ℓ := by
  have h1 : coordC W ℓ * (coordC W x - coordC W x') = coordC W y - coordC W y' := by
    rw [← coordC_sub, ← coordC_mul, ← coordC_sub, hl]
  simp only [lineNumeratorNeg]
  linear_combination (coordX W - coordC W q₁) ^ 3 * h1

omit [IsAlgClosed F] in
/-- **The value of the conjugate line numerator at `P ⊖ Q`.**  While
`lineNumerator` *vanishes* at `P ⊖ Q` (`lineNumerator_mem_pointIdeal_sub`),
its hyperelliptic conjugate takes there the value
`−(2y + a₁x + a₃)·(α − q₁)³`, `(α, β) = P ⊖ Q`.  Reason: `ñ/T³` is the line
value read at `⊖Q ⊖ taut`, so at `taut = P ⊖ Q` it is `L(⊖P)`, and
`L(⊖P) = negY x y − y = −(2y + a₁x + a₃)` because `L(P) = 0`.

Formally it is the same computation as `lineNumerator_mem_pointIdeal_sub`
— the group law `Q ⊕ (α, β) = P` supplies `addX q₁ α λ = x` and
`addY q₁ α q₂ λ = y`, and the cleared slope relation eliminates `β` — with
the cofactors `(q₁ − α)³` and `(a₁ + ℓ)(q₁ − α)³` instead of
`−(q₁ − α)³`, `ℓ(q₁ − α)³`. -/
lemma coordEval_lineNumeratorNeg_sub {q₁ q₂ x y α β : F} (hq : W.Nonsingular q₁ q₂)
    (h : W.Nonsingular x y) (hαβ : W.Nonsingular α β)
    (hd : (Point.some x y h : W.Point) - Point.some q₁ q₂ hq = Point.some α β hαβ)
    (ℓ : F) :
    coordEval W hαβ.left (lineNumeratorNeg W q₁ q₂ x y ℓ) =
      -(2 * y + W.a₁ * x + W.a₃) * (α - q₁) ^ 3 := by
  have hsum : (Point.some q₁ q₂ hq : W.Point) + Point.some α β hαβ =
      Point.some x y h := by rw [← hd]; abel
  by_cases hQA : q₁ = α ∧ q₂ = W.negY α β
  · exact absurd (by rw [← hsum, Point.add_of_Y_eq hQA.1 hQA.2] :
      (Point.some x y h : W.Point) = 0) (Point.some_ne_zero h)
  · rw [Point.add_some hQA] at hsum
    rw [Point.some.injEq] at hsum
    obtain ⟨hX, hY⟩ := hsum
    simp only [lineNumeratorNeg, map_sub, map_add, map_mul, map_pow,
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
      linear_combination ((q₁ - α) ^ 3) * hY +
        ((W.a₁ + ℓ) * (q₁ - α) ^ 3) * hX

omit [IsAlgClosed F] in
/-- **Non-vanishing of the conjugate line numerator at `P ⊖ Q`**, read off
`coordEval_lineNumeratorNeg_sub`: it needs exactly `2P ≠ O` and
`P ⊖ Q ∉ {Q, ⊖Q}`.  This is the input the prime-power squeeze consumes at
every coincident point *other than* `Q`. -/
lemma lineNumeratorNeg_notMem_pointIdeal_sub {q₁ q₂ x y α β : F}
    (hq : W.Nonsingular q₁ q₂) (h : W.Nonsingular x y) (hαβ : W.Nonsingular α β)
    (hd : (Point.some x y h : W.Point) - Point.some q₁ q₂ hq = Point.some α β hαβ)
    (ℓ : F) (h2P : y ≠ W.negY x y) (hne : α ≠ q₁) :
    lineNumeratorNeg W q₁ q₂ x y ℓ ∉ pointIdeal W (.some α β hαβ) := by
  intro hmem
  have hval := coordEval_eq_zero_of_mem hαβ hmem
  rw [coordEval_lineNumeratorNeg_sub hq h hαβ hd ℓ] at hval
  have hd1 : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro hc
    refine h2P ?_
    rw [show W.negY x y = -y - W.a₁ * x - W.a₃ from rfl]
    linear_combination hc
  rcases mul_eq_zero.mp hval with hc | hc
  · exact hd1 (by linear_combination -hc)
  · exact hne (by
      have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hc
      linear_combination this)

/-- **The product identity `⟨n · ñ⟩ = RHS · RHS'`** (PROVEN), hoisted out
of `span_lineNumerator`'s proof so that it is available to the coincidence
leaf below it.  It is `lineNumerator_mul_lineNumeratorNeg` (the cleared
conjugate product) combined with the three exact vertical spans
`span_vertNumerator`. -/
lemma span_lineNumerator_mul_lineNumeratorNeg (hΔ : W.Δ ≠ 0)
    {q₁ q₂ x₁ y₁ x₂ y₂ : F}
    (hq : W.Nonsingular q₁ q₂) (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    Ideal.span {lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) *
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
  have h₃ : W.Nonsingular (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
      (W.negY (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
        (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂))) :=
    (nonsingular_neg ..).mpr (nonsingular_add h₁ h₂ hxy)
  have hS : -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) =
      Point.some _ _ h₃ := by rw [Point.add_some hxy, Point.neg_some]
  have hv₃ : Ideal.span {vertNumerator W q₁ q₂
        (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))} =
      pointIdeal W (.some q₁ q₂ hq) ^ 2 *
        (pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) - .some q₁ q₂ hq) *
          pointIdeal W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ - .some q₁ q₂ hq)) := by
    have hv := span_vertNumerator hΔ hq h₃
    rwa [← hS, neg_neg] at hv
  rw [lineNumerator_mul_lineNumeratorNeg hq.left h₁.left h₂.left hxy,
    Ideal.span_singleton_neg, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton,
    span_vertNumerator hΔ hq h₁, span_vertNumerator hΔ hq h₂, hv₃]
  ring

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The cleared branch identity at `Q`** (the whole arithmetic input of the
order-4 local normal form).  With `T = coordX − q₁`, `U = coordY − q₂` and
`A₀ = 2q₂ + a₁q₁ + a₃`, the Weierstrass relation shifted to `Q` reads
`U·(A₀ + U + a₁T) = T·(EX + (3q₁ + a₂)T + T²)`, `EX = 3q₁² + 2a₂q₁ + a₄ − a₁q₂`.
Subtracting the truncated branch `B = c₁T + c₂T² + c₃T³` — whose coefficients
are pinned by `hc₁`, `hc₂`, `hc₃`, i.e. by `W(q₁ + t, q₂ + B(t)) ≡ 0 mod t⁴` —
turns that into
`(U − B)·(A₀ + U + a₁T + B) = T⁴·D`,
`D = −(a₁c₃ + 2c₁c₃ + c₂²) − 2c₂c₃·T − c₃²·T²`,
the point being that the left cofactor is a UNIT at `Q` (it evaluates to `A₀`).
One `linear_combination` against `coord_equation_coordC`, `W.Equation q₁ q₂`
and the three coefficient equations, with cofactors `1, −1, −T, −T², −T³`. -/
lemma sub_branch_mul_eq {q₁ q₂ c₁ c₂ c₃ : F} (hq : W.Equation q₁ q₂)
    (hc₁ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₁ =
      3 * q₁ ^ 2 + 2 * W.a₂ * q₁ + W.a₄ - W.a₁ * q₂)
    (hc₂ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₂ =
      3 * q₁ + W.a₂ - c₁ ^ 2 - W.a₁ * c₁)
    (hc₃ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₃ = 1 - 2 * c₁ * c₂ - W.a₁ * c₂) :
    (coordY W - coordC W q₂ -
        (coordC W c₁ * (coordX W - coordC W q₁) +
          coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
          coordC W c₃ * (coordX W - coordC W q₁) ^ 3)) *
      (coordC W (2 * q₂ + W.a₁ * q₁ + W.a₃) + (coordY W - coordC W q₂) +
        coordC W W.a₁ * (coordX W - coordC W q₁) +
        (coordC W c₁ * (coordX W - coordC W q₁) +
          coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
          coordC W c₃ * (coordX W - coordC W q₁) ^ 3)) =
    (coordX W - coordC W q₁) ^ 4 *
      (coordC W (-(W.a₁ * c₃) - 2 * c₁ * c₃ - c₂ ^ 2) +
        coordC W (-(2 * c₂ * c₃)) * (coordX W - coordC W q₁) +
        coordC W (-(c₃ ^ 2)) * (coordX W - coordC W q₁) ^ 2) := by
  have hcr := coord_equation_coordC W
  simp only [coordC_eq_algebraMap] at hcr
  rw [WeierstrassCurve.Affine.equation_iff] at hq
  have hqW := congrArg (algebraMap F W.CoordinateRing) hq
  have hc₁W := congrArg (algebraMap F W.CoordinateRing) hc₁
  have hc₂W := congrArg (algebraMap F W.CoordinateRing) hc₂
  have hc₃W := congrArg (algebraMap F W.CoordinateRing) hc₃
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
    at hqW hc₁W hc₂W hc₃W
  simp only [coordC_eq_algebraMap, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat]
  linear_combination hcr - hqW -
    (coordX W - algebraMap F W.CoordinateRing q₁) * hc₁W -
    (coordX W - algebraMap F W.CoordinateRing q₁) ^ 2 * hc₂W -
    (coordX W - algebraMap F W.CoordinateRing q₁) ^ 3 * hc₃W

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The order-4 normal form of `lineNumerator`** — a pure polynomial identity
(no curve relation is used).  Expanding `n = lineNumerator q₁ q₂ x₁ y₁ ℓ` in
powers of `U = coordY − q₂` gives `n = n₀ + n₁U + n₂U² − U³` with
`n₁ = (a₂ + 3q₁ − a₁² − ℓa₁)T² + T³`, `n₂ = −(2a₁ + ℓ)T`, so the divided
difference `n(T, U) − n(T, B)` factors through `U − B`; and substituting the
branch, `n(T, B) = L(2Q)·T³ + T⁴·K` with `L(2Q)` the value at `2Q` of the line
through `(x₁, y₁)` of slope `ℓ` — the coefficient identity verified by `ring`
after unfolding `addX`/`addY`.  Together: `n ≡ L(2Q)·T³ mod ⟨U − B, T⁴⟩`. -/
lemma lineNumerator_sub_lineValue_eq {q₁ q₂ c₁ c₂ c₃ x₁ y₁ ℓ : F} :
    lineNumerator W q₁ q₂ x₁ y₁ ℓ -
        coordC W (W.addY q₁ q₁ q₂ c₁ - (ℓ * (W.addX q₁ q₁ c₁ - x₁) + y₁)) *
          (coordX W - coordC W q₁) ^ 3 =
      (coordY W - coordC W q₂ -
          (coordC W c₁ * (coordX W - coordC W q₁) +
            coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
            coordC W c₃ * (coordX W - coordC W q₁) ^ 3)) *
        (coordC W (W.a₂ + 3 * q₁ - W.a₁ ^ 2 - ℓ * W.a₁) *
              (coordX W - coordC W q₁) ^ 2 +
            (coordX W - coordC W q₁) ^ 3 -
          coordC W (2 * W.a₁ + ℓ) * (coordX W - coordC W q₁) *
            (coordY W - coordC W q₂ +
              (coordC W c₁ * (coordX W - coordC W q₁) +
                coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
                coordC W c₃ * (coordX W - coordC W q₁) ^ 3)) -
          ((coordY W - coordC W q₂) ^ 2 +
            (coordY W - coordC W q₂) *
              (coordC W c₁ * (coordX W - coordC W q₁) +
                coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
                coordC W c₃ * (coordX W - coordC W q₁) ^ 3) +
            (coordC W c₁ * (coordX W - coordC W q₁) +
                coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
                coordC W c₃ * (coordX W - coordC W q₁) ^ 3) ^ 2)) +
      (coordX W - coordC W q₁) ^ 4 *
        ((coordC W c₂ + coordC W c₃ * (coordX W - coordC W q₁)) *
            (-((coordC W c₁ + coordC W c₂ * (coordX W - coordC W q₁) +
                    coordC W c₃ * (coordX W - coordC W q₁) ^ 2) ^ 2 +
                (coordC W c₁ + coordC W c₂ * (coordX W - coordC W q₁) +
                    coordC W c₃ * (coordX W - coordC W q₁) ^ 2) * coordC W c₁ +
                coordC W c₁ ^ 2) -
              coordC W (2 * W.a₁ + ℓ) *
                ((coordC W c₁ + coordC W c₂ * (coordX W - coordC W q₁) +
                    coordC W c₃ * (coordX W - coordC W q₁) ^ 2) + coordC W c₁) +
              coordC W (W.a₂ + 3 * q₁ - W.a₁ ^ 2 - ℓ * W.a₁)) +
          (coordC W c₁ + coordC W c₂ * (coordX W - coordC W q₁) +
            coordC W c₃ * (coordX W - coordC W q₁) ^ 2) +
          coordC W (W.a₁ + ℓ)) := by
  simp only [lineNumerator, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.addX, coordC_eq_algebraMap, map_add, map_sub,
    map_mul, map_pow, map_neg, map_ofNat]
  ring

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The order-4 normal form of `lineNumeratorNeg`**, the mirror of
`lineNumerator_sub_lineValue_eq`: `ñ ≡ L(⊖2Q)·T³ mod ⟨U − B, T⁴⟩`, where
`L(⊖2Q)` is the line value at `⊖2Q` (whose `y`-coordinate is `negAddY`).
Same pure-`ring` route, with `ñ₁ = −(a₂ + 3q₁ + ℓa₁)T² − T³`,
`ñ₂ = (a₁ − ℓ)T`, `ñ₃ = 1`. -/
lemma lineNumeratorNeg_sub_lineValue_eq {q₁ q₂ c₁ c₂ c₃ x₁ y₁ ℓ : F} :
    lineNumeratorNeg W q₁ q₂ x₁ y₁ ℓ -
        coordC W (W.negAddY q₁ q₁ q₂ c₁ - (ℓ * (W.addX q₁ q₁ c₁ - x₁) + y₁)) *
          (coordX W - coordC W q₁) ^ 3 =
      (coordY W - coordC W q₂ -
          (coordC W c₁ * (coordX W - coordC W q₁) +
            coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
            coordC W c₃ * (coordX W - coordC W q₁) ^ 3)) *
        (-(coordC W (W.a₂ + 3 * q₁ + ℓ * W.a₁) * (coordX W - coordC W q₁) ^ 2) -
            (coordX W - coordC W q₁) ^ 3 +
          coordC W (W.a₁ - ℓ) * (coordX W - coordC W q₁) *
            (coordY W - coordC W q₂ +
              (coordC W c₁ * (coordX W - coordC W q₁) +
                coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
                coordC W c₃ * (coordX W - coordC W q₁) ^ 3)) +
          ((coordY W - coordC W q₂) ^ 2 +
            (coordY W - coordC W q₂) *
              (coordC W c₁ * (coordX W - coordC W q₁) +
                coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
                coordC W c₃ * (coordX W - coordC W q₁) ^ 3) +
            (coordC W c₁ * (coordX W - coordC W q₁) +
                coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
                coordC W c₃ * (coordX W - coordC W q₁) ^ 3) ^ 2)) +
      (coordX W - coordC W q₁) ^ 4 *
        ((coordC W c₂ + coordC W c₃ * (coordX W - coordC W q₁)) *
            (((coordC W c₁ + coordC W c₂ * (coordX W - coordC W q₁) +
                    coordC W c₃ * (coordX W - coordC W q₁) ^ 2) ^ 2 +
                (coordC W c₁ + coordC W c₂ * (coordX W - coordC W q₁) +
                    coordC W c₃ * (coordX W - coordC W q₁) ^ 2) * coordC W c₁ +
                coordC W c₁ ^ 2) +
              coordC W (W.a₁ - ℓ) *
                ((coordC W c₁ + coordC W c₂ * (coordX W - coordC W q₁) +
                    coordC W c₃ * (coordX W - coordC W q₁) ^ 2) + coordC W c₁) -
              coordC W (W.a₂ + 3 * q₁ + ℓ * W.a₁)) -
          (coordC W c₁ + coordC W c₂ * (coordX W - coordC W q₁) +
            coordC W c₃ * (coordX W - coordC W q₁) ^ 2) +
          coordC W ℓ) := by
  simp only [lineNumeratorNeg, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX, coordC_eq_algebraMap, map_add, map_sub,
    map_mul, map_pow, map_ofNat]
  ring


/-- **The generalized prime-power squeeze**: `p^(k+j) ∣ a·b` and
`p^(j+1) ∤ b` force `p^k ∣ a`.  The `j = 0` case is
`Prime.pow_dvd_of_dvd_mul_right`; the induction step peels one `p` off `b`
and cancels it (the ideal monoid of a Dedekind domain is cancellative).
This is what converts the exact product identity `⟨n·ñ⟩ = RHS·RHS'` into
a bound on `v_Q(n)` from an UPPER bound `v_Q(ñ) ≤ 3` on the partner. -/
lemma pow_dvd_of_pow_dvd_mul {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]
    {p : M} (hp : Prime p) :
    ∀ (j k : ℕ) (a b : M), p ^ (k + j) ∣ a * b → ¬ p ^ (j + 1) ∣ b → p ^ k ∣ a := by
  intro j
  induction j with
  | zero =>
    intro k a b h hb
    exact hp.pow_dvd_of_dvd_mul_right k (by simpa using hb) (by simpa using h)
  | succ j ih =>
    intro k a b h hb
    by_cases hpb : p ∣ b
    · obtain ⟨c, rfl⟩ := hpb
      refine ih k a c ?_ ?_
      · have hmul : a * (p * c) = a * c * p := by
          rw [← mul_assoc, mul_right_comm]
        have h2 : p ^ (k + j) * p ∣ a * c * p := by
          rw [← pow_succ, ← hmul]; exact h
        exact (mul_dvd_mul_iff_right hp.ne_zero).mp h2
      · intro hc
        exact hb (by rw [pow_succ']; exact mul_dvd_mul_left p hc)
    · refine hp.pow_dvd_of_dvd_mul_right k hpb (dvd_trans ?_ h)
      exact pow_dvd_pow p (Nat.le_add_right _ _)

omit [DecidableEq F] in
/-- **Point ideals are determined by their points**: if `I_Q ∣ I_V` then
`V = Q`.  Divisibility is containment (`Ideal.dvd_iff_le`), and distinct
points have coprime point ideals (`isCoprime_pointIdeal`), so `I_V ≤ I_Q`
with `V ≠ Q` would make `I_Q = ⊤`, contradicting primality.  Covers `V = O`
too, since `I_O = ⊤`. -/
lemma eq_of_pointIdeal_dvd (hΔ : W.Δ ≠ 0) {q₁ q₂ : F} (hq : W.Nonsingular q₁ q₂)
    {V : W.Point} (hdvd : pointIdeal W (.some q₁ q₂ hq) ∣ pointIdeal W V) :
    V = .some q₁ q₂ hq := by
  haveI := isDedekindDomain_coordinateRing hΔ
  by_contra hne
  have hcop := isCoprime_pointIdeal (W := W) hne
  rw [Ideal.isCoprime_iff_sup_eq] at hcop
  have hle : pointIdeal W V ≤ pointIdeal W (.some q₁ q₂ hq) := Ideal.le_of_dvd hdvd
  have htop : pointIdeal W (.some q₁ q₂ hq) = ⊤ := by
    rw [← hcop, sup_eq_right.mpr hle]
  exact (prime_pointIdeal hΔ hq).not_unit (Ideal.isUnit_iff.mpr htop)

omit [DecidableEq F] in
/-- **`T³` has `Q`-multiplicity exactly 3** (when `2Q ≠ O`): no nonzero
constant multiple of `T³ = (coordX − q₁)³` lies in `I_Q⁴`.  Indeed
`⟨T⟩ = I_{⊖Q}·I_Q` (mathlib's `XYIdeal_neg_mul`), so `I_Q⁴ ∣ I_{⊖Q}³I_Q³`
would give `I_Q ∣ I_{⊖Q}³` after cancelling `I_Q³`, hence `I_Q = I_{⊖Q}`,
i.e. `Q = ⊖Q` — excluded by `2Q ≠ O`.  This is the lower half of the
squeeze: it turns `ñ ≡ L(⊖2Q)T³` with `L(⊖2Q) ≠ 0` into `ñ ∉ I_Q⁴`. -/
lemma smul_pow_three_notMem_pointIdeal_pow_four (hΔ : W.Δ ≠ 0) {q₁ q₂ : F}
    (hq : W.Nonsingular q₁ q₂) (h2Q : q₂ ≠ W.negY q₁ q₂) {c : F} (hc : c ≠ 0) :
    coordC W c * (coordX W - coordC W q₁) ^ 3 ∉
      pointIdeal W (.some q₁ q₂ hq) ^ 4 := by
  haveI := isDedekindDomain_coordinateRing hΔ
  intro hmem
  have hq' : W.Nonsingular q₁ (W.negY q₁ q₂) := (nonsingular_neg ..).mpr hq
  have hne : (Point.some q₁ (W.negY q₁ q₂) hq' : W.Point) ≠ .some q₁ q₂ hq := by
    simp only [ne_eq, Point.some.injEq, not_and]
    exact fun _ => fun hcon => h2Q hcon.symm
  have hspan : Ideal.span {(coordX W - coordC W q₁)} =
      pointIdeal W (.some q₁ (W.negY q₁ q₂) hq') *
        pointIdeal W (.some q₁ q₂ hq) := by
    rw [pointIdeal_some, pointIdeal_some, CoordinateRing.XYIdeal_neg_mul hq,
      CoordinateRing.XIdeal, XClass_eq]
  have hT3 : (coordX W - coordC W q₁) ^ 3 ∈ pointIdeal W (.some q₁ q₂ hq) ^ 4 := by
    have : (coordX W - coordC W q₁) ^ 3 =
        coordC W c⁻¹ * (coordC W c * (coordX W - coordC W q₁) ^ 3) := by
      rw [← mul_assoc, ← coordC_mul, inv_mul_cancel₀ hc, coordC_one, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hmem
  have hdvd : pointIdeal W (.some q₁ q₂ hq) ^ 4 ∣
      (pointIdeal W (.some q₁ (W.negY q₁ q₂) hq') *
        pointIdeal W (.some q₁ q₂ hq)) ^ 3 := by
    rw [← hspan, Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hT3
  have hne0 : pointIdeal W (.some q₁ q₂ hq) ^ 3 ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact pow_ne_zero 3 (pointIdeal_ne_bot hq)
  have hdvd' : pointIdeal W (.some q₁ q₂ hq) ∣
      pointIdeal W (.some q₁ (W.negY q₁ q₂) hq') ^ 3 := by
    refine (mul_dvd_mul_iff_left hne0).mp ?_
    calc pointIdeal W (.some q₁ q₂ hq) ^ 3 * pointIdeal W (.some q₁ q₂ hq)
        = pointIdeal W (.some q₁ q₂ hq) ^ 4 := by ring
      _ ∣ (pointIdeal W (.some q₁ (W.negY q₁ q₂) hq') *
            pointIdeal W (.some q₁ q₂ hq)) ^ 3 := hdvd
      _ = pointIdeal W (.some q₁ q₂ hq) ^ 3 *
            pointIdeal W (.some q₁ (W.negY q₁ q₂) hq') ^ 3 := by ring
  have := eq_of_pointIdeal_dvd hΔ hq
    ((prime_pointIdeal hΔ hq).dvd_of_dvd_pow hdvd')
  exact hne this


omit [DecidableEq F] in
/-- **The branch lies in `I_Q⁴`**: `U − B ∈ I_Q⁴`.  From the cleared branch
identity `(U − B)·V' = T⁴·D` (`sub_branch_mul_eq`), the right side is in
`I_Q⁴` because `T ∈ I_Q`, while `V'` evaluates to `A₀ ≠ 0` at `Q`, hence
`V' ∉ I_Q`; the prime-power squeeze `mem_pointIdeal_pow_of_dvd_of_notMem`
puts the whole `I_Q⁴` on `U − B`.  This is the substitute for constructing
the truncated quotient `F[t]/(t⁴)`: it says exactly that `U` agrees with
the branch to order 3 at `Q`. -/
lemma branch_sub_mem_pointIdeal_pow_four (hΔ : W.Δ ≠ 0) {q₁ q₂ c₁ c₂ c₃ : F}
    (hq : W.Nonsingular q₁ q₂) (hA₀ : 2 * q₂ + W.a₁ * q₁ + W.a₃ ≠ 0)
    (hc₁ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₁ =
      3 * q₁ ^ 2 + 2 * W.a₂ * q₁ + W.a₄ - W.a₁ * q₂)
    (hc₂ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₂ =
      3 * q₁ + W.a₂ - c₁ ^ 2 - W.a₁ * c₁)
    (hc₃ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₃ = 1 - 2 * c₁ * c₂ - W.a₁ * c₂) :
    coordY W - coordC W q₂ -
        (coordC W c₁ * (coordX W - coordC W q₁) +
          coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
          coordC W c₃ * (coordX W - coordC W q₁) ^ 3) ∈
      pointIdeal W (.some q₁ q₂ hq) ^ 4 := by
  haveI := isDedekindDomain_coordinateRing hΔ
  have hT4 : (coordX W - coordC W q₁) ^ 4 ∈ pointIdeal W (.some q₁ q₂ hq) ^ 4 :=
    Ideal.pow_mem_pow (sub_coordX_mem_pointIdeal hq) 4
  refine mem_pointIdeal_pow_of_dvd_of_notMem hΔ hq
    (w := coordC W (2 * q₂ + W.a₁ * q₁ + W.a₃) + (coordY W - coordC W q₂) +
      coordC W W.a₁ * (coordX W - coordC W q₁) +
      (coordC W c₁ * (coordX W - coordC W q₁) +
        coordC W c₂ * (coordX W - coordC W q₁) ^ 2 +
        coordC W c₃ * (coordX W - coordC W q₁) ^ 3)) ?_ ?_
  · rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff,
      sub_branch_mul_eq hq.left hc₁ hc₂ hc₃]
    exact Ideal.mul_mem_right _ _ hT4
  · intro hmem
    have hval := coordEval_eq_zero_of_mem hq hmem
    simp only [map_add, map_sub, map_mul, map_pow, coordEval_coordC,
      coordEval_coordX, coordEval_coordY] at hval
    exact hA₀ (by linear_combination hval)

omit [DecidableEq F] in
/-- **`n ≡ L(2Q)·T³ mod I_Q⁴`.**  Combines the polynomial normal form
`lineNumerator_sub_lineValue_eq` with `branch_sub_mem_pointIdeal_pow_four`:
the `(U − B)·H` part is in `I_Q⁴` because `U − B` is, and `T⁴·K` because
`T ∈ I_Q`.  Consequence used below: if the line passes through `2Q`
(`L(2Q) = 0`) then `n ∈ I_Q⁴`. -/
lemma lineNumerator_sub_lineValue_mem_pow_four (hΔ : W.Δ ≠ 0) {q₁ q₂ c₁ c₂ c₃ : F}
    (hq : W.Nonsingular q₁ q₂) (hA₀ : 2 * q₂ + W.a₁ * q₁ + W.a₃ ≠ 0)
    (hc₁ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₁ =
      3 * q₁ ^ 2 + 2 * W.a₂ * q₁ + W.a₄ - W.a₁ * q₂)
    (hc₂ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₂ =
      3 * q₁ + W.a₂ - c₁ ^ 2 - W.a₁ * c₁)
    (hc₃ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₃ = 1 - 2 * c₁ * c₂ - W.a₁ * c₂)
    (x₁ y₁ ℓ : F) :
    lineNumerator W q₁ q₂ x₁ y₁ ℓ -
        coordC W (W.addY q₁ q₁ q₂ c₁ - (ℓ * (W.addX q₁ q₁ c₁ - x₁) + y₁)) *
          (coordX W - coordC W q₁) ^ 3 ∈
      pointIdeal W (.some q₁ q₂ hq) ^ 4 := by
  have hT4 : (coordX W - coordC W q₁) ^ 4 ∈ pointIdeal W (.some q₁ q₂ hq) ^ 4 :=
    Ideal.pow_mem_pow (sub_coordX_mem_pointIdeal hq) 4
  rw [lineNumerator_sub_lineValue_eq]
  exact add_mem
    (Ideal.mul_mem_right _ _ (branch_sub_mem_pointIdeal_pow_four hΔ hq hA₀ hc₁ hc₂ hc₃))
    (Ideal.mul_mem_right _ _ hT4)

omit [DecidableEq F] in
/-- **`ñ ≡ L(⊖2Q)·T³ mod I_Q⁴`**, the mirror of
`lineNumerator_sub_lineValue_mem_pow_four`.  Consequence used below: if the
line MISSES `⊖2Q` then `ñ ∉ I_Q⁴`, i.e. `v_Q(ñ) = 3` exactly. -/
lemma lineNumeratorNeg_sub_lineValue_mem_pow_four (hΔ : W.Δ ≠ 0)
    {q₁ q₂ c₁ c₂ c₃ : F}
    (hq : W.Nonsingular q₁ q₂) (hA₀ : 2 * q₂ + W.a₁ * q₁ + W.a₃ ≠ 0)
    (hc₁ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₁ =
      3 * q₁ ^ 2 + 2 * W.a₂ * q₁ + W.a₄ - W.a₁ * q₂)
    (hc₂ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₂ =
      3 * q₁ + W.a₂ - c₁ ^ 2 - W.a₁ * c₁)
    (hc₃ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₃ = 1 - 2 * c₁ * c₂ - W.a₁ * c₂)
    (x₁ y₁ ℓ : F) :
    lineNumeratorNeg W q₁ q₂ x₁ y₁ ℓ -
        coordC W (W.negAddY q₁ q₁ q₂ c₁ - (ℓ * (W.addX q₁ q₁ c₁ - x₁) + y₁)) *
          (coordX W - coordC W q₁) ^ 3 ∈
      pointIdeal W (.some q₁ q₂ hq) ^ 4 := by
  have hT4 : (coordX W - coordC W q₁) ^ 4 ∈ pointIdeal W (.some q₁ q₂ hq) ^ 4 :=
    Ideal.pow_mem_pow (sub_coordX_mem_pointIdeal hq) 4
  rw [lineNumeratorNeg_sub_lineValue_eq]
  exact add_mem
    (Ideal.mul_mem_right _ _ (branch_sub_mem_pointIdeal_pow_four hΔ hq hA₀ hc₁ hc₂ hc₃))
    (Ideal.mul_mem_right _ _ hT4)

/-- **A point on the chord is one of its three intersection points.**  If the
line through `P = (x₁,y₁)` and `R = (x₂,y₂)` (at the group-law slope) vanishes
at an affine point `V`, then `V ∈ {P, R, ⊖(P ⊕ R)}`.  Read off
`YIdeal_eq_prod_pointIdeal` — which is uniform in all tangency configurations
— by primality of `I_V`. -/
lemma mem_chord_of_lineValue_eq_zero (hΔ : W.Δ ≠ 0) {x₁ y₁ x₂ y₂ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {α β : F} (hαβ : W.Nonsingular α β)
    (hval : β - (W.slope x₁ x₂ y₁ y₂ * (α - x₁) + y₁) = 0) :
    (Point.some x₁ y₁ h₁ : W.Point) = .some α β hαβ ∨
      (Point.some x₂ y₂ h₂ : W.Point) = .some α β hαβ ∨
      (-(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) : W.Point) = .some α β hαβ := by
  haveI := isDedekindDomain_coordinateRing hΔ
  have hmem : CoordinateRing.YClass W
      (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) ∈
      pointIdeal W (.some α β hαβ) := by
    refine mem_pointIdeal_of_coordEval_eq_zero hαβ ?_
    rw [YClass_line_eq]
    simp only [map_sub, map_add, map_mul, coordEval_coordX, coordEval_coordY,
      coordEval_coordC]
    linear_combination hval
  have hdvd : pointIdeal W (.some α β hαβ) ∣
      pointIdeal W (.some x₁ y₁ h₁) *
        (pointIdeal W (.some x₂ y₂ h₂) *
          pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂))) := by
    rw [← YIdeal_eq_prod_pointIdeal h₁ h₂ hxy, CoordinateRing.YIdeal,
      Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  have hprime := prime_pointIdeal hΔ hαβ
  rcases hprime.dvd_or_dvd hdvd with h | h
  · exact Or.inl (eq_of_pointIdeal_dvd hΔ hαβ h)
  · rcases hprime.dvd_or_dvd h with h | h
    · exact Or.inr (Or.inl (eq_of_pointIdeal_dvd hΔ hαβ h))
    · exact Or.inr (Or.inr (eq_of_pointIdeal_dvd hΔ hαβ h))


omit [DecidableEq F] in
/-- **One coincidence from `I_Q⁴`**: if `I_Q⁴ ∣ I_Q³ · I_{V₁}I_{V₂}I_{V₃}`
then some `Vᵢ = Q`.  Cancel `I_Q³`, then use that `I_Q` is prime. -/
lemma exists_eq_of_pow_four_dvd (hΔ : W.Δ ≠ 0) {q₁ q₂ : F} (hq : W.Nonsingular q₁ q₂)
    {V₁ V₂ V₃ : W.Point}
    (hd : pointIdeal W (.some q₁ q₂ hq) ^ 4 ∣ pointIdeal W (.some q₁ q₂ hq) ^ 3 *
      (pointIdeal W V₁ * (pointIdeal W V₂ * pointIdeal W V₃))) :
    V₁ = .some q₁ q₂ hq ∨ V₂ = .some q₁ q₂ hq ∨ V₃ = .some q₁ q₂ hq := by
  haveI := isDedekindDomain_coordinateRing hΔ
  have hQne0 : pointIdeal W (.some q₁ q₂ hq) ≠ 0 := by
    rw [Ideal.zero_eq_bot]; exact pointIdeal_ne_bot hq
  have hprime := prime_pointIdeal hΔ hq
  have h1 : pointIdeal W (.some q₁ q₂ hq) ∣
      pointIdeal W V₁ * (pointIdeal W V₂ * pointIdeal W V₃) := by
    refine (mul_dvd_mul_iff_left (pow_ne_zero 3 hQne0)).mp ?_
    calc pointIdeal W (.some q₁ q₂ hq) ^ 3 * pointIdeal W (.some q₁ q₂ hq)
        = pointIdeal W (.some q₁ q₂ hq) ^ 4 := by ring
      _ ∣ _ := hd
  rcases hprime.dvd_or_dvd h1 with h | h
  · exact Or.inl (eq_of_pointIdeal_dvd hΔ hq h)
  · rcases hprime.dvd_or_dvd h with h | h
    · exact Or.inr (Or.inl (eq_of_pointIdeal_dvd hΔ hq h))
    · exact Or.inr (Or.inr (eq_of_pointIdeal_dvd hΔ hq h))

omit [DecidableEq F] in
/-- **Two coincidences from `I_Q⁵`**: if `I_Q⁵ ∣ I_Q³ · I_{V₁}I_{V₂}I_{V₃}`
then TWO of the `Vᵢ` equal `Q`.  Cancel `I_Q³` to get `I_Q² ∣ I_{V₁}I_{V₂}I_{V₃}`,
extract one factor by primality, cancel it, and extract a second. -/
lemma two_eq_of_pow_five_dvd (hΔ : W.Δ ≠ 0) {q₁ q₂ : F} (hq : W.Nonsingular q₁ q₂)
    {V₁ V₂ V₃ : W.Point}
    (hd : pointIdeal W (.some q₁ q₂ hq) ^ 5 ∣ pointIdeal W (.some q₁ q₂ hq) ^ 3 *
      (pointIdeal W V₁ * (pointIdeal W V₂ * pointIdeal W V₃))) :
    (V₁ = .some q₁ q₂ hq ∧ V₂ = .some q₁ q₂ hq) ∨
      (V₁ = .some q₁ q₂ hq ∧ V₃ = .some q₁ q₂ hq) ∨
      (V₂ = .some q₁ q₂ hq ∧ V₃ = .some q₁ q₂ hq) := by
  haveI := isDedekindDomain_coordinateRing hΔ
  have hQne0 : pointIdeal W (.some q₁ q₂ hq) ≠ 0 := by
    rw [Ideal.zero_eq_bot]; exact pointIdeal_ne_bot hq
  have hprime := prime_pointIdeal hΔ hq
  have h2 : pointIdeal W (.some q₁ q₂ hq) ^ 2 ∣
      pointIdeal W V₁ * (pointIdeal W V₂ * pointIdeal W V₃) := by
    refine (mul_dvd_mul_iff_left (pow_ne_zero 3 hQne0)).mp ?_
    calc pointIdeal W (.some q₁ q₂ hq) ^ 3 * pointIdeal W (.some q₁ q₂ hq) ^ 2
        = pointIdeal W (.some q₁ q₂ hq) ^ 5 := by ring
      _ ∣ _ := hd
  have h1 : pointIdeal W (.some q₁ q₂ hq) ∣
      pointIdeal W V₁ * (pointIdeal W V₂ * pointIdeal W V₃) :=
    (dvd_pow_self _ two_ne_zero).trans h2
  rcases hprime.dvd_or_dvd h1 with hA | hBC
  · have e1 := eq_of_pointIdeal_dvd hΔ hq hA
    rw [e1] at h2
    have h3 : pointIdeal W (.some q₁ q₂ hq) ∣ pointIdeal W V₂ * pointIdeal W V₃ := by
      refine (mul_dvd_mul_iff_left hQne0).mp ?_
      calc pointIdeal W (.some q₁ q₂ hq) * pointIdeal W (.some q₁ q₂ hq)
          = pointIdeal W (.some q₁ q₂ hq) ^ 2 := by ring
        _ ∣ _ := h2
    rcases hprime.dvd_or_dvd h3 with h | h
    · exact Or.inl ⟨e1, eq_of_pointIdeal_dvd hΔ hq h⟩
    · exact Or.inr (Or.inl ⟨e1, eq_of_pointIdeal_dvd hΔ hq h⟩)
  · rcases hprime.dvd_or_dvd hBC with hB | hC
    · have e2 := eq_of_pointIdeal_dvd hΔ hq hB
      rw [e2] at h2
      have h3 : pointIdeal W (.some q₁ q₂ hq) ∣ pointIdeal W V₁ * pointIdeal W V₃ := by
        refine (mul_dvd_mul_iff_left hQne0).mp ?_
        calc pointIdeal W (.some q₁ q₂ hq) * pointIdeal W (.some q₁ q₂ hq)
            = pointIdeal W (.some q₁ q₂ hq) ^ 2 := by ring
          _ ∣ pointIdeal W V₁ *
                (pointIdeal W (.some q₁ q₂ hq) * pointIdeal W V₃) := h2
          _ = pointIdeal W (.some q₁ q₂ hq) *
                (pointIdeal W V₁ * pointIdeal W V₃) := by ring
      rcases hprime.dvd_or_dvd h3 with h | h
      · exact Or.inl ⟨eq_of_pointIdeal_dvd hΔ hq h, e2⟩
      · exact Or.inr (Or.inr ⟨e2, eq_of_pointIdeal_dvd hΔ hq h⟩)
    · have e3 := eq_of_pointIdeal_dvd hΔ hq hC
      rw [e3] at h2
      have h3 : pointIdeal W (.some q₁ q₂ hq) ∣ pointIdeal W V₁ * pointIdeal W V₂ := by
        refine (mul_dvd_mul_iff_left hQne0).mp ?_
        calc pointIdeal W (.some q₁ q₂ hq) * pointIdeal W (.some q₁ q₂ hq)
            = pointIdeal W (.some q₁ q₂ hq) ^ 2 := by ring
          _ ∣ pointIdeal W V₁ *
                (pointIdeal W V₂ * pointIdeal W (.some q₁ q₂ hq)) := h2
          _ = pointIdeal W (.some q₁ q₂ hq) *
                (pointIdeal W V₁ * pointIdeal W V₂) := by ring
      rcases hprime.dvd_or_dvd h3 with h | h
      · exact Or.inr (Or.inl ⟨eq_of_pointIdeal_dvd hΔ hq h, e3⟩)
      · exact Or.inr (Or.inr ⟨eq_of_pointIdeal_dvd hΔ hq h, e3⟩)

/-- **L4-8 line-numerator sub-leaf (PROVEN 2026-07-25): the multiplicity of
the line numerator at `Q` ITSELF.**  This was the last piece of the coincidence
zoo: `n` achieves the `Q`-multiplicity of its divisor, i.e. `n ∈ I_Q^k`
whenever `I_Q^k` divides the whole product `I_Q³ · I_{P⊖Q} · I_{R⊖Q} ·
I_{⊖(P⊕R)⊖Q}`.  For `k ≤ 3` this is `lineNumerator_mem_pointIdeal_pow_three`;
the content is `k ≥ 4`, which happens exactly when `2Q ∈ {P, R, S}`
(`S = ⊖(P ⊕ R)`).

WHY THE PARTNER SQUEEZE ALONE CANNOT DO THIS.  Every *other* coincident point
is handled by `mem_pointIdeal_pow_of_dvd_of_notMem` together with
`lineNumeratorNeg_notMem_pointIdeal_sub`: at `Z = Pᵢ ⊖ Q ≠ Q` the partner `ñ`
is a UNIT at `Z`.  At `Z = Q` that is unavailable *in principle*: the conjugate
divisor `RHS' = 3(Q) + (⊖P⊖Q) + (⊖R⊖Q) + ((P⊕R)⊖Q)` always contains `3(Q)`, so
`v_Q(ñ) ≥ 3 > 0` unconditionally.  What IS true is that `v_Q(ñ) = 3` *exactly*
in the generic case, and that is what the proof establishes, by a local
expansion at `Q` — the *generalized* squeeze then needs only an UPPER bound on
the partner, not non-vanishing.

PROOF (route: order-4 local normal form; the chord-product route of the
previous owner was rejected — see the note at the end).

* Since `k ≥ 4`, cancelling `I_Q³` and using primality of `I_Q`
  (`exists_eq_of_pow_four_dvd`) gives some `Pᵢ ⊖ Q = Q`, i.e. `Pᵢ = 2Q`; as
  `Pᵢ` is affine this forces `2Q ≠ O`, hence `A₀ = 2q₂ + a₁q₁ + a₃ ≠ 0`.
* With `A₀ ≠ 0` the truncated branch `B = c₁T + c₂T² + c₃T³` exists
  (`c₁ = slope q₁ q₁ q₂ q₂`, then `c₂`, `c₃` by division by `A₀`) and
  `U − B ∈ I_Q⁴` (`branch_sub_mem_pointIdeal_pow_four`).  Substituting it into
  the two numerators gives the order-4 normal forms
  `n ≡ L(2Q)·T³` and `ñ ≡ L(⊖2Q)·T³ mod I_Q⁴`,
  where `L` is the chord through `P` and `R`.  (This replaces the
  `AdjoinRoot.lift` into `F[t]/(t⁴)` sketched by the previous owner: the
  membership `U − B ∈ I_Q⁴` carries all of the truncation, and needs no
  quotient ring.)
* GENERIC CASE `L(⊖2Q) ≠ 0`: then `ñ ∉ I_Q⁴` by
  `smul_pow_three_notMem_pointIdeal_pow_four` (`T³ ∉ I_Q⁴` because `2Q ≠ O`),
  i.e. `v_Q(ñ) ≤ 3`.  Since `I_Q^k ∣ RHS` and `I_Q³ ∣ RHS'`, the product
  identity `span_lineNumerator_mul_lineNumeratorNeg` gives
  `I_Q^(k+3) ∣ ⟨n·ñ⟩`, and `pow_dvd_of_pow_dvd_mul` (with `j = 3`) yields
  `n ∈ I_Q^k` for EVERY `k` at once.
* RESIDUAL CASE `L(⊖2Q) = 0`: then `⊖2Q` lies on the chord
  (`mem_chord_of_lineValue_eq_zero`), so `⊖2Q ∈ {P, R, S}`; combined with
  `2Q ∈ {P, R, S}` and `P ⊕ R ⊕ S = O` (with all three affine) the two must be
  the SAME point, so `2Q = ⊖2Q`, i.e. `4Q = O`.  Then `L(2Q) = L(⊖2Q) = 0`, so
  `n ∈ I_Q⁴` outright by the normal form; and `k ≤ 4`, since `I_Q⁵ ∣ RHS` would
  force two of `P, R, S` to equal `2Q` (`two_eq_of_pow_five_dvd`), whence two
  of them sum to `4Q = O` and the third would be `O`.

WHY NOT THE CHORD-PRODUCT IDENTITY (route 2 of the previous owner's docstring,
`n·L̄ = L(Q)·ℓ(Q,⊖P)·ℓ(Q,⊖R)·ℓ(Q,⊖S)`).  The identity is correct — its divisor
bookkeeping checks out, `⟨ℓ(Q,V)⟩ = I_Q I_V I_{⊖(Q⊕V)}` — but each of the three
chords `ℓ(Q, ⊖Pᵢ)` DEGENERATES to the tangent at `Q` when `Q = ⊖Pᵢ`, and there
`slope_mul_sub` degenerates to `0 = 0`, so the cleared slope relation no longer
pins the slope down: the identity then needs the tangent relation instead, and
one gets a `2³`-way case split with a distinct large certificate in each
branch.  (Its residual degeneracy `2Q = O ∧ Q ∈ {P,R,S}` is harmless here —
`k ≥ 4` already forces `2Q ≠ O` — but the tangency split is not.)  The route
taken above has NO case split of that kind: the two normal forms are single
`ring` identities. -/
theorem lineNumerator_mem_pointIdeal_pow_of_dvd (hΔ : W.Δ ≠ 0)
    {q₁ q₂ x₁ y₁ x₂ y₂ : F}
    (hq : W.Nonsingular q₁ q₂) (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {k : ℕ}
    (hk : pointIdeal W (.some q₁ q₂ hq) ^ k ∣
      pointIdeal W (.some q₁ q₂ hq) ^ 3 *
        (pointIdeal W (.some x₁ y₁ h₁ - .some q₁ q₂ hq) *
          (pointIdeal W (.some x₂ y₂ h₂ - .some q₁ q₂ hq) *
            pointIdeal W (-(.some x₁ y₁ h₁ + .some x₂ y₂ h₂) - .some q₁ q₂ hq)))) :
    lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
      pointIdeal W (.some q₁ q₂ hq) ^ k := by
  haveI := isDedekindDomain_coordinateRing hΔ
  by_cases hk3 : k ≤ 3
  · exact Ideal.pow_le_pow_right hk3
      (lineNumerator_mem_pointIdeal_pow_three hq x₁ y₁ (W.slope x₁ x₂ y₁ y₂))
  have hk4 : 4 ≤ k := by omega
  have hprime := prime_pointIdeal hΔ hq
  have hPR : (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ : W.Point) ≠ 0 := by
    rw [Point.add_some hxy]; exact Point.some_ne_zero _
  have hPS : (Point.some x₁ y₁ h₁ : W.Point) +
      -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) ≠ 0 := by
    intro hc
    refine Point.some_ne_zero h₂ (neg_eq_zero.mp ?_)
    rw [← hc]; abel
  have hRS : (Point.some x₂ y₂ h₂ : W.Point) +
      -(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) ≠ 0 := by
    intro hc
    refine Point.some_ne_zero h₁ (neg_eq_zero.mp ?_)
    rw [← hc]; abel
  -- one of the three translated points is `Q` itself
  have hex := exists_eq_of_pow_four_dvd hΔ hq ((pow_dvd_pow _ hk4).trans hk)
  -- hence `2Q ≠ O`
  have hD0 : (Point.some q₁ q₂ hq + Point.some q₁ q₂ hq : W.Point) ≠ 0 := by
    rcases hex with h | h | h
    · rw [← sub_eq_iff_eq_add.mp h]; exact Point.some_ne_zero h₁
    · rw [← sub_eq_iff_eq_add.mp h]; exact Point.some_ne_zero h₂
    · rw [← sub_eq_iff_eq_add.mp h, neg_ne_zero]; exact hPR
  have h2Q : q₂ ≠ W.negY q₁ q₂ := fun hc => hD0 (Point.add_of_Y_eq rfl hc)
  have hnegYq : W.negY q₁ q₂ = -q₂ - W.a₁ * q₁ - W.a₃ := rfl
  have hA₀ : 2 * q₂ + W.a₁ * q₁ + W.a₃ ≠ 0 := by
    intro hc
    exact h2Q (by rw [hnegYq]; linear_combination hc)
  have hden : q₂ - W.negY q₁ q₂ = 2 * q₂ + W.a₁ * q₁ + W.a₃ := by rw [hnegYq]; ring
  have hc₁ : (2 * q₂ + W.a₁ * q₁ + W.a₃) * W.slope q₁ q₁ q₂ q₂ =
      3 * q₁ ^ 2 + 2 * W.a₂ * q₁ + W.a₄ - W.a₁ * q₂ := by
    rw [slope_of_Y_ne rfl h2Q, hden]
    field_simp
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : F, (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₂ =
      3 * q₁ + W.a₂ - (W.slope q₁ q₁ q₂ q₂) ^ 2 - W.a₁ * (W.slope q₁ q₁ q₂ q₂) :=
    ⟨(3 * q₁ + W.a₂ - (W.slope q₁ q₁ q₂ q₂) ^ 2 - W.a₁ * (W.slope q₁ q₁ q₂ q₂)) /
      (2 * q₂ + W.a₁ * q₁ + W.a₃), by field_simp⟩
  obtain ⟨c₃, hc₃⟩ : ∃ c₃ : F, (2 * q₂ + W.a₁ * q₁ + W.a₃) * c₃ =
      1 - 2 * (W.slope q₁ q₁ q₂ q₂) * c₂ - W.a₁ * c₂ :=
    ⟨(1 - 2 * (W.slope q₁ q₁ q₂ q₂) * c₂ - W.a₁ * c₂) /
      (2 * q₂ + W.a₁ * q₁ + W.a₃), by field_simp⟩
  -- the doubled point and its negative
  have hDsome : (Point.some q₁ q₂ hq + Point.some q₁ q₂ hq : W.Point) =
      Point.some (W.addX q₁ q₁ (W.slope q₁ q₁ q₂ q₂))
        (W.addY q₁ q₁ q₂ (W.slope q₁ q₁ q₂ q₂))
        (nonsingular_add hq hq (fun hc => h2Q hc.2)) :=
    Point.add_some (fun hc => h2Q hc.2)
  have hns' : W.Nonsingular (W.addX q₁ q₁ (W.slope q₁ q₁ q₂ q₂))
      (W.negY (W.addX q₁ q₁ (W.slope q₁ q₁ q₂ q₂))
        (W.addY q₁ q₁ q₂ (W.slope q₁ q₁ q₂ q₂))) :=
    (nonsingular_neg ..).mpr (nonsingular_add hq hq (fun hc => h2Q hc.2))
  have hnegD : -(Point.some q₁ q₂ hq + Point.some q₁ q₂ hq : W.Point) =
      Point.some (W.addX q₁ q₁ (W.slope q₁ q₁ q₂ q₂))
        (W.negY (W.addX q₁ q₁ (W.slope q₁ q₁ q₂ q₂))
          (W.addY q₁ q₁ q₂ (W.slope q₁ q₁ q₂ q₂))) hns' := by
    rw [hDsome, Point.neg_some]
  have hnegAddY : W.negY (W.addX q₁ q₁ (W.slope q₁ q₁ q₂ q₂))
      (W.addY q₁ q₁ q₂ (W.slope q₁ q₁ q₂ q₂)) =
      W.negAddY q₁ q₁ q₂ (W.slope q₁ q₁ q₂ q₂) := by
    simp only [WeierstrassCurve.Affine.addY, negY_negY]
  by_cases hLn : W.negAddY q₁ q₁ q₂ (W.slope q₁ q₁ q₂ q₂) -
      (W.slope x₁ x₂ y₁ y₂ * (W.addX q₁ q₁ (W.slope q₁ q₁ q₂ q₂) - x₁) + y₁) = 0
  · -- residual configuration: `2Q = ⊖2Q` lies on the chord
    have honline := mem_chord_of_lineValue_eq_zero hΔ h₁ h₂ hxy hns'
      (by rw [hnegAddY]; exact hLn)
    rw [← hnegD] at honline
    have hexD : (Point.some x₁ y₁ h₁ : W.Point) =
          Point.some q₁ q₂ hq + Point.some q₁ q₂ hq ∨
        (Point.some x₂ y₂ h₂ : W.Point) =
          Point.some q₁ q₂ hq + Point.some q₁ q₂ hq ∨
        (-(Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) : W.Point) =
          Point.some q₁ q₂ hq + Point.some q₁ q₂ hq := by
      rcases hex with h | h | h
      · exact Or.inl (sub_eq_iff_eq_add.mp h)
      · exact Or.inr (Or.inl (sub_eq_iff_eq_add.mp h))
      · exact Or.inr (Or.inr (sub_eq_iff_eq_add.mp h))
    have hsumneg : ∀ {U V : W.Point},
        U = Point.some q₁ q₂ hq + Point.some q₁ q₂ hq →
        V = -(Point.some q₁ q₂ hq + Point.some q₁ q₂ hq) → U + V = 0 := by
      intro U V hu hv; rw [hu, hv]; exact add_neg_cancel _
    have hsumneg' : ∀ {U V : W.Point},
        U = -(Point.some q₁ q₂ hq + Point.some q₁ q₂ hq) →
        V = Point.some q₁ q₂ hq + Point.some q₁ q₂ hq → U + V = 0 := by
      intro U V hu hv; rw [hu, hv]; exact neg_add_cancel _
    have hDD : (Point.some q₁ q₂ hq + Point.some q₁ q₂ hq : W.Point) =
        -(Point.some q₁ q₂ hq + Point.some q₁ q₂ hq) := by
      rcases hexD with e1 | e1 | e1 <;> rcases honline with e2 | e2 | e2
      · exact e1.symm.trans e2
      · exact absurd (hsumneg e1 e2) hPR
      · exact absurd (hsumneg e1 e2) hPS
      · exact absurd (hsumneg' e2 e1) hPR
      · exact e1.symm.trans e2
      · exact absurd (hsumneg e1 e2) hRS
      · exact absurd (hsumneg' e2 e1) hPS
      · exact absurd (hsumneg' e2 e1) hRS
      · exact e1.symm.trans e2
    have hsum0 : ∀ {U V : W.Point},
        U = Point.some q₁ q₂ hq + Point.some q₁ q₂ hq →
        V = Point.some q₁ q₂ hq + Point.some q₁ q₂ hq → U + V = 0 := by
      intro U V hu hv; rw [hu, hv]; nth_rewrite 2 [hDD]; exact add_neg_cancel _
    -- the line value at `2Q` vanishes, so `n ∈ I_Q⁴`
    have hDDcoord := hDD
    rw [hnegD, hDsome] at hDDcoord
    simp only [Point.some.injEq] at hDDcoord
    have hLval : W.addY q₁ q₁ q₂ (W.slope q₁ q₁ q₂ q₂) -
        (W.slope x₁ x₂ y₁ y₂ * (W.addX q₁ q₁ (W.slope q₁ q₁ q₂ q₂) - x₁) + y₁) = 0 := by
      rw [hDDcoord.2, hnegAddY]; exact hLn
    have hn4 : lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∈
        pointIdeal W (.some q₁ q₂ hq) ^ 4 := by
      have h := lineNumerator_sub_lineValue_mem_pow_four hΔ hq hA₀ hc₁ hc₂ hc₃ x₁ y₁
        (W.slope x₁ x₂ y₁ y₂)
      rwa [hLval, show coordC W (0 : F) = 0 from by rw [coordC_eq_algebraMap, map_zero],
        zero_mul, sub_zero] at h
    -- and `k ≤ 4`
    have hkle : k ≤ 4 := by
      by_contra hcon
      rw [Nat.not_le] at hcon
      rcases two_eq_of_pow_five_dvd hΔ hq ((pow_dvd_pow _ hcon).trans hk) with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hPR (hsum0 (sub_eq_iff_eq_add.mp e1) (sub_eq_iff_eq_add.mp e2))
      · exact hPS (hsum0 (sub_eq_iff_eq_add.mp e1) (sub_eq_iff_eq_add.mp e2))
      · exact hRS (hsum0 (sub_eq_iff_eq_add.mp e1) (sub_eq_iff_eq_add.mp e2))
    exact Ideal.pow_le_pow_right hkle hn4
  · -- generic configuration: the conjugate numerator is exactly of order 3 at `Q`
    have hnmem : lineNumeratorNeg W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂) ∉
        pointIdeal W (.some q₁ q₂ hq) ^ 4 := by
      intro hmem
      have hsub := sub_mem hmem (lineNumeratorNeg_sub_lineValue_mem_pow_four hΔ hq hA₀
        hc₁ hc₂ hc₃ x₁ y₁ (W.slope x₁ x₂ y₁ y₂))
      rw [sub_sub_cancel] at hsub
      exact smul_pow_three_notMem_pointIdeal_pow_four hΔ hq h2Q hLn hsub
    have hdvdmul : pointIdeal W (.some q₁ q₂ hq) ^ (k + 3) ∣
        Ideal.span {lineNumerator W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂)} *
          Ideal.span {lineNumeratorNeg W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂)} := by
      rw [Ideal.span_singleton_mul_span_singleton,
        span_lineNumerator_mul_lineNumeratorNeg hΔ hq h₁ h₂ hxy, pow_add]
      exact mul_dvd_mul hk (dvd_mul_right _ _)
    have hnotdvd : ¬ (pointIdeal W (.some q₁ q₂ hq) ^ (3 + 1) ∣
        Ideal.span {lineNumeratorNeg W q₁ q₂ x₁ y₁ (W.slope x₁ x₂ y₁ y₂)}) := by
      intro hc
      rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff] at hc
      exact hnmem hc
    have hfin := pow_dvd_of_pow_dvd_mul hprime 3 k _ _ hdvdmul hnotdvd
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff] at hfin
    exact hfin

/-- **L4-8 line-numerator sub-leaf: the assembly in the COINCIDENT
configurations — the residual coincidence zoo, now REDUCED to a single
local statement at `Q`.**

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

PROOF (2026-07-25).  The *non-vanishing squeeze* recommended by the
previous owner is carried out here, and it discharges the entire zoo
EXCEPT at `Q`, where it provably cannot work.  Structure:

* The divisor is packaged as a MULTISET `E = {Q, Q, Q, P⊖Q, R⊖Q, S⊖Q}`
  and the target product is `(E.map I).prod` (`mem_prod_map_pointIdeal`);
  it therefore suffices to prove `n ∈ I_Z ^ (E.count Z)` for every point
  `Z` separately, with no case analysis on which factors coincide.
* At a point `Z` of multiplicity `≤ 1` the single membership `hQ3`/`hA`/
  `hB`/`hC` already gives it.
* At a coincident `Z ≠ Q` — i.e. two of `P⊖Q`, `R⊖Q`, `S⊖Q` agree — the
  coincidence itself supplies the non-vanishing input: `P = R` forces
  `2P ≠ O` through `hxy`, and `P = S` (resp. `R = S`) forces `2P ≠ O`
  (resp. `2R ≠ O`) because otherwise `R = ⊖2P = O` (resp. `P = O`).  Also
  `Z ≠ ±Q`, since `Z = ⊖Q` would mean `P = O`.  So
  `lineNumeratorNeg_notMem_pointIdeal_sub` applies, and the prime-power
  squeeze `mem_pointIdeal_pow_of_dvd_of_notMem` against the product
  identity `span_lineNumerator_mul_lineNumeratorNeg` puts the WHOLE
  `Z`-multiplicity on `n`.
* At `Z = Q` the squeeze in that form is unavailable in principle — the
  conjugate divisor always contains `3(Q)`, so `ñ ∈ I_Q` — and that single
  local statement is isolated as `lineNumerator_mem_pointIdeal_pow_of_dvd`,
  now PROVEN (2026-07-25) by an order-4 local normal form at `Q` feeding a
  *generalized* squeeze that needs only `v_Q(ñ) ≤ 3` rather than
  `ñ ∉ I_Q`. -/
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
  classical
  set ℓ := W.slope x₁ x₂ y₁ y₂ with hℓ
  set n := lineNumerator W q₁ q₂ x₁ y₁ ℓ with hn
  set ñ := lineNumeratorNeg W q₁ q₂ x₁ y₁ ℓ with hñ
  set Q : W.Point := .some q₁ q₂ hq with hQdef
  set P : W.Point := .some x₁ y₁ h₁ with hPdef
  set R : W.Point := .some x₂ y₂ h₂ with hRdef
  set E : Multiset W.Point :=
    Q ::ₘ Q ::ₘ Q ::ₘ (P - Q) ::ₘ (R - Q) ::ₘ ({-(P + R) - Q} : Multiset W.Point)
    with hE
  have hED : (E.map (pointIdeal W)).prod =
      pointIdeal W Q ^ 3 *
        (pointIdeal W (P - Q) *
          (pointIdeal W (R - Q) * pointIdeal W (-(P + R) - Q))) := by
    rw [hE]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
      Multiset.prod_singleton]
    ring
  have hdvd_gen : ∀ Z : W.Point,
      pointIdeal W Z ^ E.count Z ∣ (E.map (pointIdeal W)).prod := by
    intro Z
    have hle : Multiset.replicate (E.count Z) Z ≤ E :=
      Multiset.le_count_iff_replicate_le.mp le_rfl
    have hd := Multiset.prod_dvd_prod_of_le
      (Multiset.map_le_map (f := pointIdeal W) hle)
    rwa [Multiset.map_replicate, Multiset.prod_replicate] at hd
  have hmul := span_lineNumerator_mul_lineNumeratorNeg hΔ hq h₁ h₂ hxy
  have hmem1 : ∀ Z : W.Point, Z ∈ E → n ∈ pointIdeal W Z := by
    intro Z hZ
    rw [hE] at hZ
    simp only [Multiset.mem_cons, Multiset.mem_singleton] at hZ
    rcases hZ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (Ideal.pow_le_self (by norm_num)) hQ3
    · exact (Ideal.pow_le_self (by norm_num)) hQ3
    · exact (Ideal.pow_le_self (by norm_num)) hQ3
    · exact hA
    · exact hB
    · exact hC
  have key : ∀ Z : W.Point, n ∈ pointIdeal W Z ^ E.count Z := by
    intro Z
    have hdvdD : pointIdeal W Z ^ E.count Z ∣
        pointIdeal W Q ^ 3 *
          (pointIdeal W (P - Q) *
            (pointIdeal W (R - Q) * pointIdeal W (-(P + R) - Q))) := by
      rw [← hED]; exact hdvd_gen Z
    by_cases hZQ : Z = Q
    · subst hZQ
      exact lineNumerator_mem_pointIdeal_pow_of_dvd hΔ hq h₁ h₂ hxy hdvdD
    · have hdvdspan : pointIdeal W Z ^ E.count Z ∣ Ideal.span {n * ñ} := by
        rw [hmul]; exact hdvdD.trans (dvd_mul_right _ _)
      cases Z with
      | zero =>
        rw [show pointIdeal W (Point.zero : W.Point) = ⊤ from rfl, ← Ideal.one_eq_top,
          one_pow, Ideal.one_eq_top]
        exact Submodule.mem_top
      | some α β hαβ =>
        by_cases hle : E.count (Point.some α β hαβ) ≤ 1
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
          · rw [h0, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
          · rw [h1, pow_one]
            exact hmem1 _ (Multiset.count_pos.mp (by omega))
        · -- the coincident branch: at least two of `A, B, C` are `Z`
          have hcnt : E.count (Point.some α β hαβ) =
              (if (Point.some α β hαβ : W.Point) = P - Q then 1 else 0)
              + (if (Point.some α β hαβ : W.Point) = R - Q then 1 else 0)
              + (if (Point.some α β hαβ : W.Point) = -(P + R) - Q then 1 else 0) := by
            rw [hE]
            simp only [Multiset.count_cons, Multiset.count_singleton, if_neg hZQ]
            ring
          -- a translate of a nonzero point is neither `Q` nor `⊖Q`, so `α ≠ q₁`
          have hneOf : ∀ V : W.Point, V ≠ 0 →
              (Point.some α β hαβ : W.Point) = V - Q → α ≠ q₁ := by
            intro V hV0 hZV hc
            rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hαβ.left hq.left hc with hyy | hyy
            · exact hZQ (by rw [hQdef]; subst hc; subst hyy; rfl)
            · refine hV0 ?_
              have hZnQ : (Point.some α β hαβ : W.Point) = -Q := by
                rw [hQdef, Point.neg_some]; subst hc; subst hyy; rfl
              have h2 : V - Q = -Q := hZV.symm.trans hZnQ
              rwa [sub_eq_iff_eq_add, neg_add_cancel] at h2
          have hnot : ∀ (u v : F) (hu : W.Nonsingular u v),
              (Point.some u v hu : W.Point) ≠ 0 →
              (Point.some α β hαβ : W.Point) = Point.some u v hu - Q →
              v ≠ W.negY u v →
              lineNumeratorNeg W q₁ q₂ u v ℓ ∉ pointIdeal W (.some α β hαβ) := by
            intro u v hu hu0 hZu h2u
            exact lineNumeratorNeg_notMem_pointIdeal_sub hq hu hαβ hZu.symm ℓ h2u
              (hneOf _ hu0 hZu)
          have hfin : ∀ w : W.CoordinateRing, w = ñ →
              w ∉ pointIdeal W (.some α β hαβ) →
              n ∈ pointIdeal W (Point.some α β hαβ) ^ E.count (Point.some α β hαβ) := by
            intro w hw hwn
            exact mem_pointIdeal_pow_of_dvd_of_notMem hΔ hαβ hdvdspan (hw ▸ hwn)
          by_cases hZA : (Point.some α β hαβ : W.Point) = P - Q
          · by_cases hZB : (Point.some α β hαβ : W.Point) = R - Q
            · -- `P = R`: the chord is the tangent at `P`, and `2P ≠ O` by `hxy`
              have hPR : (P : W.Point) = R := sub_left_inj.mp (hZA.symm.trans hZB)
              rw [hPdef, hRdef, Point.some.injEq] at hPR
              refine hfin ñ rfl (hnot x₁ y₁ h₁ (Point.some_ne_zero h₁) hZA ?_)
              intro hc
              exact hxy ⟨hPR.1, by rw [hc, hPR.1, hPR.2]⟩
            · have hZC : (Point.some α β hαβ : W.Point) = -(P + R) - Q := by
                by_contra hc
                rw [if_pos hZA, if_neg hZB, if_neg hc] at hcnt
                omega
              -- `P = ⊖(P ⊕ R)`, so `2P = O` would force `R = O`
              have hPS : (P : W.Point) = -(P + R) := sub_left_inj.mp (hZA.symm.trans hZC)
              refine hfin ñ rfl (hnot x₁ y₁ h₁ (Point.some_ne_zero h₁) hZA ?_)
              intro hc
              refine Point.some_ne_zero h₂ ?_
              have h2P : (P : W.Point) + P = 0 := by
                rw [hPdef]; exact Point.add_of_Y_eq rfl hc
              rw [eq_neg_iff_add_eq_zero, ← add_assoc, h2P, zero_add] at hPS
              rw [← hRdef]; exact hPS
          · have hZB : (Point.some α β hαβ : W.Point) = R - Q := by
              by_contra hc
              rw [if_neg hZA, if_neg hc] at hcnt
              split_ifs at hcnt <;> omega
            have hZC : (Point.some α β hαβ : W.Point) = -(P + R) - Q := by
              by_contra hc
              rw [if_neg hZA, if_pos hZB, if_neg hc] at hcnt
              omega
            -- `R = ⊖(P ⊕ R)`, so `2R = O` would force `P = O`
            have hRS : (R : W.Point) = -(P + R) := sub_left_inj.mp (hZB.symm.trans hZC)
            refine hfin (lineNumeratorNeg W q₁ q₂ x₂ y₂ ℓ)
              (lineNumeratorNeg_congr (slope_mul_sub h₁.left h₂.left hxy)).symm
              (hnot x₂ y₂ h₂ (Point.some_ne_zero h₂) hZB ?_)
            intro hc
            refine Point.some_ne_zero h₁ ?_
            have h2R : (R : W.Point) + R = 0 := by
              rw [hRdef]; exact Point.add_of_Y_eq rfl hc
            rw [eq_neg_iff_add_eq_zero, add_comm (P : W.Point) R, ← add_assoc, h2R,
              zero_add] at hRS
            rw [← hPdef]; exact hRS
  have hfinal := mem_prod_map_pointIdeal E key
  rwa [hED] at hfinal

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

/-- **L4-8 numerator leaf (PROVEN): the divisor of the line
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
every degeneracy makes both factors drop in lockstep.

STATUS (2026-07-25, after three owners landed): the whole subtree is now
proven.  `lineNumerator_mul_lineNumeratorNeg` is proven outright (one
cleared `addPolynomial` identity, discharged by a single
`linear_combination`).  Both membership leaves are proven: the plain one
from its four factor memberships plus the comaximal assembly
`lineNumerator_mem_prod_of_mem_factors` and the multiplicity-wise
coincident assembly `lineNumerator_mem_prod_of_mem_factors_coincident`,
and the conjugate one from the plain one by involution transport
(`involHom`, `map_involHom_pointIdeal`, `involHom_lineNumerator`).  The
last local statement, the `Q`-multiplicity
`lineNumerator_mem_pointIdeal_pow_of_dvd`, was closed by the order-4
normal form of the two numerators at `Q`
(`lineNumerator_sub_lineValue_mem_pow_four` and its mirror) feeding the
generalized prime-power squeeze `pow_dvd_of_pow_dvd_mul`. -/
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

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The `2`-division polynomial is nonzero** for a curve of nonzero
discriminant: `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` vanishing identically
forces `4 = b₂ = b₆ = 0`, hence `2 = 0` (a field), hence
`Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆ = 0`. -/
theorem Ψ₂Sq_ne_zero_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) : W.Ψ₂Sq ≠ 0 := by
  intro h0
  have h4 : (4 : F) = 0 := by
    have h := congrArg (fun q => Polynomial.coeff q 3) h0
    simpa [WeierstrassCurve.Ψ₂Sq, Polynomial.coeff_one] using h
  have hb2 : W.b₂ = 0 := by
    have h := congrArg (fun q => Polynomial.coeff q 2) h0
    simpa [WeierstrassCurve.Ψ₂Sq, Polynomial.coeff_one] using h
  have hb6 : W.b₆ = 0 := by
    have h := congrArg (fun q => Polynomial.coeff q 0) h0
    simpa [WeierstrassCurve.Ψ₂Sq, Polynomial.coeff_one] using h
  have h2 : (2 : F) = 0 := by
    have hsq : (2 : F) ^ 2 = 0 := by linear_combination h4
    exact pow_eq_zero_iff two_ne_zero |>.mp hsq
  refine hΔ ?_
  rw [WeierstrassCurve.Δ]
  linear_combination (-(W.b₂) * W.b₈ + 9 * W.b₄ * W.b₆) * hb2 +
    (-27 * W.b₆) * hb6 + (-4 * W.b₄ ^ 3) * h2

omit [DecidableEq F] [IsAlgClosed F] in
/-- The fraction-field lift of an evaluation fixes the constants
(the general form of `lift_pointEval_constHom`, applied below at the
generic multiple `p • taut` and at `⊖taut`). -/
lemma lift_eval_constHom {x₀ y₀ : W.FunctionField}
    (h : (curveK W).Equation x₀ y₀)
    (hg : Function.Injective (pointEval (constHom W) h)) (d : F) :
    IsFractionRing.lift hg (constHom W d) = constHom W d := by
  show IsFractionRing.lift hg (algebraMap W.CoordinateRing W.FunctionField
    (CoordinateRing.mk W (Polynomial.C (Polynomial.C d)))) = constHom W d
  rw [IsFractionRing.lift_algebraMap, pointEval_C]

omit [DecidableEq F] [IsAlgClosed F] in
/-- The fraction-field lift of an evaluation sends the tautological
`x`-coordinate to the point's `x`-coordinate. -/
lemma lift_eval_tautX {x₀ y₀ : W.FunctionField}
    (h : (curveK W).Equation x₀ y₀)
    (hg : Function.Injective (pointEval (constHom W) h)) :
    IsFractionRing.lift hg (tautX W) = x₀ := by
  rw [tautX, IsFractionRing.lift_algebraMap, pointEval_X]

omit [DecidableEq F] [IsAlgClosed F] in
/-- The fraction-field lift of an evaluation sends the tautological
`y`-coordinate to the point's `y`-coordinate. -/
lemma lift_eval_tautY {x₀ y₀ : W.FunctionField}
    (h : (curveK W).Equation x₀ y₀)
    (hg : Function.Injective (pointEval (constHom W) h)) :
    IsFractionRing.lift hg (tautY W) = y₀ := by
  rw [tautY, IsFractionRing.lift_algebraMap, pointEval_Y]

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The canonical embedding of the coordinate ring into the function
field is evaluation at the tautological point** — the two ring
homomorphisms agree on the constants and on both coordinate
functions. -/
lemma algebraMap_eq_pointEval_taut (W : WeierstrassCurve.Affine F) :
    (algebraMap W.CoordinateRing W.FunctionField) =
      pointEval (constHom W) (taut_equation W) := by
  refine coordinateRing_ringHom_ext (fun d => ?_) ?_ ?_
  · rw [pointEval_C]; rfl
  · rw [pointEval_X]; rfl
  · rw [pointEval_Y]; rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- `pointEval` on the `{1, Y}`-basis presentation of a coordinate-ring
element: `pp + qq·Y ↦ pp(x₀) + qq(x₀)·y₀`. -/
lemma pointEval_smul_basis {K' : Type*} [Field K'] (φ : F →+* K') {x₀ y₀ : K'}
    (h : ((W.map φ).toAffine).Equation x₀ y₀) (pp qq : Polynomial F) :
    pointEval φ h (pp • (1 : W.CoordinateRing) +
        qq • CoordinateRing.mk W Polynomial.X) =
      (pp.map φ).eval x₀ + (qq.map φ).eval x₀ * y₀ := by
  rw [CoordinateRing.smul, CoordinateRing.smul, mul_one, map_add, map_mul,
    pointEval_ofPoly, pointEval_ofPoly, pointEval_Y]

omit [DecidableEq F] [IsAlgClosed F] in
/-- A polynomial in the constants evaluated at a member of an
intermediate field of the function field stays in that field. -/
lemma eval_map_constHom_mem {L' : Type*} [Field L']
    [Algebra L' W.FunctionField] (M : IntermediateField L' W.FunctionField)
    (hc : ∀ d : F, constHom W d ∈ M) {x₀ : W.FunctionField} (hx : x₀ ∈ M)
    (r : Polynomial F) : (r.map (constHom W)).eval x₀ ∈ M := by
  refine Polynomial.induction_on' r ?_ ?_
  · intro f g hf hg
    rw [Polynomial.map_add, Polynomial.eval_add]
    exact add_mem hf hg
  · intro n a
    rw [Polynomial.map_monomial, Polynomial.eval_monomial]
    exact mul_mem (hc a) (pow_mem hx n)

omit [DecidableEq F] in
/-- **L4-5/6 sub-leaf (PROVEN): the `[p]`-pullback subfield has index at
most `p²`** — `[K : [p]^*K] ≤ p²`.  The subfield
`L := (IsFractionRing.lift hinj).fieldRange` contains the constants
(`[p]^*` fixes them, `lift_eval_constHom`) and the coordinates
`xp, yp` of `p • taut` (`lift_eval_tautX`, `lift_eval_tautY`).

The proof runs in the intermediate field `M := L(tautX)`:

* `tautX` is a root of `q := Φ_p − C xp·ΨSq_p ∈ L[T]`, which is monic
  of degree `p²` (`coeff_Φ` gives the leading `1`, `natDegree_ΨSq_le`
  keeps the correction below `p²`) and annihilates `tautX` by `hxrel`;
  so `tautX` is integral over `L` with
  `[M : L] = (minpoly L tautX).natDegree ≤ p²`
  (`IntermediateField.adjoin.finrank`).
* `tautY ∈ M` by the `y`-bookkeeping.  Write `yp = a/b` with
  `a, b ∈ F[W]` (`IsFractionRing.div_surjective`) and expand both in
  the `{1, Y}`-basis (`CoordinateRing.exists_smul_basis_eq`,
  `algebraMap_eq_pointEval_taut`, `pointEval_smul_basis`):
  `yp·(B₁ + B₂·tautY) = A₁ + A₂·tautY` with all `Aᵢ, Bᵢ ∈ M`
  (`eval_map_constHom_mem`).  Applying the hyperelliptic involution
  `ι` — the lift of evaluation at `⊖taut`, which fixes the constants
  and `tautX`, sends `tautY ↦ negY` and hence (through `endoMap`,
  `hsmul`) `yp ↦ negY xp yp` — gives the conjugate relation.  If
  `yp·B₂ ≠ A₂` the first relation solves for `tautY`; otherwise the
  two relations combine to
  `(2yp + a₁xp + a₃)·(B₁ + B₂·negY tautX tautY) = 0`, and
  `2yp + a₁xp + a₃ ≠ 0` because `Ψ₂Sq ≠ 0`
  (`Ψ₂Sq_ne_zero_of_Δ_ne_zero`) does not vanish at the nonconstant
  `xp` (`smul_taut_xCoord_ne_constHom`), so `B₁ + B₂·negY = 0` and
  either `tautY` is solved for or `b = 0`, a contradiction.
* `M = ⊤`, since every `z ∈ K` is a ratio of elements of `F[W]`, each
  of which is `pp(tautX) + qq(tautX)·tautY ∈ M`.

Hence `[K : L] = [M : L] ≤ p²`.  The hypothesis `hp : (p : F) ≠ 0` is
not needed: the degree bookkeeping only uses `hxrel`. -/
theorem finiteDimensional_and_finrank_le_pullback (hΔ : W.Δ ≠ 0)
    (_hp : (p : F) ≠ 0)
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
  classical
  set L : Subfield W.FunctionField :=
    (IsFractionRing.lift (K := W.FunctionField) hinj).fieldRange
  -- the constants and the coordinates of `p • taut` lie in `L`
  have hconstL : ∀ d : F, constHom W d ∈ L := fun d =>
    RingHom.mem_fieldRange.mpr ⟨constHom W d, lift_eval_constHom hpn.left hinj d⟩
  have hxpL : xp ∈ L :=
    RingHom.mem_fieldRange.mpr ⟨tautX W, lift_eval_tautX hpn.left hinj⟩
  have hypL : yp ∈ L :=
    RingHom.mem_fieldRange.mpr ⟨tautY W, lift_eval_tautY hpn.left hinj⟩
  -- the hyperelliptic involution as an endomorphism of the function field
  have hnegns : (curveK W).Nonsingular (tautX W)
      ((curveK W).negY (tautX W) (tautY W)) :=
    ((curveK W).nonsingular_neg (tautX W) (tautY W)).mpr (taut_nonsingular W hΔ)
  have hιinj := pointEval_injective_of_forall_ne_constHom hnegns tautX_ne_constHom
  have hιconst : ∀ d : F,
      IsFractionRing.lift hιinj (constHom W d) = constHom W d := fun d =>
    lift_eval_constHom hnegns.left hιinj d
  have hιX : IsFractionRing.lift hιinj (tautX W) = tautX W :=
    lift_eval_tautX hnegns.left hιinj
  have hιY : IsFractionRing.lift hιinj (tautY W) =
      (curveK W).negY (tautX W) (tautY W) :=
    lift_eval_tautY hnegns.left hιinj
  have hcvι : (curveK W).map (IsFractionRing.lift hιinj) = W.map (constHom W) :=
    curveK_map_eq_of_constHom hιconst
  have hendoTaut : endoMap hcvι (tautPoint W hΔ) = -tautPoint W hΔ := by
    rw [tautPoint, endoMap_some, Point.neg_some]
    exact point_some_congr' hιX hιY
  have hendoP : endoMap hcvι ((p : ℤ) • tautPoint W hΔ) =
      -((p : ℤ) • tautPoint W hΔ) := by
    rw [endoMap_zsmul, hendoTaut, zsmul_neg]
  rw [hsmul, endoMap_some, Point.neg_some] at hendoP
  injection hendoP with hιxp hιyp
  -- `p • taut` is not a `2`-torsion point
  have heqp := ((curveK W).equation_iff xp yp).mp hpn.left
  have hΨmap : (curveK W).Ψ₂Sq = (W.Ψ₂Sq).map (constHom W) :=
    W.map_Ψ₂Sq (constHom W)
  have hΨne : ((W.Ψ₂Sq).map (constHom W)).eval xp ≠ 0 :=
    eval_map_ne_zero_of_forall_ne_constHom (smul_taut_xCoord_ne_constHom hxrel)
      (Ψ₂Sq_ne_zero_of_Δ_ne_zero hΔ)
  have hval : ((W.Ψ₂Sq).map (constHom W)).eval xp =
      (2 * yp + ((curveK W).a₁ * xp + (curveK W).a₃)) ^ 2 := by
    rw [← hΨmap, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    linear_combination (-4 : W.FunctionField) * heqp
  have hsne : 2 * yp + ((curveK W).a₁ * xp + (curveK W).a₃) ≠ 0 := by
    intro hc
    rw [hval, hc] at hΨne
    exact hΨne (by ring)
  -- the intermediate field generated by the tautological `x`-coordinate
  set M : IntermediateField ↥L W.FunctionField :=
    IntermediateField.adjoin ↥L {tautX W}
  have hLM : ∀ {w : W.FunctionField}, w ∈ L → w ∈ M := fun {w} hw =>
    M.algebraMap_mem ⟨w, hw⟩
  have htXM : tautX W ∈ M :=
    IntermediateField.subset_adjoin ↥L {tautX W} rfl
  have hMpoly : ∀ r : Polynomial F,
      (r.map (constHom W)).eval (tautX W) ∈ M := fun r =>
    eval_map_constHom_mem M (fun d => hLM (hconstL d)) htXM r
  have halg : ∀ pp qq : Polynomial F,
      algebraMap W.CoordinateRing W.FunctionField
          (pp • (1 : W.CoordinateRing) + qq • CoordinateRing.mk W Polynomial.X) =
        (pp.map (constHom W)).eval (tautX W) +
          (qq.map (constHom W)).eval (tautX W) * tautY W := by
    intro pp qq
    rw [algebraMap_eq_pointEval_taut]
    exact pointEval_smul_basis (constHom W) (taut_equation W) pp qq
  have hιalg : ∀ pp qq : Polynomial F,
      IsFractionRing.lift hιinj (algebraMap W.CoordinateRing W.FunctionField
          (pp • (1 : W.CoordinateRing) + qq • CoordinateRing.mk W Polynomial.X)) =
        (pp.map (constHom W)).eval (tautX W) +
          (qq.map (constHom W)).eval (tautX W) *
            (-tautY W - (curveK W).a₁ * tautX W - (curveK W).a₃) := by
    intro pp qq
    rw [IsFractionRing.lift_algebraMap]
    exact pointEval_smul_basis (constHom W) hnegns.left pp qq
  -- the `y`-bookkeeping: `tautY` lies in `L(tautX)`
  have hYM : tautY W ∈ M := by
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective W.CoordinateRing yp
    obtain ⟨pa, qa, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
    obtain ⟨pb, qb, rfl⟩ := CoordinateRing.exists_smul_basis_eq b
    have hb0 : algebraMap W.CoordinateRing W.FunctionField
        (pb • (1 : W.CoordinateRing) + qb • CoordinateRing.mk W Polynomial.X)
        ≠ 0 :=
      map_ne_zero_of_mem_nonZeroDivisors _
        (IsFractionRing.injective W.CoordinateRing W.FunctionField) hb
    have hE1 := (div_eq_iff hb0).mp hab
    have hE2 := congrArg (IsFractionRing.lift hιinj) hE1
    rw [map_mul, hιyp, hιalg, hιalg] at hE2
    rw [halg, halg] at hE1
    simp only [Affine.negY] at hE2
    by_cases hd : yp * (qb.map (constHom W)).eval (tautX W) -
        (qa.map (constHom W)).eval (tautX W) = 0
    · have hA1 : (pa.map (constHom W)).eval (tautX W) =
          yp * (pb.map (constHom W)).eval (tautX W) := by
        linear_combination hE1 + tautY W * hd
      have hkey : (pb.map (constHom W)).eval (tautX W) +
          (qb.map (constHom W)).eval (tautX W) *
            (-tautY W - (curveK W).a₁ * tautX W - (curveK W).a₃) = 0 := by
        have hmul : (2 * yp + ((curveK W).a₁ * xp + (curveK W).a₃)) *
            ((pb.map (constHom W)).eval (tautX W) +
              (qb.map (constHom W)).eval (tautX W) *
                (-tautY W - (curveK W).a₁ * tautX W - (curveK W).a₃)) = 0 := by
          linear_combination hE2 - hA1 +
            (-tautY W - (curveK W).a₁ * tautX W - (curveK W).a₃) * hd
        rcases mul_eq_zero.mp hmul with h | h
        · exact absurd h hsne
        · exact h
      by_cases hB : (qb.map (constHom W)).eval (tautX W) = 0
      · exfalso
        refine hb0 ?_
        rw [halg, hB]
        rw [hB] at hkey
        linear_combination hkey
      · have hu : tautY W =
            ((pb.map (constHom W)).eval (tautX W) -
              (qb.map (constHom W)).eval (tautX W) *
                ((curveK W).a₁ * tautX W + (curveK W).a₃)) /
              (qb.map (constHom W)).eval (tautX W) := by
          rw [eq_div_iff hB]
          linear_combination -hkey
        rw [hu]
        exact div_mem (sub_mem (hMpoly pb) (mul_mem (hMpoly qb)
          (add_mem (mul_mem (hLM (hconstL W.a₁)) htXM) (hLM (hconstL W.a₃)))))
          (hMpoly qb)
    · have hu : tautY W =
          ((pa.map (constHom W)).eval (tautX W) -
            yp * (pb.map (constHom W)).eval (tautX W)) /
            (yp * (qb.map (constHom W)).eval (tautX W) -
              (qa.map (constHom W)).eval (tautX W)) := by
        rw [eq_div_iff hd]
        linear_combination -hE1
      rw [hu]
      exact div_mem (sub_mem (hMpoly pa) (mul_mem (hLM hypL) (hMpoly pb)))
        (sub_mem (mul_mem (hLM hypL) (hMpoly qb)) (hMpoly qa))
  -- `K` is generated by the two tautological coordinates
  have hMtop : M = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective W.CoordinateRing z
    obtain ⟨pa, qa, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
    obtain ⟨pb, qb, rfl⟩ := CoordinateRing.exists_smul_basis_eq b
    rw [halg, halg]
    exact div_mem (add_mem (hMpoly pa) (mul_mem (hMpoly qa) hYM))
      (add_mem (hMpoly pb) (mul_mem (hMpoly qb) hYM))
  -- the monic degree-`p²` relation for `tautX` over `L`
  set φL : F →+* ↥L := (constHom W).codRestrict L hconstL
  set q : Polynomial ↥L := (W.Φ (p : ℤ)).map φL -
    Polynomial.C (⟨xp, hxpL⟩ : ↥L) * (W.ΨSq (p : ℤ)).map φL with hqdef
  have hcomp : (algebraMap (↥L) W.FunctionField).comp φL = constHom W :=
    RingHom.ext fun d => rfl
  have haeval : ∀ f : Polynomial F,
      Polynomial.aeval (tautX W) (f.map φL) =
        (f.map (constHom W)).eval (tautX W) := by
    intro f
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_map,
      hcomp]
  have hΦc : (W.Φ (p : ℤ)).coeff (p ^ 2) = 1 := by
    have h1 := W.coeff_Φ (p : ℤ)
    rwa [Int.natAbs_natCast] at h1
  have hΨc : (W.ΨSq (p : ℤ)).coeff (p ^ 2) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt (W.natDegree_ΨSq_le (p : ℤ))
    rw [Int.natAbs_natCast]
    exact Nat.sub_lt (pow_pos (Fact.out : p.Prime).pos 2) one_pos
  have hqcoeff : q.coeff (p ^ 2) = 1 := by
    rw [hqdef, Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_mul,
      Polynomial.coeff_map, hΦc, hΨc, map_zero, mul_zero, sub_zero, map_one]
  have hqdegle : q.natDegree ≤ p ^ 2 := by
    rw [hqdef]
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_map_le) ?_
      have h1 := W.natDegree_Φ_le (p : ℤ)
      rwa [Int.natAbs_natCast] at h1
    · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      refine le_trans (Polynomial.natDegree_map_le) ?_
      have h1 := W.natDegree_ΨSq_le (p : ℤ)
      rw [Int.natAbs_natCast] at h1
      exact le_trans h1 (Nat.sub_le _ _)
  have hqmonic : q.Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hqdegle hqcoeff
  have hqaeval : Polynomial.aeval (tautX W) q = 0 := by
    rw [hqdef, map_sub, map_mul, haeval, haeval, Polynomial.aeval_C]
    show ((W.Φ (p : ℤ)).map (constHom W)).eval (tautX W) -
      xp * ((W.ΨSq (p : ℤ)).map (constHom W)).eval (tautX W) = 0
    linear_combination -hxrel
  have hint : IsIntegral (↥L) (tautX W) := ⟨q, hqmonic, hqaeval⟩
  have hminle : (minpoly (↥L) (tautX W)).natDegree ≤ p ^ 2 := by
    refine le_trans (Polynomial.natDegree_le_natDegree ?_) hqdegle
    exact minpoly.degree_le_of_ne_zero (↥L) (tautX W) hqmonic.ne_zero hqaeval
  have hfrM : Module.finrank (↥L) ↥M = (minpoly (↥L) (tautX W)).natDegree :=
    IntermediateField.adjoin.finrank hint
  have hfdM : FiniteDimensional (↥L) ↥M :=
    IntermediateField.adjoin.finiteDimensional hint
  rw [hMtop] at hfdM
  refine ⟨?_, ?_⟩
  · haveI := hfdM
    exact (IntermediateField.topEquiv (F := ↥L)
      (E := W.FunctionField)).toLinearEquiv.finiteDimensional
  · have hfr : Module.finrank (↥L) W.FunctionField = Module.finrank (↥L) ↥M := by
      rw [hMtop, IntermediateField.finrank_top']
    rw [hfr, hfrM]
    exact hminle

/-- **L4-5/6 Galois core (PROVEN, as is its degree sub-lemma
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
`H = {σ_κ : κ ∈ E[p]}`, assembled here from three stages (all three
now proven — the third, the degree bound, by exhibiting the generic
point as integral over the pullback field with a monic annihilator of
degree `p²` built from the division-polynomial relation, so that
`K = L(tautX)` has `finrank ≤ deg (minpoly) ≤ p²`):

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
* `[K : L] ≤ p²` (`finiteDimensional_and_finrank_le_pullback`,
  PROVEN).

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
`pointIdeal W R` of the affine points `R`.

*Update (brick 1 proven).* No Dedekind instance turned out to be needed
for the FACTORIZATION half of that story, and none is stated here (a
sorried instance would be free-floating).  `section
DedekindFactorization` above proves, outright, that every nonzero ideal
of `F[W]` is a product of point ideals at affine points
(`exists_multiset_ideal_eq_prod_pointIdeal`), by noetherian induction
(`isNoetherianRing_coordinateRing`) over the two facts that point
ideals are invertible as fractional ideals (mathlib's
`CoordinateRing.XYIdeal'`) and that the maximal ideals of `F[W]` are
exactly the point ideals (`exists_point_pointIdeal_eq`).  What that
route does NOT give — and what the two remaining bricks still need — is
UNIQUENESS of the factorization, i.e. reading off multiplicities. -/

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

omit [DecidableEq F] in
/-- **L4-7 brick (PROVEN): the affine divisor of a nonzero coordinate
function.**  Every nonzero `z ∈ F[W]` has `Ideal.span {z}` equal to a
product of point ideals at affine points — the affine part of `div z`,
`Σ_R v_R(z)·(R)`, read as a multiset of affine points.

Proof: the principal ideal `⟨z⟩` is nonzero, so
`exists_multiset_ideal_eq_prod_pointIdeal` factors it into point ideals
at affine points.  That factorization needs NO Dedekind-domain instance
for `F[W]` (the pin has none): it is a noetherian induction over ideals
whose only input beyond noetherianity (`isNoetherianRing_coordinateRing`)
is the invertibility of point ideals as fractional ideals — mathlib's
`CoordinateRing.XYIdeal'` — together with the identification of the
maximal ideals of `F[W]` with the affine points
(`exists_point_pointIdeal_eq`, which over the algebraically closed `F`
comes from `CoordinateRing.XYIdeal_neg_mul` and primality rather than
from Zariski's lemma).  The point `O` never occurs,
`pointIdeal W 0 = ⊤` being the unit ideal. -/
theorem exists_multiset_span_eq_prod_pointIdeal (hΔ : W.Δ ≠ 0)
    {z : W.CoordinateRing} (hz : z ≠ 0) :
    ∃ D : Multiset W.Point, (0 : W.Point) ∉ D ∧
      Ideal.span {z} = (D.map (pointIdeal W)).prod :=
  exists_multiset_ideal_eq_prod_pointIdeal hΔ _
    (fun h => hz (Ideal.span_singleton_eq_bot.mp h))

omit [IsAlgClosed F] in
/-- **Point ideals separate points** (PROVEN): `pointIdeal` is
injective.  Equal point ideals give equal unit fractional point ideals
(`coe_pointIdeal'`), hence equal ideal classes (`mk_pointIdeal'`), hence
equal `Point.toClass` values — and `toClass` is injective. -/
lemma pointIdeal_injective : Function.Injective (pointIdeal W) := by
  intro R S hRS
  have h2 : pointIdeal' W R = pointIdeal' W S :=
    Units.ext (by rw [coe_pointIdeal', coe_pointIdeal', hRS])
  have h3 : Additive.toMul (Point.toClass R) = Additive.toMul (Point.toClass S) := by
    rw [← mk_pointIdeal', ← mk_pointIdeal', h2]
  exact Point.toClass_injective (Additive.toMul.injective h3)

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Every affine point carries a height-one place** (PROVEN): the
point ideal of `S ≠ O` is maximal (`xyIdeal_isMaximal`), hence prime,
and nonzero — it contains the nonzero vertical
`CoordinateRing.XClass W x`. -/
lemma exists_heightOneSpectrum_pointIdeal {S : W.Point} (hS0 : S ≠ 0) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing,
      v.asIdeal = pointIdeal W S := by
  cases S with
  | zero => exact absurd rfl hS0
  | some x y h =>
    refine ⟨⟨CoordinateRing.XYIdeal W x (Polynomial.C y),
      (xyIdeal_isMaximal h.left).isPrime, ?_⟩, rfl⟩
    intro hbot
    have hmem : CoordinateRing.XClass W x ∈
        CoordinateRing.XYIdeal W x (Polynomial.C y) := by
      rw [CoordinateRing.XYIdeal]
      exact Ideal.subset_span (Set.mem_insert _ _)
    rw [hbot, Ideal.mem_bot] at hmem
    exact CoordinateRing.XClass_ne_zero x hmem

omit [IsAlgClosed F] in
/-- **The point-adic multiplicity of a unit point ideal** (PROVEN): at
the place of the affine point `S`, the unit fractional point ideal of
`Q` contributes `1` when `Q = S` and `0` otherwise —
`pointIdeal' W O = 1` contributing `0` at the origin
(`FractionalIdeal.count_one`), and an affine `Q` contributing through
`FractionalIdeal.count_maximal` once its point ideal is recognized as a
height-one place (`exists_heightOneSpectrum_pointIdeal`) and points are
separated by their ideals (`pointIdeal_injective`). -/
lemma count_coe_pointIdeal' [IsDedekindDomain W.CoordinateRing]
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing} {S : W.Point}
    (hS0 : S ≠ 0) (hvS : v.asIdeal = pointIdeal W S) (Q : W.Point)
    [Decidable (Q = S)] :
    FractionalIdeal.count W.FunctionField v
        (pointIdeal' W Q : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      if Q = S then 1 else 0 := by
  classical
  cases Q with
  | zero =>
    rw [show (pointIdeal' W (WeierstrassCurve.Affine.Point.zero : W.Point) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = 1 from by
        simp only [pointIdeal', Units.val_one],
      if_neg (fun hcon :
        (WeierstrassCurve.Affine.Point.zero : W.Point) = S => hS0 hcon.symm)]
    exact FractionalIdeal.count_one W.FunctionField v
  | some x y h =>
    obtain ⟨w, hw⟩ := exists_heightOneSpectrum_pointIdeal
      (S := (WeierstrassCurve.Affine.Point.some x y h)) (Point.some_ne_zero h)
    rw [show (pointIdeal' W (WeierstrassCurve.Affine.Point.some x y h) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
        (w.asIdeal : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) from by
        rw [coe_pointIdeal', hw],
      FractionalIdeal.count_maximal W.FunctionField v w]
    refine if_congr (Iff.intro ?_ ?_) rfl rfl
    · intro hwv
      exact pointIdeal_injective (by rw [← hw, hwv, hvS])
    · intro hQS
      exact IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr (by rw [hw, hQS, hvS])

omit [IsAlgClosed F] in
/-- **The point-adic multiplicity of a point-ideal product counts the
copies of the point** (PROVEN): multiset induction over
`count_coe_pointIdeal'`, the factors being units so that
`FractionalIdeal.count_mul` applies (`isUnit_prod_coe_pointIdeal'`). -/
lemma count_prod_coe_pointIdeal' [IsDedekindDomain W.CoordinateRing]
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing} {S : W.Point}
    (hS0 : S ≠ 0) (hvS : v.asIdeal = pointIdeal W S) (D : Multiset W.Point) :
    FractionalIdeal.count W.FunctionField v
        ((D.map fun R => (pointIdeal' W R :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) =
      (Multiset.count S D : ℤ) := by
  classical
  induction D using Multiset.induction with
  | empty => simpa using FractionalIdeal.count_one W.FunctionField v
  | cons R D ih =>
    rw [Multiset.map_cons, Multiset.prod_cons,
      FractionalIdeal.count_mul W.FunctionField v
        (pointIdeal' W R).isUnit.ne_zero
        (isUnit_prod_coe_pointIdeal' D).ne_zero,
      ih, count_coe_pointIdeal' hS0 hvS R, Multiset.count_cons]
    by_cases hRS : R = S
    · rw [if_pos hRS, if_pos hRS.symm]
      push_cast
      ring
    · rw [if_neg hRS, if_neg (fun hc : S = R => hRS hc.symm)]
      push_cast
      ring

omit [IsAlgClosed F] in
/-- **The order of a coordinate function at an affine place is its
divisor multiplicity** (PROVEN): if `z` has affine divisor `D` then its
order at the place of `S` is the number of copies of `S` in `D`
(`prod_coe_pointIdeal'_eq_spanSingleton` turns the principal span into
the point-ideal product, `count_prod_coe_pointIdeal'` counts it). -/
lemma count_spanSingleton_algebraMap [IsDedekindDomain W.CoordinateRing]
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing} {S : W.Point}
    (hS0 : S ≠ 0) (hvS : v.asIdeal = pointIdeal W S)
    {z : W.CoordinateRing} {D : Multiset W.Point}
    (hD : Ideal.span {z} = (D.map (pointIdeal W)).prod) :
    FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField z)) =
      (Multiset.count S D : ℤ) := by
  rw [← prod_coe_pointIdeal'_eq_spanSingleton hD,
    count_prod_coe_pointIdeal' hS0 hvS]

/-! ### Univariate classes and their local multiplicities

The `[p]`-pullback of a vertical is, by the division-polynomial
relation `xp·ΨSq_p(x) = Φ_p(x)` of `exists_smul_tautPoint_eq`, a
QUOTIENT OF TWO UNIVARIATE POLYNOMIALS evaluated at the tautological
`x`.  The bricks below turn that observation into a computation: the
class `polyClass W g = g(X) ∈ F[W]` of a univariate `g`, its order at
an affine place (`rootMultiplicity` times the ramification `1` or `2`
of `x` at the place), and the dictionary between the point-side data
(`S = ⊖S`, `p • S = P`) and the polynomial-side data (`Ψ₂Sq(a) = 0`,
`Φ_p(a) = x·ΨSq_p(a)`).  What is left after all of this is a single
statement about polynomials — the leaf
`rootMultiplicity_Φ_sub_C_mul_ΨSq` below. -/

/-- The class of a univariate polynomial `g(X)` in the coordinate ring
(so `polyClass W (X − x) = CoordinateRing.XClass W x`). -/
noncomputable def polyClass (W : WeierstrassCurve.Affine F) (g : Polynomial F) :
    W.CoordinateRing :=
  CoordinateRing.mk W (Polynomial.C g)

omit [DecidableEq F] [IsAlgClosed F] in
/-- A vertical is the class of a linear polynomial. -/
lemma polyClass_X_sub_C (x : F) :
    polyClass W (Polynomial.X - Polynomial.C x) = CoordinateRing.XClass W x := rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- `polyClass` is multiplicative (it is a ring hom `F[X] → F[W]`). -/
lemma polyClass_mul (g h : Polynomial F) :
    polyClass W (g * h) = polyClass W g * polyClass W h := by
  simp only [polyClass, map_mul]

omit [DecidableEq F] [IsAlgClosed F] in
/-- The class of a constant is the constant of the coordinate ring. -/
lemma polyClass_C (c : F) : polyClass W (Polynomial.C c) = coordC W c := rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- In the function field, `polyClass W g` is `g` evaluated at the
tautological `x`-coordinate. -/
lemma algebraMap_polyClass (g : Polynomial F) :
    algebraMap W.CoordinateRing W.FunctionField (polyClass W g) =
      (g.map (constHom W)).eval (tautX W) := by
  have h : ((algebraMap W.CoordinateRing W.FunctionField).comp
        ((CoordinateRing.mk W).comp (Polynomial.C (R := Polynomial F)))) =
      Polynomial.eval₂RingHom (constHom W) (tautX W) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact algebraMap_coordC a
    · simp only [RingHom.coe_comp, Function.comp_apply,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      exact algebraMap_coordX
  have h2 := RingHom.congr_fun h g
  simp only [RingHom.coe_comp, Function.comp_apply,
    Polynomial.coe_eval₂RingHom] at h2
  rw [Polynomial.eval_map]
  exact h2

omit [DecidableEq F] in
/-- A nonzero univariate polynomial has nonzero class: the tautological
`x` is transcendental over the constants
(`eval_map_ne_zero_of_forall_ne_constHom`). -/
lemma polyClass_ne_zero {g : Polynomial F} (hg : g ≠ 0) : polyClass W g ≠ 0 := by
  intro h0
  refine eval_map_ne_zero_of_forall_ne_constHom (tautX_ne_constHom (W := W)) hg ?_
  rw [← algebraMap_polyClass, h0, map_zero]

omit [DecidableEq F] [IsAlgClosed F] in
/-- `pointEval` on a univariate class is evaluation of the polynomial
at the point's `x`-coordinate. -/
lemma pointEval_polyClass {K' : Type*} [Field K'] (φ : F →+* K') {x₀ y₀ : K'}
    (h : ((W.map φ).toAffine).Equation x₀ y₀) (g : Polynomial F) :
    pointEval φ h (polyClass W g) = (g.map φ).eval x₀ :=
  pointEval_ofPoly φ h g

/-- **The order of a vertical at an affine place** (PROVEN): at the
place of `S = (a, b)`, the vertical `X − α` has order `0` unless
`α = a`, in which case it has order `1`, or `2` when `S` is
`2`-torsion — the ramification of `x : E → P¹` at `S`.  The divisor of
`X − α` is `(A) + (⊖A)` for any point `A` above `α`
(`CoordinateRing.XYIdeal_neg_mul`), and `count_spanSingleton_algebraMap`
counts the copies of `S` in it. -/
lemma count_spanSingleton_XClass [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) {a b : F} (hab : W.Nonsingular a b)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W (.some a b hab)) (α : F) :
    FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField
            (CoordinateRing.XClass W α))) =
      if α = a then
        (if (Point.some a b hab : W.Point) = -(Point.some a b hab) then 2 else 1)
      else 0 := by
  classical
  obtain ⟨β, hβeq⟩ := exists_equation W α
  have hβ : W.Nonsingular α β :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hβeq
  have hS0 : (Point.some a b hab : W.Point) ≠ 0 := Point.some_ne_zero hab
  have hD : Ideal.span {CoordinateRing.XClass W α} =
      (((Point.some α β hβ : W.Point) ::ₘ
        (-(Point.some α β hβ) : W.Point) ::ₘ 0).map (pointIdeal W)).prod := by
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, Multiset.map_zero, Multiset.prod_zero, mul_one,
      Point.neg_some, pointIdeal_some, pointIdeal_some, mul_comm,
      CoordinateRing.XYIdeal_neg_mul hβ]
    rfl
  rw [count_spanSingleton_algebraMap hS0 hvS hD]
  simp only [Multiset.count_cons, Multiset.count_zero, zero_add]
  by_cases hα : α = a
  · subst hα
    rw [if_pos rfl]
    have hchoice : (Point.some α b hab : W.Point) = Point.some α β hβ ∨
        (Point.some α b hab : W.Point) = -(Point.some α β hβ) := by
      rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hab.1 hβ.1 rfl with hy | hy
      · left; subst hy; rfl
      · right
        rw [Point.neg_some]
        subst hy
        rfl
    rcases hchoice with hc | hc
    · rw [hc, if_pos rfl]
      by_cases hneg : (Point.some α β hβ : W.Point) = -(Point.some α β hβ)
      · rw [if_pos hneg, if_pos hneg]
        norm_num
      · rw [if_neg hneg, if_neg hneg]
        norm_num
    · rw [hc, neg_neg, if_pos rfl]
      by_cases hneg : (-(Point.some α β hβ) : W.Point) = Point.some α β hβ
      · rw [if_pos hneg, if_pos hneg]
        norm_num
      · rw [if_neg hneg, if_neg hneg]
        norm_num
  · have h1 : ¬ ((Point.some a b hab : W.Point) = Point.some α β hβ) := by
      intro hcon
      injection hcon with hx _
      exact hα hx.symm
    have h2 : ¬ ((Point.some a b hab : W.Point) = -(Point.some α β hβ)) := by
      rw [Point.neg_some]
      intro hcon
      injection hcon with hx _
      exact hα hx.symm
    rw [if_neg hα, if_neg h1, if_neg h2]
    norm_num

/-- **The order of a univariate class at an affine place** (PROVEN):
`ord_S(g(x)) = mult_a(g) · e`, where `a = x(S)` and `e ∈ {1, 2}` is the
ramification of `x` at `S`.  Strong induction on `deg g`, splitting off
a linear factor at a time (`IsAlgClosed.exists_root`,
`Polynomial.dvd_iff_isRoot`) over `count_spanSingleton_XClass`. -/
lemma count_spanSingleton_polyClass [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) {a b : F} (hab : W.Nonsingular a b)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W (.some a b hab))
    {g : Polynomial F} (hg : g ≠ 0) :
    FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField (polyClass W g))) =
      (g.rootMultiplicity a : ℤ) *
        (if (Point.some a b hab : W.Point) = -(Point.some a b hab)
          then 2 else 1) := by
  classical
  have hspan0 : ∀ q : Polynomial F, q ≠ 0 →
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField (polyClass W q)) ≠ 0 := by
    intro q hq
    refine (isUnit_spanSingleton_of_ne_zero ?_).ne_zero
    intro h0
    exact polyClass_ne_zero hq
      ((injective_iff_map_eq_zero _).mp
        (FaithfulSMul.algebraMap_injective W.CoordinateRing W.FunctionField) _ h0)
  suffices H : ∀ (n : ℕ) (q : Polynomial F), q.natDegree = n → q ≠ 0 →
      FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField (polyClass W q))) =
        (q.rootMultiplicity a : ℤ) *
          (if (Point.some a b hab : W.Point) = -(Point.some a b hab)
            then 2 else 1) by
    exact H g.natDegree g rfl hg
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro q hdeg hq
  by_cases h0 : q.natDegree = 0
  · have hqc : q = Polynomial.C (q.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero h0
    have hc0 : q.coeff 0 ≠ 0 := by
      intro hc
      rw [hc, map_zero] at hqc
      exact hq hqc
    have htop : Ideal.span {polyClass W q} =
        (((0 : Multiset W.Point)).map (pointIdeal W)).prod := by
      rw [Multiset.map_zero, Multiset.prod_zero, Ideal.one_eq_top]
      refine Ideal.span_singleton_eq_top.mpr ?_
      rw [hqc, polyClass_C]
      exact isUnit_coordC hc0
    rw [count_spanSingleton_algebraMap (Point.some_ne_zero hab) hvS htop]
    have hrm : q.rootMultiplicity a = 0 := by
      refine Polynomial.rootMultiplicity_eq_zero ?_
      intro hroot
      apply hc0
      have hval := hroot
      rw [Polynomial.IsRoot.def, hqc, Polynomial.eval_C] at hval
      exact hval
    rw [hrm]
    simp
  · obtain ⟨α, hα⟩ := IsAlgClosed.exists_root q
      (by rw [Polynomial.degree_eq_natDegree hq]; exact_mod_cast h0)
    obtain ⟨q', rfl⟩ := (Polynomial.dvd_iff_isRoot).mpr hα
    have hq' : q' ≠ 0 := by
      intro hc
      rw [hc, mul_zero] at hq
      exact hq rfl
    have hXne : (Polynomial.X - Polynomial.C α : Polynomial F) ≠ 0 :=
      Polynomial.X_sub_C_ne_zero α
    have hdeg' : q'.natDegree < n := by
      rw [← hdeg, Polynomial.natDegree_mul hXne hq', Polynomial.natDegree_X_sub_C]
      omega
    have hsplit :
        FractionalIdeal.count W.FunctionField v
          (FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (algebraMap W.CoordinateRing W.FunctionField
              (polyClass W ((Polynomial.X - Polynomial.C α) * q')))) =
        FractionalIdeal.count W.FunctionField v
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField
                (polyClass W (Polynomial.X - Polynomial.C α)))) +
          FractionalIdeal.count W.FunctionField v
            (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (algebraMap W.CoordinateRing W.FunctionField (polyClass W q'))) := by
      rw [polyClass_mul, map_mul,
        ← FractionalIdeal.spanSingleton_mul_spanSingleton,
        FractionalIdeal.count_mul W.FunctionField v (hspan0 _ hXne)
          (hspan0 _ hq')]
    rw [hsplit, IH q'.natDegree hdeg' q' rfl hq', polyClass_X_sub_C,
      count_spanSingleton_XClass hΔ hab hvS α,
      Polynomial.rootMultiplicity_mul (by exact mul_ne_zero hXne hq')]
    by_cases hαa : α = a
    · subst hαa
      rw [if_pos rfl, Polynomial.rootMultiplicity_X_sub_C_self]
      push_cast
      ring
    · have hrm0 : Polynomial.rootMultiplicity a
          (Polynomial.X - Polynomial.C α) = 0 := by
        refine Polynomial.rootMultiplicity_eq_zero ?_
        intro hroot
        rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C, sub_eq_zero] at hroot
        exact hαa hroot.symm
      rw [if_neg hαa, hrm0]
      push_cast
      ring

omit [DecidableEq F] [IsAlgClosed F] in
/-- **`negY` fixes `y` exactly at a root of `Ψ₂Sq`** (PROVEN): on the
curve `Ψ₂Sq(x) = (2y + a₁x + a₃)²` (`TorsionCard.eval_Ψ₂Sq_eq_sq`). -/
lemma negY_eq_self_iff {x y : F} (heq : W.Equation x y) :
    W.negY x y = y ↔ W.Ψ₂Sq.eval x = 0 := by
  have hsq : W.Ψ₂Sq.eval x = (2 * y + (W.a₁ * x + W.a₃)) ^ 2 :=
    TorsionCard.eval_Ψ₂Sq_eq_sq W heq
  rw [hsq, pow_eq_zero_iff two_ne_zero, WeierstrassCurve.Affine.negY]
  constructor
  · intro hh; linear_combination -hh
  · intro hh; linear_combination -hh

omit [IsAlgClosed F] in
/-- **A point is its own negative exactly over a root of `Ψ₂Sq`**
(PROVEN): `P = ⊖P` iff `2 • P = 0` iff `Ψ₂Sq(x_P) = 0`
(`TorsionCard.two_smul_some_eq_zero_iff`). -/
lemma point_eq_neg_iff_Ψ₂Sq {a b : F} (hab : W.Nonsingular a b) :
    ((Point.some a b hab : W.Point) = -(Point.some a b hab)) ↔
      W.Ψ₂Sq.eval a = 0 := by
  have key : ((2 : ℤ) • (Point.some a b hab : W.Point) = 0) ↔
      W.Ψ₂Sq.eval a = 0 := TorsionCard.two_smul_some_eq_zero_iff W hab
  rw [← key, two_zsmul, add_eq_zero_iff_eq_neg]

omit [IsAlgClosed F] in
/-- **The point-side multiplicity in polynomial terms** (PROVEN): with
`S = (a, b)` and `ΨSq_p(a) ≠ 0`, the multiplicity of `p • S` in the
divisor `(P) + (⊖P)` of the vertical at `P = (x, y)` is `0` unless
`x(p • S) = x`, i.e. `Φ_p(a) = x·ΨSq_p(a)`
(`TorsionCard.exists_smul_some_eq`), in which case it is the
ramification `1` or `2` of `x` at `P`, i.e. `2` exactly when
`Ψ₂Sq(x) = 0`. -/
lemma count_smul_pair_eq (hΔ : W.Δ ≠ 0) {a b : F} (hab : W.Nonsingular a b)
    (hΨ : ((W.ΨSq (p : ℤ)).eval a) ≠ 0) {x y : F} (h : W.Nonsingular x y) :
    (Multiset.count ((p : ℤ) • (Point.some a b hab : W.Point))
        ((Point.some x y h : W.Point) ::ₘ
          (-(Point.some x y h) : W.Point) ::ₘ 0) : ℤ) =
      if (W.Φ (p : ℤ)).eval a = x * (W.ΨSq (p : ℤ)).eval a then
        (if W.Ψ₂Sq.eval x = 0 then 2 else 1) else 0 := by
  classical
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hpZ : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨x', y', hns0, heq0, hx'0⟩ :=
    TorsionCard.exists_smul_some_eq W hpZ hab hΨ
  have h' : W.Nonsingular x' y' := hns0
  have heq : ((p : ℤ) • (Point.some a b hab : W.Point)) =
      Point.some x' y' h' := heq0
  have hx' : x' * (W.ΨSq (p : ℤ)).eval a = (W.Φ (p : ℤ)).eval a := hx'0
  rw [heq]
  simp only [Multiset.count_cons, Multiset.count_zero, zero_add]
  by_cases hxx : x' = x
  · have hcond : (W.Φ (p : ℤ)).eval a = x * (W.ΨSq (p : ℤ)).eval a := by
      rw [← hx', hxx]
    have hEq1 : ((Point.some x' y' h' : W.Point) = Point.some x y h) ↔
        y' = y := by
      constructor
      · intro hh
        injection hh with _ hy2
      · intro hy2
        subst hxx
        subst hy2
        rfl
    have hEq2 : ((Point.some x' y' h' : W.Point) = -(Point.some x y h)) ↔
        y' = W.negY x y := by
      rw [Point.neg_some]
      constructor
      · intro hh
        injection hh with _ hy2
      · intro hy2
        subst hxx
        subst hy2
        rfl
    rw [if_pos hcond, if_congr hEq1 rfl rfl, if_congr hEq2 rfl rfl]
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 h.1 hxx with hy | hy
    · rw [hy, if_pos rfl]
      by_cases hz : W.Ψ₂Sq.eval x = 0
      · rw [if_pos ((negY_eq_self_iff h.1).mpr hz).symm, if_pos hz]
        norm_num
      · rw [if_neg (fun hc => hz ((negY_eq_self_iff h.1).mp hc.symm)),
          if_neg hz]
        norm_num
    · rw [hy, if_pos rfl]
      by_cases hz : W.Ψ₂Sq.eval x = 0
      · rw [if_pos ((negY_eq_self_iff h.1).mpr hz), if_pos hz]
        norm_num
      · rw [if_neg (fun hc => hz ((negY_eq_self_iff h.1).mp hc)), if_neg hz]
        norm_num
  · have hcond : ¬((W.Φ (p : ℤ)).eval a = x * (W.ΨSq (p : ℤ)).eval a) := by
      intro hc
      refine hxx (mul_right_cancel₀ hΨ ?_)
      rw [hx', hc]
    have hne1 : ¬((Point.some x' y' h' : W.Point) = Point.some x y h) := by
      intro hh
      injection hh with hx2 _
      exact hxx hx2
    have hne2 : ¬((Point.some x' y' h' : W.Point) = -(Point.some x y h)) := by
      rw [Point.neg_some]
      intro hh
      injection hh with hx2 _
      exact hxx hx2
    rw [if_neg hcond, if_neg hne1, if_neg hne2]
    norm_num

omit [DecidableEq F] [IsAlgClosed F] in
/-- **`Φ_p − c·ΨSq_p` is nonzero** (PROVEN): its coefficient in degree
`p²` is `1`, because `Φ_p` is monic of degree `p²` (`coeff_Φ`) while
`ΨSq_p` has degree `≤ p² − 1` (`natDegree_ΨSq_le`). -/
lemma Φ_sub_C_mul_ΨSq_ne_zero (c : F) :
    W.Φ (p : ℤ) - Polynomial.C c * W.ΨSq (p : ℤ) ≠ 0 := by
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

/-- **L4-7 LEAF (sorry): multiplicity one for `[p]`, in `x`-coordinates
only.**  This is the entire remaining geometric content of the L4-7
stage, isolated as a statement about POLYNOMIALS: no function field, no
ideals, no divisors.

Fix `a` with `ΨSq_p(a) ≠ 0` (i.e. `p • S ≠ O` for the points `S` above
`a`) and any `x`.  Then the multiplicity of `a` as a root of
`G := Φ_p − x·ΨSq_p` is `0` when `a` is not a root at all, and
otherwise exactly `d_P / d_S`, where `d_S = 2` or `1` according as
`Ψ₂Sq(a) = 0` or not (the ramification of `x : E → P¹` at `S`), and
likewise `d_P` at `x`:

`mult_a(Φ_p − x·ΨSq_p) · d_S = if Φ_p(a) = x·ΨSq_p(a) then d_P else 0`.

Equivalently: `x ∘ [p] − x` has a zero of order exactly `d_P` at every
point of the fiber — the SEPARABILITY of `[p]` for `(p : F) ≠ 0`, in
the only form the descent needs.

**A route (found 2026-07-25, and it is much shorter than the two routes
recorded at `count_pointEval_of_smul_ne_zero`).**  Everything follows
from ONE polynomial identity, the algebraic form of `[p]^*ω = p·ω`.
Write `W := Φ_p'·ΨSq_p − Φ_p·ΨSq_p'` for the Wronskian and
`Ñ := 4Φ_p³ + b₂Φ_p²ΨSq_p + 2b₄Φ_pΨSq_p² + b₆ΨSq_p³`.  The identity is

`(★)  W² · Ψ₂Sq = p² · ΨSq_p · Ñ`,

i.e. `f'(X)²·Ψ₂Sq(X) = p²·Ψ₂Sq(f(X))` for `f = Φ_p/ΨSq_p`, which is
exactly `d(x∘[p])/(2y∘[p] + …) = p·dx/(2y + …)`.

Given `(★)`, the leaf is a two-line order count.  Put
`G = Φ_p − x·ΨSq_p`, `m = mult_a(G)`, `j = mult_a(Ψ₂Sq)`,
`k = mult_x(Ψ₂Sq)`.  Since `Φ_p = G + x·ΨSq_p`,

`Ñ = ΨSq_p³·Ψ₂Sq(x) + G·ΨSq_p²·Ψ₂Sq'(x) + G²·(…)`,

and `ΨSq_p(a) ≠ 0`, so `ord_a(Ñ) = 0` when `k = 0` and `ord_a(Ñ) = m`
when `k = 1`.  Also `W = G'·ΨSq_p − G·ΨSq_p'`, whence
`ord_a(W) ≥ m − 1`.  Reading `(★)` at `a` gives `2·ord_a(W) + j =
ord_a(Ñ)`, and the four cases `j, k ∈ {0, 1}` give `m·(j+1) = k+1`
exactly — including the impossible combination `j = 1, k = 0`
(a `2`-torsion `S` over a non-`2`-torsion `p • S`), which the identity
rules out.  `Ψ₂Sq` is squarefree — so `j, k ≤ 1` — whenever
`2 ≠ 0` (`TorsionCard.separable_Ψ₂Sq`).

**Two things are still open in that route**, and they are the honest
statement of what this leaf costs:

* `(★)` itself.  It is a universal identity in `ℤ[a₁, …, a₆][X]`, so it
  is a candidate for a Gröbner/`Singular` certificate at small `p` but
  needs an argument for general `p`.  The clean derivation is through a
  derivation `D` of `K = Frac F[W]` with `D x = ψ₂`,
  `D y = 3x² + 2a₂x + a₄ − a₁y`, for which mathlib's missing
  quotient/fraction-field `Derivation` API can be SIDESTEPPED: such a
  `D` is the same thing as an `F`-algebra map
  `F[W] → TrivSqZeroExt K K` sending `x ↦ (x, ψ₂)`,
  `y ↦ (y, 3x²+2a₂x+a₄−a₁y)`, which is an `AdjoinRoot.lift` (the
  defining polynomial maps to `0` because `f_X·f_Y − f_Y·f_X = 0`),
  extended to `K` by `IsLocalization.lift` (nonzero elements go to
  units of `K[ε]`).  Then `μ(P) := D(x_P)/(2y_P + a₁x_P + a₃)` is
  ADDITIVE on `(curveK W).Point` — an identity in the group-law
  formulas, structurally like the proven `endoMap_add`, and a good
  target for a `Singular`-computed `linear_combination` — so
  `μ(p • taut) = p·μ(taut) = p` by `AddMonoidHom.map_zsmul`, which is
  `(★)` evaluated at the (transcendental) tautological `x`.
* Characteristic `2`.  There `Ψ₂Sq = (a₁X + a₃)²` is not squarefree, so
  `k` can be `2`, and the case `j = 0, k = 2` (an `S` that is not
  `2`-torsion over a `2`-torsion `p • S`) is NOT decided by `(★)`: the
  identity degenerates to `W·(a₁X+a₃) = p·a₁·ΨSq_p·G`, which only says
  `2 ∣ m`.  Settling it needs the fiber count `#E[p] = p²` (with
  `deg G = p²` and `mult ≥ 2` at each of the `(p²−1)/2` non-`2`-torsion
  abscissae, equality is forced), or another idea. -/
theorem rootMultiplicity_Φ_sub_C_mul_ΨSq (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {a x : F} (hΨ : ((W.ΨSq (p : ℤ)).eval a) ≠ 0) :
    ((W.Φ (p : ℤ) - Polynomial.C x * W.ΨSq (p : ℤ)).rootMultiplicity a : ℤ) *
        (if W.Ψ₂Sq.eval a = 0 then 2 else 1) =
      if (W.Φ (p : ℤ)).eval a = x * (W.ΨSq (p : ℤ)).eval a then
        (if W.Ψ₂Sq.eval x = 0 then 2 else 1) else 0 := by
  sorry

/-- **L4-7 (PROVEN over `rootMultiplicity_Φ_sub_C_mul_ΨSq`): the
`[p]`-pullback of a VERTICAL, at an affine
place lying over an affine point.**  With `(xp, yp)` the affine
coordinates of the generic multiple `p • taut` — so that
`pointEval (constHom W) hpn.left` is the pullback `z ↦ z ∘ [p]` — and
`S ≠ O` an affine point with `T := p • S ≠ O`, the order at the place
of `S` of the pulled-back vertical `x ∘ [p] − x_P` is the multiplicity
of `T` in the affine divisor `(P) + (⊖P)` of `X − x_P`:

`ord_S(x ∘ [p] − x_P) = mult_T ((P) + (⊖P))`.

This is the `[p]`-analogue of the PROVEN translation brick
`spanSingleton_pointEval_XClass`, in the local `count` form rather than
the global fractional-ideal form (at a place over an AFFINE point there
is no `(O)`-correction to carry, which is why the two branches of
`count_pointEval_of_*` are stated separately).

**PROOF (2026-07-25).**  By `exists_smul_tautPoint_eq` the
`x`-coordinate of `p • taut` satisfies the division-polynomial relation
`xp · ΨSq_p(x) = Φ_p(x)`, so

`x ∘ [p] − x_P = (Φ_p − x_P·ΨSq_p)(x) / ΨSq_p(x)`,

a quotient of two univariate classes (`polyClass`) — whence
`ord_S` of it is the difference of their orders
(`FractionalIdeal.count_mul`).  Each of those is
`mult_a(g) · d_S` by `count_spanSingleton_polyClass`, with
`d_S ∈ {1, 2}` the ramification of `x` at `S = (a, b)`; the denominator
contributes `0` because `ΨSq_p(a) ≠ 0`, which holds because `p • S ≠ O`
(`TorsionCard.smul_some_eq_zero_iff`).  The right-hand side is
translated into the same polynomial language by `count_smul_pair_eq`
and `point_eq_neg_iff_Ψ₂Sq`, and what is left is exactly the leaf
`rootMultiplicity_Φ_sub_C_mul_ΨSq` — the multiplicity-one statement
for `[p]` in `x`-coordinates, i.e. the separability of `[p]` for
`(p : F) ≠ 0`. -/
theorem count_pointEval_XClass_of_smul_ne_zero
    [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {x y : F} (h : W.Nonsingular x y)
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S) :
    FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left (CoordinateRing.XClass W x))) =
      (Multiset.count ((p : ℤ) • S)
        (WeierstrassCurve.Affine.Point.some x y h ::ₘ
          (-WeierstrassCurve.Affine.Point.some x y h : W.Point) ::ₘ 0) : ℤ) := by
  classical
  obtain ⟨xp', yp', hpn', hptaut', hxrel⟩ :=
    exists_smul_tautPoint_eq (W := W) hΔ hp
  have hxx : xp = xp' := by
    have hpts := hptaut.symm.trans hptaut'
    injection hpts with hx _
  subst hxx
  cases S with
  | zero => exact absurd rfl hS0
  | some a b hab =>
  have hpZ : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpF : ((p : ℤ) : F) ≠ 0 := by exact_mod_cast hp
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hΨiff : (((p : ℤ) • (Point.some a b hab : W.Point)) = 0) ↔
      (W.ΨSq (p : ℤ)).eval a = 0 :=
    TorsionCard.smul_some_eq_zero_iff W hpZ hab
  have hΨa : ((W.ΨSq (p : ℤ)).eval a) ≠ 0 := fun hc => hpS (hΨiff.mpr hc)
  have hτX : pointEval (constHom W) hpn.left (CoordinateRing.XClass W x) =
      xp - constHom W x := by
    rw [XClass_eq, map_sub]
    simp only [coordX, coordC]
    rw [pointEval_X, pointEval_C]
  have hGne : W.Φ (p : ℤ) - Polynomial.C x * W.ΨSq (p : ℤ) ≠ 0 :=
    Φ_sub_C_mul_ΨSq_ne_zero x
  have hΨne : W.ΨSq (p : ℤ) ≠ 0 := W.ΨSq_ne_zero hpF
  have hrel : (xp - constHom W x) *
      algebraMap W.CoordinateRing W.FunctionField
        (polyClass W (W.ΨSq (p : ℤ))) =
      algebraMap W.CoordinateRing W.FunctionField
        (polyClass W (W.Φ (p : ℤ) - Polynomial.C x * W.ΨSq (p : ℤ))) := by
    rw [algebraMap_polyClass, algebraMap_polyClass, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination hxrel
  have hxpne : xp - constHom W x ≠ 0 :=
    sub_ne_zero.mpr (smul_taut_xCoord_ne_constHom hxrel x)
  have hspanne : ∀ z : W.FunctionField, z ≠ 0 →
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ z ≠ 0 :=
    fun z hz => (isUnit_spanSingleton_of_ne_zero hz).ne_zero
  have halgne : ∀ q : Polynomial F, q ≠ 0 →
      algebraMap W.CoordinateRing W.FunctionField (polyClass W q) ≠ 0 := by
    intro q hq h0
    exact polyClass_ne_zero hq
      ((injective_iff_map_eq_zero _).mp
        (FaithfulSMul.algebraMap_injective W.CoordinateRing W.FunctionField) _ h0)
  have hcount : FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (xp - constHom W x)) +
      FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField
            (polyClass W (W.ΨSq (p : ℤ))))) =
      FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField
            (polyClass W (W.Φ (p : ℤ) - Polynomial.C x * W.ΨSq (p : ℤ))))) := by
    rw [← FractionalIdeal.count_mul W.FunctionField v (hspanne _ hxpne)
        (hspanne _ (halgne _ hΨne)),
      FractionalIdeal.spanSingleton_mul_spanSingleton, hrel]
  have hrm2 : (W.ΨSq (p : ℤ)).rootMultiplicity a = 0 :=
    Polynomial.rootMultiplicity_eq_zero (by simpa using hΨa)
  rw [count_spanSingleton_polyClass hΔ hab hvS hΨne, hrm2,
    count_spanSingleton_polyClass hΔ hab hvS hGne] at hcount
  rw [hτX]
  have hfinal : FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (xp - constHom W x)) =
      ((W.Φ (p : ℤ) - Polynomial.C x * W.ΨSq (p : ℤ)).rootMultiplicity a : ℤ) *
        (if (Point.some a b hab : W.Point) = -(Point.some a b hab)
          then 2 else 1) := by
    rw [← hcount]
    push_cast
    ring
  rw [hfinal, if_congr (point_eq_neg_iff_Ψ₂Sq hab) rfl rfl,
    rootMultiplicity_Φ_sub_C_mul_ΨSq hΔ hp hΨa,
    count_smul_pair_eq hΔ hab hΨa h]

/-- **L4-7 leaf (sorry): the `[p]`-pullback of a LINE, at an affine
place lying over an affine point.**  Same setup as
`count_pointEval_XClass_of_smul_ne_zero`, for the line class
`Y − (ℓ(X − x₁) + y₁)` through the pair `P₁ = (x₁, y₁)`,
`P₂ = (x₂, y₂)` at the group-law slope `ℓ`.  Its affine divisor is
`(P₁) + (P₂) + (⊖(P₁ ⊕ P₂))`, and the claim is that the pullback has,
at the place of `S`, the multiplicity that the line itself has at
`T = p • S`:

`ord_S(ℓ ∘ [p]) = mult_T ((P₁) + (P₂) + (⊖(P₁ ⊕ P₂)))`.

This is the `[p]`-analogue of the PROVEN translation brick
`spanSingleton_pointEval_YClass`.  Together with
`count_pointEval_XClass_of_smul_ne_zero` it carries the whole of
`count_pointEval_of_smul_ne_zero`, whose proof is the Miller-style
pair-peeling induction over exactly these two bricks (already written
and PROVEN below, over these two leaves).

**State of play (2026-07-25): the vertical brick above is now PROVEN
over a purely polynomial leaf, and this one reduces to it up to ONE
missing ingredient.**  The reduction, worked out but not formalized:

*The norm identity.*  Let `ι = involHom W` be the hyperelliptic
involution and `L` the line class.  Then `L·ι L` is a product of three
verticals (mathlib's `CoordinateRing.YClass_mul` /
`lineNumerator_mul_lineNumeratorNeg` here), i.e. a `polyClass`.
Applying the ring hom `[p]^*` and `FractionalIdeal.count_mul`,

`ord_S([p]^*L) + ord_S([p]^*(ι L)) = Σ_{i=1,2,3} ord_S([p]^*(X − x_i))`,

and every term on the right is computed by
`count_pointEval_XClass_of_smul_ne_zero`.  Moreover
`[p]^* ∘ ι = ` evaluation at `⊖(p • taut) = (−p) • taut`, whose
`x`-coordinate is again `xp`, so the SAME vertical brick computes the
`ι`-side; writing `T = p • S`, the right-hand side is
`mult_T(D) + mult_{⊖T}(D)` for `D = (P₁) + (P₂) + (⊖(P₁⊕P₂))`.

*What the identity alone settles.*  Together with
`ord_S([p]^*z) ≥ 0` and the CENTER statement
`ord_S([p]^*z) > 0 ↔ z ∈ pointIdeal T`, it settles every case:
if `T ∉ D` or `⊖T ∉ D` one of the two terms vanishes and the other is
the required multiplicity; and `T ≠ ⊖T` with both `T, ⊖T ∈ D` is
IMPOSSIBLE here (each of the six combinations forces `P₁ = O`,
`P₂ = O`, or the excluded `P₂ = ⊖P₁` of `hxy`).  In the one remaining
case — `T` `2`-torsion and `T ∈ D` — the same enumeration gives
`mult_T(D) = 1`, so the identity reads `A + A' = 2` with `A, A' ≥ 1`,
forcing `A = 1`.  So only POSITIVITY is needed there, not the full
center.

*The missing ingredient is the center, and it is exactly the statement
that the `y`-coordinate of `p • taut` specializes correctly*: the
vertical brick pins `x(p • taut) ↦ x_T` at the place of `S`, which only
determines the center up to `T ↔ ⊖T`.  Every quantity computable from
`polyClass` data is `ι`-symmetric, so the ambiguity cannot be resolved
that way (concretely `w = yp − y_T` and `w̄ = yp − y(⊖T)` differ by the
constant `ψ₂(T)`, and `w·w̄` and `w + w̄` are both computable while
neither singles out `w`).  What is needed is `ord_S(yp − y_T) ≥ 1`,
i.e. a `y`-coordinate multiplication formula — `TorsionCard` supplies
only the `x`-relation `x' · ΨSq_p(a) = Φ_p(a)`.  Alternatively, center
propagates along translations (`spanSingleton_pointEval_translate` and
`[p] ∘ τ_Q = τ_{p•Q} ∘ [p]`), so it suffices at ONE point `S₀` — and it
is automatic at any `S₀` with `p • S₀` `2`-torsion, where `T = ⊖T`;
that needs a nonzero `2`-torsion point in the image of `[p]`
(`TorsionCard.smul_surjective`, and note there is no nonzero
`2`-torsion at all when `char F = 2` and `a₁ = 0`).

*A concrete proof of the center when `2 ≠ 0` in `F`* (worked out, not
formalized): `TorsionCard.zsmul_some_aux_strong` tracks not only the
`x`-coordinate but the `ψ₂`-value,
`(2y' + a₁x' + a₃)·ψ_p(x, y)⁴ = ψ_{2p}(x, y)`, whenever the base point
is not `2`-torsion.  Both `ψ_p` and `ψ_{2p}` are BIVARIATE polynomials,
so `ψ_n(taut)` is `algebraMap (CoordinateRing.mk W (W.ψ n))` and
`ψ_n(taut) − ψ_n(S)` lies in `pointIdeal S`
(`mem_pointIdeal_of_coordEval_eq_zero`), i.e. has `ord_S ≥ 1`; since
`ψ_p(S) ≠ 0` (as `p • S ≠ O`) the same holds after dividing, giving
`ord_S(ψ₂(p • taut) − ψ₂(p • S)) ≥ 1`.  Subtracting `a₁·(xp − x_T)`,
whose order is `≥ 1` by the vertical brick, leaves
`ord_S(2·(yp − y_T)) ≥ 1`, hence `ord_S(yp − y_T) ≥ 1` when `2 ≠ 0`.
For a `2`-torsion `S` (where `zsmul_some_aux_strong` does not apply)
one has `p • S = S` for odd `p`, so `T = ⊖T`, and the curve-equation
identity `(yp − y_T)² = (xp − x_T)·(xp² + xp x_T + x_T² + a₂(xp + x_T)
+ a₄ − a₁ yp)` gives `2·ord_S(yp − y_T) ≥ 1` directly.  What this
argument does NOT cover is `char F = 2`, where `ψ₂ = a₁x + a₃` carries
no `y`-information at all — the same characteristic that blocks the
last case of `rootMultiplicity_Φ_sub_C_mul_ΨSq`. -/
theorem count_pointEval_YClass_of_smul_ne_zero
    [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {x₁ y₁ x₂ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂))
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S) :
    FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left
            (CoordinateRing.YClass W
              (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))))) =
      (Multiset.count ((p : ℤ) • S)
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ ::ₘ
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ ::ₘ
          (-(WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
            WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) : W.Point) ::ₘ 0) : ℤ) := by
  sorry

/-- **L4-7: the `[p]`-pullback is unramified over an affine
point** (PROVEN over the two bricks
`count_pointEval_XClass_of_smul_ne_zero` /
`count_pointEval_YClass_of_smul_ne_zero`).
Let `(xp, yp)` be the affine coordinates of the generic
multiple `p • taut`, so that `[p]^* = pointEval (constHom W) hpn.left`
realizes `z ↦ z ∘ [p]` on `F[W]` with values in `K = Frac F[W]`.  For an
affine point `S ≠ O` whose image `p • S` is again affine, the place of
`S` restricts along `[p]^*` to the place of `p • S` with ramification
index ONE:

`ord_S([p]^* z) = ord_{p • S}(z)`.

Two independent facts are packed in here.

*The center.*  The prime `([p]^*)⁻¹(m_S)` of `F[W]` is
`pointIdeal W (p • S)`, because evaluating the generic identity
`hptaut` at `S` gives `([p]^* z)(S) = z(p • S)`; equivalently, the
composite `F[W] → K → F` "evaluate the pullback at `S`" is the
evaluation at `p • S`.

*Unramifiedness.*  The index is `1`, not merely positive: `[p]` is
separable when `(p : F) ≠ 0`, the fiber of the vertical `X − x_R` being
cut out by the division-polynomial pullback `Φ_p − x_R·Ψ_p²` (mathlib's
`WeierstrassCurve.Φ` / `ΨSq`), monic of degree `p²`
(`natDegree_Φ`, `coeff_Φ`) with `p²` DISTINCT roots — so `x ∘ [p] − x_R`
has a simple zero at each of the `p²` points of the fiber.

**State of the proof: PROVEN over the two bricks.**  The route
suggested by the previous owner is the one implemented below: the
statement is proven first for the vertical generators
`CoordinateRing.XClass W x_R` and for the line classes — the exact
`[p]`-analogues of the proven translation bricks
`spanSingleton_pointEval_XClass` / `spanSingleton_pointEval_YClass`,
now `count_pointEval_XClass_of_smul_ne_zero` (PROVEN 2026-07-25, over
the purely polynomial leaf `rootMultiplicity_Φ_sub_C_mul_ΨSq`) and the
still-sorried `count_pointEval_YClass_of_smul_ne_zero` — and then propagated to a
general `z` by the same Miller-style pair-peeling induction on the
affine divisor of `z` that `spanSingleton_pointEval_translate` runs for
`τ_Q^*`.  The induction is the whole proof below and is complete: the
`O`-entries of the divisor are invisible because `p • S ≠ O`, the empty
divisor makes `z` a unit constant whose pullback is a unit, a single
affine point is impossible by the class-group argument, and the two
pair cases peel a vertical resp. a line, the extra vertical of the line
case cancelling exactly against the `(P₁ ⊕ P₂)`-entry it introduces.

**Where the remaining mathematics is.**  Both bricks reduce, through
the division-polynomial relation `xp · ΨSq_p(x) = Φ_p(x)` of
`exists_smul_tautPoint_eq`, to the SEPARABILITY of `[p]` for
`(p : F) ≠ 0` — concretely, that `x_S` is a simple root of
`Φ_p − x_R·ΨSq_p`.  (A THIRD and much shorter route, found 2026-07-25,
is recorded at the leaf `rootMultiplicity_Φ_sub_C_mul_ΨSq`, which is
all that the vertical brick now costs.)  Two routes were known before,
and neither is in mathlib:

* *Invariant differential.*  `[p]^*ω = p·ω` with `ω = dx/(2y+a₁x+a₃)`
  nowhere zero forces every ramification index of `[p]` to be `1`.  In
  algebraic form: the `F`-derivation `D` of `F[W]` with `D x = ψ₂`,
  `D y = 3x²+2a₂x+a₄−a₁y` satisfies `D ∘ [p]^* = p · [p]^* ∘ D`, which
  is exactly the additivity of `P ↦ D(x_P)/ψ₂(P)` on `(curveK W).Point`
  — an algebraic identity in the group-law formulas.  Missing machinery:
  a derivation on `F[W] = F[X][Y]/(f)` (descent of `f_y ∂_X − f_x ∂_Y`
  along `AdjoinRoot.mk`, mathlib has no quotient-descent API for
  `Derivation`), its extension to `K = Frac F[W]` (mathlib has no
  fraction-field extension of a derivation either), and the order
  estimate `ord_v(D g) ≥ ord_v(g) − 1`.
* *Fiber counting.*  All ramification indices of `[p]` over a point are
  equal, because `[p] ∘ τ_κ = [p]` for `κ ∈ E[p]`
  (`lift_pointEval_pullback_eq`, already proven here); so
  `e · #E[p] = deg[p]`, and `#E[p] = p² = deg[p]` gives `e = 1`.  This
  needs `deg[p] = p²`, i.e. `[K : [p]^*K] = p²`, which is again the
  degree statement for `Φ_p/ΨSq_p`.

The hypothesis `hzev` is REDUNDANT: evaluation at `p • taut` is
injective (`pointEval_injective_of_forall_ne_constHom` applied through
`smul_taut_xCoord_ne_constHom`), so `z ≠ 0` already gives it, and the
proof below derives it rather than using the hypothesis.  It is kept in
the signature because the consumer supplies it and the sibling leaf
`count_pointEval_of_smul_eq_zero` is stated in parallel. -/
theorem count_pointEval_of_smul_ne_zero [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {z : W.CoordinateRing} (hz : z ≠ 0)
    (_hzev : pointEval (constHom W) hpn.left z ≠ 0)
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S ≠ 0)
    {v w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S)
    (hwS : w.asIdeal = pointIdeal W ((p : ℤ) • S)) :
    FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left z)) =
      FractionalIdeal.count W.FunctionField w
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField z)) := by
  classical
  -- ── Evaluation at `p • taut` is injective: its `x`-coordinate is not a
  -- constant, by the division-polynomial relation `xp·ΨSq_p(x) = Φ_p(x)`.
  obtain ⟨xp', yp', hpn', hptaut', hxrel⟩ :=
    exists_smul_tautPoint_eq (W := W) hΔ hp
  have hxx : xp = xp' := by
    have hpts := hptaut.symm.trans hptaut'
    injection hpts with hx _
  subst hxx
  have hinj : Function.Injective (pointEval (constHom W) hpn.left) :=
    pointEval_injective_of_forall_ne_constHom hpn
      (smul_taut_xCoord_ne_constHom hxrel)
  have hspan0 : ∀ a : W.CoordinateRing, a ≠ 0 →
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left a) ≠ 0 := by
    intro a ha
    refine (isUnit_spanSingleton_of_ne_zero ?_).ne_zero
    intro h0
    exact ha (hinj (by rw [h0, map_zero]))
  -- ── The right-hand side is the multiplicity of `p • S` in the affine
  -- divisor `D` of `z` (`count_spanSingleton_algebraMap`).
  obtain ⟨D, -, hD⟩ := exists_multiset_span_eq_prod_pointIdeal hΔ hz
  rw [count_spanSingleton_algebraMap hpS hwS hD]
  -- ── Miller-style induction on the affine divisor, exactly as for the
  -- generic translate (`spanSingleton_pointEval_translate`).
  suffices H : ∀ (n : ℕ) (E : Multiset W.Point), Multiset.card E = n →
      ∀ a : W.CoordinateRing, a ≠ 0 →
      Ideal.span {a} = (E.map (pointIdeal W)).prod →
      FractionalIdeal.count W.FunctionField v
          (FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hpn.left a)) =
        (Multiset.count ((p : ℤ) • S) E : ℤ) by
    exact H (Multiset.card D) D rfl z hz hD
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
  intro E hcard a ha haspan
  by_cases h0 : (0 : W.Point) ∈ E
  · -- an `O` entry is invisible to both sides, because `p • S ≠ O`
    obtain ⟨E', rfl⟩ := Multiset.exists_cons_of_mem h0
    have hlt : Multiset.card E' < n := by
      rw [← hcard, Multiset.card_cons]; omega
    have haspan' : Ideal.span {a} = (E'.map (pointIdeal W)).prod := by
      rwa [Multiset.map_cons, Multiset.prod_cons,
        show pointIdeal W 0 = ⊤ from rfl, Ideal.top_mul] at haspan
    rw [IH (Multiset.card E') hlt E' rfl a ha haspan',
      Multiset.count_cons_of_ne hpS]
  · by_cases hE0 : E = 0
    · -- empty divisor: `a` is a unit constant, and so is its pullback
      subst hE0
      have hatop : Ideal.span {a} = ⊤ := by
        rw [haspan, Multiset.map_zero, Multiset.prod_zero, Ideal.one_eq_top]
      obtain ⟨c, -, rfl⟩ :=
        coordinateRing_isUnit_eq_const (Ideal.span_singleton_eq_top.mp hatop)
      rw [pointEval_C,
        show constHom W c = algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (Polynomial.C (Polynomial.C c))) from rfl,
        ← FractionalIdeal.coeIdeal_span_singleton, hatop,
        FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one]
      simp
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
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
      · -- opposite points at the head: peel the vertical `X − x₁`
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
        have hV := count_pointEval_XClass_of_smul_ne_zero (W := W)
          hΔ hp hptaut h₂ hS0 hpS hvS
        rw [map_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
          FractionalIdeal.count_mul W.FunctionField v
            (hspan0 _ (CoordinateRing.XClass_ne_zero x₁)) (hspan0 _ ha'),
          hV, hIH,
          show (WeierstrassCurve.Affine.Point.some x₁ (W.negY x₁ y₂) h₁ :
              W.Point) = -WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ from
            (Point.neg_some h₂).symm]
        simp only [Multiset.count_cons, Multiset.count_zero]
        push_cast
        ring
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
        rw [← hadd] at hIH
        have hV := count_pointEval_XClass_of_smul_ne_zero (W := W) hΔ hp hptaut
          (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy) hS0 hpS hvS
        rw [← hadd] at hV
        have hL := count_pointEval_YClass_of_smul_ne_zero (W := W)
          hΔ hp hptaut h₁ h₂ hxy hS0 hpS hvS
        -- the ideal identity `a · (X − x_{P₁⊕P₂}) = ℓ · a'` in orders
        have hkey : FractionalIdeal.count W.FunctionField v
              (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hpn.left a)) +
            FractionalIdeal.count W.FunctionField v
              (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hpn.left
                  (CoordinateRing.XClass W
                    (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))))) =
            FractionalIdeal.count W.FunctionField v
              (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hpn.left
                  (CoordinateRing.YClass W
                    (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))))) +
            FractionalIdeal.count W.FunctionField v
              (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                (pointEval (constHom W) hpn.left a')) := by
          rw [← FractionalIdeal.count_mul W.FunctionField v (hspan0 _ ha)
                (hspan0 _ (CoordinateRing.XClass_ne_zero _)),
            ← FractionalIdeal.count_mul W.FunctionField v
                (hspan0 _ (CoordinateRing.YClass_ne_zero _)) (hspan0 _ ha'),
            FractionalIdeal.spanSingleton_mul_spanSingleton,
            FractionalIdeal.spanSingleton_mul_spanSingleton,
            ← map_mul, ← map_mul, hfact]
        rw [hV, hL, hIH] at hkey
        simp only [Multiset.count_cons, Multiset.count_zero] at hkey ⊢
        push_cast at hkey ⊢
        linarith

/-- **L4-7 leaf (PROVEN, over the affine branch): the `[p]`-pullback
over the place at infinity.**  Same setup as
`count_pointEval_of_smul_ne_zero`, but now the affine point `S ≠ O` is a
`p`-torsion point, so it lies over the point at infinity: `p • S = O`.
If `z` has affine divisor `D`, then

`ord_S([p]^* z) = −#D`,

a POLE of order the affine degree of `z`.  Reason: the divisor of `z`
on the complete curve is `Σ_{R ∈ D} (R) − #D·(O)` — the affine data `D`
determines the pole at infinity because `deg div z = 0` — and `[p]` is
unramified over `O` exactly as over every other point (separability,
`(p : F) ≠ 0`), with `[p]^*(O) = Σ_{κ ∈ E[p]} (κ)`; `S` is one of those
`κ`, and it occurs once.

**PROOF (translation transport + a degree count).**  No division
polynomial and no pair-peeling induction is needed: this branch is
DERIVED from the affine branch `count_pointEval_of_smul_ne_zero`, which
is declared above, so the dependency is mechanically acyclic (the affine
branch cannot in turn consume this one).  The two leaves are therefore
one leaf: what remains open is exactly the multiplicity-one statement
over affine points.

Write `u = [p]^*z = A/B` with `A, B ∈ F[W]` (`IsLocalization.surj`) of
affine divisors `D_A, D_B` (`exists_multiset_span_eq_prod_pointIdeal`),
and set `ord P := mult_P(D_A) − mult_P(D_B)` — the multiplicity of `u`
at the place of `P` (`count_spanSingleton_algebraMap` on numerator and
denominator) — and `deg := #D_A − #D_B`, the affine degree of `div u`.

* *Lemma A (translation transport).*  For EVERY nonzero `p`-torsion
  point `κ`, `ord κ = −deg`.  Since `[p] ∘ τ_κ = [p]`, the function `u`
  is fixed by the lifted translation `σ_{⊖κ}`
  (`lift_pointEval_pullback_eq`), so `u = (τ_{⊖κ}^*A)/(τ_{⊖κ}^*B)`; and
  the PROVEN divisor transport `spanSingleton_pointEval_translate`,
  `(τ_{⊖κ}^*b)·I_{κ}^{#E} = ∏_{R ∈ E} I_{R⊖(⊖κ)}`, read at the place of
  `κ` gives `ord_κ(τ_{⊖κ}^*b) = −#E`, because `R ⊖ (⊖κ) = κ` forces
  `R = O ∉ E`.  This is the step that makes the pole at infinity visible
  affinely: translating by `⊖κ` moves `O` onto `κ`.

* *Lemma S (affine branch).*  For `p • P ≠ O`,
  `ord P = mult_{p•P}(D)` — this is `count_pointEval_of_smul_ne_zero`.

Summing `ord` over the finite support of `div u` gives `deg`; splitting
that sum along the torsion fiber gives `−deg·#(E[p]∖O) + #E[p]·#D`,
since every one of the `#E[p]` preimages of an `R ∈ D` has `ord > 0` and
so really occurs in the support, while (once `deg ≠ 0`) Lemma A puts
every nonzero torsion point in the support too.  Hence
`deg·#E[p] = #D·#E[p]`, so `deg = #D` and `ord S = −#D`.  (If `deg = 0`
the same identity forces `D = 0` and the claim reads `0 = 0`.)  Note
that `#E[p] = p²` is never used as a NUMBER — it cancels — and the
finiteness of `E[p]` is *derived* from the finiteness of the divisor
support rather than assumed, so no torsion enumeration has to be
supplied. -/
theorem count_pointEval_of_smul_eq_zero [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {z : W.CoordinateRing} (hz : z ≠ 0)
    (hzev : pointEval (constHom W) hpn.left z ≠ 0)
    {D : Multiset W.Point} (hD0 : (0 : W.Point) ∉ D)
    (hD : Ideal.span {z} = (D.map (pointIdeal W)).prod)
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S = 0)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S) :
    FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left z)) = -(Multiset.card D : ℤ) := by
  classical
  -- ── the pullback `[p]^*` is injective, so it extends to `K`
  obtain ⟨xp', yp', hpn', hsmul', hxrel⟩ := exists_smul_tautPoint_eq (W := W) hΔ hp
  have hxx : xp = xp' := by
    have h := hptaut.symm.trans hsmul'
    injection h with h1 _
  have hxc : ∀ c : F, xp ≠ constHom W c := by
    intro c
    rw [hxx]
    exact smul_taut_xCoord_ne_constHom hxrel c
  have hinj : Function.Injective (pointEval (constHom W) hpn.left) :=
    pointEval_injective_of_forall_ne_constHom hpn hxc
  set u : W.FunctionField := pointEval (constHom W) hpn.left z with hudef
  -- ── a fraction presentation `u = A / B` of the pullback
  obtain ⟨⟨A, ⟨B, hBmem⟩⟩, hAB0⟩ := IsLocalization.surj W.CoordinateRing⁰ u
  have hAB : u * algebraMap W.CoordinateRing W.FunctionField B =
      algebraMap W.CoordinateRing W.FunctionField A := hAB0
  have hB0 : B ≠ 0 := nonZeroDivisors.ne_zero hBmem
  have halgB0 : algebraMap W.CoordinateRing W.FunctionField B ≠ 0 := fun h =>
    hB0 ((injective_iff_map_eq_zero _).mp
      (IsFractionRing.injective W.CoordinateRing W.FunctionField) B h)
  have halgA0 : algebraMap W.CoordinateRing W.FunctionField A ≠ 0 := by
    rw [← hAB]
    exact mul_ne_zero hzev halgB0
  have hA0 : A ≠ 0 := fun h => halgA0 (by rw [h, map_zero])
  obtain ⟨DA, hDA0, hDAspan⟩ := exists_multiset_span_eq_prod_pointIdeal hΔ hA0
  obtain ⟨DB, hDB0, hDBspan⟩ := exists_multiset_span_eq_prod_pointIdeal hΔ hB0
  -- `ord P` is the multiplicity of `u` at the place of `P`, and `dgr`
  -- the affine degree of `div u`.
  set ord : W.Point → ℤ :=
    fun P => (Multiset.count P DA : ℤ) - (Multiset.count P DB : ℤ) with horddef
  have hord : ∀ P : W.Point,
      ord P = (Multiset.count P DA : ℤ) - (Multiset.count P DB : ℤ) :=
    fun P => congrFun horddef P
  set dgr : ℤ := (Multiset.card DA : ℤ) - (Multiset.card DB : ℤ) with hdgref
  have hspanmul : FractionalIdeal.spanSingleton W.CoordinateRing⁰ u *
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField B) =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (algebraMap W.CoordinateRing W.FunctionField A) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hAB]
  have hspanu0 : FractionalIdeal.spanSingleton W.CoordinateRing⁰ u ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hzev
  have hspanB0 : FractionalIdeal.spanSingleton W.CoordinateRing⁰
      (algebraMap W.CoordinateRing W.FunctionField B) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact halgB0
  have hbridge : ∀ (P : W.Point) (w : IsDedekindDomain.HeightOneSpectrum
      W.CoordinateRing), P ≠ 0 → w.asIdeal = pointIdeal W P →
      FractionalIdeal.count W.FunctionField w
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ u) = ord P := by
    intro P w hP0 hwP
    have h1 := congrArg (FractionalIdeal.count W.FunctionField w) hspanmul
    rw [FractionalIdeal.count_mul W.FunctionField w hspanu0 hspanB0,
      count_spanSingleton_algebraMap hP0 hwP hDAspan,
      count_spanSingleton_algebraMap hP0 hwP hDBspan] at h1
    rw [hord]
    omega
  -- ── the support of `div u`, and its affine degree as a sum
  set Ssup : Finset W.Point := DA.toFinset ∪ DB.toFinset with hSsupdef
  have h0not : (0 : W.Point) ∉ Ssup := by
    rw [hSsupdef]
    simp only [Finset.mem_union, Multiset.mem_toFinset]
    exact fun h => h.elim hDA0 hDB0
  have hordzero : ∀ P : W.Point, P ∉ Ssup → ord P = 0 := by
    intro P hP
    rw [hSsupdef] at hP
    simp only [Finset.mem_union, Multiset.mem_toFinset, not_or] at hP
    rw [hord, Multiset.count_eq_zero_of_notMem hP.1,
      Multiset.count_eq_zero_of_notMem hP.2]
    ring
  have hsumord : ∑ P ∈ Ssup, ord P = dgr := by
    have hsA : ∑ P ∈ Ssup, (Multiset.count P DA : ℤ) = (Multiset.card DA : ℤ) := by
      rw [← Multiset.toFinset_sum_count_eq DA]
      push_cast
      refine (Finset.sum_subset (hSsupdef ▸ Finset.subset_union_left) ?_).symm
      intro x _ hx
      simp only [Multiset.mem_toFinset] at hx
      simp [Multiset.count_eq_zero_of_notMem hx]
    have hsB : ∑ P ∈ Ssup, (Multiset.count P DB : ℤ) = (Multiset.card DB : ℤ) := by
      rw [← Multiset.toFinset_sum_count_eq DB]
      push_cast
      refine (Finset.sum_subset (hSsupdef ▸ Finset.subset_union_right) ?_).symm
      intro x _ hx
      simp only [Multiset.mem_toFinset] at hx
      simp [Multiset.count_eq_zero_of_notMem hx]
    rw [Finset.sum_congr rfl (fun P _ => hord P), Finset.sum_sub_distrib,
      hsA, hsB, hdgref]
  -- ── LEMMA A: at every nonzero `p`-torsion point the multiplicity of
  -- the pullback is minus its affine degree.  `u` is invariant under the
  -- lifted translation by `⊖κ`, which carries the place at infinity onto
  -- the place of `κ`.
  have hLemA : ∀ κ : W.Point, κ ≠ 0 → (p : ℤ) • κ = 0 → ord κ = -dgr := by
    intro κ hκ0 hκtor
    obtain ⟨xQ, yQ, hQn, hptQ⟩ := exists_translate_some hΔ (-κ)
    obtain ⟨w, hw⟩ := exists_heightOneSpectrum_pointIdeal hκ0
    have hσu : IsFractionRing.lift (pointEval_injective hΔ hptQ) u = u := by
      have h := lift_pointEval_pullback_eq hΔ (Q := -κ)
        (by rw [smul_neg, hκtor, neg_zero]) hptQ hptaut hinj
        (algebraMap W.CoordinateRing W.FunctionField z)
      rwa [IsFractionRing.lift_algebraMap] at h
    have hABσ : u * pointEval (constHom W) hQn.left B =
        pointEval (constHom W) hQn.left A := by
      have h := congrArg (IsFractionRing.lift (pointEval_injective hΔ hptQ)) hAB
      rwa [map_mul, hσu, IsFractionRing.lift_algebraMap,
        IsFractionRing.lift_algebraMap] at h
    -- the multiplicity at `κ` of a `(⊖κ)`-translated coordinate function
    -- is minus the affine degree of its divisor
    have htrans : ∀ (b : W.CoordinateRing) (E : Multiset W.Point), b ≠ 0 →
        (0 : W.Point) ∉ E → Ideal.span {b} = (E.map (pointIdeal W)).prod →
        FractionalIdeal.count W.FunctionField w
          (FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hQn.left b)) = -(Multiset.card E : ℤ) := by
      intro b E hb hE0 hEspan
      have h := spanSingleton_pointEval_translate hΔ hptQ hb hEspan
      rw [neg_neg] at h
      have hb0 : FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hQn.left b) ≠ 0 := by
        rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
        exact fun h0 => hb ((injective_iff_map_eq_zero _).mp
          (pointEval_injective hΔ hptQ) b h0)
      have hpi0 : ((pointIdeal' W κ :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) ^
            Multiset.card E ≠ 0 :=
        pow_ne_zero _ (pointIdeal' W κ).isUnit.ne_zero
      have h2 : (E.map fun R => (pointIdeal' W (R - -κ) :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod =
          ((E.map fun R => R - -κ).map fun R =>
            (pointIdeal' W R :
              FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
        rw [Multiset.map_map]
        rfl
      have h3 : Multiset.count κ (E.map fun R => R - -κ) = 0 := by
        refine Multiset.count_eq_zero_of_notMem ?_
        intro hmem
        obtain ⟨R, hR, hRe⟩ := Multiset.mem_map.mp hmem
        rw [sub_neg_eq_add] at hRe
        exact hE0 (add_right_cancel (hRe.trans (zero_add κ).symm) ▸ hR)
      have h1 := congrArg (FractionalIdeal.count W.FunctionField w) h
      rw [FractionalIdeal.count_mul W.FunctionField w hb0 hpi0,
        FractionalIdeal.count_pow, count_coe_pointIdeal' hκ0 hw κ,
        if_pos rfl, mul_one, h2, count_prod_coe_pointIdeal' hκ0 hw, h3] at h1
      push_cast at h1 ⊢
      omega
    have hcountA := htrans A DA hA0 hDA0 hDAspan
    have hcountB := htrans B DB hB0 hDB0 hDBspan
    have hspanmulσ : FractionalIdeal.spanSingleton W.CoordinateRing⁰ u *
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hQn.left B) =
        FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hQn.left A) := by
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hABσ]
    have hspanBσ0 : FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hQn.left B) ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
      exact fun h0 => hB0 ((injective_iff_map_eq_zero _).mp
        (pointEval_injective hΔ hptQ) B h0)
    have h5 := congrArg (FractionalIdeal.count W.FunctionField w) hspanmulσ
    rw [FractionalIdeal.count_mul W.FunctionField w hspanu0 hspanBσ0,
      hcountA, hcountB, hbridge κ w hκ0 hw] at h5
    rw [hdgref]
    omega
  -- ── LEMMA S: away from the torsion fiber the affine branch computes
  -- the multiplicity of the pullback.
  have hLemS : ∀ P : W.Point, P ≠ 0 → (p : ℤ) • P ≠ 0 →
      ord P = (Multiset.count ((p : ℤ) • P) D : ℤ) := by
    intro P hP0 hpP0
    obtain ⟨w, hw⟩ := exists_heightOneSpectrum_pointIdeal hP0
    obtain ⟨w', hw'⟩ := exists_heightOneSpectrum_pointIdeal hpP0
    have h := count_pointEval_of_smul_ne_zero hΔ hp hptaut hz hzev hP0 hpP0 hw hw'
    rw [count_spanSingleton_algebraMap hpP0 hw' hD, hbridge P w hP0 hw] at h
    exact h
  -- ── split the affine degree along the torsion fiber
  set Stor : Finset W.Point := Ssup.filter (fun P => (p : ℤ) • P = 0) with hStordef
  set Snon : Finset W.Point :=
    Ssup.filter (fun P => ¬ ((p : ℤ) • P = 0)) with hSnondef
  have hsplit : ∑ P ∈ Stor, ord P + ∑ P ∈ Snon, ord P = dgr := by
    rw [hStordef, hSnondef, Finset.sum_filter_add_sum_filter_not, hsumord]
  have ht : ∑ P ∈ Stor, ord P = (Stor.card : ℤ) * (-dgr) := by
    have hc : ∀ P ∈ Stor, ord P = -dgr := by
      intro P hP
      rw [hStordef, Finset.mem_filter] at hP
      exact hLemA P (fun h => h0not (h ▸ hP.1)) hP.2
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  have hn : ∑ P ∈ Snon, ord P =
      ∑ P ∈ Snon, (Multiset.count ((p : ℤ) • P) D : ℤ) := by
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [hSnondef, Finset.mem_filter] at hP
    exact hLemS P (fun h => h0not (h ▸ hP.1)) hP.2
  rw [ht, hn] at hsplit
  have hkey : dgr * (1 + (Stor.card : ℤ)) =
      ∑ P ∈ Snon, (Multiset.count ((p : ℤ) • P) D : ℤ) := by
    linear_combination -hsplit
  -- ── every preimage of a point of `D` really occurs in `Snon`
  have hfibmem : ∀ P : W.Point, P ≠ 0 → (p : ℤ) • P ∈ D → P ∈ Snon := by
    intro P hP0 hmem
    have hpP0 : (p : ℤ) • P ≠ 0 := fun h => hD0 (h ▸ hmem)
    have hordP : ord P = (Multiset.count ((p : ℤ) • P) D : ℤ) := hLemS P hP0 hpP0
    have hpos : 0 < Multiset.count ((p : ℤ) • P) D := Multiset.count_pos.mpr hmem
    have hPS : P ∈ Ssup := by
      by_contra hc
      rw [hordzero P hc] at hordP
      omega
    rw [hSnondef, Finset.mem_filter]
    exact ⟨hPS, hpP0⟩
  -- ── conclude: the multiplicity at `S` is minus the affine degree,
  -- and the affine degree is `#D`.
  have hgoal : FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ u) = -dgr := by
    rw [hbridge S v hS0 hvS]
    exact hLemA S hS0 hpS
  rw [hgoal]
  by_cases hdgr0 : dgr = 0
  · -- degenerate branch: `D` is empty
    have hDempty : D = 0 := by
      by_contra hDne
      obtain ⟨R, hR⟩ := Multiset.exists_mem_of_ne_zero hDne
      have hR0 : R ≠ 0 := fun h => hD0 (h ▸ hR)
      obtain ⟨T, hT⟩ := exists_zsmul_eq hΔ hp R
      have hT0 : T ≠ 0 := by
        intro h
        rw [h, smul_zero] at hT
        exact hR0 hT.symm
      have hTm : T ∈ Snon := hfibmem T hT0 (by rw [hT]; exact hR)
      have hsum0 : ∑ P ∈ Snon, (Multiset.count ((p : ℤ) • P) D : ℤ) = 0 := by
        rw [← hkey, hdgr0, zero_mul]
      have hnn : ∀ P ∈ Snon, (0 : ℤ) ≤ (Multiset.count ((p : ℤ) • P) D : ℤ) :=
        fun P _ => Int.natCast_nonneg _
      have hz0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 T hTm
      rw [hT] at hz0
      have hcp := Multiset.count_pos.mpr hR
      omega
    rw [hDempty, hdgr0]
    simp
  · -- generic branch: every fiber of `[p]` has `Stor.card + 1` points
    have htor : ∀ Q : W.Point, (p : ℤ) • Q = 0 → Q ≠ 0 → Q ∈ Stor := by
      intro Q hQtor hQ0
      have hordQ := hLemA Q hQ0 hQtor
      have hQS : Q ∈ Ssup := by
        by_contra hc
        rw [hordzero Q hc] at hordQ
        exact hdgr0 (by omega)
      rw [hStordef, Finset.mem_filter]
      exact ⟨hQS, hQtor⟩
    have hfibcard : ∀ R ∈ D.toFinset,
        (Snon.filter (fun P => (p : ℤ) • P = R)).card = Stor.card + 1 := by
      intro R hR
      rw [Multiset.mem_toFinset] at hR
      have hR0 : R ≠ 0 := fun h => hD0 (h ▸ hR)
      obtain ⟨T, hT⟩ := exists_zsmul_eq hΔ hp R
      have hcard : (insert (0 : W.Point) Stor).card = Stor.card + 1 :=
        Finset.card_insert_of_notMem (fun h => h0not
          (by rw [hStordef, Finset.mem_filter] at h; exact h.1))
      rw [← hcard]
      refine (Finset.card_nbij' (fun κ => T + κ) (fun P => P - T) ?_ ?_ ?_ ?_).symm
      · intro κ hκ
        simp only [Finset.mem_coe, Finset.mem_insert] at hκ
        have hκtor : (p : ℤ) • κ = 0 := by
          rcases hκ with rfl | hκ
          · exact smul_zero _
          · rw [hStordef, Finset.mem_filter] at hκ
            exact hκ.2
        have hpTκ : (p : ℤ) • (T + κ) = R := by
          rw [smul_add, hT, hκtor, add_zero]
        have hTκ0 : T + κ ≠ 0 := by
          intro h
          rw [h, smul_zero] at hpTκ
          exact hR0 hpTκ.symm
        simp only [Finset.mem_coe, Finset.mem_filter]
        exact ⟨hfibmem (T + κ) hTκ0 (by rw [hpTκ]; exact hR), hpTκ⟩
      · intro P hP
        simp only [Finset.mem_coe, Finset.mem_filter] at hP
        have hκtor : (p : ℤ) • (P - T) = 0 := by
          rw [smul_sub, hP.2, hT, sub_self]
        simp only [Finset.mem_coe, Finset.mem_insert]
        by_cases hc : P - T = 0
        · exact Or.inl hc
        · exact Or.inr (htor (P - T) hκtor hc)
      · intro κ _
        simp
      · intro P _
        simp
    have hsumfib : ∑ P ∈ Snon, (Multiset.count ((p : ℤ) • P) D : ℤ) =
        (1 + (Stor.card : ℤ)) * (Multiset.card D : ℤ) := by
      have hsub : ∑ P ∈ Snon, (Multiset.count ((p : ℤ) • P) D : ℤ) =
          ∑ P ∈ Snon.filter (fun P => (p : ℤ) • P ∈ D),
            (Multiset.count ((p : ℤ) • P) D : ℤ) := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro x hxm hx
        rw [Finset.mem_filter, not_and] at hx
        rw [Multiset.count_eq_zero_of_notMem (hx hxm), Nat.cast_zero]
      have hfw := Finset.sum_fiberwise_of_maps_to
        (s := Snon.filter (fun P => (p : ℤ) • P ∈ D)) (t := D.toFinset)
        (g := fun P => (p : ℤ) • P)
        (fun x hx => by
          rw [Finset.mem_filter] at hx
          exact Multiset.mem_toFinset.mpr hx.2)
        (fun P => (Multiset.count ((p : ℤ) • P) D : ℤ))
      rw [hsub, ← hfw]
      have hinner : ∀ R ∈ D.toFinset,
          ∑ P ∈ (Snon.filter (fun P => (p : ℤ) • P ∈ D)).filter
              (fun P => (p : ℤ) • P = R),
            (Multiset.count ((p : ℤ) • P) D : ℤ) =
          (1 + (Stor.card : ℤ)) * (Multiset.count R D : ℤ) := by
        intro R hR
        have hfeq : (Snon.filter (fun P => (p : ℤ) • P ∈ D)).filter
            (fun P => (p : ℤ) • P = R) =
            Snon.filter (fun P => (p : ℤ) • P = R) := by
          rw [Finset.filter_filter]
          refine Finset.filter_congr fun x _ => ?_
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨h ▸ Multiset.mem_toFinset.mp hR, h⟩
        rw [hfeq, Finset.sum_congr rfl (fun P hP => by
            rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const, nsmul_eq_mul,
          hfibcard R hR]
        push_cast
        ring
      rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
      congr 1
      rw [← Multiset.toFinset_sum_count_eq D]
      push_cast
      rfl
    rw [hsumfib] at hkey
    have hpos : (0 : ℤ) < 1 + (Stor.card : ℤ) := by positivity
    have hfin : dgr = (Multiset.card D : ℤ) :=
      mul_right_cancel₀ hpos.ne' (hkey.trans (by ring))
    rw [hfin]

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
is all a fractional ideal sees).

**State of the proof.**  The skeleton below is written out and the whole
divisor bookkeeping is proven: the identity is reduced to an equality of
`FractionalIdeal.count`s at every height-one place of `F[W]` (closed by
`FractionalIdeal.finprod_heightOneSpectrum_factorization'`), the count of
a multiset product, of an indicator sum, and of a `fiberProd` are
computed, the point-ideal multiplicities are proven (point ideals at
affine points are maximal, nonzero and injective in the point), and the
weak Nullstellensatz identification of height-one primes with affine
point ideals is proven.  The Dedekind substrate, which mathlib does not
provide for `CoordinateRing`, is supplied by
`isDedekindDomain_coordinateRing` — and note that it needs NO integral
closedness and NO smoothness argument, so the normality of the affine
curve that this proof once planned to establish is not required at all.
NO sorried `have` remains inside the proof: the multiplicity-one
pullback count `hcountEv` is now assembled from two TOP-LEVEL leaves,
split along the two geometrically different branches (both now PROVEN, the
second over the first; the open content has moved down into the two X/Y bricks),

* `count_pointEval_of_smul_ne_zero`: for `p • S ≠ O`, the order of
  `[p]^*z` at the place of `S` is the order of `z` at `p • S`
  (multiplicity one from separability of `[p]`, `(p : F) ≠ 0`, via
  `Φ_p − x_R·Ψ_p²`) — PROVEN, by Miller-style pair-peeling induction
  over the two sorried bricks `count_pointEval_XClass_of_smul_ne_zero` /
  `count_pointEval_YClass_of_smul_ne_zero`, which are where the
  separability of `[p]` is now localized;
* `count_pointEval_of_smul_eq_zero` (PROVEN): for `p • S = O`, that
  order is the pole order `−#D` of `z` at infinity — derived from the
  branch above by translation transport, since translating by `⊖S`
  carries the place at infinity onto the place of `S`;

the glue between them — reading the order of `z` at `p • S` off its
affine divisor `D` — being the proven
`count_spanSingleton_algebraMap`. -/
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
  classical
  -- ── The Dedekind substrate of `F[W]`, absent from mathlib for
  -- `CoordinateRing`.  It is NOT the geometric fact it looks like: as
  -- recorded at `isDedekindDomain_coordinateRing`, invertibility of the
  -- point ideals plus the factorization brick already carry the whole
  -- Dedekind property, with no integral-closedness and no smoothness
  -- argument, so the instance is a one-line consumption of that lemma.
  haveI : IsDedekindDomain W.CoordinateRing := isDedekindDomain_coordinateRing hΔ
  -- `F[W]` is a free rank-two `F[X]`-module, hence integral over `F[X]`;
  -- the weak Nullstellensatz step `hspec` below contracts a height-one
  -- place along `F[X]` and needs exactly that.
  haveI : Module.Finite (Polynomial F) W.CoordinateRing :=
    Polynomial.Monic.finite_adjoinRoot WeierstrassCurve.Affine.monic_polynomial
  -- ── Weak Nullstellensatz: over the algebraically closed `F`, every
  -- height-one prime of `F[W]` is the point ideal of an affine point.
  -- `F[W]` is a free rank-two `F[X]`-module, so it is integral over
  -- `F[X]` and the contraction `q = v ∩ F[X]` is maximal, i.e. `⟨X − x₀⟩`
  -- for some `x₀ ∈ F` (`F` algebraically closed).  The Weierstrass
  -- equation at `x₀` then splits over `F` as `(Y − y₁)(Y − y₂)` modulo
  -- the vertical `X − x₀ ∈ v`, and `v` being prime one of the two
  -- `Y`-classes lies in `v`; the resulting point ideal is maximal, hence
  -- equal to `v`.
  have hspec : ∀ v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing,
      ∃ S : W.Point, S ≠ 0 ∧ v.asIdeal = pointIdeal W S := by
    intro v
    haveI hmMax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    haveI hqMax : (v.asIdeal.comap
        (algebraMap (Polynomial F) W.CoordinateRing)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
    -- the contracted place is the vertical through some `x₀ ∈ F`
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F, CoordinateRing.XClass W x₀ ∈ v.asIdeal := by
      obtain ⟨g, hgspan⟩ := Submodule.IsPrincipal.principal
        (v.asIdeal.comap (algebraMap (Polynomial F) W.CoordinateRing))
      have hg0 : g ≠ 0 := by
        intro hg
        rw [hg, Submodule.span_zero_singleton] at hgspan
        rw [hgspan] at hqMax
        exact Polynomial.X_ne_zero
          (Ideal.span_singleton_eq_bot.mp
            (hqMax.eq_of_le
              (fun htop => Polynomial.not_isUnit_X
                (Ideal.span_singleton_eq_top.mp htop)) bot_le).symm)
      have hgu : ¬ IsUnit g := fun hu =>
        hqMax.ne_top (by rw [hgspan, Ideal.span_singleton_eq_top]; exact hu)
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root g fun hdeg =>
        hgu (Polynomial.isUnit_iff_degree_eq_zero.mpr hdeg)
      refine ⟨r, ?_⟩
      have hle : v.asIdeal.comap (algebraMap (Polynomial F) W.CoordinateRing) ≤
          Ideal.span {Polynomial.X - Polynomial.C r} := by
        rw [hgspan]
        exact Ideal.span_singleton_le_span_singleton.mpr
          (Polynomial.dvd_iff_isRoot.mpr hr)
      have hmem : (Polynomial.X - Polynomial.C r) ∈
          v.asIdeal.comap (algebraMap (Polynomial F) W.CoordinateRing) := by
        rw [hqMax.eq_of_le (fun htop => Polynomial.not_isUnit_X_sub_C r
          (Ideal.span_singleton_eq_top.mp htop)) hle]
        exact Ideal.mem_span_singleton_self _
      exact Ideal.mem_comap.mp hmem
    -- a root of the Weierstrass equation at `x₀` (`F` is algebraically closed)
    obtain ⟨y₁, hy₁⟩ : ∃ y : F, y ^ 2 + (W.a₁ * x₀ + W.a₃) * y -
        (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) = 0 := by
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
        (Polynomial.C 1 * Polynomial.X ^ 2 +
          Polynomial.C (W.a₁ * x₀ + W.a₃) * Polynomial.X +
          Polynomial.C (-(x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)))
        (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
      refine ⟨y, ?_⟩
      simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at hy
      linear_combination hy
    -- the two roots give the Weierstrass equation at `x₀`
    have hEq₁ : W.Equation x₀ y₁ :=
      (WeierstrassCurve.Affine.equation_iff ..).mpr (by linear_combination hy₁)
    have hEq₂ : W.Equation x₀ (-(W.a₁ * x₀ + W.a₃) - y₁) :=
      (WeierstrassCurve.Affine.equation_iff ..).mpr (by linear_combination hy₁)
    -- the Weierstrass polynomial vanishes in `F[W]`
    have h0 : CoordinateRing.mk W (Polynomial.X ^ 2 +
        Polynomial.C (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) *
          Polynomial.X -
        Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2 +
          Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆)) = 0 := by
      show CoordinateRing.mk W W.polynomial = 0
      exact AdjoinRoot.mk_self
    -- the splitting identity in `F[X][Y]`, exact modulo the vertical `X − x₀`
    have hpolyid : (Polynomial.X - Polynomial.C (Polynomial.C y₁)) *
        (Polynomial.X - Polynomial.C (Polynomial.C
          (-(W.a₁ * x₀ + W.a₃) - y₁))) =
        (Polynomial.X ^ 2 + Polynomial.C (Polynomial.C W.a₁ * Polynomial.X +
            Polynomial.C W.a₃) * Polynomial.X -
          Polynomial.C (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2 +
            Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆)) +
        Polynomial.C (Polynomial.X - Polynomial.C x₀) *
          (-(Polynomial.C (Polynomial.C W.a₁)) * Polynomial.X +
            Polynomial.C (Polynomial.X ^ 2 + Polynomial.C x₀ * Polynomial.X +
              Polynomial.C (x₀ ^ 2) + Polynomial.C W.a₂ *
                (Polynomial.X + Polynomial.C x₀) + Polynomial.C W.a₄)) := by
      have hy₁' := congrArg (fun t : F =>
        Polynomial.C (Polynomial.C t) : F → Polynomial (Polynomial F)) hy₁
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero] at hy₁' ⊢
      linear_combination -hy₁'
    -- hence the product of the two `Y`-classes lies in `v`
    have hprodmem : CoordinateRing.YClass W (Polynomial.C y₁) *
        CoordinateRing.YClass W (Polynomial.C (-(W.a₁ * x₀ + W.a₃) - y₁)) ∈
        v.asIdeal := by
      have hfac : CoordinateRing.YClass W (Polynomial.C y₁) *
          CoordinateRing.YClass W (Polynomial.C (-(W.a₁ * x₀ + W.a₃) - y₁)) =
          CoordinateRing.XClass W x₀ * CoordinateRing.mk W
            (-(Polynomial.C (Polynomial.C W.a₁)) * Polynomial.X +
              Polynomial.C (Polynomial.X ^ 2 + Polynomial.C x₀ * Polynomial.X +
                Polynomial.C (x₀ ^ 2) + Polynomial.C W.a₂ *
                  (Polynomial.X + Polynomial.C x₀) + Polynomial.C W.a₄)) := by
        simp only [CoordinateRing.YClass, CoordinateRing.XClass, ← map_mul]
        rw [hpolyid, map_add, map_mul, h0, zero_add]
      rw [hfac]
      exact Ideal.mul_mem_right _ _ hx₀
    -- either `Y`-class gives an affine point whose ideal is `v`
    have hmain : ∀ y : F, W.Equation x₀ y →
        CoordinateRing.YClass W (Polynomial.C y) ∈ v.asIdeal →
        ∃ S : W.Point, S ≠ 0 ∧ v.asIdeal = pointIdeal W S := by
      intro y hEq hYmem
      refine ⟨WeierstrassCurve.Affine.Point.some x₀ y
        ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
          hΔ).mp hEq), ?_, ?_⟩
      · exact WeierstrassCurve.Affine.Point.some_ne_zero _
      · refine ((xyIdeal_isMaximal hEq).eq_of_le hmMax.ne_top ?_).symm
        simp only [CoordinateRing.XYIdeal]
        refine Ideal.span_le.mpr ?_
        intro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        rcases ht with rfl | rfl
        · exact hx₀
        · exact hYmem
    rcases v.isPrime.mem_or_mem hprodmem with hy | hy
    · exact hmain y₁ hEq₁ hy
    · exact hmain (-(W.a₁ * x₀ + W.a₃) - y₁) hEq₂ hy
  -- ── The `v`-multiplicity of a point ideal: at the place of the
  -- affine point `S`, the point ideal of `Q` contributes `1` if
  -- `Q = S` and `0` otherwise (`pointIdeal W 0 = ⊤` contributing `0`).
  have hcountPt : ∀ (v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
      (S : W.Point), S ≠ 0 → v.asIdeal = pointIdeal W S → ∀ Q : W.Point,
      FractionalIdeal.count W.FunctionField v
          (pointIdeal' W Q : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
        if Q = S then 1 else 0 :=
    fun _ _ hS0 hvS Q => count_coe_pointIdeal' hS0 hvS Q
  -- ── The multiplicity-one pullback count.  This is the geometric
  -- heart of the brick: at the place of an affine point `S`, the order
  -- of the pullback `[p]^*z = pointEval (constHom W) hpn.left z` is the
  -- order of `z` at `p • S` — with multiplicity one, since `[p]` is
  -- separable when `(p : F) ≠ 0` — and the order of `z` at the place at
  -- infinity is minus its affine degree `#D` (`deg div z = 0`), which is
  -- what the `p • S = 0` branch records.  The two branches are the two
  -- sorried leaves `count_pointEval_of_smul_ne_zero` /
  -- `count_pointEval_of_smul_eq_zero`; here they are assembled, the
  -- affine branch reading the order of `z` at `p • S` off its divisor
  -- `D` through `count_spanSingleton_algebraMap`.
  have hcountEv : ∀ (v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
      (S : W.Point), S ≠ 0 → v.asIdeal = pointIdeal W S →
      FractionalIdeal.count W.FunctionField v
          (FractionalIdeal.spanSingleton W.CoordinateRing⁰
            (pointEval (constHom W) hpn.left z)) =
        (Multiset.count ((p : ℤ) • S) D : ℤ) -
          (if (p : ℤ) • S = 0 then (Multiset.card D : ℤ) else 0) := by
    intro v S hS0 hvS
    by_cases hpS : (p : ℤ) • S = 0
    · rw [if_pos hpS,
        count_pointEval_of_smul_eq_zero hΔ hp hptaut hz hzev hD0 hD hS0 hpS hvS,
        Multiset.count_eq_zero_of_notMem (by rwa [hpS])]
      push_cast
      ring
    · obtain ⟨w, hw⟩ := exists_heightOneSpectrum_pointIdeal hpS
      rw [if_neg hpS,
        count_pointEval_of_smul_ne_zero hΔ hp hptaut hz hzev hS0 hpS hvS hw,
        count_spanSingleton_algebraMap hpS hw hD]
      ring
  -- ── Fiber products are units, in particular nonzero.
  have hfib0 : ∀ T : W.Point, fiberProd W val T ≠ 0 := by
    intro T
    have hu : IsUnit (fiberProd W val T) := by
      unfold fiberProd
      exact isUnit_prod_coe_pointIdeal' _
    exact hu.ne_zero
  -- ── The `v`-multiplicity of a multiset product of nonzero fractional
  -- ideals is the sum of the multiplicities.
  have hcountProd : ∀ (v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
      (f : W.Point → FractionalIdeal W.CoordinateRing⁰ W.FunctionField),
      (∀ R : W.Point, f R ≠ 0) → ∀ s : Multiset W.Point,
      FractionalIdeal.count W.FunctionField v (s.map f).prod =
        (s.map fun R => FractionalIdeal.count W.FunctionField v (f R)).sum := by
    intro v f hf s
    induction s using Multiset.induction with
    | empty => simpa using FractionalIdeal.count_one W.FunctionField v
    | cons a s ih =>
      have h0 : (s.map f).prod ≠ 0 := by
        refine Multiset.prod_ne_zero ?_
        intro hmem
        obtain ⟨R, -, hR⟩ := Multiset.mem_map.mp hmem
        exact hf R hR
      rw [Multiset.map_cons, Multiset.prod_cons,
        FractionalIdeal.count_mul W.FunctionField v (hf a) h0, ih,
        Multiset.map_cons, Multiset.sum_cons]
  -- ── An indicator sum over a multiset is its count.
  have hsumcount : ∀ (a : W.Point) (s : Multiset W.Point),
      (s.map fun R => if a = R then (1 : ℤ) else 0).sum = (Multiset.count a s : ℤ) := by
    intro a s
    induction s using Multiset.induction with
    | empty => simp
    | cons b s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
      split_ifs with h <;> push_cast <;> ring
  -- ── The `v`-multiplicity of a fiber product: the fiber of `[p]` over
  -- `p • T` meets the place of `S` exactly once, and only when
  -- `p • S = p • T`.
  have hcountFib : ∀ (v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
      (S : W.Point), S ≠ 0 → v.asIdeal = pointIdeal W S → ∀ T : W.Point,
      FractionalIdeal.count W.FunctionField v (fiberProd W val T) =
        if (p : ℤ) • S = (p : ℤ) • T then 1 else 0 := by
    intro v S hS0 hvS T
    have hstep : FractionalIdeal.count W.FunctionField v (fiberProd W val T) =
        (Finset.univ.val.map fun i : ι =>
          if T + val i = S then (1 : ℤ) else 0).sum := by
      unfold fiberProd
      rw [hcountProd v (fun R => (pointIdeal' W R :
            FractionalIdeal W.CoordinateRing⁰ W.FunctionField))
          (fun R => (pointIdeal' W R).isUnit.ne_zero)
          (Finset.univ.val.map fun i => T + val i), Multiset.map_map]
      exact congrArg Multiset.sum
        (Multiset.map_congr rfl fun i _ => hcountPt v S hS0 hvS (T + val i))
    by_cases hcase : (p : ℤ) • S = (p : ℤ) • T
    · rw [hstep, if_pos hcase, Finset.sum_map_val]
      obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ι, val i₀ = S - T :=
        hval_surj _ (by rw [smul_sub, hcase, sub_self])
      have hfun : ∀ i : ι, (if T + val i = S then (1 : ℤ) else 0) =
          if i = i₀ then (1 : ℤ) else 0 := by
        intro i
        by_cases hi : i = i₀
        · rw [if_pos hi, if_pos (show T + val i = S by rw [hi, hi₀]; abel)]
        · refine if_neg (fun hcon => hi ?_) |>.trans (if_neg hi).symm
          exact hval_inj (by rw [hi₀]; exact eq_sub_of_add_eq' hcon)
      simp only [hfun]
      simp
    · rw [hstep, if_neg hcase, Finset.sum_map_val]
      refine Finset.sum_eq_zero fun i _ => if_neg fun hcon => hcase ?_
      rw [← hcon, smul_add, hval_tor i, add_zero]
  -- ── Both sides are nonzero fractional ideals.
  have hL0 : (D.map fun R => fiberProd W val (sec R)).prod ≠ 0 := by
    refine Multiset.prod_ne_zero ?_
    intro hmem
    obtain ⟨R, -, hR⟩ := Multiset.mem_map.mp hmem
    exact hfib0 (sec R) hR
  have hspan0 : FractionalIdeal.spanSingleton W.CoordinateRing⁰
      (pointEval (constHom W) hpn.left z) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hzev
  have hR0 : FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left z) *
      fiberProd W val (sec 0) ^ Multiset.card D ≠ 0 :=
    mul_ne_zero hspan0 (pow_ne_zero _ (hfib0 (sec 0)))
  -- ── The two sides have the same multiplicity at every place.
  have hcounts : ∀ v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing,
      FractionalIdeal.count W.FunctionField v
          (D.map fun R => fiberProd W val (sec R)).prod =
        FractionalIdeal.count W.FunctionField v
          (FractionalIdeal.spanSingleton W.CoordinateRing⁰
              (pointEval (constHom W) hpn.left z) *
            fiberProd W val (sec 0) ^ Multiset.card D) := by
    intro v
    obtain ⟨S, hS0, hvS⟩ := hspec v
    rw [hcountProd v (fun R => fiberProd W val (sec R))
        (fun R => hfib0 (sec R)) D,
      FractionalIdeal.count_mul W.FunctionField v hspan0
        (pow_ne_zero _ (hfib0 (sec 0))),
      FractionalIdeal.count_pow, hcountEv v S hS0 hvS,
      hcountFib v S hS0 hvS (sec 0), hsec 0]
    have hLHS : (D.map fun R =>
        FractionalIdeal.count W.FunctionField v (fiberProd W val (sec R))).sum =
        (Multiset.count ((p : ℤ) • S) D : ℤ) := by
      have hfun : ∀ R : W.Point,
          FractionalIdeal.count W.FunctionField v (fiberProd W val (sec R)) =
            if (p : ℤ) • S = R then (1 : ℤ) else 0 := by
        intro R
        rw [hcountFib v S hS0 hvS (sec R), hsec R]
      simp only [hfun]
      exact hsumcount _ D
    rw [hLHS]
    by_cases h0 : (p : ℤ) • S = 0
    · rw [if_pos h0, if_pos h0]; ring
    · rw [if_neg h0, if_neg h0]; ring
  -- ── Equal multiplicities at every place means equal fractional
  -- ideals (unique factorization over the Dedekind domain `F[W]`).
  calc (D.map fun R => fiberProd W val (sec R)).prod
      = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing,
          (v.asIdeal : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
            FractionalIdeal.count W.FunctionField v
              (D.map fun R => fiberProd W val (sec R)).prod :=
        (FractionalIdeal.finprod_heightOneSpectrum_factorization'
          (K := W.FunctionField) hL0).symm
    _ = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing,
          (v.asIdeal : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^
            FractionalIdeal.count W.FunctionField v
              (FractionalIdeal.spanSingleton W.CoordinateRing⁰
                  (pointEval (constHom W) hpn.left z) *
                fiberProd W val (sec 0) ^ Multiset.card D) :=
        finprod_congr fun v => by rw [hcounts v]
    _ = FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left z) *
        fiberProd W val (sec 0) ^ Multiset.card D :=
        FractionalIdeal.finprod_heightOneSpectrum_factorization'
          (K := W.FunctionField) hR0

/-- **L4-7 substrate brick (PROVEN): point-adic multiplicities on the
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

Proof.  `mult S I` is mathlib's `FractionalIdeal.count`, the exponent
of a height-one prime in the factorization of `I`, taken at the prime
`pointIdeal W S` (and `0` at `S = O`, where nothing is claimed): the
three properties are then `FractionalIdeal.count_mul`, `count_self`
and `count_maximal_coprime` (plus `count_one` at `R = O`, where
`pointIdeal' W O = 1`).

Three inputs feed that.  (i) `pointIdeal W S` is a height-one prime
for `S ≠ O`: it is maximal by `xyIdeal_isMaximal` (the weak
Nullstellensatz through `CoordinateRing.quotientXYIdealEquiv`, which
exhibits `F[W]/pointIdeal W S ≃ F`), hence prime, and it is nonzero
because it contains the nonzero vertical `CoordinateRing.XClass W x`.
(ii) Distinct points give distinct point ideals — needed to separate
`S` from `R`: equal point ideals give equal unit fractional ideals
(`coe_pointIdeal'`), hence equal ideal classes, hence equal
`Point.toClass` values (`mk_pointIdeal'`), and `toClass` is injective.
(iii) `F[W]` IS a Dedekind domain — `isDedekindDomain_coordinateRing`,
hoisted out of this proof so the other consumers of the instance can
share it; as recorded there, it comes for free from the factorization
brick rather than from smoothness/integral closedness. -/
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
  classical
  -- ── point ideals at affine points are maximal, hence prime, and nonzero
  have hmax : ∀ S : W.Point, S ≠ 0 → (pointIdeal W S).IsMaximal := by
    intro S hS
    cases S with
    | zero => exact absurd rfl hS
    | some x y h => exact xyIdeal_isMaximal h.left
  have hbot : ∀ S : W.Point, S ≠ 0 → pointIdeal W S ≠ ⊥ := by
    intro S hS
    cases S with
    | zero => exact absurd rfl hS
    | some x y h =>
      intro hc
      have hmem : CoordinateRing.XClass W x ∈ pointIdeal W
          (WeierstrassCurve.Affine.Point.some x y h) := by
        rw [pointIdeal_some, CoordinateRing.XYIdeal]
        exact Ideal.subset_span (Set.mem_insert _ _)
      rw [hc, Ideal.mem_bot] at hmem
      exact CoordinateRing.XClass_ne_zero x hmem
  -- ── distinct points have distinct point ideals (`toClass` is injective)
  have hinj : ∀ S R : W.Point, pointIdeal W R = pointIdeal W S → R = S := by
    intro S R hRS
    have h2 : pointIdeal' W R = pointIdeal' W S :=
      Units.ext (by rw [coe_pointIdeal', coe_pointIdeal', hRS])
    have h3 : Additive.toMul (Point.toClass R) = Additive.toMul (Point.toClass S) := by
      rw [← mk_pointIdeal', ← mk_pointIdeal', h2]
    exact Point.toClass_injective (Additive.toMul.injective h3)
  -- ── `F[W]` is a Dedekind domain (the factorization brick, hoisted)
  haveI := isDedekindDomain_coordinateRing hΔ
  -- ── the multiplicity: the `(pointIdeal W S)`-adic count
  refine ⟨fun S I => if hS : S = 0 then 0 else
    FractionalIdeal.count W.FunctionField
      ⟨pointIdeal W S, (hmax S hS).isPrime, hbot S hS⟩ I, ?_, ?_, ?_⟩
  · intro S I J hI hJ
    by_cases hS : S = 0
    · simp only [dif_pos hS, add_zero]
    · simp only [dif_neg hS]
      exact FractionalIdeal.count_mul _ _ hI.ne_zero hJ.ne_zero
  · intro S hS
    simp only [dif_neg hS, coe_pointIdeal']
    exact FractionalIdeal.count_self W.FunctionField _
  · intro S R hS hRS
    simp only [dif_neg hS, coe_pointIdeal']
    by_cases hR : R = 0
    · subst hR
      rw [pointIdeal_zero, FractionalIdeal.coeIdeal_top]
      exact FractionalIdeal.count_one W.FunctionField _
    · refine FractionalIdeal.count_maximal_coprime W.FunctionField _
        (w := ⟨pointIdeal W R, (hmax R hR).isPrime, hbot R hR⟩) ?_
      intro hc
      exact hRS (hinj S R (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hc))

omit [DecidableEq F] [IsAlgClosed F] in
/-- **L4-7 substrate brick (PROVEN): a point-adic multiplicity of a
product of point ideals counts the copies of the point.**  Stated over
an abstract multiplicity `mult` with exactly the three properties
`exists_pointMult` supplies, so that it transfers unchanged to
`FractionalIdeal.count`.  Induction on the multiset: the point ideals
are units (`pointIdeal'`), so `mult S` is additive across the product
(`hmul`), and each factor contributes `1` or `0` by `hself`/`hother`. -/
lemma mult_prod_pointIdeal' [DecidableEq W.Point]
    {mult : W.Point → FractionalIdeal W.CoordinateRing⁰ W.FunctionField → ℤ}
    (hmul : ∀ (S : W.Point)
      (I J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField),
      IsUnit I → IsUnit J → mult S (I * J) = mult S I + mult S J)
    (hself : ∀ S : W.Point, S ≠ 0 →
      mult S (pointIdeal' W S :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = 1)
    (hother : ∀ S R : W.Point, S ≠ 0 → R ≠ S →
      mult S (pointIdeal' W R :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = 0)
    {S : W.Point} (hS : S ≠ 0) (M : Multiset W.Point) :
    mult S ((M.map fun R =>
      (pointIdeal' W R :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod) =
      (Multiset.count S M : ℤ) := by
  have hone : mult S 1 = 0 := by
    have h1 := hmul S 1 1 isUnit_one isUnit_one
    rw [one_mul] at h1
    omega
  induction M using Multiset.induction with
  | empty => simpa using hone
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

omit [Fact p.Prime] [IsAlgClosed F] in
/-- **L4-7 substrate brick (PROVEN): a point-adic multiplicity of a
`[p]`-fiber product is `1` exactly on the fiber through the point.**
Stated over the same abstract multiplicity as `mult_prod_pointIdeal'`.
Since `i ↦ T + val i` is injective with image the whole `[p]`-fiber
through `T`, the point `S` occurs in the fiber multiset exactly once
when `p • S = p • T` and not at all otherwise; `mult_prod_pointIdeal'`
converts that count into the multiplicity. -/
lemma mult_fiberProd {ι : Type*} [Fintype ι] {val : ι → W.Point}
    (hval_inj : Function.Injective val)
    (hval_tor : ∀ i, (p : ℤ) • val i = 0)
    (hval_surj : ∀ Q : W.Point, (p : ℤ) • Q = 0 → ∃ i, val i = Q)
    {mult : W.Point → FractionalIdeal W.CoordinateRing⁰ W.FunctionField → ℤ}
    (hmul : ∀ (S : W.Point)
      (I J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField),
      IsUnit I → IsUnit J → mult S (I * J) = mult S I + mult S J)
    (hself : ∀ S : W.Point, S ≠ 0 →
      mult S (pointIdeal' W S :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = 1)
    (hother : ∀ S R : W.Point, S ≠ 0 → R ≠ S →
      mult S (pointIdeal' W R :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = 0)
    {S T : W.Point} [Decidable ((p : ℤ) • S = (p : ℤ) • T)] (hS : S ≠ 0) :
    mult S (fiberProd W val T) =
      (if (p : ℤ) • S = (p : ℤ) • T then (1 : ℤ) else 0) := by
  classical
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
  rw [hunf, mult_prod_pointIdeal' hmul hself hother hS]
  by_cases hpST : (p : ℤ) • S = (p : ℤ) • T
  · have hnd : (Finset.univ.val.map fun i => T + val i).Nodup :=
      Multiset.Nodup.map (fun i j hij => hval_inj (add_left_cancel hij))
        Finset.univ.nodup
    simp [hpST, Multiset.count_eq_one_of_mem hnd (hmem.mpr hpST)]
  · rw [if_neg hpST]
    exact_mod_cast Multiset.count_eq_zero_of_notMem fun hc => hpST (hmem.mp hc)

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
        (if (p : ℤ) • S = (p : ℤ) • T then (1 : ℤ) else 0) :=
    fun S T hS => mult_fiberProd hval_inj hval_tor hval_surj hmul hself hother hS
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
