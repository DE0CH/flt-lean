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
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Fermat.FLT.EllipticCurve.TorsionCard
import Fermat.FLT.EllipticCurve.TorsionCardSep

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
`Φ_p(a) = x·ΨSq_p(a)`).  What is left after all of this is
`rootMultiplicity_Φ_sub_C_mul_ΨSq` below — itself now derived from the
universal polynomial identity `sq_wronskian_mul_Ψ₂Sq` (`[p]^*ω = p·ω`)
plus the characteristic-`2` residue
`rootMultiplicity_Φ_sub_C_mul_ΨSq_of_Ψ₂Sq_inseparable`. -/

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

/-! ### The invariant differential `[n]^*ω = n·ω`

Self-contained development, over an ARBITRARY base field and with no
reference to the rest of this file, of the derivation `D` on `Frac L[E]`
with `Dx = ψ₂`, of the additivity of the resulting speed function on
`(curveK E).Point`, and of the resulting universal polynomial identity
`sq_wronskian_mul_Ψ₂Sq` below. -/

namespace InvariantDifferential

universe u

open _root_.Polynomial _root_.TrivSqZeroExt

/-! ### The two group-law branches, as pure field algebra -/

/-- **Secant branch.** -/
theorem tang_secant_aux {K : Type*} [Field K]
    (a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ c₁ c₂ l dl x₃ ny₃ y₃ : K)
    (hx : x₁ - x₂ ≠ 0)
    (he₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (he₂ : y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆)
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (hdl : dl * (x₁ - x₂) =
      (c₁ * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) -
        c₂ * (3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂)) -
      l * (c₁ * (2 * y₁ + a₁ * x₁ + a₃) - c₂ * (2 * y₂ + a₁ * x₂ + a₃)))
    (hx₃ : x₃ = l ^ 2 + a₁ * l - a₂ - x₁ - x₂)
    (hny₃ : ny₃ = l * (x₃ - x₁) + y₁)
    (hy₃ : y₃ = -ny₃ - a₁ * x₃ - a₃) :
    ((2 * l + a₁) * dl - c₁ * (2 * y₁ + a₁ * x₁ + a₃) - c₂ * (2 * y₂ + a₁ * x₂ + a₃) =
        (c₁ + c₂) * (2 * y₃ + a₁ * x₃ + a₃)) ∧
      (-(dl * (x₃ - x₁) +
            l * (((2 * l + a₁) * dl - c₁ * (2 * y₁ + a₁ * x₁ + a₃) -
              c₂ * (2 * y₂ + a₁ * x₂ + a₃)) - c₁ * (2 * y₁ + a₁ * x₁ + a₃)) +
            c₁ * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁)) -
          a₁ * ((2 * l + a₁) * dl - c₁ * (2 * y₁ + a₁ * x₁ + a₃) -
            c₂ * (2 * y₂ + a₁ * x₂ + a₃)) =
        (c₁ + c₂) * (3 * x₃ ^ 2 + 2 * a₂ * x₃ + a₄ - a₁ * y₃)) := by
  subst hx₃ hny₃ hy₃
  have hl' : l = (y₁ - y₂) / (x₁ - x₂) := by
    field_simp
    linear_combination hl
  subst hl'
  have hdl' : dl =
      ((c₁ * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) -
        c₂ * (3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂)) -
      ((y₁ - y₂) / (x₁ - x₂)) *
        (c₁ * (2 * y₁ + a₁ * x₁ + a₃) - c₂ * (2 * y₂ + a₁ * x₂ + a₃))) / (x₁ - x₂) := by
    field_simp
    field_simp at hdl
    linear_combination hdl
  subst hdl'
  have ha₆ : a₆ = y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ - (x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁) := by
    linear_combination -he₁
  subst ha₆
  have ha₄ : a₄ = ((y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ - x₁ ^ 3 - a₂ * x₁ ^ 2) -
      (y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ - x₂ ^ 3 - a₂ * x₂ ^ 2)) / (x₁ - x₂) := by
    field_simp
    linear_combination he₂ - he₁
  subst ha₄
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **Tangent (doubling) branch.**  This one is an unconditional identity:
the Weierstrass equation is not needed. -/
theorem tang_double_aux {K : Type*} [Field K]
    (a₁ a₂ a₃ a₄ x y c l dl x₃ ny₃ y₃ : K)
    (hp : 2 * y + a₁ * x + a₃ ≠ 0)
    (hl : l * (2 * y + a₁ * x + a₃) = 3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hdl : dl * (2 * y + a₁ * x + a₃) =
      c * ((6 * x + 2 * a₂) * (2 * y + a₁ * x + a₃) -
        a₁ * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)) -
      l * (2 * (c * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)) +
        a₁ * (c * (2 * y + a₁ * x + a₃))))
    (hx₃ : x₃ = l ^ 2 + a₁ * l - a₂ - x - x)
    (hny₃ : ny₃ = l * (x₃ - x) + y)
    (hy₃ : y₃ = -ny₃ - a₁ * x₃ - a₃) :
    ((2 * l + a₁) * dl - c * (2 * y + a₁ * x + a₃) - c * (2 * y + a₁ * x + a₃) =
        (c + c) * (2 * y₃ + a₁ * x₃ + a₃)) ∧
      (-(dl * (x₃ - x) +
            l * (((2 * l + a₁) * dl - c * (2 * y + a₁ * x + a₃) -
              c * (2 * y + a₁ * x + a₃)) - c * (2 * y + a₁ * x + a₃)) +
            c * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)) -
          a₁ * ((2 * l + a₁) * dl - c * (2 * y + a₁ * x + a₃) -
            c * (2 * y + a₁ * x + a₃)) =
        (c + c) * (3 * x₃ ^ 2 + 2 * a₂ * x₃ + a₄ - a₁ * y₃)) := by
  subst hx₃ hny₃ hy₃
  have hdl' : dl =
      (c * ((6 * x + 2 * a₂) * (2 * y + a₁ * x + a₃) -
        a₁ * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)) -
      l * (2 * (c * (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)) +
        a₁ * (c * (2 * y + a₁ * x + a₃)))) / (2 * y + a₁ * x + a₃) := by
    rw [eq_div_iff hp]
    linear_combination hdl
  subst hdl'
  have hl' : l = (3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) / (2 * y + a₁ * x + a₃) := by
    rw [eq_div_iff hp]
    linear_combination hl
  subst hl'
  clear hl hdl
  set pp := 2 * y + a₁ * x + a₃ with hpp
  constructor
  · field_simp
    rw [hpp]
    ring
  · field_simp
    rw [hpp]
    ring


/-! ### Reduction to the generic curve -/

section Generic

open Polynomial

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The statement of the invariant-differential identity, as a predicate. -/
def IdentityHolds (V : WeierstrassCurve A) (n : ℤ) : Prop :=
  (Polynomial.derivative (V.Φ n) * V.ΨSq n -
      V.Φ n * Polynomial.derivative (V.ΨSq n)) ^ 2 * V.Ψ₂Sq =
    Polynomial.C ((n : A) ^ 2) * V.ΨSq n *
      (Polynomial.C 4 * V.Φ n ^ 3 + Polynomial.C V.b₂ * V.Φ n ^ 2 * V.ΨSq n +
        Polynomial.C (2 * V.b₄) * V.Φ n * V.ΨSq n ^ 2 +
        Polynomial.C V.b₆ * V.ΨSq n ^ 3)

lemma identityLHS_map (V : WeierstrassCurve A) (f : A →+* B) (n : ℤ) :
    (Polynomial.derivative ((V.map f).Φ n) * (V.map f).ΨSq n -
        (V.map f).Φ n * Polynomial.derivative ((V.map f).ΨSq n)) ^ 2 * (V.map f).Ψ₂Sq =
      Polynomial.map f ((Polynomial.derivative (V.Φ n) * V.ΨSq n -
        V.Φ n * Polynomial.derivative (V.ΨSq n)) ^ 2 * V.Ψ₂Sq) := by
  simp only [WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq,
    WeierstrassCurve.map_Ψ₂Sq, ← Polynomial.derivative_map, Polynomial.map_mul,
    Polynomial.map_sub, Polynomial.map_pow]

lemma identityRHS_map (V : WeierstrassCurve A) (f : A →+* B) (n : ℤ) :
    Polynomial.C ((n : B) ^ 2) * (V.map f).ΨSq n *
        (Polynomial.C 4 * (V.map f).Φ n ^ 3 +
          Polynomial.C (V.map f).b₂ * (V.map f).Φ n ^ 2 * (V.map f).ΨSq n +
          Polynomial.C (2 * (V.map f).b₄) * (V.map f).Φ n * (V.map f).ΨSq n ^ 2 +
          Polynomial.C (V.map f).b₆ * (V.map f).ΨSq n ^ 3) =
      Polynomial.map f (Polynomial.C ((n : A) ^ 2) * V.ΨSq n *
        (Polynomial.C 4 * V.Φ n ^ 3 + Polynomial.C V.b₂ * V.Φ n ^ 2 * V.ΨSq n +
          Polynomial.C (2 * V.b₄) * V.Φ n * V.ΨSq n ^ 2 +
          Polynomial.C V.b₆ * V.ΨSq n ^ 3)) := by
  simp only [WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq,
    WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C,
    map_mul, map_pow, map_intCast, map_ofNat, Polynomial.map_ofNat,
    Polynomial.map_intCast]

lemma identityHolds_map (V : WeierstrassCurve A) (f : A →+* B) (n : ℤ)
    (h : IdentityHolds V n) : IdentityHolds (V.map f) n := by
  rw [IdentityHolds, identityLHS_map, identityRHS_map, h]

lemma identityHolds_of_map (V : WeierstrassCurve A) (f : A →+* B)
    (hf : Function.Injective f) (n : ℤ) (h : IdentityHolds (V.map f) n) :
    IdentityHolds V n := by
  rw [IdentityHolds, identityLHS_map, identityRHS_map] at h
  exact Polynomial.map_injective f hf h

/-- The generic Weierstrass curve over `MvPolynomial (Fin 5) M`. -/
noncomputable def genericCurve (M : Type*) [CommRing M] :
    WeierstrassCurve (MvPolynomial (Fin 5) M) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3,
    MvPolynomial.X 4⟩

/-- The specialization of the generic curve at a given curve's coefficients. -/
noncomputable def genericEval {M : Type*} [CommRing M] (V : WeierstrassCurve M) :
    MvPolynomial (Fin 5) M →+* M :=
  MvPolynomial.eval ![V.a₁, V.a₂, V.a₃, V.a₄, V.a₆]

lemma genericCurve_map_eval {M : Type*} [CommRing M] (V : WeierstrassCurve M) :
    (genericCurve M).map (genericEval V) = V := by
  cases V
  simp only [genericCurve, genericEval, WeierstrassCurve.map, MvPolynomial.eval_X,
    WeierstrassCurve.mk.injEq]
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A specialization witnessing that the generic discriminant is nonzero:
`a₁ = 1`, `a₂ = a₃ = a₄ = 0`, `a₆ = t`, for which `Δ = −t − 432t²`. -/
noncomputable def genericSpec (M : Type*) [CommRing M] :
    MvPolynomial (Fin 5) M →+* Polynomial M :=
  MvPolynomial.eval₂Hom Polynomial.C ![1, 0, 0, 0, Polynomial.X]

lemma genericCurve_Δ_ne_zero (M : Type*) [Field M] : (genericCurve M).Δ ≠ 0 := by
  intro h0
  have h2 : ((genericCurve M).map (genericSpec M)).Δ =
      -Polynomial.X - 432 * Polynomial.X ^ 2 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, genericCurve, genericSpec,
      WeierstrassCurve.map, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    ring
  have h1 : ((genericCurve M).map (genericSpec M)).Δ = 0 := by
    rw [WeierstrassCurve.map_Δ, h0, map_zero]
  rw [h2] at h1
  have h3 : (-Polynomial.X - 432 * Polynomial.X ^ 2 : Polynomial M).coeff 1 = -1 := by
    simp
  rw [h1, Polynomial.coeff_zero] at h3
  exact one_ne_zero (neg_eq_zero.mp h3.symm)

/-- **Reduction to the nonsingular case**: an identity of this shape holding for
every curve of nonzero discriminant over every field holds for every curve. -/
theorem identityHolds_of_generic {M : Type u} [Field M]
    (H : ∀ (K : Type u) [Field K] (V : WeierstrassCurve K) (m : ℤ),
      V.Δ ≠ 0 → ((m : ℤ) : K) ≠ 0 → IdentityHolds V m)
    (V : WeierstrassCurve M) (n : ℤ) (hn : ((n : ℤ) : M) ≠ 0) : IdentityHolds V n := by
  have hnR : ((n : ℤ) : MvPolynomial (Fin 5) M) ≠ 0 := by
    rw [show ((n : ℤ) : MvPolynomial (Fin 5) M) =
        (MvPolynomial.C : M →+* MvPolynomial (Fin 5) M) ((n : ℤ) : M) from
      (map_intCast (MvPolynomial.C : M →+* MvPolynomial (Fin 5) M) n).symm]
    intro hc
    exact hn (MvPolynomial.C_injective (Fin 5) M (by rw [hc, map_zero]))
  have hinj := IsFractionRing.injective (MvPolynomial (Fin 5) M)
    (FractionRing (MvPolynomial (Fin 5) M))
  have hgen : IdentityHolds (genericCurve M) n := by
    refine identityHolds_of_map _ (algebraMap (MvPolynomial (Fin 5) M)
      (FractionRing (MvPolynomial (Fin 5) M))) hinj n ?_
    refine H _ _ n ?_ ?_
    · rw [WeierstrassCurve.map_Δ]
      exact fun hc => genericCurve_Δ_ne_zero M (hinj (by rw [hc, map_zero]))
    · intro hc
      exact hnR (hinj (by rw [map_intCast, hc, map_zero]))
  rw [← genericCurve_map_eval V]
  exact identityHolds_map _ _ n hgen


end Generic

/-- Transport of points along an equality of curves. -/
def castPointAux {L : Type*} [Field L] [DecidableEq L]
    {W₁ W₂ : WeierstrassCurve.Affine L} (h : W₁ = W₂) : W₁.Point → W₂.Point :=
  fun P => h ▸ P

lemma castPointAux_some {L : Type*} [Field L] [DecidableEq L]
    {W₁ W₂ : WeierstrassCurve.Affine L} (h : W₁ = W₂) {x y : L}
    (hn : W₁.Nonsingular x y) :
    castPointAux h (.some x y hn) = .some x y (h ▸ hn) := by subst h; rfl

lemma castPointAux_zsmul {L : Type*} [Field L] [DecidableEq L]
    {W₁ W₂ : WeierstrassCurve.Affine L} (h : W₁ = W₂) (n : ℤ) (P : W₁.Point) :
    castPointAux h (n • P) = n • castPointAux h P := by subst h; rfl

/-! ### The function-field substrate, over an arbitrary base field -/

section Main

variable {L : Type*} [Field L] (E : WeierstrassCurve.Affine L)

noncomputable scoped instance instDecEqFunctionField : DecidableEq E.FunctionField :=
  Classical.decEq _

/-- The constants embedding `L → K = Frac L[E]`. -/
noncomputable def constHom : L →+* E.FunctionField :=
  (algebraMap E.CoordinateRing E.FunctionField).comp
    ((CoordinateRing.mk E).comp
      ((Polynomial.C : Polynomial L →+* Polynomial (Polynomial L)).comp
        (Polynomial.C : L →+* Polynomial L)))

/-- The tautological `x`-coordinate. -/
noncomputable def tautX : E.FunctionField :=
  algebraMap E.CoordinateRing E.FunctionField
    (CoordinateRing.mk E (Polynomial.C Polynomial.X))

/-- The tautological `y`-coordinate. -/
noncomputable def tautY : E.FunctionField :=
  algebraMap E.CoordinateRing E.FunctionField (CoordinateRing.mk E Polynomial.X)

/-- The curve base-changed to its own function field. -/
noncomputable def curveK : WeierstrassCurve.Affine E.FunctionField :=
  (E.map (constHom E)).toAffine

theorem taut_equation : (curveK E).Equation (tautX E) (tautY E) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h : (algebraMap E.CoordinateRing E.FunctionField) (CoordinateRing.mk E
      (Polynomial.X ^ 2 + Polynomial.C (Polynomial.C E.a₁ * Polynomial.X +
        Polynomial.C E.a₃) * Polynomial.X -
      Polynomial.C (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 +
        Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆))) = 0 := by
    show (algebraMap E.CoordinateRing E.FunctionField)
      (CoordinateRing.mk E E.polynomial) = 0
    rw [AdjoinRoot.mk_self, map_zero]
  simp only [map_add, map_sub, map_mul, map_pow] at h
  show tautY E ^ 2 + (curveK E).a₁ * tautX E * tautY E + (curveK E).a₃ * tautY E =
    tautX E ^ 3 + (curveK E).a₂ * tautX E ^ 2 + (curveK E).a₄ * tautX E +
      (curveK E).a₆
  simp only [curveK, WeierstrassCurve.map, constHom, RingHom.coe_comp,
    Function.comp_apply, tautX, tautY] at h ⊢
  linear_combination h

theorem curveK_Δ_ne_zero (hΔ : E.Δ ≠ 0) : (curveK E).Δ ≠ 0 := by
  intro hc
  rw [curveK, WeierstrassCurve.map_Δ] at hc
  exact hΔ ((constHom E).injective (hc.trans (map_zero (constHom E)).symm))

theorem taut_nonsingular (hΔ : E.Δ ≠ 0) :
    (curveK E).Nonsingular (tautX E) (tautY E) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (curveK_Δ_ne_zero E hΔ)).mp (taut_equation E)

/-! ### The tangent data at a point -/

/-- `ψ₂` evaluated at a point of the base-changed curve: `2y + a₁x + a₃`. -/
noncomputable def psiAt (x y : E.FunctionField) : E.FunctionField :=
  2 * y + constHom E E.a₁ * x + constHom E E.a₃

/-- `−W_X` evaluated at a point: `3x² + 2a₂x + a₄ − a₁y`. -/
noncomputable def qAt (x y : E.FunctionField) : E.FunctionField :=
  3 * x ^ 2 + 2 * constHom E E.a₂ * x + constHom E E.a₄ - constHom E E.a₁ * y

/-! ### The dual-number lift -/

/-- The coefficient map `L → K[ε]`. -/
noncomputable def dnCoeff : L →+* DualNumber E.FunctionField :=
  (TrivSqZeroExt.inlHom E.FunctionField E.FunctionField).comp (constHom E)

/-- The dual number `x + ψ₂ ε`. -/
noncomputable def dnGenX : DualNumber E.FunctionField :=
  TrivSqZeroExt.inl (tautX E) + TrivSqZeroExt.inr (psiAt E (tautX E) (tautY E))

/-- The dual number `y + (3x²+2a₂x+a₄−a₁y) ε`. -/
noncomputable def dnGenY : DualNumber E.FunctionField :=
  TrivSqZeroExt.inl (tautY E) + TrivSqZeroExt.inr (qAt E (tautX E) (tautY E))

/-- Base map `L[X] → K[ε]` sending `X ↦ x + ψ₂ ε`. -/
noncomputable def dnBase : Polynomial L →+* DualNumber E.FunctionField :=
  Polynomial.eval₂RingHom (dnCoeff E) (dnGenX E)

@[simp] lemma fst_dnGenX : (dnGenX E).fst = tautX E := by
  simp [dnGenX]

@[simp] lemma snd_dnGenX : (dnGenX E).snd = psiAt E (tautX E) (tautY E) := by
  simp [dnGenX]

@[simp] lemma fst_dnGenY : (dnGenY E).fst = tautY E := by
  simp [dnGenY]

@[simp] lemma snd_dnGenY : (dnGenY E).snd = qAt E (tautX E) (tautY E) := by
  simp [dnGenY]

@[simp] lemma fst_dnCoeff (c : L) : (dnCoeff E c).fst = constHom E c := by
  simp [dnCoeff]

@[simp] lemma snd_dnCoeff (c : L) : (dnCoeff E c).snd = 0 := by
  simp [dnCoeff]

/-- **The defining polynomial dies in the dual numbers**: its `ε`-part is
`W_X·ψ₂ + W_Y·(−W_X) = 0`. -/
theorem eval₂_polynomial_dn :
    E.polynomial.eval₂ (dnBase E) (dnGenY E) = 0 := by
  have heq := taut_equation E
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [curveK, WeierstrassCurve.map] at heq
  simp only [WeierstrassCurve.Affine.polynomial, dnBase, eval₂_add, eval₂_sub, eval₂_mul,
    eval₂_pow, eval₂_C, eval₂_X, Polynomial.coe_eval₂RingHom]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub,
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero, fst_dnGenX, fst_dnGenY, fst_dnCoeff]
    linear_combination heq
  · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub,
      TrivSqZeroExt.snd_pow, TrivSqZeroExt.snd_zero, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_pow, fst_dnGenX, fst_dnGenY, fst_dnCoeff,
      snd_dnGenX, snd_dnGenY, snd_dnCoeff, smul_zero, op_smul_eq_smul, smul_eq_mul,
      nsmul_eq_mul, show Nat.pred 2 = 1 from rfl, show Nat.pred 3 = 2 from rfl,
      pow_one, psiAt, qAt]
    push_cast
    ring

/-- Evaluation of a bivariate polynomial at the tautological point. -/
noncomputable def evalTaut : Polynomial (Polynomial L) →+* E.FunctionField :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (constHom E) (tautX E)) (tautY E)

theorem evalTaut_eq :
    evalTaut E =
      (algebraMap E.CoordinateRing E.FunctionField).comp (CoordinateRing.mk E) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have h : ((evalTaut E).comp Polynomial.C) =
        (((algebraMap E.CoordinateRing E.FunctionField).comp
          (CoordinateRing.mk E)).comp Polynomial.C) := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, evalTaut,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        rfl
      · simp only [RingHom.coe_comp, Function.comp_apply, evalTaut,
          Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
        rfl
    exact RingHom.congr_fun h a
  · simp only [evalTaut, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      RingHom.coe_comp, Function.comp_apply]
    rfl

/-- The `fst`-component of the base map is evaluation at `tautX`. -/
theorem fstHom_comp_dnBase :
    ((TrivSqZeroExt.fstHom E.FunctionField E.FunctionField
        E.FunctionField).toRingHom).comp (dnBase E) =
      Polynomial.eval₂RingHom (constHom E) (tautX E) := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_ <;>
    simp [dnBase, TrivSqZeroExt.fstHom]

/-- The dual-number lift of the coordinate ring. -/
noncomputable def cdiff : E.CoordinateRing →+* DualNumber E.FunctionField :=
  AdjoinRoot.lift (dnBase E) (dnGenY E) (eval₂_polynomial_dn E)

theorem fst_cdiff (z : E.CoordinateRing) :
    (cdiff E z).fst = algebraMap E.CoordinateRing E.FunctionField z := by
  induction z using AdjoinRoot.induction_on with
  | ih q =>
    have h := Polynomial.hom_eval₂ q (dnBase E)
      (TrivSqZeroExt.fstHom E.FunctionField E.FunctionField
        E.FunctionField).toRingHom (dnGenY E)
    have h2 : (TrivSqZeroExt.fstHom E.FunctionField E.FunctionField
        E.FunctionField).toRingHom (dnGenY E) = tautY E := fst_dnGenY E
    have h3 := RingHom.congr_fun (evalTaut_eq E) q
    show (cdiff E (CoordinateRing.mk E q)).fst = _
    rw [cdiff, AdjoinRoot.lift_mk,
      show (q.eval₂ (dnBase E) (dnGenY E)).fst =
        (TrivSqZeroExt.fstHom E.FunctionField E.FunctionField
          E.FunctionField).toRingHom (q.eval₂ (dnBase E) (dnGenY E)) from rfl,
      h, fstHom_comp_dnBase, h2]
    exact h3

theorem isUnit_cdiff (y : E.CoordinateRing⁰) : IsUnit (cdiff E (y : E.CoordinateRing)) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_cdiff]
  refine isUnit_iff_ne_zero.mpr ?_
  simp only [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective E.CoordinateRing E.FunctionField)]
  exact ( nonZeroDivisors.coe_ne_zero y)

/-- The dual-number lift of the function field. -/
noncomputable def kdiff : E.FunctionField →+* DualNumber E.FunctionField :=
  IsLocalization.lift (isUnit_cdiff E)

theorem fst_kdiff (z : E.FunctionField) : (kdiff E z).fst = z := by
  have hext : ((TrivSqZeroExt.fstHom E.FunctionField E.FunctionField
      E.FunctionField).toRingHom).comp (kdiff E) = RingHom.id E.FunctionField := by
    refine IsLocalization.ringHom_ext E.CoordinateRing⁰ ?_
    refine RingHom.ext (fun a => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, kdiff, IsLocalization.lift_eq,
      RingHom.id_apply]
    exact fst_cdiff E a
  exact RingHom.congr_fun hext z

/-- The derivation `D` on the function field with `Dx = ψ₂`. -/
noncomputable def derivK (z : E.FunctionField) : E.FunctionField := (kdiff E z).snd

/-! ### Derivation calculus -/

@[simp] lemma curveK_a₁ : (curveK E).a₁ = constHom E E.a₁ := rfl
@[simp] lemma curveK_a₂ : (curveK E).a₂ = constHom E E.a₂ := rfl
@[simp] lemma curveK_a₃ : (curveK E).a₃ = constHom E E.a₃ := rfl
@[simp] lemma curveK_a₄ : (curveK E).a₄ = constHom E E.a₄ := rfl
@[simp] lemma curveK_a₆ : (curveK E).a₆ = constHom E E.a₆ := rfl

lemma kdiff_algebraMap (z : E.CoordinateRing) :
    kdiff E (algebraMap E.CoordinateRing E.FunctionField z) = cdiff E z :=
  IsLocalization.lift_eq _ z

lemma cdiff_mk (q : Polynomial (Polynomial L)) :
    cdiff E (CoordinateRing.mk E q) = q.eval₂ (dnBase E) (dnGenY E) :=
  AdjoinRoot.lift_mk (eval₂_polynomial_dn E) q

@[simp] lemma derivK_zero : derivK E 0 = 0 := by
  simp [derivK]

@[simp] lemma derivK_add (a b : E.FunctionField) :
    derivK E (a + b) = derivK E a + derivK E b := by
  simp [derivK, TrivSqZeroExt.snd_add]

@[simp] lemma derivK_neg (a : E.FunctionField) : derivK E (-a) = -derivK E a := by
  simp [derivK]

@[simp] lemma derivK_sub (a b : E.FunctionField) :
    derivK E (a - b) = derivK E a - derivK E b := by
  simp [derivK, TrivSqZeroExt.snd_sub]

lemma derivK_mul (a b : E.FunctionField) :
    derivK E (a * b) = a * derivK E b + b * derivK E a := by
  simp only [derivK, map_mul, TrivSqZeroExt.snd_mul, fst_kdiff, op_smul_eq_smul,
    smul_eq_mul]

lemma derivK_constHom (c : L) : derivK E (constHom E c) = 0 := by
  show (kdiff E (constHom E c)).snd = 0
  rw [show constHom E c = algebraMap E.CoordinateRing E.FunctionField
      (CoordinateRing.mk E (Polynomial.C (Polynomial.C c))) from rfl,
    kdiff_algebraMap, cdiff_mk]
  simp [dnBase]

@[simp] lemma derivK_one : derivK E 1 = 0 := by
  have h : (1 : E.FunctionField) = constHom E 1 := (map_one _).symm
  rw [h, derivK_constHom]

@[simp] lemma derivK_ofNat (n : ℕ) [n.AtLeastTwo] :
    derivK E (OfNat.ofNat n : E.FunctionField) = 0 := by
  have h : (OfNat.ofNat n : E.FunctionField) = constHom E (OfNat.ofNat n) :=
    (map_ofNat _ n).symm
  rw [h, derivK_constHom]

@[simp] lemma derivK_two : derivK E 2 = 0 := by
  have h : (2 : E.FunctionField) = constHom E 2 := (map_ofNat _ 2).symm
  rw [h, derivK_constHom]

@[simp] lemma derivK_three : derivK E 3 = 0 := by
  have h : (3 : E.FunctionField) = constHom E 3 := (map_ofNat _ 3).symm
  rw [h, derivK_constHom]

@[simp] lemma derivK_six : derivK E 6 = 0 := by
  have h : (6 : E.FunctionField) = constHom E 6 := (map_ofNat _ 6).symm
  rw [h, derivK_constHom]

lemma derivK_tautX : derivK E (tautX E) = psiAt E (tautX E) (tautY E) := by
  show (kdiff E (tautX E)).snd = _
  rw [show tautX E = algebraMap E.CoordinateRing E.FunctionField
      (CoordinateRing.mk E (Polynomial.C Polynomial.X)) from rfl,
    kdiff_algebraMap, cdiff_mk]
  simp only [Polynomial.eval₂_C, dnBase, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X, snd_dnGenX]
  rfl

lemma derivK_tautY : derivK E (tautY E) = qAt E (tautX E) (tautY E) := by
  show (kdiff E (tautY E)).snd = _
  rw [show tautY E = algebraMap E.CoordinateRing E.FunctionField
      (CoordinateRing.mk E Polynomial.X) from rfl,
    kdiff_algebraMap, cdiff_mk]
  simp only [Polynomial.eval₂_X, snd_dnGenY]
  rfl

/-- The `derivK`-image of a `constHom`-scalar multiple. -/
lemma derivK_constHom_mul (c : L) (a : E.FunctionField) :
    derivK E (constHom E c * a) = constHom E c * derivK E a := by
  rw [derivK_mul, derivK_constHom, mul_zero, add_zero]

/-! ### Derivation of the group-law formulas -/

lemma derivK_sq (a : E.FunctionField) : derivK E (a ^ 2) = 2 * a * derivK E a := by
  rw [pow_two, derivK_mul]; ring

lemma negY_eq (x y : E.FunctionField) :
    (curveK E).negY x y = -y - constHom E E.a₁ * x - constHom E E.a₃ := rfl

lemma derivK_negY (x y : E.FunctionField) :
    derivK E ((curveK E).negY x y) = -derivK E y - constHom E E.a₁ * derivK E x := by
  rw [negY_eq, derivK_sub, derivK_sub, derivK_neg, derivK_constHom_mul,
    derivK_constHom, sub_zero]

lemma derivK_addX (x₁ x₂ l : E.FunctionField) :
    derivK E ((curveK E).addX x₁ x₂ l) =
      (2 * l + constHom E E.a₁) * derivK E l - derivK E x₁ - derivK E x₂ := by
  show derivK E (l ^ 2 + constHom E E.a₁ * l - constHom E E.a₂ - x₁ - x₂) = _
  rw [derivK_sub, derivK_sub, derivK_sub, derivK_add, derivK_sq,
    derivK_constHom_mul, derivK_constHom, sub_zero]
  ring

lemma derivK_negAddY (x₁ x₂ y₁ l : E.FunctionField) :
    derivK E ((curveK E).negAddY x₁ x₂ y₁ l) =
      derivK E l * ((curveK E).addX x₁ x₂ l - x₁) +
        l * (derivK E ((curveK E).addX x₁ x₂ l) - derivK E x₁) + derivK E y₁ := by
  show derivK E (l * ((curveK E).addX x₁ x₂ l - x₁) + y₁) = _
  rw [derivK_add, derivK_mul, derivK_sub]
  ring

lemma derivK_addY (x₁ x₂ y₁ l : E.FunctionField) :
    derivK E ((curveK E).addY x₁ x₂ y₁ l) =
      -derivK E ((curveK E).negAddY x₁ x₂ y₁ l) -
        constHom E E.a₁ * derivK E ((curveK E).addX x₁ x₂ l) := by
  show derivK E ((curveK E).negY _ _) = _
  rw [derivK_negY]

/-! ### The tangent predicate -/

noncomputable instance : DecidableEq E.FunctionField := Classical.decEq _

/-- `Tang E c P` says that the derivation `D` moves the point `P` at speed `c`
times the invariant vector field `(ψ₂, 3x²+2a₂x+a₄−a₁y)`. -/
def Tang (c : E.FunctionField) : (curveK E).Point → Prop
  | .zero => c = 0
  | .some x y _ => derivK E x = c * psiAt E x y ∧ derivK E y = c * qAt E x y

/-- The tautological point moves at unit speed. -/
theorem Tang_tautPoint (hns : (curveK E).Nonsingular (tautX E) (tautY E)) :
    Tang E 1 (.some (tautX E) (tautY E) hns) :=
  ⟨by rw [derivK_tautX, one_mul], by rw [derivK_tautY, one_mul]⟩

/-- **Additivity of the speed.**  This is the invariance of the differential
`ω = dx/(2y+a₁x+a₃)` under translation, in tangent-vector form. -/
theorem Tang_add {c₁ c₂ : E.FunctionField} :
    ∀ {P₁ P₂ : (curveK E).Point}, Tang E c₁ P₁ → Tang E c₂ P₂ →
      Tang E (c₁ + c₂) (P₁ + P₂) := by
  rintro (_ | ⟨x₁, y₁, hns₁⟩) (_ | ⟨x₂, y₂, hns₂⟩) h₁ h₂
  · exact show c₁ + c₂ = 0 by
      rw [show c₁ = 0 from h₁, show c₂ = 0 from h₂, add_zero]
  · rw [show (Point.zero : (curveK E).Point) = 0 from rfl, zero_add,
      show c₁ = 0 from h₁, zero_add]
    exact h₂
  · rw [show (Point.zero : (curveK E).Point) = 0 from rfl, add_zero,
      show c₂ = 0 from h₂, add_zero]
    exact h₁
  obtain ⟨hDx₁, hDy₁⟩ := h₁
  obtain ⟨hDx₂, hDy₂⟩ := h₂
  have hns₁' := hns₁.2
  rw [WeierstrassCurve.Affine.evalEval_polynomialX,
    WeierstrassCurve.Affine.evalEval_polynomialY] at hns₁'
  simp only [curveK_a₁, curveK_a₂, curveK_a₃, curveK_a₄] at hns₁'
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curveK E).negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
    show c₁ + c₂ = 0
    subst hx
    have hy₂ : y₂ = -y₁ - constHom E E.a₁ * x₁ - constHom E E.a₃ := by
      rw [negY_eq] at hy; linear_combination hy
    subst hy₂
    have hDy₂' : derivK E (-y₁ - constHom E E.a₁ * x₁ - constHom E E.a₃) =
        -derivK E y₁ - constHom E E.a₁ * derivK E x₁ := by
      rw [derivK_sub, derivK_sub, derivK_neg, derivK_constHom,
        derivK_constHom_mul, sub_zero]
    rw [hDy₂'] at hDy₂
    rw [hDx₁] at hDx₂
    rw [hDy₁, hDx₁] at hDy₂
    have e1 : (c₁ + c₂) * psiAt E x₁ y₁ = 0 := by
      simp only [psiAt] at hDx₂ ⊢
      linear_combination hDx₂
    have e2 : (c₁ + c₂) * qAt E x₁ y₁ = 0 := by
      simp only [psiAt, qAt] at hDy₂ e1 ⊢
      linear_combination -hDy₂ - constHom E E.a₁ * e1
    rcases hns₁' with hq | hp
    · have hq' : qAt E x₁ y₁ ≠ 0 := by
        simp only [qAt]
        intro hc
        exact hq (by linear_combination -hc)
      exact (mul_eq_zero.mp e2).resolve_right hq'
    · have hp' : psiAt E x₁ y₁ ≠ 0 := by
        simp only [psiAt]
        intro hc
        exact hp (by linear_combination hc)
      exact (mul_eq_zero.mp e1).resolve_right hp'
  · rw [WeierstrassCurve.Affine.Point.add_some hxy]
    show derivK E ((curveK E).addX x₁ x₂ _) = _ ∧ derivK E ((curveK E).addY x₁ x₂ y₁ _) = _
    rw [derivK_addX, derivK_addY, derivK_negAddY, derivK_addX, hDx₁, hDx₂, hDy₁]
    by_cases hx : x₁ = x₂
    · -- doubling branch
      have hyne : y₁ ≠ (curveK E).negY x₂ y₂ := fun hc => hxy ⟨hx, hc⟩
      have hy12 : y₁ = y₂ :=
        WeierstrassCurve.Affine.Y_eq_of_Y_ne hns₁.1 hns₂.1 hx hyne
      subst hx
      subst hy12
      have hp : psiAt E x₁ y₁ ≠ 0 := by
        simp only [psiAt]
        intro hc
        exact hyne (by rw [negY_eq]; linear_combination hc)
      have hc12 : c₁ = c₂ := mul_right_cancel₀ hp (hDx₁.symm.trans hDx₂)
      subst hc12
      have hslope : (curveK E).slope x₁ x₁ y₁ y₁ * (2 * y₁ + constHom E E.a₁ * x₁ +
          constHom E E.a₃) = 3 * x₁ ^ 2 + 2 * constHom E E.a₂ * x₁ +
            constHom E E.a₄ - constHom E E.a₁ * y₁ := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne, negY_eq,
          div_mul_eq_mul_div, div_eq_iff (by
            simp only [psiAt] at hp
            intro hc; exact hp (by linear_combination hc))]
        simp only [curveK_a₁, curveK_a₂, curveK_a₄]
        ring
      have hdl : derivK E ((curveK E).slope x₁ x₁ y₁ y₁) *
          (2 * y₁ + constHom E E.a₁ * x₁ + constHom E E.a₃) =
          c₁ * ((6 * x₁ + 2 * constHom E E.a₂) *
              (2 * y₁ + constHom E E.a₁ * x₁ + constHom E E.a₃) -
            constHom E E.a₁ * (3 * x₁ ^ 2 + 2 * constHom E E.a₂ * x₁ +
              constHom E E.a₄ - constHom E E.a₁ * y₁)) -
          (curveK E).slope x₁ x₁ y₁ y₁ *
            (2 * (c₁ * (3 * x₁ ^ 2 + 2 * constHom E E.a₂ * x₁ + constHom E E.a₄ -
                constHom E E.a₁ * y₁)) +
              constHom E E.a₁ * (c₁ * (2 * y₁ + constHom E E.a₁ * x₁ +
                constHom E E.a₃))) := by
        have hd := congrArg (derivK E) hslope
        rw [derivK_mul] at hd
        simp only [derivK_add, derivK_sub, derivK_mul, derivK_constHom, derivK_two,
          derivK_three, derivK_sq, mul_zero, add_zero] at hd
        rw [hDx₁, hDy₁] at hd
        simp only [psiAt, qAt] at hd
        linear_combination hd
      have key := tang_double_aux (constHom E E.a₁) (constHom E E.a₂) (constHom E E.a₃)
        (constHom E E.a₄) x₁ y₁ c₁ ((curveK E).slope x₁ x₁ y₁ y₁)
        (derivK E ((curveK E).slope x₁ x₁ y₁ y₁))
        ((curveK E).addX x₁ x₁ ((curveK E).slope x₁ x₁ y₁ y₁))
        ((curveK E).negAddY x₁ x₁ y₁ ((curveK E).slope x₁ x₁ y₁ y₁))
        ((curveK E).addY x₁ x₁ y₁ ((curveK E).slope x₁ x₁ y₁ y₁))
        (by simp only [psiAt] at hp; exact hp) hslope hdl rfl rfl rfl
      simp only [psiAt, qAt]
      exact ⟨by linear_combination key.1, by linear_combination key.2⟩
    · -- secant branch
      have hxs : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      have hslope : (curveK E).slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
        rw [WeierstrassCurve.Affine.slope_of_X_ne hx, div_mul_cancel₀ _ hxs]
      have hdl : derivK E ((curveK E).slope x₁ x₂ y₁ y₂) * (x₁ - x₂) =
          (c₁ * (3 * x₁ ^ 2 + 2 * constHom E E.a₂ * x₁ + constHom E E.a₄ -
              constHom E E.a₁ * y₁) -
            c₂ * (3 * x₂ ^ 2 + 2 * constHom E E.a₂ * x₂ + constHom E E.a₄ -
              constHom E E.a₁ * y₂)) -
          (curveK E).slope x₁ x₂ y₁ y₂ *
            (c₁ * (2 * y₁ + constHom E E.a₁ * x₁ + constHom E E.a₃) -
              c₂ * (2 * y₂ + constHom E E.a₁ * x₂ + constHom E E.a₃)) := by
        have hd := congrArg (derivK E) hslope
        rw [derivK_mul, derivK_sub, derivK_sub] at hd
        rw [hDx₁, hDx₂, hDy₁, hDy₂] at hd
        simp only [psiAt, qAt] at hd
        linear_combination hd
      have he₁ : y₁ ^ 2 + constHom E E.a₁ * x₁ * y₁ + constHom E E.a₃ * y₁ =
          x₁ ^ 3 + constHom E E.a₂ * x₁ ^ 2 + constHom E E.a₄ * x₁ + constHom E E.a₆ :=
        (WeierstrassCurve.Affine.equation_iff _ _).mp hns₁.1
      have he₂ : y₂ ^ 2 + constHom E E.a₁ * x₂ * y₂ + constHom E E.a₃ * y₂ =
          x₂ ^ 3 + constHom E E.a₂ * x₂ ^ 2 + constHom E E.a₄ * x₂ + constHom E E.a₆ :=
        (WeierstrassCurve.Affine.equation_iff _ _).mp hns₂.1
      have key := tang_secant_aux (constHom E E.a₁) (constHom E E.a₂) (constHom E E.a₃)
        (constHom E E.a₄) (constHom E E.a₆) x₁ y₁ x₂ y₂ c₁ c₂
        ((curveK E).slope x₁ x₂ y₁ y₂) (derivK E ((curveK E).slope x₁ x₂ y₁ y₂))
        ((curveK E).addX x₁ x₂ ((curveK E).slope x₁ x₂ y₁ y₂))
        ((curveK E).negAddY x₁ x₂ y₁ ((curveK E).slope x₁ x₂ y₁ y₂))
        ((curveK E).addY x₁ x₂ y₁ ((curveK E).slope x₁ x₂ y₁ y₂))
        hxs he₁ he₂ hslope hdl rfl rfl rfl
      simp only [psiAt, qAt]
      exact ⟨by linear_combination key.1, by linear_combination key.2⟩

/-! ### Negation, integer multiples, and the chain rule -/

lemma psiAt_negY (x y : E.FunctionField) :
    psiAt E x ((curveK E).negY x y) = -psiAt E x y := by
  simp only [psiAt, negY_eq]; ring

lemma qAt_negY (x y : E.FunctionField) :
    qAt E x ((curveK E).negY x y) = qAt E x y + constHom E E.a₁ * psiAt E x y := by
  simp only [psiAt, qAt, negY_eq]; ring

theorem Tang_neg {c : E.FunctionField} :
    ∀ {P : (curveK E).Point}, Tang E c P → Tang E (-c) (-P) := by
  rintro (_ | ⟨x, y, hns⟩) h
  · exact show -c = 0 by rw [show c = 0 from h, neg_zero]
  · obtain ⟨hDx, hDy⟩ := h
    refine ⟨?_, ?_⟩
    · rw [psiAt_negY, hDx]; ring
    · rw [derivK_negY, qAt_negY, hDx, hDy]; ring

theorem Tang_zsmul {c : E.FunctionField} {P : (curveK E).Point} (h : Tang E c P) :
    ∀ n : ℤ, Tang E ((n : E.FunctionField) * c) (n • P) := by
  intro n
  induction n using Int.induction_on with
  | zero => exact show ((0 : ℤ) : E.FunctionField) * c = 0 by simp
  | succ k ih =>
    have hadd := Tang_add E ih h
    have h1 : ((k : ℤ) + 1) • P = (k : ℤ) • P + P := by rw [add_zsmul, one_zsmul]
    have h2 : (((k : ℤ) + 1 : ℤ) : E.FunctionField) * c =
        ((k : ℤ) : E.FunctionField) * c + c := by push_cast; ring
    rw [h1, h2]
    exact hadd
  | pred k ih =>
    have hadd := Tang_add E ih (Tang_neg E h)
    have h1 : (-(k : ℤ) - 1) • P = (-(k : ℤ)) • P + -P := by
      rw [sub_zsmul, one_zsmul]
    have h2 : ((-(k : ℤ) - 1 : ℤ) : E.FunctionField) * c =
        ((-(k : ℤ) : ℤ) : E.FunctionField) * c + -c := by push_cast; ring
    rw [h1, h2]
    exact hadd

/-- One step of the chain rule. -/
lemma derivK_eval_map_step (z : E.FunctionField) (g : Polynomial L)
    (ih : derivK E ((g.map (constHom E)).eval z) =
      ((Polynomial.derivative g).map (constHom E)).eval z * derivK E z) :
    derivK E (((g * Polynomial.X).map (constHom E)).eval z) =
      ((Polynomial.derivative (g * Polynomial.X)).map (constHom E)).eval z *
        derivK E z := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_X,
    derivK_mul, ih, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  ring

/-- **Chain rule** for evaluation of a univariate polynomial over the constants. -/
lemma derivK_eval_map (z : E.FunctionField) (g : Polynomial L) :
    derivK E ((g.map (constHom E)).eval z) =
      ((Polynomial.derivative g).map (constHom E)).eval z * derivK E z := by
  induction g using Polynomial.induction_on with
  | C a => simp [derivK_constHom]
  | add p q hp hq =>
    simp only [Polynomial.map_add, Polynomial.eval_add, derivK_add, hp, hq,
      Polynomial.derivative_add]
    ring
  | monomial n a ih =>
    have hrw : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial L) =
        (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    rw [hrw]
    exact derivK_eval_map_step E z _ ih

/-- The square of `ψ₂` at a point of the curve is `Ψ₂Sq` of its abscissa. -/
lemma psiAt_sq (x y : E.FunctionField) (h : (curveK E).Equation x y) :
    psiAt E x y ^ 2 = ((E.Ψ₂Sq).map (constHom E)).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [curveK_a₁, curveK_a₂, curveK_a₃, curveK_a₄, curveK_a₆] at h
  simp only [psiAt, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, map_add, map_mul,
    map_pow, map_ofNat, Polynomial.map_ofNat, Polynomial.eval_ofNat]
  linear_combination 4 * h

/-! ### The identity at the tautological point -/

/-- Evaluation of a univariate polynomial over `L` at the tautological `x`. -/
noncomputable def evTaut1 (E : WeierstrassCurve.Affine L) :
    Polynomial L →+* E.FunctionField :=
  Polynomial.eval₂RingHom (constHom E) (tautX E)

lemma evTaut1_apply (g : Polynomial L) :
    evTaut1 E g = (g.map (constHom E)).eval (tautX E) :=
  (Polynomial.eval_map _ _).symm

lemma evTaut1_C (c : L) : evTaut1 E (Polynomial.C c) = constHom E c :=
  Polynomial.eval₂_C _ _

lemma derivK_evTaut1 (g : Polynomial L) :
    derivK E (evTaut1 E g) =
      evTaut1 E (Polynomial.derivative g) * psiAt E (tautX E) (tautY E) := by
  rw [evTaut1_apply, evTaut1_apply, derivK_eval_map, derivK_tautX]

lemma Ψ₂Sq_eval (z : E.FunctionField) :
    ((E.Ψ₂Sq).map (constHom E)).eval z =
      4 * z ^ 3 + constHom E E.b₂ * z ^ 2 + 2 * constHom E E.b₄ * z +
        constHom E E.b₆ := by
  simp only [WeierstrassCurve.Ψ₂Sq, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    map_mul, map_ofNat, Polynomial.map_ofNat, Polynomial.eval_ofNat]

/-- **The identity, evaluated at the tautological point.** -/
theorem sq_wronskian_evTaut (hns : (curveK E).Nonsingular (tautX E) (tautY E))
    {n : ℤ} {xp yp : E.FunctionField} (hpn : (curveK E).Nonsingular xp yp)
    (hsmul : (n : ℤ) • (WeierstrassCurve.Affine.Point.some (tautX E) (tautY E) hns :
        (curveK E).Point) = WeierstrassCurve.Affine.Point.some xp yp hpn)
    (hxrel : xp * evTaut1 E (E.ΨSq n) = evTaut1 E (E.Φ n)) :
    evTaut1 E ((Polynomial.derivative (E.Φ n) * E.ΨSq n -
        E.Φ n * Polynomial.derivative (E.ΨSq n)) ^ 2 * E.Ψ₂Sq) =
      evTaut1 E (Polynomial.C ((n : L) ^ 2) * E.ΨSq n *
        (Polynomial.C 4 * E.Φ n ^ 3 + Polynomial.C E.b₂ * E.Φ n ^ 2 * E.ΨSq n +
          Polynomial.C (2 * E.b₄) * E.Φ n * E.ΨSq n ^ 2 +
          Polynomial.C E.b₆ * E.ΨSq n ^ 3)) := by
  simp only [map_mul, map_add, map_sub, map_pow, evTaut1_C, map_ofNat]
  have hcast : constHom E ((n : ℤ) : L) = (n : E.FunctionField) :=
    map_intCast (constHom E) n
  rw [hcast]
  have hTang : Tang E ((n : E.FunctionField)) (WeierstrassCurve.Affine.Point.some
      xp yp hpn) := by
    have h := Tang_zsmul E (Tang_tautPoint E hns) n
    rw [mul_one, hsmul] at h
    exact h
  obtain ⟨hDxp, -⟩ := hTang
  set pt := psiAt E (tautX E) (tautY E) with hpt
  set A := evTaut1 E (E.Φ n) with hA
  set B := evTaut1 E (E.ΨSq n) with hBdef
  set A' := evTaut1 E (Polynomial.derivative (E.Φ n)) with hA'
  set B' := evTaut1 E (Polynomial.derivative (E.ΨSq n)) with hB'
  have hd := congrArg (derivK E) hxrel
  rw [derivK_mul, derivK_evTaut1, derivK_evTaut1, hDxp, ← hA', ← hB', ← hpt] at hd
  have key : (n : E.FunctionField) * psiAt E xp yp * B ^ 2 = (A' * B - A * B') * pt := by
    have h2 := congrArg (fun t => t * B) hd
    linear_combination h2 - B' * pt * hxrel
  have keysq : (n : E.FunctionField) ^ 2 * (psiAt E xp yp ^ 2) * B ^ 4 =
      (A' * B - A * B') ^ 2 * pt ^ 2 := by
    have h3 := congrArg (fun t => t ^ 2) key
    linear_combination h3
  have hptsq : pt ^ 2 = evTaut1 E E.Ψ₂Sq := by
    rw [hpt, psiAt_sq E _ _ hns.1, evTaut1_apply]
  have hppsq : psiAt E xp yp ^ 2 * B ^ 3 =
      4 * A ^ 3 + constHom E E.b₂ * A ^ 2 * B + 2 * constHom E E.b₄ * A * B ^ 2 +
        constHom E E.b₆ * B ^ 3 := by
    rw [psiAt_sq E _ _ hpn.1, Ψ₂Sq_eval]
    linear_combination (4 * (xp * B) ^ 2 + 4 * (xp * B) * A + 4 * A ^ 2 +
      constHom E E.b₂ * B * (xp * B) + constHom E E.b₂ * B * A +
      2 * constHom E E.b₄ * B ^ 2) * hxrel
  have hfinal : (A' * B - A * B') ^ 2 * evTaut1 E E.Ψ₂Sq =
      (n : E.FunctionField) ^ 2 * B *
        (4 * A ^ 3 + constHom E E.b₂ * A ^ 2 * B +
          2 * constHom E E.b₄ * A * B ^ 2 + constHom E E.b₆ * B ^ 3) := by
    rw [← hptsq, ← keysq, ← hppsq]
    ring
  linear_combination hfinal

lemma evTaut1_eq_algebraMap (g : Polynomial L) :
    evTaut1 E g = algebraMap E.CoordinateRing E.FunctionField
      (CoordinateRing.mk E (Polynomial.C g)) := by
  have h : ((evalTaut E).comp Polynomial.C) =
      (((algebraMap E.CoordinateRing E.FunctionField).comp
        (CoordinateRing.mk E)).comp Polynomial.C) := by
    rw [evalTaut_eq]
  have hEq : evTaut1 E g = evalTaut E (Polynomial.C g) := by
    simp only [evalTaut, evTaut1, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rw [hEq]
  exact RingHom.congr_fun h g

/-- **Transcendence of the tautological `x`** over the constants: a nonzero
univariate polynomial does not vanish at `tautX`.  `L[E]` is free of rank `2`
over `L[X]`, so `L[X] → L[E]` is injective. -/
theorem evTaut1_injective : Function.Injective (evTaut1 E) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  rw [evTaut1_eq_algebraMap] at hg
  have h0 : CoordinateRing.mk E (Polynomial.C g) = 0 :=
    (IsFractionRing.injective E.CoordinateRing E.FunctionField)
      (by rw [hg, map_zero])
  have hdvd : E.polynomial ∣ Polynomial.C g := AdjoinRoot.mk_eq_zero.mp h0
  by_contra hne
  have hCne : (Polynomial.C g : Polynomial (Polynomial L)) ≠ 0 := by
    simpa using hne
  have hle := Polynomial.natDegree_le_of_dvd hdvd hCne
  rw [WeierstrassCurve.Affine.natDegree_polynomial, Polynomial.natDegree_C] at hle
  omega


/-! ### The identity for a curve of nonzero discriminant -/

/-- `n • taut` is affine and its abscissa satisfies `x·ΨSq_n = Φ_n`. -/
theorem exists_smul_taut (hΔ : E.Δ ≠ 0) {n : ℤ} (hn : ((n : ℤ) : L) ≠ 0) :
    ∃ (xp yp : E.FunctionField) (hpn : (curveK E).Nonsingular xp yp),
      (n : ℤ) • (WeierstrassCurve.Affine.Point.some (tautX E) (tautY E)
          (taut_nonsingular E hΔ) : (curveK E).Point) =
        WeierstrassCurve.Affine.Point.some xp yp hpn ∧
      xp * evTaut1 E (E.ΨSq n) = evTaut1 E (E.Φ n) := by
  haveI : (E.map (constHom E)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (curveK_Δ_ne_zero E hΔ)⟩
  have hnZ : n ≠ 0 := by
    intro h0; exact hn (by rw [h0]; simp)
  have hcast : ((E.map (constHom E)).baseChange E.FunctionField).toAffine =
      curveK E := WeierstrassCurve.map_id _
  have hΨbridge :
      ((E.map (constHom E)).baseChange E.FunctionField).ΨSq n =
        (E.ΨSq n).map (constHom E) := by
    rw [show (E.map (constHom E)).baseChange E.FunctionField = E.map (constHom E) from
      WeierstrassCurve.map_id _, WeierstrassCurve.map_ΨSq]
  have hΦbridge :
      ((E.map (constHom E)).baseChange E.FunctionField).Φ n =
        (E.Φ n).map (constHom E) := by
    rw [show (E.map (constHom E)).baseChange E.FunctionField = E.map (constHom E) from
      WeierstrassCurve.map_id _, WeierstrassCurve.map_Φ]
  have hnsE : ((E.map (constHom E)).baseChange
      E.FunctionField).toAffine.Nonsingular (tautX E) (tautY E) := by
    rw [hcast]; exact taut_nonsingular E hΔ
  have hΨx : ((((E.map (constHom E)).baseChange E.FunctionField).ΨSq
      n).eval (tautX E)) ≠ 0 := by
    rw [hΨbridge, ← evTaut1_apply]
    intro hc
    exact E.ΨSq_ne_zero hn ((injective_iff_map_eq_zero _).mp (evTaut1_injective E) _ hc)
  obtain ⟨xp, yp, hpn', heq, hx⟩ :=
    TorsionCard.exists_smul_some_eq (E.map (constHom E)) hnZ hnsE hΨx
  refine ⟨xp, yp, hcast ▸ hpn', ?_, ?_⟩
  · have h1 := congrArg (castPointAux hcast) heq
    rw [castPointAux_zsmul, castPointAux_some, castPointAux_some] at h1
    exact h1
  · rw [hΨbridge, hΦbridge, ← evTaut1_apply, ← evTaut1_apply] at hx
    exact hx

/-- **The invariant-differential identity for a curve of nonzero
discriminant.** -/
theorem identityHolds_of_Δ_ne_zero (hΔ : E.Δ ≠ 0) {n : ℤ}
    (hn : ((n : ℤ) : L) ≠ 0) : IdentityHolds E n := by
  obtain ⟨xp, yp, hpn, hsmul, hxrel⟩ := exists_smul_taut E hΔ hn
  exact evTaut1_injective E
    (sq_wronskian_evTaut E (taut_nonsingular E hΔ) hpn hsmul hxrel)

end Main

end InvariantDifferential


omit [DecidableEq F] [IsAlgClosed F] in
/-- **L4-7 (PROVEN 2026-07-26) `(★)`: the invariant differential, as a
universal polynomial identity.**  For every `n : ℤ`, writing
`Wr := Φ_n'·ΨSq_n − Φ_n·ΨSq_n'` for the Wronskian of the two
division polynomials,

`Wr² · Ψ₂Sq = n² · ΨSq_n · (4Φ_n³ + b₂Φ_n²ΨSq_n + 2b₄Φ_nΨSq_n² + b₆ΨSq_n³)`.

Dividing by `ΨSq_n⁴` this reads `f'(X)²·Ψ₂Sq(X) = n²·Ψ₂Sq(f(X))` for
the rational function `f = Φ_n/ΨSq_n = x ∘ [n]`, i.e. exactly
`d(x∘[n])/(2y∘[n] + a₁x∘[n] + a₃) = n · dx/(2y + a₁x + a₃)` — the
invariance of `ω = dx/(2y + a₁x + a₃)`, `[n]^*ω = n·ω`.

**On the hypothesis `(n : F) ≠ 0`.**  It is not needed for `n = 0`
(both sides vanish, since `ΨSq_0 = 0`), and for `n ≠ 0` in `ℤ` with
`(n : F) = 0` the identity is still true but by a SEPARATE
inseparability argument that the route below does not give.  The
hypothesis has been left exactly as stated, since it is what the
descent consumes.

**THE PROOF** (`InvariantDifferential`, immediately above; note that
NO hypothesis `Δ ≠ 0` appears here — see step 5).

1. *The derivation.*  A derivation `D` of `K = Frac L[E]` with
   `Dx = ψ₂`, `Dy = 3x²+2a₂x+a₄−a₁y` is the same thing as an
   `L`-algebra map `L[E] → DualNumber K` sending `x ↦ (x, ψ₂)`,
   `y ↦ (y, 3x²+2a₂x+a₄−a₁y)`, which is an `AdjoinRoot.lift`: the
   defining polynomial dies because its `ε`-part is `W_X·ψ₂ + W_Y·(−W_X)`
   (`eval₂_polynomial_dn`).  It extends to `K` by `IsLocalization.lift`,
   because `TrivSqZeroExt.isUnit_iff_isUnit_fst` makes every nonzero
   element of `L[E]` a unit of `K[ε]` (`isUnit_cdiff`).  `D z := (φ̃ z).snd`
   is then a derivation because `fst ∘ φ̃ = id` (`fst_kdiff`).

2. *The speed of a point.*  Rather than `μ(P) = D(x_P)/ψ₂(P)`, which
   divides by zero at `2`-torsion, the DIVISION-FREE predicate
   `Tang c P : D(x_P) = c·ψ₂(P) ∧ D(y_P) = c·q(P)` is used.  Its
   additivity `Tang c₁ P₁ → Tang c₂ P₂ → Tang (c₁+c₂) (P₁+P₂)`
   (`Tang_add`) is the invariance of `ω` under translation and needs no
   case analysis on `2`-torsion; the `P₁ + P₂ = 0` branch is closed by
   nonsingularity, and the two genuine branches are the pure field
   identities `tang_secant_aux` and `tang_double_aux`.  (The doubling
   branch is unconditional — the Weierstrass equation is not needed.)

3. *Integer multiples.*  `Tang_neg` and `Tang_zsmul` give
   `Tang (n·1) (n • taut)` from `Tang 1 taut`, which holds by the
   construction of `D`.

4. *Descent to polynomials.*  With `n • taut = (xp, yp)` and
   `xp·ΨSq_n(taut) = Φ_n(taut)` (`exists_smul_taut`, over
   `TorsionCard.exists_smul_some_eq`), applying `D` and using
   `ψ₂(P)² = Ψ₂Sq(x_P)` gives the identity evaluated at `tautX`
   (`sq_wronskian_evTaut`); `tautX` is transcendental over the constants
   because `L[E]` is free of rank `2` over `L[X]`, so `L[X] → K` is
   injective (`evTaut1_injective`), and the identity descends.

5. *Removing `Δ ≠ 0`.*  Steps 1–4 need a nonsingular curve.  The
   identity is transported along ring homomorphisms in both directions
   (`identityHolds_map`, `identityHolds_of_map`, using
   `Polynomial.map_injective`), so it suffices to prove it for the
   GENERIC curve over `MvPolynomial (Fin 5) L`, which embeds in its
   fraction field and has `Δ ≠ 0` — witnessed by the specialization
   `a₁ = 1, a₂ = a₃ = a₄ = 0, a₆ = t`, where `Δ = −t − 432t²` has
   `t`-coefficient `−1` in every characteristic
   (`genericCurve_Δ_ne_zero`).  Specializing back along
   `MvPolynomial (Fin 5) L → L` gives an arbitrary `W`
   (`identityHolds_of_generic`). -/
theorem sq_wronskian_mul_Ψ₂Sq (W : WeierstrassCurve.Affine F) {n : ℤ}
    (hn : ((n : ℤ) : F) ≠ 0) :
    (Polynomial.derivative (W.Φ n) * W.ΨSq n -
        W.Φ n * Polynomial.derivative (W.ΨSq n)) ^ 2 * W.Ψ₂Sq =
      Polynomial.C ((n : F) ^ 2) * W.ΨSq n *
        (Polynomial.C 4 * W.Φ n ^ 3 +
          Polynomial.C W.b₂ * W.Φ n ^ 2 * W.ΨSq n +
          Polynomial.C (2 * W.b₄) * W.Φ n * W.ΨSq n ^ 2 +
          Polynomial.C W.b₆ * W.ΨSq n ^ 3) :=
  InvariantDifferential.identityHolds_of_generic
    (fun _ _ V _ hΔ hm => InvariantDifferential.identityHolds_of_Δ_ne_zero V hΔ hm)
    W n hn

/-! ### The characteristic-`2` structure behind the inseparable residue

The leaf `rootMultiplicity_Φ_sub_C_mul_ΨSq_of_Ψ₂Sq_inseparable` below was cut
open on 2026-07-26.  The hypotheses `Ψ₂Sq(x) = Ψ₂Sq'(x) = 0` force `2 = 0` in
`F`, and in characteristic `2` the whole configuration collapses to ONE clean
polynomial identity,

  `Φ_p − x·Ψ²_p = (X − x) · Φ_p'`   (`Φ_sub_C_mul_ΨSq_eq_X_sub_C_mul_derivative_Φ`),

from which every case of the multiplicity claim except one is immediate.  The
declarations in this block are the steps of that reduction. -/

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Step 1 (PROVEN): a multiple root of `Ψ₂Sq` forces characteristic `2`.**

`disc(4X³ + b₂X² + 2b₄X + b₆) = 16Δ`, and a Bézout identity puts `16Δ` in the
ideal generated by `Ψ₂Sq` and `Ψ₂Sq'` — so a common root of the two makes
`16Δ = 0`, whence `(16 : F) = 0` and therefore `(2 : F) = 0`.  The cofactors
were computed by Singular's `lift` and are verified here by `linear_combination`;
nothing about elliptic curves is used beyond the definition of `Δ`.

This is why the leaf is "stated without naming the characteristic": the
characteristic is a CONSEQUENCE of the hypotheses, not an assumption. -/
theorem two_eq_zero_of_Ψ₂Sq_inseparable (hΔ : W.Δ ≠ 0) {x : F}
    (hx0 : W.Ψ₂Sq.eval x = 0)
    (hx1 : (Polynomial.derivative W.Ψ₂Sq).eval x = 0) :
    (2 : F) = 0 := by
  have he0 : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
    have h := hx0
    rw [WeierstrassCurve.Ψ₂Sq] at h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at h
    linear_combination h
  have he1 : 12 * x ^ 2 + 2 * W.b₂ * x + 2 * W.b₄ = 0 := by
    have h := hx1
    rw [WeierstrassCurve.Ψ₂Sq] at h
    simp only [Polynomial.derivative_add, Polynomial.derivative_C_mul,
      Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.derivative_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, mul_one, add_zero] at h
    push_cast at h
    linear_combination h
  have hb : (16 : F) * W.Δ = 144 * W.b₂ * W.b₄ * W.b₆ - 4 * W.b₂ ^ 3 * W.b₆
      + 4 * W.b₂ ^ 2 * W.b₄ ^ 2 - 128 * W.b₄ ^ 3 - 432 * W.b₆ ^ 2 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have hD : (16 : F) * W.Δ = 0 := by
    rw [hb]
    linear_combination (-24 * x * W.b₂ ^ 2 - 4 * W.b₂ ^ 3 + 576 * x * W.b₄
        + 120 * W.b₂ * W.b₄ - 432 * W.b₆) * he0
      + (8 * x ^ 2 * W.b₂ ^ 2 + 2 * x * W.b₂ ^ 3 - 192 * x ^ 2 * W.b₄
        - 56 * x * W.b₂ * W.b₄ + 2 * W.b₂ ^ 2 * W.b₄ - 64 * W.b₄ ^ 2
        + 144 * x * W.b₆ + 12 * W.b₂ * W.b₆) * he1
  have h16 : (16 : F) = 0 := by
    rcases mul_eq_zero.mp hD with h | h
    · exact h
    · exact absurd h hΔ
  have h4 : (2 : F) ^ 4 = 0 := by linear_combination h16
  exact pow_eq_zero_iff (four_ne_zero' ℕ) |>.mp h4

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Step 2a (PROVEN): in characteristic `2`, `Ψ₂Sq = (a₁X + a₃)²` pointwise.**
Immediate from `4 = 2·2 = 0`, `b₂ = a₁²`, `b₆ = a₃²`. -/
theorem eval_Ψ₂Sq_eq_sq_of_two_eq_zero (h2 : (2 : F) = 0) (z : F) :
    W.Ψ₂Sq.eval z = (W.a₁ * z + W.a₃) ^ 2 := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  linear_combination (2 * z ^ 3 + 2 * W.a₂ * z ^ 2 + 2 * W.a₄ * z + 2 * W.a₆) * h2

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Step 2b (PROVEN): `a₃ = a₁·x`.**  In characteristic `2` the hypothesis
`Ψ₂Sq(x) = 0` says `(a₁x + a₃)² = 0`, i.e. `x` is the abscissa of the unique
nonzero `2`-torsion point. -/
theorem a₃_eq_of_two_eq_zero (h2 : (2 : F) = 0) {x : F} (hx0 : W.Ψ₂Sq.eval x = 0) :
    W.a₃ = W.a₁ * x := by
  have h := (eval_Ψ₂Sq_eq_sq_of_two_eq_zero h2 x).symm.trans hx0
  have h0 : W.a₁ * x + W.a₃ = 0 := pow_eq_zero_iff two_ne_zero |>.mp h
  linear_combination h0 - (W.a₁ * x) * h2 - h2 * 0

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Step 2c (PROVEN): `a₁ ≠ 0`.**  If `a₁ = 0` then `a₃ = 0` by step 2b, and
then `Δ = 0` in characteristic `2` — so the SUPERSINGULAR case `a₁ = 0` (where
`Ψ₂Sq` is the nonzero constant `a₃²` and has no root at all) is excluded by the
hypothesis `hx0` itself, not assumed away. -/
theorem a₁_ne_zero_of_two_eq_zero (h2 : (2 : F) = 0) (hΔ : W.Δ ≠ 0) {x : F}
    (hx0 : W.Ψ₂Sq.eval x = 0) : W.a₁ ≠ 0 := by
  intro ha₁
  have ha₃ : W.a₃ = 0 := by
    have := a₃_eq_of_two_eq_zero h2 hx0
    rw [this, ha₁, zero_mul]
  apply hΔ
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha₁, ha₃]
  linear_combination (-32 * W.a₂ ^ 3 * W.a₆ + 8 * W.a₂ ^ 2 * W.a₄ ^ 2 - 32 * W.a₄ ^ 3
    - 216 * W.a₆ ^ 2 + 144 * W.a₂ * W.a₄ * W.a₆) * h2

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Step 3 (PROVEN): `Ψ₂Sq' = 0` in characteristic `2`** — it is a square. -/
theorem derivative_Ψ₂Sq_eq_zero_of_two_eq_zero (h2 : (2 : F) = 0) :
    Polynomial.derivative W.Ψ₂Sq = 0 := by
  have h4 : (4 : F) = 0 := by linear_combination 2 * h2
  have h2n : ((2 : ℕ) : F) = 0 := by exact_mod_cast h2
  have h2b : (2 : F) * W.b₄ = 0 := by linear_combination W.b₄ * h2
  simp only [WeierstrassCurve.Ψ₂Sq, Polynomial.derivative_add, Polynomial.derivative_C_mul,
    Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.derivative_C,
    h4, h2n, h2b, map_zero]
  simp

omit [DecidableEq F] [IsAlgClosed F] in
/-- `(p : F) ≠ 0` in characteristic `2` makes `p` odd. -/
theorem not_even_of_two_eq_zero (h2 : (2 : F) = 0) (hp : (p : F) ≠ 0) : ¬ Even p := by
  have hne : p ≠ 2 := by rintro rfl; exact hp (by exact_mod_cast h2)
  exact Nat.not_even_iff_odd.mpr ((Fact.out : p.Prime).odd_of_ne_two hne)

omit [DecidableEq F] [IsAlgClosed F] in
/-- An odd prime is `1` in characteristic `2`. -/
theorem cast_eq_one_of_two_eq_zero (h2 : (2 : F) = 0) (hp : (p : F) ≠ 0) : (p : F) = 1 := by
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp (not_even_of_two_eq_zero h2 hp)
  rw [hk]
  push_cast
  linear_combination (k : F) * h2

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Step 4 (PROVEN): `Ψ²_p` has zero derivative in characteristic `2`.**  For odd
`p`, `ΨSq_ofNat` makes `Ψ²_p = (preΨ'_p)²` an honest square, and the derivative of
a square carries the factor `2`. -/
theorem derivative_ΨSq_eq_zero_of_two_eq_zero (h2 : (2 : F) = 0) (hp : (p : F) ≠ 0) :
    Polynomial.derivative (W.ΨSq (p : ℤ)) = 0 := by
  have hsq : W.ΨSq ((p : ℕ) : ℤ) = W.preΨ' p ^ 2 := by
    rw [WeierstrassCurve.ΨSq_ofNat, if_neg (not_even_of_two_eq_zero h2 hp), mul_one]
  rw [hsq, Polynomial.derivative_pow, show ((2 : ℕ) : F) = 0 from by exact_mod_cast h2]
  simp

omit [DecidableEq F] [IsAlgClosed F] in
/-- `(2 : F[X]) = 0` when `(2 : F) = 0`. -/
theorem two_eq_zero_polynomial (h2 : (2 : F) = 0) : (2 : Polynomial F) = 0 := by
  rw [← map_ofNat (Polynomial.C : F →+* Polynomial F) 2, h2, map_zero]

omit [DecidableEq F] [IsAlgClosed F] in
/-- Squaring is injective on `F[X]` in characteristic `2`: `A² = B²` gives
`(A − B)² = A² − 2AB + B² = 0`. -/
theorem sq_injective_of_two_eq_zero (h2 : (2 : F) = 0) {A B : Polynomial F}
    (h : A ^ 2 = B ^ 2) : A = B := by
  have h2P := two_eq_zero_polynomial h2
  have hz : (A - B) ^ 2 = 0 := by linear_combination h + (B ^ 2 - A * B) * h2P
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz)

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Step 5 (PROVEN): THE KEY FACTORIZATION.**  In characteristic `2`, with `x`
the abscissa of the unique nonzero `2`-torsion point,

  `Φ_p − x·Ψ²_p = (X − x) · Φ_p'`.

**Proof.**  Write `G = Φ_p − x·Ψ²_p`.  In characteristic `2`, `Ψ²_p` is a square
so `(Ψ²_p)' = 0` (step 4) and the wronskian in `(★)` collapses to `Φ_p'·Ψ²_p`;
moreover `4 = 2b₄ = 0`, `b₂ = a₁²`, `b₆ = a₃²`, so the cubic factor of `(★)`
collapses to `Ψ²_p·(a₁Φ_p + a₃Ψ²_p)²` and `Ψ₂Sq` to `(a₁X + a₃)²`.  Thus `(★)`
reads

  `(Φ_p'·Ψ²_p·(a₁X + a₃))² = (p·Ψ²_p·(a₁Φ_p + a₃Ψ²_p))²`,

and squaring is injective (`sq_injective_of_two_eq_zero`).  Cancelling `Ψ²_p ≠ 0`
and `a₁ ≠ 0`, substituting `a₃ = a₁x` and `(p : F) = 1`, gives the claim.

**NUMERICAL CHECK** (2026-07-26).  For `W : y² + xy = x³ + 1` over `𝔽₂` (so
`a₁ = 1`, `b₂ = 1`, `b₆ = 0`, `Δ = 1 ≠ 0`, `Ψ₂Sq = X²`, hence `x = 0`) and
`p = 3`: `Ψ²₃ = X⁸ + X⁶ + 1`, `Φ₃ = X⁹ + X³ + X`, `Φ₃' = X⁸ + X² + 1`, and
indeed `Φ₃ − 0·Ψ²₃ = X·(X⁸ + X² + 1) = (X − 0)·Φ₃'`. -/
theorem Φ_sub_C_mul_ΨSq_eq_X_sub_C_mul_derivative_Φ (h2 : (2 : F) = 0) (hΔ : W.Δ ≠ 0)
    (hp : (p : F) ≠ 0) {x : F} (hx0 : W.Ψ₂Sq.eval x = 0) :
    W.Φ ((p : ℕ) : ℤ) - Polynomial.C x * W.ΨSq ((p : ℕ) : ℤ)
      = (Polynomial.X - Polynomial.C x) * Polynomial.derivative (W.Φ ((p : ℕ) : ℤ)) := by
  have h2P := two_eq_zero_polynomial h2
  have ha₁ : W.a₁ ≠ 0 := a₁_ne_zero_of_two_eq_zero h2 hΔ hx0
  have ha₃ : W.a₃ = W.a₁ * x := a₃_eq_of_two_eq_zero h2 hx0
  have hΨ' : Polynomial.derivative (W.ΨSq ((p : ℕ) : ℤ)) = 0 :=
    derivative_ΨSq_eq_zero_of_two_eq_zero h2 hp
  have hpZ : (((p : ℕ) : ℤ) : F) ≠ 0 := by exact_mod_cast hp
  have hΨ0 : W.ΨSq ((p : ℕ) : ℤ) ≠ 0 := WeierstrassCurve.ΨSq_ne_zero _ hpZ
  set Φ := W.Φ ((p : ℕ) : ℤ) with hΦdef
  set Ψ := W.ΨSq ((p : ℕ) : ℤ) with hΨdef
  set D := Polynomial.derivative Φ with hDdef
  have hΨ₂ : W.Ψ₂Sq = (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) ^ 2 := by
    simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, map_add, map_mul, map_pow, map_ofNat]
    linear_combination (2 * Polynomial.X ^ 3 + 2 * Polynomial.C W.a₂ * Polynomial.X ^ 2
      + 2 * Polynomial.C W.a₄ * Polynomial.X + 2 * Polynomial.C W.a₆) * h2P
  have hN : Polynomial.C 4 * Φ ^ 3 + Polynomial.C W.b₂ * Φ ^ 2 * Ψ
      + Polynomial.C (2 * W.b₄) * Φ * Ψ ^ 2 + Polynomial.C W.b₆ * Ψ ^ 3
      = Ψ * (Polynomial.C W.a₁ * Φ + Polynomial.C W.a₃ * Ψ) ^ 2 := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      map_add, map_mul, map_pow, map_ofNat]
    linear_combination (2 * Φ ^ 3 + 2 * Polynomial.C W.a₂ * Φ ^ 2 * Ψ
      + 2 * Polynomial.C W.a₄ * Φ * Ψ ^ 2 + 2 * Polynomial.C W.a₆ * Ψ ^ 3) * h2P
  have hstar := sq_wronskian_mul_Ψ₂Sq W (n := ((p : ℕ) : ℤ)) hpZ
  rw [← hΦdef, ← hΨdef, hΨ', ← hDdef, hΨ₂, hN] at hstar
  have hsq : (D * Ψ * (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃)) ^ 2
      = (Polynomial.C ((((p : ℕ) : ℤ) : F)) * Ψ
          * (Polynomial.C W.a₁ * Φ + Polynomial.C W.a₃ * Ψ)) ^ 2 := by
    rw [map_pow] at hstar
    linear_combination hstar
  have hroot := sq_injective_of_two_eq_zero h2 hsq
  have hCa₁ : (Polynomial.C W.a₁ : Polynomial F) ≠ 0 := Polynomial.C_ne_zero.mpr ha₁
  have hone : (((p : ℕ) : ℤ) : F) = 1 := by
    rw [show ((((p : ℕ) : ℤ)) : F) = ((p : ℕ) : F) from by push_cast; ring]
    exact cast_eq_one_of_two_eq_zero h2 hp
  rw [hone, map_one, ha₃, map_mul] at hroot
  have hfin : Ψ * Polynomial.C W.a₁ * (D * (Polynomial.X - Polynomial.C x))
      = Ψ * Polynomial.C W.a₁ * (Φ - Polynomial.C x * Ψ) := by
    linear_combination hroot
      + (Ψ * Polynomial.C W.a₁ * Polynomial.C x * (Ψ - D)) * h2P
  have hcancel := mul_left_cancel₀ (mul_ne_zero hΨ0 hCa₁) hfin
  rw [← hcancel]
  ring

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Step 6 (PROVEN): `Φ_p'(x) = Ψ²_p(x)` at the two-torsion abscissa.**

`Φ_p = X·Ψ²_p − preΨ_{p+1}·preΨ_{p−1}·Ψ₂Sq` for odd `p`, and in characteristic `2`
both `Ψ²_p` and `Ψ₂Sq` have zero derivative, so
`Φ_p' = Ψ²_p − (preΨ_{p+1}preΨ_{p−1})'·Ψ₂Sq`.  Evaluating at `x`, where
`Ψ₂Sq(x) = 0`, kills the second term.

This is what discharges the case `a = x` of the leaf: there `hΨ` says
`Ψ²_p(x) ≠ 0`, so `x` is NOT a root of `Φ_p'` and the multiplicity is exactly `1`. -/
theorem eval_derivative_Φ_eq_eval_ΨSq_of_two_eq_zero (h2 : (2 : F) = 0) (hp : (p : F) ≠ 0)
    {x : F} (hx0 : W.Ψ₂Sq.eval x = 0) :
    (Polynomial.derivative (W.Φ ((p : ℕ) : ℤ))).eval x = (W.ΨSq ((p : ℕ) : ℤ)).eval x := by
  have hΨ' : Polynomial.derivative (W.ΨSq ((p : ℕ) : ℤ)) = 0 :=
    derivative_ΨSq_eq_zero_of_two_eq_zero h2 hp
  have hΨ₂' : Polynomial.derivative W.Ψ₂Sq = 0 := derivative_Ψ₂Sq_eq_zero_of_two_eq_zero h2
  have hev : ¬ Even ((p : ℕ) : ℤ) := by
    simpa [Int.even_coe_nat] using not_even_of_two_eq_zero (p := p) (F := F) h2 hp
  rw [WeierstrassCurve.Φ, if_neg hev]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_X,
    hΨ', hΨ₂', mul_zero, add_zero, one_mul,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, hx0]
  ring

omit [DecidableEq F] [IsAlgClosed F] in
/-- **Characteristic two, as a `CharP` instance** (PROVEN): in a field, `2 = 0`
forces `ringChar = 2`. -/
lemma charP_two_of_two_eq_zero (h2 : (2 : F) = 0) : CharP F 2 := by
  have h : ringChar F = 2 :=
    CharP.ringChar_of_prime_eq_zero Nat.prime_two (by exact_mod_cast h2)
  exact h ▸ ringChar.charP F

omit [DecidableEq F] [IsAlgClosed F] in
/-- **In characteristic `2` every root of a polynomial with vanishing derivative
has EVEN multiplicity** (PROVEN): `f' = 0` puts `f` in `F[X²]`
(`Polynomial.expand_contract`), and `Polynomial.rootMultiplicity_expand` reads
off `mult_a(expand 2 g) = 2·mult_{a²}(g)`.

This is the "even half" of the residual leaf below, and it is exactly the half
that the factorization `G = (X − x)·Φ_p'` supplies for free; the fibre count is
needed only for the matching UPPER bound. -/
lemma two_dvd_rootMultiplicity_of_derivative_eq_zero (h2 : (2 : F) = 0)
    {f : Polynomial F} (hf : Polynomial.derivative f = 0) (a : F) :
    2 ∣ f.rootMultiplicity a := by
  haveI : CharP F 2 := charP_two_of_two_eq_zero h2
  haveI : ExpChar F 2 := ExpChar.prime Nat.prime_two
  have hexp : Polynomial.expand F 2 (Polynomial.contract 2 f) = f :=
    Polynomial.expand_contract 2 hf two_ne_zero
  rw [← hexp, Polynomial.rootMultiplicity_expand]
  exact ⟨_, rfl⟩

/-- **THE FIBRE COUNT** (PROVEN 2026-07-27): `G := Φ_p − x·Ψ²_p` has at least
`(p² + 1)/2` DISTINCT roots, when `x` is the abscissa of an affine point `P₀`
with `Ψ₂Sq(x) = 0` — i.e. of a nonzero `2`-torsion point.

This is the separability of `[p]` in the only form the residual leaf needs, and
it is what the algebra around `G = (X − x)·Φ_p'` cannot supply.

**Proof.**  `P₀` is `2`-torsion (`TorsionCard.two_smul_some_eq_zero_iff`), and `p`
is odd, so `[p]P₀ = P₀`.  Hence the whole coset `P₀ + E[p]` lies in the fibre
`[p]⁻¹(P₀)`, and it has `p²` elements because `E[p]` does
(`TorsionCard.card_torsionBy`, over the separably closed `F`) and translation is
injective.  Every point of that coset is affine (its image `P₀` is nonzero) with
`Ψ²_p` nonvanishing at its abscissa (`TorsionCard.smul_some_eq_zero_iff`), so the
multiplication formula `TorsionCard.exists_smul_some_eq` makes its abscissa a root
of `G`.  Finally the abscissa map is at most `2`-to-`1`, since the `y`-fibre over
a point is cut out by the quadratic `TorsionCard.yQuad`.  So `p² ≤ 2·#roots(G)`.

Note NO surjectivity of `[p]` is used: the fibre is exhibited explicitly as a
coset, because `P₀` is visibly one of its own preimages. -/
theorem card_le_two_mul_card_roots_Φ_sub_C_mul_ΨSq (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {x y : F} (hxy : W.Nonsingular x y) (hodd : Odd p)
    (hx0 : W.Ψ₂Sq.eval x = 0) :
    p ^ 2 ≤ 2 *
      (W.Φ ((p : ℕ) : ℤ) - Polynomial.C x * W.ΨSq ((p : ℕ) : ℤ)).roots.toFinset.card := by
  classical
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hpZ : ((p : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  set G := W.Φ ((p : ℕ) : ℤ) - Polynomial.C x * W.ΨSq ((p : ℕ) : ℤ) with hGdef
  have hGne : G ≠ 0 := Φ_sub_C_mul_ΨSq_ne_zero x
  set P₀ : W.Point := Point.some x y hxy with hP₀def
  have hzero : (0 : W.Point) = Point.zero := rfl
  have hP₀ne : P₀ ≠ 0 := fun h => nomatch (h.trans hzero)
  -- `P₀` is `2`-torsion, hence fixed by `[p]` for odd `p`
  have h2P₀ : (2 : ℤ) • P₀ = 0 := (TorsionCard.two_smul_some_eq_zero_iff W hxy).mpr hx0
  obtain ⟨k, hk⟩ : ∃ k, p = k * 2 + 1 := ⟨p / 2, by
    have := Nat.odd_iff.mp hodd; omega⟩
  have hcast : ((p : ℕ) : ℤ) = (k : ℤ) * 2 + 1 := by exact_mod_cast hk
  have hpP₀ : ((p : ℕ) : ℤ) • P₀ = P₀ := by
    rw [hcast, add_smul, one_smul, mul_smul, h2P₀, smul_zero, zero_add]
  -- the `p`-torsion, as a finset of size `p²`
  have hbc : (WeierstrassCurve.Affine.baseChange W F) = W := WeierstrassCurve.map_id _
  have hM : Nat.card (Submodule.torsionBy ℤ W.Point ((p : ℕ) : ℤ)) = p ^ 2 := by
    have h := TorsionCard.card_torsionBy W p hp
    rwa [hbc] at h
  haveI : Finite (Submodule.torsionBy ℤ W.Point ((p : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ (Fact.out : p.Prime).pos.ne')
  haveI : Fintype (Submodule.torsionBy ℤ W.Point ((p : ℕ) : ℤ)) := Fintype.ofFinite _
  set T : Finset W.Point :=
    Finset.univ.image (Subtype.val : (Submodule.torsionBy ℤ W.Point ((p : ℕ) : ℤ)) → W.Point)
    with hTdef
  have hTcard : T.card = p ^ 2 := by
    rw [hTdef, Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hM]
  have hTtor : ∀ Q ∈ T, ((p : ℕ) : ℤ) • Q = 0 := by
    intro Q hQ
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hQ
    exact (Submodule.mem_torsionBy_iff _ _).mp m.2
  -- the fibre `P₀ + E[p]`
  set S : Finset W.Point := T.image (fun κ => P₀ + κ) with hSdef
  have hScard : S.card = p ^ 2 := by
    rw [hSdef, Finset.card_image_of_injective _ (add_right_injective P₀), hTcard]
  have hSfib : ∀ Q ∈ S, ((p : ℕ) : ℤ) • Q = P₀ := by
    intro Q hQ
    obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.mp hQ
    rw [smul_add, hTtor κ hκ, add_zero, hpP₀]
  -- coordinate functions
  set xc : W.Point → F := fun P =>
    match P with
    | .zero => 0
    | @Point.some _ _ _ x _ _ => x with hxcdef
  set yc : W.Point → F := fun P =>
    match P with
    | .zero => 0
    | @Point.some _ _ _ _ y _ => y with hycdef
  -- every point of the fibre is affine, with abscissa a root of `G`
  have hne0 : ∀ Q ∈ S, Q ≠ 0 := by
    intro Q hQ hQ0
    have h := hSfib Q hQ
    rw [hQ0, smul_zero] at h
    exact hP₀ne h.symm
  have hmaps : ∀ Q ∈ S, xc Q ∈ G.roots.toFinset := by
    have key : ∀ Q : W.Point, ((p : ℕ) : ℤ) • Q = P₀ → xc Q ∈ G.roots.toFinset := by
      intro Q hQp
      cases Q with
      | zero =>
        rw [show (Point.zero : W.Point) = 0 from rfl, smul_zero] at hQp
        exact absurd hQp.symm hP₀ne
      | some x₁ y₁ h₁ =>
        have hΨ₁ : (W.ΨSq ((p : ℕ) : ℤ)).eval x₁ ≠ 0 := by
          intro h0
          have hz : ((p : ℕ) : ℤ) • (Point.some x₁ y₁ h₁ : W.Point) = 0 :=
            (TorsionCard.smul_some_eq_zero_iff W hpZ h₁).mpr h0
          exact hP₀ne (hQp.symm.trans hz)
        obtain ⟨x', y', h', heq, hx'⟩ := TorsionCard.exists_smul_some_eq W hpZ h₁ hΨ₁
        have heq' : ((p : ℕ) : ℤ) • (Point.some x₁ y₁ h₁ : W.Point)
            = Point.some x' y' h' := heq
        have hx'' : x' * (W.ΨSq ((p : ℕ) : ℤ)).eval x₁
            = (W.Φ ((p : ℕ) : ℤ)).eval x₁ := hx'
        have hxx : x' = x := by
          have hpts := heq'.symm.trans hQp
          injection hpts with h1 _
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hGne]
        show G.eval x₁ = 0
        rw [hGdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
        rw [← hx'', hxx]
        ring
    exact fun Q hQ => key Q (hSfib Q hQ)
  -- the abscissa map is at most two-to-one
  have hfibre : ∀ x₀ ∈ G.roots.toFinset, (S.filter (fun Q => xc Q = x₀)).card ≤ 2 := by
    intro x₀ _
    have hstep : (S.filter (fun Q => xc Q = x₀)).card ≤
        (TorsionCard.yQuad W x₀).roots.toFinset.card := by
      refine Finset.card_le_card_of_injOn yc ?_ ?_
      · intro P hP
        obtain ⟨hP', hx⟩ := Finset.mem_filter.mp hP
        have hPne : P ≠ 0 := hne0 P hP'
        cases P with
        | zero => exact absurd rfl hPne
        | some x₂ y₂ h₂ =>
          have hxx : x₂ = x₀ := hx
          subst hxx
          rw [Finset.mem_coe, Multiset.mem_toFinset,
            Polynomial.mem_roots (TorsionCard.yQuad_ne_zero W x₂)]
          exact (TorsionCard.eval_yQuad_eq_zero_iff_equation W x₂ y₂).mpr h₂.1
      · intro P hP Q hQ hy
        obtain ⟨hP', hxP⟩ := Finset.mem_filter.mp hP
        obtain ⟨hQ', hxQ⟩ := Finset.mem_filter.mp hQ
        have hPne : P ≠ 0 := hne0 P hP'
        have hQne : Q ≠ 0 := hne0 Q hQ'
        cases P with
        | zero => exact absurd rfl hPne
        | some xP yP hP'' =>
          cases Q with
          | zero => exact absurd rfl hQne
          | some xQ yQ hQ'' =>
            have h1 : xP = x₀ := hxP
            have h2 : xQ = x₀ := hxQ
            have hxx : xQ = xP := h2.trans h1.symm
            have h3 : yP = yQ := hy
            subst hxx
            subst h3
            rfl
    refine hstep.trans ?_
    calc (TorsionCard.yQuad W x₀).roots.toFinset.card
        ≤ Multiset.card (TorsionCard.yQuad W x₀).roots := Multiset.toFinset_card_le _
      _ ≤ (TorsionCard.yQuad W x₀).natDegree := Polynomial.card_roots' _
      _ = 2 := TorsionCard.yQuad_natDegree W x₀
  have hcount := Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfibre
  rwa [hScard] at hcount

/-- **The residual leaf over an ALGEBRAICALLY CLOSED field** (PROVEN 2026-07-27).

With `G := Φ_p − x·Ψ²_p` and `H := Φ_p'`, step 5 gives `G = (X − x)·H` and step 4
gives `(Ψ²_p)' = 0`, whence `G' = H` and therefore `(X − x)·H' = 0`, i.e. `H' = 0`.
So every root of `H` has EVEN multiplicity
(`two_dvd_rootMultiplicity_of_derivative_eq_zero`), i.e. `≥ 2`.

The matching upper bound is the fibre count.  `G` is monic of degree `p²`
(`natDegree_Φ`, `natDegree_ΨSq_le`), it has `mult_x(G) = 1` — because
`H(x) = Ψ²_p(x) ≠ 0` by step 6 and by `[p]P₀ = P₀ ≠ O` — and by
`card_le_two_mul_card_roots_Φ_sub_C_mul_ΨSq` it has at least `(p²+1)/2` distinct
roots.  Summing multiplicities over the distinct roots,

  `p² ≥ mult_x(G) + mult_a(G) + 2·(#roots − 2) ≥ 1 + mult_a(G) + (p² + 1) − 4`,

so `mult_a(G) ≤ 2`; with the even lower bound, `mult_a(G) = mult_a(H) = 2`.

Note the hypothesis `Ψ²_p(a) ≠ 0` of the leaf below is NOT needed here: it is
implied by `hroot` together with the coprimality of `Φ_p` and `Ψ²_p`. -/
theorem rootMultiplicity_derivative_Φ_eq_two_of_two_eq_zero_isAlgClosed
    (h2 : (2 : F) = 0) (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0) {a x : F}
    (hx0 : W.Ψ₂Sq.eval x = 0) (hax : a ≠ x)
    (hroot : (W.Φ ((p : ℕ) : ℤ)).eval a = x * (W.ΨSq ((p : ℕ) : ℤ)).eval a) :
    (Polynomial.derivative (W.Φ ((p : ℕ) : ℤ))).rootMultiplicity a = 2 := by
  classical
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hpZ : ((p : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hodd : Odd p := Nat.not_even_iff_odd.mp (not_even_of_two_eq_zero (p := p) (F := F) h2 hp)
  set G := W.Φ ((p : ℕ) : ℤ) - Polynomial.C x * W.ΨSq ((p : ℕ) : ℤ) with hGdef
  set H := Polynomial.derivative (W.Φ ((p : ℕ) : ℤ)) with hHdef
  have hGne : G ≠ 0 := Φ_sub_C_mul_ΨSq_ne_zero x
  have hfact : G = (Polynomial.X - Polynomial.C x) * H :=
    Φ_sub_C_mul_ΨSq_eq_X_sub_C_mul_derivative_Φ h2 hΔ hp hx0
  have hHne : H ≠ 0 := by
    intro h0
    rw [hfact, h0, mul_zero] at hGne
    exact hGne rfl
  -- the derivative of `H` vanishes
  have hΨ' : Polynomial.derivative (W.ΨSq ((p : ℕ) : ℤ)) = 0 :=
    derivative_ΨSq_eq_zero_of_two_eq_zero h2 hp
  have hHd : Polynomial.derivative H = 0 := by
    have h1 := congrArg Polynomial.derivative hfact
    rw [hGdef, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
      hΨ', mul_zero, zero_mul, add_zero, sub_zero, Polynomial.derivative_mul,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
      one_mul] at h1
    have h2' : (Polynomial.X - Polynomial.C x) * Polynomial.derivative H = 0 := by
      linear_combination -h1
    rcases mul_eq_zero.mp h2' with hz | hz
    · exact absurd hz (Polynomial.X_sub_C_ne_zero x)
    · exact hz
  -- a point above the two-torsion abscissa `x`
  obtain ⟨y, hy⟩ : ∃ y : F, W.Nonsingular x y := by
    obtain ⟨y, hyroot⟩ := IsAlgClosed.exists_root (TorsionCard.yQuad W x) (by
      rw [Polynomial.degree_eq_natDegree (TorsionCard.yQuad_ne_zero W x),
        TorsionCard.yQuad_natDegree]
      decide)
    exact ⟨y, W.equation_iff_nonsingular.mp
      ((TorsionCard.eval_yQuad_eq_zero_iff_equation W x y).mp hyroot)⟩
  -- `Ψ²_p(x) ≠ 0`, since `[p]P₀ = P₀ ≠ O`
  have hzero : (0 : W.Point) = Point.zero := rfl
  have hP₀ne : (Point.some x y hy : W.Point) ≠ 0 := fun h => nomatch (h.trans hzero)
  have h2P₀ : (2 : ℤ) • (Point.some x y hy : W.Point) = 0 :=
    (TorsionCard.two_smul_some_eq_zero_iff W hy).mpr hx0
  obtain ⟨k, hk⟩ : ∃ k, p = k * 2 + 1 := ⟨p / 2, by have := Nat.odd_iff.mp hodd; omega⟩
  have hcast : ((p : ℕ) : ℤ) = (k : ℤ) * 2 + 1 := by exact_mod_cast hk
  have hpP₀ : ((p : ℕ) : ℤ) • (Point.some x y hy : W.Point) = Point.some x y hy := by
    rw [hcast, add_smul, one_smul, mul_smul, h2P₀, smul_zero, zero_add]
  have hΨx : (W.ΨSq ((p : ℕ) : ℤ)).eval x ≠ 0 := by
    intro h0
    have hz : ((p : ℕ) : ℤ) • (Point.some x y hy : W.Point) = 0 :=
      (TorsionCard.smul_some_eq_zero_iff W hpZ hy).mpr h0
    exact hP₀ne (hpP₀.symm.trans hz)
  -- multiplicities: `1` at `x`, even and positive elsewhere
  have hmultX : G.rootMultiplicity x = 1 := by
    have hHx : H.rootMultiplicity x = 0 := by
      refine Polynomial.rootMultiplicity_eq_zero ?_
      rw [Polynomial.IsRoot.def, hHdef,
        eval_derivative_Φ_eq_eval_ΨSq_of_two_eq_zero h2 hp hx0]
      exact hΨx
    rw [hfact, Polynomial.rootMultiplicity_mul (hfact ▸ hGne), hHx,
      Polynomial.rootMultiplicity_X_sub_C_self]
  have hshift : ∀ r : F, r ≠ x → G.rootMultiplicity r = H.rootMultiplicity r := by
    intro r hrx
    have hXm : (Polynomial.X - Polynomial.C x : Polynomial F).rootMultiplicity r = 0 := by
      refine Polynomial.rootMultiplicity_eq_zero ?_
      simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      exact sub_ne_zero.mpr hrx
    rw [hfact, Polynomial.rootMultiplicity_mul (hfact ▸ hGne), hXm, zero_add]
  have hkey : ∀ r : F, G.eval r = 0 → r ≠ x → 2 ≤ G.rootMultiplicity r := by
    intro r hr hrx
    have hHr : H.eval r = 0 := by
      have hev := hr
      rw [hfact, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] at hev
      rcases mul_eq_zero.mp hev with hz | hz
      · exact absurd (sub_eq_zero.mp hz) hrx
      · exact hz
    have hpos : 0 < H.rootMultiplicity r :=
      (Polynomial.rootMultiplicity_pos hHne).mpr hHr
    have heven := two_dvd_rootMultiplicity_of_derivative_eq_zero h2 hHd r
    rw [hshift r hrx]
    omega
  -- the counting
  set R := G.roots.toFinset with hRdef
  have hxR : x ∈ R := by
    rw [hRdef, Multiset.mem_toFinset, Polynomial.mem_roots hGne]
    show G.eval x = 0
    rw [hfact, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_mul]
  have hGa : G.eval a = 0 := by
    rw [hGdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hroot, sub_self]
  have haR : a ∈ R := by
    rw [hRdef, Multiset.mem_toFinset, Polynomial.mem_roots hGne]
    exact hGa
  have hamem : a ∈ R.erase x := Finset.mem_erase.mpr ⟨hax, haR⟩
  have hsum : ∑ r ∈ R, G.rootMultiplicity r = Multiset.card G.roots := by
    rw [hRdef, ← Multiset.toFinset_sum_count_eq G.roots]
    exact Finset.sum_congr rfl (fun r _ => (Polynomial.count_roots G).symm)
  have hGdeg : G.natDegree = p ^ 2 := by
    have h1 : (W.Φ ((p : ℕ) : ℤ)).natDegree = p ^ 2 := by
      have h := W.natDegree_Φ ((p : ℕ) : ℤ)
      rwa [Int.natAbs_natCast] at h
    have h2' : (Polynomial.C x * W.ΨSq ((p : ℕ) : ℤ)).natDegree < p ^ 2 := by
      refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le x _) ?_
      refine lt_of_le_of_lt (W.natDegree_ΨSq_le ((p : ℕ) : ℤ)) ?_
      rw [Int.natAbs_natCast]
      exact Nat.sub_lt (pow_pos (Fact.out : p.Prime).pos 2) one_pos
    rw [hGdef, Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rw [h1]; exact h2'), h1]
  have hle : ∑ r ∈ R, G.rootMultiplicity r ≤ p ^ 2 := by
    rw [hsum, ← hGdeg]
    exact Polynomial.card_roots' G
  have hsplit : ∑ r ∈ R, G.rootMultiplicity r
      = (∑ r ∈ (R.erase x).erase a, G.rootMultiplicity r)
        + G.rootMultiplicity a + G.rootMultiplicity x := by
    rw [Finset.sum_erase_add _ _ hamem, Finset.sum_erase_add _ _ hxR]
  have hbig : 2 * ((R.erase x).erase a).card
      ≤ ∑ r ∈ (R.erase x).erase a, G.rootMultiplicity r := by
    have hall : ∀ r ∈ (R.erase x).erase a, 2 ≤ G.rootMultiplicity r := by
      intro r hr
      have hrx : r ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)
      have hrR : r ∈ R := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
      rw [hRdef, Multiset.mem_toFinset, Polynomial.mem_roots hGne] at hrR
      exact hkey r hrR hrx
    have hns := Finset.card_nsmul_le_sum ((R.erase x).erase a)
      (fun r => G.rootMultiplicity r) 2 hall
    simpa [mul_comm] using hns
  have hcards : ((R.erase x).erase a).card + 2 = R.card := by
    rw [Finset.card_erase_of_mem hamem, Finset.card_erase_of_mem hxR]
    have h1 : 1 ≤ R.card := Finset.card_pos.mpr ⟨x, hxR⟩
    have h2' : 1 ≤ (R.erase x).card := Finset.card_pos.mpr ⟨a, hamem⟩
    rw [Finset.card_erase_of_mem hxR] at h2'
    omega
  have hfib := card_le_two_mul_card_roots_Φ_sub_C_mul_ΨSq (W := W) hΔ hp hy hodd hx0
  rw [← hGdef, ← hRdef] at hfib
  have hma : 2 ≤ G.rootMultiplicity a := hkey a hGa hax
  have hoddsq : p ^ 2 % 2 = 1 := Nat.odd_iff.mp (hodd.pow)
  rw [← hshift a hax]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, p ^ 2 = n := ⟨p ^ 2, rfl⟩
  rw [hn] at hle hfib hoddsq
  omega

omit [DecidableEq F] [IsAlgClosed F] in
/-- **THE RESIDUAL LEAF of the characteristic-`2` case (PROVEN 2026-07-27 by the
fibre count): the roots of `Φ_p'` away from the two-torsion abscissa are DOUBLE.**

After `Φ_sub_C_mul_ΨSq_eq_X_sub_C_mul_derivative_Φ` this is all that is left of
`rootMultiplicity_Φ_sub_C_mul_ΨSq_of_Ψ₂Sq_inseparable`, and it is exactly the
separability of `[p]` in the form the descent needs.

**THE EVEN HALF, which the algebra supplies.**  Put `G = Φ_p − x·Ψ²_p` and
`H = Φ_p'`, so `G = (X − x)·H`.  Differentiating and using `(Ψ²_p)' = 0` gives
`G' = H`, hence `H = H + (X − x)·H'`, hence `H' = 0`.  A polynomial with zero
derivative in characteristic `2` lies in `F[X²]`, so EVERY root of `H` has EVEN
multiplicity (`two_dvd_rootMultiplicity_of_derivative_eq_zero`, over mathlib's
`Polynomial.rootMultiplicity_expand` at `p = 2`).  Since `a` is a root of `H`
here, `2 ∣ mult_a(H)` and `mult_a(H) ≥ 2`.

**THE UPPER HALF `mult_a(H) ≤ 2` IS THE FIBRE COUNT**, and the identity
`G = (X − x)·H` alone CANNOT supply it: `G = (X − x)(X − β)⁴` satisfies
`G' · (X − x) = G` just as well as `G = (X − x)(X − β)²` does.  It is proven as
`card_le_two_mul_card_roots_Φ_sub_C_mul_ΨSq` above: `[p]⁻¹(P₀) ⊇ P₀ + E[p]` has
`p²` points (`TorsionCard.card_torsionBy`; `[p]P₀ = P₀` because `p` is odd and
`P₀` is `2`-torsion, so NO surjectivity of `[p]` is needed), each contributing a
root of `G` through the multiplication formula, and the abscissa map is at most
`2`-to-`1`.  So `G` has at least `(p² + 1)/2` distinct roots; with `mult_x(G) = 1`
and every other multiplicity `≥ 2` and even, `deg G = p²` forces `mult = 2` at
each of them.

Assembled in `rootMultiplicity_derivative_Φ_eq_two_of_two_eq_zero_isAlgClosed`
above and transported here along `F ↪ AlgebraicClosure F`
(`Polynomial.eq_rootMultiplicity_map`, `map_Φ` / `map_ΨSq` / `map_Ψ₂Sq`), which is
what lets `IsAlgClosed F` stay OMITTED on this leaf and on its consumer.

The hypothesis `hΨ : Ψ²_p(a) ≠ 0` is REDUNDANT for this statement — it is implied
by `hroot` and the coprimality of `Φ_p, Ψ²_p` — so it is bound as `_hΨ`.  It is
retained in the signature because the consumer's other branches need it and call
this positionally.

**NUMERICAL CERTIFICATE — a check of the STATEMENT, made before the proof**
(PARI/GP over `𝔽₂`, 2026-07-26).  Division polynomials were built from the standard
recursions for `(a₁,a₂,a₃,a₄,a₆) ∈ {(1,0,0,0,1), (1,1,0,0,1), (1,0,1,1,1)}` and
`p ∈ {3,5,7}` (six `Δ ≠ 0` instances).  In every one: `deg G = p²` (9, 25, 49);
the identity `G = (X − x₀)·Φ_p'` of step 5 HOLDS; and every irreducible factor of
`Φ_p'` occurs with multiplicity exactly `2` — i.e. the conclusion of this leaf is
correct, and in particular the leaf is neither false nor vacuous. -/
theorem rootMultiplicity_derivative_Φ_eq_two_of_two_eq_zero
    (h2 : (2 : F) = 0) (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0) {a x : F}
    (_hΨ : ((W.ΨSq ((p : ℕ) : ℤ)).eval a) ≠ 0)
    (hx0 : W.Ψ₂Sq.eval x = 0) (hax : a ≠ x)
    (hroot : (W.Φ ((p : ℕ) : ℤ)).eval a = x * (W.ΨSq ((p : ℕ) : ℤ)).eval a) :
    (Polynomial.derivative (W.Φ ((p : ℕ) : ℤ))).rootMultiplicity a = 2 := by
  classical
  let K := AlgebraicClosure F
  let φ : F →+* K := algebraMap F K
  have hinj : Function.Injective φ := (algebraMap F K).injective
  have hev : ∀ (q : Polynomial F) (t : F), (q.map φ).eval (φ t) = φ (q.eval t) := by
    intro q t
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have h2K : (2 : K) = 0 := by
    rw [← map_ofNat φ 2, h2, map_zero]
  have hpK : (p : K) ≠ 0 := by
    intro h0
    exact hp (hinj (by rw [map_natCast, h0, map_zero]))
  have hΔK : (W.map φ).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    intro h0
    exact hΔ (hinj (by rw [h0, map_zero]))
  have hx0K : (W.map φ).Ψ₂Sq.eval (φ x) = 0 := by
    rw [WeierstrassCurve.map_Ψ₂Sq, hev, hx0, map_zero]
  have haxK : φ a ≠ φ x := fun h => hax (hinj h)
  have hrootK : ((W.map φ).Φ ((p : ℕ) : ℤ)).eval (φ a)
      = φ x * (((W.map φ).ΨSq ((p : ℕ) : ℤ)).eval (φ a)) := by
    rw [WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq, hev, hev, hroot, map_mul]
  rw [Polynomial.eq_rootMultiplicity_map hinj a, ← Polynomial.derivative_map,
    ← WeierstrassCurve.map_Φ]
  exact rootMultiplicity_derivative_Φ_eq_two_of_two_eq_zero_isAlgClosed
    (W := (W.map φ)) h2K hΔK hpK hx0K haxK hrootK

omit [IsAlgClosed F] in
/-- **L4-7: the inseparable residue of `Ψ₂Sq`** (DECOMPOSED 2026-07-26; the last
leaf underneath, `rootMultiplicity_derivative_Φ_eq_two_of_two_eq_zero` above, was
PROVEN 2026-07-27 by the fibre count, so this node is now sorry-free).
The multiplicity statement `rootMultiplicity_Φ_sub_C_mul_ΨSq` below is
derived from `(★)` in every case EXCEPT the one where `x` is a MULTIPLE root of
`Ψ₂Sq` — this node.

The hypothesis `Ψ₂Sq(x) = Ψ₂Sq'(x) = 0` is VACUOUS when `2 ≠ 0` in `F`
(`TorsionCard.separable_Ψ₂Sq`: `Ψ₂Sq` is separable for `Δ ≠ 0` and `2 ≠ 0`), so
this is exactly the characteristic-`2` case, stated without mentioning the
characteristic.  `two_eq_zero_of_Ψ₂Sq_inseparable` above now DERIVES `(2 : F) = 0`
from the hypotheses, so nothing is assumed.

In characteristic `2`, `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆ = (a₁X + a₃)²`, whose
derivative vanishes identically; the hypothesis then says `a₁x + a₃ = 0`, i.e.
`P₀ = (x, y)` is the unique nonzero `2`-torsion point.  The case `a₁ = 0` is
empty rather than assumed away: there `Ψ₂Sq = a₃²` is a nonzero constant unless
`a₃ = 0`, and `a₁ = a₃ = 0` forces `Δ = 0` (`a₁_ne_zero_of_two_eq_zero`).

**HOW IT IS PROVED NOW.**  Step 5 gives `G := Φ_p − x·Ψ²_p = (X − x)·Φ_p'`, and
`Ψ₂Sq(a) = a₁²(a − x)²` vanishes exactly at `a = x`.  Hence three cases:

* `Φ_p(a) ≠ x·Ψ²_p(a)`: `a` is not a root of `G`, both sides are `0`.
* `a = x`: the ramification index `d_S` is `2`, and `mult_x(G) = 1` because
  `Φ_p'(x) = Ψ²_p(x) ≠ 0` by step 6 and `hΨ`.  So `1 · 2 = 2`.
* `a ≠ x`: `d_S = 1`, and `mult_a(G) = mult_a(Φ_p')`, which is `2` by the
  residual leaf.  So `2 · 1 = 2`.

The old note here said "what would settle it: the fibre count", and that is still
true — but it is now needed for ONE case only, and is isolated in the leaf above
rather than entangled with the characteristic-`2` algebra. -/
theorem rootMultiplicity_Φ_sub_C_mul_ΨSq_of_Ψ₂Sq_inseparable
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0) {a x : F}
    (hΨ : ((W.ΨSq (p : ℤ)).eval a) ≠ 0)
    (hx0 : W.Ψ₂Sq.eval x = 0)
    (hx1 : (Polynomial.derivative W.Ψ₂Sq).eval x = 0) :
    ((W.Φ (p : ℤ) - Polynomial.C x * W.ΨSq (p : ℤ)).rootMultiplicity a : ℤ) *
        (if W.Ψ₂Sq.eval a = 0 then 2 else 1) =
      if (W.Φ (p : ℤ)).eval a = x * (W.ΨSq (p : ℤ)).eval a then
        (if W.Ψ₂Sq.eval x = 0 then 2 else 1) else 0 := by
  classical
  have h2 : (2 : F) = 0 := two_eq_zero_of_Ψ₂Sq_inseparable hΔ hx0 hx1
  have ha₁ : W.a₁ ≠ 0 := a₁_ne_zero_of_two_eq_zero h2 hΔ hx0
  have ha₃ : W.a₃ = W.a₁ * x := a₃_eq_of_two_eq_zero h2 hx0
  have hfact : W.Φ ((p : ℕ) : ℤ) - Polynomial.C x * W.ΨSq ((p : ℕ) : ℤ)
      = (Polynomial.X - Polynomial.C x) * Polynomial.derivative (W.Φ ((p : ℕ) : ℤ)) :=
    Φ_sub_C_mul_ΨSq_eq_X_sub_C_mul_derivative_Φ h2 hΔ hp hx0
  have hG0 : W.Φ ((p : ℕ) : ℤ) - Polynomial.C x * W.ΨSq ((p : ℕ) : ℤ) ≠ 0 :=
    Φ_sub_C_mul_ΨSq_ne_zero x
  have hcond : W.Ψ₂Sq.eval a = 0 ↔ a = x := by
    rw [eval_Ψ₂Sq_eq_sq_of_two_eq_zero h2 a, pow_eq_zero_iff (two_ne_zero), ha₃]
    constructor
    · intro h
      have hz : W.a₁ * (a - x) = 0 := by linear_combination h - W.a₁ * x * h2
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' ha₁
      · exact sub_eq_zero.mp h'
    · rintro rfl
      linear_combination W.a₁ * a * h2
  rw [if_pos hx0]
  by_cases hr : (W.Φ ((p : ℕ) : ℤ)).eval a = x * (W.ΨSq ((p : ℕ) : ℤ)).eval a
  · rw [if_pos hr]
    by_cases hax : a = x
    · subst hax
      rw [if_pos (hcond.mpr rfl)]
      have hD : (Polynomial.derivative (W.Φ ((p : ℕ) : ℤ))).rootMultiplicity a = 0 := by
        refine Polynomial.rootMultiplicity_eq_zero ?_
        rw [Polynomial.IsRoot.def, eval_derivative_Φ_eq_eval_ΨSq_of_two_eq_zero h2 hp hx0]
        exact hΨ
      rw [hfact, Polynomial.rootMultiplicity_mul (hfact ▸ hG0), hD,
        Polynomial.rootMultiplicity_X_sub_C_self]
      norm_num
    · rw [if_neg (fun h => hax (hcond.mp h))]
      have hXm : (Polynomial.X - Polynomial.C x : Polynomial F).rootMultiplicity a = 0 := by
        refine Polynomial.rootMultiplicity_eq_zero ?_
        simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C]
        exact sub_ne_zero.mpr hax
      rw [hfact, Polynomial.rootMultiplicity_mul (hfact ▸ hG0), hXm,
        rootMultiplicity_derivative_Φ_eq_two_of_two_eq_zero h2 hΔ hp hΨ hx0 hax hr]
      norm_num
  · rw [if_neg hr]
    have hzero :
        (W.Φ ((p : ℕ) : ℤ) - Polynomial.C x * W.ΨSq ((p : ℕ) : ℤ)).rootMultiplicity a = 0 := by
      refine Polynomial.rootMultiplicity_eq_zero ?_
      simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C]
      exact fun h => hr (sub_eq_zero.mp h)
    rw [hzero]
    norm_num

omit [IsAlgClosed F] in
/-- **L4-7 (PROVEN over `sq_wronskian_mul_Ψ₂Sq` and
`rootMultiplicity_Φ_sub_C_mul_ΨSq_of_Ψ₂Sq_inseparable`): multiplicity
one for `[p]`, in `x`-coordinates only.**  This is the geometric
content of the L4-7 stage, as a statement about POLYNOMIALS: no
function field, no ideals, no divisors.

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

**PROOF (an order count over `(★)`).**  Put `G = Φ_p − x·ΨSq_p`,
`m = mult_a(G)`, `Wr = Φ_p'·ΨSq_p − Φ_p·ΨSq_p'` and
`Ñ = 4Φ_p³ + b₂Φ_p²ΨSq_p + 2b₄Φ_pΨSq_p² + b₆ΨSq_p³`, so that `(★)` is
`Wr²·Ψ₂Sq = p²·ΨSq_p·Ñ`.  If `a` is not a root of `G` both sides of the
claim are `0`.  Otherwise `m ≥ 1`, and since `Φ_p = G + x·ΨSq_p`,

`Ñ = ΨSq_p³·Ψ₂Sq(x) + G·(ΨSq_p²·Ψ₂Sq'(x) + G·(…))`,

while `Wr = G'·ΨSq_p − G·ΨSq_p'` gives `(X − a)^{m−1} ∣ Wr`.  Reading
multiplicities at `a` in `(★)` — where `ΨSq_p(a) ≠ 0` and `p² ≠ 0` —
gives `2·mult_a(Wr) + mult_a(Ψ₂Sq) = mult_a(Ñ)`, and then:

* `Ψ₂Sq(x) ≠ 0`: `Ñ(a) = Ψ₂Sq(x)·ΨSq_p(a)³ ≠ 0`, so both summands
  vanish; `mult_a(Wr) = 0` forces `m ≤ 1`, so `m = 1`, and
  `mult_a(Ψ₂Sq) = 0` makes both `d`'s equal `1`.
* `Ψ₂Sq(x) = 0 ≠ Ψ₂Sq'(x)`: `Ñ = G·R` with `R(a) ≠ 0`, so
  `mult_a(Ñ) = m`.  If `Ψ₂Sq(a) = 0` then `2(m−1) + 1 ≤ m` forces
  `m = 1` and the claim is `1·2 = 2`; otherwise `2(m−1) ≤ 2·mult_a(Wr)
  = m` forces `m ≤ 2`, and `m` is even and positive, so `m = 2` and the
  claim is `2·1 = 2`.  (Note that `mult_a(Ψ₂Sq) ≥ 2` is impossible
  here — the inequality alone rules it out, so no separability of
  `Ψ₂Sq` at `a` is needed.)
* `Ψ₂Sq(x) = Ψ₂Sq'(x) = 0`: this is the leaf
  `rootMultiplicity_Φ_sub_C_mul_ΨSq_of_Ψ₂Sq_inseparable`, vacuous
  unless `2 = 0` in `F`. -/
theorem rootMultiplicity_Φ_sub_C_mul_ΨSq (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {a x : F} (hΨ : ((W.ΨSq (p : ℤ)).eval a) ≠ 0) :
    ((W.Φ (p : ℤ) - Polynomial.C x * W.ΨSq (p : ℤ)).rootMultiplicity a : ℤ) *
        (if W.Ψ₂Sq.eval a = 0 then 2 else 1) =
      if (W.Φ (p : ℤ)).eval a = x * (W.ΨSq (p : ℤ)).eval a then
        (if W.Ψ₂Sq.eval x = 0 then 2 else 1) else 0 := by
  classical
  have hpF : (((p : ℤ) : F)) ≠ 0 := by exact_mod_cast hp
  set Ψ : Polynomial F := W.ΨSq (p : ℤ) with hΨdef
  set Φ : Polynomial F := W.Φ (p : ℤ) with hΦdef
  set G : Polynomial F := Φ - Polynomial.C x * Ψ with hGdef
  have hGne : G ≠ 0 := Φ_sub_C_mul_ΨSq_ne_zero x
  have hΨne : Ψ ≠ 0 := W.ΨSq_ne_zero hpF
  have hΨ2ne : W.Ψ₂Sq ≠ 0 := Ψ₂Sq_ne_zero_of_Δ_ne_zero hΔ
  have hC : Polynomial.C ((((p : ℤ)) : F) ^ 2) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]
    exact pow_ne_zero 2 hpF
  have hGeval : G.eval a = Φ.eval a - x * Ψ.eval a := by
    rw [hGdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  by_cases hroot : G.eval a = 0
  swap
  · have h1 : G.rootMultiplicity a = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hroot)
    have h2 : ¬ (Φ.eval a = x * Ψ.eval a) := by
      intro hc
      exact hroot (by rw [hGeval, hc, sub_self])
    rw [h1, if_neg h2]
    norm_num
  have hcond : Φ.eval a = x * Ψ.eval a := by
    have hz := hroot
    rw [hGeval, sub_eq_zero] at hz
    exact hz
  rw [if_pos hcond]
  set m : ℕ := G.rootMultiplicity a with hmdef
  have hm1 : 1 ≤ m := (Polynomial.rootMultiplicity_pos hGne).mpr hroot
  -- the Wronskian
  set Wr : Polynomial F :=
    Polynomial.derivative Φ * Ψ - Φ * Polynomial.derivative Ψ with hWrdef
  have hWrG : Wr = Polynomial.derivative G * Ψ - G * Polynomial.derivative Ψ := by
    rw [hWrdef, hGdef]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_C_mul]
    ring
  have hdvdWr : (Polynomial.X - Polynomial.C a) ^ (m - 1) ∣ Wr := by
    rw [hWrG]
    refine dvd_sub (Dvd.dvd.mul_right ?_ _) (Dvd.dvd.mul_right ?_ _)
    · exact Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd
        (Polynomial.pow_rootMultiplicity_dvd G a)
    · exact dvd_trans (pow_dvd_pow _ (Nat.sub_le m 1))
        (Polynomial.pow_rootMultiplicity_dvd G a)
  -- the homogenized cubic `ΨSq_p³ · Ψ₂Sq(Φ_p/ΨSq_p)`
  set Nt : Polynomial F :=
    Polynomial.C 4 * Φ ^ 3 + Polynomial.C W.b₂ * Φ ^ 2 * Ψ +
      Polynomial.C (2 * W.b₄) * Φ * Ψ ^ 2 + Polynomial.C W.b₆ * Ψ ^ 3 with hNtdef
  set Rq : Polynomial F :=
    Polynomial.C ((Polynomial.derivative W.Ψ₂Sq).eval x) * Ψ ^ 2 +
      G * (Polynomial.C (12 * x + W.b₂) * Ψ + Polynomial.C 4 * G) with hRqdef
  have hev0 : W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
    simp [WeierstrassCurve.Ψ₂Sq]
  have hev1 : (Polynomial.derivative W.Ψ₂Sq).eval x =
      12 * x ^ 2 + 2 * W.b₂ * x + 2 * W.b₄ := by
    simp [WeierstrassCurve.Ψ₂Sq]
    ring
  have hdecomp : Nt = Polynomial.C (W.Ψ₂Sq.eval x) * Ψ ^ 3 + G * Rq := by
    rw [hNtdef, hRqdef, hGdef, hev0, hev1]
    simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow, map_ofNat]
    ring
  have hRqa : Rq.eval a = (Polynomial.derivative W.Ψ₂Sq).eval x * Ψ.eval a ^ 2 := by
    rw [hRqdef]
    simp [hroot]
  have hNta : Nt.eval a = W.Ψ₂Sq.eval x * Ψ.eval a ^ 3 := by
    rw [hdecomp]
    simp [hroot]
  -- the identity `(★)`
  have hstar : Wr ^ 2 * W.Ψ₂Sq = Polynomial.C (((p : ℤ) : F) ^ 2) * Ψ * Nt := by
    rw [hWrdef, hΨdef, hΦdef, hNtdef]
    exact sq_wronskian_mul_Ψ₂Sq W hpF
  -- the multiplicity bookkeeping, once `Nt ≠ 0` is known
  have hkey : ∀ hNtne : Nt ≠ 0,
      2 * Wr.rootMultiplicity a + W.Ψ₂Sq.rootMultiplicity a =
        Nt.rootMultiplicity a ∧ Wr ≠ 0 := by
    intro hNtne
    have hrhsne : Polynomial.C (((p : ℤ) : F) ^ 2) * Ψ * Nt ≠ 0 :=
      mul_ne_zero (mul_ne_zero hC hΨne) hNtne
    have hlhsne : Wr ^ 2 * W.Ψ₂Sq ≠ 0 := by rw [hstar]; exact hrhsne
    have hWrne : Wr ≠ 0 := by
      intro h0
      rw [h0] at hlhsne
      simp at hlhsne
    refine ⟨?_, hWrne⟩
    have h1 : (Wr ^ 2 * W.Ψ₂Sq).rootMultiplicity a =
        2 * Wr.rootMultiplicity a + W.Ψ₂Sq.rootMultiplicity a := by
      rw [pow_two] at hlhsne ⊢
      rw [Polynomial.rootMultiplicity_mul hlhsne,
        Polynomial.rootMultiplicity_mul (mul_ne_zero hWrne hWrne)]
      ring
    have h2 : (Polynomial.C (((p : ℤ) : F) ^ 2) * Ψ * Nt).rootMultiplicity a =
        Nt.rootMultiplicity a := by
      rw [Polynomial.rootMultiplicity_mul hrhsne,
        Polynomial.rootMultiplicity_mul (mul_ne_zero hC hΨne),
        Polynomial.rootMultiplicity_C,
        Polynomial.rootMultiplicity_eq_zero
          (by simpa [Polynomial.IsRoot] using hΨ)]
      omega
    rw [← h1, hstar, h2]
  have hmWr : ∀ hWrne : Wr ≠ 0, m - 1 ≤ Wr.rootMultiplicity a := fun hWrne =>
    (Polynomial.le_rootMultiplicity_iff hWrne).mpr hdvdWr
  by_cases hx0 : W.Ψ₂Sq.eval x = 0
  swap
  · -- `P` is not `2`-torsion
    have hNta0 : Nt.eval a ≠ 0 := by
      rw [hNta]
      exact mul_ne_zero hx0 (pow_ne_zero _ hΨ)
    have hNtne : Nt ≠ 0 := fun h => hNta0 (by rw [h]; simp)
    obtain ⟨hsum, hWrne⟩ := hkey hNtne
    have hNtrm : Nt.rootMultiplicity a = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hNta0)
    rw [hNtrm] at hsum
    have hWrrm : Wr.rootMultiplicity a = 0 := by omega
    have hΨ2rm : W.Ψ₂Sq.rootMultiplicity a = 0 := by omega
    have hmle : m ≤ 1 := by
      have hb := hmWr hWrne
      omega
    have hmeq : m = 1 := le_antisymm hmle hm1
    have hΨ2a : W.Ψ₂Sq.eval a ≠ 0 := by
      intro hc
      have hpos : 0 < W.Ψ₂Sq.rootMultiplicity a :=
        (Polynomial.rootMultiplicity_pos hΨ2ne).mpr hc
      omega
    rw [hmeq, if_neg hΨ2a, if_neg hx0]
    norm_num
  by_cases hx1 : (Polynomial.derivative W.Ψ₂Sq).eval x = 0
  · have hres := rootMultiplicity_Φ_sub_C_mul_ΨSq_of_Ψ₂Sq_inseparable hΔ hp hΨ hx0 hx1
    rw [← hΦdef, ← hΨdef, ← hGdef, ← hmdef, if_pos hcond] at hres
    exact hres
  -- `P` is `2`-torsion and `x` is a simple root of `Ψ₂Sq`
  have hRqa0 : Rq.eval a ≠ 0 := by
    rw [hRqa]
    exact mul_ne_zero hx1 (pow_ne_zero _ hΨ)
  have hRqne : Rq ≠ 0 := fun h => hRqa0 (by rw [h]; simp)
  have hNtGR : Nt = G * Rq := by
    rw [hdecomp, hx0]
    simp
  have hNtne : Nt ≠ 0 := by rw [hNtGR]; exact mul_ne_zero hGne hRqne
  obtain ⟨hsum, hWrne⟩ := hkey hNtne
  have hRqrm : Rq.rootMultiplicity a = 0 :=
    Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hRqa0)
  have hNtrm : Nt.rootMultiplicity a = m := by
    rw [hNtGR, Polynomial.rootMultiplicity_mul (by rw [← hNtGR]; exact hNtne), hRqrm,
      ← hmdef, add_zero]
  rw [hNtrm] at hsum
  have hbnd := hmWr hWrne
  by_cases hΨ2a : W.Ψ₂Sq.eval a = 0
  · have hpos : 0 < W.Ψ₂Sq.rootMultiplicity a :=
      (Polynomial.rootMultiplicity_pos hΨ2ne).mpr hΨ2a
    have hmeq : m = 1 := by omega
    rw [hmeq, if_pos hΨ2a, if_pos hx0]
    norm_num
  · have hzero : W.Ψ₂Sq.rootMultiplicity a = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hΨ2a)
    rw [hzero, add_zero] at hsum
    have hmeq : m = 2 := by omega
    rw [hmeq, if_neg hΨ2a, if_pos hx0]
    norm_num

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

omit [DecidableEq F] [IsAlgClosed F] in
/-- **A sign does not move a principal fractional ideal** (PROVEN):
`⟨−z⟩ = ⟨z⟩`, because `−1` is a unit of `F[W]` and the coerced unit
ideal is `1`.  Needed because the norm identity of a line
(`CoordinateRing.C_addPolynomial_slope`) carries an overall `−`. -/
lemma spanSingleton_neg' (z : W.FunctionField) :
    FractionalIdeal.spanSingleton W.CoordinateRing⁰ (-z) =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ z := by
  rw [show -z = algebraMap W.CoordinateRing W.FunctionField (-1) * z by simp,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← FractionalIdeal.coeIdeal_span_singleton,
    Ideal.span_singleton_eq_top.mpr (isUnit_one.neg),
    FractionalIdeal.coeIdeal_top, one_mul]

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The point ideal of an affine point is maximal** (PROVEN):
`xyIdeal_isMaximal`, packaged for a `W.Point` that is merely known to
be nonzero rather than presented as a `Point.some`. -/
lemma pointIdeal_isMaximal_of_ne_zero {Q : W.Point} (hQ : Q ≠ 0) :
    (pointIdeal W Q).IsMaximal := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some x y h => rw [pointIdeal_some]; exact xyIdeal_isMaximal h.left

/-- **The point ideal of an affine point is a prime of the ideal
monoid** (PROVEN): `prime_pointIdeal`, in the `Q ≠ 0` packaging. -/
lemma prime_pointIdeal_of_ne_zero (hΔ : W.Δ ≠ 0) {Q : W.Point} (hQ : Q ≠ 0) :
    Prime (pointIdeal W Q) := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some x y h => exact prime_pointIdeal hΔ h

/-- **A function whose divisor is a three-point sum vanishes exactly at
those three points** (PROVEN): if `⟨z⟩ = I_A·I_B·I_C` with `A`, `B`, `C`
affine, then for an affine `Q` one has `z ∈ I_Q` iff `Q` is one of them.
The forward direction is primality of `I_Q` (`prime_pointIdeal`) applied
twice, followed by maximality to upgrade `I_R ≤ I_Q` to `I_R = I_Q` and
`pointIdeal_injective` to `R = Q`; the reverse is `I_A·I_B·I_C ≤ I_R`
for each factor.  This is the dictionary that turns both the line class
and its hyperelliptic conjugate into point conditions. -/
lemma mem_pointIdeal_iff_of_span_eq_prod_three (hΔ : W.Δ ≠ 0)
    {A B C Q : W.Point} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hQ : Q ≠ 0)
    {z : W.CoordinateRing}
    (hspan : Ideal.span {z} =
      pointIdeal W A * (pointIdeal W B * pointIdeal W C)) :
    z ∈ pointIdeal W Q ↔ (Q = A ∨ Q = B ∨ Q = C) := by
  haveI := isDedekindDomain_coordinateRing hΔ
  have hQp : Prime (pointIdeal W Q) := prime_pointIdeal_of_ne_zero hΔ hQ
  have key : ∀ R : W.Point, R ≠ 0 → pointIdeal W Q ∣ pointIdeal W R → Q = R := by
    intro R hR hdvd
    exact (pointIdeal_injective
      ((pointIdeal_isMaximal_of_ne_zero hR).eq_of_le
        (pointIdeal_isMaximal_of_ne_zero hQ).ne_top
        (Ideal.dvd_iff_le.mp hdvd))).symm
  constructor
  · intro hz
    have hdvd : pointIdeal W Q ∣
        pointIdeal W A * (pointIdeal W B * pointIdeal W C) := by
      rw [← hspan, Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
      exact hz
    rcases hQp.dvd_mul.mp hdvd with h | h
    · exact Or.inl (key A hA h)
    · rcases hQp.dvd_mul.mp h with h' | h'
      · exact Or.inr (Or.inl (key B hB h'))
      · exact Or.inr (Or.inr (key C hC h'))
  · intro hQeq
    have hle : Ideal.span {z} ≤ pointIdeal W Q := by
      rw [hspan]
      rcases hQeq with rfl | rfl | rfl
      · exact Ideal.mul_le_right
      · exact le_trans Ideal.mul_le_left Ideal.mul_le_right
      · exact le_trans Ideal.mul_le_left Ideal.mul_le_left
    exact hle (Ideal.mem_span_singleton_self z)

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The divisor of a vertical** (PROVEN): `⟨X − a⟩ = I_P · I_{⊖P}` for
`P = (a, b)` — mathlib's `CoordinateRing.XYIdeal_neg_mul`, restated in
the `pointIdeal` vocabulary. -/
lemma span_XClass_eq_pointIdeal_mul_neg {a b : F} (k : W.Nonsingular a b) :
    Ideal.span {CoordinateRing.XClass W a} =
      pointIdeal W (.some a b k) * pointIdeal W (-(.some a b k : W.Point)) := by
  calc Ideal.span {CoordinateRing.XClass W a} = CoordinateRing.XIdeal W a := rfl
    _ = CoordinateRing.XYIdeal W a (Polynomial.C (W.negY a b)) *
        CoordinateRing.XYIdeal W a (Polynomial.C b) :=
      (CoordinateRing.XYIdeal_neg_mul k).symm
    _ = pointIdeal W (.some a b k) * pointIdeal W (-(.some a b k : W.Point)) := by
      rw [Point.neg_some, pointIdeal_some, pointIdeal_some, mul_comm]

/-- **The arithmetic core of the line brick** (PROVEN, pure integer
arithmetic): two nonnegative orders `A`, `B` whose sum is `m + m'`, each
positive exactly when its multiplicity is, and with the degenerate case
`m, m' > 0` forcing `m = m' = 1`, satisfy `A = m`.  Isolated from the
geometry so that the three cases of the line brick — `T ∉ D`,
`⊖T ∉ D`, and `T = ⊖T ∈ D` — are discharged by `omega`. -/
lemma count_arith {A B : ℤ} {m m' : ℕ}
    (hsum : A + B = (m : ℤ) + (m' : ℤ)) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : 1 ≤ A ↔ 0 < m) (hB : 1 ≤ B ↔ 0 < m')
    (hboth : 0 < m → 0 < m' → m = 1 ∧ m' = 1) :
    A = (m : ℤ) := by
  by_cases hm : 0 < m
  · by_cases hm' : 0 < m'
    · obtain ⟨e, e'⟩ := hboth hm hm'
      have h1 : 1 ≤ A := hA.mpr hm
      have h2 : 1 ≤ B := hB.mpr hm'
      subst e; subst e'; omega
    · have hBle : B ≤ 0 := by by_contra hc; exact hm' (hB.mp (by omega))
      have hz : m' = 0 := by omega
      subst hz; omega
  · have hz : m = 0 := by omega
    subst hz
    have hAle : A ≤ 0 := by by_contra hc; exact hm (hA.mp (by omega))
    omega

section CountValuation

/-!
### The `v`-adic order of a principal fractional ideal is a valuation

`FractionalIdeal.count` is the `v`-exponent in the factorization, and
mathlib's `Factorization.lean` supplies `count_mul`, `count_mono` and
`count_coe_nonneg` but **nothing about sums** — the gap recorded by the
two `[p]`-pullback leaves below.  It is filled here once and for all by
identifying `count` with `IsDedekindDomain.HeightOneSpectrum.valuation`,
which IS a genuine valuation and therefore ultrametric.
-/

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : IsDedekindDomain.HeightOneSpectrum R)

/-- **The `v`-adic valuation of a nonzero element of the fraction field is
the exponential of minus its `count`.** -/
theorem valuation_eq_exp_neg_count {w : K} (hw : w ≠ 0) :
    v.valuation K w =
      WithZero.exp (-(FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ w))) := by
  classical
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective R⁰ w
  simp only at hrs
  subst hrs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hw
    exact hw rfl
  have hs0 : (s : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  -- the count side
  have hmul : IsLocalization.mk' K r s * algebraMap R K (s : R) = algebraMap R K r := by
    rw [IsLocalization.mk'_spec]
  have hspanne : ∀ z : K, z ≠ 0 →
      FractionalIdeal.spanSingleton R⁰ z ≠ 0 := by
    intro z hz
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hz
  have halg : ∀ z : R, z ≠ 0 → (algebraMap R K z) ≠ 0 := by
    intro z hz
    exact fun h0 => hz ((injective_iff_map_eq_zero _).mp
      (IsFractionRing.injective R K) _ h0)
  have hcountmul :
      FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K r s)) +
        FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton R⁰ (algebraMap R K (s : R))) =
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (algebraMap R K r)) := by
    rw [← FractionalIdeal.count_mul K v (hspanne _ hw)
        (hspanne _ (halg _ hs0)),
      FractionalIdeal.spanSingleton_mul_spanSingleton, hmul]
  have hcoe : ∀ z : R, z ≠ 0 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K z)) =
        ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {z})).factors : ℤ) := by
    intro z hz
    rw [← FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.count_coe K v (by simpa [Ideal.span_singleton_eq_bot] using hz)]
  rw [hcoe _ hr0, hcoe _ hs0] at hcountmul
  -- the valuation side
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg hr0, v.intValuation_if_neg hs0]
  rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
  congr 1
  omega

/-- Multiplicativity of `count` on principal fractional ideals. -/
theorem count_spanSingleton_mul {w₁ w₂ : K} (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (w₁ * w₂)) =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ w₁) +
        FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ w₂) := by
  have hspanne : ∀ z : K, z ≠ 0 →
      FractionalIdeal.spanSingleton R⁰ z ≠ 0 := by
    intro z hz
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hz
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v (hspanne _ h₁) (hspanne _ h₂)]

/-- A sign does not move the `count` of a principal fractional ideal. -/
theorem count_spanSingleton_neg (w : K) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (-w)) =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ w) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [FractionalIdeal.count_zero]
  · rw [show -w = (-1 : K) * w by ring,
      count_spanSingleton_mul v (by norm_num) hw]
    have : FractionalIdeal.spanSingleton R⁰ (-1 : K) = 1 := by
      rw [show (-1 : K) = algebraMap R K (-1) by simp,
        ← FractionalIdeal.coeIdeal_span_singleton,
        Ideal.span_singleton_eq_top.mpr isUnit_one.neg,
        FractionalIdeal.coeIdeal_top]
    rw [this, FractionalIdeal.count_one]
    ring

/-- **The ultrametric inequality for `count`.** -/
theorem le_count_spanSingleton_add {n : ℤ} {w₁ w₂ : K}
    (h₁ : n ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ w₁))
    (h₂ : n ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ w₂))
    (h : w₁ + w₂ ≠ 0) :
    n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ (w₁ + w₂)) := by
  rcases eq_or_ne w₁ 0 with rfl | hw₁
  · simpa using h₂
  rcases eq_or_ne w₂ 0 with rfl | hw₂
  · simpa using h₁
  have key := (v.valuation K).map_add w₁ w₂
  rw [valuation_eq_exp_neg_count v hw₁, valuation_eq_exp_neg_count v hw₂,
    valuation_eq_exp_neg_count v h] at key
  have hk1 : WithZero.exp (-(FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ w₁))) ≤ WithZero.exp (-n) := by
    rw [WithZero.exp_le_exp]; omega
  have hk2 : WithZero.exp (-(FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ w₂))) ≤ WithZero.exp (-n) := by
    rw [WithZero.exp_le_exp]; omega
  have hb := le_trans key (max_le hk1 hk2)
  rw [WithZero.exp_le_exp] at hb
  omega

/-- `count` of the image of a ring element is nonnegative. -/
theorem count_spanSingleton_algebraMap_nonneg (z : R) :
    0 ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ (algebraMap R K z)) := by
  rw [← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K v _

/-- The subring of elements of `K` with nonnegative `count` at `v`. -/
def countNonneg : Subring K where
  carrier := {w : K | 0 ≤ FractionalIdeal.count K v
    (FractionalIdeal.spanSingleton R⁰ w)}
  zero_mem' := by simp [FractionalIdeal.count_zero]
  one_mem' := by simp [FractionalIdeal.count_one]
  add_mem' := by
    intro a b ha hb
    rcases eq_or_ne (a + b) 0 with h | h
    · simp [h, FractionalIdeal.count_zero]
    · exact le_count_spanSingleton_add v ha hb h
  mul_mem' := by
    intro a b ha hb
    rcases eq_or_ne a 0 with rfl | ha0
    · simp [FractionalIdeal.count_zero]
    rcases eq_or_ne b 0 with rfl | hb0
    · simp [FractionalIdeal.count_zero]
    have := count_spanSingleton_mul v ha0 hb0
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    omega
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rwa [count_spanSingleton_neg v]

@[simp] lemma mem_countNonneg {w : K} :
    w ∈ countNonneg v ↔ 0 ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ w) := Iff.rfl

/-- Multiplying by something of nonnegative `count` does not lower a
lower bound on `count`. -/
theorem le_count_spanSingleton_mul_of_nonneg {a b : K} {n : ℤ}
    (ha : 0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a))
    (hb : n ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ b))
    (h : a * b ≠ 0) :
    n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ (a * b)) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at h
  have hb0 : b ≠ 0 := by rintro rfl; simp at h
  rw [count_spanSingleton_mul v ha0 hb0]
  omega

/-- Nonpositive-bound form of the ultrametric: no nonvanishing side
condition is needed, because `count 0 = 0`. -/
theorem le_count_spanSingleton_add' {n : ℤ} (hn : n ≤ 0) {w₁ w₂ : K}
    (h₁ : n ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ w₁))
    (h₂ : n ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ w₂)) :
    n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ (w₁ + w₂)) := by
  rcases eq_or_ne (w₁ + w₂) 0 with h | h
  · rw [h]
    simpa [FractionalIdeal.count_zero] using hn
  · exact le_count_spanSingleton_add v h₁ h₂ h

/-- Nonpositive-bound form of the product estimate. -/
theorem le_count_spanSingleton_mul' {n : ℤ} (hn : n ≤ 0) {a b : K}
    (ha : 0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ a))
    (hb : n ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ b)) :
    n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ (a * b)) := by
  rcases eq_or_ne (a * b) 0 with h | h
  · rw [h]
    simpa [FractionalIdeal.count_zero] using hn
  · exact le_count_spanSingleton_mul_of_nonneg v ha hb h

end CountValuation

omit [DecidableEq F] [IsAlgClosed F] in
/-- **A subring of the target absorbs a ring hom out of the coordinate
ring as soon as it absorbs the constants and the two coordinates.** -/
theorem coordinateRing_forall_mem_subring {A : Type*} [CommRing A]
    {ψ : W.CoordinateRing →+* A} (S : Subring A)
    (hC : ∀ d : F, ψ (coordC W d) ∈ S) (hX : ψ (coordX W) ∈ S)
    (hY : ψ (coordY W) ∈ S) (z : W.CoordinateRing) : ψ z ∈ S := by
  have hpoly : ∀ r : Polynomial F,
      ψ (CoordinateRing.mk W (Polynomial.C r)) ∈ S := by
    intro r
    induction r using Polynomial.induction_on with
    | C d => exact hC d
    | add f g hf hg =>
      simp only [map_add]
      exact S.add_mem hf hg
    | monomial n d _ =>
      simp only [map_mul, map_pow]
      exact S.mul_mem (hC d) (S.pow_mem hX _)
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  induction f using Polynomial.induction_on with
  | C r => exact hpoly r
  | add f g hf hg =>
    simp only [map_add]
    exact S.add_mem hf hg
  | monomial n r _ =>
    simp only [map_mul, map_pow]
    exact S.mul_mem (hpoly r) (S.pow_mem hY _)

/-- **L4-7 (PROVEN 2026-07-27): the `[p]`-pullback is REGULAR at a place
over an affine point.**  For `S ≠ O` affine with `p • S ≠ O`, and any
nonzero `z ∈ F[W]`, the pulled-back function `[p]^* z = z ∘ [p]` has no
pole at the place of `S`:

`ord_S([p]^* z) ≥ 0`.

Geometrically this is just that `[p]` carries `S` to the AFFINE point
`p • S`, so a function regular on the affine curve stays regular after
composing with `[p]`.

**PROOF.**  The set of elements of `K = Frac F[W]` of nonnegative order
at `v` is a SUBRING (`countNonneg`, above) — that is exactly what the
ultrametric inequality for `FractionalIdeal.count` buys, and it is the
lemma the previous owner of this leaf recorded as missing from mathlib's
`Factorization.lean` (which has `count_mul`, `count_mono` and
`count_coe_nonneg` but nothing about sums).  Since `[p]^*` is a ring hom
out of `F[W]`, which is generated by the constants and the two
coordinate functions (`coordinateRing_forall_mem_subring`), it suffices
to check the three generators:

* constants: `[p]^* c = constHom W c` is the image of `coordC W c`, and
  the image of a ring element always has nonnegative order
  (`count_spanSingleton_algebraMap_nonneg`);
* `ord_S(xp) ≥ 0`: FREE from the vertical brick
  `count_pointEval_XClass_of_smul_ne_zero`, whose value at the vertical
  through `T = p • S` is a `Multiset.count`, hence `≥ 0`; adding back
  the constant `x_T` keeps the order nonnegative;
* `ord_S(yp) ≥ 0`: this is route (ii) of the original leaf note, and it
  is CHARACTERISTIC-FREE.  `yp` is integral over the ring where `xp`
  already has nonnegative order: the Weierstrass equation gives
  `yp² = −a₁ xp yp − a₃ yp + (xp³ + a₂xp² + a₄xp + a₆)`, and if
  `m := ord_S(yp)` were `< 0` then every term on the right has order
  `≥ m` (the polynomial part has order `≥ 0 > m`, the two mixed terms
  order `≥ 0 + m`), so the ultrametric gives `2m = ord(yp²) ≥ m`, i.e.
  `m ≥ 0` — a contradiction.  No `ψ₂`-tracking and no `2 ≠ 0` is needed.

The hypothesis `hz` is not used: the bound holds for `z = 0` too, since
`count 0 = 0`. -/
theorem count_pointEval_nonneg [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S)
    {z : W.CoordinateRing} (hz : z ≠ 0) :
    0 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left z)) := by
  classical
  obtain ⟨xT, yT, hT, hTeq⟩ :
      ∃ (xT yT : F) (hT : W.Nonsingular xT yT),
        ((p : ℤ) • S : W.Point) =
          WeierstrassCurve.Affine.Point.some xT yT hT := by
    cases hcase : ((p : ℤ) • S : W.Point) with
    | zero => exact absurd hcase hpS
    | some xT yT hT => exact ⟨xT, yT, hT, rfl⟩
  -- the two coordinate atoms lie in the nonnegativity subring
  have hxval : pointEval (constHom W) hpn.left (CoordinateRing.XClass W xT) =
      xp - constHom W xT := by
    rw [XClass_eq, map_sub]
    simp only [coordX, coordC]
    rw [pointEval_X, pointEval_C]
  have hxcount := count_pointEval_XClass_of_smul_ne_zero (W := W)
    hΔ hp hptaut hT hS0 hpS hvS
  rw [hxval] at hxcount
  have hxnn : 0 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (xp - constHom W xT)) := by
    rw [hxcount]; exact Int.natCast_nonneg _
  -- `xp` and the constants have nonnegative order
  have hcN : ∀ d : F, constHom W d ∈ countNonneg v := by
    intro d
    rw [mem_countNonneg,
      show constHom W d =
        algebraMap W.CoordinateRing W.FunctionField (coordC W d) from rfl]
    exact count_spanSingleton_algebraMap_nonneg v _
  have hxN : xp ∈ countNonneg v := by
    rw [mem_countNonneg,
      show xp = (xp - constHom W xT) + constHom W xT by ring]
    exact (countNonneg v).add_mem
      ((mem_countNonneg v).mpr hxnn) (hcN xT)
  -- `yp` is integral over `xp`, so its order is nonnegative too
  have hyN : yp ∈ countNonneg v := by
    rw [mem_countNonneg]
    by_contra hneg
    rw [not_le] at hneg
    have hyp0 : yp ≠ 0 := by
      rintro rfl
      simp [FractionalIdeal.count_zero] at hneg
    have hm0 : FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ yp) ≤ 0 := le_of_lt hneg
    have heqc : yp ^ 2 + constHom W W.a₁ * xp * yp + constHom W W.a₃ * yp =
        xp ^ 3 + constHom W W.a₂ * xp ^ 2 + constHom W W.a₄ * xp +
          constHom W W.a₆ := by
      have h2 := ((curveK W).equation_iff xp yp).mp hpn.left
      simpa only [curveK, WeierstrassCurve.map] using h2
    have hsq : yp * yp =
        (-(constHom W W.a₁ * xp * yp)) +
          ((-(constHom W W.a₃ * yp)) +
            (xp ^ 3 + constHom W W.a₂ * xp ^ 2 + constHom W W.a₄ * xp +
              constHom W W.a₆)) := by
      linear_combination heqc
    have hpolyN : (xp ^ 3 + constHom W W.a₂ * xp ^ 2 + constHom W W.a₄ * xp +
        constHom W W.a₆) ∈ countNonneg v :=
      (countNonneg v).add_mem
        ((countNonneg v).add_mem
          ((countNonneg v).add_mem
            ((countNonneg v).pow_mem hxN 3)
            ((countNonneg v).mul_mem (hcN _)
              ((countNonneg v).pow_mem hxN 2)))
          ((countNonneg v).mul_mem (hcN _) hxN))
        (hcN _)
    have h1 := le_count_spanSingleton_mul' v hm0
      ((mem_countNonneg v).mp
        ((countNonneg v).mul_mem (hcN W.a₁) hxN)) (le_refl
      (FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ yp)))
    rw [← count_spanSingleton_neg v
      (constHom W W.a₁ * xp * yp)] at h1
    have h2 := le_count_spanSingleton_mul' v hm0
      ((mem_countNonneg v).mp (hcN W.a₃)) (le_refl
      (FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ yp)))
    rw [← count_spanSingleton_neg v (constHom W W.a₃ * yp)] at h2
    have h3 := le_trans hm0 ((mem_countNonneg v).mp hpolyN)
    have hall := le_count_spanSingleton_add' v hm0 h1
      (le_count_spanSingleton_add' v hm0 h2 h3)
    rw [← hsq, count_spanSingleton_mul v hyp0 hyp0] at hall
    omega
  refine coordinateRing_forall_mem_subring (countNonneg v) ?_ ?_ ?_ z
  · intro d
    rw [show pointEval (constHom W) hpn.left (coordC W d) = constHom W d from
      pointEval_C _ _ _]
    exact hcN d
  · rw [show pointEval (constHom W) hpn.left (coordX W) = xp from
      pointEval_X _ _]
    exact hxN
  · rw [show pointEval (constHom W) hpn.left (coordY W) = yp from
      pointEval_Y _ _]
    exact hyN

omit [DecidableEq F] in
/-- **PROVEN: the pullback of the `y`-coordinate is not a constant.** -/
theorem smul_taut_yCoord_ne_constHom {xp yp : W.FunctionField}
    (hpn : (curveK W).Nonsingular xp yp)
    (hxrel : xp * ((W.ΨSq (p : ℤ)).map (constHom W)).eval (tautX W) =
      ((W.Φ (p : ℤ)).map (constHom W)).eval (tautX W)) (d : F) :
    yp ≠ constHom W d := by
  intro hd
  have heqc : yp ^ 2 + constHom W W.a₁ * xp * yp + constHom W W.a₃ * yp =
      xp ^ 3 + constHom W W.a₂ * xp ^ 2 + constHom W W.a₄ * xp +
        constHom W W.a₆ := by
    have h2 := ((curveK W).equation_iff xp yp).mp hpn.left
    simpa only [curveK, WeierstrassCurve.map] using h2
  set q : Polynomial F := Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2 +
    Polynomial.C (W.a₄ - W.a₁ * d) * Polynomial.X +
    Polynomial.C (W.a₆ - d ^ 2 - W.a₃ * d) with hq
  have hq0 : q ≠ 0 := by
    intro h0
    have hc := congrArg (fun r : Polynomial F => r.coeff 3) h0
    simp only [hq, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C,
      Polynomial.coeff_zero] at hc
    norm_num at hc
  refine eval_map_ne_zero_of_forall_ne_constHom
    (smul_taut_xCoord_ne_constHom hxrel) hq0 ?_
  rw [hd] at heqc
  simp only [hq, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  simp only [map_sub, map_mul, map_pow]
  linear_combination -heqc

/-- **PROVEN: the algebraic core of the `y`-center.**  The pullback of the
PAIR of horizontals through `T` and `⊖T` vanishes at the place of `S`. -/
theorem one_le_count_pointEval_YClass_pair
    [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S)
    {xT yT : F} {hT : W.Nonsingular xT yT}
    (hTeq : ((p : ℤ) • S : W.Point) =
      WeierstrassCurve.Affine.Point.some xT yT hT) :
    1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        ((yp - constHom W yT) *
          (yp - constHom W (W.negY xT yT)))) := by
  classical
  obtain ⟨xp', yp', hpn', hptaut', hxrel⟩ :=
    exists_smul_tautPoint_eq (W := W) hΔ hp
  have hxx : xp = xp' := by
    have hpts := hptaut.symm.trans hptaut'
    injection hpts with hx _
  subst hxx
  -- the vertical brick gives order `≥ 1` for `xp − x_T`
  have hxval : pointEval (constHom W) hpn.left (CoordinateRing.XClass W xT) =
      xp - constHom W xT := by
    rw [XClass_eq, map_sub]
    simp only [coordX, coordC]
    rw [pointEval_X, pointEval_C]
  have hxcount := count_pointEval_XClass_of_smul_ne_zero (W := W)
    hΔ hp hptaut hT hS0 hpS hvS
  rw [hxval] at hxcount
  have hx1 : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (xp - constHom W xT)) := by
    rw [hxcount, hTeq]
    have hcnt : (1 : ℕ) ≤ Multiset.count
        (WeierstrassCurve.Affine.Point.some xT yT hT : W.Point)
        (WeierstrassCurve.Affine.Point.some xT yT hT ::ₘ
          (-WeierstrassCurve.Affine.Point.some xT yT hT : W.Point) ::ₘ 0) := by
      rw [Multiset.count_cons_self]; omega
    exact_mod_cast hcnt
  -- everything in sight has nonnegative order
  have hcN : ∀ d : F, constHom W d ∈ countNonneg v := by
    intro d
    rw [mem_countNonneg,
      show constHom W d =
        algebraMap W.CoordinateRing W.FunctionField (coordC W d) from rfl]
    exact count_spanSingleton_algebraMap_nonneg v _
  have hxN : xp ∈ countNonneg v := by
    rw [mem_countNonneg,
      show xp = (xp - constHom W xT) + constHom W xT by ring]
    exact (countNonneg v).add_mem
      ((mem_countNonneg v).mpr (by omega)) (hcN xT)
  have hyN : yp ∈ countNonneg v := by
    rw [mem_countNonneg,
      show yp = pointEval (constHom W) hpn.left (coordY W) from
        (pointEval_Y _ _).symm]
    have hcoordY0 : coordY W ≠ 0 := by
      have h := CoordinateRing.YClass_ne_zero (W' := W) (0 : Polynomial F)
      simpa [CoordinateRing.YClass, coordY] using h
    exact count_pointEval_nonneg hΔ hp hptaut hS0 hpS hvS
      (z := coordY W) hcoordY0
  -- the two curve equations
  have heqc : yp ^ 2 + constHom W W.a₁ * xp * yp + constHom W W.a₃ * yp =
      xp ^ 3 + constHom W W.a₂ * xp ^ 2 + constHom W W.a₄ * xp +
        constHom W W.a₆ := by
    have h2 := ((curveK W).equation_iff xp yp).mp hpn.left
    simpa only [curveK, WeierstrassCurve.map] using h2
  have heqT : constHom W yT ^ 2 +
      constHom W W.a₁ * constHom W xT * constHom W yT +
      constHom W W.a₃ * constHom W yT =
      constHom W xT ^ 3 + constHom W W.a₂ * constHom W xT ^ 2 +
        constHom W W.a₄ * constHom W xT + constHom W W.a₆ := by
    have h := (W.equation_iff xT yT).mp hT.left
    simpa only [map_add, map_mul, map_pow] using congrArg (constHom W) h
  have hnegY : constHom W (W.negY xT yT) =
      -(constHom W yT) - constHom W W.a₁ * constHom W xT - constHom W W.a₃ := by
    simp [WeierstrassCurve.Affine.negY]
  -- the identity
  set Q : W.FunctionField :=
    (xp ^ 2 + xp * constHom W xT + constHom W xT ^ 2) +
      constHom W W.a₂ * (xp + constHom W xT) + constHom W W.a₄ -
      constHom W W.a₁ * yp with hQdef
  have hident : (yp - constHom W yT) * (yp - constHom W (W.negY xT yT)) =
      Q * (xp - constHom W xT) := by
    rw [hnegY, hQdef]
    linear_combination heqc - heqT
  have hQN : Q ∈ countNonneg v := by
    rw [hQdef]
    exact (countNonneg v).sub_mem
      ((countNonneg v).add_mem
        ((countNonneg v).add_mem
          ((countNonneg v).add_mem
            ((countNonneg v).add_mem
              ((countNonneg v).pow_mem hxN 2)
              ((countNonneg v).mul_mem hxN (hcN xT)))
            ((countNonneg v).pow_mem (hcN xT) 2))
          ((countNonneg v).mul_mem (hcN W.a₂)
            ((countNonneg v).add_mem hxN (hcN xT))))
        (hcN W.a₄))
      ((countNonneg v).mul_mem (hcN W.a₁) hyN)
  have hne : (yp - constHom W yT) *
      (yp - constHom W (W.negY xT yT)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact sub_ne_zero.mpr (smul_taut_yCoord_ne_constHom hpn hxrel yT)
    · exact sub_ne_zero.mpr (smul_taut_yCoord_ne_constHom hpn hxrel _)
  rw [hident]
  exact le_count_spanSingleton_mul_of_nonneg v
    ((mem_countNonneg v).mp hQN) hx1 (hident ▸ hne)

section CountMemBridge

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : IsDedekindDomain.HeightOneSpectrum R)

/-- **`count ≥ 1` for the image of a ring element is membership in `v`**
(PROVEN).  `count` of a principal INTEGRAL ideal is the `v`-exponent of
its factorization (`FractionalIdeal.count_coe`), and an exponent is
nonzero exactly when the prime divides
(`Associates.count_ne_zero_iff_dvd`), i.e. exactly when `z ∈ v`
(`Ideal.dvd_span_singleton`).  This is the local-vanishing dictionary
the `CountValuation` section above was missing: it turns "`ord_S(z) ≥ 1`"
into "`z` vanishes at `S`" for `z` in the coordinate ring. -/
theorem one_le_count_algebraMap_iff_mem {z : R} (hz : z ≠ 0) :
    1 ≤ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (algebraMap R K z)) ↔ z ∈ v.asIdeal := by
  have hspan : Ideal.span {z} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hz
  have hcoe : FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ (algebraMap R K z)) =
      ((Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {z})).factors : ℤ) := by
    rw [← FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.count_coe K v hspan]
  rw [hcoe]
  constructor
  · intro h
    have hne : (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {z})).factors ≠ 0 := by omega
    have hdvd := (Associates.count_ne_zero_iff_dvd hspan v.irreducible).mp hne
    rwa [Ideal.dvd_span_singleton] at hdvd
  · intro h
    have hdvd : v.asIdeal ∣ Ideal.span {z} := Ideal.dvd_span_singleton.mpr h
    have hne := (Associates.count_ne_zero_iff_dvd hspan v.irreducible).mpr hdvd
    omega

end CountMemBridge

omit [DecidableEq F] [IsAlgClosed F] in
/-- **`pointEval` on the class of a BIVARIATE polynomial** (PROVEN): the
two-variable evaluation of the `φ`-mapped polynomial at the point.  The
univariate case is `pointEval_polyClass`; this is what the
division-polynomial classes `ψₙ ∈ F[X][Y]` need. -/
lemma pointEval_mk {K' : Type*} [Field K'] (φ : F →+* K') {x₀ y₀ : K'}
    (h : ((W.map φ).toAffine).Equation x₀ y₀)
    (q : Polynomial (Polynomial F)) :
    pointEval φ h (CoordinateRing.mk W q) =
      (q.map (Polynomial.mapRingHom φ)).evalEval x₀ y₀ := by
  rw [pointEval, AdjoinRoot.lift_mk]
  have h2 := Polynomial.hom_eval₂ q (Polynomial.mapRingHom φ)
    (Polynomial.evalRingHom x₀) (Polynomial.C y₀)
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C] at h2
  rw [Polynomial.evalEval, Polynomial.eval_map]
  exact h2.symm

omit [DecidableEq F] [IsAlgClosed F] in
/-- **At the tautological point, `pointEval` along the constants IS the
structural map to the function field** (PROVEN by
`coordinateRing_ringHom_ext`: both send `X ↦ tautX`, `Y ↦ tautY` and
fix the constants). -/
lemma pointEval_taut_eq_algebraMap (W : WeierstrassCurve.Affine F) :
    pointEval (constHom W) (taut_equation W) =
      algebraMap W.CoordinateRing W.FunctionField := by
  refine coordinateRing_ringHom_ext (fun d => ?_) ?_ ?_
  · rw [pointEval_C]; rfl
  · rw [pointEval_X]; rfl
  · rw [pointEval_Y]; rfl

omit [DecidableEq F] [IsAlgClosed F] in
/-- **The class of a bivariate polynomial, read in the function field**
(PROVEN): the bivariate analogue of `algebraMap_polyClass`. -/
lemma algebraMap_mk_eq_evalEval (W : WeierstrassCurve.Affine F)
    (q : Polynomial (Polynomial F)) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W q) =
      (q.map (Polynomial.mapRingHom (constHom W))).evalEval
        (tautX W) (tautY W) := by
  rw [← pointEval_taut_eq_algebraMap W, pointEval_mk]

omit [IsAlgClosed F] in
/-- **A nonzero constant has order `0` at every affine place** (PROVEN):
`c` is a unit of `F[W]`, so its span is `⊤`, the empty divisor. -/
lemma count_constHom_eq_zero [IsDedekindDomain W.CoordinateRing]
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    {S : W.Point} (hS0 : S ≠ 0) (hvS : v.asIdeal = pointIdeal W S)
    {c : F} (hc : c ≠ 0) :
    FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (constHom W c)) = 0 := by
  have hcoord : constHom W c =
      algebraMap W.CoordinateRing W.FunctionField (coordC W c) := rfl
  have hunit : IsUnit (coordC W c) := by
    refine ⟨⟨coordC W c, coordC W c⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← coordC_mul, mul_inv_cancel₀ hc]; rfl
    · rw [← coordC_mul, inv_mul_cancel₀ hc]; rfl
  have htop : Ideal.span {coordC W c} =
      ((0 : Multiset W.Point).map (pointIdeal W)).prod := by
    rw [Multiset.map_zero, Multiset.prod_zero, Ideal.one_eq_top,
      Ideal.span_singleton_eq_top]
    exact hunit
  rw [hcoord, count_spanSingleton_algebraMap hS0 hvS htop]
  simp

/-- **PROVEN (2026-07-27): the `y`-CENTER, main branch `2 ≠ 0`** —
`ord_S(yp − y_T) ≥ 1`, by the `ψ₂`-tracking of
`TorsionCard.zsmul_some_aux_strong` (route (i) of the leaf below).

**The argument.**  The multiplication formula carries, beside the
`x`-relation `x' · ψₙ² = φₙ`, the `y`-relation

`ψ₂([n]P) · ψₙ(P)⁴ = ψ₂ₙ(P)`,  `ψ₂ = 2Y + a₁X + a₃`,

and this is the ONLY `ι`-asymmetric datum available (`ι` = the
hyperelliptic involution): `ι` acts by `−1` on `ψ₂`, so `ψ₂([n]·)/ψ₂`
is `ι`-invariant and the identity above genuinely distinguishes `T`
from `⊖T`.  Applying it TWICE — generically at `taut`, and at the
`F`-point `S` — gives an element of `F[W]`

`N := ψ_{2p} − ψ₂(T)·ψ_p⁴`

whose value at `S` is `0` (the identity at `S`), hence `ord_S(N) ≥ 1`
(`one_le_count_algebraMap_iff_mem`), while `ord_S(ψ_p) = 0` because
`ψ_p(S) ≠ 0` (`p • S ≠ O`).  Since `[p]^*N = u · ψ_p(taut)⁴` with
`u = ψ₂([p]taut) − ψ₂(T) = 2(yp − y_T) + a₁(xp − x_T)`, this gives
`ord_S(u) ≥ 1`; the vertical brick gives `ord_S(xp − x_T) ≥ 1`, and
subtracting leaves `ord_S(2·(yp − y_T)) ≥ 1`.  A nonzero constant has
order `0` (`count_constHom_eq_zero`), so for `2 ≠ 0` the factor `2`
drops out and `ord_S(yp − y_T) ≥ 1`.

Two side conditions, both free: `S` is not `2`-torsion (else
`T = p • S = ⊖T`, excluded by `hne`), and the tautological point is not
`2`-torsion (`Ψ₂Sq ≠ 0` for `Δ ≠ 0`, and `tautX` is transcendental over
the constants).

**Where `2 ≠ 0` is used, and only there**: the very last step.  In
characteristic `2` the relation `ψ₂ = a₁X + a₃` carries no
`y`-information at all, which is the residue isolated as
`count_pointEval_YClass_neg_nonpos_of_ne_neg_char_two`. -/
theorem one_le_count_pointEval_YClass_of_two_ne_zero
    [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0) (h2 : (2 : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S)
    {xT yT : F} {hT : W.Nonsingular xT yT}
    (hTeq : ((p : ℤ) • S : W.Point) =
      WeierstrassCurve.Affine.Point.some xT yT hT)
    (hne : (WeierstrassCurve.Affine.Point.some xT yT hT : W.Point) ≠
      -(WeierstrassCurve.Affine.Point.some xT yT hT : W.Point)) :
    1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (yp - constHom W yT)) := by
  classical
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hppos : (0 : ℤ) < (p : ℤ) :=
    Int.natCast_pos.mpr (Fact.out : p.Prime).pos
  obtain ⟨xp', yp', hpn', hptaut', hxrel⟩ :=
    exists_smul_tautPoint_eq (W := W) hΔ hp
  have hxx : xp = xp' := by
    have hpts := hptaut.symm.trans hptaut'
    injection hpts with hx _
  subst hxx
  -- the vertical brick
  have hxval : pointEval (constHom W) hpn.left (CoordinateRing.XClass W xT) =
      xp - constHom W xT := by
    rw [XClass_eq, map_sub]
    simp only [coordX, coordC]
    rw [pointEval_X, pointEval_C]
  have hxcount := count_pointEval_XClass_of_smul_ne_zero (W := W)
    hΔ hp hptaut hT hS0 hpS hvS
  rw [hxval] at hxcount
  have hx1 : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (xp - constHom W xT)) := by
    rw [hxcount, hTeq]
    have hcnt : (1 : ℕ) ≤ Multiset.count
        (WeierstrassCurve.Affine.Point.some xT yT hT : W.Point)
        (WeierstrassCurve.Affine.Point.some xT yT hT ::ₘ
          (-WeierstrassCurve.Affine.Point.some xT yT hT : W.Point) ::ₘ 0) := by
      rw [Multiset.count_cons_self]; omega
    exact_mod_cast hcnt
  have hypne : yp - constHom W yT ≠ 0 :=
    sub_ne_zero.mpr (smul_taut_yCoord_ne_constHom hpn hxrel yT)
  cases S with
  | zero => exact absurd rfl hS0
  | some a b hab =>
  -- `T ≠ ⊖T` forces `S ≠ ⊖S`
  have hSne : (Point.some a b hab : W.Point) ≠ -(Point.some a b hab) := by
    intro hself
    refine hne ?_
    rw [← hTeq, ← smul_neg, ← hself]
  have hΨ2S : W.Ψ₂Sq.eval a ≠ 0 := fun hc =>
    hSne ((point_eq_neg_iff_Ψ₂Sq hab).mpr hc)
  have hψ2val : (W.ψ (2 : ℤ)).evalEval a b = 2 * b + W.a₁ * a + W.a₃ :=
    TorsionCard.evalEval_ψ_two W a b
  have hΨ2sq : W.Ψ₂Sq.eval a = (2 * b + (W.a₁ * a + W.a₃)) ^ 2 :=
    TorsionCard.eval_Ψ₂Sq_eq_sq W hab.left
  have hψ2S : (W.ψ (2 : ℤ)).evalEval a b ≠ 0 := by
    intro hc
    refine hΨ2S ?_
    rw [hψ2val] at hc
    rw [hΨ2sq, show 2 * b + (W.a₁ * a + W.a₃) = 2 * b + W.a₁ * a + W.a₃ from by ring,
      hc]
    ring
  -- the `ψ₂`-tracking at `S`
  have hstrongS := TorsionCard.zsmul_some_aux_strong W hab hψ2S (p : ℤ) hppos
  have hψpS : (W.ψ (p : ℤ)).evalEval a b ≠ 0 := by
    intro hc
    exact hpS (show ((p : ℤ) • (Point.some a b hab : W.Point)) = 0 from
      hstrongS.1.mp hc)
  obtain ⟨x', y', h', heq', -, htr'⟩ := hstrongS.2 hψpS
  have heqS : ((p : ℤ) • (Point.some a b hab : W.Point)) =
      Point.some x' y' (show W.Nonsingular x' y' from h') := heq'
  have htrS : (2 * y' + W.a₁ * x' + W.a₃) *
      (W.ψ (p : ℤ)).evalEval a b ^ 4 = (W.ψ (2 * (p : ℤ))).evalEval a b := htr'
  have hxeq : x' = xT := by
    have hh := heqS.symm.trans hTeq
    injection hh with h1 _
  have hyeq : y' = yT := by
    have hh := heqS.symm.trans hTeq
    injection hh with _ h1
  rw [hxeq, hyeq] at htrS
  -- the `ψ₂`-tracking at the tautological point
  haveI : (W.map (constHom W)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (curveK_Δ_ne_zero W hΔ)⟩
  have hcast : ((W.map (constHom W)).baseChange W.FunctionField).toAffine =
      curveK W := map_constHom_baseChange_self W
  have hnsE : ((W.map (constHom W)).baseChange
      W.FunctionField).toAffine.Nonsingular (tautX W) (tautY W) := by
    rw [hcast]
    exact taut_nonsingular W hΔ
  have hψbridge : ∀ n : ℤ,
      (((W.map (constHom W)).baseChange W.FunctionField).ψ n) =
        (W.ψ n).map (Polynomial.mapRingHom (constHom W)) := by
    intro n
    rw [map_constHom_baseChange_self W, WeierstrassCurve.map_ψ]
  have hψK : ∀ n : ℤ,
      (((W.map (constHom W)).baseChange W.FunctionField).ψ n).evalEval
          (tautX W) (tautY W) =
        algebraMap W.CoordinateRing W.FunctionField
          (CoordinateRing.mk W (W.ψ n)) := by
    intro n
    rw [hψbridge n, algebraMap_mk_eq_evalEval]
  have hΨ2K : (((W.map (constHom W)).baseChange
      W.FunctionField).Ψ₂Sq).eval (tautX W) ≠ 0 := by
    rw [map_constHom_baseChange_self W, WeierstrassCurve.map_Ψ₂Sq]
    exact eval_map_ne_zero_of_forall_ne_constHom
      (tautX_ne_constHom (W := W)) (Ψ₂Sq_ne_zero_of_Δ_ne_zero hΔ)
  have hψ2taut : (((W.map (constHom W)).baseChange W.FunctionField).ψ
      (2 : ℤ)).evalEval (tautX W) (tautY W) ≠ 0 := by
    intro hc
    refine hΨ2K ?_
    have h0 : 2 * tautY W +
        (((W.map (constHom W)).baseChange W.FunctionField).a₁ * tautX W +
          ((W.map (constHom W)).baseChange W.FunctionField).a₃) = 0 := by
      rw [← hc, TorsionCard.evalEval_ψ_two (W.map (constHom W))
        (tautX W) (tautY W)]
      ring
    rw [TorsionCard.eval_Ψ₂Sq_eq_sq (W.map (constHom W)) hnsE.left, h0]
    ring
  have hstrongK := TorsionCard.zsmul_some_aux_strong (W.map (constHom W))
    hnsE hψ2taut (p : ℤ) hppos
  have htransport : ((p : ℤ) • tautPoint W hΔ) = castPoint hcast
      ((p : ℤ) • WeierstrassCurve.Affine.Point.some (tautX W) (tautY W) hnsE) := by
    rw [castPoint_zsmul, castPoint_some]
    rfl
  have hψptaut : (((W.map (constHom W)).baseChange W.FunctionField).ψ
      (p : ℤ)).evalEval (tautX W) (tautY W) ≠ 0 := by
    intro hc
    have h1 : ((p : ℤ) • tautPoint W hΔ) = 0 := by
      rw [htransport, hstrongK.1.mp hc, castPoint_zero]
    rw [hptaut] at h1
    exact WeierstrassCurve.Affine.Point.some_ne_zero hpn h1
  obtain ⟨X', Y', H', HEQ, -, HTR⟩ := hstrongK.2 hψptaut
  have hcastEq : ((p : ℤ) • tautPoint W hΔ) =
      castPoint hcast (WeierstrassCurve.Affine.Point.some X' Y' H') := by
    rw [htransport, HEQ]
  rw [castPoint_some] at hcastEq
  have hXeq : X' = xp := by
    have hh := hcastEq.symm.trans hptaut
    injection hh with h1 _
  have hYeq : Y' = yp := by
    have hh := hcastEq.symm.trans hptaut
    injection hh with _ h1
  rw [hXeq, hYeq] at HTR
  -- transporting the two `a`-coefficients across the base change
  have ha1 : ((W.map (constHom W)).baseChange W.FunctionField).a₁ =
      constHom W W.a₁ := by rw [map_constHom_baseChange_self W]; rfl
  have ha3 : ((W.map (constHom W)).baseChange W.FunctionField).a₃ =
      constHom W W.a₃ := by rw [map_constHom_baseChange_self W]; rfl
  rw [ha1, ha3, hψK, hψK] at HTR
  -- the coordinate-ring witness of the two trackings
  set cT : F := 2 * yT + W.a₁ * xT + W.a₃ with hcTdef
  set ζ : W.CoordinateRing := CoordinateRing.mk W (W.ψ (p : ℤ)) with hζdef
  set ζ₂ : W.CoordinateRing := CoordinateRing.mk W (W.ψ (2 * (p : ℤ))) with hζ₂def
  set N : W.CoordinateRing := ζ₂ - coordC W cT * ζ ^ 4 with hNdef
  set ζK : W.FunctionField :=
    algebraMap W.CoordinateRing W.FunctionField ζ with hζKdef
  have hζKne : ζK ≠ 0 := by rw [hζKdef, ← hψK]; exact hψptaut
  have hζne : ζ ≠ 0 := fun h0 => hζKne (by rw [hζKdef, h0, map_zero])
  -- `N` vanishes at `S`
  have hNS : coordEval W hab.left N = 0 := by
    rw [hNdef, map_sub, map_mul, map_pow, hζdef, hζ₂def, coordEval_mk,
      coordEval_mk, coordEval_coordC, hcTdef]
    linear_combination -htrS
  have hNmem : N ∈ v.asIdeal := by
    rw [hvS]
    exact mem_pointIdeal_of_coordEval_eq_zero hab hNS
  -- `ζ` does NOT vanish at `S`
  have hζmem : ζ ∉ v.asIdeal := by
    rw [hvS]
    intro hc
    exact hψpS (by
      have := coordEval_eq_zero_of_mem hab hc
      rwa [hζdef, coordEval_mk] at this)
  have hcount0 : ∀ z : W.CoordinateRing, z ≠ 0 → z ∉ v.asIdeal →
      FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField z)) = 0 := by
    intro z hz hzm
    have hnn := count_spanSingleton_algebraMap_nonneg
      (K := W.FunctionField) v z
    have hno : ¬ (1 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField z))) :=
      fun hc => hzm ((one_le_count_algebraMap_iff_mem v hz).mp hc)
    omega
  -- the difference of the two tracked values
  set u : W.FunctionField :=
    2 * yp + constHom W W.a₁ * xp + constHom W W.a₃ - constHom W cT with hudef
  have hcv : algebraMap W.CoordinateRing W.FunctionField (coordC W cT) =
      constHom W cT := rfl
  have hNval : algebraMap W.CoordinateRing W.FunctionField N = u * ζK ^ 4 := by
    rw [hNdef, map_sub, map_mul, map_pow, hcv, ← hζKdef, hudef]
    linear_combination -HTR
  have hu2 : u = 2 * (yp - constHom W yT) +
      constHom W W.a₁ * (xp - constHom W xT) := by
    rw [hudef, hcTdef]
    simp only [map_add, map_mul, map_ofNat]
    ring
  -- the count of `u`
  have hucase : u = 0 ∨ 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ u) := by
    rcases eq_or_ne u 0 with h0 | h0
    · exact Or.inl h0
    refine Or.inr ?_
    have hNne : N ≠ 0 := by
      intro hc
      rw [hc, map_zero] at hNval
      exact h0 (by
        have := (mul_eq_zero.mp hNval.symm)
        rcases this with h | h
        · exact h
        · exact absurd (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h) hζKne)
    have h1 := (one_le_count_algebraMap_iff_mem (K := W.FunctionField) v hNne).mpr hNmem
    have hpow : FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (ζK ^ 4)) = 0 := by
      have hmem4 : ζ ^ 4 ∉ v.asIdeal := fun hc =>
        hζmem (v.isPrime.mem_of_pow_mem 4 hc)
      have h4 := hcount0 (ζ ^ 4) (pow_ne_zero _ hζne) hmem4
      rw [map_pow, ← hζKdef] at h4
      exact h4
    rw [hNval, count_spanSingleton_mul v h0 (pow_ne_zero _ hζKne), hpow] at h1
    omega
  -- the count of the vertical correction
  have hvcase : constHom W W.a₁ * (xp - constHom W xT) = 0 ∨
      1 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (constHom W W.a₁ * (xp - constHom W xT))) := by
    rcases eq_or_ne (constHom W W.a₁ * (xp - constHom W xT)) 0 with h0 | h0
    · exact Or.inl h0
    refine Or.inr (le_count_spanSingleton_mul_of_nonneg v ?_ hx1 h0)
    exact count_spanSingleton_algebraMap_nonneg (K := W.FunctionField) v
      (coordC W W.a₁)
  -- combine
  have hcomb : ∀ w₁ w₂ : W.FunctionField,
      (w₁ = 0 ∨ 1 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ w₁)) →
      (w₂ = 0 ∨ 1 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ w₂)) →
      w₁ + w₂ ≠ 0 →
      1 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (w₁ + w₂)) := by
    intro w₁ w₂ h₁ h₂ hs
    rcases h₁ with rfl | h₁
    · rcases h₂ with rfl | h₂
      · exact absurd (by ring) hs
      · rwa [zero_add]
    rcases h₂ with rfl | h₂
    · rwa [add_zero]
    exact le_count_spanSingleton_add v h₁ h₂ hs
  have hc2ne : constHom W (2 : F) ≠ 0 := fun hc =>
    h2 ((map_eq_zero_iff _ (constHom W).injective).mp hc)
  have h2K : (2 : W.FunctionField) ≠ 0 := by
    intro hc
    exact hc2ne (by rw [map_ofNat]; exact hc)
  have htwo : (2 : W.FunctionField) * (yp - constHom W yT) ≠ 0 :=
    mul_ne_zero h2K hypne
  have hvcase' : (-(constHom W W.a₁ * (xp - constHom W xT)) = 0) ∨
      1 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (-(constHom W W.a₁ * (xp - constHom W xT)))) := by
    rcases hvcase with h | h
    · exact Or.inl (by rw [h]; ring)
    · exact Or.inr (by rw [count_spanSingleton_neg v]; exact h)
  have hsumeq : u + (-(constHom W W.a₁ * (xp - constHom W xT))) =
      2 * (yp - constHom W yT) := by rw [hu2]; ring
  have hfinal := hcomb _ _ hucase hvcase' (by rw [hsumeq]; exact htwo)
  rw [hsumeq] at hfinal
  have hsplit : FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        ((2 : W.FunctionField) * (yp - constHom W yT))) =
      FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (constHom W (2 : F))) +
      FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (yp - constHom W yT)) := by
    rw [← count_spanSingleton_mul v hc2ne hypne, map_ofNat]
  rw [hsplit, count_constHom_eq_zero hS0 hvS h2] at hfinal
  omega

/-- **Count transport along a lifted translation evaluation, on the
coordinate ring** (PROVEN 2026-07-27).  Writing `σ_Q` for the lifted
translation evaluation `f ↦ f ∘ τ_Q`, the order of `σ_Q b` at the place
of `S` is the order of `b` at the place of `S ⊕ Q`:

`ord_S(σ_Q b) = ord_{S ⊕ Q}(b)`,  `b ∈ F[W]`, `S ⊕ Q ≠ O`.

This is `spanSingleton_pointEval_translate` read ONE PLACE AT A TIME.
That brick gives the divisor identity
`(τ_Q^* b) · I_{⊖Q}^{|D|} = ∏_{R ∈ D} I_{R ⊖ Q}` for any `D` with
`div b = Σ_{R ∈ D} (R)` (`exists_multiset_span_eq_prod_pointIdeal`).
Counting at the place of `S`: the `I_{⊖Q}`-power contributes `0`
because `S ≠ ⊖Q` (that is exactly `S ⊕ Q ≠ O`), and the right-hand
product contributes the multiplicity of `S` in `D.map (· ⊖ Q)`, i.e.
the multiplicity of `S ⊕ Q` in `D` — which is `ord_{S ⊕ Q}(b)` by
`count_spanSingleton_algebraMap`. -/
theorem count_lift_translate_algebraMap [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xQ yQ : W.FunctionField} {hQn : (curveK W).Nonsingular xQ yQ}
    (hptQ : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQn)
    {S : W.Point} (hS0 : S ≠ 0) (hSQ : S + Q ≠ 0)
    {v v' : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S)
    (hvSQ : v'.asIdeal = pointIdeal W (S + Q))
    {b : W.CoordinateRing} (hb : b ≠ 0) :
    FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (IsFractionRing.lift (pointEval_injective hΔ hptQ)
            (algebraMap W.CoordinateRing W.FunctionField b))) =
      FractionalIdeal.count W.FunctionField v'
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (algebraMap W.CoordinateRing W.FunctionField b)) := by
  classical
  obtain ⟨D, -, hDspan⟩ := exists_multiset_span_eq_prod_pointIdeal hΔ hb
  have hlift : IsFractionRing.lift (pointEval_injective hΔ hptQ)
      (algebraMap W.CoordinateRing W.FunctionField b) =
      pointEval (constHom W) hQn.left b := IsFractionRing.lift_algebraMap _ _
  have hkey := spanSingleton_pointEval_translate hΔ hptQ hb hDspan
  have hbne : pointEval (constHom W) hQn.left b ≠ 0 := fun h =>
    hb (pointEval_injective hΔ hptQ (by rw [h, map_zero]))
  have hspanne : FractionalIdeal.spanSingleton W.CoordinateRing⁰
      (pointEval (constHom W) hQn.left b) ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hbne
  have hnegQ : (-Q : W.Point) ≠ S := by
    intro hc
    refine hSQ ?_
    rw [← hc]
    abel
  have hpow : ∀ n : ℕ, FractionalIdeal.count W.FunctionField v
      ((pointIdeal' W (-Q) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n) = 0 := by
    intro n
    induction n with
    | zero => simpa using FractionalIdeal.count_one W.FunctionField v
    | succ n ih =>
      rw [pow_succ, FractionalIdeal.count_mul W.FunctionField v
          (pow_ne_zero _ (pointIdeal' W (-Q)).isUnit.ne_zero)
          (pointIdeal' W (-Q)).isUnit.ne_zero, ih,
        count_coe_pointIdeal' hS0 hvS (-Q), if_neg hnegQ]
      norm_num
  have hcountL := congrArg (FractionalIdeal.count W.FunctionField v) hkey
  rw [FractionalIdeal.count_mul W.FunctionField v hspanne
      (pow_ne_zero _ (pointIdeal' W (-Q)).isUnit.ne_zero), hpow, add_zero] at hcountL
  have hreindex : (D.map fun R => (pointIdeal' W (R - Q) :
      FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod =
      ((D.map (fun R => R - Q)).map fun R => (pointIdeal' W R :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hreindex, count_prod_coe_pointIdeal' hS0 hvS] at hcountL
  have hinj : Function.Injective (fun R : W.Point => R - Q) := by
    intro a b hab
    simpa using congrArg (fun z : W.Point => z + Q) hab
  have hcnt : Multiset.count S (D.map (fun R => R - Q)) =
      Multiset.count (S + Q) D := by
    have h := Multiset.count_map_eq_count' (fun R : W.Point => R - Q) D hinj (S + Q)
    simpa using h
  rw [hcnt] at hcountL
  rw [hlift, hcountL, count_spanSingleton_algebraMap hSQ hvSQ hDspan]

/-- **Count transport along a lifted translation evaluation** (PROVEN
2026-07-27), for an arbitrary nonzero element of the function field:

`ord_S(σ_Q f) = ord_{S ⊕ Q}(f)`,  `f ∈ K^×`, `S ⊕ Q ≠ O`.

Write `f = n/d` with `n, d ∈ F[W]` (`IsFractionRing.div_surjective`);
`count` is additive on products (`count_spanSingleton_mul`) and `σ_Q`
is a ring hom, so the coordinate-ring case above transports both
numerator and denominator.

**This is the lemma that breaks the `ι`-symmetry obstruction** in
`count_pointEval_YClass_neg_nonpos_of_ne_neg_char_two`: it lets a
statement proven at ONE place be read at ANOTHER, and translation by
`Q` is not `ι`-equivariant. -/
theorem count_lift_translate [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) {Q : W.Point}
    {xQ yQ : W.FunctionField} {hQn : (curveK W).Nonsingular xQ yQ}
    (hptQ : constPoint W Q + tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xQ yQ hQn)
    {S : W.Point} (hS0 : S ≠ 0) (hSQ : S + Q ≠ 0)
    {v v' : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S)
    (hvSQ : v'.asIdeal = pointIdeal W (S + Q))
    {f : W.FunctionField} (hf : f ≠ 0) :
    FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (IsFractionRing.lift (pointEval_injective hΔ hptQ) f)) =
      FractionalIdeal.count W.FunctionField v'
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ f) := by
  classical
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective W.CoordinateRing f
  have hdK : algebraMap W.CoordinateRing W.FunctionField d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hd0 : d ≠ 0 := fun h => hdK (by rw [h, map_zero])
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, map_zero, zero_div] at hnd
    exact hf hnd.symm
  have hmul : f * algebraMap W.CoordinateRing W.FunctionField d =
      algebraMap W.CoordinateRing W.FunctionField n := by
    rw [← hnd]
    field_simp
  set σ : W.FunctionField →+* W.FunctionField :=
    IsFractionRing.lift (pointEval_injective hΔ hptQ) with hσdef
  have hσinj : Function.Injective σ := σ.injective
  have hσf : σ f ≠ 0 := fun h => hf (hσinj (by rw [h, map_zero]))
  have hσd : σ (algebraMap W.CoordinateRing W.FunctionField d) ≠ 0 := fun h =>
    hdK (hσinj (by rw [h, map_zero]))
  have hσmul : σ f * σ (algebraMap W.CoordinateRing W.FunctionField d) =
      σ (algebraMap W.CoordinateRing W.FunctionField n) := by
    rw [← map_mul, hmul]
  have e1 := count_spanSingleton_mul (K := W.FunctionField) v hσf hσd
  rw [hσmul] at e1
  have e2 := count_spanSingleton_mul (K := W.FunctionField) v' hf hdK
  rw [hmul] at e2
  have e3 := count_lift_translate_algebraMap hΔ hptQ hS0 hSQ hvS hvSQ hd0
  have e4 := count_lift_translate_algebraMap hΔ hptQ hS0 hSQ hvS hvSQ hn0
  rw [← hσdef] at e3 e4
  omega

/-- **An auxiliary affine point off a prescribed vertical and off the
`2`-torsion** (PROVEN 2026-07-27).  `F` is algebraically closed, hence
infinite, so an `x`-coordinate can be chosen away from `x₀` and away
from the finitely many roots of `Ψ₂Sq`; the `y`-fibre quadratic
`TorsionCard.yQuad` has degree `2`, hence a root, and `Δ ≠ 0` upgrades
its `Equation` to `Nonsingular`.  `Ψ₂Sq(x_R) ≠ 0` says exactly that the
resulting point is NOT `2`-torsion (`point_eq_neg_iff_Ψ₂Sq`). -/
theorem exists_aux_translate_point (hΔ : W.Δ ≠ 0) (x₀ : F) :
    ∃ (xR yR : F) (_ : W.Nonsingular xR yR),
      xR ≠ x₀ ∧ W.Ψ₂Sq.eval xR ≠ 0 := by
  classical
  have hΨ : W.Ψ₂Sq ≠ 0 := Ψ₂Sq_ne_zero_of_Δ_ne_zero hΔ
  obtain ⟨xR, hxR⟩ := Infinite.exists_notMem_finset
    (({x₀} : Finset F) ∪ W.Ψ₂Sq.roots.toFinset)
  have hx0 : xR ≠ x₀ := by
    intro h
    exact hxR (Finset.mem_union_left _ (by simp [h]))
  have hΨx : W.Ψ₂Sq.eval xR ≠ 0 := by
    intro h
    refine hxR (Finset.mem_union_right _ ?_)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hΨ]
    exact h
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  obtain ⟨yR, hyR⟩ := IsAlgClosed.exists_root (k := F) (TorsionCard.yQuad W xR) (by
    intro hdeg
    have h2 := TorsionCard.yQuad_natDegree W xR
    rw [Polynomial.natDegree, hdeg] at h2
    simp at h2)
  have hEq : W.Equation xR yR :=
    (TorsionCard.eval_yQuad_eq_zero_iff_equation W xR yR).mp hyR
  exact ⟨xR, yR, (W.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hEq, hx0, hΨx⟩

omit [DecidableEq F] in
/-- **The generic `y`-coordinate of `p • taut` is not an `F`-affine
function of the generic `x`-coordinate** (PROVEN 2026-07-27): the
strengthening of `smul_taut_yCoord_ne_constHom` that the slope
computations of the characteristic-`2` leaf below need.  Substituting
`yp = α·xp + β` into the Weierstrass equation makes `xp` a root of the
monic (up to sign) cubic
`−X³ + (α² + a₁α − a₂)X² + (2αβ + a₁β + a₃α − a₄)X + (β² + a₃β − a₆)`
over `F`, contradicting the transcendence of `xp`
(`eval_map_ne_zero_of_forall_ne_constHom` at
`smul_taut_xCoord_ne_constHom`). -/
theorem smul_taut_yCoord_ne_affine {xp yp : W.FunctionField}
    (hpn : (curveK W).Nonsingular xp yp)
    (hxrel : xp * ((W.ΨSq (p : ℤ)).map (constHom W)).eval (tautX W) =
      ((W.Φ (p : ℤ)).map (constHom W)).eval (tautX W)) (α β : F) :
    yp ≠ constHom W α * xp + constHom W β := by
  intro hd
  have heqc : yp ^ 2 + constHom W W.a₁ * xp * yp + constHom W W.a₃ * yp =
      xp ^ 3 + constHom W W.a₂ * xp ^ 2 + constHom W W.a₄ * xp +
        constHom W W.a₆ := by
    have h2 := ((curveK W).equation_iff xp yp).mp hpn.left
    simpa only [curveK, WeierstrassCurve.map] using h2
  set q : Polynomial F :=
    -Polynomial.X ^ 3 + Polynomial.C (α ^ 2 + W.a₁ * α - W.a₂) * Polynomial.X ^ 2 +
      Polynomial.C (2 * α * β + W.a₁ * β + W.a₃ * α - W.a₄) * Polynomial.X +
      Polynomial.C (β ^ 2 + W.a₃ * β - W.a₆) with hq
  have hq0 : q ≠ 0 := by
    intro h0
    have hc := congrArg (fun r : Polynomial F => r.coeff 3) h0
    simp only [hq, Polynomial.coeff_add, Polynomial.coeff_neg,
      Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C, Polynomial.coeff_zero] at hc
    norm_num at hc
  refine eval_map_ne_zero_of_forall_ne_constHom
    (smul_taut_xCoord_ne_constHom hxrel) hq0 ?_
  rw [hd] at heqc
  simp only [hq, Polynomial.map_add, Polynomial.map_neg, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add,
    Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  linear_combination heqc

/-- **PROVEN (2026-07-27): the wrong branch in CHARACTERISTIC `2`, by
TRANSLATION TRANSPORT.**  Exactly the statement of
`count_pointEval_YClass_neg_nonpos_of_ne_neg` below, with the extra
hypothesis `2 = 0`.

**THE OLD AUDIT'S "STRUCTURAL OBSTRUCTION" VERDICT WAS WRONG, AND THE
AXIS THAT CLOSED IT IS A THIRD ONE.**  That audit searched exactly one
axis — `ι`-anti-invariant tracking, `ι` the hyperelliptic involution —
and was right about it: every `polyClass`/`ΨSq` quantity is
`ι`-SYMMETRIC, the unique `ι`-anti-invariant datum in the pin is
`ψ₂ = 2Y + a₁X + a₃`, and at `2 = 0` that is `a₁X + a₃`, a function of
`X` alone, hence `ι`-INVARIANT, so the `±1` eigenspace decomposition
collapses.  It then named two untried axes — the `ω` division
polynomial (a mathlib TODO) and Artin–Schreier additive tracking — and
declared the residue structural.  **Neither is needed.**  The proof
below is CHARACTERISTIC-FREE: `h2` is never used.

**THE ARGUMENT.**  The `ι`-symmetry obstruction bites only as long as
one stays at the single place of `S`.  Break it by moving the PLACE.
For `Q ∈ W(F)` let `σ_Q := IsFractionRing.lift (pointEval_injective …)`
be the lifted translation evaluation `f ↦ f ∘ τ_Q` — the substrate of
`spanSingleton_pointEval_translate`.  Two new bricks:

* `count_lift_translate` (above): `ord_S(σ_Q f) = ord_{S ⊕ Q}(f)`
  whenever `S ⊕ Q ≠ O`.  A statement proven at one place is now
  readable at another, and translation is NOT `ι`-equivariant.
* `endoMap_zsmul` / `endoMap_tautPoint` transport the group law along
  `σ_Q`: it sends `p • taut` to `p • (Q ⊕ taut) = R ⊕ p • taut` with
  `R := p • Q`.  So `σ_Q xp` is the ADDITION-FORMULA value
  `addX x_R xp λ`, `λ = (y_R − yp)/(x_R − xp)` — and `x(P ⊕ R)` is not
  `ι`-symmetric in `P`, which is precisely the datum characteristic `2`
  destroyed on the `ψ₂` axis.

Pick `R` off the vertical of `T` and off the `2`-torsion
(`exists_aux_translate_point`) and `Q` with `p • Q = R` by divisibility
(`TorsionCard.smul_surjective`, available since `F` is algebraically
closed).  Then `S ⊕ Q ≠ O` — else `Q = ⊖S` and `R = ⊖T` — and
`p • (S ⊕ Q) = T ⊕ R`.  Two counts at the place of `S` now collide:

* the vertical brick `count_pointEval_XClass_of_smul_ne_zero` at the
  place of `S ⊕ Q`, transported back by `count_lift_translate`, gives
  `ord_S(σ_Q xp − x(T ⊕ R)) ≥ 1`;
* assuming the WRONG branch `ord_S(yp − y_{⊖T}) ≥ 1`, together with
  the vertical brick `ord_S(xp − x_T) ≥ 1` at `S` and
  `ord_S(xp − x_R) = 0` (`R ≠ ±T`), the slope congruence
  `ord_S(λ − λ_{⊖T}) ≥ 1` propagates through
  `addX x_R x_T λ = λ² + a₁λ − a₂ − x_R − x_T` — the difference is
  `(λ − λ_{⊖T})(λ + λ_{⊖T} + a₁) − (xp − x_T)` — to
  `ord_S(σ_Q xp − x(⊖T ⊕ R)) ≥ 1`.

Their difference is the CONSTANT `x(T ⊕ R) − x(⊖T ⊕ R)`, whose order is
`0` unless it vanishes (`count_constHom_eq_zero`), so ultrametricity
forces `x(T ⊕ R) = x(⊖T ⊕ R)`.  The `x`-collision dichotomy
(`Y_eq_of_X_eq` / `Point.add_of_Y_eq`) then gives `T ⊕ R = ⊖T ⊕ R`,
i.e. `T = ⊖T`, excluded by `hne`; or `(T ⊕ R) ⊕ (⊖T ⊕ R) = O`, i.e.
`2R = O`, excluded by the choice of `R`.  Contradiction.

All non-vanishing side conditions come from transcendence of the
generic coordinates: `smul_taut_xCoord_ne_constHom` and the new
`smul_taut_yCoord_ne_affine`.

**Route (ii) of the original leaf** — translation off a base point whose
`[p]`-image is `2`-torsion — was correctly ruled out, and is not what
this is: nothing here needs a `2`-torsion point, only one that is NOT
`2`-torsion.

**Axioms — CLEAN as of 2026-07-27** (audited by `#print axioms`, not
inferred).  The last `sorryAx` in this declaration's cone came from the
vertical brick `count_pointEval_XClass_of_smul_ne_zero`, through its
characteristic-`2` residue
`rootMultiplicity_derivative_Φ_eq_two_of_two_eq_zero`; that leaf is now
PROVEN (by the fibre count, above), so this declaration, its sibling
`one_le_count_pointEval_YClass_of_two_ne_zero`, the bricks
`count_pointEval_{X,Y}Class_of_smul_ne_zero`,
`count_pointEval_of_smul_{ne,eq}_zero` and the L4-7 assembly
`spanSingleton_pointEval_mul_fiberProd_pow` all audit to
`[propext, Classical.choice, Quot.sound]`.  Nothing below adds a new
axiom. -/
theorem count_pointEval_YClass_neg_nonpos_of_ne_neg_char_two
    [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0) (_h2 : (2 : F) = 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S)
    {xT yT : F} {hT : W.Nonsingular xT yT}
    (hTeq : ((p : ℤ) • S : W.Point) =
      WeierstrassCurve.Affine.Point.some xT yT hT)
    (hne : (WeierstrassCurve.Affine.Point.some xT yT hT : W.Point) ≠
      -(WeierstrassCurve.Affine.Point.some xT yT hT : W.Point)) :
    FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (yp - constHom W (W.negY xT yT))) ≤ 0 := by
  classical
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  obtain ⟨xp', yp', hpn', hptaut', hxrel⟩ :=
    exists_smul_tautPoint_eq (W := W) hΔ hp
  have hxx : xp = xp' := by
    have hpts := hptaut.symm.trans hptaut'
    injection hpts with hx _
  subst hxx
  have hxpconst : ∀ d : F, xp ≠ constHom W d := smul_taut_xCoord_ne_constHom hxrel
  have hypaff : ∀ α β : F, yp ≠ constHom W α * xp + constHom W β :=
    fun α β => smul_taut_yCoord_ne_affine hpn hxrel α β
  have ha1 : (curveK W).a₁ = constHom W W.a₁ := rfl
  have ha2 : (curveK W).a₂ = constHom W W.a₂ := rfl
  -- the vertical brick, in the form used below
  have hxval : ∀ x : F,
      pointEval (constHom W) hpn.left (CoordinateRing.XClass W x) =
      xp - constHom W x := by
    intro x
    rw [XClass_eq, map_sub]
    simp only [coordX, coordC]
    rw [pointEval_X, pointEval_C]
  set T : W.Point := WeierstrassCurve.Affine.Point.some xT yT hT with hTdef
  have hA : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (xp - constHom W xT)) := by
    have hxcount := count_pointEval_XClass_of_smul_ne_zero (W := W)
      hΔ hp hptaut hT hS0 hpS hvS
    rw [hxval] at hxcount
    rw [hxcount, hTeq]
    have hcnt : (1 : ℕ) ≤ Multiset.count T (T ::ₘ (-T : W.Point) ::ₘ 0) := by
      rw [Multiset.count_cons_self]; omega
    exact_mod_cast hcnt
  -- the auxiliary translate
  obtain ⟨xR, yR, hRns, hxRT, hΨR⟩ := exists_aux_translate_point (W := W) hΔ xT
  set R : W.Point := WeierstrassCurve.Affine.Point.some xR yR hRns with hRdef
  have hR0 : R ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hRns
  have hRT : R ≠ T := by
    intro hc
    rw [hRdef, hTdef] at hc
    injection hc with hx _
    exact hxRT hx
  have hRnegT : R ≠ -T := by
    intro hc
    rw [hRdef, hTdef, WeierstrassCurve.Affine.Point.neg_some] at hc
    injection hc with hx _
    exact hxRT hx
  have hRself : R ≠ -R := fun hc => hΨR ((point_eq_neg_iff_Ψ₂Sq hRns).mp hc)
  -- `ord_S(xp − x_R) = 0`
  have hdR0 : FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (xp - constHom W xR)) = 0 := by
    have hxcount := count_pointEval_XClass_of_smul_ne_zero (W := W)
      hΔ hp hptaut hRns hS0 hpS hvS
    rw [hxval] at hxcount
    rw [hxcount, hTeq]
    have hTR : T ≠ R := fun hc => hRT hc.symm
    have hTnR : T ≠ -R := by
      intro hc
      exact hRnegT (by rw [hc]; simp)
    simp [hTR, hTnR, ← hRdef]
  -- a `p`-th root of `R`
  obtain ⟨Q0, hQ0⟩ := TorsionCard.smul_surjective W (n := p) hp R
  obtain ⟨Q, hQ⟩ : ∃ Q : W.Point, ((p : ℤ) • Q : W.Point) = R := ⟨Q0, hQ0⟩
  have hSQ : S + Q ≠ 0 := by
    intro hc
    have hQS : Q = -S := by
      have h := congrArg (fun z : W.Point => z - S) hc
      simpa using h
    refine hRnegT ?_
    rw [← hQ, hQS, smul_neg, hTeq]
  obtain ⟨v', hv'⟩ := exists_heightOneSpectrum_pointIdeal hSQ
  obtain ⟨xQ, yQ, hQn, hptQ⟩ := exists_translate_some hΔ Q
  set σ : W.FunctionField →+* W.FunctionField :=
    IsFractionRing.lift (pointEval_injective hΔ hptQ) with hσdef
  have hcv : (curveK W).map σ = W.map (constHom W) :=
    curveK_map_eq_of_constHom (lift_pointEval_constHom hΔ hptQ)
  have hend : endoMap hcv ((p : ℤ) • tautPoint W hΔ) =
      constPoint W R + (p : ℤ) • tautPoint W hΔ := by
    rw [endoMap_zsmul, endoMap_tautPoint hΔ hptQ, zsmul_add]
    congr 1
    rw [← hQ]
    exact (map_zsmul (constPointHom W) (p : ℤ) Q).symm
  rw [hptaut, endoMap_some] at hend
  have hRnsK : (curveK W).Nonsingular (constHom W xR) (constHom W yR) :=
    (W.map_nonsingular (constHom W).injective xR yR).mpr hRns
  have hcR : (constPoint W R : (curveK W).Point) =
      WeierstrassCurve.Affine.Point.some (constHom W xR) (constHom W yR) hRnsK := rfl
  have hxyK : ¬(constHom W xR = xp ∧
      constHom W yR = (curveK W).negY xp yp) := fun h => hxpconst xR h.1.symm
  rw [hcR, WeierstrassCurve.Affine.Point.add_some hxyK] at hend
  injection hend with hσx _
  set L : W.FunctionField :=
    (curveK W).slope (constHom W xR) xp (constHom W yR) yp with hLdef
  have hLval : L = (constHom W yR - yp) / (constHom W xR - xp) := by
    rw [hLdef, WeierstrassCurve.Affine.slope_of_X_ne (fun h => hxpconst xR h.symm)]
  have hdRne : constHom W xR - xp ≠ 0 := fun h =>
    hxpconst xR (by linear_combination -h)
  have hLnc : ∀ c : F, L ≠ constHom W c := by
    intro c hc
    refine hypaff c (yR - c * xR) ?_
    have h1 : constHom W yR - yp = constHom W c * (constHom W xR - xp) := by
      rw [← hc, hLval]
      field_simp
    simp only [map_sub, map_mul]
    linear_combination -h1
  -- the two candidate `x`-values downstairs
  set ℓ₀ : F := W.slope xR xT yR (W.negY xT yT) with hℓ₀def
  set ℓ₁ : F := W.slope xR xT yR yT with hℓ₁def
  set c₀ : F := W.addX xR xT ℓ₀ with hc₀def
  set c₁ : F := W.addX xR xT ℓ₁ with hc₁def
  have hℓ₀val : ℓ₀ = (yR - W.negY xT yT) / (xR - xT) := by
    rw [hℓ₀def, WeierstrassCurve.Affine.slope_of_X_ne hxRT]
  have hxRTne : xR - xT ≠ 0 := sub_ne_zero.mpr hxRT
  -- the two sums downstairs
  have hnsT' : W.Nonsingular xT (W.negY xT yT) := (W.nonsingular_neg xT yT).mpr hT
  have hnegTeq : (-T : W.Point) =
      WeierstrassCurve.Affine.Point.some xT (W.negY xT yT) hnsT' := by
    rw [hTdef, WeierstrassCurve.Affine.Point.neg_some]
  have hxy0 : ¬(xR = xT ∧ yR = W.negY xT (W.negY xT yT)) := fun h => hxRT h.1
  have hxy1 : ¬(xR = xT ∧ yR = W.negY xT yT) := fun h => hxRT h.1
  have hadd0 : (R + (-T) : W.Point) =
      WeierstrassCurve.Affine.Point.some c₀ (W.addY xR xT yR ℓ₀)
        (nonsingular_add hRns hnsT' hxy0) := by
    rw [hRdef, hnegTeq, WeierstrassCurve.Affine.Point.add_some hxy0]
  have hadd1 : (R + T : W.Point) =
      WeierstrassCurve.Affine.Point.some c₁ (W.addY xR xT yR ℓ₁)
        (nonsingular_add hRns hT hxy1) := by
    rw [hRdef, hTdef, WeierstrassCurve.Affine.Point.add_some hxy1]
  -- the transported vertical at `T ⊕ R`
  have hpSQ : ((p : ℤ) • (S + Q) : W.Point) = R + T := by
    rw [smul_add, hTeq, hQ]
    abel
  have hpSQ0 : ((p : ℤ) • (S + Q) : W.Point) ≠ 0 := by
    rw [hpSQ, hadd1]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have hxpc₁ : xp - constHom W c₁ ≠ 0 := fun h =>
    hxpconst c₁ (by linear_combination h)
  have hE1 : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (σ xp - constHom W c₁)) := by
    have htr := count_lift_translate hΔ hptQ hS0 hSQ hvS hv' (f := xp - constHom W c₁)
      hxpc₁
    rw [← hσdef] at htr
    have hσc : σ (xp - constHom W c₁) = σ xp - constHom W c₁ := by
      rw [map_sub, hσdef, lift_pointEval_constHom hΔ hptQ]
    rw [hσc] at htr
    rw [htr]
    have hxcount := count_pointEval_XClass_of_smul_ne_zero (W := W)
      hΔ hp hptaut (nonsingular_add hRns hT hxy1) hSQ hpSQ0 hv'
    rw [hxval] at hxcount
    rw [hxcount, hpSQ, hadd1]
    have hcnt : (1 : ℕ) ≤ Multiset.count
        (WeierstrassCurve.Affine.Point.some c₁ (W.addY xR xT yR ℓ₁)
          (nonsingular_add hRns hT hxy1) : W.Point)
        (WeierstrassCurve.Affine.Point.some c₁ (W.addY xR xT yR ℓ₁)
            (nonsingular_add hRns hT hxy1) ::ₘ
          (-(WeierstrassCurve.Affine.Point.some c₁ (W.addY xR xT yR ℓ₁)
            (nonsingular_add hRns hT hxy1)) : W.Point) ::ₘ 0) := by
      rw [Multiset.count_cons_self]; omega
    exact_mod_cast hcnt
  -- now assume the WRONG branch and derive a contradiction
  by_contra hgoal
  have hG : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (yp - constHom W (W.negY xT yT))) := by omega
  -- the slope congruence
  have hLdiffne : L - constHom W ℓ₀ ≠ 0 := fun h =>
    hLnc ℓ₀ (by linear_combination h)
  have hkeyid : (L - constHom W ℓ₀) *
        ((constHom W xR - xp) * (constHom W xR - constHom W xT)) =
      -((yp - constHom W (W.negY xT yT)) * (constHom W xR - constHom W xT)) +
        (constHom W yR - constHom W (W.negY xT yT)) * (xp - constHom W xT) := by
    have hc0 : constHom W xR - constHom W xT ≠ 0 := by
      rw [← map_sub]
      exact fun h => hxRTne ((constHom W).injective (by rw [h, map_zero]))
    have hℓ₀K : constHom W ℓ₀ =
        (constHom W yR - constHom W (W.negY xT yT)) /
          (constHom W xR - constHom W xT) := by
      rw [hℓ₀val, map_div₀, map_sub, map_sub]
    rw [hLval, hℓ₀K]
    field_simp
    ring
  have hcnst0 : FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (constHom W xR - constHom W xT)) = 0 := by
    rw [← map_sub]
    exact count_constHom_eq_zero hS0 hvS hxRTne
  have hcntdR : FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (constHom W xR - xp)) = 0 := by
    rw [show constHom W xR - xp = -(xp - constHom W xR) from by ring,
      count_spanSingleton_neg, hdR0]
  -- the count of the right-hand side of `hkeyid`
  have hcxRT : constHom W xR - constHom W xT ≠ 0 := by
    rw [← map_sub]
    exact fun h => hxRTne ((constHom W).injective (by rw [h, map_zero]))
  have hGne : yp - constHom W (W.negY xT yT) ≠ 0 :=
    sub_ne_zero.mpr (smul_taut_yCoord_ne_constHom hpn hxrel _)
  have hAne : xp - constHom W xT ≠ 0 := fun h => hxpconst xT (by linear_combination h)
  have hRHSne :
      -((yp - constHom W (W.negY xT yT)) * (constHom W xR - constHom W xT)) +
        (constHom W yR - constHom W (W.negY xT yT)) * (xp - constHom W xT) ≠ 0 := by
    rw [← hkeyid]
    exact mul_ne_zero hLdiffne (mul_ne_zero hdRne hcxRT)
  have h1 : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (-((yp - constHom W (W.negY xT yT)) *
          (constHom W xR - constHom W xT)))) := by
    rw [count_spanSingleton_neg, count_spanSingleton_mul v hGne hcxRT, hcnst0]
    omega
  have hRHS : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (-((yp - constHom W (W.negY xT yT)) * (constHom W xR - constHom W xT)) +
          (constHom W yR - constHom W (W.negY xT yT)) * (xp - constHom W xT))) := by
    by_cases hz : constHom W yR - constHom W (W.negY xT yT) = 0
    · rw [hz, zero_mul, add_zero]
      exact h1
    · refine le_count_spanSingleton_add v h1 ?_ hRHSne
      rw [count_spanSingleton_mul v hz hAne]
      have hnn := count_spanSingleton_algebraMap_nonneg (K := W.FunctionField) v
        (coordC W (yR - W.negY xT yT))
      have hcz : algebraMap W.CoordinateRing W.FunctionField
          (coordC W (yR - W.negY xT yT)) =
          constHom W yR - constHom W (W.negY xT yT) := by
        rw [show (algebraMap W.CoordinateRing W.FunctionField (coordC W
          (yR - W.negY xT yT))) = constHom W (yR - W.negY xT yT) from rfl, map_sub]
      rw [hcz] at hnn
      omega
  -- hence the slope congruence
  have hLdiff : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (L - constHom W ℓ₀)) := by
    have hcm := count_spanSingleton_mul v hLdiffne (mul_ne_zero hdRne hcxRT)
    rw [count_spanSingleton_mul v hdRne hcxRT, hcntdR, hcnst0] at hcm
    rw [hkeyid] at hcm
    omega
  -- regularity of the slope
  have hzne : coordY W - coordC W yR ≠ 0 := by
    intro h
    refine smul_taut_yCoord_ne_constHom hpn hxrel yR ?_
    have h2 := congrArg (pointEval (constHom W) hpn.left) (sub_eq_zero.mp h)
    rw [show coordY W = CoordinateRing.mk W Polynomial.X from rfl,
      show coordC W yR = CoordinateRing.mk W (Polynomial.C (Polynomial.C yR)) from rfl,
      pointEval_Y, pointEval_C] at h2
    exact h2
  have hyRnn : 0 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (constHom W yR - yp)) := by
    have hnn := count_pointEval_nonneg hΔ hp hptaut hS0 hpS hvS hzne
    rw [map_sub, show coordY W = CoordinateRing.mk W Polynomial.X from rfl,
      show coordC W yR = CoordinateRing.mk W (Polynomial.C (Polynomial.C yR)) from rfl,
      pointEval_Y, pointEval_C] at hnn
    rw [show constHom W yR - yp = -(yp - constHom W yR) from by ring,
      count_spanSingleton_neg]
    exact hnn
  have hLnn : 0 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ L) := by
    have hLne : L ≠ 0 := fun h => hLnc 0 (by rw [h, map_zero])
    have hprod : L * (constHom W xR - xp) = constHom W yR - yp := by
      rw [hLval]
      field_simp
    have hcm := count_spanSingleton_mul v hLne hdRne
    rw [hprod, hcntdR] at hcm
    omega
  have hsumnn : 0 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (L + constHom W ℓ₀ + constHom W W.a₁)) := by
    have hc1 := count_spanSingleton_algebraMap_nonneg (K := W.FunctionField) v
      (coordC W (ℓ₀ + W.a₁))
    have hc1' : algebraMap W.CoordinateRing W.FunctionField (coordC W (ℓ₀ + W.a₁)) =
        constHom W ℓ₀ + constHom W W.a₁ := by
      rw [show (algebraMap W.CoordinateRing W.FunctionField (coordC W (ℓ₀ + W.a₁))) =
        constHom W (ℓ₀ + W.a₁) from rfl, map_add]
    rw [hc1'] at hc1
    have hmem := (countNonneg (K := W.FunctionField) v).add_mem
      (show L ∈ countNonneg (K := W.FunctionField) v from hLnn)
      (show constHom W ℓ₀ + constHom W W.a₁ ∈ countNonneg (K := W.FunctionField) v
        from hc1)
    rw [mem_countNonneg] at hmem
    rw [show L + constHom W ℓ₀ + constHom W W.a₁ =
      L + (constHom W ℓ₀ + constHom W W.a₁) from by ring]
    exact hmem
  -- the transported vertical, expanded through the addition formula
  have hE0id : σ xp - constHom W c₀ =
      (L - constHom W ℓ₀) * (L + constHom W ℓ₀ + constHom W W.a₁) +
        (-(xp - constHom W xT)) := by
    rw [hσx, hc₀def]
    simp only [WeierstrassCurve.Affine.addX, ha1, ha2, map_add, map_sub, map_mul,
      map_pow]
    ring
  have hsum2ne : L + constHom W ℓ₀ + constHom W W.a₁ ≠ 0 := by
    intro h
    refine hLnc (-(ℓ₀ + W.a₁)) ?_
    rw [map_neg, map_add]
    linear_combination h
  -- conclude that the two candidate `x`-values agree
  have hc01 : c₀ = c₁ := by
    by_contra hcne
    have hE0ne : σ xp - constHom W c₀ ≠ 0 := by
      intro h0
      have h1' : σ xp - constHom W c₁ = constHom W (c₀ - c₁) := by
        rw [map_sub]
        linear_combination h0
      rw [h1', count_constHom_eq_zero hS0 hvS (sub_ne_zero.mpr hcne)] at hE1
      omega
    have hE0 : 1 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (σ xp - constHom W c₀)) := by
      rw [hE0id]
      refine le_count_spanSingleton_add v ?_ ?_ (by rw [← hE0id]; exact hE0ne)
      · rw [count_spanSingleton_mul v hLdiffne hsum2ne]
        omega
      · rw [count_spanSingleton_neg]
        exact hA
    have hfin : 1 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (constHom W (c₁ - c₀))) := by
      have hid : constHom W (c₁ - c₀) =
          (σ xp - constHom W c₀) + (-(σ xp - constHom W c₁)) := by
        rw [map_sub]; ring
      rw [hid]
      refine le_count_spanSingleton_add v hE0 ?_ ?_
      · rw [count_spanSingleton_neg]; exact hE1
      · rw [← hid, ← map_zero (constHom W)]
        exact fun h => (sub_ne_zero.mpr (Ne.symm hcne)) ((constHom W).injective h)
    rw [count_constHom_eq_zero hS0 hvS (sub_ne_zero.mpr (Ne.symm hcne))] at hfin
    omega
  -- the geometric contradiction
  have hcongr : ∀ {x₁ y₁ x₂ y₂ : F} (h₁ : W.Nonsingular x₁ y₁)
      (h₂ : W.Nonsingular x₂ y₂), x₁ = x₂ → y₁ = y₂ →
      (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.Point) =
        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ hx hy
    subst hx
    subst hy
    rfl
  have hdich : (WeierstrassCurve.Affine.Point.some c₀ (W.addY xR xT yR ℓ₀)
        (nonsingular_add hRns hnsT' hxy0) : W.Point) =
      WeierstrassCurve.Affine.Point.some c₁ (W.addY xR xT yR ℓ₁)
        (nonsingular_add hRns hT hxy1) ∨
      (WeierstrassCurve.Affine.Point.some c₀ (W.addY xR xT yR ℓ₀)
        (nonsingular_add hRns hnsT' hxy0) : W.Point) +
        WeierstrassCurve.Affine.Point.some c₁ (W.addY xR xT yR ℓ₁)
          (nonsingular_add hRns hT hxy1) = 0 := by
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq
        (nonsingular_add hRns hnsT' hxy0).1 (nonsingular_add hRns hT hxy1).1 hc01
      with hy | hy
    · exact Or.inl (hcongr _ _ hc01 hy)
    · exact Or.inr (WeierstrassCurve.Affine.Point.add_of_Y_eq hc01 hy)
  rcases hdich with h | h
  · rw [← hadd0, ← hadd1] at h
    exact hne (add_left_cancel h).symm
  · rw [← hadd0, ← hadd1] at h
    refine hRself ?_
    have h2 : (R + R : W.Point) = 0 := by
      rw [← h]; abel
    exact (neg_eq_of_add_eq_zero_left h2).symm


/-- **PROVEN (2026-07-27) over the characteristic-`2` residue
`count_pointEval_YClass_neg_nonpos_of_ne_neg_char_two`: the WRONG
BRANCH does not vanish.**  With `T = p • S = (x_T, y_T)` affine and `T ≠ ⊖T`, the
pullback of the horizontal through `⊖T` does NOT vanish at the place of
`S`:

`ord_S(yp − y_{⊖T}) ≤ 0`,  where `y_{⊖T} = negY x_T y_T`.

**This is all that is left of the `y`-center.**  The algebraic half is
already PROVEN as `one_le_count_pointEval_YClass_pair`: the PAIR
`(yp − y_T)(yp − y_{⊖T})` has order `≥ 1`, because the two Weierstrass
equations (for `(xp, yp)` over `K` and for `(x_T, y_T)` over `F`)
combine into the identity

`(yp − y_T)(yp − y_{⊖T}) = Q · (xp − x_T)`,
`Q = (xp² + xp x_T + x_T²) + a₂(xp + x_T) + a₄ − a₁ yp`,

with `ord_S(Q) ≥ 0` and `ord_S(xp − x_T) ≥ 1`.  So the pullback of the
pair of horizontals through `T` and `⊖T` always vanishes; the only
content left is WHICH of the two factors does it — and when `T = ⊖T`
the two factors coincide and `2·ord ≥ 1` settles it with no input at
all (that case is discharged inside
`one_le_count_pointEval_YClass_of_smul_ne_zero`).

Since `ord_S(yp − y_{⊖T}) ≥ 0` always (`count_pointEval_nonneg`), the
statement says the order is exactly `0`, i.e. `[p]^*(Y − y_{⊖T})` is a
UNIT at the place of `S`.  Mathematically this holds because `Y − y_{⊖T}`
vanishes on the curve exactly at the points of `y`-coordinate `y_{⊖T}`,
and `T` is such a point iff `y_T = negY x_T y_T`, i.e. iff `T = ⊖T`,
which `hne` excludes.

**STATE (2026-07-27): route (i) is now CARRIED OUT, and with the
characteristic-`2` residue also closed the leaf is proven for EVERY
field.**  The two halves are:

* `one_le_count_pointEval_YClass_of_two_ne_zero` (PROVEN above) — the
  `ψ₂`-tracking `(2y' + a₁x' + a₃)·ψ_p⁴ = ψ_{2p}` of
  `TorsionCard.zsmul_some_aux_strong`, applied both generically at
  `taut` and at the `F`-point `S`, gives `ord_S(yp − y_T) ≥ 1` whenever
  `2 ≠ 0`.  (`hne` is what supplies the tracking's side condition at
  `S`: `T ≠ ⊖T` forces `S ≠ ⊖S`, i.e. `ψ₂(S) ≠ 0`.)
* `count_pointEval_YClass_neg_nonpos_of_ne_neg_char_two` (PROVEN
  2026-07-27) — the characteristic-`2` residue, closed on a THIRD axis,
  TRANSLATION TRANSPORT (`count_lift_translate`), which is in fact
  characteristic-free.  Neither of the two axes that leaf's audit named
  as the only remaining checks — the `ω` division polynomial and
  Artin–Schreier additive tracking — was needed.

Given `ord_S(yp − y_T) ≥ 1`, the conclusion here is immediate and needs
no further geometry: the two factors differ by the NONZERO CONSTANT
`y_{⊖T} − y_T = −ψ₂(T)`, whose order is `0`
(`count_constHom_eq_zero`), so by ultrametricity
(`le_count_spanSingleton_add`) they cannot BOTH have order `≥ 1`.

Route (ii) of the original decomposition — propagation along
translations (`spanSingleton_pointEval_translate` with
`[p] ∘ τ_Q = τ_{p•Q} ∘ [p]`) off a base point `S₀` whose image is
`2`-torsion, which exists by `TorsionCard.smul_surjective` unless
`char F = 2` and `a₁ = 0` — is NOT needed for `char ≠ 2` and does NOT
reach the residue, since a supersingular characteristic-`2` curve has
`E[2] = 0`. -/
theorem count_pointEval_YClass_neg_nonpos_of_ne_neg
    [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S)
    {xT yT : F} {hT : W.Nonsingular xT yT}
    (hTeq : ((p : ℤ) • S : W.Point) =
      WeierstrassCurve.Affine.Point.some xT yT hT)
    (hne : (WeierstrassCurve.Affine.Point.some xT yT hT : W.Point) ≠
      -(WeierstrassCurve.Affine.Point.some xT yT hT : W.Point)) :
    FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (yp - constHom W (W.negY xT yT))) ≤ 0 := by
  classical
  -- `T ≠ ⊖T` says exactly that `y_T ≠ negY x_T y_T`
  have hkey : ∀ (y' : F) (h' : W.Nonsingular xT y'), yT = y' →
      (WeierstrassCurve.Affine.Point.some xT yT hT : W.Point) =
        WeierstrassCurve.Affine.Point.some xT y' h' := by
    intro y' h' hy
    subst hy
    rfl
  have hyne : W.negY xT yT - yT ≠ 0 := by
    intro h0
    refine hne ?_
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact hkey _ _ (by linear_combination -h0)
  by_cases h2 : (2 : F) = 0
  · exact count_pointEval_YClass_neg_nonpos_of_ne_neg_char_two
      hΔ hp h2 hptaut hS0 hpS hvS hTeq hne
  -- the main branch: the `ψ₂`-tracking pins the RIGHT factor
  have hA := one_le_count_pointEval_YClass_of_two_ne_zero
    hΔ hp h2 hptaut hS0 hpS hvS hTeq hne
  by_contra hB
  have hB1 : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (yp - constHom W (W.negY xT yT))) := by omega
  have hdiff : (yp - constHom W yT) +
      (-(yp - constHom W (W.negY xT yT))) =
      constHom W (W.negY xT yT - yT) := by
    rw [map_sub]; ring
  have hcne : constHom W (W.negY xT yT - yT) ≠ 0 := by
    intro h0
    exact hyne ((constHom W).injective (h0.trans (map_zero _).symm))
  have hsum := le_count_spanSingleton_add v hA
    (by rw [count_spanSingleton_neg v]; exact hB1)
    (by rw [hdiff]; exact hcne)
  rw [hdiff, count_constHom_eq_zero hS0 hvS hyne] at hsum
  omega

/-- **PROVEN (2026-07-27) over the pair identity and the single branch
leaf: the `y`-CENTER.**  `ord_S(yp − y_T) ≥ 1`.  When `T = ⊖T` the two
factors of `one_le_count_pointEval_YClass_pair` coincide, so `2·ord ≥ 1`
forces `ord ≥ 1` with no further input; otherwise the branch leaf
`count_pointEval_YClass_neg_nonpos_of_ne_neg` says the other factor
contributes `≤ 0`. -/
theorem one_le_count_pointEval_YClass_of_smul_ne_zero
    [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S)
    {xT yT : F} {hT : W.Nonsingular xT yT}
    (hTeq : ((p : ℤ) • S : W.Point) =
      WeierstrassCurve.Affine.Point.some xT yT hT) :
    1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (yp - constHom W yT)) := by
  classical
  obtain ⟨xp', yp', hpn', hptaut', hxrel⟩ :=
    exists_smul_tautPoint_eq (W := W) hΔ hp
  have hxx : xp = xp' := by
    have hpts := hptaut.symm.trans hptaut'
    injection hpts with hx _
  subst hxx
  have hpair := one_le_count_pointEval_YClass_pair hΔ hp hptaut hS0 hpS hvS hTeq
  have hne0 : yp - constHom W yT ≠ 0 :=
    sub_ne_zero.mpr (smul_taut_yCoord_ne_constHom hpn hxrel yT)
  by_cases hself : (WeierstrassCurve.Affine.Point.some xT yT hT : W.Point) =
      -(WeierstrassCurve.Affine.Point.some xT yT hT : W.Point)
  · have hyeq : W.negY xT yT = yT := by
      rw [WeierstrassCurve.Affine.Point.neg_some] at hself
      injection hself with _ h2
      exact h2.symm
    rw [hyeq, count_spanSingleton_mul v hne0 hne0] at hpair
    omega
  · have hb := count_pointEval_YClass_neg_nonpos_of_ne_neg hΔ hp hptaut hS0 hpS
      hvS hTeq hself
    have hne1 : yp - constHom W (W.negY xT yT) ≠ 0 :=
      sub_ne_zero.mpr (smul_taut_yCoord_ne_constHom hpn hxrel _)
    rw [count_spanSingleton_mul v hne0 hne1] at hpair
    omega

/-- **L4-7 (PROVEN 2026-07-27 over the single leaf
`count_pointEval_YClass_neg_nonpos_of_ne_neg`): the CENTER of the
`[p]`-pullback place.**  For `S ≠ O` affine with `T := p • S ≠ O`, and
any nonzero `z ∈ F[W]`, the pullback `[p]^* z` vanishes at the place of
`S` exactly when `z` vanishes at `T`:

`ord_S([p]^* z) ≥ 1  ↔  z ∈ pointIdeal W (p • S)`.

Equivalently: the prime `([p]^*)⁻¹(m_S)` of `F[W]` is `pointIdeal W T`.

**PROOF.**  Both directions are now formal, over the ultrametric of the
`CountValuation` section above.

*`⟸`.*  `pointIdeal W T = ⟨X − x_T, Y − y_T⟩` is generated by two
elements (`Ideal.mem_span_pair`), so writing `z = c(X − x_T) + d(Y − y_T)`
and applying `[p]^*` it is enough that each generator's pullback has
order `≥ 1` while `[p]^* c`, `[p]^* d` have order `≥ 0`
(`count_pointEval_nonneg`).  `ord_S(xp − x_T) ≥ 1` is FREE from the
vertical brick `count_pointEval_XClass_of_smul_ne_zero`, whose value is
`mult_T((T) + (⊖T)) ≥ 1`; `ord_S(yp − y_T) ≥ 1` is
`one_le_count_pointEval_YClass_of_smul_ne_zero` below.  `[p]^*` is
injective (`pointEval_injective_of_forall_ne_constHom`), so no summand
degenerates to `0`.

*`⟹`.*  Formal from `⟸` by maximality: if `z ∉ I_T` then
`w + c·z = 1` with `w ∈ I_T`, and `[p]^*` turns that into a sum of two
terms of order `≥ 1` equal to `1`, whose order is `0`. -/
theorem one_le_count_pointEval_iff_mem_pointIdeal_smul
    [IsDedekindDomain W.CoordinateRing]
    (hΔ : W.Δ ≠ 0) (hp : (p : F) ≠ 0)
    {xp yp : W.FunctionField} {hpn : (curveK W).Nonsingular xp yp}
    (hptaut : (p : ℤ) • tautPoint W hΔ =
      WeierstrassCurve.Affine.Point.some xp yp hpn)
    {S : W.Point} (hS0 : S ≠ 0) (hpS : (p : ℤ) • S ≠ 0)
    {v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing}
    (hvS : v.asIdeal = pointIdeal W S)
    {z : W.CoordinateRing} (hz : z ≠ 0) :
    1 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left z)) ↔
      z ∈ pointIdeal W ((p : ℤ) • S) := by
  classical
  obtain ⟨xp', yp', hpn', hptaut', hxrel⟩ :=
    exists_smul_tautPoint_eq (W := W) hΔ hp
  have hxx : xp = xp' := by
    have hpts := hptaut.symm.trans hptaut'
    injection hpts with hx _
  subst hxx
  have hinj : Function.Injective (pointEval (constHom W) hpn.left) :=
    pointEval_injective_of_forall_ne_constHom hpn
      (smul_taut_xCoord_ne_constHom hxrel)
  set φ := pointEval (constHom W) hpn.left with hφ
  obtain ⟨xT, yT, hT, hTeq⟩ :
      ∃ (xT yT : F) (hT : W.Nonsingular xT yT),
        ((p : ℤ) • S : W.Point) =
          WeierstrassCurve.Affine.Point.some xT yT hT := by
    cases hcase : ((p : ℤ) • S : W.Point) with
    | zero => exact absurd hcase hpS
    | some xT yT hT => exact ⟨xT, yT, hT, rfl⟩
  -- the two generators of the point ideal at `T`
  have hxval : φ (CoordinateRing.XClass W xT) = xp - constHom W xT := by
    rw [hφ, XClass_eq, map_sub]
    simp only [coordX, coordC]
    rw [pointEval_X, pointEval_C]
  have hyval : φ (CoordinateRing.YClass W (Polynomial.C yT)) =
      yp - constHom W yT := by
    rw [hφ, CoordinateRing.YClass]
    simp only [map_sub]
    rw [pointEval_Y, pointEval_C]
  have hxcount := count_pointEval_XClass_of_smul_ne_zero (W := W)
    hΔ hp hptaut hT hS0 hpS hvS
  rw [hxval] at hxcount
  have hx1 : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (xp - constHom W xT)) := by
    rw [hxcount, hTeq]
    have : (1 : ℕ) ≤ Multiset.count
        (WeierstrassCurve.Affine.Point.some xT yT hT : W.Point)
        (WeierstrassCurve.Affine.Point.some xT yT hT ::ₘ
          (-WeierstrassCurve.Affine.Point.some xT yT hT : W.Point) ::ₘ 0) := by
      rw [Multiset.count_cons_self]; omega
    exact_mod_cast this
  have hy1 : 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (yp - constHom W yT)) :=
    one_le_count_pointEval_YClass_of_smul_ne_zero hΔ hp hptaut hS0 hpS hvS hTeq
  -- nonnegativity of every pullback
  have hnn : ∀ w : W.CoordinateRing, 0 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (φ w)) := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp [hφ, FractionalIdeal.count_zero]
    · exact count_pointEval_nonneg hΔ hp hptaut hS0 hpS hvS hw
  -- the `⟸` half, for an arbitrary nonzero member of the point ideal
  have key : ∀ w : W.CoordinateRing, w ∈ pointIdeal W ((p : ℤ) • S) →
      w ≠ 0 →
      1 ≤ FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (φ w)) := by
    intro w hwmem hw0
    rw [hTeq, pointIdeal_some, CoordinateRing.XYIdeal] at hwmem
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hwmem
    have hsum : φ c * (xp - constHom W xT) + φ d * (yp - constHom W yT) = φ w := by
      rw [← hcd, map_add, map_mul, map_mul, hxval, hyval]
    have hwne : φ w ≠ 0 := fun h0 => hw0 (hinj (by rw [h0, map_zero]))
    rcases eq_or_ne (φ c * (xp - constHom W xT)) 0 with hA | hA
    · have hsum' : φ d * (yp - constHom W yT) = φ w := by
        rw [← hsum, hA, zero_add]
      rw [← hsum']
      exact le_count_spanSingleton_mul_of_nonneg v (hnn d) hy1
        (by rw [hsum']; exact hwne)
    rcases eq_or_ne (φ d * (yp - constHom W yT)) 0 with hB | hB
    · have hsum' : φ c * (xp - constHom W xT) = φ w := by
        rw [← hsum, hB, add_zero]
      rw [← hsum']
      exact le_count_spanSingleton_mul_of_nonneg v (hnn c) hx1 hA
    · rw [← hsum]
      exact le_count_spanSingleton_add v
        (le_count_spanSingleton_mul_of_nonneg v (hnn c) hx1 hA)
        (le_count_spanSingleton_mul_of_nonneg v (hnn d) hy1 hB)
        (by rw [hsum]; exact hwne)
  refine ⟨fun hcount => ?_, fun hmem => key z hmem hz⟩
  -- the `⟹` half, by maximality of the point ideal
  by_contra hzmem
  have hmax : (pointIdeal W ((p : ℤ) • S)).IsMaximal :=
    pointIdeal_isMaximal_of_ne_zero hpS
  have htop : pointIdeal W ((p : ℤ) • S) ⊔ Ideal.span {z} = ⊤ := by
    by_contra hne
    have heq := hmax.eq_of_le hne (le_sup_left)
    exact hzmem (heq ▸ (le_sup_right (a := pointIdeal W ((p : ℤ) • S))
      (b := Ideal.span {z})) (Ideal.mem_span_singleton_self z))
  have h1mem : (1 : W.CoordinateRing) ∈
      pointIdeal W ((p : ℤ) • S) ⊔ Ideal.span {z} := by
    rw [htop]; trivial
  obtain ⟨w, hwmem, u, humem, hsum⟩ := Submodule.mem_sup.mp h1mem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp humem
  have hφsum : φ w + φ c * φ z = 1 := by
    rw [← map_mul, ← map_add, hsum, map_one]
  have hone : ¬ (1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (1 : W.FunctionField))) := by
    rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
    omega
  have hA : φ w = 0 ∨ 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (φ w)) := by
    rcases eq_or_ne w 0 with rfl | hw
    · exact Or.inl (map_zero _)
    · exact Or.inr (key w hwmem hw)
  have hB : φ c * φ z = 0 ∨ 1 ≤ FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰ (φ c * φ z)) := by
    rcases eq_or_ne (φ c * φ z) 0 with h | h
    · exact Or.inl h
    · exact Or.inr
        (le_count_spanSingleton_mul_of_nonneg v (hnn c) hcount h)
  rcases hA with hA | hA
  · rw [hA, zero_add] at hφsum
    rcases hB with hB | hB
    · rw [hB] at hφsum; exact zero_ne_one hφsum
    · rw [hφsum] at hB; exact hone hB
  · rcases hB with hB | hB
    · rw [hB, add_zero] at hφsum
      rw [hφsum] at hA; exact hone hA
    · have hs1 := le_count_spanSingleton_add v hA hB
        (by rw [hφsum]; exact one_ne_zero)
      rw [hφsum] at hs1; exact hone hs1

/-- **L4-7: the `[p]`-pullback of a LINE, at an affine place lying over
an affine point** (PROVEN 2026-07-26 over the two center leaves
`count_pointEval_nonneg` / `one_le_count_pointEval_iff_mem_pointIdeal_smul`).
Same setup as
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

**State of play (2026-07-26): the reduction below is now FORMALIZED.**
The proof is the one sketched here, over the two center leaves
`count_pointEval_nonneg` (positivity) and
`one_le_count_pointEval_iff_mem_pointIdeal_smul` (the center) — the two
ingredients this docstring already named.  Everything else — the norm
identity, the three vertical-brick evaluations, the divisor dictionary
and the chord enumeration — is proven.

*The norm identity.*  Let `ι` be the hyperelliptic involution and `L`
the line class.  Then `L·ι L` is (minus) a product of three verticals.
The implementation does not go through `involHom` at all: mathlib's
`CoordinateRing.C_addPolynomial` already exhibits `ι L` as
`mk W (negPolynomial − C ℓ₀)` and pairs it with `L`, and
`CoordinateRing.C_addPolynomial_slope` identifies the product with
`−(X − x₁)(X − x₂)(X − x₃)`.  The mirrored divisor
`⟨ι L⟩ = I_{⊖P₁}·I_{⊖P₂}·I_{⊖P₃}` is then obtained by CANCELLING
`⟨L⟩ = I_{P₁}·I_{P₂}·I_{P₃}` (`YIdeal_eq_prod_pointIdeal`) against
`⟨X − x_i⟩ = I_{P_i}·I_{⊖P_i}` (`span_XClass_eq_pointIdeal_mul_neg`) in
the cancellative ideal monoid of the Dedekind domain `F[W]` — cheaper
than transporting ideals along `ι`.
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

*The remaining mathematics is the center, and it is exactly the
statement that the `y`-coordinate of `p • taut` specializes correctly*:
the vertical brick pins `x(p • taut) ↦ x_T` at the place of `S`, which
only determines the center up to `T ↔ ⊖T`.  Every quantity computable
from `polyClass` data is `ι`-symmetric, so the ambiguity cannot be
resolved that way (concretely `w = yp − y_T` and `w̄ = yp − y(⊖T)` differ
by the constant `ψ₂(T)`, and `w·w̄` and `w + w̄` are both computable while
neither singles out `w`).  What is needed is `ord_S(yp − y_T) ≥ 1`.
**Both known routes to it — the `ψ₂`-tracking of
`TorsionCard.zsmul_some_aux_strong`, and propagation along translations
off a base point whose image is `2`-torsion (`TorsionCard.smul_surjective`,
now PROVEN) — are written out in full at
`one_le_count_pointEval_iff_mem_pointIdeal_smul`, and both leave the same
characteristic-`2` residue** that blocks the last case of
`rootMultiplicity_Φ_sub_C_mul_ΨSq`.  Recorded there rather than here so
that the two copies cannot drift apart. -/
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
  classical
  haveI := isDedekindDomain_coordinateRing hΔ
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
  have hadd := Point.add_some (h₁ := h₁) (h₂ := h₂) hxy
  have h₃ : W.Nonsingular (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
      (W.negY (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
        (W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂))) :=
    (WeierstrassCurve.Affine.nonsingular_neg ..).mpr
      (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy)
  -- the three X-brick instances, taken BEFORE abstracting the points
  have hV₁ := count_pointEval_XClass_of_smul_ne_zero (W := W) hΔ hp hptaut h₁ hS0 hpS hvS
  have hV₂ := count_pointEval_XClass_of_smul_ne_zero (W := W) hΔ hp hptaut h₂ hS0 hpS hvS
  have hV₃ := count_pointEval_XClass_of_smul_ne_zero (W := W) hΔ hp hptaut h₃ hS0 hpS hvS
  have hLne : CoordinateRing.YClass W
      (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) ≠ 0 :=
    CoordinateRing.YClass_ne_zero _
  have hnorm : CoordinateRing.YClass W
        (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) *
      CoordinateRing.mk W (W.negPolynomial -
        Polynomial.C (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))) =
      -(CoordinateRing.XClass W x₁ * CoordinateRing.XClass W x₂ *
        CoordinateRing.XClass W (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))) := by
    rw [← CoordinateRing.C_addPolynomial_slope h₁.left h₂.left hxy,
      CoordinateRing.C_addPolynomial, map_mul]
    rfl
  have hVne : (CoordinateRing.XClass W x₁ * CoordinateRing.XClass W x₂ *
      CoordinateRing.XClass W (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (CoordinateRing.XClass_ne_zero _)
      (CoordinateRing.XClass_ne_zero _)) (CoordinateRing.XClass_ne_zero _)
  have hL'ne : CoordinateRing.mk W (W.negPolynomial -
      Polynomial.C (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnorm
    exact hVne (neg_eq_zero.mp hnorm.symm)
  -- ── abstract the three points
  set P₁ : W.Point := WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ with hP₁d
  set P₂ : W.Point := WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ with hP₂d
  set P₃ : W.Point := WeierstrassCurve.Affine.Point.some _ _ h₃ with hP₃d
  set L : W.CoordinateRing :=
    CoordinateRing.YClass W (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) with hLd
  set L' : W.CoordinateRing :=
    CoordinateRing.mk W (W.negPolynomial -
      Polynomial.C (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))) with hL'd
  have hP₃ : (-(P₁ + P₂) : W.Point) = P₃ := by
    rw [hP₁d, hP₂d, hadd, Point.neg_some]
  have hP₁0 : P₁ ≠ 0 := Point.some_ne_zero h₁
  have hP₂0 : P₂ ≠ 0 := Point.some_ne_zero h₂
  have hP₃0 : P₃ ≠ 0 := Point.some_ne_zero h₃
  have hnegP₃ : (-P₃ : W.Point) = P₁ + P₂ := by rw [← hP₃, neg_neg]
  have hne21 : P₂ ≠ -P₁ := by
    rw [hP₁d, hP₂d, Point.neg_some]
    intro hc
    injection hc with hx hy
    refine hxy ⟨hx.symm, ?_⟩
    rw [hx, hy]
    simp only [WeierstrassCurve.Affine.negY]
    ring
  -- ── the two ideal factorizations
  have hLspan : Ideal.span {L} =
      pointIdeal W P₁ * (pointIdeal W P₂ * pointIdeal W P₃) := by
    rw [hLd, show Ideal.span {CoordinateRing.YClass W
        (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))} =
        CoordinateRing.YIdeal W (linePolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂)) from rfl,
      YIdeal_eq_prod_pointIdeal h₁ h₂ hxy, hP₃]
  have hprodne : pointIdeal W P₁ * (pointIdeal W P₂ * pointIdeal W P₃) ≠ 0 := by
    rw [← hLspan]
    simpa using hLne
  have hs₁ : Ideal.span {CoordinateRing.XClass W x₁} =
      pointIdeal W P₁ * pointIdeal W (-P₁) :=
    span_XClass_eq_pointIdeal_mul_neg h₁
  have hs₂ : Ideal.span {CoordinateRing.XClass W x₂} =
      pointIdeal W P₂ * pointIdeal W (-P₂) :=
    span_XClass_eq_pointIdeal_mul_neg h₂
  have hs₃ : Ideal.span {CoordinateRing.XClass W
      (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))} =
      pointIdeal W P₃ * pointIdeal W (-P₃) :=
    span_XClass_eq_pointIdeal_mul_neg h₃
  have hL'span : Ideal.span {L'} =
      pointIdeal W (-P₁) * (pointIdeal W (-P₂) * pointIdeal W (-P₃)) := by
    refine mul_left_cancel₀ hprodne ?_
    calc pointIdeal W P₁ * (pointIdeal W P₂ * pointIdeal W P₃) * Ideal.span {L'}
        = Ideal.span {L} * Ideal.span {L'} := by rw [hLspan]
      _ = Ideal.span {L * L'} :=
          Ideal.span_singleton_mul_span_singleton L L'
      _ = Ideal.span {CoordinateRing.XClass W x₁} *
            Ideal.span {CoordinateRing.XClass W x₂} *
            Ideal.span {CoordinateRing.XClass W
              (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))} := by
          rw [hnorm, Ideal.span_singleton_neg,
            Ideal.span_singleton_mul_span_singleton,
            Ideal.span_singleton_mul_span_singleton]
      _ = pointIdeal W P₁ * pointIdeal W (-P₁) *
            (pointIdeal W P₂ * pointIdeal W (-P₂)) *
            (pointIdeal W P₃ * pointIdeal W (-P₃)) := by
          rw [hs₁, hs₂, hs₃]
      _ = pointIdeal W P₁ * (pointIdeal W P₂ * pointIdeal W P₃) *
            (pointIdeal W (-P₁) *
              (pointIdeal W (-P₂) * pointIdeal W (-P₃))) := by ring
  -- ── the norm identity in orders
  have hAB : FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left L) *
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left L') =
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left (CoordinateRing.XClass W x₁)) *
       FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left (CoordinateRing.XClass W x₂))) *
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left
          (CoordinateRing.XClass W (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)))) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, ← map_mul, ← map_mul,
      ← map_mul, hnorm, map_neg, spanSingleton_neg']
  have hV₁₂ne : FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left (CoordinateRing.XClass W x₁)) *
      FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left (CoordinateRing.XClass W x₂)) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, ← map_mul]
    exact hspan0 _ (mul_ne_zero (CoordinateRing.XClass_ne_zero x₁)
      (CoordinateRing.XClass_ne_zero x₂))
  have hcnt : FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left L)) +
      FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left L')) =
      (FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left (CoordinateRing.XClass W x₁))) +
      FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left (CoordinateRing.XClass W x₂)))) +
      FractionalIdeal.count W.FunctionField v
        (FractionalIdeal.spanSingleton W.CoordinateRing⁰
          (pointEval (constHom W) hpn.left
            (CoordinateRing.XClass W (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))))) := by
    rw [← FractionalIdeal.count_mul W.FunctionField v
        (hspan0 _ hLne) (hspan0 _ hL'ne), hAB,
      FractionalIdeal.count_mul W.FunctionField v hV₁₂ne
        (hspan0 _ (CoordinateRing.XClass_ne_zero _)),
      FractionalIdeal.count_mul W.FunctionField v
        (hspan0 _ (CoordinateRing.XClass_ne_zero x₁))
        (hspan0 _ (CoordinateRing.XClass_ne_zero x₂))]
  rw [hV₁, hV₂, hV₃] at hcnt
  -- ── the enumeration of the chord divisor
  have hkey : ∀ Q : W.Point, (Q = P₁ ∨ Q = P₂ ∨ Q = P₃) →
      (Q = -P₁ ∨ Q = -P₂ ∨ Q = -P₃) → Q = -Q := by
    rintro Q (rfl | rfl | rfl) (h | h | h)
    · exact h
    · exact absurd (by rw [h, neg_neg] : P₂ = -P₁) hne21
    · rw [hnegP₃] at h; exact absurd (by simpa using h.symm : P₂ = 0) hP₂0
    · exact absurd h hne21
    · exact h
    · rw [hnegP₃] at h; exact absurd (by simpa using h.symm : P₁ = 0) hP₁0
    · exact absurd (by rw [← hnegP₃, h, neg_neg] : P₁ + P₂ = P₁) (by simp)
    · exact absurd (by rw [← hnegP₃, h, neg_neg] : P₁ + P₂ = P₂) (by simp)
    · exact h
  have hex12 : ∀ Q : W.Point, Q = -Q → Q = P₁ → Q = P₂ → False := by
    intro Q hQ e1 e2
    exact hne21 (by rw [← e2, ← e1]; exact hQ)
  have hex13 : ∀ Q : W.Point, Q = -Q → Q = P₁ → Q = P₃ → False := by
    intro Q hQ e1 e3
    have h1 : P₁ + P₂ = P₁ := by rw [← hnegP₃, ← e3, ← hQ]; exact e1
    exact absurd h1 (by simp)
  have hex23 : ∀ Q : W.Point, Q = -Q → Q = P₂ → Q = P₃ → False := by
    intro Q hQ e2 e3
    have h1 : P₁ + P₂ = P₂ := by rw [← hnegP₃, ← e3, ← hQ]; exact e2
    exact absurd h1 (by simp)
  have hle1 : ∀ Q : W.Point, Q = -Q →
      Multiset.count Q (P₁ ::ₘ P₂ ::ₘ P₃ ::ₘ 0) ≤ 1 := by
    intro Q hQ
    simp only [Multiset.count_cons, Multiset.count_zero, zero_add]
    by_cases e1 : Q = P₁
    · by_cases e2 : Q = P₂
      · exact (hex12 Q hQ e1 e2).elim
      · by_cases e3 : Q = P₃
        · exact (hex13 Q hQ e1 e3).elim
        · rw [if_neg e3, if_neg e2, if_pos e1]
    · by_cases e2 : Q = P₂
      · by_cases e3 : Q = P₃
        · exact (hex23 Q hQ e2 e3).elim
        · rw [if_neg e3, if_pos e2, if_neg e1]
      · by_cases e3 : Q = P₃
        · rw [if_pos e3, if_neg e2, if_neg e1]
        · rw [if_neg e3, if_neg e2, if_neg e1]
          omega
  have hnegiff : ∀ Q : W.Point, Q = -Q → ∀ R : W.Point, (Q = -R) ↔ (Q = R) := by
    intro Q hQ R
    constructor
    · intro h; calc Q = -Q := hQ
        _ = -(-R) := by rw [h]
        _ = R := neg_neg R
    · intro h; calc Q = -Q := hQ
        _ = -R := by rw [h]
  have hle2 : ∀ Q : W.Point, Q = -Q →
      Multiset.count Q ((-P₁) ::ₘ (-P₂) ::ₘ (-P₃) ::ₘ 0) ≤ 1 := by
    intro Q hQ
    have hEq : Multiset.count Q ((-P₁) ::ₘ (-P₂) ::ₘ (-P₃) ::ₘ 0)
        = Multiset.count Q (P₁ ::ₘ P₂ ::ₘ P₃ ::ₘ 0) := by
      simp only [Multiset.count_cons, Multiset.count_zero, hnegiff Q hQ]
    rw [hEq]; exact hle1 Q hQ
  -- ── membership dictionaries
  have hc1 := one_le_count_pointEval_iff_mem_pointIdeal_smul
    (W := W) hΔ hp hptaut hS0 hpS hvS hLne
  have hc2 := one_le_count_pointEval_iff_mem_pointIdeal_smul
    (W := W) hΔ hp hptaut hS0 hpS hvS hL'ne
  rw [mem_pointIdeal_iff_of_span_eq_prod_three hΔ hP₁0 hP₂0 hP₃0 hpS hLspan] at hc1
  rw [mem_pointIdeal_iff_of_span_eq_prod_three hΔ (neg_ne_zero.mpr hP₁0)
      (neg_ne_zero.mpr hP₂0) (neg_ne_zero.mpr hP₃0) hpS hL'span] at hc2
  have hmpos : 0 < Multiset.count ((p : ℤ) • S) (P₁ ::ₘ P₂ ::ₘ P₃ ::ₘ 0) ↔
      ((p : ℤ) • S = P₁ ∨ (p : ℤ) • S = P₂ ∨ (p : ℤ) • S = P₃) := by
    simp [Multiset.count_pos]
  have hm'pos : 0 < Multiset.count ((p : ℤ) • S)
      ((-P₁) ::ₘ (-P₂) ::ₘ (-P₃) ::ₘ 0) ↔
      ((p : ℤ) • S = -P₁ ∨ (p : ℤ) • S = -P₂ ∨ (p : ℤ) • S = -P₃) := by
    simp [Multiset.count_pos]
  rw [hP₃]
  refine count_arith
    (B := FractionalIdeal.count W.FunctionField v
      (FractionalIdeal.spanSingleton W.CoordinateRing⁰
        (pointEval (constHom W) hpn.left L')))
    (m' := Multiset.count ((p : ℤ) • S)
      ((-P₁) ::ₘ (-P₂) ::ₘ (-P₃) ::ₘ 0)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hcnt]
    simp only [Multiset.count_cons, Multiset.count_zero, zero_add]
    push_cast
    ring
  · exact count_pointEval_nonneg (W := W) hΔ hp hptaut hS0 hpS hvS hLne
  · exact count_pointEval_nonneg (W := W) hΔ hp hptaut hS0 hpS hvS hL'ne
  · rw [hc1, hmpos]
  · rw [hc2, hm'pos]
  · intro hm hm'
    have hself := hkey _ (hmpos.mp hm) (hm'pos.mp hm')
    exact ⟨le_antisymm (hle1 _ hself) hm, le_antisymm (hle2 _ hself) hm'⟩

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
`count_pointEval_YClass_of_smul_ne_zero` (PROVEN 2026-07-26, over the two
center leaves `count_pointEval_nonneg` /
`one_le_count_pointEval_iff_mem_pointIdeal_smul`) — and then propagated to a
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
is now IMPLEMENTED: the vertical brick costs exactly the universal
polynomial identity `sq_wronskian_mul_Ψ₂Sq` — the algebraic form of
`[p]^*ω = p·ω`, needing none of the machinery below — plus the
characteristic-`2` residue
`rootMultiplicity_Φ_sub_C_mul_ΨSq_of_Ψ₂Sq_inseparable`.)  Two routes
were known before, and neither is in mathlib:

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

/-- **L4-7 brick (PROVEN, and axiom-clean since 2026-07-27): the
multiplicity-one `[p]`-pullback formula
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
  over the two bricks `count_pointEval_XClass_of_smul_ne_zero` /
  `count_pointEval_YClass_of_smul_ne_zero`, both now PROVEN in turn — the
  vertical one over the polynomial leaves
  `sq_wronskian_mul_Ψ₂Sq` / `rootMultiplicity_Φ_sub_C_mul_ΨSq_of_Ψ₂Sq_inseparable`
  (separability of `[p]`), the line one over the center leaves
  `count_pointEval_nonneg` / `one_le_count_pointEval_iff_mem_pointIdeal_smul`;
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
