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

* L4-4 substrate (2026-07-24): the **tautological point** of `W` over
  its own function field `K = Frac(F[W])` (`tautX`/`tautY`/`tautPoint`,
  with `taut_evalEval_mk` the evaluation bridge — all PROVEN following
  the `TautologicalPoint.lean` pattern, generalized from the universal
  curve to any Weierstrass curve over a field); the **evaluation
  homomorphism** `pointEval : F[W] →+* K` at any `K`-point of the
  base-changed curve; the **translation pullback**
  `translationEval κ := pointEval (taut ⊕ κ)` realizing `h ↦ h∘τ_κ`,
  and its fraction-field extension `translationHom κ : K →+* K`
  (through the sorried leaf `translationEval_injective`).

* `exists_span_pointIdeal_of_translation_fixed` (L4-5/6, sorry node):
  the **fixed-field descent** — if the auxiliary function `g` of the
  descent is fixed by every `p`-torsion translation, it descends
  through `Fix(E[p]) = [p]^*K` to `g = h∘[p]`, forcing the point ideal
  of the original point to be principal.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Fermat.FLT.EllipticCurve.Torsion

@[expose] public section

namespace WeilPairing

open WeierstrassCurve WeierstrassCurve.Affine
open scoped nonZeroDivisors Polynomial.Bivariate

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

/-! ## L4-4: the tautological-point substrate for the translation action

The translation pullback `h ↦ h∘τ_κ` on the function field
`K = Frac(F[W])` is realized as evaluation at the point `taut ⊕ κ` of
the base-changed curve `W ⁄ K`, where `taut = (X̄, Ȳ)` is the
tautological point (the images of the coordinates in `K`).  This
instantiates the `TautologicalPoint.lean` pattern (there developed for
the universal curve) at an arbitrary Weierstrass curve over a field —
HLEG-NOTES.md §4(B), stage L4-4. -/

omit [DecidableEq F] in
open Polynomial in
/-- Elements of the base field embed in the coordinate ring as the
classes of constant polynomials. -/
lemma algebraMap_coordinateRing_apply (c : F) :
    algebraMap F W.CoordinateRing c =
      CoordinateRing.mk W (Polynomial.C (Polynomial.C c)) := by
  rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing,
    AdjoinRoot.algebraMap_eq]
  rfl

/-- The function field of a Weierstrass curve carries a (classical)
decidable equality — needed for the group law on the points of the
base-changed curve `W ⁄ Frac(F[W])`. -/
noncomputable instance instDecEqFunctionField : DecidableEq W.FunctionField :=
  Classical.decEq _

variable (W)

/-- The tautological `x`-coordinate of `W` in its own function field:
the image of `X`. -/
noncomputable def tautX : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField
    (CoordinateRing.mk W (Polynomial.C Polynomial.X))

/-- The tautological `y`-coordinate of `W` in its own function field:
the image of `Y`. -/
noncomputable def tautY : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Polynomial.X)

omit [DecidableEq F] in
open Polynomial in
/-- **Evaluation at the tautological point is the quotient map**: for a
bivariate polynomial over `F`, mapping the coefficients into the
function field and evaluating at `(tautX, tautY)` agrees with reducing
modulo the Weierstrass polynomial and embedding into the function
field. -/
theorem taut_evalEval_mk (g : F[X][Y]) :
    (g.map (mapRingHom (algebraMap F W.FunctionField))).evalEval
        (tautX W) (tautY W) =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W g) := by
  have hhom : (Polynomial.evalEvalRingHom (tautX W) (tautY W)).comp
      (mapRingHom (mapRingHom (algebraMap F W.FunctionField))) =
      (algebraMap W.CoordinateRing W.FunctionField).comp
        ((CoordinateRing.mk W : F[X][Y] →+* W.CoordinateRing)) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · apply RingHom.ext
        intro c
        simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom,
          Polynomial.map_C, coe_evalRingHom, eval_C]
        rw [IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
        exact congrArg (algebraMap W.CoordinateRing W.FunctionField)
          (algebraMap_coordinateRing_apply c)
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom,
          Polynomial.map_C, Polynomial.map_X, coe_evalRingHom, eval_C, eval_X]
        rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom,
        Polynomial.map_X, coe_evalRingHom, eval_C, eval_X]
      rfl
  exact DFunLike.congr_fun hhom g

omit [DecidableEq F] in
open Polynomial in
/-- The tautological point satisfies the Weierstrass equation of the
base-changed curve. -/
theorem taut_equation :
    (W⁄W.FunctionField).toAffine.Equation (tautX W) (tautY W) := by
  show ((W⁄W.FunctionField).toAffine.polynomial).evalEval (tautX W) (tautY W) = 0
  have hpoly : (W⁄W.FunctionField).toAffine.polynomial =
      W.polynomial.map (mapRingHom (algebraMap F W.FunctionField)) :=
    WeierstrassCurve.Affine.map_polynomial ..
  rw [hpoly, taut_evalEval_mk, AdjoinRoot.mk_self, map_zero]

omit [DecidableEq F] in
/-- **The tautological point is nonsingular** (when the curve has
nonzero discriminant). -/
theorem taut_nonsingular (hΔ : W.Δ ≠ 0) :
    (W⁄W.FunctionField).toAffine.Nonsingular (tautX W) (tautY W) := by
  refine (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero ?_).mp
    (taut_equation W)
  show (W⁄W.FunctionField).toAffine.Δ ≠ 0
  rw [show (W⁄W.FunctionField).toAffine.Δ =
    algebraMap F W.FunctionField W.Δ from WeierstrassCurve.map_Δ ..]
  exact fun hc => hΔ ((algebraMap F W.FunctionField).injective (by rwa [map_zero]))

/-- The tautological point of `W` on the base-changed curve
`W ⁄ Frac(F[W])`, as a group-law point. -/
noncomputable def tautPoint (hΔ : W.Δ ≠ 0) : (W⁄W.FunctionField).Point :=
  .some (tautX W) (tautY W) (taut_nonsingular W hΔ)

open Polynomial in
/-- **The evaluation homomorphism** of the coordinate ring at a
function-field point of the base-changed curve: `F[W] →+* K` sending
`X ↦ u`, `Y ↦ v`.  Applied at `taut ⊕ κ` this realizes the translation
pullback `h ↦ h∘τ_κ` (`translationEval`). -/
noncomputable def pointEval {u v : W.FunctionField}
    (h : (W⁄W.FunctionField).toAffine.Equation u v) :
    W.CoordinateRing →+* W.FunctionField :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap F W.FunctionField) u) v <| by
    rw [Polynomial.eval₂_eval₂RingHom_apply,
      ← WeierstrassCurve.Affine.map_polynomial]
    exact h

/-- **The translation pullback** `h ↦ h∘τ_κ` on the coordinate ring:
evaluation at the point `taut ⊕ κ` of the base-changed curve.  (The
`O`-branch of the match is junk — `taut ⊕ κ` is affine for every
`F`-point `κ` since the tautological coordinates are not constants —
kept total for definitional convenience.) -/
noncomputable def translationEval (hΔ : W.Δ ≠ 0) (κ : W.Point) :
    W.CoordinateRing →+* W.FunctionField :=
  match tautPoint W hΔ +
      Point.map (W' := W) (Algebra.ofId F W.FunctionField) κ with
  | .zero => algebraMap W.CoordinateRing W.FunctionField
  | .some _ _ h => pointEval W h.left

/-- **Injectivity of the translation pullback** (sorry node — L4-4 of
the nondegeneracy descent, HLEG-NOTES.md §4(B)): evaluation of the
coordinate ring at `taut ⊕ κ` is injective.  Route (per the staged
plan): composing with the translation by `⊖κ` — i.e. evaluating the
image at `taut ⊖ κ` — recovers evaluation at
`(taut ⊕ κ) ⊖ κ = taut`, which is the canonical embedding
`F[W] ↪ K` (`AdjoinRoot`-induction against `taut_evalEval_mk`); no
transcendence argument is needed.  The composition identity is the
taut-multiplication content of `TautMultiplication.lean` transported
to `W` over its own function field. -/
theorem translationEval_injective (hΔ : W.Δ ≠ 0) (κ : W.Point) :
    Function.Injective (translationEval W hΔ κ) := by
  sorry

/-- **The translation automorphism of the function field**: the
fraction-field extension of the translation pullback
`translationEval κ`.  This is the substrate of the translation
character `χ(κ) = (g∘τ_κ)/g` of the descent (L4-8). -/
noncomputable def translationHom (hΔ : W.Δ ≠ 0) (κ : W.Point) :
    W.FunctionField →+* W.FunctionField :=
  IsFractionRing.lift (translationEval_injective W hΔ κ)

/-- The vertical-line coordinate function of a point: `X − x` at an
affine point `(x, y)` (whose affine divisor is `(P) + (⊖P)`), and `1`
at `O`.  The product `∏_{κ ∈ E[p]} vertical κ` is the denominator
turning the zero-sum Miller generator of
`Σ_{κ} (T'⊕κ) + (⊖κ)` into the descent function `g` with
`div g = Σ_{κ} (T'⊕κ) − (κ)`. -/
noncomputable def verticalClass : W.Point → W.CoordinateRing
  | .zero => 1
  | .some x _ _ => CoordinateRing.XClass W x

section FixedDescent

variable {k : Type*} [Field k] [DecidableEq k] (E : WeierstrassCurve k)
  [E.IsElliptic]

/-- **The fixed-field descent** (sorry node — L4-5/6 of the
nondegeneracy descent, HLEG-NOTES.md §4(B); Silverman AEC III.8.1(c)):
let `x` be a `p`-torsion point, `T'` a `p`-division point of it, and
`a` a Miller generator of the zero-sum divisor multiset
`Σ_{κ ∈ E[p]} (T'⊕κ) + (⊖κ)`; write
`g := a / ∏_{κ ∈ E[p]} vertical κ`, so
`div g = Σ_{κ ∈ E[p]} (T'⊕κ) − (κ) = [p]^*((x) − (O))`.  If `g` is
fixed by every `p`-torsion translation, then `g` lies in the fixed
field of the translation action, which equals `[p]^*K` — the
translation automorphisms are a faithful `E[p]`-action fixing the
constants, so `[K : Fix(E[p])] = p²` by Artin, while `[K : [p]^*K] ≤ p²`
since `tautX` is a root of `Φ_p − ([p]^*x)·ΨSq_p` — hence `g = h∘[p]`
for some `h ∈ K`; comparing divisors through the injectivity of `[p]^*`
forces `div h = (x) − (O)`, i.e. `h` is integral and generates the
point ideal of `x`. -/
theorem exists_span_pointIdeal_of_translation_fixed
    (hΔ : (E⁄k).Δ ≠ 0) (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)
    [Fintype (E.nTorsion p)]
    (x : E.nTorsion p) (T' : (E⁄k).Point)
    (hT2 : ((p : ℕ) : ℤ) • T' = x.val)
    (a : (E⁄k).toAffine.CoordinateRing) (ha0 : a ≠ 0)
    (haspan : Ideal.span {a} =
      (((Finset.univ.val.map fun κ : E.nTorsion p => T' + κ.val) +
        (Finset.univ.val.map fun κ : E.nTorsion p => -κ.val)).map
          (pointIdeal (E⁄k).toAffine)).prod)
    (hfix : ∀ κ : E.nTorsion p,
      translationHom (E⁄k).toAffine hΔ κ.val
          (algebraMap (E⁄k).toAffine.CoordinateRing
              (E⁄k).toAffine.FunctionField a /
            algebraMap (E⁄k).toAffine.CoordinateRing
              (E⁄k).toAffine.FunctionField
              (Finset.univ.val.map fun κ' : E.nTorsion p =>
                verticalClass (E⁄k).toAffine κ'.val).prod) =
        algebraMap (E⁄k).toAffine.CoordinateRing
            (E⁄k).toAffine.FunctionField a /
          algebraMap (E⁄k).toAffine.CoordinateRing
            (E⁄k).toAffine.FunctionField
            (Finset.univ.val.map fun κ' : E.nTorsion p =>
              verticalClass (E⁄k).toAffine κ'.val).prod) :
    ∃ h : (E⁄k).toAffine.CoordinateRing, h ≠ 0 ∧
      Ideal.span {h} = pointIdeal (E⁄k).toAffine x.val := by
  sorry

end FixedDescent

end WeilPairing
