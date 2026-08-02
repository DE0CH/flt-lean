/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.PrincipalDivisorDegree
public import Fermat.FLT.Mathlib.AlgebraicGeometry.BirationalFunctionField
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# From `div f = [x] − [y]` to birationality with the affine line

This file is the SHARP END of the divisor/degree layer that the degree-`1` Riemann–Roch
leaves of `Fermat/FLT/ModularCurve/X0.lean` are gated on.  The layer itself — `divSupport`,
`divCoeff`, `divDegree`, the zero/pole decomposition, the counting lemmas, and the degree
formula `deg (div g) = 0` — lives one module up, in
`Fermat/FLT/Mathlib/AlgebraicGeometry/PrincipalDivisorDegree.lean`, and this file `public
import`s it.  What is added here is the single classical statement that turns the degree
formula into a GEOMETRIC conclusion:

> a rational function with one simple pole at a `K`-rational point generates the function
> field, so `K(X) ↪ K(t)`, so `X` is birational over `K` to the affine line.

## RECONCILED 2026-08-01 — this file used to be a RIVAL divisor layer, and is not one now

Two branches developed a divisor-degree layer on the same day (2026-07-31), one here and
one in `PrincipalDivisorDegree.lean`, and they collided on
`AlgebraicGeometry.Scheme.ord_one` and `AlgebraicGeometry.Scheme.ord_inv` — so no module
could import both, and `X0.lean` (the only would-be importer of either that sees both)
carried an explicit note DELIBERATELY NOT importing this one.  That note is now removed:
the duplicated declarations have been deleted from this file in favour of
`PrincipalDivisorDegree`'s, and this file imports that one.

**The reconciliation deleted two duplicate SORRY LEAVES**, which is why it is worth
recording rather than merely doing.  Both pairs were *definitionally* the same
proposition, verified by `rfl` before either was touched:

* `finite_support_ord hproper hcurve hf : (Function.support (Scheme.ord f)).Finite`
  was `finite_divSupport`, since `Scheme.divSupport g` is by definition
  `Function.support (Scheme.ord g)`;
* `divDegree_eq_zero_curve hproper hcurve hf : divDegree strX f = 0` was
  `divDegree_eq_zero_of_ne_zero`, since this file's `divDegree strX f` was by definition
  `∑ᶠ z, ord f z * residueDegree z`, which is `Scheme.Hom.divDegree strX f` unfolded.

So the frontier fell by two with no mathematics done, and — the point worth keeping —
**a `sorry` in one of two rival modules is invisible to every duplicate scan that keys on
NAMES**, because the two names shared no component.  What found it was elaborating
`example : <one statement> = <the other> := rfl` in a four-second scratch.  The general
check is in `CLAUDE.md` under the duplicate-cut sections; the specific instrument is
`tools/merge/dupstmt.py`, which does not see this pair either, because the two statements
differ in their binder NAMES and in which of `divSupport`/`Function.support` they are
phrased over.

The declarations that were genuinely unique to this file are kept, restated over
`PrincipalDivisorDegree`'s vocabulary: `Scheme.ord_div`, `divDegree_of_ord_eq_sub`,
`residueDegree_eq_of_ord_eq_sub`, the leaf
`exists_hom_functionField_ratFunc_of_ord_eq_sub`, and the bridge
`birationalOver_affineLine_of_ord_eq_sub`.

## Main statements

* `exists_hom_functionField_ratFunc_of_ord_eq_sub` — OPEN LEAF, and the only one in this
  file: a function whose divisor is `[x] − [y]` with both points `K`-rational embeds
  `K(X)` into `K(t)`.  Stichtenoth I.4.11.
* `birationalOver_affineLine_of_ord_eq_sub` — PROVEN over it: the geometric conclusion, in
  a form that mentions no `RelPicEquiv`, no `sectionIdeal`, no `RelPoint` and no base
  scheme.

## The route from `div f = [x] − [y]` to `BirationalOver`, and why it is SHORT

`Fermat/FLT/Mathlib/AlgebraicGeometry/BirationalFunctionField.lean` already proves, with no
sorry:

* `exists_iso_specRatFunc_specFunctionField_of_hom` — a `K`-algebra map `K(X) ⟶ K(t)`
  (merely a MAP: Lüroth upgrades it) gives `Spec (RatFunc K) ≅ Spec K(X)` over `Spec K`;
* `exists_iso_specRatFunc_specFunctionField_affineSpace` — `K(𝔸¹) ≅ K(t)` over `Spec K`;
* `birationalOver_of_iso_specFunctionField` — an isomorphism of function fields over `S`
  IS a birational map over `S`.

So the ONLY thing missing between the divisor hypothesis and the geometric conclusion is a
`K`-embedding `K(X) ↪ K(t)`, which is `exists_hom_functionField_ratFunc_of_ord_eq_sub`
below.  In particular a prover attacking that leaf may produce a mere EMBEDDING and let
`Mathlib`'s Lüroth do the rest; the isomorphism is not needed.

## What is still owed by the layer as a whole

Three leaves, all in `PrincipalDivisorDegree.lean` or here:
`finite_divSupport`, `poleDegree_inv_eq_poleDegree` (both there) and
`exists_hom_functionField_ratFunc_of_ord_eq_sub` (here).  All three are Stichtenoth I.4.11
or its immediate corollaries, and `HyperellipticJacobian.lean` carries the same mathematics
cut to ONE leaf in the abstract-places formulation
(`degOf_poleDivisor_eq_finrank_of_transcendental`); a bridge to that formulation is the
cheapest way to close all three, and is written up on `poleDegree_inv_eq_poleDegree`.
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Elementary `ord` arithmetic missing from `Mathlib`

`Scheme.ord_one` and `Scheme.ord_inv` used to be declared here as well; they are
`PrincipalDivisorDegree.lean`'s now, and this file imports them.  Only the quotient rule,
which that file does not carry, is left. -/

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

-- `ord_one` and `ord_inv` USED TO BE DECLARED HERE, character-for-character as in
-- `PrincipalDivisorDegree` (which is now imported above), `@[simp]` and all.  Two branches
-- built this layer independently and both landed; the duplicate pair is what made the two
-- modules un-co-importable, and `X0.lean` dropped ITS import of this file at release 31
-- rather than resolve it.  Deleted 2026-08-01; recover with
-- `git show 280981f1:Fermat/FLT/Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean`.
lemma ord_div {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) (z : X) :
    ord (f / g) z = ord f z - ord g z := by
  rw [div_eq_mul_inv, ord_mul hf (inv_ne_zero hg), ord_inv hg]
  omega

end Scheme

/-! ### Reading off the degree of a divisor supported at two points -/

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The degree of a divisor supported at two points, read off from the three clauses that
say `div f = [x] − [y]`.

Stated over `Scheme.Hom.divDegree` (`PrincipalDivisorDegree.lean`) — this file's own
`divDegree`, which was definitionally the same `finsum`, was deleted in the 2026-08-01
reconciliation. -/
lemma divDegree_of_ord_eq_sub {S : Scheme.{u}} {strX : X ⟶ S}
    {x y : X} (hxy : x ≠ y) {f : X.functionField}
    (hordx : Scheme.ord f x = 1) (hordy : Scheme.ord f y = -1)
    (hord0 : ∀ z : X, z ≠ x → z ≠ y → Scheme.ord f z = 0) :
    strX.divDegree f = (strX.residueDegree x : ℤ) - (strX.residueDegree y : ℤ) := by
  classical
  have hsupp : (Function.support fun z : X => strX.divCoeff f z) ⊆
      ↑({x, y} : Finset X) := by
    intro z hz
    simp only [Scheme.Hom.divCoeff, Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
    by_contra hmem
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hmem
    exact hz.1 (hord0 z (fun h' => hmem (Or.inl h')) (fun h' => hmem (Or.inr h')))
  rw [Scheme.Hom.divDegree, finsum_eq_finsetSum_of_support_subset _ hsupp,
    Finset.sum_pair hxy]
  simp only [Scheme.Hom.divCoeff, hordx, hordy]
  ring

/-- Two points whose difference is a principal divisor on a smooth proper curve have the
same residue degree — the first consequence of `divDegree_eq_zero`, and the reason the
`residueDegree` hypothesis on `x` in `exists_hom_functionField_ratFunc_of_ord_eq_sub` below
is REDUNDANT rather than an extra obligation on a prover. -/
lemma residueDegree_eq_of_ord_eq_sub {strX : X ⟶ Spec (CommRingCat.of K)}
    (hproper : IsProper strX) (hcurve : SmoothOfRelativeDimension 1 strX)
    {x y : X} (hxy : x ≠ y) {f : X.functionField}
    (hordx : Scheme.ord f x = 1) (hordy : Scheme.ord f y = -1)
    (hord0 : ∀ z : X, z ≠ x → z ≠ y → Scheme.ord f z = 0) :
    strX.residueDegree x = strX.residueDegree y := by
  have h := divDegree_of_ord_eq_sub (strX := strX) hxy hordx hordy hord0
  rw [divDegree_eq_zero hproper hcurve f] at h
  omega

/-! ### The sharp leaf: a single simple rational pole generates the function field -/

/-- **A RATIONAL FUNCTION WITH ONE SIMPLE POLE AT A `K`-RATIONAL POINT GENERATES THE
FUNCTION FIELD** (sorry leaf, cut 2026-07-31) — the sharp form of the degree theory, and
the ONLY thing standing between `div f = [x] − [y]` and
`Scheme.BirationalOver … (𝔸¹_K ↘ Spec K)`.

The conclusion asks only for a `K`-ALGEBRA MAP `K(X) ⟶ K(t)`, in the `Spec.map`-triangle
shape that `exists_iso_specRatFunc_specFunctionField_of_hom`
(`BirationalFunctionField.lean`, PROVEN) consumes; that theorem then applies `Mathlib`'s
Lüroth (`RatFunc.Luroth.algEquiv`) to upgrade the map to an isomorphism.  **So a prover
does NOT have to produce an isomorphism** — a map suffices, and `K(X) = K(f)` is the
natural way to produce one.

**IT IS TRUE, AND HERE IS THE CLASSICAL PROOF.**  `hdiv` says the pole divisor of `f` is
exactly `1 · [y]`, so Stichtenoth I.4.11 gives `[K(X) : K(f)] = deg (f)_∞ =
1 · [κ(y) : K] = 1` by `hydeg`, i.e. `K(X) = K(f)`.  And `f` is transcendental over `K`:
an algebraic `f` over a field is a constant on an integral scheme, whose divisor is `0`,
contradicting `hxy` through `hdiv` at `z = x`.  So `K(f) ≅ K(t)` as `K`-algebras and the
required map is that isomorphism.

**`hydeg` IS LOAD-BEARING AND `hxdeg` IS NOT.**  If the pole `y` has `[κ(y) : K] = d > 1`
then `[K(X) : K(f)] = d` and `X` need not be rational at all — a pointless conic over `ℝ`
carries functions with a single pole of degree `2`.  `hxdeg`, by contrast, FOLLOWS from
`hydeg` by `residueDegree_eq_of_ord_eq_sub` above; it is stated because it costs a consumer
nothing (both points are `K`-rational at every call site in this development) and because
it keeps this leaf independent of `divDegree_eq_zero`, so that the two may be attacked in
either order.

**`hproper` IS LOAD-BEARING, WITH THE COUNTEREXAMPLE THAT ALSO GOVERNS THE `X0.lean`
CONSUMER.**  Let `E : y² = x³ + 4x + 1` over `𝔽₅`, which has `E(𝔽₅) ≅ ℤ/8` (PARI/GP
`ellgroup` returns `[8]`, and `8` is inside the Hasse interval `[2, 10]`); let `P` generate
it and put `C := E ∖ {O, P}`, a smooth affine curve over `K = 𝔽₅`.  From
`ℤ² → Pic E → Pic C → 0` with `[O] ↦ (1, 0)` and `[P] ↦ (1, [P − O])` in
`Pic E ≅ ℤ ⊕ ℤ/8`, the image is everything, so `Pic C = 0`: every pair of the six remaining
`𝔽₅`-points is linearly equivalent, so `f` with `div f = [x] − [y]`, `x ≠ y`, EXISTS and
every hypothesis but `hproper` holds.  But `K(C) = K(E)` has genus `1`, and a genus-`1`
field admits no `K`-embedding into `K(t)` (Lüroth: every intermediate field of `K(t)/K` is
`K` or a rational function field).  So a proof that does not consume `hproper` is wrong.

**`hcurve` IS LOAD-BEARING** for the same reason it is in `divDegree_eq_zero`: it supplies
dimension `1` and regularity, without which `Scheme.ord` is not a valuation and "pole
divisor" is not defined.  `hxy` is what makes `f` nonconstant.

**NO `coheight` HYPOTHESIS IS NEEDED, AND THAT IS A FACT ABOUT `Mathlib`'S CONVENTION
RATHER THAN A WEAKENING.**  `Scheme.ord f z` is defined to be `0` unless `coheight z = 1`
(`ord_eq_zero_of_coheight_neq_one`), so `hordx : ord f x = 1` already FORCES
`coheight x = 1`, and likewise for `y`.  An earlier draft of this leaf carried
`coheight x = 1` and `coheight y = 1` as hypotheses; they were removed as derivable, not
dropped as inconvenient, and the leaf is inhabited exactly as before.

**THE DIVISOR IS WRITTEN AS THREE CLAUSES, NOT AS `∀ z, ord f z = [z = x] − [z = y]`.**
The indicator form needs `DecidableEq X`, which no scheme carries; the three-clause form is
what a consumer can actually supply and is literally the same statement. -/
theorem exists_hom_functionField_ratFunc_of_ord_eq_sub {strX : X ⟶ Spec (CommRingCat.of K)}
    (hproper : IsProper strX) (hcurve : SmoothOfRelativeDimension 1 strX)
    {x y : X} (hxy : x ≠ y)
    (hxdeg : strX.residueDegree x = 1) (hydeg : strX.residueDegree y = 1)
    {f : X.functionField} (hf : f ≠ 0)
    (hordx : Scheme.ord f x = 1) (hordy : Scheme.ord f y = -1)
    (hord0 : ∀ z : X, z ≠ x → z ≠ y → Scheme.ord f z = 0) :
    ∃ φ : X.functionField ⟶ CommRingCat.of (RatFunc K),
      Spec.map φ ≫ X.fromSpecStalk (genericPoint X) ≫ strX
        = Spec.map (CommRingCat.ofHom (algebraMap K (RatFunc K))) :=
  sorry

/-- **THE BRIDGE: a rational function with divisor `[x] − [y]`, `x ≠ y` both `K`-rational,
makes the curve BIRATIONAL OVER `K` TO THE AFFINE LINE** (PROVEN 2026-07-31 over the leaf
immediately above).

This is the geometric conclusion that `birationalOver_affineLine_of_relPicEquiv_sectionIdeal`
(`X0.lean`) needs, in a form that mentions no `RelPicEquiv`, no `sectionIdeal`, no `RelPoint`
and no base scheme `S` — only the divisor of a rational function on the fibre.  What is left
between it and that leaf is the purely sheaf-theoretic step "an isomorphism `𝒪(−x) ≅ 𝒪(−y)`
of invertible sheaves on an integral scheme is multiplication by a rational function whose
divisor is `[x] − [y]`", which is cut as `exists_ord_eq_sub_of_relPicEquiv_sectionIdeal` in
`X0.lean`, beside the definitions it mentions.

The assembly is three named theorems from `BirationalFunctionField.lean`, all sorry-free,
composed exactly as `exists_iso_specFunctionField_affineSpace_of_isDominant` composes them:
two isomorphisms out of the common source `Spec (RatFunc K)` over the common base `Spec K`
compose to an isomorphism of function fields over `Spec K`, which
`birationalOver_of_iso_specFunctionField` turns into `Scheme.BirationalOver`. -/
theorem birationalOver_affineLine_of_ord_eq_sub {n : Type u} [Unique n]
    {strX : X ⟶ Spec (CommRingCat.of K)}
    (hproper : IsProper strX) (hcurve : SmoothOfRelativeDimension 1 strX)
    {x y : X} (hxy : x ≠ y)
    (hxdeg : strX.residueDegree x = 1) (hydeg : strX.residueDegree y = 1)
    {f : X.functionField} (hf : f ≠ 0)
    (hordx : Scheme.ord f x = 1) (hordy : Scheme.ord f y = -1)
    (hord0 : ∀ z : X, z ≠ x → z ≠ y → Scheme.ord f z = 0) :
    Scheme.BirationalOver strX
      (𝔸(n; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
  haveI := hcurve
  haveI : Smooth strX := SmoothOfRelativeDimension.smooth (n := 1) (f := strX)
  obtain ⟨φ, hφ⟩ := exists_hom_functionField_ratFunc_of_ord_eq_sub hproper hcurve hxy
    hxdeg hydeg hf hordx hordy hord0
  obtain ⟨eP, hP⟩ := exists_iso_specRatFunc_specFunctionField_of_hom hcurve φ hφ
  obtain ⟨eA, hA⟩ :=
    exists_iso_specRatFunc_specFunctionField_affineSpace (K := K) (n := n)
  refine birationalOver_of_iso_specFunctionField strX _ (eP.symm ≪≫ eA) ?_
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hA, ← hP, Iso.inv_hom_id_assoc]

end AlgebraicGeometry
