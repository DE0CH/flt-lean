/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Fermat.FLT.Mathlib.AlgebraicGeometry.BirationalFunctionField

/-!
# Divisors and degrees on a smooth proper curve over a field

This file is the DIVISOR/DEGREE LAYER that the degree-`1` Riemann–Roch leaves of
`Fermat/FLT/ModularCurve/X0.lean` are gated on.  At this `Mathlib` pin there is no
Riemann–Roch, no genus, no degree of a divisor and no degree of a morphism of curves —
`grep -rl 'RiemannRoch\|riemannRoch' Mathlib/` returns nothing, and neither `~/cs/FLT` nor
`Fermat/` supplies any of them.  (That survey was re-run 2026-07-31 ON THE HOST THAT OWNS
`.lake`; a `Mathlib` grep run anywhere else silently returns empty, because
`.lake/packages` is a symlink into machine-local `/scratch`, and reads exactly like a
confirmed absence.)

What DOES exist and is what this file is built on:

* `Mathlib/AlgebraicGeometry/OrderOfVanishing.lean` — `AlgebraicGeometry.Scheme.ord
  (f : X.functionField) (z : X) : ℤ`, the order of vanishing of a rational function at a
  point of codimension `1` of a locally Noetherian integral scheme, with `ord_mul`,
  `ord_add` and the DVR-stalk API.  So "the divisor of `f` is `[x] − [y]`" IS sayable at
  this pin, as `∀ z, ord f z = …`, and this file says it that way rather than building a
  `Divisor` type: `Mathlib`'s `AlgebraicCycle` is `Function.locallyFinsupp`, whose local
  finiteness would have to be PROVEN before anything could be stated, and nothing here
  needs the cycle group structure.
* `Mathlib/AlgebraicGeometry/ResidueField.lean` — `Scheme.Hom.residueDegree f x`, the
  degree `[κ(x) : κ(f x)]` of the residue field extension.  Over `S = Spec K` this is the
  DEGREE OF A CLOSED POINT, which is the weight in `deg D = ∑ n_z · [κ(z) : K]`.

## Main definitions

* `AlgebraicGeometry.divDegree strX f` — the degree `∑ᶠ z, ord f z · [κ(z) : K]` of the
  divisor of `f`, as a `finsum` so that it is defined without a prior finiteness proof
  (and is junk `0` when the support is infinite, which `finite_support_ord` rules out).

## Main statements

Two are OPEN LEAVES, both classical, both stated with their own falsity audits:

* `finite_support_ord` — a nonzero rational function on a proper curve has finitely many
  zeros and poles;
* `divDegree_eq_zero` — **`deg (div f) = 0`**, the one identity the whole layer rests on
  (Hartshorne II.6.10, Stichtenoth I.4.11 Cor., Stacks 0BFN/0AYT);
* `exists_hom_functionField_ratFunc_of_ord_eq_sub` — the SHARP form actually needed
  downstream: a function with a single simple pole at a `K`-rational point generates the
  function field, so `K(X) ↪ K(t)`.

and the rest is proven here, including the bridge

* `birationalOver_affineLine_of_ord_eq_sub` — from `div f = [x] − [y]` with `x ≠ y` two
  `K`-rational points, the fibre is `Scheme.BirationalOver` the affine line.

That bridge is what turns `birationalOver_affineLine_of_relPicEquiv_sectionIdeal`
(`X0.lean`) into a purely sheaf-theoretic obligation — "extract the rational function `f`
from the isomorphism `𝒪(−x) ≅ 𝒪(−y)`" — with every field-theoretic and degree-theoretic
step accounted for here.

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
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Elementary `ord` arithmetic missing from `Mathlib` -/

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

@[simp]
lemma ord_one (z : X) : ord (1 : X.functionField) z = 0 := by
  have h := ord_mul (X := X) (x := z) (f := 1) (g := 1) one_ne_zero one_ne_zero
  rw [one_mul] at h
  omega

lemma ord_inv {f : X.functionField} (hf : f ≠ 0) (z : X) : ord f⁻¹ z = - ord f z := by
  have h := ord_mul (X := X) (x := z) (f := f) (g := f⁻¹) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one] at h
  omega

lemma ord_div {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) (z : X) :
    ord (f / g) z = ord f z - ord g z := by
  rw [div_eq_mul_inv, ord_mul hf (inv_ne_zero hg), ord_inv hg]
  omega

end Scheme

/-! ### The degree of the divisor of a rational function -/

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The DEGREE OF THE DIVISOR of a rational function `f` on a scheme `X` over a field `K`:
`deg (div f) = ∑ z, ord_z(f) · [κ(z) : K]`, the sum running over all points (only the
codimension-`1` ones contribute, since `Scheme.ord` is `0` elsewhere by definition).

It is a `finsum`, so it is defined with no prior finiteness proof; when the support is
infinite it is junk `0`.  `finite_support_ord` below says the support IS finite on a proper
curve, which is the hypothesis every lemma about `divDegree` carries. -/
noncomputable def divDegree (strX : X ⟶ Spec (CommRingCat.of K)) (f : X.functionField) : ℤ :=
  ∑ᶠ z : X, Scheme.ord f z * (strX.residueDegree z : ℤ)

lemma divDegree_def (strX : X ⟶ Spec (CommRingCat.of K)) (f : X.functionField) :
    divDegree strX f = ∑ᶠ z : X, Scheme.ord f z * (strX.residueDegree z : ℤ) := rfl

@[simp]
lemma divDegree_one (strX : X ⟶ Spec (CommRingCat.of K)) : divDegree strX 1 = 0 := by
  simp [divDegree]

lemma support_ord_mul_residueDegree_subset (strX : X ⟶ Spec (CommRingCat.of K))
    (f : X.functionField) :
    (Function.support fun z : X => Scheme.ord f z * (strX.residueDegree z : ℤ)) ⊆
      Function.support (Scheme.ord (X := X) f) := by
  intro z hz
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz ⊢
  exact hz.1

/-- The support of the divisor of a nonzero rational function on a PROPER curve over a
field is FINITE (sorry leaf, cut 2026-07-31).

Classical and true: the zero locus of `f` is a closed subset of `X` not containing the
generic point, hence — `X` being an irreducible Noetherian space of dimension `1` — a finite
set of closed points; the same for `f⁻¹`, and `ord f z ≠ 0` forces `z` into one of the two.

**`hproper` IS LOAD-BEARING, and the failure without it is not exotic.**  `X = 𝔸¹_K` is a
smooth integral curve over `K` and `f = 1` has finite support, but take instead the
*locally* Noetherian integral curve obtained as an infinite disjoint union — no: that is not
irreducible.  The honest witness is that properness is used only through
QUASI-COMPACTNESS: on a quasi-compact `X` a proper closed subset of an irreducible
`1`-dimensional space is finite, and on a non-quasi-compact one (an infinite-dimensional
affine line is not available, but `Spec` of a `1`-dimensional non-semilocal ring covered by
infinitely many opens is) the same argument gives only LOCAL finiteness, which is exactly
what `Mathlib`'s `Function.locallyFinsupp` records.  So the statement should be read as
"quasi-compact + dimension `1`", and `IsProper` is the hypothesis the call sites carry.

**`hcurve` IS LOAD-BEARING**: it is what makes `X` one-dimensional.  On a proper surface the
zero locus of `f` is a curve, which has infinitely many codimension-`1` points, and the
support is infinite while remaining locally finite.

**`hf` IS LOAD-BEARING**: `Scheme.ord 0 = 0` by `Mathlib`'s junk convention, so the leaf is
in fact TRUE for `f = 0` as well; `hf` is kept because every consumer has it and because a
proof that does not use it is proving the harder statement for no reason. -/
theorem finite_support_ord {strX : X ⟶ Spec (CommRingCat.of K)}
    (hproper : IsProper strX) (hcurve : SmoothOfRelativeDimension 1 strX)
    {f : X.functionField} (hf : f ≠ 0) :
    (Function.support (Scheme.ord (X := X) f)).Finite :=
  sorry

lemma divDegree_mul {strX : X ⟶ Spec (CommRingCat.of K)}
    (hproper : IsProper strX) (hcurve : SmoothOfRelativeDimension 1 strX)
    {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    divDegree strX (f * g) = divDegree strX f + divDegree strX g := by
  have hfs := ((finite_support_ord hproper hcurve hf).subset
    (support_ord_mul_residueDegree_subset strX f))
  have hgs := ((finite_support_ord hproper hcurve hg).subset
    (support_ord_mul_residueDegree_subset strX g))
  rw [divDegree, divDegree, divDegree, ← finsum_add_distrib hfs hgs]
  refine finsum_congr fun z => ?_
  rw [Scheme.ord_mul hf hg, add_mul]

lemma divDegree_inv {strX : X ⟶ Spec (CommRingCat.of K)}
    {f : X.functionField} (hf : f ≠ 0) :
    divDegree strX f⁻¹ = - divDegree strX f := by
  rw [divDegree, divDegree, ← finsum_neg_distrib]
  refine finsum_congr fun z => ?_
  rw [Scheme.ord_inv hf, neg_mul]

/-- **THE DEGREE OF A PRINCIPAL DIVISOR IS ZERO** (sorry leaf, cut 2026-07-31) — the one
identity the whole divisor/degree layer rests on, and the reason this file exists.

Hartshorne II.6.10; Stichtenoth, *Algebraic Function Fields and Codes*, Cor. I.4.12 (from
Thm. I.4.11, `[F : K(f)] = deg (f)_∞`); Stacks 0AYT/0BFN in the form "for a proper
`1`-dimensional scheme over a field, the degree of the divisor of a rational function is
zero".

**IT IS TRUE, AND HERE IS THE CLASSICAL PROOF THIS `sorry` IS A PROMISE OF.**  `f` gives a
finite morphism `X ⟶ ℙ¹_K` (finite because `X` is proper and the fibres are finite), and
`deg (f^{-1}(0)) = deg (f^{-1}(∞)) = [K(X) : K(f)]` — the fundamental identity
`∑_i e_i f_i = n` for the two Dedekind rings `K[f]` and `K[1/f]` and their integral closures
in `K(X)`, which at this pin is `Ideal.sum_ramification_inertia`
(`Mathlib/NumberTheory/RamificationInertia`).  Subtracting the two gives `deg (div f) = 0`.
A prover who prefers to stay inside `Mathlib` may take the function-field route instead and
never mention `ℙ¹`, which does not exist as a scheme at this pin: `K(X)/K(f)` is a finite
extension, `K[f]` is a PID, the integral closure `A` of `K[f]` in `K(X)` is Dedekind and
finite over `K[f]` (Krull–Akizuki, or separability plus `IsIntegralClosure.isNoetherian`),
the closed points of `X` at which `f` is regular correspond to the maximal ideals of `A`,
and `Scheme.ord` at such a point is the `A`-adic valuation.

**`hproper` IS LOAD-BEARING, WITH AN EXPLICIT COUNTEREXAMPLE.**  On `X = 𝔸¹_K` — smooth,
integral, geometrically connected, of relative dimension `1`, and NOT proper — the function
`f = t` has `div f = [0]`, of degree `1 ≠ 0`.  So a proof that does not consume `hproper` is
wrong.  This is the standard failure: the degree of a principal divisor measures exactly the
points that have been thrown away by non-properness.

**`hcurve` IS LOAD-BEARING**: without dimension `1` the sum is over codimension-`1` points of
a higher-dimensional scheme and `Scheme.ord`'s DVR hypotheses fail at non-regular points; the
identity as stated is then not even well-posed, since `finite_support_ord` fails and
`divDegree` collapses to its junk value.

**IT DOES NOT NEED GEOMETRIC CONNECTEDNESS**, and deliberately does not assume it: for
`K = ℝ` and `X` a smooth proper curve over `ℂ`, viewed over `ℝ` through the étale map
`Spec ℂ ⟶ Spec ℝ`, every residue degree doubles and the identity survives.  `IsIntegral X`
is what is really used, and it is an instance hypothesis so that this statement stands on
its own; at the call sites it comes from
`isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`.

**NOT VACUOUS**: `X = 𝔸¹_K` compactified — or, entirely inside this development, any fibre of
a smooth proper curve — satisfies the hypotheses, and `divDegree strX f` is a nonconstant
function of `f` in general (it is `0` for every `f` by this very statement, but the
UNRESTRICTED `∑ᶠ z, n_z · [κ(z) : K]` obviously is not, which is what makes this a theorem
rather than a definitional identity). -/
theorem divDegree_eq_zero_curve {strX : X ⟶ Spec (CommRingCat.of K)}
    (hproper : IsProper strX) (hcurve : SmoothOfRelativeDimension 1 strX)
    {f : X.functionField} (hf : f ≠ 0) :
    divDegree strX f = 0 :=
  sorry

/-! ### Reading off the degree of a divisor supported at two points -/

lemma divDegree_of_ord_eq_sub {strX : X ⟶ Spec (CommRingCat.of K)}
    {x y : X} (hxy : x ≠ y) {f : X.functionField}
    (hordx : Scheme.ord f x = 1) (hordy : Scheme.ord f y = -1)
    (hord0 : ∀ z : X, z ≠ x → z ≠ y → Scheme.ord f z = 0) :
    divDegree strX f = (strX.residueDegree x : ℤ) - (strX.residueDegree y : ℤ) := by
  classical
  have hsupp : (Function.support fun z : X => Scheme.ord f z * (strX.residueDegree z : ℤ)) ⊆
      ↑({x, y} : Finset X) := by
    intro z hz
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
    by_contra hmem
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hmem
    exact hz.1 (hord0 z (fun h' => hmem (Or.inl h')) (fun h' => hmem (Or.inr h')))
  rw [divDegree, finsum_eq_finsetSum_of_support_subset _ hsupp, Finset.sum_pair hxy]
  simp only [hordx, hordy]
  ring

/-- Two `K`-rational points whose difference is a principal divisor on a smooth proper curve
have the same degree — the first consequence of `divDegree_eq_zero`, and the reason the
`residueDegree` hypothesis on `x` in `exists_hom_functionField_ratFunc_of_ord_eq_sub` below
is REDUNDANT rather than an extra obligation on a prover. -/
lemma residueDegree_eq_of_ord_eq_sub {strX : X ⟶ Spec (CommRingCat.of K)}
    (hproper : IsProper strX) (hcurve : SmoothOfRelativeDimension 1 strX)
    {x y : X} (hxy : x ≠ y) {f : X.functionField} (hf : f ≠ 0)
    (hordx : Scheme.ord f x = 1) (hordy : Scheme.ord f y = -1)
    (hord0 : ∀ z : X, z ≠ x → z ≠ y → Scheme.ord f z = 0) :
    strX.residueDegree x = strX.residueDegree y := by
  have h := divDegree_of_ord_eq_sub (strX := strX) hxy hordx hordy hord0
  rw [divDegree_eq_zero_curve hproper hcurve hf] at h
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
divisor is `[x] − [y]`", which belongs in `X0.lean` beside the definitions it mentions.

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
