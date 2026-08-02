/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Modularity.AbelianScheme
public import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveAffineComplement
public import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveExtension
public import Fermat.FLT.Mathlib.AlgebraicGeometry.ProperPushforward
public import Fermat.FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothReduced
-- `AlgebraicGeometry.Scheme.ord`, the order of vanishing at a codimension-one point of a
-- locally Noetherian integral scheme, together with `ord_mul`, `ord_add`, `ord_zero`.  This
-- is the ONE mathlib file the construction below runs on, and until this module it was
-- imported nowhere in `Fermat/`.
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# The pole order at the zero section of a genus-one curve, as a `def`

`Fermat/FLT/ModularCurve/EllipticScheme.lean` needs, for the reverse Riemann–Roch bridge, a
pole-order function on the affine complement `Spec R = A ∖ {O}` of the zero section of an
abelian scheme `A` of relative dimension one over a field `K`.  Its leaf
`exists_poleOrderValuation_of_affineComplement` asked for that function EXISTENTIALLY,
together with nine clauses.

**This module builds the function as an actual `def` and proves the clauses that are pure
valuation theory, leaving three named leaves.**  Doing it as a `def` is what makes the split
legal at all, and that is worth stating because it is the trap the previous owner recorded:
the valuation clauses do NOT pin the function — `deg' = 2 · deg` satisfies `hzero`, `hmul`,
`hconst`, `hdesc`, `htop` and `hone` — so a standalone leaf of the form "for ANY such `deg`,
`∃ x, deg x = 2`" is **FALSE**.  Once `deg` is `-ord_O` on the nose, the genus clauses can be
stated about *that* function and are true.

## What is proven here

* `Fermat.PoleOrder.poleOrd` — the pole order `-ord_O`, as an integer-valued function on the
  chart, built from `AlgebraicGeometry.Scheme.ord` through the embedding
  `chartToFunctionField` of the chart's coordinate ring into `A.functionField`;
* `poleOrd_zero`, `poleOrd_one`, `poleOrd_mul` (multiplicativity) and `poleOrd_add_le`
  (the ultrametric inequality, which is what makes `{r | deg r ≤ n}` a submodule);
* the geometric prerequisites, each of independent interest:
  `not_isField_stalk_of_ne_genericPoint` (mathlib-shaped: on an integral scheme the stalk at
  a point other than the generic point is not a field), `isDiscreteValuationRing_stalk_of_`
  `ne_genericPoint` and `coheight_eq_one_of_ne_genericPoint`;
* `exists_poleOrderValuation_of_affineComplement'`, the full nine-clause conclusion of the
  original leaf, over the three residual leaves below.

## The three residual leaves

1. `nonneg_poleOrd_and_eq_zero_iff` — **`Γ(A, 𝒪_A) = K`.**  A chart function with no pole at
   `O` extends to a global section of a proper geometrically connected geometrically reduced
   `K`-scheme, hence is constant.  This is the clause that makes `deg` land in `ℕ` at all and
   is simultaneously `hconst`.
2. `exists_sub_smul_poleOrd_lt` — **the residue field of `𝒪_{A,O}` is `K`.**  `r / s` is a
   unit of the DVR `𝒪_{A,O}`; `c` is its residue.  This is where `O` being a *section* rather
   than an arbitrary closed point is spent.
3. `isEmpty_algEquivPolynomial_chart` — **the affine complement is not the affine line**
   (genus `≥ 1`), cut 2026-08-02 out of leaf 3 below and containing no pole order at all.
4. `exists_poleOrd_eq_two_and_three` — **some function has a double pole and some a triple
   pole** (genus `≤ 1`, i.e. Riemann's inequality at `n = 2, 3`).

`poleOrd_ne_one_and_exists_two_three` — the old leaf 3, "the genus is one" — is PROVEN over
3 and 4 as of 2026-08-02, with its name and statement unchanged, so nothing below it moved.

Leaf 1 is a properness/descent statement, leaf 2 a residue-field statement; 3 and 4 are the
two halves of the genus and share no technique.

**THE ABSENCE CLAIM THAT USED TO STAND HERE WAS STALE AND IS CORRECTED** (2026-08-02).  It
read "there is still no Riemann–Roch, genus or divisor theory in `Fermat/`, in the mathlib
pin or in `~/cs/FLT` (re-checked 2026-07-31)".  The mathlib and `~/cs/FLT` halves still hold.
The `Fermat/` half is FALSE: `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveGenus.lean` carries
`rrSet`, `ell`, `divisorDegree`, `IsDivisorOn`, `IsCurveGenus` (Riemann's theorem) with
`IsCurveGenus.unique` PROVEN and `exists_isCurveGenus` as its single leaf, and
`CurveDivisorDegree.lean` / `PrincipalDivisorDegree.lean` carry the degree of a principal
divisor.  Neither is imported here, and both import only mathlib, so either may be imported
at no cost in build order.  Leaf 4's docstring gives the route through them **and the trap in
it** (`IsCurveGenus` bounds nothing, so it cannot be read off at `n = 2, 3`).  Separately,
leaf 3's mathematics is PROVEN in this tree already, DOWNSTREAM, as
`exists_section_of_affineLine_toAbelianScheme` in `ModularCurve/X0.lean`; leaf 3 is blocked by
import order, and its docstring gives the hoist.

Leaves 1 and 2 are each reachable with tooling this tree already owns
(`AlgebraicGeometry.isIso_appTop_of_isProper_over_field` in `ProperPushforward.lean` for the
first, `Scheme.Hom.stalkClosedPointTo` and the section lemmas of `CurveAffineComplement.lean`
for the second) and are left open here only for want of time, not for want of a route.

## Accounting

**The direct-sorry count goes 1 → 3 (2026-07-31) → 4 (2026-08-02), and that is disclosure
rather than regression.**  What changed at the first cut is that the ~300 lines of
valuation-theoretic plumbing between `Scheme.ord` and the nine clauses — the embedding of the
chart in the function field, the DVR at `O`, the ultrametric inequality, the submodule, the
`ℤ`-to-`ℕ` normalisation — can never have to be written again; what changed at the second is
that the two halves of the genus were separated and the `≥` half was reduced, over ~90 lines
of proven algebra, to a statement about `R` alone that the tree already proves downstream.
Each of the four survivors is a statement with a name in a textbook.
Judged by CLAUDE.md's own tie-breaker ("what is LEFT in the leaf, not how many leaves"), this
is the cut: the old leaf mixed properness, residue fields and the genus into one existential
that no single citation could discharge.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

noncomputable section

namespace Fermat.PoleOrder

variable {K : Type} [Field K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)}

/-! ### The zero section and the point it picks out -/

/-- The zero section of an abelian scheme over a field, as a morphism `Spec K ⟶ A`. -/
def zeroSection (ab : AbelianSchemeStruct f) : Spec (CommRingCat.of K) ⟶ A :=
  (ab.zero (𝟙 (Spec (CommRingCat.of K)))).1

lemma zeroSection_comp (ab : AbelianSchemeStruct f) : zeroSection ab ≫ f = 𝟙 _ :=
  (ab.zero (𝟙 (Spec (CommRingCat.of K)))).2

/-- The point of `A` underlying the zero section: `Spec K` is a one-point space, so the
section has a single point in its range and this is it. -/
def zeroPoint (ab : AbelianSchemeStruct f) : A :=
  (zeroSection ab).base (IsLocalRing.closedPoint K)

lemma range_zeroSection_base (ab : AbelianSchemeStruct f) :
    Set.range (zeroSection ab).base = {zeroPoint ab} := by
  haveI : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  ext y
  simp only [Set.mem_range, Set.mem_singleton_iff, zeroPoint]
  constructor
  · rintro ⟨w, rfl⟩
    exact congrArg _ (Subsingleton.elim w _)
  · rintro rfl
    exact ⟨_, rfl⟩

/-! ### The curve, its integrality, and the DVR at a non-generic point -/

section Curve

variable [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]

omit [IsProper f] in
include f in
/-- A smooth proper geometrically connected curve over a field is an integral scheme.  This
is `isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected` with the connectedness
read off the instance rather than passed by hand. -/
lemma isIntegral_of_abelianScheme : IsIntegral A :=
  isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected (n := 1) f inferInstance

omit [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] in
/-- The zero section of a separated morphism has closed range, and its range is a point. -/
lemma isClosed_zeroPoint (ab : AbelianSchemeStruct f) : IsClosed ({zeroPoint ab} : Set A) :=
  isClosed_singleton_of_section (zeroSection_comp ab) (range_zeroSection_base ab)

end Curve

section Stalk

variable [IsIntegral A]

/-- **On an integral scheme the stalk at a point other than the generic point is not a
field.**

`ringKrullDim_stalk_eq_coheight` turns the stalk's Krull dimension into `Order.coheight`, a
field has dimension zero, and `Order.coheight_eq_zero` then says the point is maximal in the
specialization order.  The generic point specializes to every point, so a maximal point IS
the generic point (the space is `T0`, being sober).

Mathlib has the converse — `isField_stalk_of_closure_mem_irreducibleComponents` — and not
this direction; it is stated here in mathlib-facing form and is the input to the DVR lemma
below. -/
lemma not_isField_stalk_of_ne_genericPoint {x : A} (hx : x ≠ genericPoint A) :
    ¬ IsField (A.presheaf.stalk x) := by
  intro h
  have hco : Order.coheight x = 0 := by
    have h1 := ringKrullDim_stalk_eq_coheight (X := A) x
    rw [ringKrullDim_eq_zero_of_isField h] at h1
    exact_mod_cast h1.symm
  have hmax : IsMax x := Order.coheight_eq_zero.mp hco
  have h1 : x ≤ genericPoint A := (genericPoint_spec A).specializes trivial
  have h2 : genericPoint A ≤ x := hmax h1
  exact hx (Specializes.antisymm h2 h1).eq

end Stalk

section Dvr

variable [SmoothOfRelativeDimension 1 f] [IsIntegral A]

include f in
/-- **Every local ring of a smooth curve at a non-generic point is a discrete valuation
ring.**  This is `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` with its
`¬ IsField` hypothesis discharged by the lemma above. -/
lemma isDiscreteValuationRing_stalk_of_ne_genericPoint {x : A} (hx : x ≠ genericPoint A) :
    IsDiscreteValuationRing (A.presheaf.stalk x) :=
  isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one f
    (not_isField_stalk_of_ne_genericPoint hx)

include f in
/-- **A non-generic point of a smooth curve has coheight one** — the hypothesis
`AlgebraicGeometry.Scheme.ord_mul` needs, and the reason `ord` is not junk at `O`. -/
lemma coheight_eq_one_of_ne_genericPoint {x : A} (hx : x ≠ genericPoint A) :
    Order.coheight x = 1 := by
  haveI := isDiscreteValuationRing_stalk_of_ne_genericPoint (f := f) hx
  have h1 := ringKrullDim_stalk_eq_coheight (X := A) x
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
  exact_mod_cast h1.symm

end Dvr

/-! ### `0 ≤ ord` says exactly that the function lies in the stalk

The three lemmas here are about `AlgebraicGeometry.Scheme.ord` alone — no curve, no abelian
scheme, no chart.  They are what converts the numerical hypothesis `0 ≤ ord_x g` into the
statement a gluing argument needs, namely that `g` is in the image of `𝒪_{X,x}` inside
`K(X)`.  Mathlib has the two halves separately (`Ring.ordFrac_ge_one_of_ne_zero` and
`Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing`) and not the combination.
-/

section OrdStalk

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **A nonzero element of the stalk has non-negative order of vanishing at that point.**
This is `Ring.ordFrac_ge_one_of_ne_zero` read through `Scheme.le_ord_iff`: the `1` there is
the `0` here, `ℤᵐ⁰` being written multiplicatively. -/
lemma zero_le_ord_algebraMap {x : X} (hx : Order.coheight x = 1)
    {a : X.presheaf.stalk x} (ha : a ≠ 0) :
    0 ≤ Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hne : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
    fun hc => ha (by
      have := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      exact this (by simpa using hc))
  rw [Scheme.le_ord_iff hx hne]
  have := Ring.ordFrac_ge_one_of_ne_zero (R := X.presheaf.stalk x) (K := X.functionField) ha
  simp [Scheme.ordHom] at this ⊢
  exact this

/-- `ord 1 = 0`, which `Scheme.ord_mul` gives with no hypothesis on the point at all. -/
lemma ord_one_eq_zero (x : X) : Scheme.ord (1 : X.functionField) x = 0 := by
  have h := Scheme.ord_mul (X := X) (x := x) (f := 1) (g := 1) one_ne_zero one_ne_zero
  rw [one_mul] at h
  omega

/-- **`0 ≤ ord_x g` says exactly that `g` lies in the stalk at `x`.**

At a point whose stalk is a discrete valuation ring, `ValuationRing.isInteger_or_isInteger`
gives `g` or `g⁻¹` in `𝒪_{X,x}`.  In the second case `ord g + ord g⁻¹ = ord 1 = 0` while
both summands are `≥ 0` (the second by `zero_le_ord_algebraMap`), so both vanish, so the
preimage of `g⁻¹` is a UNIT of the DVR
(`Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing`) and `g` is the image of its
inverse.  `hx` is load-bearing: at a point of coheight `≠ 1`, `ord` is identically `0` and
the hypothesis says nothing. -/
lemma exists_algebraMap_eq_of_ord_nonneg {x : X} (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {g : X.functionField} (hg : g ≠ 0) (h : 0 ≤ Scheme.ord g x) :
    ∃ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a = g := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk x) g with hi | hi
  · obtain ⟨a, ha⟩ := hi
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hi
  have hginv : g⁻¹ ≠ 0 := inv_ne_zero hg
  have ha0 : a ≠ 0 := by
    intro hc
    rw [hc, map_zero] at ha
    exact hginv ha.symm
  have h2 : Scheme.ord g x + Scheme.ord g⁻¹ x = 0 := by
    have hm := Scheme.ord_mul (X := X) (x := x) hg hginv
    rw [mul_inv_cancel₀ hg, ord_one_eq_zero] at hm
    omega
  have h3 : 0 ≤ Scheme.ord g⁻¹ x := ha ▸ zero_le_ord_algebraMap hx ha0
  have h4 : Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
    rw [ha]; omega
  have hne : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 := by
    rw [ha]; exact hginv
  have hu : IsUnit a := by
    rw [Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := X.functionField)]
    have := (Scheme.ord_eq_iff hx hne (n := 0)).mp h4
    simpa [Scheme.ordHom] using this
  refine ⟨(hu.unit⁻¹ : (X.presheaf.stalk x)ˣ), ?_⟩
  have hprod : a * ((hu.unit⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) = 1 := by
    simp
  have := congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hprod
  rw [map_mul, map_one, ha] at this
  field_simp at this
  exact this

end OrdStalk

/-! ### The chart's coordinate ring inside the function field -/

section Chart

variable {R : Type} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ A) [IsOpenImmersion ι]
  [IsIntegral A]

/-- **The chart's coordinate ring, embedded in the function field of `A`.**

`ι` is an open immersion, so `Scheme.Hom.appIso` identifies `Γ(A, ι ''ᵁ ⊤)` with
`Γ(Spec R, ⊤) ≃ R`, and the germ at the generic point takes that to `A.functionField`.  The
membership `hgen` is passed as a proof argument rather than as a `Nonempty` instance, so that
nothing has to be synthesized at the use sites. -/
def chartToFunctionField
    (hgen : genericPoint A ∈ ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) :
    CommRingCat.of R ⟶ A.functionField :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (ι.appIso ⊤).inv ≫
    A.presheaf.germ (ι ''ᵁ ⊤) (genericPoint A) hgen

lemma chartToFunctionField_injective
    (hgen : genericPoint A ∈ ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) :
    Function.Injective ⇑(chartToFunctionField ι hgen).hom := by
  have h1 := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  have h2 := (ConcreteCategory.bijective_of_isIso (ι.appIso ⊤).inv).1
  have h3 := germ_injective_of_isIntegral A (U := ι ''ᵁ ⊤) (genericPoint A) hgen
  intro a b hab
  simp only [chartToFunctionField, ConcreteCategory.comp_apply] at hab
  exact h1 (h2 (h3 hab))

end Chart

/-! ### The pole order -/

section PoleOrd

variable [IsIntegral A] [IsLocallyNoetherian A]
  {R : Type} [CommRing R] (ι : Spec (CommRingCat.of R) ⟶ A) [IsOpenImmersion ι]
  (hgen : genericPoint A ∈ ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) (O : A)

/-- **The pole order at `O` of an element of an affine chart**, as an integer: minus the
order of vanishing at `O` of the corresponding element of the function field.

This is the object the original existential leaf was asking for, made into a `def` so that
the residual genus statements can be about *it* rather than about an arbitrary function
satisfying the valuation clauses (which they cannot be — see the module docstring). -/
def poleOrd (r : R) : ℤ := - Scheme.ord ((chartToFunctionField ι hgen).hom r) O

omit [IsLocallyNoetherian A] in
lemma chart_ne_zero {r : R} (hr : r ≠ 0) : (chartToFunctionField ι hgen).hom r ≠ 0 := by
  intro h
  exact hr (chartToFunctionField_injective ι hgen (by simpa using h))

@[simp] lemma poleOrd_zero : poleOrd ι hgen O 0 = 0 := by
  simp [poleOrd]

/-- **Multiplicativity of the pole order**, i.e. `Scheme.ord_mul`.  Note this needs no
hypothesis on `O` beyond what `ord` itself demands: at a point of coheight `≠ 1`, `ord` is
identically zero and the identity is `0 = 0 + 0`. -/
lemma poleOrd_mul {r s : R} (hr : r ≠ 0) (hs : s ≠ 0) :
    poleOrd ι hgen O (r * s) = poleOrd ι hgen O r + poleOrd ι hgen O s := by
  simp only [poleOrd, map_mul]
  rw [Scheme.ord_mul (chart_ne_zero ι hgen hr) (chart_ne_zero ι hgen hs)]
  ring

@[simp] lemma poleOrd_one : poleOrd ι hgen O 1 = 0 := by
  rcases subsingleton_or_nontrivial R with h | h
  · rw [Subsingleton.elim (1 : R) 0]; simp
  · have h := poleOrd_mul ι hgen O (r := 1) (s := 1) one_ne_zero one_ne_zero
    simp only [mul_one] at h
    omega

include f in
/-- **The ultrametric inequality.**  This is the clause that makes `{r | poleOrd r ≤ n}` a
submodule, and it is the one place the DVR at `O` is used: `Scheme.ord_add` is stated for a
point whose stalk is a discrete valuation ring. -/
lemma poleOrd_add_le [SmoothOfRelativeDimension 1 f] (hO : O ≠ genericPoint A)
    {r s : R} (hrs : r + s ≠ 0) :
    poleOrd ι hgen O (r + s) ≤ max (poleOrd ι hgen O r) (poleOrd ι hgen O s) := by
  haveI := isDiscreteValuationRing_stalk_of_ne_genericPoint (f := f) hO
  have h := Scheme.ord_add (X := A) (x := O)
    (f := (chartToFunctionField ι hgen).hom r) (g := (chartToFunctionField ι hgen).hom s)
    (by simpa using chart_ne_zero ι hgen hrs)
  simp only [poleOrd, map_add]
  omega

end PoleOrd

/-! ### `Scheme.ord` against `Ring.ord`: the discrete-valuation dictionary

`AlgebraicGeometry.Scheme.ord` is defined through `Ring.ordFrac (X.presheaf.stalk z)`, and
`Ring.ordFrac` in turn through `Ring.ord` — the LENGTH of `R ⧸ (x)` — so at a point whose
stalk is a discrete valuation ring the scheme-level order of vanishing and the ring-level one
agree.  Mathlib does not state that comparison, and it is what lets a statement about
`poleOrd` be attacked with `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`.

The three ring-level lemmas below are pure commutative algebra about a DVR; the fourth is the
bridge.  Together they say: on a smooth curve, the elements of `𝒪_{A,O}` of `Scheme.ord` zero
are exactly the units, and those of positive `Scheme.ord` are exactly the maximal ideal. -/

section DvrOrd

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

/-- **`Ring.ord` of `u * ϖ ^ n` in a discrete valuation ring is `n`.**  This is what makes
`Ring.ord` computable against `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`. -/
lemma ringOrd_unit_mul_pow {ϖ : S} (hϖ : Irreducible ϖ) (u : Sˣ) (n : ℕ) :
    Ring.ord S ((u : S) * ϖ ^ n) = n := by
  rw [Ring.ord_mul_of_isUnit_left u.isUnit,
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) n,
    Ring.ord_of_irreducible hϖ]
  simp

/-- **Two nonzero elements of a DVR with the same `Ring.ord` differ by a unit.** -/
lemma exists_unit_mul_of_ringOrd_eq {a b : S} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Ring.ord S a = Ring.ord S b) : ∃ u : Sˣ, a = (u : S) * b := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨m, u₁, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n, u₂, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  rw [ringOrd_unit_mul_pow hϖ, ringOrd_unit_mul_pow hϖ] at h
  have hmn : m = n := by exact_mod_cast h
  subst hmn
  refine ⟨u₁ * u₂⁻¹, ?_⟩
  rw [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]

/-- **An element of the maximal ideal of a DVR has `Ring.ord` at least one.** -/
lemma one_le_ringOrd_of_mem_maximalIdeal {z : S} (hz : z ∈ IsLocalRing.maximalIdeal S) :
    1 ≤ Ring.ord S z := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hdvd : ϖ ∣ z := by
    have hspan : IsLocalRing.maximalIdeal S = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
    rw [hspan, Ideal.mem_span_singleton] at hz
    exact hz
  calc (1 : ℕ∞) = Ring.ord S ϖ := (Ring.ord_of_irreducible hϖ).symm
    _ ≤ Ring.ord S z := Ring.ord_le_ord_of_dvd hdvd

end DvrOrd

section OrdBridge

variable [IsIntegral A] [IsLocallyNoetherian A] {O : A}

/-- **`Scheme.ord` of the image of a stalk element in the function field is its `Ring.ord`.**

`Scheme.ordHom O hO` is `Ring.ordFrac (A.presheaf.stalk O)` on the nose — the `haveI` inside
mathlib's definition supplies a `Prop`, so proof irrelevance makes the two `rfl`-equal and one
`show` crosses the gap.  After that it is `Ring.ordFrac_eq_ord` and
`Ring.ordMonoidWithZeroHom_eq_coe`.  Note that no discrete-valuation hypothesis is needed: only
`coheight O = 1`, which is what makes `ord` non-junk at `O`. -/
lemma schemeOrd_algebraMap (hO : Order.coheight O = 1) {x : A.presheaf.stalk O} (hx : x ≠ 0)
    {n : ℕ} (hn : Ring.ord (A.presheaf.stalk O) x = n) :
    Scheme.ord (algebraMap (A.presheaf.stalk O) A.functionField x) O = n := by
  haveI : Ring.KrullDimLE 1 (A.presheaf.stalk O) := krullDimLE_of_coheight_le hO.le
  have hne : algebraMap (A.presheaf.stalk O) A.functionField x ≠ 0 := fun h =>
    hx (IsFractionRing.injective (A.presheaf.stalk O) A.functionField (by simpa using h))
  rw [Scheme.ord_eq_iff hO hne]
  show Ring.ordFrac (A.presheaf.stalk O) _ = _
  rw [Ring.ordFrac_eq_ord _ hx]
  exact Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hx) hn

end OrdBridge

/-! ### Locating the generic point inside the chart -/

section Assembly

variable [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
  [IsIntegral A] [IsLocallyNoetherian A] (ab : AbelianSchemeStruct f)
  {R : Type} [CommRing R] [Algebra K R] (ι : Spec (CommRingCat.of R) ⟶ A) [IsOpenImmersion ι]

omit [IsProper f] [GeometricallyConnected f] [IsIntegral A] [IsLocallyNoetherian A] in
include f in
/-- The complement of the zero section is nonempty: a nonempty smooth curve over a field has
infinitely many points (`infinite_of_smoothOfRelativeDimension_one`), and the zero section
supplies the nonemptiness. -/
lemma compl_zeroPoint_nonempty : ({zeroPoint ab}ᶜ : Set A).Nonempty := by
  haveI : Nonempty A := ⟨zeroPoint ab⟩
  haveI := infinite_of_smoothOfRelativeDimension_one f
  exact ((Set.finite_singleton (zeroPoint ab)).infinite_compl).nonempty

omit [GeometricallyConnected f] [IsLocallyNoetherian A] in
include f in
/-- The generic point is not the zero section's point: it lies in every nonempty open, and
the complement of the zero section is a nonempty open. -/
lemma genericPoint_ne_zeroPoint : genericPoint A ≠ zeroPoint ab := by
  have hop : IsOpen ({zeroPoint ab}ᶜ : Set A) := (isClosed_zeroPoint ab).isOpen_compl
  have hm : genericPoint A ∈ ({zeroPoint ab}ᶜ : Set A) :=
    ((genericPoint_spec A).mem_open_set_iff hop).mpr
      (by simpa using compl_zeroPoint_nonempty (f := f) ab)
  simpa using hm

omit [GeometricallyConnected f] [IsLocallyNoetherian A] [Algebra K R] in
include f in
/-- The hypothesis `chartToFunctionField` needs, read off the range hypothesis of the leaf. -/
lemma genericPoint_mem_chart
    (hrange : Set.range ι.base =
      (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of K)))).1.base)ᶜ) :
    genericPoint A ∈ ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := by
  have h1 : (ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) : Set A) = Set.range ι.base := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    rfl
  show genericPoint A ∈ (ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) : Set A)
  rw [h1, hrange, show (ab.zero (𝟙 (Spec (CommRingCat.of K)))).1 = zeroSection ab from rfl,
    range_zeroSection_base ab]
  simpa using genericPoint_ne_zeroPoint (f := f) ab

/-! ### The three residual leaves -/

section Leaves

variable (hstr : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K R)))
  (hrange : Set.range ι.base =
    (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of K)))).1.base)ᶜ)
  (hgen : genericPoint A ∈ ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens))

/-! #### The chart's `K`-algebra structure, read in the function field

`hstr` says the chart lies over `Spec K` through `algebraMap K R`.  What the constants
argument needs is that same statement transported into `A.functionField`: the composite
`K → R → K(A)` is the composite `K → Γ(A, ⊤) → K(A)`.  That is `chart_comp_algebraMap`, and
the two lemmas above it are the open-immersion bookkeeping it runs on. -/

omit [IsIntegral A] [IsLocallyNoetherian A] in
/-- Restricting a global section to the chart and then comparing along the open immersion is
`ι.appTop`.  `Scheme.Hom.map_appLE` does the work; `appLE_top_top_eq_appTop` is the
`ι ⁻¹ᵁ ⊤ = ⊤` bookkeeping. -/
lemma res_comp_appIso_hom :
    A.presheaf.map
        (homOfLE (le_top : (ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) ≤ ⊤)).op
      ≫ (ι.appIso ⊤).hom = ι.appTop := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  exact appLE_top_top_eq_appTop ι _

omit [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
  [IsIntegral A] [IsLocallyNoetherian A] in
include f hstr in
/-- **`hstr`, read on global sections.**  A constant of `K`, viewed as a global section of `A`
through the structure morphism and then restricted to the chart, is its image under
`algebraMap K R`.  This is the ONLY place `hstr` is consumed, and it is what makes the two
`K`-algebra structures on the function field — through `Γ(A, ⊤)` and through `R` — agree. -/
@[reassoc]
theorem constSec_res_eq :
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫
        A.presheaf.map (homOfLE (le_top : ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op
      = CommRingCat.ofHom (algebraMap K R) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (ι.appIso ⊤).inv := by
  rw [← cancel_mono (ι.appIso ⊤).hom]
  rw [Category.assoc, Category.assoc, res_comp_appIso_hom ι, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← Scheme.Hom.comp_appTop, hstr, appTop_Spec_map,
    Category.assoc, Iso.inv_hom_id_assoc]

omit [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
  [IsLocallyNoetherian A] in
include f hstr in
/-- **THE RESIDUE FIELD AT THE ZERO SECTION IS `K`** (PROVEN 2026-08-02).

`O = zeroPoint ab` is the image of a SECTION of `f`, so `f` and `zeroSection ab` induce a
retraction `K → 𝒪_{A,O} → K`; the second map is
`AlgebraicGeometry.Scheme.stalkClosedPointTo (zeroSection ab)` and the first is a constant
global section germinated at `O`.  That the first map is COMPATIBLE with the `K`-algebra
structure of the chart — i.e. that `algebraMap S F ∘ ιK` is `φ ∘ algebraMap K R` — is `hstr`,
and the comparison runs through `Γ(A, ⊤)`: both the stalk at `O` and the function field
receive the global sections, and `Scheme.algebraMap_germ_eq_germToFunctionField` identifies
the two routes.  There is no direct map between the two stalks to argue with.

`ιK` is only a ring hom, not an `Algebra` instance, because nothing downstream needs one and
installing one would create a second `Algebra K (A.presheaf.stalk O)` in scope. -/
theorem exists_residueSection_zeroPoint :
    ∃ (ιK : K →+* A.presheaf.stalk (zeroPoint ab))
      (ρ : A.presheaf.stalk (zeroPoint ab) →+* K),
      (∀ c : K, ρ (ιK c) = c) ∧
      (∀ c : K, algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField (ιK c)
        = (chartToFunctionField ι hgen).hom (algebraMap K R c)) := by
  have key1 : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫
      A.presheaf.germ ⊤ (zeroPoint ab) trivial) ≫
      Scheme.stalkClosedPointTo (zeroSection ab) = 𝟙 (CommRingCat.of K) := by
    simp only [zeroPoint]
    rw [Category.assoc, Category.assoc,
      Scheme.germ_stalkClosedPointTo (zeroSection ab) ⊤ trivial]
    have h2 : f.appTop ≫ (zeroSection ab).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
      rw [← Category.assoc, ← Scheme.Hom.comp_appTop, zeroSection_comp]
      simp
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op]
    rw [Scheme.Hom.app_eq_appLE (zeroSection ab), Scheme.Hom.appLE_map_assoc,
      appLE_top_top_eq_appTop, h2, Iso.inv_hom_id]
  have key2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫
      A.presheaf.germ ⊤ (genericPoint A) trivial =
      CommRingCat.ofHom (algebraMap K R) ≫ chartToFunctionField ι hgen := by
    rw [chartToFunctionField, ← TopCat.Presheaf.germ_res A.presheaf
      (homOfLE (le_top : ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)) (genericPoint A) hgen,
      constSec_res_eq_assoc ι hstr]
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫
      A.presheaf.germ ⊤ (zeroPoint ab) trivial).hom,
    (Scheme.stalkClosedPointTo (zeroSection ab)).hom, fun c => ?_, fun c => ?_⟩
  · exact congrArg (fun m : CommRingCat.of K ⟶ CommRingCat.of K => m.hom c) key1
  · have h := congrArg (fun m : CommRingCat.of K ⟶ A.functionField => m.hom c) key2
    simpa using h

omit [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
  [IsIntegral A] [IsLocallyNoetherian A] in
include f hstr in
/-- **`hstr` at the level of global sections**: `algebraMap K R`, read through the chart's
identification of `Γ(Spec R, ⊤)` with `Γ(A, ι ''ᵁ ⊤)`, is `f.appTop` followed by
restriction. -/
lemma chartStruct_key :
    CommRingCat.ofHom (algebraMap K R) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv
        ≫ (ι.appIso ⊤).inv
      = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop
        ≫ A.presheaf.map
            (homOfLE (le_top : (ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) ≤ ⊤)).op := by
  rw [← cancel_mono (ι.appIso (⊤ : (Spec (CommRingCat.of R)).Opens)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, res_comp_appIso_hom ι]
  rw [← Scheme.Hom.comp_appTop, hstr, appTop_Spec_map]
  simp

omit [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
  [IsLocallyNoetherian A] in
include f hstr in
/-- **The chart's `K`-algebra structure is the restriction of the global one**, read in the
function field: `K → R → K(A)` equals `K → Γ(A, ⊤) → K(A)`.  Both the non-negativity and the
constants half of `nonneg_poleOrd_and_eq_zero_iff` are applications of this. -/
lemma chart_comp_algebraMap :
    CommRingCat.ofHom (algebraMap K R) ≫ chartToFunctionField ι hgen
      = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop
        ≫ A.presheaf.germ ⊤ (genericPoint A) trivial := by
  have hres := A.presheaf.germ_res
    (homOfLE (le_top : (ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) ≤ ⊤)) (genericPoint A) hgen
  calc CommRingCat.ofHom (algebraMap K R) ≫ chartToFunctionField ι hgen
      = (CommRingCat.ofHom (algebraMap K R) ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv
          ≫ (ι.appIso ⊤).inv) ≫ A.presheaf.germ (ι ''ᵁ ⊤) (genericPoint A) hgen := by
        rw [chartToFunctionField]; simp only [Category.assoc]
    _ = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫ A.presheaf.map
          (homOfLE (le_top : (ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) ≤ ⊤)).op)
          ≫ A.presheaf.germ (ι ''ᵁ ⊤) (genericPoint A) hgen := by
        rw [chartStruct_key ι hstr]
    _ = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop
          ≫ A.presheaf.germ ⊤ (genericPoint A) trivial := by
        simp only [Category.assoc, hres]

omit [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] [IsIntegral A]
  [IsLocallyNoetherian A] [Algebra K R] in
include f hrange in
/-- Every point other than the zero section's lies in the chart — this is `hrange`, with
`range_zeroSection_base` computing the right-hand side. -/
lemma mem_chart_of_ne_zeroPoint {x : A} (hx : x ≠ zeroPoint ab) :
    x ∈ ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := by
  have h1 : (ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) : Set A) = Set.range ι.base := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    rfl
  show x ∈ (ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) : Set A)
  rw [h1, hrange, show (ab.zero (𝟙 (Spec (CommRingCat.of K)))).1 = zeroSection ab from rfl,
    range_zeroSection_base ab]
  simpa using hx

omit [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] in
include f hstr in
/-- **A nonzero constant has order of vanishing zero at the zero section.**  It is a global
section and a unit there, so `Scheme.ord_of_isUnit` applies at `U = ⊤`; `hstr` is what makes
the constant global in the first place. -/
lemma ord_chart_algebraMap (c : K) (hc : c ≠ 0) :
    Scheme.ord ((chartToFunctionField ι hgen).hom (algebraMap K R c)) (zeroPoint ab) = 0 := by
  haveI : Nonempty (⊤ : A.Opens) := ⟨⟨genericPoint A, trivial⟩⟩
  have hcomp := congrArg (fun φ => φ.hom c) (chart_comp_algebraMap ι hstr hgen)
  simp only [ConcreteCategory.comp_apply] at hcomp
  have hu : IsUnit (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) :=
    ((isUnit_iff_ne_zero.mpr hc).map
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).map f.appTop.hom
  have := Scheme.ord_of_isUnit (X := A) (U := ⊤) hu (x := zeroPoint ab) trivial
  rw [← hcomp] at this
  exact this

omit [GeometricallyConnected f] [Algebra K R] in
include f hrange in
/-- **THE GLUING STEP** — a chart function with `0 ≤ ord_O` extends to a GLOBAL section.

This is where the cut differs from the route the leaf's docstring prescribed, and it is
shorter: instead of gluing two sections with `exists_res_eq_of_germ_eq` and
`exists_glue_of_agree`, feed `exists_germToFunctionField_eq_of_forall_isInteger` at `U = ⊤`.
That lemma asks only for a stalk element over `φ r` at EVERY point, and there are exactly two
kinds of point — the ones in the chart, where the germ of `r`'s own section does it, and the
zero section, where `exists_algebraMap_eq_of_ord_nonneg` does it off the hypothesis.  No
overlap, no cocycle, no second open. -/
lemma exists_global_of_ord_nonneg (r : R)
    (h : 0 ≤ Scheme.ord ((chartToFunctionField ι hgen).hom r) (zeroPoint ab)) :
    ∃ s : Γ(A, ⊤), (A.presheaf.germ ⊤ (genericPoint A) trivial).hom s
      = (chartToFunctionField ι hgen).hom r := by
  haveI : Nonempty (⊤ : A.Opens) := ⟨⟨genericPoint A, trivial⟩⟩
  haveI hne : Nonempty (ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) := ⟨⟨genericPoint A, hgen⟩⟩
  have hOne : zeroPoint ab ≠ genericPoint A := fun hq =>
    genericPoint_ne_zeroPoint (f := f) ab hq.symm
  haveI := isDiscreteValuationRing_stalk_of_ne_genericPoint (f := f) hOne
  have hco := coheight_eq_one_of_ne_genericPoint (f := f) hOne
  set sr : Γ(A, ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    (ι.appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) with hsrdef
  have hsr : A.germToFunctionField (ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) sr
      = (chartToFunctionField ι hgen).hom r := by
    simp [hsrdef, chartToFunctionField]
  have hloc : ∀ x ∈ (⊤ : A.Opens), ∃ a : A.presheaf.stalk x,
      algebraMap (A.presheaf.stalk x) A.functionField a
        = (chartToFunctionField ι hgen).hom r := by
    intro x _
    rcases eq_or_ne r 0 with rfl | hr
    · exact ⟨0, by simp [map_zero]⟩
    rcases eq_or_ne x (zeroPoint ab) with rfl | hx
    · exact exists_algebraMap_eq_of_ord_nonneg hco (chart_ne_zero ι hgen hr) h
    · have hxU := mem_chart_of_ne_zeroPoint ab ι hrange hx
      refine ⟨A.presheaf.germ (ι ''ᵁ ⊤) x hxU sr, ?_⟩
      rw [Scheme.algebraMap_germ_eq_germToFunctionField A hxU sr]
      exact hsr
  obtain ⟨s, hs⟩ := exists_germToFunctionField_eq_of_forall_isInteger (X := A) ⊤
    ((chartToFunctionField ι hgen).hom r) hloc
  exact ⟨s, hs⟩

include f hstr hrange in
/-- **`Γ(A, 𝒪_A) = K`, in the form the pole order needs**: a chart function regular at the
zero section is a constant.  The global section produced by `exists_global_of_ord_nonneg` is
in the image of `f.appTop`, which is an isomorphism by
`isIso_appTop_of_isProper_over_field` — `GeometricallyReduced f` coming from smoothness
through `GeometricallyReduced.of_smooth` — and `chart_comp_algebraMap` identifies its
preimage with the constant we want. -/
lemma mem_range_of_ord_nonneg (r : R)
    (h : 0 ≤ Scheme.ord ((chartToFunctionField ι hgen).hom r) (zeroPoint ab)) :
    r ∈ Set.range (algebraMap K R) := by
  haveI : Nonempty (⊤ : A.Opens) := ⟨⟨genericPoint A, trivial⟩⟩
  obtain ⟨s, hs⟩ := exists_global_of_ord_nonneg ab ι hrange hgen r h
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (n := 1) (f := f)
  haveI : GeometricallyReduced f := GeometricallyReduced.of_smooth f
  haveI : IsIso f.appTop := isIso_appTop_of_isProper_over_field (Field.toIsField K) f
  obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso f.appTop).2 s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom t, ?_⟩
  have hcomp := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom t))
    (chart_comp_algebraMap ι hstr hgen)
  simp only [ConcreteCategory.comp_apply] at hcomp
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom t) = t := by
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id]
    rfl
  rw [hinv, ht, hs] at hcomp
  exact chartToFunctionField_injective ι hgen hcomp

include f hstr hrange in
/-- **LEAF 1 — `Γ(A, 𝒪_A) = K`, in the form the pole order needs** (cut 2026-07-31 out of
`exists_poleOrderValuation_of_affineComplement`; **PROVEN 2026-08-02**).

A chart function `r` with `poleOrd r < 0` — that is, with `ord_O r > 0` — is regular
everywhere on `A ∖ {O}` (it is a section there) and lies in the stalk at `O`, hence glues to
a GLOBAL section of `A`; and a chart function with `poleOrd r = 0` is a global section too.
`A` is proper, geometrically connected and geometrically reduced over `K`, so its global
sections are exactly `K` — this is `AlgebraicGeometry.isIso_appTop_of_isProper_over_field`
in `Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean`, which is PROVEN.  Hence
`poleOrd r ≥ 0` always, and `poleOrd r = 0` exactly for the constants.

**THE ROUTE TAKEN, and where it differs from the one this docstring used to prescribe.**
Step 1 and step 3 are as recorded; step 2 is not, and the recorded version is the expensive
one.

1. `0 ≤ ord_O (φ r)` gives an element of `A.presheaf.stalk O` over `φ r` —
   `exists_algebraMap_eq_of_ord_nonneg` above, off the DVR at `O`
   (`isDiscreteValuationRing_stalk_of_ne_genericPoint`) and `Ring.ordFrac`'s own API;
2. **NOT a two-open gluing.**  The recorded route was to glue a section on `U = A ∖ {O}`
   against one defined near `O` with `AlgebraicGeometry.exists_res_eq_of_germ_eq` and
   `AlgebraicGeometry.exists_glue_of_agree`, which needs the overlap and the agreement
   there.  `AlgebraicGeometry.exists_germToFunctionField_eq_of_forall_isInteger` in the same
   file does the whole thing at `U = ⊤` from a purely POINTWISE hypothesis — a stalk element
   over `φ r` at every point — and there are exactly two kinds of point, the ones in the
   chart (germ of `r`'s own section) and `O` (step 1).  See `exists_global_of_ord_nonneg`;
3. `isIso_appTop_of_isProper_over_field (Field.toIsField K) f`, with `GeometricallyReduced f`
   supplied by `GeometricallyReduced.of_smooth f` and `Smooth f` by
   `SmoothOfRelativeDimension.smooth`.  Transporting the resulting constant back to the
   chart is `chart_comp_algebraMap`, which is where `hstr` is spent.

The other direction of the `iff`, and the non-negativity, are both
`ord_chart_algebraMap`: a nonzero constant is a global unit, so `Scheme.ord_of_isUnit` at
`U = ⊤` gives it order zero.  Non-negativity is then a contradiction — if `ord_O (φ r) > 0`
then `r` is a constant by the above, and a nonzero constant has `ord_O = 0`.

**FAITHFULNESS.**  `hrange` is load-bearing exactly as the parent leaf's audit says: with two
points removed instead of one, a function with poles only at the second point has
`poleOrd_O = 0` without being constant.  `hstr` is load-bearing because
`Set.range (algebraMap K R)` has to BE the constants: over a base with a twisted `K`-algebra
structure (`K = ℚ(t)` acting through `t ↦ t²`) the range is a proper subfield of the constant
field and the statement is false, and the parent's audit gives that witness in full.

**NOT VACUOUS**: at the Weierstrass chart of an elliptic curve, `poleOrd (x^i y^j) = 2i + 3j`
and the constants are exactly the elements of `poleOrd` zero. -/
theorem nonneg_poleOrd_and_eq_zero_iff (r : R) (hr : r ≠ 0) :
    0 ≤ poleOrd ι hgen (zeroPoint ab) r ∧
      (poleOrd ι hgen (zeroPoint ab) r = 0 ↔ r ∈ Set.range (algebraMap K R)) := by
  have hback : ∀ c : K, algebraMap K R c = r → poleOrd ι hgen (zeroPoint ab) r = 0 := by
    intro c hcr
    have hc : c ≠ 0 := by rintro rfl; exact hr (by rw [← hcr, map_zero])
    have := ord_chart_algebraMap ab ι hstr hgen c hc
    rw [hcr] at this
    simp [poleOrd, this]
  refine ⟨?_, ?_, ?_⟩
  · by_contra hcon
    simp only [not_le] at hcon
    have h0 : 0 ≤ Scheme.ord ((chartToFunctionField ι hgen).hom r) (zeroPoint ab) := by
      simp only [poleOrd] at hcon; omega
    obtain ⟨c, hcr⟩ := mem_range_of_ord_nonneg ab ι hstr hrange hgen r h0
    have := hback c hcr
    omega
  · intro h0
    refine mem_range_of_ord_nonneg ab ι hstr hrange hgen r ?_
    simp only [poleOrd] at h0
    omega
  · rintro ⟨c, hcr⟩
    exact hback c hcr

-- `hrange` is not consumed by the proof below (`hgen`, which is what the argument needs, is a
-- hypothesis of this section), and neither is `GeometricallyConnected f`.  Both are kept in the
-- signature because the sorried version carried them and the call site in
-- `exists_poleOrderValuation_of_affineComplement'` passes `hrange` positionally; dropping it
-- would be a signature change for no gain.
set_option linter.unusedSectionVars false in
include f hstr hrange in
/-- **LEAF 2 — the residue field of `𝒪_{A,O}` is `K`, in the form the pole order needs**
(cut 2026-07-31 out of `exists_poleOrderValuation_of_affineComplement`;
**PROVEN 2026-08-02, no sorry**).

Two chart functions with the SAME pole order at `O` differ, after scaling the second by a
constant of `K`, by a function of strictly smaller pole order.  This is not a dimension count
and not the genus: `φ r / φ s` has `ord_O = 0`, so it is a unit of the discrete valuation ring
`𝒪_{A,O}`, and `c` is its residue.  What the statement asserts is precisely that the residue
can be taken IN `K` — i.e. that the residue field at `O` is `K` and not a proper extension —
and that is true because `O = zeroPoint ab` is the image of a SECTION of `f`, hence a
`K`-rational point.

**THE ROUTE AS TAKEN**, which is the one the cut predicted, in four steps:

1. `exists_residueSection_zeroPoint` above: the section `zeroSection ab` gives a retraction
   `ιK : K → 𝒪_{A,O}`, `ρ : 𝒪_{A,O} → K` with `ρ ∘ ιK = id`, compatible with `φ`.  Since `ρ`
   is then surjective onto a field, `ker ρ` is maximal, hence IS `𝔪_O`
   (`IsLocalRing.ker_eq_maximalIdeal`) — so no `IsLocalHom` bookkeeping is needed;
2. `Scheme.ord (φ r / φ s) = 0`, so writing `φ r / φ s = a / b` with `a, b ∈ 𝒪_{A,O}` and
   passing to `Ring.ord` through `schemeOrd_algebraMap` gives `Ring.ord a = Ring.ord b`,
   whence `a = u · b` for a UNIT `u` (`exists_unit_mul_of_ringOrd_eq`).  So `φ r = u · φ s`;
3. `c := ρ u`, and `z := u - ιK c` lies in `𝔪_O`, so `1 ≤ Ring.ord z`
   (`one_le_ringOrd_of_mem_maximalIdeal`) and hence `1 ≤ Scheme.ord z`;
4. `φ (r - c • s) = z · φ s`, so its `Scheme.ord` exceeds that of `φ s = φ r` by at least one.
   The degenerate case `z = 0` is not an exception: then `r - c • s = 0`, `poleOrd` of it is
   `0`, and `h1` says `0 < poleOrd r`.

Note `h1` is used ONLY for that degenerate case, and `hrange` is not used at all (`hgen`,
which is what the argument needs, is a hypothesis of the section); both are kept because the
call site holds them and dropping either would be a signature change.

**FAITHFULNESS.**  Without `hstr` — i.e. with the `K`-algebra structure on `R` restricted
along a proper subfield `K₀ ⊂ K` — the statement is FALSE: each graded piece
`L n / L (n-1)` becomes `[K : K₀]`-dimensional and no single `c ∈ K₀` can cancel the leading
term.  That is the parent audit's `hdesc` witness, and it transfers verbatim because the
conclusion here is the parent's `hdesc` clause with `deg` replaced by `poleOrd`.  In the proof
`hstr` enters exactly once, at `constSec_res_eq`. -/
theorem exists_sub_smul_poleOrd_lt (r s : R) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrs : poleOrd ι hgen (zeroPoint ab) r = poleOrd ι hgen (zeroPoint ab) s)
    (h1 : 1 ≤ poleOrd ι hgen (zeroPoint ab) r) :
    ∃ c : K, poleOrd ι hgen (zeroPoint ab) (r - c • s) <
      poleOrd ι hgen (zeroPoint ab) r := by
  obtain ⟨ιK, ρ, hsec, hcompat⟩ := exists_residueSection_zeroPoint ab ι hstr hgen
  have hOne : zeroPoint ab ≠ genericPoint A := (genericPoint_ne_zeroPoint (f := f) ab).symm
  have hcoh : Order.coheight (zeroPoint ab) = 1 :=
    coheight_eq_one_of_ne_genericPoint (f := f) hOne
  haveI hdvr : IsDiscreteValuationRing (A.presheaf.stalk (zeroPoint ab)) :=
    isDiscreteValuationRing_stalk_of_ne_genericPoint (f := f) hOne
  haveI hkd : Ring.KrullDimLE 1 (A.presheaf.stalk (zeroPoint ab)) :=
    krullDimLE_of_coheight_le hcoh.le
  have hx : (chartToFunctionField ι hgen).hom r ≠ 0 := chart_ne_zero ι hgen hr
  have hy : (chartToFunctionField ι hgen).hom s ≠ 0 := chart_ne_zero ι hgen hs
  have hordxy : Scheme.ord ((chartToFunctionField ι hgen).hom r) (zeroPoint ab) =
      Scheme.ord ((chartToFunctionField ι hgen).hom s) (zeroPoint ab) := by
    simp only [poleOrd] at hrs; omega
  -- STEP 2: the ratio has order zero, hence is a unit of the stalk
  have hvne : (chartToFunctionField ι hgen).hom r / (chartToFunctionField ι hgen).hom s ≠ 0 :=
    div_ne_zero hx hy
  have hvy : ((chartToFunctionField ι hgen).hom r / (chartToFunctionField ι hgen).hom s) *
      (chartToFunctionField ι hgen).hom s = (chartToFunctionField ι hgen).hom r :=
    div_mul_cancel₀ _ hy
  have hordv : Scheme.ord ((chartToFunctionField ι hgen).hom r /
      (chartToFunctionField ι hgen).hom s) (zeroPoint ab) = 0 := by
    have h := Scheme.ord_mul (x := zeroPoint ab) hvne hy
    rw [hvy] at h
    omega
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective
    (A := (A.presheaf.stalk (zeroPoint ab) : Type))
    ((chartToFunctionField ι hgen).hom r / (chartToFunctionField ι hgen).hom s)
  have hbne : b ≠ 0 := fun h => by simp [h] at hb
  have hAb : algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField b ≠ 0 := fun h =>
    hbne (IsFractionRing.injective (A.presheaf.stalk (zeroPoint ab)) A.functionField
      (by simpa using h))
  have hane : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact hvne hab.symm
  have hmulab : ((chartToFunctionField ι hgen).hom r / (chartToFunctionField ι hgen).hom s) *
      algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField b =
      algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField a := by
    rw [← hab]; field_simp
  have hordab : Scheme.ord (algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField a)
      (zeroPoint ab) =
      Scheme.ord (algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField b)
        (zeroPoint ab) := by
    rw [← hmulab, Scheme.ord_mul hvne hAb, hordv]; ring
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Ring.ord (A.presheaf.stalk (zeroPoint ab)) a = m :=
    ⟨_, (ENat.ne_top_iff_exists.mp
      (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hane))).choose_spec.symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Ring.ord (A.presheaf.stalk (zeroPoint ab)) b = n :=
    ⟨_, (ENat.ne_top_iff_exists.mp
      (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hbne))).choose_spec.symm⟩
  have hmn : m = n := by
    have h1' := schemeOrd_algebraMap hcoh hane hm
    have h2' := schemeOrd_algebraMap hcoh hbne hn
    rw [h1', h2'] at hordab
    exact_mod_cast hordab
  subst hmn
  obtain ⟨u, hu⟩ := exists_unit_mul_of_ringOrd_eq hane hbne (by rw [hm, hn])
  have hvu : (chartToFunctionField ι hgen).hom r / (chartToFunctionField ι hgen).hom s =
      algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField (u : _) := by
    have hmap : algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField a =
        algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField (u : _) *
          algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField b := by
      rw [← map_mul, ← hu]
    rw [← hmulab] at hmap
    exact mul_right_cancel₀ hAb hmap
  -- STEP 3: the residue, and the resulting element of the maximal ideal
  refine ⟨ρ (u : _), ?_⟩
  have hzker : ρ ((u : A.presheaf.stalk (zeroPoint ab)) - ιK (ρ (u : _))) = 0 := by
    rw [map_sub, hsec]; ring
  have hzmem : (u : A.presheaf.stalk (zeroPoint ab)) - ιK (ρ (u : _)) ∈
      IsLocalRing.maximalIdeal (A.presheaf.stalk (zeroPoint ab)) := by
    rw [← IsLocalRing.ker_eq_maximalIdeal ρ (fun k => ⟨ιK k, hsec k⟩)]
    exact hzker
  -- STEP 4
  have hkey : (chartToFunctionField ι hgen).hom (r - ρ (u : _) • s) =
      algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField
        ((u : A.presheaf.stalk (zeroPoint ab)) - ιK (ρ (u : _))) *
        (chartToFunctionField ι hgen).hom s := by
    rw [map_sub, map_sub, sub_mul, Algebra.smul_def, map_mul, hcompat, ← hvu, hvy]
  rcases eq_or_ne ((u : A.presheaf.stalk (zeroPoint ab)) - ιK (ρ (u : _))) 0 with hz | hz
  · have hzero : (chartToFunctionField ι hgen).hom (r - ρ (u : _) • s) = 0 := by
      rw [hkey, hz, map_zero, zero_mul]
    simp only [poleOrd, hzero, Scheme.ord_zero, Pi.zero_apply]
    simp only [poleOrd] at h1
    omega
  · have hAz : algebraMap (A.presheaf.stalk (zeroPoint ab)) A.functionField
        ((u : A.presheaf.stalk (zeroPoint ab)) - ιK (ρ (u : _))) ≠ 0 := fun h =>
      hz (IsFractionRing.injective (A.presheaf.stalk (zeroPoint ab)) A.functionField
        (by simpa using h))
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Ring.ord (A.presheaf.stalk (zeroPoint ab))
        ((u : A.presheaf.stalk (zeroPoint ab)) - ιK (ρ (u : _))) = k :=
      ⟨_, (ENat.ne_top_iff_exists.mp
        (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hz))).choose_spec.symm⟩
    have hk1 : 1 ≤ k := by
      have hge := one_le_ringOrd_of_mem_maximalIdeal hzmem
      rw [hk] at hge
      exact_mod_cast hge
    have hordz := schemeOrd_algebraMap hcoh hz hk
    have hfin : Scheme.ord ((chartToFunctionField ι hgen).hom (r - ρ (u : _) • s))
        (zeroPoint ab) =
        (k : ℤ) + Scheme.ord ((chartToFunctionField ι hgen).hom s) (zeroPoint ab) := by
      rw [hkey, Scheme.ord_mul hAz hy, hordz]
    simp only [poleOrd] at hrs h1 ⊢
    omega

include f hstr hrange in
/-- Every unit of the chart has pole order zero: its pole order and that of its inverse sum
to zero and both are non-negative by leaf 1. -/
lemma poleOrd_eq_zero_of_isUnit {u : R} (hu : IsUnit u) :
    poleOrd ι hgen (zeroPoint ab) u = 0 := by
  rcases subsingleton_or_nontrivial R with hsub | hnt
  · rw [Subsingleton.elim u 0]; simp
  obtain ⟨v, huv⟩ := hu.exists_right_inv
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := by rintro rfl; simp at huv
  have h := poleOrd_mul ι hgen (zeroPoint ab) hu0 hv0
  rw [huv, poleOrd_one] at h
  have h1 := (nonneg_poleOrd_and_eq_zero_iff ab ι hstr hrange hgen u hu0).1
  have h2 := (nonneg_poleOrd_and_eq_zero_iff ab ι hstr hrange hgen v hv0).1
  omega

include f hstr hrange in
lemma poleOrd_nonneg (r : R) : 0 ≤ poleOrd ι hgen (zeroPoint ab) r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · exact (nonneg_poleOrd_and_eq_zero_iff ab ι hstr hrange hgen r hr).1

include f hstr hrange in
/-- Scaling by a constant of `K` does not increase the pole order. -/
lemma poleOrd_smul_le (c : K) (r : R) :
    poleOrd ι hgen (zeroPoint ab) (c • r) ≤ poleOrd ι hgen (zeroPoint ab) r := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using poleOrd_nonneg ab ι hstr hrange hgen r
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have hnt : Nontrivial R := ⟨⟨r, 0, hr⟩⟩
  have hcu : IsUnit (algebraMap K R c) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap K R)
  have hsd : c • r = algebraMap K R c * r := Algebra.smul_def c r
  rw [hsd, poleOrd_mul ι hgen (zeroPoint ab) hcu.ne_zero hr,
    poleOrd_eq_zero_of_isUnit ab ι hstr hrange hgen hcu, zero_add]

/-! ### The genus, split along the classical `≥` / `≤` line

What was one leaf — "the genus is one" — is here one PROVEN reduction plus two leaves that
share no technique.  The reduction is the `genus ≥ 1` half stripped of every mention of the
pole order: a function with a SIMPLE pole generates the chart as a `K`-algebra, and generates
it FREELY, so a simple pole makes `Spec R` the affine line.  What is left of that half is
`isEmpty_algEquivPolynomial_chart`, a statement about `R` alone. -/

include ι hgen in
/-- **The chart's coordinate ring is a domain**, because `chartToFunctionField` embeds it in
the function field of `A`, which is a field since `A` is integral.  Nontriviality of `R`
comes with it (`Function.Injective.isDomain` derives it from nontriviality of the target). -/
lemma isDomain_chart : IsDomain R :=
  Function.Injective.isDomain (chartToFunctionField ι hgen).hom
    (chartToFunctionField_injective ι hgen)

/-- **The pole order of a power**, `poleOrd (r ^ n) = n · poleOrd r`.  Induction on `n` over
`poleOrd_mul`; the domain hypothesis is what makes `r ^ n ≠ 0` available at each step. -/
lemma poleOrd_pow {r : R} (hr : r ≠ 0) (n : ℕ) (O : A) :
    poleOrd ι hgen O (r ^ n) = n * poleOrd ι hgen O r := by
  haveI := isDomain_chart ι hgen
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, poleOrd_mul ι hgen O (pow_ne_zero n hr) hr, ih]
    push_cast
    ring

include f hstr hrange in
/-- **A FUNCTION WITH A SIMPLE POLE GENERATES THE CHART** (PROVEN 2026-08-02): if
`poleOrd r = 1` then every `s : R` is a polynomial in `r` with coefficients in `K`.

This is the dimension count `L(n) = K · 1 ⊕ K · r ⊕ ⋯ ⊕ K · rⁿ` written without any
`finrank`, and it is the whole of the `genus ≥ 1` half of leaf 3 that does not need new
mathematics.  Strong induction on `(poleOrd s).toNat`, over the two sibling leaves of this
file and nothing else:

* at `0`, leaf 1 (`nonneg_poleOrd_and_eq_zero_iff`) says `s` is a constant;
* at `n + 1`, `poleOrd (r ^ (n+1)) = n + 1 = poleOrd s` by `poleOrd_pow`, so leaf 2
  (`exists_sub_smul_poleOrd_lt`) produces `c : K` with `poleOrd (s - c • r ^ (n+1)) < n + 1`,
  and the inductive hypothesis applies to that difference.

Both leaves are used only through their statements, so this lemma is as strong as they are
and no stronger. -/
lemma mem_adjoin_of_poleOrd_eq_one {r : R} (hr1 : poleOrd ι hgen (zeroPoint ab) r = 1)
    (s : R) : s ∈ Algebra.adjoin K ({r} : Set R) := by
  haveI := isDomain_chart ι hgen
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [poleOrd_zero] at hr1
    exact one_ne_zero hr1.symm
  have hnn := poleOrd_nonneg ab ι hstr hrange hgen
  have key : ∀ n : ℕ, ∀ s : R, (poleOrd ι hgen (zeroPoint ab) s).toNat ≤ n →
      s ∈ Algebra.adjoin K ({r} : Set R) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      rcases eq_or_ne s 0 with rfl | hs0
      · exact Subalgebra.zero_mem _
      have h0 : poleOrd ι hgen (zeroPoint ab) s = 0 := by have := hnn s; omega
      obtain ⟨c, hc⟩ := (nonneg_poleOrd_and_eq_zero_iff ab ι hstr hrange hgen s hs0).2.mp h0
      exact hc ▸ Subalgebra.algebraMap_mem _ c
    | succ n ih =>
      intro s hs
      rcases eq_or_ne s 0 with rfl | hs0
      · exact Subalgebra.zero_mem _
      by_cases hle : (poleOrd ι hgen (zeroPoint ab) s).toNat ≤ n
      · exact ih s hle
      have hval : poleOrd ι hgen (zeroPoint ab) s = (n : ℤ) + 1 := by
        have := hnn s; omega
      have hpow : poleOrd ι hgen (zeroPoint ab) (r ^ (n + 1)) = (n : ℤ) + 1 := by
        rw [poleOrd_pow ι hgen hr0, hr1]; push_cast; ring
      obtain ⟨c, hc⟩ := exists_sub_smul_poleOrd_lt ab ι hstr hrange hgen s (r ^ (n + 1))
        hs0 (pow_ne_zero _ hr0) (by rw [hval, hpow]) (by omega)
      have hmem : s - c • r ^ (n + 1) ∈ Algebra.adjoin K ({r} : Set R) := by
        refine ih _ ?_
        have := hnn (s - c • r ^ (n + 1))
        omega
      have hmem2 : c • r ^ (n + 1) ∈ Algebra.adjoin K ({r} : Set R) := by
        rw [Algebra.smul_def]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c)
          (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton K r) (n + 1))
      have hEq : s = (s - c • r ^ (n + 1)) + c • r ^ (n + 1) := by ring
      rw [hEq]
      exact Subalgebra.add_mem _ hmem hmem2
  exact key _ s le_rfl

include f hstr hrange in
/-- **A function with a simple pole is transcendental over `K`** (PROVEN 2026-08-02).  An
algebraic element of a domain over a field is a unit (`IsIntegral.isUnit`), and a unit has
pole order zero (`poleOrd_eq_zero_of_isUnit`), not one. -/
lemma transcendental_of_poleOrd_eq_one {r : R}
    (hr1 : poleOrd ι hgen (zeroPoint ab) r = 1) : Transcendental K r := by
  haveI := isDomain_chart ι hgen
  intro halg
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [poleOrd_zero] at hr1
    exact one_ne_zero hr1.symm
  have hu : IsUnit r := (IsAlgebraic.isIntegral halg).isUnit hr0
  have h0 := poleOrd_eq_zero_of_isUnit ab ι hstr hrange hgen hu
  omega

include f hstr hrange in
/-- **A SIMPLE POLE MAKES THE CHART A POLYNOMIAL RING** (PROVEN 2026-08-02) — the reduction
that turns the `genus ≥ 1` half of leaf 3 into a statement with no pole order in it.

`Polynomial.aeval r` is surjective by `mem_adjoin_of_poleOrd_eq_one` and injective by
`transcendental_of_poleOrd_eq_one`, so it is an isomorphism of `K`-algebras.  Geometrically:
a simple pole at `O` exhibits `Spec R = A ∖ {O}` as the affine line. -/
lemma nonempty_algEquivPolynomial_of_poleOrd_eq_one {r : R}
    (hr1 : poleOrd ι hgen (zeroPoint ab) r = 1) :
    Nonempty (Polynomial K ≃ₐ[K] R) := by
  have hinj : Function.Injective (Polynomial.aeval r : Polynomial K →ₐ[K] R) :=
    transcendental_iff_injective.mp
      (transcendental_of_poleOrd_eq_one ab ι hstr hrange hgen hr1)
  have hsurj : Function.Surjective (Polynomial.aeval r : Polynomial K →ₐ[K] R) := by
    intro s
    have hm := mem_adjoin_of_poleOrd_eq_one ab ι hstr hrange hgen hr1 s
    rwa [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hm
  exact ⟨AlgEquiv.ofBijective _ ⟨hinj, hsurj⟩⟩

include f hstr hrange in
/-- **LEAF 3a — THE AFFINE COMPLEMENT OF THE ZERO SECTION IS NOT THE AFFINE LINE**, i.e.
*an elliptic curve is not rational* (sorry leaf, cut 2026-08-02 out of
`poleOrd_ne_one_and_exists_two_three`; this is the `genus ≥ 1` half).

**THE MATHEMATICS OF THIS LEAF IS ALREADY PROVEN IN THIS TREE — DOWNSTREAM.**  It is
`Fermat.exists_section_of_affineLine_toAbelianScheme` in `Fermat/FLT/ModularCurve/X0.lean`
(PROVEN 2026-07-28, over `exists_smoothProperCompactification_affineLine`): *every morphism
`𝔸(Unit; Spec K) ⟶ A` over `Spec K` into an abelian scheme factors through a section*, i.e.
is constant.  `X0.lean` imports `EllipticScheme.lean`, which imports this module, so the name
is not available here and this leaf is blocked by DECLARATION/IMPORT ORDER rather than by
mathematics.  **A successor should not re-prove it and should not attack the geometry.**

**THE ROUTE, in the order to take it.**

1. *The hoist.*  Move `exists_section_of_affineLine_toAbelianScheme` (and, if its own cone
   needs it, `exists_unique_extension_of_valuationRing_stalk_of_isOpenImmersion` and
   `valuationRing_stalk_affineLine`) out of `X0.lean` into a module upstream of this one —
   `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean` already holds
   `exists_smoothProperCompactification_affineLine`, which is that proof's own main input, so
   that file (or a new sibling) is the natural destination.  `AbelianSchemeStruct` lives in
   `Fermat/FLT/Modularity/AbelianScheme.lean`, which this module already imports, so the
   statement is expressible there.  Measure the block with `flt-hoistcheck.py` first;
   `X0.lean` is the most contended file in the repository and the move belongs in a commit of
   its own.
2. *The assembly, ~40 lines and needing no geometry.*  Given `e : Polynomial K ≃ₐ[K] R`:
   compose `MvPolynomial.pUnitAlgEquiv K` with `e` to get `MvPolynomial Unit K ≃ₐ[K] R`,
   apply `Spec` to obtain `𝔸(Unit; Spec K) ≅ Spec (CommRingCat.of R)`, and postcompose with
   `ι` to get `Φ : 𝔸(Unit; Spec K) ⟶ A`.  `hstr` is exactly what makes `Φ` a morphism over
   `Spec K`.  Rigidity then gives a section `s` with `Φ = (structure map) ≫ s`, so `Φ`'s image
   is the single point `s(Spec K)` — while `Φ` is a composite of an isomorphism with an open
   immersion, hence INJECTIVE on points, and `𝔸¹_K = Spec K[X]` has at least the two points
   `(0)` and `(X)`.  Contradiction.

**FAITHFULNESS.**  `hstr` is load-bearing: the conclusion is about `R` AS A `K`-ALGEBRA, and
without `hstr` the `Algebra K R` instance need not be the geometric one (the parent's audit's
`K = ℚ(t)`, `t ↦ t²` witness applies verbatim).  `hrange` is NOT needed for truth — the
statement holds for the coordinate ring of ANY nonempty open affine of `A`, since the route
above consumes only that `ι` is an open immersion over `Spec K` — and is retained because
the call site holds it for free and it cannot make a true leaf false.  A prover who wants to
drop it may.  `hgen` is deliberately absent: it is derivable from `hrange`
(`genericPoint_mem_chart`) and nothing in the statement mentions the function field.

**NOT VACUOUS**: at the Weierstrass chart of an elliptic curve, `R = K[x, y]/(y² + ⋯)` needs
two generators as a `K`-algebra, so no such isomorphism exists — which is the statement, and
it is exactly what `poleOrd (x^i y^j) = 2i + 3j` records: `1` is not a value, so no `r`
generates. -/
theorem isEmpty_algEquivPolynomial_chart : IsEmpty (Polynomial K ≃ₐ[K] R) :=
  sorry

include f hstr hrange in
/-- **LEAF 3b — SOME FUNCTION HAS A DOUBLE POLE AND SOME A TRIPLE POLE** (sorry leaf, cut
2026-08-02 out of `poleOrd_ne_one_and_exists_two_three`; this is the `genus ≤ 1` half, and
it is Riemann's inequality).

Unlike leaf 3a this is NOT reducible to anything already in the tree, and the two halves
share no technique: 3a is rigidity, this is a dimension count.

**THE ABSENCE CLAIM ON THE PARENT LEAF WAS STALE, AND THIS IS THE CORRECTION.**  That leaf
said "there is no Riemann–Roch theorem, no genus and no theory of divisors/linear systems in
`Fermat/`, in the mathlib pin or in `~/cs/FLT`; absent from all three as of 2026-07-31".
Re-run 2026-08-02 the mathlib and `~/cs/FLT` halves still hold; the `Fermat/` half is FALSE.
The tree carries

* `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveGenus.lean` — `rrSet` (the Riemann–Roch space),
  `ell` (`ℓ(D)`), `divisorDegree`, `IsDivisorOn`, `pointDivisor`, `IsCurveGenus strX g`
  (Riemann's theorem `ℓ(D) = deg D + 1 − g` for `deg D ≥ B`), `IsCurveGenus.unique` (PROVEN)
  and `exists_isCurveGenus` (Riemann's theorem itself, a leaf);
* `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean` — `divDegree`,
  `divDegree_eq_zero_curve` (`deg div f = 0`, a leaf) and the degree-one machinery;
* `Fermat/FLT/Mathlib/AlgebraicGeometry/PrincipalDivisorDegree.lean` — the zero/pole
  decomposition of a principal divisor.

None of those is imported here, and none of them is upstream of this module by accident:
`CurveGenus.lean` imports only mathlib, so importing it is available at no cost.

**THE ROUTE, AND THE TRAP IN IT.**  Two things are needed and only the second is hard:

1. *`ℓ(n · [O])` counts pole orders*: `ell strX (pointDivisor (zeroPoint ab) n)` equals the
   number of values of `poleOrd` in `[0, n]`.  This is the identification of `rrSet` with
   `{r ∈ R | poleOrd r ≤ n}` — the functions regular away from `O` are exactly the elements
   of `R`, which is `hrange` — together with `Submodule.span = rrSet`, which `CurveGenus.lean`
   flags in `ell`'s own docstring as the expensive step (it needs `algebraMap k K(X)`
   identified with the germ of the structure map at `⊤`).
2. *The genus of an abelian scheme of relative dimension one is `1`.*

**THE TRAP: `IsCurveGenus` GIVES NO BOUND ON `B`, so it cannot be applied at `n = 2, 3`.**
Its own docstring says so ("It gives no bound on `B`, and in particular does not assert
`ℓ(D) = deg D + 1 − g` for `deg D ≥ 2g − 1`").  The argument must therefore go through LARGE
`n`: with `g = 1`, `ℓ(n[O]) = n` for all `n ≥ B`, and `ℓ(n[O])` is the number of values of
`poleOrd` in `[0, n]`, so the value semigroup has exactly ONE gap; leaf 3a says `1` is a gap;
hence the value semigroup is `ℕ ∖ {1}` and `2` and `3` are values.  A prover who tries to
read `ℓ(2[O]) = 2` off `IsCurveGenus` directly will find the hypothesis `B ≤ deg D`
undischargeable.

**FAITHFULNESS.**  `hrange` is load-bearing: it is what makes the elements of `R` the
functions with poles only at `O`, and hence what ties `ℓ(n[O])` to `poleOrd`.  `hstr` is
load-bearing for the same reason it is on leaf 2 — the graded pieces are one-dimensional over
`K` only if the residue field at `O` is `K`.  Note this leaf does NOT need leaf 3a for its
truth; the two are independent, and the gap-counting argument above uses 3a only to identify
WHICH integer the single gap is.

**NOT VACUOUS**: at the Weierstrass chart, `x` and `y` witness the two existentials. -/
theorem exists_poleOrd_eq_two_and_three :
    (∃ x : R, poleOrd ι hgen (zeroPoint ab) x = 2) ∧
      (∃ y : R, poleOrd ι hgen (zeroPoint ab) y = 3) :=
  sorry

include f hstr hrange in
/-- **LEAF 3 — the genus is one** — PROVEN 2026-08-02 over `isEmpty_algEquivPolynomial_chart`
(the `genus ≥ 1` half) and `exists_poleOrd_eq_two_and_three` (the `genus ≤ 1` half).

The statement and the name are unchanged, so
`exists_poleOrderValuation_of_affineComplement'` and everything below it are untouched.
What changed is that the `hone` clause no longer mentions the genus at all: a simple pole
would make `Spec R` the affine line (`nonempty_algEquivPolynomial_of_poleOrd_eq_one`, PROVEN
above), and 3a says it is not.

**ACCOUNTING: the direct-sorry count of this module goes `3 → 4`, and that is the honest
figure.**  One leaf became two, and what was bought is that the two halves are now separately
dispatchable at people who share no technique — 3a is rigidity and its mathematics is
already proven downstream (so it is a HOIST, not a proof), 3b is Riemann's inequality and now
names the file that carries the genus.  Between them sits ~90 lines of proven reduction that
nobody has to write again.  Judged by CLAUDE.md's tie-breaker — what is LEFT in the leaf,
not how many leaves — 3a mentions no pole order, no `Scheme.ord`, no chart embedding and no
`hgen`, and 3b is a citation with a named route. -/
theorem poleOrd_ne_one_and_exists_two_three :
    (∀ r : R, r ≠ 0 → poleOrd ι hgen (zeroPoint ab) r ≠ 1) ∧
      (∃ x : R, poleOrd ι hgen (zeroPoint ab) x = 2) ∧
      (∃ y : R, poleOrd ι hgen (zeroPoint ab) y = 3) := by
  refine ⟨fun r _ hr1 => ?_, (exists_poleOrd_eq_two_and_three ab ι hstr hrange hgen).1,
    (exists_poleOrd_eq_two_and_three ab ι hstr hrange hgen).2⟩
  exact (isEmpty_algEquivPolynomial_chart ab ι hstr hrange).elim
    (nonempty_algEquivPolynomial_of_poleOrd_eq_one ab ι hstr hrange hgen hr1).some


end Leaves

end Assembly

/-! ### The target theorem -/

/-- **RIEMANN–ROCH, IN ELEMENTARY TERMS: the affine complement of the zero section carries a
pole order whose value semigroup is `⟨2, 3⟩`** — PROVEN 2026-07-31 over the three leaves
above, with the pole order being `-ord_O` on the nose.

This is verbatim the conclusion of
`Fermat.exists_poleOrderValuation_of_affineComplement` in
`Fermat/FLT/ModularCurve/EllipticScheme.lean`, which now delegates to it.  Everything between
`AlgebraicGeometry.Scheme.ord` and the nine clauses is discharged here: the embedding of the
chart in the function field, the DVR at `O`, multiplicativity, the ultrametric inequality (so
that `{r | deg r ≤ n}` really is a `K`-submodule), and the normalisation from `ℤ` to `ℕ`.

Two of the nine clauses are in fact REDUNDANT and are proven rather than assumed here, which
is worth recording for whoever next touches the statement: `deg 0 = 0` follows from the
submodule clause (`0 ∈ L 0` forces `deg 0 ≤ 0`), and `⨆ n, L n = ⊤` is automatic for any
`ℕ`-valued `deg` (every `r` lies in `L (deg r)`). -/
theorem exists_poleOrderValuation_of_affineComplement' {K : Type} [Field K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} (ab : AbelianSchemeStruct f)
    (hdim : SmoothOfRelativeDimension 1 f)
    (R : Type) [CommRing R] [Algebra K R] (ι : Spec (CommRingCat.of R) ⟶ A)
    (hopen : IsOpenImmersion ι)
    (hstr : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K R)))
    (hrange : Set.range ι.base =
      (Set.range (ab.zero (𝟙 (Spec (CommRingCat.of K)))).1.base)ᶜ) :
    ∃ (deg : R → ℕ) (L : ℕ → Submodule K R),
      (∀ n : ℕ, (L n : Set R) = {r : R | deg r ≤ n}) ∧
      deg 0 = 0 ∧
      (∀ r s : R, r ≠ 0 → s ≠ 0 → deg (r * s) = deg r + deg s) ∧
      (∀ r : R, r ≠ 0 → (deg r = 0 ↔ r ∈ Set.range (algebraMap K R))) ∧
      (∀ r : R, r ≠ 0 → deg r ≠ 1) ∧
      (∀ r s : R, r ≠ 0 → s ≠ 0 → deg r = deg s → 1 ≤ deg r →
        ∃ c : K, deg (r - c • s) < deg r) ∧
      (∃ x : R, deg x = 2) ∧ (∃ y : R, deg y = 3) ∧
      (⨆ n, L n) = ⊤ := by
  haveI := hdim
  haveI := hopen
  haveI : IsProper f := ab.proper
  haveI : GeometricallyConnected f := ab.connected
  haveI : IsIntegral A := isIntegral_of_abelianScheme (f := f)
  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  have hgen : genericPoint A ∈ ι ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) :=
    genericPoint_mem_chart (f := f) ab ι hrange
  have hOne : zeroPoint ab ≠ genericPoint A := fun h =>
    genericPoint_ne_zeroPoint (f := f) ab h.symm
  have hnn : ∀ r : R, 0 ≤ poleOrd ι hgen (zeroPoint ab) r :=
    poleOrd_nonneg ab ι hstr hrange hgen
  have hmul : ∀ r s : R, r ≠ 0 → s ≠ 0 →
      poleOrd ι hgen (zeroPoint ab) (r * s)
        = poleOrd ι hgen (zeroPoint ab) r + poleOrd ι hgen (zeroPoint ab) s :=
    fun r s hr hs => poleOrd_mul ι hgen (zeroPoint ab) hr hs
  have hadd : ∀ r s : R, r + s ≠ 0 → poleOrd ι hgen (zeroPoint ab) (r + s)
      ≤ max (poleOrd ι hgen (zeroPoint ab) r) (poleOrd ι hgen (zeroPoint ab) s) :=
    fun r s h => poleOrd_add_le (f := f) ι hgen (zeroPoint ab) hOne h
  have hsm : ∀ (c : K) (r : R), poleOrd ι hgen (zeroPoint ab) (c • r)
      ≤ poleOrd ι hgen (zeroPoint ab) r := poleOrd_smul_le ab ι hstr hrange hgen
  have hcst : ∀ r : R, r ≠ 0 →
      (poleOrd ι hgen (zeroPoint ab) r = 0 ↔ r ∈ Set.range (algebraMap K R)) :=
    fun r hr => (nonneg_poleOrd_and_eq_zero_iff ab ι hstr hrange hgen r hr).2
  obtain ⟨hone, ⟨x, hx⟩, ⟨y, hy⟩⟩ :=
    poleOrd_ne_one_and_exists_two_three ab ι hstr hrange hgen
  refine ⟨fun r => (poleOrd ι hgen (zeroPoint ab) r).toNat, fun n =>
    { carrier := {r : R | (poleOrd ι hgen (zeroPoint ab) r).toNat ≤ n}
      add_mem' := ?_
      zero_mem' := ?_
      smul_mem' := ?_ }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rcases eq_or_ne (a + b) 0 with h | h
    · rw [h, poleOrd_zero]; omega
    · have := hadd a b h
      omega
  · show (poleOrd ι hgen (zeroPoint ab) 0).toNat ≤ n
    rw [poleOrd_zero]; omega
  · intro c r hr
    simp only [Set.mem_setOf_eq] at hr ⊢
    have := hsm c r
    have := hnn (c • r)
    omega
  · intro n; rfl
  · show (poleOrd ι hgen (zeroPoint ab) 0).toNat = 0
    rw [poleOrd_zero]; rfl
  · intro r s hr hs
    show (poleOrd ι hgen (zeroPoint ab) (r * s)).toNat
      = (poleOrd ι hgen (zeroPoint ab) r).toNat + (poleOrd ι hgen (zeroPoint ab) s).toNat
    rw [hmul r s hr hs]
    have := hnn r
    have := hnn s
    omega
  · intro r hr
    show (poleOrd ι hgen (zeroPoint ab) r).toNat = 0 ↔ _
    have := hnn r
    rw [← hcst r hr]
    omega
  · intro r hr
    show (poleOrd ι hgen (zeroPoint ab) r).toNat ≠ 1
    have := hone r hr
    have := hnn r
    omega
  · intro r s hr hs hrs h1
    show ∃ c : K, (poleOrd ι hgen (zeroPoint ab) (r - c • s)).toNat
      < (poleOrd ι hgen (zeroPoint ab) r).toNat
    have hrs2 : (poleOrd ι hgen (zeroPoint ab) r).toNat
        = (poleOrd ι hgen (zeroPoint ab) s).toNat := hrs
    have h12 : 1 ≤ (poleOrd ι hgen (zeroPoint ab) r).toNat := h1
    have hr0 := hnn r
    have hs0 := hnn s
    have hrs' : poleOrd ι hgen (zeroPoint ab) r = poleOrd ι hgen (zeroPoint ab) s := by omega
    have h1' : 1 ≤ poleOrd ι hgen (zeroPoint ab) r := by omega
    obtain ⟨c, hc⟩ := exists_sub_smul_poleOrd_lt ab ι hstr hrange hgen r s hr hs hrs' h1'
    exact ⟨c, by have := hnn (r - c • s); omega⟩
  · exact ⟨x, by show (poleOrd ι hgen (zeroPoint ab) x).toNat = 2; omega⟩
  · exact ⟨y, by show (poleOrd ι hgen (zeroPoint ab) y).toNat = 3; omega⟩
  · refine eq_top_iff.mpr fun r _ => ?_
    exact Submodule.mem_iSup_of_mem (poleOrd ι hgen (zeroPoint ab) r).toNat (by
      show (poleOrd ι hgen (zeroPoint ab) r).toNat ≤ (poleOrd ι hgen (zeroPoint ab) r).toNat
      exact le_rfl)

end Fermat.PoleOrder

end
