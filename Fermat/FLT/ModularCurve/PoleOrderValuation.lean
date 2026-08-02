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
* **`nonneg_poleOrd_and_eq_zero_iff` — `Γ(A, 𝒪_A) = K`, PROVEN 2026-08-02**, together with
  the generic valuation-theoretic input it runs on: `zero_le_ord_algebraMap`,
  `ord_one_eq_zero` and `exists_algebraMap_eq_of_ord_nonneg` (`0 ≤ ord_x g` says exactly
  that `g` lies in the stalk at `x`), and the chart-level bookkeeping
  `chart_comp_algebraMap` (the chart's `K`-algebra structure is the restriction of the
  global one, read in the function field);
* `exists_poleOrderValuation_of_affineComplement'`, the full nine-clause conclusion of the
  original leaf, over the two residual leaves below.

## The two residual leaves

1. `exists_sub_smul_poleOrd_lt` — **the residue field of `𝒪_{A,O}` is `K`.**  `r / s` is a
   unit of the DVR `𝒪_{A,O}`; `c` is its residue.  This is where `O` being a *section* rather
   than an arbitrary closed point is spent.
2. `poleOrd_ne_one_and_exists_two_three` — **the genus is one.**  No function has a simple
   pole at `O` (genus `≥ 1`), and some function has a double pole and some a triple pole
   (genus `≤ 1`, i.e. Riemann's inequality at `n = 2, 3`).

Leaf 1 is a residue-field statement, leaf 2 the only genuinely missing mathematics.  There is
still no Riemann–Roch, genus or divisor theory in `Fermat/`, in the mathlib pin or in
`~/cs/FLT` (re-checked 2026-07-31), which is why leaf 2 stands; leaf 1 is reachable with
tooling this tree already owns (`Scheme.Hom.stalkClosedPointTo` and the section lemmas of
`CurveAffineComplement.lean`) and is left open here only for want of time, not for want of a
route.

**What closing the properness leaf cost, and what it says about the recorded route.**  Its
docstring prescribed gluing two sections over `A ∖ {O}` and a neighbourhood of `O`, with
`exists_res_eq_of_germ_eq` and `exists_glue_of_agree`.  That is not the cheap route: the
same file's `exists_germToFunctionField_eq_of_forall_isInteger` produces a section over `⊤`
from a purely POINTWISE hypothesis, so no overlap and no second open ever appears.  The
route note was written before anyone tried, as route notes are; the correction is recorded
on the theorem itself.

## Accounting

**The direct-sorry count went 1 → 3 at the cut and is now 2.**  What the cut changed is that
the ~300 lines of valuation-theoretic plumbing between `Scheme.ord` and the nine clauses —
the embedding of the chart in the function field, the DVR at `O`, the ultrametric
inequality, the submodule, the `ℤ`-to-`ℕ` normalisation — can never have to be written
again, and each survivor is a statement with a name in a textbook.  Judged by CLAUDE.md's
own tie-breaker ("what is LEFT in the leaf, not how many leaves"), that was the cut: the old
leaf mixed properness, residue fields and the genus into one existential that no single
citation could discharge.
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

include f hstr hrange in
/-- **LEAF 2 — the residue field of `𝒪_{A,O}` is `K`, in the form the pole order needs**
(sorry leaf, cut 2026-07-31 out of `exists_poleOrderValuation_of_affineComplement`).

Two chart functions with the SAME pole order at `O` differ, after scaling the second by a
constant of `K`, by a function of strictly smaller pole order.  This is not a dimension count
and not the genus: `φ r / φ s` has `ord_O = 0`, so it is a unit of the discrete valuation ring
`𝒪_{A,O}`, and `c` is its residue.  What the statement asserts is precisely that the residue
can be taken IN `K` — i.e. that the residue field at `O` is `K` and not a proper extension —
and that is true because `O = zeroPoint ab` is the image of a SECTION of `f`, hence a
`K`-rational point.

**THE ROUTE.**  `zeroSection ab ≫ f = 𝟙 _` makes `K → 𝒪_{A,O} → κ(O) → K` the identity, so
`κ(O) = K`; `Scheme.Hom.stalkClosedPointTo` and `AlgebraicGeometry.base_closedPoint_eq_of_`
`mem_range` in `CurveAffineComplement.lean` are the two pieces of plumbing that say so.  Then
`ord_O (φ r - c • φ s) > ord_O (φ s)` because subtracting the residue moves a unit of the DVR
into the maximal ideal.

**FAITHFULNESS.**  Without `hstr` — i.e. with the `K`-algebra structure on `R` restricted
along a proper subfield `K₀ ⊂ K` — the statement is FALSE: each graded piece
`L n / L (n-1)` becomes `[K : K₀]`-dimensional and no single `c ∈ K₀` can cancel the leading
term.  That is the parent audit's `hdesc` witness, and it transfers verbatim because the
conclusion here is the parent's `hdesc` clause with `deg` replaced by `poleOrd`. -/
theorem exists_sub_smul_poleOrd_lt (r s : R) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrs : poleOrd ι hgen (zeroPoint ab) r = poleOrd ι hgen (zeroPoint ab) s)
    (h1 : 1 ≤ poleOrd ι hgen (zeroPoint ab) r) :
    ∃ c : K, poleOrd ι hgen (zeroPoint ab) (r - c • s) < poleOrd ι hgen (zeroPoint ab) r :=
  sorry

include f hstr hrange in
/-- **LEAF 3 — the genus is one** (sorry leaf, cut 2026-07-31 out of
`exists_poleOrderValuation_of_affineComplement`; this is the ONLY one of the three that needs
mathematics the tree does not have).

* `∀ r ≠ 0, poleOrd r ≠ 1` is **genus `≥ 1`**: a function with a simple pole at `O` is a
  degree-one map `A → P¹`, hence an isomorphism, and `P¹` carries no abelian-scheme structure
  (an abelian scheme has translation-invariant, hence trivial, canonical bundle, so
  `2g - 2 = 0`).
* `∃ x, poleOrd x = 2` and `∃ y, poleOrd y = 3` are **genus `≤ 1`**, i.e. Riemann's
  inequality `dim L(n[O]) ≥ n + 1 - g` read at `n = 2` and `n = 3`.

Together with the valuation clauses proven in this file these pin the value semigroup of
`poleOrd` to `⟨2, 3⟩ = ℕ ∖ {1}`, which is what
`Fermat.PoleOrderFiltration.exists_deg_eq` consumes.

**WHY THIS IS STATED ABOUT `poleOrd` AND NOT ABOUT AN ARBITRARY `deg`.**  It has to be.  The
valuation clauses do not pin the function: `2 · poleOrd` satisfies every one of them, and
also `hone`, while satisfying neither existential.  So a leaf quantified over all `deg` with
those clauses would be FALSE, and the whole point of making `poleOrd` a `def` is that this
leaf can name it.  (A scale-invariant substitute exists — "exactly one `n : ℕ` is not a value
of `deg`", the Weierstrass gap theorem — but it is the same mathematics and a worse
statement.)

**WHAT WOULD REFUTE THE "MISSING" DIAGNOSIS**: a Riemann–Roch theorem, a genus, or a theory of
divisors/linear systems on a curve, in `Fermat/`, `.lake/packages/mathlib` or `~/cs/FLT`.
Absent from all three as of 2026-07-31.

**NOT VACUOUS**: at the Weierstrass chart, `x` and `y` witness the two existentials and
`2i + 3j = 1` has no solution in non-negative integers. -/
theorem poleOrd_ne_one_and_exists_two_three :
    (∀ r : R, r ≠ 0 → poleOrd ι hgen (zeroPoint ab) r ≠ 1) ∧
      (∃ x : R, poleOrd ι hgen (zeroPoint ab) x = 2) ∧
      (∃ y : R, poleOrd ι hgen (zeroPoint ab) y = 3) :=
  sorry

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
