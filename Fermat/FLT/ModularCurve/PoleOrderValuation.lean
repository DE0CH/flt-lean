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

include f hstr hrange in
/-- **LEAF 1 — `Γ(A, 𝒪_A) = K`, in the form the pole order needs** (sorry leaf, cut
2026-07-31 out of `exists_poleOrderValuation_of_affineComplement`).

A chart function `r` with `poleOrd r < 0` — that is, with `ord_O r > 0` — is regular
everywhere on `A ∖ {O}` (it is a section there) and lies in the stalk at `O`, hence glues to
a GLOBAL section of `A`; and a chart function with `poleOrd r = 0` is a global section too.
`A` is proper, geometrically connected and geometrically reduced over `K`, so its global
sections are exactly `K` — this is `AlgebraicGeometry.isIso_appTop_of_isProper_over_field`
in `Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean`, which is PROVEN.  Hence
`poleOrd r ≥ 0` always, and `poleOrd r = 0` exactly for the constants.

**THE ROUTE, in the order a prover should take it.**  The three ingredients all exist:

1. `0 ≤ ord_O (φ r)` iff `φ r` lies in the image of `A.presheaf.stalk O` inside
   `A.functionField` — the DVR at `O` is `isDiscreteValuationRing_stalk_of_ne_genericPoint`
   above and the valuation-ring characterisation is `Ring.ordFrac`'s own API in
   `Mathlib/RingTheory/OrderOfVanishing/`;
2. an element of `Γ(A, U)` (`U = A ∖ {O}`) whose germ at the generic point comes from the
   stalk at `O` agrees, on the overlap, with a section defined near `O` — this is
   `AlgebraicGeometry.exists_res_eq_of_germ_eq` in `CurveAffineComplement.lean` — and the two
   glue by `AlgebraicGeometry.exists_glue_of_agree` in the same file, `U` and a neighbourhood
   of `O` covering `A`;
3. `isIso_appTop_of_isProper_over_field (Field.toIsField K) f`, with `GeometricallyReduced f`
   supplied by `GeometricallyReduced.of_smooth f`.

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
      (poleOrd ι hgen (zeroPoint ab) r = 0 ↔ r ∈ Set.range (algebraMap K R)) :=
  sorry

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
