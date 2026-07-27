/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Extension of a morphism over the missing points of a smooth curve

A morphism from a dense open subscheme `Y` of a smooth proper curve `X` over a field into
a **proper** scheme `Z` extends, uniquely, to all of `X`.  Classically this is Hartshorne
I.6.8 / II Ex. 4.5, Stacks `0BXA`: the local rings of `X` at its finitely many missing
points are discrete valuation rings, so the valuative criterion of properness supplies the
missing local pieces, and they glue because `X` is reduced and `Z` separated.

This module exists because **that theorem was independently cut three times** in this
development — as `exists_unique_extension_of_isX0Compactification` over `Spec ℚ`, as
`exists_extension_of_isX0Compactification` over `Spec 𝔽_ℓ`, and implicitly inside
`exists_inverse_of_isX0Compactification` — and because its residue is shared with
`smoothOfRelativeDimension_one_fromNormalization` in `CurveCompactification.lean`.  All four
sites now consume this file.

## What is PROVEN here, and what the honest residue is

`exists_unique_extension_of_valuationRing_stalk` is **proven outright**, with no sorry, from
`Mathlib` alone.  Its single geometric hypothesis is

    ∀ x : X, ValuationRing 𝒪_{X,x}

and everything else — the passage to a rational map, the valuative square, the spreading out
of the local lift, the gluing over the maximal domain of definition, and the uniqueness — is
carried out here.  The proof is worth describing because the earlier "IRREDUCIBLE at this
pin" verdicts on the three consumers were all mis-scoped, and this is why:

1. `partialMapOfOpenImmersion` turns `φ : Y ⟶ Z` into a `Scheme.PartialMap X Z` with domain
   `j.opensRange`, and `f` is its class in `Scheme.RationalMap`.
2. For each `x : X`, `𝒪_{X,x}` is a valuation ring with fraction field `K(X)`
   (`functionField_isFractionRing_of_isIntegral`, free from `Mathlib` for integral `X`), so
   `f.fromFunctionField` together with `Spec 𝒪_{X,x} ⟶ Spec K` is a `ValuativeCommSq` for
   `strZ`, and `IsProper.eq_valuativeCriterion` produces a lift `Spec 𝒪_{X,x} ⟶ Z`.
3. `Scheme.PartialMap.ofFromSpecStalk` **spreads that lift out** to a partial map defined on
   a neighbourhood of `x` — this is the step textbook proofs hand-wave as "spread out and
   glue", and `Mathlib` has it (`SpreadingOut.lean`, via `IsGermInjectiveAt`, which is an
   instance for integral schemes).  Comparing function-field restrictions
   (`RationalMap.eq_of_fromFunctionField_eq`) identifies it with `f`, so `x` lies in
   `f.domain`; hence `f.domain = ⊤`.
4. `RationalMap.toPartialMap` glues the representatives over the maximal domain — this needs
   `IsReduced X` and a separated target — and transporting along `X.topIso` and
   `X.isoOfEq` reads off the morphism `X ⟶ Z`.
5. Uniqueness is `ext_of_isDominant`.

The two facts about `Spec 𝒪_{X,x}` that `Mathlib` was missing and are supplied here are
`Scheme.PartialMap.fromSpecStalkOfMem_specializes` (compatibility of the restriction of a
partial map to `Spec 𝒪_{X,x}` with specialization — this is what identifies the spread-out
lift with `f` at the generic point) and `Scheme.PartialMap.fromSpecStalkOfMem_comp` (that
restriction is a morphism over the base).  Both are `Mathlib`-ready.

## The leaves

Only four things are left open here, and none of them mentions a modular curve.

| leaf | content |
| --- | --- |
| `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` | smooth of relative dimension one over a field ⟹ the local rings away from the generic point are DVRs |
| `smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk` | the CONVERSE over a **perfect** field: DVR local rings ⟹ smooth of relative dimension one |
| `isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected` | smooth over a field + geometrically connected ⟹ integral |
| `infinite_of_smoothOfRelativeDimension_one` | a nonempty smooth proper curve over a field has infinitely many points |

**The first two are the two directions of ONE classical equivalence** ("regular ⟺ smooth
over a perfect field", in dimension one, where regular ⟺ DVR), and it is worth saying so
loudly because the task that produced this file was dispatched on the belief that the two
consumers shared a single *statement*.  They do not: `X0.lean` needs the forward direction
(it HAS smoothness and WANTS DVRs) and `CurveCompactification.lean` needs the backward one
(it HAS normality/DVRs and WANTS smoothness).  They share a file, a docstring and an owner,
which is what "build it once" can mean here; they are not the same theorem.

`Mathlib` has `IsRegularLocalRing` (`Mathlib/RingTheory/RegularLocalRing/Defs.lean` — note
this REFUTES the frequently repeated claim that there is no notion of regularity at this
pin; what is missing is only the link to *smoothness*, and a grep over
`Mathlib/RingTheory/Smooth/` for `IsRegularLocalRing` is indeed empty).  So a prover of
either direction should route through it:

* `IsLocalRing.finrank_CotangentSpace_eq_one_iff` (`DiscreteValuationRing/TFAE.lean`) turns
  `IsDiscreteValuationRing R` into `finrank (ResidueField R) (CotangentSpace R) = 1` for a
  noetherian local domain, and `IsRegularLocalRing.iff_finrank_cotangentSpace` turns
  regularity into `finrank … = ringKrullDim R`.  So in dimension one the two coincide and
  **the whole of both leaves is "smooth over a field ⟺ regular local rings" (Stacks `00TT`,
  `056S`)**, not any dimension theory.
* `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
  (`Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean`) is the differential-side input:
  a standard smooth algebra of relative dimension `n` has free differentials of rank `n`.
* `instance [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] : IsRegularLocalRing R` is
  already there, so the DVR ⟹ regular half is free.

## Relation to the leaves elsewhere in this development

* `Fermat/FLT/ModularCurve/X0.lean` has `isReduced_of_isX0Compactification` and
  `isDominant_of_isX0Compactification`, which have a **separate owner**.  They are the
  `𝔽_ℓ`-shaped specialisations of `isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`
  and of `isDominant_of_finite_compl` below; that file's own docstring asks for exactly this
  hoist ("the mathlib-shaped statement … belongs in `Fermat/FLT/Mathlib/AlgebraicGeometry/`
  beside `CurveCompactification.lean` rather than here").  Their declarations are NOT touched
  here; whoever owns them should re-derive them from this file rather than proving them
  twice.
* `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean` consumes
  `smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk`.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Order

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K]

/-! ### `Mathlib`-ready preliminaries -/

/-- **A scheme separated over a separated base is separated.**

`Mathlib` has `Scheme.IsSeparated` (separatedness over the terminal scheme) and
`IsSeparated f` (relative separatedness) but no lemma converting the second into the first;
`RationalMap.toPartialMap` wants the first, and properness over an affine base is what a
compactification supplies. -/
lemma Scheme.isSeparated_of_isSeparated_over {Z S : Scheme.{u}} (strZ : Z ⟶ S)
    [IsSeparated strZ] [S.IsSeparated] : Z.IsSeparated := by
  refine ⟨?_⟩
  have h : terminal.from Z = strZ ≫ terminal.from S := Subsingleton.elim _ _
  rw [h]
  have : IsSeparated (terminal.from S) := Scheme.IsSeparated.isSeparated_terminal_from
  infer_instance

/-- **Compatibility of `PartialMap.fromSpecStalkOfMem` with specialization.**

If `x ⤳ y` and both lie in the domain of a partial map `f`, the restriction of `f` to
`Spec 𝒪_{X,x}` is the restriction to `Spec 𝒪_{X,y}` composed with the specialization map.
Taking `x` to be the generic point, this is what identifies a partial map spread out from
`Spec 𝒪_{X,y}` with the original rational map. -/
lemma Scheme.PartialMap.fromSpecStalkOfMem_specializes {X Z : Scheme.{u}} (f : X.PartialMap Z)
    {x y : X} (hx : x ∈ f.domain) (hy : y ∈ f.domain) (h : x ⤳ y) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ f.fromSpecStalkOfMem hy =
      f.fromSpecStalkOfMem hx := by
  rw [Scheme.PartialMap.fromSpecStalkOfMem, Scheme.PartialMap.fromSpecStalkOfMem,
    ← Category.assoc]
  congr 1
  rw [← cancel_mono f.domain.ι]
  simp

/-- **A partial map over the base restricts to a map out of `Spec 𝒪ₓ` over the base.** -/
lemma Scheme.PartialMap.fromSpecStalkOfMem_comp {X Z S : Scheme.{u}} (f : X.PartialMap Z)
    {x : X} (hx : x ∈ f.domain) (strX : X ⟶ S) (strZ : Z ⟶ S)
    (h : f.hom ≫ strZ = f.domain.ι ≫ strX) :
    f.fromSpecStalkOfMem hx ≫ strZ = X.fromSpecStalk x ≫ strX := by
  rw [Scheme.PartialMap.fromSpecStalkOfMem, Category.assoc, h, ← Category.assoc]
  simp

/-- **A morphism defined on a dense open subscheme, as a partial map.** -/
noncomputable def partialMapOfOpenImmersion {X Y Z : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] [IsDominant j] (φ : Y ⟶ Z) : X.PartialMap Z where
  domain := j.opensRange
  dense_domain := j.denseRange
  hom := j.isoOpensRange.inv ≫ φ

lemma partialMapOfOpenImmersion_hom_comp {X Y Z S : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] [IsDominant j] (φ : Y ⟶ Z) (strX : X ⟶ S) (strZ : Z ⟶ S)
    (hφ : φ ≫ strZ = j ≫ strX) :
    (partialMapOfOpenImmersion j φ).hom ≫ strZ =
      (partialMapOfOpenImmersion j φ).domain.ι ≫ strX := by
  simp [partialMapOfOpenImmersion, hφ]

/-! ### The extension theorem -/

/-- **A partial map into a proper scheme, out of a scheme all of whose local rings are
valuation rings, is a morphism** (PROVEN — no sorry, from `Mathlib` alone).

This is the whole geometric content of the uniqueness of a smooth compactification, in the
form that carries no curve hypothesis at all: the valuative criterion is applied at every
point of `X` in turn, and what makes that legitimate is exactly that `𝒪_{X,x}` is a valuation
ring with fraction field `K(X)`.

See the module docstring for the five steps.  Note that `X` is NOT assumed to be a curve, to
be proper, or to be of finite type: for a general integral `X` with valuation-ring local
rings the statement is still true and the proof is the same.  The curve hypotheses enter only
through `valuationRing_stalk_of_smoothOfRelativeDimension_one`, which is what supplies
`hval`. -/
theorem exists_unique_extension_of_valuationRing_stalk
    {X Z : Scheme.{u}} {strX : X ⟶ Spec (CommRingCat.of K)}
    {strZ : Z ⟶ Spec (CommRingCat.of K)} [hZ : IsProper strZ] [IsIntegral X]
    (hval : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (p : X.PartialMap Z) (hpc : p.hom ≫ strZ = p.domain.ι ≫ strX) :
    ∃! Φ : X ⟶ Z, Φ ≫ strZ = strX ∧ p.domain.ι ≫ Φ = p.hom := by
  haveI : Z.IsSeparated := Scheme.isSeparated_of_isSeparated_over strZ
  haveI : IsDominant p.domain.ι := _root_.AlgebraicGeometry.Opens.isDominant_ι p.dense_domain
  have hZ' : IsProper strZ := hZ
  rw [IsProper.eq_valuativeCriterion] at hZ'
  have hvc : ValuativeCriterion strZ := hZ'.1.1.1
  set f : X.RationalMap Z := p.toRationalMap with hfdef
  have hff : f.fromFunctionField ≫ strZ = X.fromSpecStalk (genericPoint X) ≫ strX :=
    Scheme.PartialMap.fromSpecStalkOfMem_comp p _ strX strZ hpc
  -- **Step 1**: the domain of definition is everything.
  have hdom : f.domain = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hsp : genericPoint X ⤳ x := (genericPoint_spec X).specializes (Set.mem_univ x)
    let sq : ValuativeCommSq strZ :=
      { R := X.presheaf.stalk x
        commRing := inferInstance
        domain := inferInstance
        valuationRing := hval x
        K := X.functionField
        field := inferInstance
        algebra := inferInstance
        isFractionRing := inferInstance
        i₁ := f.fromFunctionField
        i₂ := X.fromSpecStalk x ≫ strX
        commSq := ⟨by
          rw [hff]
          exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc hsp strX).symm⟩ }
    let L := (hvc sq).some.default
    let l : Spec (X.presheaf.stalk x) ⟶ Z := L.l
    have hl : l ≫ strZ = X.fromSpecStalk x ≫ strX := L.fac_right
    let g : X.PartialMap Z := Scheme.PartialMap.ofFromSpecStalk strX strZ l hl
    have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
    have hgf : g.toRationalMap = f := by
      refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
      show g.fromFunctionField = f.fromFunctionField
      have h1 := Scheme.PartialMap.fromSpecStalkOfMem_specializes g
        (show genericPoint X ∈ g.domain from hsp.mem_open g.domain.2 hxg) hxg hsp
      calc g.fromFunctionField
          = Spec.map (X.presheaf.stalkSpecializes hsp) ≫ g.fromSpecStalkOfMem hxg := h1.symm
        _ = Spec.map (X.presheaf.stalkSpecializes hsp) ≫ l := by
              rw [Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
        _ = f.fromFunctionField := L.fac_left
    exact Scheme.RationalMap.mem_domain.mpr ⟨g, hxg, hgf⟩
  -- **Step 2**: glue over the full domain, and read off the morphism.
  have hq2 : X.homOfLE p.le_domain_toRationalMap ≫ f.toPartialMap.hom = p.hom :=
    p.toPartialMap_toRationalMap_restrict
  have key : (p.domain.ι ≫ X.topIso.inv) ≫ (X.isoOfEq hdom).inv
      = X.homOfLE p.le_domain_toRationalMap := by
    rw [← cancel_mono f.domain.ι]
    simp
    exact (X.homOfLE_ι p.le_domain_toRationalMap).symm
  have hpι : p.domain.ι ≫ (X.topIso.inv ≫ (X.isoOfEq hdom).inv ≫ f.toPartialMap.hom)
      = p.hom := by
    simp only [← Category.assoc]
    rw [key]
    exact hq2
  refine ⟨X.topIso.inv ≫ (X.isoOfEq hdom).inv ≫ f.toPartialMap.hom, ⟨?_, hpι⟩, ?_⟩
  · refine ext_of_isDominant p.domain.ι ?_
    rw [← Category.assoc, hpι, hpc]
  · rintro Φ' ⟨-, h2⟩
    exact ext_of_isDominant p.domain.ι (by rw [h2, hpι])

/-- **The extension theorem, phrased for an open immersion** (PROVEN). -/
theorem exists_unique_extension_of_valuationRing_stalk_of_isOpenImmersion
    {X Y Z : Scheme.{u}} {strX : X ⟶ Spec (CommRingCat.of K)}
    {strZ : Z ⟶ Spec (CommRingCat.of K)} [IsProper strZ] [IsIntegral X]
    (hval : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    {j : Y ⟶ X} [IsOpenImmersion j] [IsDominant j]
    (φ : Y ⟶ Z) (hφ : φ ≫ strZ = j ≫ strX) :
    ∃! Φ : X ⟶ Z, Φ ≫ strZ = strX ∧ j ≫ Φ = φ := by
  obtain ⟨Φ, ⟨h1, h2⟩, huniq⟩ := exists_unique_extension_of_valuationRing_stalk
    (strX := strX) hval (partialMapOfOpenImmersion j φ)
    (partialMapOfOpenImmersion_hom_comp j φ strX strZ hφ)
  have hkey : ∀ Ψ : X ⟶ Z, (j ≫ Ψ = φ) ↔
      ((partialMapOfOpenImmersion j φ).domain.ι ≫ Ψ = (partialMapOfOpenImmersion j φ).hom) := by
    intro Ψ
    show (j ≫ Ψ = φ) ↔ (j.opensRange.ι ≫ Ψ = j.isoOpensRange.inv ≫ φ)
    constructor
    · intro h
      rw [← h, ← Category.assoc]
      simp
    · intro h
      rw [← Scheme.Hom.isoOpensRange_hom_ι j, Category.assoc, h, ← Category.assoc]
      simp
  exact ⟨Φ, ⟨h1, (hkey Φ).mpr h2⟩, fun Φ' hΦ' => huniq Φ' ⟨hΦ'.1, (hkey Φ').mp hΦ'.2⟩⟩

/-! ### The curve inputs -/

/-- **A smooth curve over a field has discrete valuation rings as its local rings away from
the generic point** (sorry leaf — the shared DVR input).

TRUE and classical (Stacks `00TT` for smooth ⟹ regular, `00NP` for regular local of
dimension one ⟹ DVR).  A smooth morphism is Zariski-locally standard smooth, and a standard
smooth algebra over a field is regular; relative dimension `1` over a field makes every
non-generic local ring one-dimensional, and a regular local ring of dimension one is a
discrete valuation ring.

**`¬ IsField 𝒪_{X,x}` is exactly the right form of "`x` is not the generic point".**  At the
generic point of an integral `X` the stalk IS the function field, so it is a field and
`IsDiscreteValuationRing` is FALSE there (`IsDiscreteValuationRing` carries
`maximalIdeal R ≠ ⊥`).  Stating the exclusion as `¬ IsField` rather than as
`x ≠ genericPoint X` is what makes `valuationRing_stalk_of_smoothOfRelativeDimension_one`
below a two-line case split instead of a point-set argument.

**No perfectness is needed in this direction.**  Smooth implies regular over ANY field; it is
only the converse (`smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk`) that
needs `PerfectField K`, and the module docstring records the counterexample.

**WHAT THE PIN HAS** — re-run these before accepting any verdict, because the frequently
repeated claim "there is no `IsRegular` for schemes at this pin" is only half true:

* `IsRegularLocalRing` **exists**, in `Mathlib/RingTheory/RegularLocalRing/Defs.lean`, with
  `isRegularLocalRing_iff`, `iff_finrank_cotangentSpace`, and the instance
  `[IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] : IsRegularLocalRing R`.  What is
  missing is a *scheme-level* `IsRegular` and any link from smoothness to regularity — a grep
  for `IsRegularLocalRing` over `Mathlib/RingTheory/Smooth/` is empty.
* `IsLocalRing.finrank_CotangentSpace_eq_one_iff` (`DiscreteValuationRing/TFAE.lean`) is the
  bridge: for a noetherian local domain, `IsDiscreteValuationRing R ↔ finrank k (m/m²) = 1`.
  So the goal reduces to computing the cotangent space of a stalk of a smooth curve.
* `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` computes the
  differentials of a standard smooth algebra; `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
  gives the local standard-smooth presentation.

So the residue is precisely: *for `S = K[x₁ … x_m]/(f₁ … f_{m-1})` with invertible Jacobian
and `p` a non-minimal prime, `finrank κ(p) (m_p/m_p²) = 1`*. -/
theorem isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [SmoothOfRelativeDimension 1 strX] {x : X} (hx : ¬ IsField (X.presheaf.stalk x)) :
    IsDiscreteValuationRing (X.presheaf.stalk x) :=
  sorry

/-- **Every local ring of a smooth curve over a field is a valuation ring** (PROVEN over the
leaf above).

This is the exact hypothesis of `exists_unique_extension_of_valuationRing_stalk`, and the
case split is the whole proof: at the generic point the stalk is a field, hence a valuation
ring for trivial reasons; elsewhere it is a discrete valuation ring. -/
theorem valuationRing_stalk_of_smoothOfRelativeDimension_one
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [SmoothOfRelativeDimension 1 strX] (x : X) :
    ValuationRing (X.presheaf.stalk x) := by
  by_cases hx : IsField (X.presheaf.stalk x)
  · have hpv : PreValuationRing (X.presheaf.stalk x) := by
      refine ⟨fun a b => ?_⟩
      rcases eq_or_ne a 0 with rfl | ha
      · exact ⟨0, Or.inr (by simp)⟩
      · obtain ⟨a', ha'⟩ := hx.mul_inv_cancel ha
        exact ⟨a' * b, Or.inl (by rw [← mul_assoc, ha', one_mul])⟩
    exact @ValuationRing.mk _ _ _ hpv
  · haveI := isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one strX hx
    infer_instance

/-- **A smooth geometrically connected scheme over a field is integral** (sorry leaf).

TRUE and classical: smooth over a field ⟹ regular local rings ⟹ reduced and normal;
a connected normal noetherian scheme is irreducible; and `GeometricallyConnected` carries
`ConnectedSpace`, hence nonemptiness.  Together these are exactly `IsIntegral`.

**This is the mathlib-shaped form of a leaf that `X0.lean` already carries** as
`isReduced_of_isX0Compactification`, whose own docstring asks for precisely this hoist.  That
declaration has a **separate owner** and is not touched here; it should be re-derived from
this one.  Note this statement is strictly stronger: it also supplies irreducibility, which
`isDominant_of_isX0Compactification` needs as its step 1 and which no field of
`IsX0Compactification` provides.

The relative dimension is left general (`n`), since neither half of the argument sees it. -/
theorem isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected {n : ℕ}
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension n strX] (hconn : GeometricallyConnected strX) :
    IsIntegral X :=
  sorry

/-- **A nonempty smooth curve over a field has infinitely many points** (sorry leaf).

**RECONCILED AT INTEGRATION, 2026-07-27.**  Two branches cut this leaf on the same day,
here with `[IsProper strX]` and in `CurveCompactification.lean` without it, and since that
file `public import`s this one the two collided outright (`has already been declared`).
The PROPERNESS-FREE form is the survivor, for a reason that is not a matter of taste: its
consumer over there,
`isDominant_of_finite_compl_of_smoothOfRelativeDimension_one`, applies it to an OPEN
subscheme `U.ι ≫ strX`, and an open of a proper scheme is not proper — so with `IsProper`
in the signature that consumer cannot be discharged at all.  The statement is true without
it (see the argument below, which never uses properness), and `isDominant_of_finite_compl`
just below keeps its own `[IsProper strX]` because its other steps want it.

TRUE: `X` is one-dimensional, so it has a generic point and infinitely many closed points —
over a finite field because there are closed points of every residue degree, over an infinite
field already among the rational points of any affine chart.  What must be ruled out is
exactly the degenerate possibility that `X` is a finite set, which is what a
`topologicalKrullDim ≤ 0` scheme would be.

This is the missing half of "the open part of a compactification is dense": the complement of
`Y` in `X` is FINITE by hypothesis, so `Y` is nonempty as soon as `X` is infinite, and then
density is formal.  Compare step 2 of `isDominant_of_isX0Compactification` in `X0.lean`,
which is the same observation at `𝔽_ℓ` and has a separate owner.

`IsProper strX` is load-bearing: `𝔸¹ ∖ {closed points}` is not a counterexample, but the leaf
is stated for the proper case because that is where it is consumed and because properness is
what makes "curve" mean "complete curve". -/
theorem infinite_of_smoothOfRelativeDimension_one
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 strX] [Nonempty X] :
    Infinite X :=
  sorry

/-- **An open subscheme with finite complement of a smooth proper curve is dense** (PROVEN
over `infinite_of_smoothOfRelativeDimension_one`).

`Set.range j.base` is nonempty — otherwise its complement is all of `X`, which is infinite —
and a nonempty open subset of an irreducible space is dense. -/
theorem isDominant_of_finite_compl
    {X Y : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K)) [IsProper strX]
    [SmoothOfRelativeDimension 1 strX] [IsIntegral X]
    (j : Y ⟶ X) [IsOpenImmersion j] (hfin : (Set.range j.base)ᶜ.Finite) :
    IsDominant j := by
  haveI : Infinite X := infinite_of_smoothOfRelativeDimension_one strX
  have hne : (Set.range j.base).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h, Set.compl_empty] at hfin
    exact (Set.infinite_univ (α := X)) hfin
  have hopen : IsOpen (Set.range j.base) := j.isOpenEmbedding.isOpen_range
  exact ⟨hopen.dense hne⟩

/-! ### The packaged statement, for a compactification -/

/-- **A morphism from a dense open of a smooth proper geometrically connected curve into a
proper scheme extends UNIQUELY** (PROVEN over the leaves above).

This is the single statement that replaces the three independently cut extension leaves in
`Fermat/FLT/ModularCurve/X0.lean`.  Its hypotheses are, field for field, those of
`Fermat.IsX0Compactification` minus the moduli clause — properness, smoothness of relative
dimension one, geometric connectedness, an open immersion `j` with finite complement — so
each consumer there is a one-line specialisation.

**The base is a FIELD and must not be generalised.**  Over `Spec ℤ_(ℓ)`, which
`IsX0Compactification` also admits, `X` is two-dimensional, the cusp locus has codimension
two, and properness of the target is not enough: the statement is very likely FALSE there.
The reason is visible in the proof: the valuative criterion is applied at `Spec 𝒪_{X,x}` for
every `x`, and that is legitimate exactly because `𝒪_{X,x}` is a valuation ring, which over a
one-dimensional base fails at the closed points of the special fibre.

**The target `Z` is only assumed PROPER.**  Nothing beyond properness of `Z` and the
valuative criterion is used, which is what lets one leaf discharge extension into another
compactification, into an arbitrary proper `ℚ`-scheme, and into `X` itself (the identity case
that gives uniqueness of the round trip).

**Density of `Y` in `X` is derived, not assumed.**  It follows from `smooth`, `connected` and
`finite_compl` JOINTLY — from no single one of them — via `isDominant_of_finite_compl`; this
is the hypothesis that is present but invisible in `IsX0Compactification` and that both of
the old X0 leaves' docstrings flagged as the place the work starts. -/
theorem exists_unique_extension_of_isSmoothProperCurve
    {X Y Z : Scheme.{u}} {strX : X ⟶ Spec (CommRingCat.of K)}
    {strY : Y ⟶ Spec (CommRingCat.of K)} {j : Y ⟶ X}
    {strZ : Z ⟶ Spec (CommRingCat.of K)}
    [IsOpenImmersion j] [IsProper strX] [SmoothOfRelativeDimension 1 strX] [IsProper strZ]
    (hconn : GeometricallyConnected strX) (hfin : (Set.range j.base)ᶜ.Finite)
    (hcomm : j ≫ strX = strY) (φ : Y ⟶ Z) (hφ : φ ≫ strZ = strY) :
    ∃! Φ : X ⟶ Z, Φ ≫ strZ = strX ∧ j ≫ Φ = φ := by
  haveI : IsIntegral X :=
    isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected (n := 1) strX hconn
  haveI : IsDominant j := isDominant_of_finite_compl strX j hfin
  exact exists_unique_extension_of_valuationRing_stalk_of_isOpenImmersion
    (valuationRing_stalk_of_smoothOfRelativeDimension_one strX) φ (by rw [hφ, ← hcomm])

/-! ### The converse direction, for `CurveCompactification.lean` -/

/-- **A curve over a PERFECT field whose local rings are discrete valuation rings is smooth of
relative dimension one** (sorry leaf — the backward half of the DVR equivalence).

TRUE and classical (Stacks `056S`: over a perfect field, regular is equivalent to smooth).
A discrete valuation ring is a principal ideal domain, hence a regular local ring
(`instance [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] : IsRegularLocalRing R`, free
at this pin), so `hdvr` says exactly that `X` is regular; over a perfect field a regular
scheme of finite type is smooth, and the relative dimension is `1` because a dense open of `X`
is already smooth of relative dimension `1`.

**`PerfectField K` is load-bearing and the statement is FALSE without it.**  Over an imperfect
field `k` of characteristic `p` the curve `y^p = t x^p + t` with `t ∈ k ∖ k^p` is regular —
so all its local rings are DVRs — and is not smooth.  `ℚ` and `𝔽_ℓ` are perfect, which is all
either consumer needs.

**Why `j` and `hY` rather than a bare dimension hypothesis.**  `hdvr` alone does not pin the
RELATIVE dimension: `Spec K` itself satisfies it vacuously (its only stalk is a field) and is
smooth of relative dimension `0`.  A dense open that is already known to be a smooth curve is
what fixes the answer at `1`, and it is exactly what the consumer
(`smoothOfRelativeDimension_one_fromNormalization`) has: the normalization of a compactified
curve contains that curve as a dense open, by Zariski's Main Theorem.

**No dimension hypothesis is carried**, deliberately.  `topologicalKrullDim X ≤ 1` is a
CONSEQUENCE of `hdvr` (a discrete valuation ring has Krull dimension one, and
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` plus `Order.krullDim_eq_iSup_coheight`
assemble the stalkwise bound), so passing it would only add an obligation at the use site —
and in `CurveCompactification.lean` the corresponding bound
(`topologicalKrullDim_normalization_le_one`) is itself proven over two further leaves and is
stated BELOW the consumer, so requiring it would force a relocation for no gain.

This is the CONVERSE of `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one`
above; the module docstring explains why the two consumers need opposite directions and why
that is not a duplication. -/
theorem smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk [PerfectField K]
    {X Y : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [LocallyOfFiniteType strX]
    (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hY : SmoothOfRelativeDimension 1 (j ≫ strX))
    (hdvr : ∀ x : X, ¬ IsField (X.presheaf.stalk x) →
      IsDiscreteValuationRing (X.presheaf.stalk x)) :
    SmoothOfRelativeDimension 1 strX :=
  sorry

end AlgebraicGeometry
