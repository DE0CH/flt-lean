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
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Jacobson.Polynomial
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.SetTheory.Cardinal.NatCard

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

Only three things are left open here, and none of them mentions a modular curve.

| leaf | content |
| --- | --- |
| `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` | smooth of relative dimension one over a field ⟹ the local rings away from the generic point are DVRs |
| `smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk` | the CONVERSE over a **perfect** field: DVR local rings ⟹ smooth of relative dimension one |
| `isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected` | smooth over a field + geometrically connected ⟹ integral |

`infinite_of_smoothOfRelativeDimension_one` — a nonempty smooth curve over a field has
infinitely many points — was the fourth, and is **PROVEN** as of 2026-07-27, over two
`Mathlib`-shaped commutative-algebra lemmas proven here beside it,
`MvPolynomial.card_le_height_of_isMaximal` and
`Algebra.not_module_finite_of_isStandardSmoothOfRelativeDimension_one`.  Neither needs
regularity theory; the inputs are Krull's height theorem and the Nullstellensatz.

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

/-! ### The commutative-algebra input to infinitude

Two `Mathlib`-shaped lemmas, both proven outright here, which together say that a nonzero
standard smooth algebra of relative dimension one over a field is *not* finite-dimensional.
That is the entire arithmetic content of `infinite_of_smoothOfRelativeDimension_one` below;
everything else in that proof is scheme-level bookkeeping. -/

/-- **A maximal ideal of a polynomial ring over a field has height at least the number of
variables** (PROVEN).

This is the half of "`dim k[x₁ … xₙ] = n` and the ring is equidimensional" that
`Mathlib` does not state: `MvPolynomial.ringKrullDim_of_isNoetherianRing` gives the
supremum of the heights, which is the *wrong* inequality for the application below.

The proof is the induction that `MvPolynomial.ringKrullDim_of_isNoetherianRing` itself uses,
`Finite.induction_empty_option`, with the two `Mathlib` inputs at the `Option` step being
`Polynomial.height_eq_height_add_one` (a maximal ideal of `R[X]` has height one more than its
contraction, for noetherian `R`) and `Polynomial.isMaximal_comap_C_of_isJacobsonRing` (that
contraction is again maximal, this being the Nullstellensatz).  Note the statement needs no
finiteness hypothesis of its own — for infinite `ι` the left-hand side is `0`. -/
theorem _root_.MvPolynomial.card_le_height_of_isMaximal (k : Type u) [Field k]
    (ι : Type) [Finite ι] :
    ∀ (M : Ideal (MvPolynomial ι k)), M.IsMaximal → (Nat.card ι : ℕ∞) ≤ M.height := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
      intro M hM
      let f := (MvPolynomial.renameEquiv k e.symm).toRingEquiv
      have h1 : (M.map f).IsMaximal := Ideal.map_isMaximal_of_equiv f (hp := hM)
      have h2 := H _ h1
      rwa [RingEquiv.height_map, Nat.card_congr e] at h2
  | h_empty => intro M _; simp
  | h_option IH =>
      rename_i α _
      intro M hM
      let f := (MvPolynomial.optionEquivLeft k α).toRingEquiv
      have h1 : (M.map f).IsMaximal := Ideal.map_isMaximal_of_equiv f (hp := hM)
      have h2 : ((M.map f).under (MvPolynomial α k)).IsMaximal := by
        rw [Ideal.under, Polynomial.algebraMap_eq]
        exact Polynomial.isMaximal_comap_C_of_isJacobsonRing (M.map f)
      have h3 := Polynomial.height_eq_height_add_one ((M.map f).under (MvPolynomial α k)) (M.map f)
      have h4 := IH _ h2
      rw [RingEquiv.height_map] at h3
      rw [Finite.card_option, Nat.cast_add, Nat.cast_one, h3]
      exact add_le_add h4 le_rfl

/-- **A nonzero standard smooth algebra of relative dimension one over a field is not a finite
module** (PROVEN).

This is the precise form in which "a smooth curve is one-dimensional, hence infinite" is
needed, and it is where the `1` in `SmoothOfRelativeDimension 1` is finally consumed.

THE ARGUMENT.  Were `B` finite over `k`, `Module.finite_iff_krullDimLE_zero` (finite type over
an artinian base) would give `Ring.KrullDimLE 0 B`.  Choose a submersive presentation
`B ≃ k[Xᵢ : i : ι] / (f_j : j : σ)` of dimension `1`, so `#ι - #σ = 1`, and a maximal ideal
`M` of `A := k[Xᵢ]` containing the kernel `I`.  Dimension zero upstairs makes *every* prime of
`A` over `I` maximal, so `M` is a MINIMAL prime over `I`; Krull's height theorem
(`Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes`) then bounds `height M ≤ #σ`, while
`MvPolynomial.card_le_height_of_isMaximal` bounds it below by `#ι`.  Hence `#ι ≤ #σ` and the
presentation's dimension is `0`, not `1`.

**Regularity theory is not needed**, matching the experience of the sibling leaf
`isReduced_of_smooth_field` in `Fermat/FLT/Modularity/MoretBailly.lean`: the only inputs are
Krull's height theorem and the Nullstellensatz, both of which `Mathlib` has. -/
theorem _root_.Algebra.not_module_finite_of_isStandardSmoothOfRelativeDimension_one
    (k B : Type u) [Field k] [CommRing B] [Nontrivial B] [Algebra k B]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k B] :
    ¬ Module.Finite k B := by
  intro hfin
  haveI : Algebra.IsStandardSmooth k B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have hKD : Ring.KrullDimLE 0 B := (Module.finite_iff_krullDimLE_zero k B).mp hfin
  obtain ⟨ι, σ, hσ, hι, P, hPdim⟩ :=
    ‹Algebra.IsStandardSmoothOfRelativeDimension 1 k B›.out
  haveI := hσ
  haveI := hι
  set Q := P.toPresentation with hQ
  -- The quotient of the polynomial ring by the kernel has Krull dimension zero.
  have hKD' : Ring.KrullDimLE 0 (Q.Ring ⧸ Q.ker) := by
    rw [Ring.krullDimLE_iff, ringKrullDim_eq_of_ringEquiv Q.quotientEquiv.toRingEquiv]
    exact Ring.krullDimLE_iff.mp hKD
  have hne : Q.ker ≠ ⊤ := by
    intro h
    haveI : Subsingleton (Q.Ring ⧸ Q.ker) := (Ideal.Quotient.subsingleton_iff).mpr h
    haveI : Subsingleton B := Q.quotientEquiv.toEquiv.symm.subsingleton
    exact absurd ‹Nontrivial B› (not_nontrivial_iff_subsingleton.mpr ‹_›)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal Q.ker hne
  -- Every prime containing the kernel is maximal, so `M` is minimal over the kernel.
  have hpm : ∀ q : Ideal Q.Ring, q.IsPrime → Q.ker ≤ q → q.IsMaximal := by
    intro q hq hle
    haveI := hq
    haveI : (q.map (Ideal.Quotient.mk Q.ker)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    haveI := hKD'
    have hq' : Ideal.comap (Ideal.Quotient.mk Q.ker) (q.map (Ideal.Quotient.mk Q.ker)) = q := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hle]
    rw [← hq']
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hmin : M ∈ Q.ker.minimalPrimes := by
    refine ⟨⟨hM.isPrime, hIM⟩, fun q hq hqle => ?_⟩
    exact le_of_eq ((hpm q hq.1 hq.2).eq_of_le hM.ne_top hqle).symm
  -- Krull's height theorem against the lower bound for maximal ideals.
  have h1 : M.height ≤ Cardinal.toENat Q.ker.spanRank :=
    Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ _ hmin
  have h2 : Cardinal.toENat Q.ker.spanRank ≤ (Nat.card σ : ℕ∞) := by
    have hfinr : (Set.range Q.relation).Finite := Set.finite_range _
    have hle : Q.ker.spanFinrank ≤ Nat.card σ := by
      rw [← Q.span_range_relation_eq_ker]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite hfinr).trans ?_
      rw [← Nat.card_coe_set_eq]
      exact Finite.card_range_le _
    rw [Submodule.FG.spanRank_eq_spanFinrank Q.fg_ker]
    simpa using hle
  have h3 : (Nat.card ι : ℕ∞) ≤ M.height := MvPolynomial.card_le_height_of_isMaximal k ι M hM
  have h4 : Nat.card ι ≤ Nat.card σ := by exact_mod_cast h3.trans (h1.trans h2)
  rw [hQ, Algebra.Presentation.dimension, Nat.sub_eq_zero_of_le h4] at hPdim
  exact absurd hPdim (by norm_num)

/-- **A nonempty smooth curve over a field has infinitely many points** (**PROVEN
2026-07-27**, over the two `Mathlib`-shaped algebra lemmas just above).

**RECONCILED AT INTEGRATION, 2026-07-27.**  Two branches cut this leaf on the same day,
here with `[IsProper strX]` and in `CurveCompactification.lean` without it, and since that
file `public import`s this one the two collided outright (`has already been declared`).
The PROPERNESS-FREE form is the survivor, for a reason that is not a matter of taste: its
consumer over there,
`isDominant_of_finite_compl_of_smoothOfRelativeDimension_one`, applies it to an OPEN
subscheme `U.ι ≫ strX`, and an open of a proper scheme is not proper — so with `IsProper`
in the signature that consumer cannot be discharged at all.  The statement is true without
it — the proof below never uses properness — and `isDominant_of_finite_compl` just below
keeps its own `[IsProper strX]` because its other steps want it.  (An older version of this
docstring claimed `IsProper` was "load-bearing".  It is not; that claim is now corrected.)

**THE STATEMENT IS A POINT COUNT, AND MUST STAY ONE.**  Do not "strengthen" it to
`1 ≤ topologicalKrullDim X`: `Spec` of a discrete valuation ring has dimension one and
exactly TWO points, so the dimension statement is strictly weaker than what the consumers
need.  What converts dimension into infinitude here is that the local models are of FINITE
TYPE over a field, hence Jacobson — a positive-dimensional finite-type algebra has infinitely
many maximal ideals — and that is exactly the content of
`Algebra.not_module_finite_of_isStandardSmoothOfRelativeDimension_one` above.

THE PROOF, which is entirely bookkeeping once that lemma is in hand.  Suppose `X` is finite.
Pick a point `x`; smoothness of relative dimension one supplies affine opens `x ∈ V ⊆ X` and
`U ⊆ Spec K` with `Γ(Spec K, U) ⟶ Γ(X, V)` standard smooth of relative dimension one.  `Spec`
of a field is a one-point space, so `U = ⊤` and the source ring is `K` up to `ΓSpecIso`;
transporting along that isomorphism (`RingHom.IsStandardSmoothOfRelativeDimension.equiv`)
makes `B := Γ(X, V)` a standard smooth `K`-algebra of relative dimension one.  It is
nontrivial because `V ∋ x`, and `PrimeSpectrum B ≃ V` is finite because `X` is; a finite
spectrum makes `B` quasi-finite over `K` (`Algebra.QuasiFinite.iff_finite_comap_preimage_singleton`,
using finite presentation) and therefore finite over `K` (`Module.Finite.of_quasiFinite`,
`K` being artinian).  That is what the algebra lemma forbids. -/
theorem infinite_of_smoothOfRelativeDimension_one
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 strX] [Nonempty X] :
    Infinite X := by
  rw [← not_finite_iff_infinite]
  intro hfin
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hU, V, hV, hxV, hle, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := strX) x
  have hUtop : U = ⊤ := by
    have hmem : strX.base x ∈ U := hle hxV
    refine le_antisymm le_top fun y _ => ?_
    exact Subsingleton.elim y (strX.base x) ▸ hmem
  subst hUtop
  -- transport the base along `Γ(Spec K, ⊤) ≅ K`
  let ε : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have hstd' : RingHom.IsStandardSmoothOfRelativeDimension 1
      (((strX.appLE ⊤ V hle).hom).comp (ε : K →+* _)) := by
    simpa using hstd.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv ε)
  letI : Algebra K Γ(X, V) := (((strX.appLE ⊤ V hle).hom).comp (ε : K →+* _)).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(X, V) := hstd'
  -- the points of `V` are the points of `Spec Γ(X, V)`
  let hom : ↥V ≃ₜ ↥(Spec Γ(X, V)) := Scheme.homeoOfIso hV.isoSpec
  haveI : Finite ↥V := Subtype.finite
  haveI : Finite (PrimeSpectrum Γ(X, V)) := Finite.of_equiv _ hom.toEquiv
  haveI : Nontrivial Γ(X, V) := PrimeSpectrum.nontrivial (hom ⟨x, hxV⟩)
  haveI : Algebra.FinitePresentation K Γ(X, V) :=
    (Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1).finitePresentation
  haveI : Algebra.QuasiFinite K Γ(X, V) :=
    Algebra.QuasiFinite.iff_finite_comap_preimage_singleton.mpr fun _ => Set.toFinite _
  exact Algebra.not_module_finite_of_isStandardSmoothOfRelativeDimension_one K Γ(X, V)
    Module.Finite.of_quasiFinite

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
