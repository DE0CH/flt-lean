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
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Smooth.Field
public import Fermat.FLT.Modularity.RegularStalks

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

**UPDATED 2026-07-27** — the three general-scheme-theory leaves of this file were worked
over on that date and the shape changed completely.  What follows supersedes the earlier
"a prover of either direction should route through `IsRegularLocalRing`" note, which was
correct but is no longer the frontier: the regularity link now EXISTS in this project.

`Fermat/FLT/Modularity/RegularStalks.lean` carries, sorry-free and with NO `Fermat`
imports of its own (so it is importable from anywhere, and this file now imports it):

* `GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field` —
  `Smooth (Z ⟶ Spec K)` ⟹ every stalk of `Z` is a regular local ring;
* `GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing` — regular local ⟹ domain,
  mathlib's own recorded TODO, closed there.

Against those, the state of this file's leaves is now:

| leaf | status |
| --- | --- |
| `isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected` | **PROVEN 2026-07-27**, no sorry |
| `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` | **PROVEN** over ONE dimension-theory leaf, `ringKrullDim_le_of_isStandardSmoothOfRelativeDimension` |
| `smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk` | **PROVEN** over TWO leaves, `formallySmooth_of_isDiscreteValuationRing_of_perfectField` and `smoothOfRelativeDimension_of_isDominant_of_smooth` |
| `infinite_of_smoothOfRelativeDimension_one` | open, untouched (separate owner) |

**The DVR pair are still the two directions of ONE classical equivalence** ("regular ⟺
smooth over a perfect field", in dimension one, where regular ⟺ DVR), and it is worth
saying so loudly because the task that produced this file was dispatched on the belief
that the two consumers shared a single *statement*.  They do not: `X0.lean` needs the
forward direction (it HAS smoothness and WANTS DVRs) and `CurveCompactification.lean`
needs the backward one (it HAS normality/DVRs and WANTS smoothness).  They share a file, a
docstring and an owner; they are not the same theorem.  What the 2026-07-27 pass showed is
that the two directions do NOT share a residue either:

* forward, regularity is FREE (`isRegularLocalRing_stalk_of_smooth_over_field`) and the
  entire residue is **dimension theory** — "a smooth `K`-algebra of relative dimension `n`
  has Krull dimension at most `n`";
* backward, dimension is nearly free and the entire residue is **formal smoothness of a
  regular local ring over a perfect field** (Stacks `056S`), for which mathlib supplies the
  local Jacobian criterion (`Algebra.FormallySmooth.iff_injective_lTensor_residueField`)
  and the field case (`Algebra.FormallySmooth.of_perfectField`), plus the transport
  `AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff` which reduces `Smooth f` to
  formal smoothness of every stalk map.

`Mathlib` has `IsRegularLocalRing` (`Mathlib/RingTheory/RegularLocalRing/Defs.lean` — note
this REFUTES the frequently repeated claim that there is no notion of regularity at this
pin).  Named inputs a prover of the residues will want:

* `IsLocalRing.finrank_CotangentSpace_eq_one_iff` (`DiscreteValuationRing/TFAE.lean`) turns
  `IsDiscreteValuationRing R` into `finrank (ResidueField R) (CotangentSpace R) = 1` for a
  noetherian local domain, and `IsRegularLocalRing.iff_finrank_cotangentSpace` turns
  regularity into `finrank … = ringKrullDim R`.  This is what makes the forward direction
  purely a Krull-dimension question — it is USED below, not merely suggested.
* `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`
  (`Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean`) is the differential-side input:
  a standard smooth algebra of relative dimension `n` has free differentials of rank `n`.
* `instance [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] : IsRegularLocalRing R` is
  already there, so the DVR ⟹ regular half is free.
* `MvPolynomial.ringKrullDim_of_isNoetherianRing` and
  `IsLocalization.AtPrime.ringKrullDim_eq_height` are the two dimension facts the forward
  residue needs about the ambient polynomial ring.

**A route that is CIRCULAR and keeps being suggested**: reaching irreducibility through
`GeometricallyIrreducible.irreducibleSpace_of_subsingleton`.  Its hypothesis asks for
irreducibility of every field base change, each of which is an instance of the very lemma
being proven.  The proof used below goes the other way — locally irreducible (domain
stalks) plus connected — and is elementary.

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

/-- **A STANDARD SMOOTH ALGEBRA OF RELATIVE DIMENSION `n` OVER A FIELD HAS KRULL DIMENSION AT
MOST `n`** (sorry leaf, cut 2026-07-27 — the ENTIRE residue of
`isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one`, and pure commutative
algebra: no schemes, no curves, no properness).

TRUE and classical (Stacks `00SB`/`02FZ`; a smooth `K`-algebra of relative dimension `n` is
equidimensional of dimension `n`, so in particular `dim A ≤ n`).  Only the `≤` direction is
asked for, because that is all the consumer needs and it is the half that does not require
`A` to be nonzero or equidimensional.

**WHY THIS IS THE RIGHT CUT.**  Once `RegularStalks.lean` supplies regularity of the stalks
for free, the forward DVR leaf reduces — through
`IsRegularLocalRing.iff_finrank_cotangentSpace` and
`IsLocalRing.finrank_CotangentSpace_eq_one_iff` — to the single numerical statement
`ringKrullDim 𝒪_{X,x} = 1`, whose `≥ 1` half is `¬ IsField` and whose `≤ 1` half is this
leaf.  Everything else in that leaf is now proven below.  So this is the last mathematical
content in the forward direction, and it is a general mathlib-shaped statement.

**THE PROOF, and the ONE piece of bookkeeping it needs that does not yet exist.**  Let
`P : SubmersivePresentation K A ι σ` with `P.dimension = #ι - #σ = n`, so `A` is
`MvPolynomial ι K` modulo the `#σ` relations.  Fix a prime `p` of `A`, let `q` be its
preimage in `MvPolynomial ι K` and `B := (MvPolynomial ι K)_q`.  Then:

1. `ringKrullDim B = q.height ≤ ringKrullDim (MvPolynomial ι K) = #ι`, by
   `IsLocalization.AtPrime.ringKrullDim_eq_height`, `Ideal.height_le_ringKrullDim_of_isPrime`
   and `MvPolynomial.ringKrullDim_of_isNoetherianRing` (`= ringKrullDim K + Nat.card ι`).
2. `A_p ≃+* B ⧸ (l)` for a list `l` of length `#σ` whose members satisfy the ITERATED
   INDEPENDENCE condition `l[i] ∈ 𝔪 ∖ (𝔪² ⊔ (l[0], …, l[i-1]))`.  This is exactly
   `GaloisRepresentation.Modularity.exists_isRegularLocalRing_quotient_indepList_of_submersivePresentation`
   (PROVEN, `Modularity/RegularStalks.lean`) — **except that its existential FORGETS both
   `B` and `l.length`**, recording only that some regular local `B` and some independent
   `l` exist.  Strengthening that statement to also expose `ringKrullDim B ≤ Nat.card ι`
   and `l.length = Nat.card σ` is the one new piece of bookkeeping this leaf needs, and it
   is an edit to a *proof that already computes both*.
3. `ringKrullDim (R ⧸ (l)) + l.length = ringKrullDim R` for `R` regular local and `l`
   independent in that sense.  Induction on `l`, mirroring
   `isRegularLocalRing_quotient_span_list_aux`: at each step `x ∈ 𝔪 ∖ 𝔪²` is nonzero (as
   `0 ∈ 𝔪²`) hence a nonzerodivisor in the domain `R` (regular local ⟹ domain), so
   `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`
   (`@[stacks 00KW]`, `Mathlib/RingTheory/KrullDimension/Regular.lean`) drops the dimension
   by exactly one, `isRegularLocalRing_quotient_span_singleton` keeps the quotient regular
   local, and `DoubleQuot.quotQuotEquivQuotSup` reassembles.  Cancellation of `+ l.length`
   in `WithBot ℕ∞` is legitimate because a regular local ring has finite dimension
   (`spanFinrank_maximalIdeal`).
4. Chaining, `ringKrullDim A_p = ringKrullDim B − #σ ≤ #ι − #σ = n`, and
   `ringKrullDim A = ⨆_p height p` is the supremum of those.

**AN ALTERNATIVE FOR STEP 2 THAT AVOIDS TOUCHING `RegularStalks.lean`**, if its owner
objects: `#ι − l.length = n` can be read off the conormal sequence instead of the
presentation, since `Ω[A_p⁄K]` is free of rank `n`
(`IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`) and
`κ^{l.length} → κ^{#ι} → κ^n → 0` is exact with the left map injective — which is precisely
what the independence of `l` says.

*Refute this leaf with:* a standard smooth `K`-algebra of relative dimension `n` carrying a
chain of `n + 1` strict prime inclusions.  There is none; the bound is Stacks `00SB`. -/
theorem ringKrullDim_le_of_isStandardSmoothOfRelativeDimension {n : ℕ}
    {A : Type u} [CommRing A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    ringKrullDim A ≤ (n : WithBot ℕ∞) :=
  sorry

/-- **THE SAME BOUND FOR A LOCALIZATION AT A PRIME** (PROVEN over the leaf above).

`ringKrullDim A_p` is the height of `p` (`IsLocalization.AtPrime.ringKrullDim_eq_height`),
which is at most `ringKrullDim A`.  Stated for an arbitrary localization `S` rather than
`Localization.AtPrime p` for the ELABORATION-COST reason `RegularStalks.lean` documents on
`exists_isRegularLocalRing_quotient_indepList_of_isStandardSmooth_of_isLocalization`: the
scheme-level consumer holds a stalk, a colimit in `CommRingCat`, and unifying that against
the concrete `Localization.AtPrime p` sends `whnf` into the colimit. -/
theorem ringKrullDim_localization_le_of_isStandardSmoothOfRelativeDimension {n : ℕ}
    {A : Type u} [CommRing A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] (p : Ideal A) [p.IsPrime]
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S p] :
    ringKrullDim S ≤ (n : WithBot ℕ∞) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S]
  exact le_trans Ideal.height_le_ringKrullDim_of_isPrime
    (ringKrullDim_le_of_isStandardSmoothOfRelativeDimension (K := K))

/-- **THE STALK OF A SCHEME SMOOTH OF RELATIVE DIMENSION `n` OVER A FIELD HAS KRULL DIMENSION
AT MOST `n`** (PROVEN 2026-07-27 over the algebra leaf above — this declaration is pure
chart bookkeeping and contains no mathematics).

The three steps are the ones
`GaloisRepresentation.Modularity.exists_isRegularLocalRing_quotient_indepList_of_smooth_over_field`
already performs for `Smooth`, transposed to `SmoothOfRelativeDimension`:

1. `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension` gives affine opens
   `U ∋ strX x` in `Spec K` and `V ∋ x` in `X` with
   `RingHom.IsStandardSmoothOfRelativeDimension n (strX.appLE U V e).hom`;
2. `Spec K` is a ONE-POINT space, so `U = ⊤`, and `Scheme.ΓSpecIso` identifies
   `Γ(Spec K, ⊤)` with `K`; transporting the ring-hom property across that iso is
   `RingHom.isStandardSmoothOfRelativeDimension_respectsIso`;
3. `IsAffineOpen.isLocalization_stalk` presents `𝒪_{X,x}` as a localization of `Γ(X, V)` at
   the prime of `x`.  The `Algebra Γ(X, V) 𝒪_{X,x}` instance has to be supplied by hand as
   `X.presheaf.algebra_section_stalk ⟨x, hxV⟩`, because instance search cannot solve
   `↑?y = x` through the coercion. -/
theorem ringKrullDim_stalk_le_of_smoothOfRelativeDimension {n : ℕ}
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension n strX] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ (n : WithBot ℕ∞) := by
  obtain ⟨U, hU, V, hV, hxV, ele, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n)
      (f := strX) x
  haveI : Subsingleton ↥(Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hUtop : U = ⊤ := by
    refine le_antisymm le_top fun y _ => ?_
    have hy : y = strX.base x := Subsingleton.elim _ _
    exact hy ▸ ele hxV
  subst hUtop
  let eK : K ≃+* ↥Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  letI : Algebra K ↥Γ(X, V) := ((strX.appLE ⊤ V ele).hom.comp eK.toRingHom).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K ↥Γ(X, V) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ eK hss
  letI : Algebra ↥Γ(X, V) ↥(X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  haveI : IsLocalization.AtPrime ↥(X.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  exact ringKrullDim_localization_le_of_isStandardSmoothOfRelativeDimension (K := K) (n := n)
    (A := ↥Γ(X, V)) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal ↥(X.presheaf.stalk x)

/-- **A smooth curve over a field has discrete valuation rings as its local rings away from
the generic point** (**PROVEN 2026-07-27** over the single dimension leaf
`ringKrullDim_le_of_isStandardSmoothOfRelativeDimension`; formerly a sorry leaf).

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
needs `PerfectField K`; the counterexample justifying that hypothesis is written out on the
converse itself (the quasi-elliptic curve `y² = x³ + t` over `𝔽₃(t)`).  This pointer used to
say "the module docstring records the counterexample", which was a dangling reference — no
counterexample was recorded there.

**THE PROOF, in four steps, and where each input lives.**  The old version of this docstring
listed the pin's regularity API and concluded that the residue was
"*for `S = K[x₁ … x_m]/(f₁ … f_{m-1})` with invertible Jacobian and `p` a non-minimal prime,
`finrank κ(p) (m_p/m_p²) = 1`*".  That was right, and it is now HALF DISCHARGED: the
cotangent computation is free, and only the dimension survives.

1. `GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field`
   (`Modularity/RegularStalks.lean`, sorry-free) makes `𝒪_{X,x}` a REGULAR local ring, and
   `isDomain_of_isRegularLocalRing` (same file, mathlib's own recorded TODO, closed there)
   makes it a domain.  **This is the input the earlier verdicts on this leaf did not have**;
   the claim that the smoothness ⟹ regularity link is missing was true of `Mathlib` and is
   false of this project.
2. `ringKrullDim 𝒪_{X,x} ≤ 1` is `ringKrullDim_stalk_le_of_smoothOfRelativeDimension` above,
   which is the ONE remaining sorry underneath this node.
3. `ringKrullDim 𝒪_{X,x} ≥ 1` is `hx`: a noetherian local DOMAIN with `KrullDimLE 0` is a
   field (`Ring.KrullDimLE.isField_of_isDomain`), so `¬ IsField` excludes dimension `0`, and
   `ENat.WithBot.lt_add_one_iff` turns `< 1` into `≤ 0`.  Hence `ringKrullDim = 1`.
4. Regularity converts that dimension into the cotangent space
   (`IsRegularLocalRing.iff_finrank_cotangentSpace`), and
   `IsLocalRing.finrank_CotangentSpace_eq_one_iff` converts `finrank = 1` into
   `IsDiscreteValuationRing`.  No dimension theory is done here — it is all pushed into
   step 2. -/
theorem isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [SmoothOfRelativeDimension 1 strX] {x : X} (hx : ¬ IsField (X.presheaf.stalk x)) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  haveI : Smooth strX := SmoothOfRelativeDimension.smooth 1 strX
  haveI hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field
      strX inferInstance x
  haveI : IsDomain (X.presheaf.stalk x) :=
    GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing _
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ (1 : ℕ) :=
    ringKrullDim_stalk_le_of_smoothOfRelativeDimension strX x
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    refine eq_of_le_of_not_lt (by exact_mod_cast hle) fun h => ?_
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
      Ring.krullDimLE_iff.mpr (ENat.WithBot.lt_add_one_iff.mp (by simpa using h))
    exact hx Ring.KrullDimLE.isField_of_isDomain
  have hfr : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) = 1 := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk x)).mp hreg
    rw [hdim] at this
    exact_mod_cast this
  exact IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hfr

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

/-! ### Connected + locally irreducible ⟹ irreducible

The three lemmas of this block are general topology and general scheme theory; together
with the regular-stalk input from `Modularity/RegularStalks.lean` they close
`isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected` outright.

**PROVENANCE, so that nobody re-derives them a third time.**  They are re-proofs of
`GaloisRepresentation.Modularity.irreducibleSpace_of_connectedSpace_of_locallyIrreducible`,
`…exists_isOpen_isIrreducible_primeSpectrum` and
`…exists_isOpen_isIrreducible_of_isDomain_stalk`, all PROVEN in
`Fermat/FLT/Modularity/MoretBailly.lean`.  They are restated here rather than imported
because `MoretBailly.lean` is a 34 000-line module whose own import cone reaches the
Deformations and automorphic-form subtrees, and `CurveExtension.lean` is imported by
`CurveCompactification.lean`, whose entire `Fermat` cone is two modules.  Importing it to
reach 130 lines of point-set topology would be a cone-growth trade nobody would take.  The
names here are deliberately DIFFERENT from the `MoretBailly` ones so that a file importing
both never sees an ambiguous bare name.  **If those three are ever hoisted into
`Fermat/FLT/Mathlib/`, delete this block and import them instead.** -/

/-- **A CONNECTED, LOCALLY IRREDUCIBLE SPACE IS IRREDUCIBLE** (PROVEN — pure point-set
topology, no schemes).

If every point has an irreducible OPEN neighbourhood then the irreducible component of any
point is open (each of its points has a neighbourhood inside it, since the closure of an
irreducible open meeting the component IS the component), hence clopen, hence everything.

The openness is load-bearing and the statement is FALSE with "irreducible open
neighbourhood" weakened to "irreducible subset containing the point": two lines crossing at
the origin form a connected space in which every point lies on an irreducible subset, and
which is reducible — the origin has no irreducible *open* neighbourhood. -/
theorem irreducibleSpace_of_isOpen_isIrreducible_nhds
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (hloc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) :
    IrreducibleSpace X := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have key : ∀ y ∈ irreducibleComponent x₀,
      ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ U ⊆ irreducibleComponent x₀ := by
    intro y hy
    obtain ⟨U, hUo, hyU, hUirr⟩ := hloc y
    refine ⟨U, hUo, hyU, ?_⟩
    have hZsub : irreducibleComponent x₀ ⊆ _root_.closure U := by
      intro z hz
      by_contra hzn
      obtain ⟨w, -, hwU, hwc⟩ :=
        (isIrreducible_irreducibleComponent (x := x₀)).2 U (_root_.closure U)ᶜ hUo
          isClosed_closure.isOpen_compl ⟨y, hy, hyU⟩ ⟨z, hz, hzn⟩
      exact hwc (subset_closure hwU)
    have heq : _root_.closure U = irreducibleComponent x₀ :=
      eq_irreducibleComponent (hUirr.isPreirreducible.closure) hZsub
    exact heq ▸ subset_closure
  have hZopen : IsOpen (irreducibleComponent x₀) := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨U, hUo, hyU, hUZ⟩ := key y hy
    exact ⟨U, hUZ, hUo, hyU⟩
  have hZuniv : irreducibleComponent x₀ = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_irreducibleComponent, hZopen⟩ ⟨x₀, mem_irreducibleComponent⟩
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hZuniv]
  exact isIrreducible_irreducibleComponent

/-- **A PRIME WHOSE LOCALIZATION IS A DOMAIN HAS AN IRREDUCIBLE OPEN NEIGHBOURHOOD IN
`Spec R`** (PROVEN — pure commutative algebra, no smoothness).

`R_p` is a domain, so `⊥` is its least prime and `IsLocalization.AtPrime.orderIsoOfPrime`
carries that to a LEAST prime `q ≤ p` of `R`, which is therefore the unique minimal prime
below `p`.  Noetherianity makes `minimalPrimes R` finite, so
`U := Spec R ∖ ⋃ {V(q') : q' ∈ minimalPrimes R, q' ≠ q}` is open; `p ∈ U` by that
uniqueness, and every prime contains some minimal prime, so `U ⊆ V(q)`, which is irreducible
because `q` is prime.

Both hypotheses are needed: without noetherianity there can be infinitely many minimal
primes and `U` is not open; without the domain hypothesis `p` may lie on several components
and then no neighbourhood of it is irreducible. -/
theorem exists_isOpen_isIrreducible_of_isDomain_localization {R : Type u} [CommRing R]
    [IsNoetherianRing R] (p : PrimeSpectrum R)
    (hp : IsDomain (Localization.AtPrime p.asIdeal)) :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ p ∈ U ∧ IsIrreducible U := by
  classical
  haveI : p.asIdeal.IsPrime := p.isPrime
  have hbot : (⊥ : Ideal (Localization.AtPrime p.asIdeal)).IsPrime := Ideal.isPrime_bot
  set e := IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime p.asIdeal) p.asIdeal
    with he
  set q : Ideal R := (e ⟨⊥, hbot⟩).1 with hqdef
  have hq : q.IsPrime := (e ⟨⊥, hbot⟩).2.1
  have hleast : ∀ r : Ideal R, r.IsPrime → r ≤ p.asIdeal → q ≤ r := by
    intro r hr hrle
    have h1 : (⟨⊥, hbot⟩ : {P : Ideal (Localization.AtPrime p.asIdeal) // P.IsPrime}) ≤
        e.symm ⟨r, hr, hrle⟩ := Subtype.mk_le_mk.mpr bot_le
    have h2 := e.monotone h1
    rw [e.apply_symm_apply] at h2
    exact h2
  have huniq : ∀ r ∈ minimalPrimes R, r ≤ p.asIdeal → r = q := by
    intro r hr hrle
    have hr' := (IsMinimalPrime.iff_minimal r).mp hr
    have h1 : q ≤ r := hleast r hr'.1 hrle
    exact le_antisymm (hr'.2 hq h1) h1
  set S : Set (Ideal R) := minimalPrimes R \ {q} with hSdef
  have hSfin : S.Finite := (minimalPrimes.finite_of_isNoetherianRing R).subset Set.sdiff_subset
  set U : Set (PrimeSpectrum R) := (⋃ r ∈ S, PrimeSpectrum.zeroLocus (r : Set R))ᶜ with hUdef
  have hUopen : IsOpen U :=
    (hSfin.isClosed_biUnion fun r _ => PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  have hpU : p ∈ U := by
    simp only [hUdef, Set.mem_compl_iff, Set.mem_iUnion, not_exists, exists_prop, not_and]
    intro r hrS hpz
    exact hrS.2 (huniq r hrS.1 (PrimeSpectrum.mem_zeroLocus _ _ |>.mp hpz))
  have hUsub : U ⊆ PrimeSpectrum.zeroLocus (q : Set R) := by
    intro x hx
    obtain ⟨r, hrmin, hrle⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := x.asIdeal) bot_le
    have hrq : r = q := by
      by_contra hne
      refine hx ?_
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨r, ⟨hrmin, hne⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hrle⟩
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (hrq ▸ hrle)
  have hqrad : q.radical.IsPrime := by rw [hq.radical]; exact hq
  have hirr : IsIrreducible (PrimeSpectrum.zeroLocus (q : Set R)) :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff q).mpr hqrad
  exact ⟨U, hUopen, hpU,
    hirr.isPreirreducible.subset_irreducible ⟨p, hpU⟩ hUopen (subset_refl U) hUsub⟩

/-- **A POINT WITH DOMAIN STALK ON A LOCALLY NOETHERIAN SCHEME HAS AN IRREDUCIBLE OPEN
NEIGHBOURHOOD** (PROVEN over the affine statement above).

`Scheme.exists_Spec_apply_eq` produces an open immersion `Spec R ⟶ Z` hitting `z`;
`Spec.stalkIso` identifies the stalk with `Localization.AtPrime y.asIdeal`, and the image of
an irreducible open under an open embedding is an irreducible open. -/
theorem exists_isOpen_isIrreducible_nhds_of_isDomain_stalk {Z : Scheme.{u}}
    [IsLocallyNoetherian Z] (z : Z) (hz : IsDomain (Z.presheaf.stalk z)) :
    ∃ U : Set Z, IsOpen U ∧ z ∈ U ∧ IsIrreducible U := by
  obtain ⟨R, f, hf, y, hy⟩ := Scheme.exists_Spec_apply_eq (X := Z) z
  haveI := hf
  haveI : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  haveI : IsNoetherianRing R := isLocallyNoetherian_Spec.mp inferInstance
  subst hy
  haveI : IsDomain ((Spec R).presheaf.stalk y) :=
    (asIso (f.stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  haveI : IsDomain (Localization.AtPrime y.asIdeal) :=
    (Spec.stalkIso R y).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  obtain ⟨U, hUopen, hyU, hUirr⟩ := exists_isOpen_isIrreducible_of_isDomain_localization y
    inferInstance
  refine ⟨f.base '' U, ?_, ⟨y, hyU, rfl⟩, ?_⟩
  · exact f.isOpenEmbedding.isOpenMap _ hUopen
  · exact hUirr.image _ f.continuous.continuousOn

/-- **A smooth geometrically connected scheme over a field is integral** (**PROVEN
2026-07-27** — no sorry, and nothing underneath it is sorried either).

TRUE and classical: smooth over a field ⟹ regular local rings ⟹ reduced and locally
irreducible; a connected, locally noetherian, locally irreducible scheme is irreducible; and
`GeometricallyConnected` over a one-point base carries `ConnectedSpace`, hence nonemptiness.
Together these are exactly `IsIntegral`.

**THE FOUR INPUTS.**

1. `GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field` and
   `…isDomain_of_isRegularLocalRing` (`Modularity/RegularStalks.lean`, both sorry-free) make
   every stalk a DOMAIN.  Note this route is `sorryAx`-free, whereas this project's own
   `AlgebraicGeometry.isReduced_of_smooth_over_field`
   (`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean`) is built over the
   still-open `Algebra.Smooth.isReduced_of_isField`; going through the stalks keeps that
   leaf's sorry out of this cone.
2. `isReduced_of_isReduced_stalk` lifts domain (hence reduced) stalks to `IsReduced X`.
3. `exists_isOpen_isIrreducible_nhds_of_isDomain_stalk` and
   `irreducibleSpace_of_isOpen_isIrreducible_nhds` above give `IrreducibleSpace X`, using
   `LocallyOfFiniteType.isLocallyNoetherian` for the noetherianity they need.
4. `isIntegral_of_irreducibleSpace_of_isReduced` assembles.

**This is the mathlib-shaped form of a leaf that `X0.lean` already carries** as
`isReduced_of_isX0Compactification`, whose own docstring asks for precisely this hoist.  That
declaration has a **separate owner** and is not touched here; **it can now be re-derived from
this one at no cost**, since this one is proven.  Note this statement is strictly stronger:
it also supplies irreducibility, which `isDominant_of_isX0Compactification` needs as its
step 1 and which no field of `IsX0Compactification` provides.

The relative dimension is left general (`n`), since no half of the argument sees it; only
`Smooth` is used, through `SmoothOfRelativeDimension.smooth`.  Ordinary `ConnectedSpace`
would do in place of `GeometricallyConnected`, which appears only because that is what the
callers hold. -/
theorem isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected {n : ℕ}
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension n strX] (hconn : GeometricallyConnected strX) :
    IsIntegral X := by
  haveI : Smooth strX := SmoothOfRelativeDimension.smooth n strX
  haveI hdom : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x => by
    haveI := GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field
      strX inferInstance x
    exact GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing _
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => inferInstance
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian strX
  haveI := hconn
  haveI : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : Nonempty (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum K))
  haveI : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton strX
  haveI : IrreducibleSpace X :=
    irreducibleSpace_of_isOpen_isIrreducible_nhds
      (fun x => exists_isOpen_isIrreducible_nhds_of_isDomain_stalk x (hdom x))
  exact isIntegral_of_irreducibleSpace_of_isReduced X

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

/-- **A DISCRETE VALUATION RING ESSENTIALLY OF FINITE TYPE OVER A PERFECT FIELD IS FORMALLY
SMOOTH** (sorry leaf, cut 2026-07-27 — the geometric heart of Stacks `056S`, and pure
commutative algebra: no schemes, no curves, no relative dimension).

TRUE and classical.  Over a perfect field, regular ⟺ smooth (Stacks `056S`, `00TT`); this is
the local, algebra-level form of the direction that is missing from the pin.  The dimension
is irrelevant to it — the statement for a general REGULAR LOCAL `R` essentially of finite
type over perfect `K` is equally true, and a prover who finds that shape more natural should
prove it and derive this one, since `IsDiscreteValuationRing R` gives
`IsPrincipalIdealRing R` and hence `IsRegularLocalRing R` for free at this pin.

**`PerfectField F` is load-bearing and the statement is FALSE without it.**

**COUNTEREXAMPLE CORRECTED, 2026-07-28.**  The first version of this docstring cited
`y^p = t x^p + t` (`t ∈ k ∖ k^p`) as "regular, so its local rings are DVRs, and not
smooth".  **That witness is invalid and justified nothing**, and the failure is exactly on
the hypothesis it was cited to illustrate: in characteristic `p`,
`t x^p + t = t (x + 1)^p`, so with `u = x + 1` the equation is `y^p = t u^p`, whose
defining polynomial lies in `𝔪²` at the `k`-rational point `u = y = 0` (checked in
`Singular`: `reduce(g, std(m^2)) == 0`).  That local ring has `dim_k 𝔪/𝔪² = 2` in
dimension one, so it is **singular, not a DVR**; its integral closure `k(t^{1/p})[u]` is
strictly larger.  It is also not geometrically reduced — over `k̄` it is
`(y − t^{1/p}(x+1))^p = 0`.

The correct witness is the classical **quasi-elliptic** curve, localized.  Over
`k = 𝔽₃(t)`, take `C : y² = x³ + t` and let `R := 𝒪_{C,P}` at the unique
Jacobian-degenerate point `P : y = 0, x³ = −t` (residue field `k(t^{1/3})`).

* `R` **is a DVR essentially of finite type over `k`**: `C` is integral, and at `P` the
  maximal ideal is `𝔪 = (y, x³ + t) = (y)` because `x³ + t = y²` — a one-dimensional local
  ring with principal maximal ideal.  So `R` satisfies **every hypothesis of this leaf**,
  which the old witness did not.
* `R` is **not formally smooth over `k`**: over `k̄`, `x³ + t = (x + t^{1/3})³`, so
  `C ⊗ k̄` is the cuspidal cubic `y² = (x + t^{1/3})³` and `P` becomes the cusp.  Formal
  smoothness is stable under base change, so it fails already over `k`.

Machine-checked in `Magma` (2026-07-28) on the same example: `k(C)` has genus `1` over
`𝔽₃(t)` with exact constant field `k`, and genus `0` after the purely inseparable base
change `t = s³` — a drop of `(p−1)/2 = 1`, exactly what Tate's genus-change theorem permits
at `p = 3`.  A geometrically regular model would preserve the genus.

**The tempting repair fails too**: `k(C)/k` **is** separably generated (`k(C)/k(x)` is
separable of degree `2`), so "separably generated function field ⟹ formally smooth" is
FALSE; separable generation is strictly weaker than conservativity.  The full worked
version of this counterexample, with the same correction, is on
`smoothOfRelativeDimension_one_fromNormalization` in `CurveCompactification.lean`.

**THE ROUTE, and what the pin already supplies for it.**

* `Algebra.FormallySmooth.iff_injective_lTensor_residueField`
  (`Mathlib/RingTheory/Smooth/Local.lean`) is the **local Jacobian criterion**: for a local
  `K`-algebra `S` with a presentation `0 → I → P → S → 0` where `P` is formally smooth with
  `Ω[P⁄K]` finite free and `I` finitely generated, `S` is formally smooth **iff**
  `κ ⊗ I/I² → κ ⊗ Ω[P⁄K]` is injective.  Take `P` a localization of a polynomial ring, which
  is where `Algebra.EssFiniteType F R` is used.
* `Algebra.FormallySmooth.of_perfectField` (`Mathlib/RingTheory/Smooth/Field.lean`) is the
  same statement when `R` is a FIELD, and is already used below for the field stalks.  What
  is missing is exactly the passage from the residue field to the DVR.
* The classical argument for the injectivity is that regularity of `R` makes the images of
  a minimal generating set of `I` linearly independent in `𝔪_P/𝔪_P²` — the Jacobian matrix
  has full rank — and perfectness of `F` is what makes `κ` separable over `F`, so that
  `H₁(L_{κ⁄F}) = 0` and no relation is created by inseparability.  It is precisely that last
  vanishing which the quasi-elliptic counterexample violates: there `κ = k(t^{1/3})` is
  purely INSEPARABLE over `k = 𝔽₃(t)`, so `H₁(L_{κ⁄k}) ≠ 0` and the Jacobian criterion's
  injectivity fails even though `R` is a DVR.
* `GaloisRepresentation.Modularity.exists_isRegularLocalRing_quotient_indepList_of_submersivePresentation`
  (`Modularity/RegularStalks.lean`, PROVEN) is the *converse* bookkeeping — it turns a
  standard smooth presentation into regularity — and its Jacobian manipulation is the
  closest existing model for the matrix argument here.

**THIS IS THE SAME GAP THAT `SmoothConnectedCriteria.lean` NAMES, AND IT SHOULD BE PROVEN
ONCE** (noticed at the release-7 merge, 2026-07-27).  That module's
`smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing` (sorry leaf, same directory,
different owner) says "regular + finite type over a perfect field ⟹ smooth of relative
dimension `ringKrullDim`", and its own docstring identifies the residue in exactly these
words: *"the missing step is therefore smoothness at the CLOSED points, i.e. formal
smoothness of a regular local ring essentially of finite type over a perfect field"*.  That
is this leaf, in its regular-local form.  So whoever proves this should prove the
regular-local version and hand both files the same theorem; that leaf then needs only its
own dimension bookkeeping on top.  Two further consumers are named there —
`X0.lean`'s `smoothOfRelativeDimension_of_gamma0GITPresentation` and
`CurveCompactification.lean`'s `smoothOfRelativeDimension_one_fromNormalization` — so this
single algebra statement is under at least four open nodes.

*Refute this leaf with:* a DVR, essentially of finite type over a PERFECT field, that is not
formally smooth over it.  There is none; over an imperfect field there are, and the example
above is one. -/
theorem formallySmooth_of_isDiscreteValuationRing_of_perfectField
    {F R : Type u} [Field F] [PerfectField F] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra F R] [Algebra.EssFiniteType F R] :
    Algebra.FormallySmooth F R :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **A SCHEME LOCALLY OF FINITE TYPE OVER A PERFECT FIELD WHOSE LOCAL RINGS ARE DISCRETE
VALUATION RINGS OR FIELDS IS SMOOTH** (PROVEN 2026-07-27 over the leaf above — this
declaration is the scheme-theoretic transport and contains no new mathematics).

**THE TRANSPORT IS FREE AT THIS PIN, and that is the discovery that reshaped this leaf.**
`AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff`
(`Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`) says that for `f` locally of finite
presentation, `Smooth f` is EQUIVALENT to `(f.stalkMap x).hom.FormallySmooth` for every `x`.
So no affine cover has to be built by hand, and `Smooth` reduces pointwise to an algebra
question about the stalks.  `LocallyOfFinitePresentation` comes from
`LocallyOfFiniteType` for free over the noetherian base `Spec K`
(`Mathlib/AlgebraicGeometry/Noetherian.lean`), and `Algebra.EssFiniteType` of the stalk map
from `LocallyOfFiniteType.stalkMap`.

The case split is then:

* `𝒪_{X,x}` a FIELD: `Algebra.FormallySmooth.of_perfectField`, exactly as mathlib's own
  `Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField` does it.  The block identifying
  the base stalk `𝒪_{Spec K, strX x}` with `K` and transporting `PerfectField` across it is
  copied from that proof.
* `𝒪_{X,x}` NOT a field: it is a DVR by `hdvr`, and the leaf above applies.

`[IsIntegral X]` is present only so that `IsDiscreteValuationRing (X.presheaf.stalk x)` can
be STATED — that class carries `[IsDomain R]`. -/
theorem smooth_of_isDiscreteValuationRing_stalk_of_perfectField [PerfectField K]
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [LocallyOfFiniteType strX]
    (hdvr : ∀ x : X, ¬ IsField (X.presheaf.stalk x) →
      IsDiscreteValuationRing (X.presheaf.stalk x)) :
    Smooth strX := by
  have hlfp : LocallyOfFinitePresentation strX := inferInstance
  refine Scheme.Hom.smoothLocus_eq_top_iff.mp (le_antisymm le_top ?_)
  rintro x -
  have hess := LocallyOfFiniteType.stalkMap strX x
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(strX.stalkMap x).hom]
  -- the stalk of `Spec K` is a perfect field
  let K' := (Spec.structureSheaf K).presheaf.stalk (strX.base x)
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ (strX.base x).asIdeal.primeCompl
      (fun y hy ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic K K' := .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField K)).toField
  let : Field ((Spec (CommRingCat.of K)).presheaf.stalk (strX.base x)) := this
  have : PerfectField ((Spec (CommRingCat.of K)).presheaf.stalk (strX.base x)) :=
    Algebra.IsAlgebraic.perfectField (K := K) (L := K')
  by_cases hf : IsField (X.presheaf.stalk x)
  · let : Field ↥(X.presheaf.stalk x) := hf.toField
    exact Algebra.FormallySmooth.of_perfectField
  · haveI := hdvr x hf
    exact formallySmooth_of_isDiscreteValuationRing_of_perfectField

/-- **RELATIVE DIMENSION IS DETERMINED BY A DENSE OPEN, ON AN INTEGRAL SCHEME** (sorry leaf,
cut 2026-07-27 — the second and last residue of
`smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk`).

TRUE: on an integral scheme the relative dimension of a smooth morphism is constant, so it
is read off any nonempty open — a fortiori off a dense one.

**WHY IT IS NOT VACUOUS AND `[IsIntegral X]` CANNOT BE DROPPED.**  A disjoint union of a
smooth curve and a smooth surface over `K` is smooth, and its open curve part has relative
dimension `1` while the whole thing has no relative dimension at all.  Irreducibility is
what rules that out; `IsDominant j` is what makes `Y` meet every component (there is only
one) rather than merely being nonempty.

**THE ROUTE.**  `Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth`
(`Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean`) says that for a nontrivial
standard smooth `K`-algebra `A`, relative dimension `n` is EQUIVALENT to
`Module.rank A Ω[A⁄K] = n`.  So, given `Smooth strX`, the goal at a point `x` is to compute
the rank of `Ω` on an affine chart `V ∋ x`:

1. `Γ(X, V)` is a DOMAIN (`IsIntegral X`) and `Ω[Γ(X,V)⁄K]` is finite projective (smooth),
   so its rank is computed after inverting any nonzero element — rank is insensitive to
   localization at a multiplicative set for finite projective modules.
2. `V ∩ (range j)` is a nonempty open of `V` (dominance), so it contains a nonempty basic
   open `D(g) ⊆ V`, and `Γ(X, D(g)) = Γ(X,V)_g` is a localization.
3. On `D(g)` the morphism factors through `j`, so `hY` gives relative dimension `n` there,
   i.e. `Module.rank Γ(X,V)_g Ω = n`; by step 1 the rank over `Γ(X,V)` is the same, and
   `iff_of_isStandardSmooth` converts back.

No dimension theory and no Krull dimension is involved — only that the rank of a finite
projective module over a domain does not change under localization.

*Refute this leaf with:* an integral `X`, smooth over `K`, with a dense open of relative
dimension `n` and a point where the relative dimension is not `n`.  On an integral scheme
there is none. -/
theorem smoothOfRelativeDimension_of_isDominant_of_smooth {n : ℕ}
    {X Y : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [Smooth strX]
    (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hY : SmoothOfRelativeDimension n (j ≫ strX)) :
    SmoothOfRelativeDimension n strX :=
  sorry

/-- **A curve over a PERFECT field whose local rings are discrete valuation rings is smooth of
relative dimension one** (**PROVEN 2026-07-27** over the two leaves
`formallySmooth_of_isDiscreteValuationRing_of_perfectField` and
`smoothOfRelativeDimension_of_isDominant_of_smooth`; formerly a sorry leaf).

TRUE and classical (Stacks `056S`: over a perfect field, regular is equivalent to smooth).
A discrete valuation ring is a principal ideal domain, hence a regular local ring
(`instance [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] : IsRegularLocalRing R`, free
at this pin), so `hdvr` says exactly that `X` is regular; over a perfect field a regular
scheme of finite type is smooth, and the relative dimension is `1` because a dense open of `X`
is already smooth of relative dimension `1`.

**`PerfectField K` is load-bearing and the statement is FALSE without it.**  `ℚ` and `𝔽_ℓ`
are perfect, which is all either consumer needs.

**COUNTEREXAMPLE CORRECTED, 2026-07-28 — the witness this docstring used to cite was FALSE
IN BOTH CLAUSES.**  It read: "over an imperfect field `k` of characteristic `p` the curve
`y^p = t x^p + t` with `t ∈ k ∖ k^p` is regular — so all its local rings are DVRs — and is
not smooth."  In characteristic `p`, `t x^p + t = t (x + 1)^p`, so with `u = x + 1` the
equation is `y^p = t u^p`; the defining polynomial lies in `𝔪²` at the `k`-rational point
`u = y = 0` (checked in `Singular`), so that local ring has `dim_k 𝔪/𝔪² = 2` in dimension
one — it is **singular, not a DVR**, and the curve is not its own normalization
(its integral closure is the strictly larger `k(t^{1/p})[u]`).  It is also not
geometrically reduced (`(y − t^{1/p}(x+1))^p = 0` over `k̄`), so it has no smooth open
subscheme and cannot satisfy `hY` either.  **The failure is precisely on `hdvr`, the
hypothesis it was cited to illustrate**, so it justified nothing.

The correct witness is the classical **quasi-elliptic** curve (these exist only in
characteristics `2` and `3`).  Over `k = 𝔽₃(t)`, take `C : y² = x³ + t ⊆ 𝔸²_k`, let `X` be
its regular proper model and `Y := C ∖ {P}` where `P : y = 0, x³ = −t` is the unique
Jacobian-degenerate point (residue field `k(t^{1/3})`).

* `hdvr` **holds**: `C` is integral (`x³ + t` has odd degree, so it is not a square) and
  regular — in characteristic `3` the partials are `∂/∂y = 2y` and `∂/∂x = −3x² = 0`, so
  `P` is the only candidate, and there `𝔪 = (y, x³ + t) = (y)` because `x³ + t = y²`.  A
  one-dimensional local ring with principal maximal ideal is a DVR.
* `hY` and dominance **hold**: `Y` is a smooth affine curve over `k`, integral, and dense.
* The conclusion **fails**: over `k̄`, `x³ + t = (x + t^{1/3})³`, so `C ⊗ k̄` is the cuspidal
  cubic `y² = (x + t^{1/3})³` and `X` is not smooth at `P`.

Machine-checked in `Magma` (2026-07-28): `k(C)` has genus `1` over `𝔽₃(t)` with exact
constant field `k` — so `C` is geometrically integral, which the genus-preservation argument
needs — and genus `0` after the purely inseparable base change `t = s³`, a drop of
`(p−1)/2 = 1`, exactly what Tate's genus-change theorem permits at `p = 3`.

**The tempting repair is wrong too**, which is why `hY` does not let one drop the
hypothesis: `k(C)/k` **is** separably generated (`k(C)/k(x)` is separable of degree `2`), so
"smooth `Y` ⟹ separably generated function field ⟹ smooth `X`" is FALSE.  Separable
generation is strictly weaker than conservativity.  The same correction was applied to the
two unowned occurrences of the old witness, in
`smoothOfRelativeDimension_one_fromNormalization` (`CurveCompactification.lean`, where the
full worked version lives) and `smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing`
(`SmoothConnectedCriteria.lean`), on branch `flt-lean-272` (`45e2a43c`).

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
that is not a duplication.

**THE PROOF is now two lines**, and the split it exposes is the useful part of this pass:
smoothness and relative dimension are INDEPENDENT residues here.
`smooth_of_isDiscreteValuationRing_stalk_of_perfectField` gets `Smooth strX` out of `hdvr`
alone — `j` and `hY` are not used for it, which confirms the old docstring's observation
that `hdvr` cannot pin the relative dimension — and
`smoothOfRelativeDimension_of_isDominant_of_smooth` then upgrades that to relative dimension
`1` using `j` and `hY` alone, with no perfectness and no DVRs.  So neither of the two open
sub-leaves needs anything the other needs. -/
theorem smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk [PerfectField K]
    {X Y : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [LocallyOfFiniteType strX]
    (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j]
    (hY : SmoothOfRelativeDimension 1 (j ≫ strX))
    (hdvr : ∀ x : X, ¬ IsField (X.presheaf.stalk x) →
      IsDiscreteValuationRing (X.presheaf.stalk x)) :
    SmoothOfRelativeDimension 1 strX :=
  haveI : Smooth strX := smooth_of_isDiscreteValuationRing_stalk_of_perfectField strX hdvr
  smoothOfRelativeDimension_of_isDominant_of_smooth strX j hY

end AlgebraicGeometry
