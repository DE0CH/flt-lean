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
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic

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

Three things are left open here, and none of them mentions a modular curve.

| leaf | content |
| --- | --- |
| ✓ `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` | **PROVEN 2026-07-27**: smooth of relative dimension one over a field ⟹ the local rings away from the generic point are DVRs |
| `smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk` | the CONVERSE over a **perfect** field: DVR local rings ⟹ smooth of relative dimension one |
| `isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected` | smooth over a field + geometrically connected ⟹ integral |
| `infinite_of_smoothOfRelativeDimension_one` | a nonempty smooth curve over a field has infinitely many points |

**The first two are the two directions of ONE classical equivalence** ("regular ⟺ smooth
over a perfect field", in dimension one, where regular ⟺ DVR), and it is worth saying so
loudly because the task that produced this file was dispatched on the belief that the two
consumers shared a single *statement*.  They do not: `X0.lean` needs the forward direction
(it HAS smoothness and WANTS DVRs) and `CurveCompactification.lean` needs the backward one
(it HAS normality/DVRs and WANTS smoothness).  They share a file, a docstring and an owner,
which is what "build it once" can mean here; they are not the same theorem.  **The forward one
is now closed and the backward one is not, which is itself evidence for the distinction** — and
the forward proof does not run backwards, for the reason recorded on the converse below.

### The route that worked, and the route that was recommended and is wrong

The earlier version of this section told a prover of *either* direction to route through
`IsRegularLocalRing` and `IsLocalRing.finrank_CotangentSpace_eq_one_iff`, on the grounds that
"the whole of both leaves is smooth ⟺ regular (Stacks `00TT`, `056S`)".  **That advice is
withdrawn for the forward direction**: it is true mathematics and a bad plan, because the pin
has no lemma at all connecting `Algebra.Smooth` to `IsRegularLocalRing`, so following it means
developing the Jacobian criterion.

What closed the forward leaf instead is the **local structure theorem for smooth morphisms**,
which IS at this pin and which three successive audits of this file missed:

    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
      (n : ℕ) (R S) [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
      ∃ g : MvPolynomial (Fin n) R →ₐ[R] S, g.Etale

— every standard smooth algebra of relative dimension `n` is étale over affine `n`-space.  In
relative dimension one the base is `K[X]`, a principal ideal ring, and
`Algebra.FormallyUnramified.map_maximalIdeal` (Stacks `00UW`(1)) says an unramified local
homomorphism carries the maximal ideal ONTO the maximal ideal.  So the maximal ideal of every
stalk is the extension of a principal ideal, hence principal, and
`IsDiscreteValuationRing.TFAE` items 4 ↔ 0 finish.  No regularity, no cotangent space, no
dimension theory, and — as the statement demands — no perfectness.

The pieces are `isPrincipal_maximalIdeal_of_isStandardSmoothOfRelativeDimension_one` (the
ring-level content, with no schemes in it) and
`exists_isStandardSmoothOfRelativeDimension_isLocalization_stalk` (the chart bookkeeping,
with no algebra in it); both are `Mathlib`-shaped and reusable by the three leaves below.

`Mathlib` does have `IsRegularLocalRing` (`Mathlib/RingTheory/RegularLocalRing/Defs.lean`), so
the claim "there is no notion of regularity at this pin" remains refuted — it is just not the
abstraction that pays here.

**And the same local structure theorem makes "smooth over a field ⟹ regular local rings"
CONSTRUCTIBLE at this pin, in every relative dimension** — which matters outside this file,
because `Fermat/FLT/Modularity/AbelianSchemeIsogeny.lean` carries
`isRegularLocalRing_stalk_of_smooth` over exactly that gap (separate owner).  The missing
ingredient is not regularity theory; it is
`MvPolynomial.isRegularRing_of_isRegularRing` (`Mathlib/RingTheory/RegularLocalRing/Polynomial.lean`),
which says `MvPolynomial (Fin n) K` is a regular RING, so every `P_𝔮` is regular local.  Then
`Algebra.FormallyUnramified.map_maximalIdeal` bounds `(maximalIdeal A_p).spanFinrank` by
`(maximalIdeal P_𝔮).spanFinrank = ringKrullDim P_𝔮`, flatness of the étale map equates the two
Krull dimensions, and `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` closes it.  What is
still NOT available is `IsRegularLocalRing R → IsDomain R` (Auslander–Buchsbaum), a grep for
which returns nothing; that is why the irreducibility half of
`isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected` below stays open while its
reducedness half does not.

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

/-- **The image of a principal ideal under a ring homomorphism is principal.** -/
lemma isPrincipal_map_of_isPrincipal {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (I : Ideal R) [I.IsPrincipal] : (I.map f).IsPrincipal := by
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  exact ⟨f a, by rw [ha, Ideal.map_span, Set.image_singleton]⟩

/-- **Principality of the maximal ideal transfers along a ring isomorphism of local rings.** -/
lemma isPrincipal_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S)
    [(IsLocalRing.maximalIdeal R).IsPrincipal] :
    (IsLocalRing.maximalIdeal S).IsPrincipal := by
  have h1 : Ideal.comap (e : R →+* S) (IsLocalRing.maximalIdeal S) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ e.surjective)
  have h2 : Ideal.map (e : R →+* S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
    rw [← h1]
    exact Ideal.map_comap_of_surjective (e : R →+* S) e.surjective _
  rw [← h2]
  exact isPrincipal_map_of_isPrincipal _ _

/-- **A localization at a prime of a standard smooth `K`-algebra of relative dimension one has
principal maximal ideal** (PROVEN — this is the whole ring-theoretic content of
`isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one`).

The proof is the local structure theorem for smooth morphisms, not dimension theory and not
the cotangent space.  `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
factors `K → A` through `K[X₁] → A` with the second map **étale** — this is `Mathlib`'s form
of "a smooth morphism of relative dimension `n` is étale over affine `n`-space", and it is the
step that every "smooth ⟹ regular is absent from the pin" verdict on this leaf missed.  Then:

* `K[X₁] ≅ K[X]` is a principal ideal ring, so the contracted prime `𝔮 = p ∩ K[X₁]` is
  principal, and `Localization.AtPrime.map_eq_maximalIdeal` makes `𝔮 · K[X₁]_𝔮` the maximal
  ideal there;
* étale ⟹ `Algebra.FormallyUnramified`, and
  `Algebra.FormallyUnramified.map_maximalIdeal` (Stacks `00UW`(1)) says an unramified local
  homomorphism carries the maximal ideal ONTO the maximal ideal — so
  `m_{A_p} = 𝔮 · A_p` is principal because `𝔮` is.

No regularity theory, no Jacobian criterion, and no base change to `K̄` is needed; in
particular **no perfectness hypothesis appears**, as it must not, since the converse direction
is the one that needs it. -/
theorem isPrincipal_maximalIdeal_of_isStandardSmoothOfRelativeDimension_one
    {A S : Type u} [CommRing A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A] (p : Ideal A) [p.IsPrime]
    [CommRing S] [IsLocalRing S] [Algebra A S] [IsLocalization.AtPrime S p] :
    (IsLocalRing.maximalIdeal S).IsPrincipal := by
  classical
  haveI : IsPrincipalIdealRing (MvPolynomial (Fin 1) K) :=
    IsPrincipalIdealRing.of_surjective
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm.toRingEquiv
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm.surjective
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 K A
  letI : Algebra (MvPolynomial (Fin 1) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin 1) K) A := by
    rw [← RingHom.etale_algebraMap]
    rwa [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower K (MvPolynomial (Fin 1) K) A :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  set Q : Ideal (MvPolynomial (Fin 1) K) := p.comap (algebraMap (MvPolynomial (Fin 1) K) A) with hQ
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  haveI : p.LiesOver Q := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver Q p
  haveI : Algebra.FormallyUnramified (Localization.AtPrime Q) (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.localization_base Q.primeCompl
  haveI : Algebra.EssFiniteType (Localization.AtPrime Q) (Localization.AtPrime p) :=
    Algebra.EssFiniteType.of_comp (MvPolynomial (Fin 1) K) _ _
  have hmap : Ideal.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime p))
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        = IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hQmax : Ideal.map (algebraMap (MvPolynomial (Fin 1) K) (Localization.AtPrime Q)) Q
      = IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    Localization.AtPrime.map_eq_maximalIdeal
  haveI : Q.IsPrincipal := IsPrincipalIdealRing.principal Q
  haveI : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).IsPrincipal := by
    rw [← hQmax]; exact isPrincipal_map_of_isPrincipal _ _
  haveI : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).IsPrincipal := by
    rw [← hmap]; exact isPrincipal_map_of_isPrincipal _ _
  exact isPrincipal_maximalIdeal_of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) S).toRingEquiv

/-- **Every stalk of a scheme smooth of relative dimension `n` over a field is a localization at
a prime of a standard smooth `K`-algebra of relative dimension `n`** (PROVEN).

This is the chart bookkeeping that separates the scheme-theoretic side of the DVR leaf from its
commutative-algebra side.  Two small points do all the work: an affine open `U` of `Spec K`
that meets the image is `⊤`, because `Spec` of a field is a one-point space, so the source of
`strX.appLE U V e` is `Γ(Spec K, ⊤) ≅ K`; and `IsAffineOpen.isLocalization_stalk` identifies
`𝒪_{X,x}` with the localization of `Γ(X, V)` at `hV.primeIdealOf x`. -/
theorem exists_isStandardSmoothOfRelativeDimension_isLocalization_stalk {n : ℕ}
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension n strX] (x : X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A)
      (_ : Algebra.IsStandardSmoothOfRelativeDimension n K A)
      (p : Ideal A) (_ : p.IsPrime) (_ : Algebra A (X.presheaf.stalk x)),
      IsLocalization.AtPrime (X.presheaf.stalk x) p := by
  obtain ⟨U, hU, V, hV, hxV, e, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := strX) x
  haveI : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hUtop : U = ⊤ := by
    have hmem : strX.base x ∈ U := e hxV
    refine le_antisymm le_top fun y _ => ?_
    exact (Subsingleton.elim y (strX.base x)) ▸ hmem
  subst hUtop
  letI : Algebra K Γ(X, V) :=
    ((strX.appLE ⊤ V e).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.toRingHom).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap, RingHom.algebraMap_toAlgebra]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ _ hss
  exact ⟨Γ(X, V), inferInstance, inferInstance, inferInstance,
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal, inferInstance,
    TopCat.Presheaf.algebra_section_stalk X.presheaf (U := V) ⟨x, hxV⟩,
    hV.isLocalization_stalk ⟨x, hxV⟩⟩

/-- **A smooth curve over a field has discrete valuation rings as its local rings away from
the generic point** (PROVEN — no sorry, and no `PerfectField`).

Classically Stacks `00TT` + `00NP` ("smooth ⟹ regular", "regular local of dimension one ⟹
DVR").  That route was never taken here, and the docstring that recommended it was wrong about
where the difficulty lies: the pin has no link at all from smoothness to `IsRegularLocalRing`,
so following it would have meant developing the Jacobian criterion.

**What the proof actually uses is the LOCAL STRUCTURE THEOREM.**  A morphism smooth of relative
dimension one is, locally on the source, étale over the affine line
(`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`, which is at this pin
and which every earlier audit of this leaf missed).  Over the affine line the maximal ideals
are principal because `K[X]` is a PID, and an unramified local homomorphism maps the maximal
ideal ONTO the maximal ideal (`Algebra.FormallyUnramified.map_maximalIdeal`, Stacks `00UW`) —
so `m_x` is principal, and a noetherian local domain that is not a field with principal maximal
ideal is a discrete valuation ring
(`IsDiscreteValuationRing.TFAE`, items 4 ↔ 0).  See
`isPrincipal_maximalIdeal_of_isStandardSmoothOfRelativeDimension_one` for the ring-level
statement and `exists_isStandardSmoothOfRelativeDimension_isLocalization_stalk` for the chart
bookkeeping.

**`¬ IsField 𝒪_{X,x}` is exactly the right form of "`x` is not the generic point".**  At the
generic point of an integral `X` the stalk IS the function field, so it is a field and
`IsDiscreteValuationRing` is FALSE there (`IsDiscreteValuationRing` carries
`maximalIdeal R ≠ ⊥`).  Stating the exclusion as `¬ IsField` rather than as
`x ≠ genericPoint X` is what makes `valuationRing_stalk_of_smoothOfRelativeDimension_one`
below a two-line case split instead of a point-set argument.

**No perfectness is needed in this direction**, and the proof shows why: nothing in it looks at
residue fields.  It is only the converse
(`smoothOfRelativeDimension_one_of_isDiscreteValuationRing_stalk`) that needs `PerfectField K`,
and the module docstring records the counterexample. -/
theorem isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one
    {X : Scheme.{u}} (strX : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [SmoothOfRelativeDimension 1 strX] {x : X} (hx : ¬ IsField (X.presheaf.stalk x)) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  obtain ⟨A, _, _, _, p, _, _, _⟩ :=
    exists_isStandardSmoothOfRelativeDimension_isLocalization_stalk (n := 1) strX x
  haveI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 1)
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  haveI : IsNoetherianRing (X.presheaf.stalk x) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have hprin : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).IsPrincipal :=
    isPrincipal_maximalIdeal_of_isStandardSmoothOfRelativeDimension_one (K := K) p
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) hx).out 4 0).mp hprin

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

**ROUTE, established 2026-07-27 while proving the DVR leaf above; the two halves are NOT
equally hard and the old "reduced and normal, both from regularity" framing hid that.**

*Reduced — available at this pin, no regularity theory needed.*  Combine
`exists_isStandardSmoothOfRelativeDimension_isLocalization_stalk` (above) with
`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`: on a chart,
`A` is étale over `P = MvPolynomial (Fin n) K`.  Étale ⟹ `Module.Flat P A`, so with `P` a
domain the localization map `A → S⁻¹A` at `S = P ∖ {0}` is INJECTIVE; and `S⁻¹A` is étale over
the field `Frac P` by base change, hence `Algebra.FormallyUnramified (Frac P) (S⁻¹A)`, hence
reduced by `Algebra.FormallyUnramified.isReduced_of_field`
(`Mathlib/RingTheory/Unramified/Field.lean`).  A subring of a reduced ring is reduced.

*Irreducible — this is the blocking half, and it is what is genuinely absent.*  The classical
argument is "connected + normal ⟹ irreducible", and normality of `X` needs either
"regular ⟹ normal" (Serre; absent) or "étale over a normal domain is normal" (absent).  The
weaker "connected + all stalks are domains ⟹ irreducible" would do, but *stalks are domains*
is exactly "regular local rings are domains", also absent.

*Except in relative dimension ONE, where the blocking half unblocks.*  There
`isPrincipal_maximalIdeal_of_isStandardSmoothOfRelativeDimension_one` gives every stalk a
PRINCIPAL maximal ideal with no integrality hypothesis, and a **reduced** noetherian local ring
with principal maximal ideal is a field or a discrete valuation ring — in particular a domain —
because `⋂ mⁿ = ⊥` (Krull) forces every nonzero element to be `tⁿ · unit`.  So at `n = 1` the
route closes: reduced (above) ⟹ stalks are domains ⟹ locally irreducible ⟹ irreducible, given
connectedness.

So the sentence this paragraph replaces — "the relative dimension is left general (`n`), since
neither half of the argument sees it" — is **FALSE for the route that is actually available**:
the general-`n` statement needs theory that the pin does not have, and only `n = 1` is
attackable today.  The single consumer here,
`exists_unique_extension_of_isSmoothProperCurve`, instantiates at `n = 1`.  Specialising the
statement is a cut-level decision and has deliberately NOT been taken unilaterally; whoever
owns this next should either specialise it to `1` or accept the general-`n` obligation
knowingly. -/
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

**The paragraph that used to stand here — "`IsProper strX` is load-bearing" — was a leftover
from the pre-reconciliation form and is DELETED as false**: the signature carries no
`[IsProper strX]`, the reconciliation note above says why it must not, and the argument below
never uses it.

**ROUTE, surveyed 2026-07-27 against the pin.**  Two steps, both concrete; neither is at the
pin, and the second is the one worth knowing about because it is small.

1. *A nonempty chart is infinite.*  On a chart, `A` is standard smooth of relative dimension
   one and nontrivial, hence étale over `P = MvPolynomial (Fin 1) K ≅ K[X]`
   (`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`).  Étale gives
   `Module.Flat` and `Algebra.FinitePresentation`, so
   `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`
   (`Mathlib/RingTheory/Spectrum/Prime/Chevalley.lean`) makes the image of
   `Spec A → Spec K[X]` a NONEMPTY OPEN.  It therefore contains a basic open `D(f)` with
   `f ≠ 0`, and `Set.Infinite.of_image` transports infinitude back to `Spec A`.
2. *`D(f)` is infinite for `f ≠ 0` in `K[X]` — Euclid, and this is what the pin lacks.*  A grep
   for `Infinite (PrimeSpectrum _)`, `Set.Infinite … Irreducible` and the like returns NOTHING
   in `Mathlib`, so infinitude of the irreducibles of `K[X]` must be written here.  The form to
   write is the one that is directly usable: *for every finite `T ⊆ Spec K[X]` and every
   `f ≠ 0` there is a maximal ideal `M` with `f ∉ M` and `M ∉ T`* — take
   `g = f · ∏_{P ∈ T, P ≠ ⊥} generator P`, note `X · g + 1` has degree `≥ 1` so it is a nonzero
   nonunit, and any maximal `M ∋ X · g + 1` has `g ∉ M` (else `1 ∈ M`).  "Every finite subset is
   proper" then gives `Set.Infinite` directly, with no need for a separate
   `Infinite (PrimeSpectrum K[X])`.
3. *Chart to scheme.*  `IsAffineOpen.isoSpec` is a homeomorphism `↥V ≃ Spec Γ(X, V)`, and an
   open subspace injects into `X`.

An alternative to (1)+(2) that was considered and is WORSE: "finite `Spec A` + finite type over
`K` ⟹ `A` Artinian ⟹ `A` module-finite over `K`", contradicting `K[X] ↪ A`.  It replaces the
Euclid lemma with Jacobson-ring and Zariski-lemma plumbing, which is more of the pin, not
less. -/
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
that is not a duplication.

**THE FORWARD DIRECTION IS NOW PROVEN, AND ITS PROOF DOES NOT REVERSE** (2026-07-27).  That is
the single most useful fact for whoever attacks this leaf, because the natural reaction to
"the other direction closed" is to look for the same argument run backwards, and there is
none.  The forward proof is: *smooth of relative dimension one ⟹ locally étale over `K[X]`*
(`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`) *⟹ the maximal ideal
of every stalk is the extension of a principal ideal*
(`Algebra.FormallyUnramified.map_maximalIdeal`) *⟹ DVR*.  Every arrow there starts from a
PRESENTATION of `A` and reads off a property of its localizations.  This leaf is handed the
properties and must MANUFACTURE the presentation, which is a different and strictly harder
problem — it is Stacks `056S`, and the ingredient it needs is a criterion for smoothness in
terms of `Ω`, not a criterion for regularity.

**What the pin actually offers for this direction**, checked rather than assumed:

* `Algebra.FormallySmooth.of_perfectField` (`Mathlib/RingTheory/Smooth/Field.lean`) — a
  separable/perfect-base instance, and the ONLY place `PerfectField` meets smoothness at this
  pin.  It is about field extensions, not about local rings of a curve.
* `Algebra.Smooth.of_formallySmooth_fiber` and `Algebra.IsSmoothAt.of_formallySmooth_fiber`
  (`Mathlib/RingTheory/Smooth/Fiber.lean`), and `Algebra.smoothLocus` with
  `Algebra.smoothLocus_eq_univ_iff` / `Algebra.isOpen_smoothLocus`
  (`Mathlib/RingTheory/Smooth/Locus.lean`) — this is the right frame: smoothness is an OPEN
  condition and `smoothLocus_eq_compl_support_inter` expresses it as
  `H¹(L_{A/K})` vanishing together with freeness of `Ω[A/K]`.  So the shape of the obligation
  is: *from `hdvr`, prove `Ω[A_p ⁄ K]` free of rank one and `H¹(L_{A_p/K}) = 0`.*
* `Algebra.Etale.of_formallyUnramified_of_flat` — useful once the relative dimension has been
  cut down, not before.

**`IsRegularLocalRing` is NOT the useful abstraction for the FORWARD direction**, despite the
earlier docstrings (now corrected) that pointed at it.  For THIS direction it may well be, and
there is now a sibling to reuse rather than duplicate:

    Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean
      smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing
        (K B) [Field K] [PerfectField K] [IsDomain B] [Algebra.FiniteType K B] [IsRegularRing B]
        (n) (hdim : ringKrullDim B = n) : SmoothOfRelativeDimension n (Spec.map …)

landed in the release of 2026-07-27 with a **separate owner**.  That is the affine, ring-level
form of exactly this leaf's content — `PerfectField` and all — and it is still open there.  So
this leaf should be discharged BY it, not alongside it: the residue here is then the affine-chart
reduction plus the two translations `hdvr ⟹ IsRegularRing Γ(X, V)` (free: a DVR is a local PID,
and the instance `[IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] : IsRegularLocalRing R`
is at the pin) and `hY ⟹ ringKrullDim Γ(X, V) = 1`.  Check before starting that the sibling is
still open and still stated this way; a release can close or restate it. -/
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
