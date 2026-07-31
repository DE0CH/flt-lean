/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Fermat.FLT.Mathlib.AlgebraicGeometry.CurveExtension

/-!
# The affine line as a source for the valuative criterion

`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean` proves that a morphism from a
DENSE OPEN of a scheme whose stalks are valuation rings into a PROPER scheme extends
uniquely (`exists_unique_extension_of_valuationRing_stalk_of_isOpenImmersion`).  Applying
that with `𝔸¹_K` as the SOURCE is what turns "`P` is birational over `K` to `𝔸¹_K`" into an
honest morphism `𝔸¹_K ⟶ P`, and that is the missing half of the rationality dictionary in
`Fermat/FLT/ModularCurve/X0.lean`: the file already goes from a nonconstant `𝔸¹_K ⟶ P` to
`Scheme.BirationalOver` (Lüroth, `birationalOver_affineLine_of_isDominant`) and had nothing
going back.

The one input the extension theorem wants and that the pin does not supply is that the
stalks of `𝔸¹_K` are valuation rings.  `X0.lean`'s own audit (on
`exists_section_of_denseOpen_affineLine_toAbelianScheme`, 2026-07-28) recorded exactly this,
noting that `SmoothOfRelativeDimension 1 (𝔸(Unit; Spec K) ↘ Spec K)` is NOT an instance at
this pin and suggesting "give the `ValuationRing` stalks of `𝔸¹_K = Spec K[t]` directly
(localisations of a PID)".  That is what `valuationRing_stalk_affineLine` does, and it needs
no smoothness of affine space at all:

* `𝔸(Unit; Spec K) ≅ Spec K[X]` — `AffineSpace.SpecIso` composed with
  `MvPolynomial.uniqueAlgEquiv`;
* the stalk of `Spec R` at `y` is `Localization.AtPrime y.asIdeal`
  (`StructureSheaf.stalkIso`), and for `R = K[X]` that localisation is already a
  `ValuationRing` BY INSTANCE SEARCH at this pin (`K[X]` is a PID, hence a Dedekind domain,
  and `Mathlib` knows the localisation of a Dedekind domain at a prime is a DVR — or a
  field at the generic point);
* `ValuationRing` transports across the isomorphism through `IsBezout`, which does transfer
  along a surjective ring hom (`Function.Surjective.isBezout`), together with the
  `IsLocalRing` and `IsDomain` instances that every stalk of an integral scheme carries.
  Going through `IsBezout` avoids needing a `ValuationRing`-transport lemma, which the pin
  does not have.

## Contents

* `valuationRing_stalk_of_iso`, `valuationRing_stalk_spec_polynomial`,
  `affineLineIsoSpecPolynomial`, `valuationRing_stalk_affineLine` — the stalk input.
* `isSplitEpi_affineLine_over` — `𝔸(n; S) ↘ S` has a section (the origin), hence is an
  epimorphism.  Used to cancel it on the left.
* `exists_hom_affineLine_of_birationalOver` — the extension itself: a proper `P` birational
  over `K` to `𝔸¹_K` receives a `K`-morphism from the WHOLE affine line whose range is
  dense.
* `ne_comp_section_of_dense_range` — such a morphism is NONCONSTANT, i.e. does not factor
  through a `K`-point.  Here properness (through separatedness) and
  `SmoothOfRelativeDimension 1` are used: the image of a section of a separated morphism is
  closed, a closed dense set is everything, and a smooth curve over a field is infinite
  (`infinite_of_smoothOfRelativeDimension_one`).

## Finiteness of a map to the affine line from the FULL domain of definition (2026-07-31)

The second half of this file is the FINITENESS obligation of
`hasDoubleCoverOfAffineLine_of_iso_sectionIdeal` in `X0.lean` — obligation 2 of the route
correction recorded on that declaration.  Everything here is sorry-free.

* `IsValuativelyFull strX ι φ π` — the honest content of "`U` is the WHOLE locus on which
  `φ` is defined", stated valuatively and with no divisor, no `ℙ¹` and no degree: whenever a
  valuation ring `R` carries a point `ψ : Spec R ⟶ X` whose generic point already lies in
  `U`, and whose `φ`-VALUE lies in `R` (that is the `i₂` datum, and it is exactly "`f` is
  regular there"), the whole of `Spec R` lies in `U`.
* `valuativeCriterion_existence_of_isValuativelyFull` — that condition plus properness of
  `strX` gives the existence half of the valuative criterion for `φ` itself.  Properness of
  `strX` supplies the centre `ψ`; `IsValuativelyFull` puts it in `U`; the monomorphism `ι`
  and the SEPARATEDNESS of `π` (uniqueness half, `IsSeparated.valuativeCriterion`) identify
  the two triangles.
* `isFinite_of_isValuativelyFull` / `isFinite_toAffineLine_of_isValuativelyFull` — `IsFinite
  φ`.  Separatedness, quasi-compactness, quasi-separatedness and finite type of `φ` all
  descend from `ι ≫ strX = φ ≫ π` by the standard cancellation lemmas; universal closedness
  is the valuative criterion above; and `IsFinite = IsProper ⊓ LocallyQuasiFinite` is
  `Mathlib`'s `IsFinite.of_isProper_of_locallyQuasiFinite` (Zariski's main theorem, which
  the pin HAS — `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`).

**No degree theory, no `h⁰`, no linear system and no `ℙ¹` is used anywhere in this half.**
That is the point: every earlier audit of the `g¹₂` leaf costed its finiteness clause at
Riemann–Roch, and the true cost is the four cancellation lemmas plus one theorem that was
already in the pin.

Everything here is sorry-free.
-/

@[expose] public section

-- (universe `0`: `𝔸(n; S)` ties the index type's universe to the base's, and `Unit : Type`,
-- so every statement below is at `Scheme.{0}` — which is also where `X0.lean` lives.)

open CategoryTheory AlgebraicGeometry TopologicalSpace CategoryTheory.Limits

open scoped Polynomial

namespace AlgebraicGeometry

variable (K : Type) [Field K]

/-! ### Valuation rings as stalks of the affine line -/

/-- **`ValuationRing` stalks transport along an isomorphism of schemes** (PROVEN).

Transport is done through `IsBezout` rather than through `ValuationRing` itself, because
`Mathlib` has `Function.Surjective.isBezout` but no `ValuationRing`-along-a-surjection
lemma, and `ValuationRing` is recovered from `IsLocalRing` + `IsBezout` + `IsDomain`, all
three of which a stalk of an integral scheme has for free. -/
theorem valuationRing_stalk_of_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y)
    (h : ∀ y : Y, ValuationRing (Y.presheaf.stalk y)) (x : X) :
    ValuationRing (X.presheaf.stalk x) := by
  haveI := h (e.hom.base x)
  haveI : IsBezout (Y.presheaf.stalk (e.hom.base x)) := inferInstance
  have hsurj : Function.Surjective (e.hom.stalkMap x).hom :=
    ((ConcreteCategory.isIso_iff_bijective (e.hom.stalkMap x)).mp inferInstance).2
  haveI : IsBezout (X.presheaf.stalk x) := hsurj.isBezout (e.hom.stalkMap x).hom
  infer_instance

/-- **Every stalk of `Spec K[X]` is a valuation ring** (PROVEN).

`StructureSheaf.stalkIso` identifies the stalk with `Localization.AtPrime`, and instance
search already knows that a localisation of `K[X]` at a prime is a valuation ring: `K[X]` is
a PID, hence Dedekind, so the localisation is a DVR away from the generic point and the
fraction field at it. -/
theorem valuationRing_stalk_spec_polynomial (y : Spec (CommRingCat.of K[X])) :
    ValuationRing ((Spec (CommRingCat.of K[X])).presheaf.stalk y) := by
  have e := (StructureSheaf.stalkIso (CommRingCat.of K[X]) y).toRingEquiv
  haveI : IsBezout (Localization.AtPrime y.asIdeal) := inferInstance
  haveI : IsBezout ((Spec (CommRingCat.of K[X])).presheaf.stalk y) :=
    e.surjective.isBezout e.toRingHom
  infer_instance

/-- **`𝔸¹_K ≅ Spec K[X]`** — `AffineSpace.SpecIso` followed by
`MvPolynomial.uniqueAlgEquiv`, which identifies `MvPolynomial Unit K` with `K[X]`. -/
noncomputable def affineLineIsoSpecPolynomial :
    𝔸(Unit; Spec (CommRingCat.of K)) ≅ Spec (CommRingCat.of K[X]) :=
  AffineSpace.SpecIso Unit (CommRingCat.of K) ≪≫
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
      (MvPolynomial.uniqueAlgEquiv K Unit).toRingEquiv).symm.op

/-- **Every stalk of the affine line over a field is a valuation ring** (PROVEN).

This is the hypothesis of `exists_unique_extension_of_valuationRing_stalk_of_isOpenImmersion`
with the affine line as SOURCE, and it is what
`Fermat/FLT/ModularCurve/X0.lean`'s audit of
`exists_section_of_denseOpen_affineLine_toAbelianScheme` named as the cheapest missing piece
("prove smoothness of the affine line, or give the `ValuationRing` stalks of
`𝔸¹_K = Spec K[t]` directly").  The second route is taken here, so
`SmoothOfRelativeDimension 1 (𝔸(Unit; Spec K) ↘ Spec K)` — still not an instance at this
pin — is not needed. -/
theorem valuationRing_stalk_affineLine (x : 𝔸(Unit; Spec (CommRingCat.of K))) :
    ValuationRing ((𝔸(Unit; Spec (CommRingCat.of K))).presheaf.stalk x) :=
  valuationRing_stalk_of_iso (affineLineIsoSpecPolynomial K)
    (valuationRing_stalk_spec_polynomial K) x

/-! ### The affine line is a split epimorphism over its base -/

/-- **`𝔸¹_S ↘ S` is a split epimorphism**, split by the ORIGIN (PROVEN).

Consequently it may be cancelled on the left, which is what turns "`u` lies over `k`" into
"the `K`-point `s` produced by `HasNoFibreAffineLine` lies over `k`". -/
theorem isSplitEpi_affineLine_over :
    IsSplitEpi (𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) :=
  ⟨⟨AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of K)))
      (fun _ : Unit => (0 : Γ(Spec (CommRingCat.of K), ⊤))),
    AffineSpace.homOfVector_over _ _⟩⟩

/-! ### From birationality to a morphism out of the whole affine line -/

/-- **A proper `K`-scheme birational over `K` to `𝔸¹_K` receives a `K`-morphism from the
WHOLE affine line, with dense range** (PROVEN).

This is the converse of `birationalOver_affineLine_of_isDominant` (Lüroth) and the reason
`Scheme.BirationalOver _ (𝔸¹ ↘ Spec K)` may be used as the STATEMENT of "this curve is
rational" even where the consumer needs an actual morphism out of `𝔸¹_K`.

`hrat` gives a partial isomorphism between a dense open `f.source ⊆ P` and a dense open
`f.target ⊆ 𝔸¹_K`.  Transporting backwards along `f.iso` gives a `K`-morphism
`f.target ⟶ P`; `f.target` is a dense open of `𝔸¹_K`, whose stalks are valuation rings by
`valuationRing_stalk_affineLine` and which is integral by instance, and `P` is proper, so
`exists_unique_extension_of_valuationRing_stalk_of_isOpenImmersion` extends it to `𝔸¹_K`.
The extension restricts to the original map on `f.target`, so its range contains
`f.source`, which is dense.

**PROPERNESS OF `P` IS LOAD-BEARING and the statement is FALSE without it**: take
`P = 𝔸¹_K ∖ {0}`, which is birational over `K` to `𝔸¹_K` (it is a dense open of it) but
receives only constant `K`-morphisms from `𝔸¹_K` — a morphism `𝔸¹_K ⟶ 𝔾ₘ,K` is a unit of
`K[t]`, hence a constant — and a constant has range a single point, which is not dense in
the infinite `P`.  So no `Φ` with dense range exists there. -/
theorem exists_hom_affineLine_of_birationalOver {P : Scheme.{0}}
    {strP : P ⟶ Spec (CommRingCat.of K)} [IsProper strP]
    (hrat : Scheme.BirationalOver strP
      (𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))) :
    ∃ Φ : 𝔸(Unit; Spec (CommRingCat.of K)) ⟶ P,
      Φ ≫ strP = 𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) ∧
      Dense (Set.range Φ.base) := by
  obtain ⟨f, hf⟩ := hrat
  haveI : IsDominant f.target.ι := Opens.isDominant_ι f.dense_target
  have hφ : (f.iso.inv ≫ f.source.ι) ≫ strP
      = f.target.ι ≫ (𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
    rw [Category.assoc, ← hf, ← Category.assoc, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  obtain ⟨Φ, ⟨h1, h2⟩, -⟩ :=
    exists_unique_extension_of_valuationRing_stalk_of_isOpenImmersion
      (K := K) (strX := 𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
      (strZ := strP) (valuationRing_stalk_affineLine K) (f.iso.inv ≫ f.source.ι) hφ
  refine ⟨Φ, h1, ?_⟩
  have hmem : Set.range (f.iso.inv ≫ f.source.ι).base ⊆ Set.range Φ.base := by
    rw [← h2]
    rintro w ⟨v, rfl⟩
    exact ⟨f.target.ι.base v, rfl⟩
  have hsub : (f.source : Set P) ⊆ Set.range Φ.base := by
    intro z hz
    refine hmem ⟨f.iso.hom.base ⟨z, hz⟩, ?_⟩
    have hid : f.iso.hom ≫ f.iso.inv ≫ f.source.ι = f.source.ι := by
      rw [Iso.hom_inv_id_assoc]
    have h := congrArg (fun g : f.source.toScheme ⟶ P => g.base ⟨z, hz⟩) hid
    simp only [] at h
    exact h
  exact f.dense_source.mono hsub

/-- **A `K`-morphism `𝔸¹_K ⟶ P` with DENSE RANGE into a smooth separated curve is
NONCONSTANT** (PROVEN) — it factors through no `K`-point of `P`.

If `Φ = π ≫ s` then `s` is a section of `strP` (cancel the split epi `π`), hence a closed
immersion (`IsClosedImmersion.of_comp` against the separated `strP`), so its range is a
CLOSED subsingleton containing the dense range of `Φ`; a closed dense set is everything, so
`P` would have exactly one point.  That contradicts
`infinite_of_smoothOfRelativeDimension_one`.

**`SmoothOfRelativeDimension 1 strP` IS LOAD-BEARING and only through infiniteness**: for
`P = Spec K` and `strP = 𝟙` every `Φ` equals `π ≫ 𝟙`, and `Φ` does have dense range, so the
conclusion is false there.  `IsSeparated strP` is load-bearing too: it is what makes the
image of `s` closed, and without it a dense one-point image is not a contradiction. -/
theorem ne_comp_section_of_dense_range {P : Scheme.{0}} {strP : P ⟶ Spec (CommRingCat.of K)}
    [IsSeparated strP] [SmoothOfRelativeDimension 1 strP]
    (Φ : 𝔸(Unit; Spec (CommRingCat.of K)) ⟶ P)
    (hΦ : Φ ≫ strP = 𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
    (hdense : Dense (Set.range Φ.base)) (s : Spec (CommRingCat.of K) ⟶ P) :
    Φ ≠ (𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) ≫ s := by
  intro hΦs
  haveI := isSplitEpi_affineLine_over K
  haveI : Nonempty P := by
    obtain ⟨x⟩ : Nonempty (𝔸(Unit; Spec (CommRingCat.of K))) := inferInstance
    exact ⟨Φ.base x⟩
  haveI : Infinite P := infinite_of_smoothOfRelativeDimension_one strP
  have hs : s ≫ strP = 𝟙 _ := by
    have h := hΦ
    rw [hΦs, Category.assoc] at h
    exact (cancel_epi (𝔸(Unit; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))).mp
      (by rw [h, Category.comp_id])
  haveI : IsClosedImmersion s := by
    have h : IsClosedImmersion (s ≫ strP) := by rw [hs]; infer_instance
    exact IsClosedImmersion.of_comp s strP
  have hclosed : IsClosed (Set.range s.base) := s.isClosedEmbedding.isClosed_range
  haveI : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hsub : (Set.range s.base).Subsingleton := by
    rintro a ⟨u, rfl⟩ b ⟨v, rfl⟩
    exact congrArg _ (Subsingleton.elim u v)
  have hle : Set.range Φ.base ⊆ Set.range s.base := by
    rw [hΦs]
    rintro w ⟨v, rfl⟩
    exact ⟨_, rfl⟩
  have huniv : Set.range s.base = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hclosed.closure_eq]
    exact hdense.closure_eq ▸ closure_mono hle
  haveI : Subsingleton P := ⟨fun a b => hsub (huniv ▸ Set.mem_univ a) (huniv ▸ Set.mem_univ b)⟩
  haveI : Finite P := Finite.of_subsingleton
  exact not_finite P

/-! ### Finiteness of a morphism to the affine line from its full domain of definition

See the module docstring.  This section is the FINITENESS obligation of the `g¹₂` leaf
`hasDoubleCoverOfAffineLine_of_iso_sectionIdeal` in `X0.lean`, discharged with no degree
theory, no `h⁰`, no linear system and no projective line. -/

section Finiteness

universe u

variable {X U A B : Scheme.{u}} {strX : X ⟶ B} {ι : U ⟶ X} {φ : U ⟶ A} {π : A ⟶ B}

/-- **`U` IS THE WHOLE LOCUS ON WHICH `φ` IS DEFINED**, stated valuatively.

`ι : U ⟶ X` is an open immersion and `φ : U ⟶ A` a morphism over `B`.  The condition says:
if a valuation ring `R` with fraction field `K` carries

* a `K`-point `i₁` of `U`,
* an `R`-point `i₂` of `A` extending its `φ`-image (`i₁ ≫ φ = Spec K ⟶ Spec R ≫ i₂` — this
  is the clause that says the VALUE of `φ` is regular, i.e. lies in `R` and not merely in
  `K`), and
* an `R`-point `ψ` of `X` extending `i₁ ≫ ι` and lying over `i₂`,

then `ψ` already factors through `U`.

**This is the ℙ¹-free form of "`U` is the full preimage of `A`".**  In the intended
application `X` is a smooth proper curve, `f` a rational function on it, `U = X ∖ (poles of
f)` and `A = 𝔸¹`; the condition is then the classical statement that the centre of a
valuation at which `f` is regular is not a pole of `f`, which for a curve is the maximality
of a DVR among the proper subrings of its fraction field.

**FALSITY AUDIT.**  The condition is a HYPOTHESIS here, not a claim, so there is nothing to
refute; what matters is that it is not vacuous and not automatic.

* *Not automatic*: take `X = ℙ¹_ℚ`, `U = 𝔸¹ ∖ {0}`, `φ` the inclusion into `𝔸¹`.  Let `R` be
  the local ring of `ℙ¹` at `0` and `K = ℚ(t)`.  Then `i₁` is the generic point of `U`, `i₂`
  is the inclusion `Spec R ⟶ 𝔸¹` (the coordinate `t` IS in `R`), `ψ` is the corresponding
  `R`-point of `ℙ¹` — and `ψ` does NOT factor through `U`, because its centre is `0 ∉ U`.
  Correspondingly `φ` is an open immersion and NOT finite, so the conclusion of
  `isFinite_of_isValuativelyFull` genuinely fails there.  The hypothesis is doing work.
* *Not vacuous*: with the same `X` and `φ` but `U = 𝔸¹` (so `X ∖ U = {∞}`) the condition
  holds, since `t ∈ R` forbids the centre `∞`.

**The `i₁ ≫ φ = … ≫ i₂` clause is load-bearing and dropping it makes the condition FALSE for
every proper `X` with `U ≠ X`.**  Without it one could take `i₂` arbitrary and `ψ` any
valuative lift with centre in `X ∖ U`, of which a proper `X` has many. -/
def IsValuativelyFull (strX : X ⟶ B) (ι : U ⟶ X) (φ : U ⟶ A) (π : A ⟶ B) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
    (i₁ : Spec (CommRingCat.of F) ⟶ U) (i₂ : Spec (CommRingCat.of R) ⟶ A)
    (ψ : Spec (CommRingCat.of R) ⟶ X),
    i₁ ≫ φ = Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ i₂ →
    Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ ψ = i₁ ≫ ι →
    ψ ≫ strX = i₂ ≫ π →
    ∃ l : Spec (CommRingCat.of R) ⟶ U, l ≫ ι = ψ

/-- A proper morphism satisfies the valuative criterion (`Mathlib`'s
`IsProper.eq_valuativeCriterion`, projected out of the `MorphismProperty` inf). -/
theorem valuativeCriterion_of_isProper (f : X ⟶ B) [IsProper f] : ValuativeCriterion f := by
  have h : ((ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓
      @LocallyOfFiniteType : MorphismProperty Scheme)) f := by
    rw [← IsProper.eq_valuativeCriterion]; exact ‹IsProper f›
  exact h.1.1.1

/-- The EXISTENCE half of the valuative criterion for a proper morphism, unbundled from
`ValuativeCommSq` so that the ring and field are ordinary binders. -/
theorem exists_lift_of_isProper {R F : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] (f : X ⟶ B) [IsProper f]
    (i₁ : Spec (CommRingCat.of F) ⟶ X) (i₂ : Spec (CommRingCat.of R) ⟶ B)
    (w : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ i₂) :
    ∃ ψ : Spec (CommRingCat.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ ψ = i₁ ∧ ψ ≫ f = i₂ := by
  obtain ⟨ψ, h₁, h₂⟩ := (valuativeCriterion_of_isProper f ⟨R, F, i₁, i₂, ⟨w⟩⟩).some.default
  exact ⟨ψ, h₁, h₂⟩

/-- The UNIQUENESS half of the valuative criterion for a separated morphism, unbundled from
`ValuativeCommSq` in the same way. -/
theorem eq_of_isSeparated_of_lift {R F : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] (f : X ⟶ B) [IsSeparated f]
    (i₁ : Spec (CommRingCat.of F) ⟶ X) (i₂ : Spec (CommRingCat.of R) ⟶ B)
    (w : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ i₂)
    (l₁ l₂ : Spec (CommRingCat.of R) ⟶ X)
    (h₁ : Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ l₁ = i₁) (h₁' : l₁ ≫ f = i₂)
    (h₂ : Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ l₂ = i₁) (h₂' : l₂ ≫ f = i₂) :
    l₁ = l₂ :=
  congrArg CommSq.LiftStruct.l
    ((IsSeparated.valuativeCriterion f ⟨R, F, i₁, i₂, ⟨w⟩⟩).elim ⟨l₁, h₁, h₁'⟩ ⟨l₂, h₂, h₂'⟩)

/-- **A MORPHISM DEFINED ON ITS FULL DOMAIN, OVER A PROPER BASE, IS UNIVERSALLY CLOSED**
(PROVEN 2026-07-31) — the existence half of the valuative criterion for `φ` itself.

Given `ι ≫ strX = φ ≫ π` with `strX` proper, `ι` an open immersion and `π` separated: a
valuative square over `φ` is pushed into `X` by `ι` and `π`, properness of `strX` produces
the centre `ψ`, `IsValuativelyFull` puts `ψ` inside `U`, `ι` being a monomorphism identifies
the upper triangle, and the uniqueness half of the valuative criterion for the SEPARATED `π`
identifies the lower one. -/
theorem valuativeCriterion_existence_of_isValuativelyFull
    [IsProper strX] [IsOpenImmersion ι] [IsSeparated π]
    (hcomm : φ ≫ π = ι ≫ strX) (hfull : IsValuativelyFull strX ι φ π) :
    ValuativeCriterion.Existence φ := by
  intro sq
  have hwX : (sq.i₁ ≫ ι) ≫ strX =
      Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ (sq.i₂ ≫ π) := by
    rw [Category.assoc, ← hcomm, ← Category.assoc, ← Category.assoc, sq.commSq.w]
  obtain ⟨ψ, hψ₁, hψ₂⟩ := exists_lift_of_isProper strX (sq.i₁ ≫ ι) (sq.i₂ ≫ π) hwX
  obtain ⟨l, hl⟩ := hfull sq.R sq.K sq.i₁ sq.i₂ ψ sq.commSq.w hψ₁ hψ₂
  have hl₁ : Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ l = sq.i₁ := by
    refine (cancel_mono ι).mp ?_
    rw [Category.assoc, hl]; exact hψ₁
  refine ⟨⟨⟨l, hl₁, ?_⟩⟩⟩
  have hwA : (sq.i₁ ≫ φ) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ (ψ ≫ strX) := by
    rw [Category.assoc, hcomm, ← Category.assoc, ← Category.assoc, hψ₁]
  exact eq_of_isSeparated_of_lift π (sq.i₁ ≫ φ) (ψ ≫ strX) hwA (l ≫ φ) sq.i₂
    (by rw [← Category.assoc, hl₁]) (by rw [Category.assoc, hcomm, ← Category.assoc, hl])
    sq.commSq.w.symm hψ₂.symm

/-- **A QUASI-FINITE MORPHISM DEFINED ON ITS FULL DOMAIN, OVER A PROPER BASE, IS FINITE**
(PROVEN 2026-07-31).

Everything except universal closedness descends from `ι ≫ strX = φ ≫ π` by the standard
cancellation lemmas (`IsSeparated.of_comp`, `QuasiSeparated.of_comp`, `QuasiCompact.of_comp`,
`locallyOfFiniteType_of_comp`); universal closedness is
`valuativeCriterion_existence_of_isValuativelyFull`; and `IsProper ⊓ LocallyQuasiFinite =
IsFinite` is `Mathlib`'s `IsFinite.of_isProper_of_locallyQuasiFinite` — Zariski's main
theorem, which this pin HAS.

**FALSITY AUDIT.**  Each hypothesis is refuted by an explicit witness.

* `IsValuativelyFull` — `X = ℙ¹_ℚ`, `U = 𝔸¹ ∖ {0}`, `φ` the inclusion: quasi-finite,
  quasi-compact, over a proper `X`, and NOT finite (it is an open immersion with dense
  non-closed image).  See the audit on `IsValuativelyFull`.
* `LocallyQuasiFinite φ` — `X = U = 𝔸¹_ℚ ×_ℚ E` for an elliptic curve `E`... more simply,
  `U = X` proper over `B` with `φ` the constant map to the origin of `A = 𝔸¹`: then `U` is
  the full domain vacuously, `φ` is proper, and `φ` is finite only if `X ⟶ B` is, which
  fails for any positive-dimensional proper `X`.
* `IsProper strX` — with `strX` merely separated one may take `X = U = 𝔸¹`, `φ = 𝟙`; that is
  finite, so the failure is not visible there, but with `X = U = 𝔸²` and `φ` a coordinate
  projection every other hypothesis except quasi-finiteness holds.  Properness is what
  supplies the centre `ψ` and there is no substitute for it.
* `QuasiCompact ι` — needed to run `UniversallyClosed.of_valuativeCriterion`, and it is a
  genuine restriction only for an open `U` that is not quasi-compact, which cannot happen
  when `X` is noetherian; it is a hypothesis here rather than a derivation because
  noetherianness of `X` is not available at this generality. -/
theorem isFinite_of_isValuativelyFull
    [IsProper strX] [IsOpenImmersion ι] [QuasiCompact ι] [IsSeparated π]
    [LocallyQuasiFinite φ]
    (hcomm : φ ≫ π = ι ≫ strX) (hfull : IsValuativelyFull strX ι φ π) :
    IsFinite φ := by
  have h1 : LocallyOfFiniteType (φ ≫ π) := by rw [hcomm]; infer_instance
  have : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ π
  have h2 : QuasiSeparated (φ ≫ π) := by rw [hcomm]; infer_instance
  have : QuasiSeparated φ := QuasiSeparated.of_comp φ π
  have h3 : QuasiCompact (φ ≫ π) := by rw [hcomm]; infer_instance
  have : QuasiCompact φ := QuasiCompact.of_comp φ π
  have h4 : IsSeparated (φ ≫ π) := by rw [hcomm]; infer_instance
  have : IsSeparated φ := IsSeparated.of_comp φ π
  have : UniversallyClosed φ :=
    UniversallyClosed.of_valuativeCriterion φ
      (valuativeCriterion_existence_of_isValuativelyFull hcomm hfull)
  have : IsProper φ := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ

/-- `isFinite_of_isValuativelyFull` at the affine line, where the separatedness of the
structure morphism is automatic (`𝔸(n; B) ↘ B` is an affine morphism). -/
theorem isFinite_toAffineLine_of_isValuativelyFull {n : Type u} {X U B : Scheme.{u}}
    {strX : X ⟶ B} {ι : U ⟶ X} {φ : U ⟶ 𝔸(n; B)}
    [IsProper strX] [IsOpenImmersion ι] [QuasiCompact ι] [LocallyQuasiFinite φ]
    (hcomm : φ ≫ (𝔸(n; B) ↘ B) = ι ≫ strX)
    (hfull : IsValuativelyFull strX ι φ (𝔸(n; B) ↘ B)) :
    IsFinite φ :=
  have : IsSeparated (𝔸(n; B) ↘ B) := IsSeparated.of_isAffineHom _
  isFinite_of_isValuativelyFull hcomm hfull

end Finiteness

end AlgebraicGeometry
