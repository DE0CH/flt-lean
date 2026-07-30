/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.FinrankGeometricPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Support
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# A finite flat morphism with REDUCED geometric fibres is étale

This is the "fibrewise criterion" half of the finite-flat/étale dictionary, and the exact
complement of `Fermat/FLT/Mathlib/AlgebraicGeometry/FinrankGeometricPoints.lean`: that file turns
a rank computation into reducedness of a geometric fibre, and this one turns reducedness of every
geometric fibre into étaleness of the morphism.

**Everything in this file is PROVEN; it contains no `sorry`.**

* `AlgebraicGeometry.etale_of_isReduced_pullback` — the headline statement, assembled from the two
  halves below.
* `AlgebraicGeometry.etale_of_etale_fiberToSpecResidueField` — the *fibrewise criterion*: finite,
  flat, locally of finite presentation with ÉTALE fibres ⟹ étale.  Mathlib has only the smooth
  analogue (`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`), and `Smooth` cannot be
  upgraded to `Etale` without a relative-dimension input unavailable here — so this goes through
  `Algebra.Etale.of_formallyUnramified_of_flat` instead, with no smoothness anywhere.
* `AlgebraicGeometry.etale_fiberToSpecResidueField_of_isReduced_pullback` — *descent* of étaleness
  of the fibre from `κ(y)‾` down to `κ(y)`.
* `Algebra.FormallyUnramified.of_formallyUnramified_fiber` and
  `Algebra.Etale.of_isReduced_of_isAlgClosed` — the two general commutative-algebra facts the
  above rest on, both absent from mathlib.
* `AlgebraicGeometry.isNilpotent_ker_SpecMap` — a small proven bridge: `Spec` of a ring map with
  nilpotent kernel is an infinitesimal thickening in the sense
  `AlgebraicGeometry.FormallyUnramified.hom_ext` wants.
* `AlgebraicGeometry.isReduced_of_formallyUnramified_over_field` — the tool a CONSUMER needs to
  DISCHARGE the `hred` hypothesis of the headline: an affine scheme, of finite type and formally
  unramified over a field, is reduced.  It is the scheme-level form of mathlib's
  `Algebra.FormallyUnramified.isReduced_of_field` and points the other way from everything else
  here, so it is stated at the end rather than folded into the assembly.

**No characteristic hypothesis appears anywhere here, and none is needed**: over `𝔽_p`,
`ker F ⊆ 𝔾ₐ` is finite flat and NOT étale, but its geometric fibre `Spec 𝔽̄_p[x]/(x^p)` is not
reduced, so the hypothesis is unsatisfiable there rather than being false.  The characteristic
enters only where a CONSUMER proves reducedness (over a `ℚ`-base, by Cartier).
-/

@[expose] public section

open CategoryTheory Limits

open scoped TensorProduct

universe u

section FormallyUnramifiedFiber

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **A module-finite algebra whose every fibre `κ(p) ⊗[R] S` is formally unramified over `κ(p)`
is formally unramified.**

This is the commutative-algebra core of `AlgebraicGeometry.etale_of_etale_fiberToSpecResidueField`,
and mathlib has no fibrewise criterion for unramifiedness (it has one for smoothness,
`Algebra.Smooth.of_formallySmooth_fiber`).

The proof is `Subsingleton Ω[S⁄R]` by Nakayama.  `Ω[S⁄R]` is a finite `S`-module, hence a finite
`R`-module because `S` is module-finite over `R`, so `Module.support_eq_empty_iff` and
`Module.mem_support_iff_nontrivial_residueField_tensorProduct` reduce vanishing to vanishing of
`κ(p) ⊗[R] Ω[S⁄R]` at every prime `p` — and that is `Ω[(κ(p) ⊗[R] S)⁄κ(p)]` by base change of
Kähler differentials (`KaehlerDifferential.tensorKaehlerEquivBase`, over the pushout instance
`Algebra.IsPushout R κ(p) S (κ(p) ⊗[R] S)`), which vanishes by hypothesis.

Module-finiteness is what makes the *R*-side support argument available; it is exactly what a
FINITE morphism of schemes supplies. -/
theorem Algebra.FormallyUnramified.of_formallyUnramified_fiber
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FiniteType R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], Algebra.FormallyUnramified p.ResidueField (p.Fiber S)) :
    Algebra.FormallyUnramified R S := by
  rw [Algebra.formallyUnramified_iff]
  have hfin : Module.Finite R (Ω[S⁄R]) := Module.Finite.trans S _
  rw [← Module.support_eq_empty_iff (R := R)]
  refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  have h1 := H p.asIdeal
  rw [Algebra.formallyUnramified_iff] at h1
  haveI := h1
  have e := KaehlerDifferential.tensorKaehlerEquivBase R p.asIdeal.ResidueField S
      (p.asIdeal.Fiber S)
  exact (not_nontrivial_iff_subsingleton.mpr e.injective.subsingleton) hp

end FormallyUnramifiedFiber

/-- **A finite REDUCED algebra over an algebraically closed field is étale.**

This is the algebra core of `AlgebraicGeometry.etale_fiberToSpecResidueField_of_isReduced_pullback`
after base change to an algebraic closure, and it is where reducedness is finally consumed:
`A` is Artinian (finite over a field) and reduced, so `IsArtinianRing.equivPi` splits it as
`∏ (m : MaximalSpectrum A), A ⧸ m`, and over an algebraically closed field every residue field
`A ⧸ m` is `K` itself (`IsAlgClosed.algebraMap_bijective_of_isIntegral`).  A finite product of
copies of `K` is étale by `Algebra.Etale.iff_exists_algEquiv_prod`.

Reducedness is not removable: `K[x]/(x²)` is finite over `K` and not étale. -/
theorem Algebra.Etale.of_isReduced_of_isAlgClosed (K A : Type u) [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [IsReduced A] : Algebra.Etale K A := by
  haveI : IsArtinianRing A := isArtinian_of_tower K inferInstance
  rw [Algebra.Etale.iff_exists_algEquiv_prod]
  refine ⟨MaximalSpectrum A, inferInstance, fun _ => K, fun _ => inferInstance,
    fun _ => inferInstance, ?_, fun _ => ⟨inferInstance, inferInstance⟩⟩
  refine ((IsArtinianRing.equivPi A).restrictScalars K).trans (AlgEquiv.piCongrRight fun m => ?_)
  haveI : m.asIdeal.IsMaximal := m.isMaximal
  haveI : m.asIdeal.IsPrime := m.isMaximal.isPrime
  haveI : IsDomain (A ⧸ m.asIdeal) := Ideal.Quotient.isDomain _
  haveI : Algebra.IsIntegral K (A ⧸ m.asIdeal) := Algebra.IsIntegral.of_finite K _
  exact (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm

namespace AlgebraicGeometry

/-- **`Spec` of a ring map with nilpotent kernel is an infinitesimal thickening.**

`AlgebraicGeometry.FormallyUnramified.hom_ext` asks for `IsNilpotent i.ker`, where `Scheme.Hom.ker`
is an ideal SHEAF; this is the translation from the ring-level hypothesis `(ker φ)ⁿ = ⊥` that
consumers actually hold.  Over an affine target the ideal sheaves are a ring isomorphic to the
ideals of the global sections (`Scheme.IdealSheafData.equivOfIsAffine`), and `Scheme.ker_of_isAffine`
identifies `(Spec.map φ).ker` with the kernel of `(Spec.map φ).appTop`, which is the kernel of `φ`
transported along `Scheme.ΓSpecIso`. -/
theorem isNilpotent_ker_SpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S) {n : ℕ}
    (hn : RingHom.ker φ.hom ^ n = ⊥) : IsNilpotent (Spec.map φ).ker := by
  refine ⟨n, Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  show ((Spec.map φ).ker.ideal ⟨⊤, isAffineOpen_top _⟩) ^ n = _
  have h1 : (Spec.map φ).ker.ideal ⟨⊤, isAffineOpen_top _⟩
      = RingHom.ker ((Spec.map φ).appTop).hom := by
    rw [Scheme.ker_of_isAffine (Spec.map φ)]
    simp
  set ψ := ((Scheme.ΓSpecIso R).hom).hom with hψ
  have hinj : Function.Injective ψ :=
    ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv).injective
  have hinjS : Function.Injective ((Scheme.ΓSpecIso S).hom).hom :=
    ((Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv).injective
  have h2 : RingHom.ker ((Spec.map φ).appTop).hom = Ideal.comap ψ (RingHom.ker φ.hom) := by
    ext x
    have hnat := congrArg (fun m : Γ(Spec R, ⊤) ⟶ S => m.hom x) (Scheme.ΓSpecIso_naturality φ)
    simp only [CommRingCat.comp_apply] at hnat
    simp only [RingHom.mem_ker, Ideal.mem_comap]
    rw [← map_eq_zero_iff _ hinjS, hnat, hψ]
  rw [h1, h2]
  have hmap : Ideal.map ψ ((Ideal.comap ψ (RingHom.ker φ.hom)) ^ n) ≤ ⊥ := by
    rw [Ideal.map_pow, ← hn]
    exact pow_le_pow_left' Ideal.map_comap_le n
  refine le_antisymm (fun x hx => ?_) bot_le
  have hx0 : ψ x = 0 := by simpa using hmap (Ideal.mem_map_of_mem ψ hx)
  simpa using hinj (hx0.trans (map_zero ψ).symm)

/-- Precomposing with an isomorphism does not change the fibres: the fibre of `e.hom ≫ h` at `y`
is the base change of the fibre of `h` at `y` along the identity of the target. -/
theorem etale_fiberToSpecResidueField_isoComp {X X' Y : Scheme.{u}} (e : X' ≅ X) (h : X ⟶ Y)
    (y : Y) [AlgebraicGeometry.Etale (h.fiberToSpecResidueField y)] :
    AlgebraicGeometry.Etale ((e.hom ≫ h).fiberToSpecResidueField y) := by
  have hsq : IsPullback e.hom (e.hom ≫ h) h (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  refine MorphismProperty.of_isPullback
    (isPullback_fiberToSpecResidueField_of_isPullback hsq y) ?_
  exact ‹AlgebraicGeometry.Etale (h.fiberToSpecResidueField y)›

/-- The affine case of `AlgebraicGeometry.etale_of_etale_fiberToSpecResidueField`: this is where the
scheme-level hypothesis is translated into the algebra-level one by
`AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso`, and
`Algebra.FormallyUnramified.of_formallyUnramified_fiber` together with
`Algebra.Etale.of_formallyUnramified_of_flat` finishes. -/
theorem etale_of_etale_fiberToSpecResidueField_SpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [hfin : IsFinite (Spec.map φ)] [hflat : AlgebraicGeometry.Flat (Spec.map φ)]
    [hlfp : LocallyOfFinitePresentation (Spec.map φ)]
    (hfib : ∀ y, AlgebraicGeometry.Etale ((Spec.map φ).fiberToSpecResidueField y)) :
    AlgebraicGeometry.Etale (Spec.map φ) := by
  rw [IsFinite.SpecMap_iff] at hfin
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)] at hflat
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hlfp
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
  algebraize [φ.hom]
  haveI : Algebra.FormallyUnramified R S := by
    refine Algebra.FormallyUnramified.of_formallyUnramified_fiber (fun p hp => ?_)
    have hE : Algebra.Etale p.ResidueField (p.Fiber S) := by
      rw [← RingHom.etale_algebraMap, ← CommRingCat.hom_ofHom (algebraMap p.ResidueField
        (p.Fiber ↑S)), ← HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale),
        ← MorphismProperty.arrow_mk_iso_iff (P := @AlgebraicGeometry.Etale)
          (Spec.fiberToSpecResidueFieldIso R S ⟨p, hp⟩)]
      exact hfib ⟨p, hp⟩
    infer_instance
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- The case of `AlgebraicGeometry.etale_of_etale_fiberToSpecResidueField` with AFFINE target.
Here `X` is automatically affine (`h` is finite, hence affine), which is what lets the source be
presented as a `Spec` — note the source cannot be localised, since `IsFinite` is not local at
source. -/
theorem etale_of_etale_fiberToSpecResidueField_specTarget {X : Scheme.{u}} {R : CommRingCat.{u}}
    (h : X ⟶ Spec R) (h1 : IsFinite h) (h2 : AlgebraicGeometry.Flat h)
    (h3 : LocallyOfFinitePresentation h)
    (hfib : ∀ y, AlgebraicGeometry.Etale (h.fiberToSpecResidueField y)) :
    AlgebraicGeometry.Etale h := by
  haveI := h1; haveI := h2; haveI := h3
  haveI : IsAffine X := isAffine_of_isAffineHom h
  let e : Spec (Scheme.Γ.obj (Opposite.op X)) ≅ X := X.isoSpec.symm
  rw [← MorphismProperty.cancel_left_of_respectsIso @AlgebraicGeometry.Etale e.hom h]
  have hfib' : ∀ y, AlgebraicGeometry.Etale ((e.hom ≫ h).fiberToSpecResidueField y) :=
    fun y => haveI := hfib y; etale_fiberToSpecResidueField_isoComp e h y
  haveI hfin : IsFinite (e.hom ≫ h) := inferInstance
  haveI hflat : AlgebraicGeometry.Flat (e.hom ≫ h) := inferInstance
  haveI hlfp : LocallyOfFinitePresentation (e.hom ≫ h) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.hom ≫ h)
  rw [← hφ] at hfib' hfin hflat hlfp ⊢
  exact etale_of_etale_fiberToSpecResidueField_SpecMap φ hfib'

/-- **A finite flat morphism whose fibres are étale over their residue fields is étale**
(PROVEN).

This is the fibrewise criterion for étaleness, and it is the piece mathlib does NOT have: it has
`Algebra.Smooth.of_formallySmooth_fiber` (flat + finitely presented + smooth fibres ⟹ smooth) and
`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`, but nothing that upgrades ÉTALE
fibres to an étale morphism, and `Smooth` cannot be improved to `Etale` without a relative-dimension
input that this development does not have.

**THE ROUTE, which needs no smoothness and no relative dimension.**  Mathlib DOES have
`Algebra.Etale.of_formallyUnramified_of_flat` (finitely presented + flat + formally unramified ⟹
étale), so the whole content is `Algebra.FormallyUnramified R S` on affine charts — supplied by
`Algebra.FormallyUnramified.of_formallyUnramified_fiber` above, i.e. `Subsingleton Ω[S⁄R]` by base
change of Kähler differentials plus Nakayama.  No smoothness enters.

The reduction to affine charts is in three steps, mirroring
`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`:

1. `Etale` is local at target, so cover `Y` by affines; fibres of the base change are base changes
   of fibres (`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`).
2. With `Y = Spec R` affine, `X` is automatically affine because `h` is finite hence affine
   (`AlgebraicGeometry.isAffine_of_isAffineHom`).  This is the one place the argument differs from
   the smooth one: `IsFinite` is NOT local at source, so the source may not be localised — but it
   need not be, since finiteness makes it affine outright.
3. `AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso` identifies the SCHEME fibre
   `(Spec.map φ).fiberToSpecResidueField p` with `Spec` of `κ(p) → κ(p) ⊗[R] S`, which is the
   translation the algebra core needs. -/
theorem etale_of_etale_fiberToSpecResidueField {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsFinite h] [AlgebraicGeometry.Flat h] [LocallyOfFinitePresentation h]
    (hfib : ∀ y : Y, AlgebraicGeometry.Etale (h.fiberToSpecResidueField y)) :
    AlgebraicGeometry.Etale h := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @AlgebraicGeometry.Etale) Y.affineCover]
  intro i
  dsimp [Scheme.Cover.pullbackHom]
  refine etale_of_etale_fiberToSpecResidueField_specTarget _
    (MorphismProperty.pullback_snd _ _ inferInstance)
    (MorphismProperty.pullback_snd _ _ inferInstance)
    (MorphismProperty.pullback_snd _ _ inferInstance) (fun y ↦ ?_)
  apply MorphismProperty.of_isPullback
  · exact isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback _ _) _
  · exact hfib _

/-- **A finite morphism to `Spec K`, `K` a field, whose base change to an algebraic closure of `K`
is reduced, is étale.**

This is the affine form of `AlgebraicGeometry.etale_fiberToSpecResidueField_of_isReduced_pullback`,
and it is where the pullback/`Spec`-of-tensor-product identification is made:
`AlgebraicGeometry.exists_algebra_iso_of_isFinite` presents the source as `Spec A` with `A` a
finite `K`-algebra, `AlgebraicGeometry.pullbackSpecIso` turns the base-changed pullback into
`Spec (A ⊗[K] K‾)`, and `AlgebraicGeometry.affine_isReduced_iff` reads reducedness back at the
ring level.  Then `Algebra.Etale.of_isReduced_of_isAlgClosed` over `K‾` and
`Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat` (descent along the faithfully flat
`K ⊆ K‾`) finish. -/
theorem etale_of_isReduced_pullback_algClosure {P : Scheme.{u}} {K : Type u} [Field K]
    (q : P ⟶ Spec (CommRingCat.of K)) [IsFinite q]
    (hred : IsReduced (pullback q (Spec.map (CommRingCat.ofHom
      (algebraMap K (AlgebraicClosure K)))))) :
    AlgebraicGeometry.Etale q := by
  obtain ⟨A, _, _, _, e, he⟩ := exists_algebra_iso_of_isFinite q
  haveI := hred
  have i2 : pullback (e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
      ≅ pullback (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) :=
    asIso (pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _) (by simp) (by simp))
  rw [he] at i2
  haveI : IsReduced (pullback (Spec.map (CommRingCat.ofHom (algebraMap K A)))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))) :=
    isReduced_of_isOpenImmersion i2.inv
  haveI : IsReduced (Spec (CommRingCat.of (A ⊗[K] AlgebraicClosure K))) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso K A (AlgebraicClosure K)).inv
  haveI : _root_.IsReduced (A ⊗[K] AlgebraicClosure K) :=
    (affine_isReduced_iff (CommRingCat.of (A ⊗[K] AlgebraicClosure K))).mp inferInstance
  haveI : _root_.IsReduced (AlgebraicClosure K ⊗[K] A) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K A (AlgebraicClosure K)).symm.toRingHom
      (Algebra.TensorProduct.comm K A (AlgebraicClosure K)).symm.injective
  haveI : Module.Finite (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A) :=
    Module.Finite.base_change K (AlgebraicClosure K) A
  haveI : Algebra.Etale (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A) :=
    Algebra.Etale.of_isReduced_of_isAlgClosed (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
  haveI : Algebra.Etale K A :=
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (AlgebraicClosure K)
  rw [← he, MorphismProperty.cancel_left_of_respectsIso @AlgebraicGeometry.Etale,
    HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- **A finite flat morphism with reduced geometric fibres has étale fibres** (PROVEN).

Fixing `y : Y` and writing `κ = κ(y)`, `Ω = AlgebraicClosure κ`, the statement is that the finite
`κ`-algebra `A₀` presenting the fibre is étale.  The hypothesis supplies reducedness of
`X ×_Y Spec Ω`, i.e. of `Ω ⊗[κ] A₀`, and the two algebra steps are:

1. *Alg-closed base.*  `Ω ⊗[κ] A₀` is a finite REDUCED algebra over an algebraically closed field,
   hence `≃ₐ[Ω] ∀ m : MaximalSpectrum, Ω`, hence étale
   (`Algebra.Etale.of_isReduced_of_isAlgClosed` above).
2. *Descent.*  `Ω` is faithfully flat over `κ`, so
   `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat` gives `Algebra.Etale κ A₀`.

Both live in `AlgebraicGeometry.etale_of_isReduced_pullback_algClosure`.  All that is left here is
the geometry: `Limits.pullbackLeftPullbackSndIso` is exactly the pasting identification of
`pullback h (Spec.map (algebraMap κ Ω) ≫ Y.fromSpecResidueField y)` — which is what `hred`
supplies — with `pullback (h.fiberToSpecResidueField y) (Spec.map (algebraMap κ Ω))`, which is
what the affine statement consumes.

Only algebraically closed `K` are used, which is what a consumer with a `geom_cyclic`-style
hypothesis can supply; reducedness at a general field-valued point is not needed and would not be
available. -/
theorem etale_fiberToSpecResidueField_of_isReduced_pullback {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsFinite h] [AlgebraicGeometry.Flat h]
    (hred : ∀ (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (CommRingCat.of K) ⟶ Y),
      IsReduced (pullback h g))
    (y : Y) : AlgebraicGeometry.Etale (h.fiberToSpecResidueField y) := by
  haveI hfibfin : IsFinite (h.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  refine @etale_of_isReduced_pullback_algClosure _ (↑(Y.residueField y)) _
    (h.fiberToSpecResidueField y) hfibfin ?_
  have i1 : pullback (h.fiberToSpecResidueField y)
      (Spec.map (CommRingCat.ofHom
        (algebraMap (↑(Y.residueField y)) (AlgebraicClosure ↑(Y.residueField y)))))
      ≅ pullback h (Spec.map (CommRingCat.ofHom
          (algebraMap (↑(Y.residueField y)) (AlgebraicClosure ↑(Y.residueField y))))
        ≫ Y.fromSpecResidueField y) :=
    pullbackLeftPullbackSndIso h (Y.fromSpecResidueField y) _
  haveI := hred (AlgebraicClosure ↑(Y.residueField y))
    (Spec.map (CommRingCat.ofHom
        (algebraMap (↑(Y.residueField y)) (AlgebraicClosure ↑(Y.residueField y))))
      ≫ Y.fromSpecResidueField y)
  exact isReduced_of_isOpenImmersion i1.hom

/-- **A finite flat morphism, locally of finite presentation, with REDUCED geometric fibres is
étale** (PROVEN over the two leaves above).

This is the general form of the classical "finite flat + reduced fibres ⟹ finite étale", and it
carries **no characteristic hypothesis**: in residue characteristic `p` its hypothesis is
unsatisfiable at the standard counterexamples (`ker F ⊆ 𝔾ₐ` and its subgroups), rather than false.

Combined with `AlgebraicGeometry.isReduced_pullback_of_finrank_le_card_geometricPoints` and
`AlgebraicGeometry.locallyOfFinitePresentation_of_finrank_const`, this says: a finite flat
morphism whose rank at every point equals the number of geometric points of the fibre there is
étale — and the rank hypothesis alone supplies finite presentation, so nothing else is needed. -/
theorem etale_of_isReduced_pullback {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsFinite h] [AlgebraicGeometry.Flat h] [LocallyOfFinitePresentation h]
    (hred : ∀ (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (CommRingCat.of K) ⟶ Y),
      IsReduced (pullback h g)) :
    AlgebraicGeometry.Etale h :=
  etale_of_etale_fiberToSpecResidueField h
    (fun y => etale_fiberToSpecResidueField_of_isReduced_pullback h hred y)

/-- **A scheme affine and of finite type over a field, formally unramified over it, is REDUCED**
(PROVEN 2026-07-30).

This is the *supplier* for the `hred` hypothesis of `etale_of_isReduced_pullback` above, and it is
the only statement in this file that points from unramifiedness towards reducedness rather than the
other way.  Its first consumer is
`Fermat.isReduced_geomFibre_nTorsion_of_specQBase` (`Fermat/FLT/ModularCurve/X0.lean`), where `X` is
a geometric fibre of `E[n]` and the unramifiedness comes from `Fermat.formallyUnramified_mulByNat`.

## The proof is the affine-local translation, and nothing else

`Algebra.FormallyUnramified.isReduced_of_field` (`Mathlib/RingTheory/Unramified/Field.lean`) is the
whole mathematical content.  What is owed is only the passage from the scheme-level property to a
statement about `Γ(X, ⊤)` as a `K`-algebra, and that is:

* `IsAffineHom h` makes `X` affine (the target `Spec K` is), so `X` is determined by `Γ(X, ⊤)` and
  `isReduced_of_isAffine_isReduced` closes the goal — no open cover is needed;
* `FormallyUnramified` and `LocallyOfFiniteType` are both `HasRingHomProperty`s, so
  `HasRingHomProperty.iff_of_isAffine` turns each into the corresponding property of `h.appTop`;
* the `K`-algebra structure is `h.appTop` precomposed with `(Scheme.ΓSpecIso _).inv : K ⟶ Γ(Spec K, ⊤)`,
  which is an isomorphism, hence surjective, hence both formally unramified and of finite type — so
  the two ring properties transfer across it by their composition lemmas.

## Faithfulness

**`LocallyOfFiniteType` is not decoration**: `isReduced_of_field` requires
`Algebra.EssFiniteType K A`, and this hypothesis is exactly what supplies it (via
`Algebra.FiniteType`).  Formal unramifiedness alone does not force reducedness for arbitrary
`K`-algebras — the finiteness is what makes the Kähler-differential argument bite.

**`IsAffineHom` is not removable as stated**, though it is not essential mathematics: for a general
`X` one would run the same argument over `X.affineCover` and conclude with
`IsReduced.of_openCover`, at the cost of `LocallyOfFiniteType` being checked on each piece (which is
automatic, being Zariski-local at the source).  Every consumer here has a *finite* `h`, which gives
`IsAffineHom` and `LocallyOfFiniteType` simultaneously, so the affine form is the one written.

There is **no characteristic hypothesis**, consistently with the rest of this file: over `𝔽_p`,
`Spec 𝔽_p[x]/(xᵖ) ⟶ Spec 𝔽_p` is affine and finite but *not* formally unramified
(`Ω = 𝔽_p[x]/(xᵖ) dx ≠ 0`), so the hypothesis is unsatisfiable there rather than false. -/
theorem isReduced_of_formallyUnramified_over_field
    {X : Scheme.{u}} {K : Type u} [Field K] (h : X ⟶ Spec (CommRingCat.of K))
    [FormallyUnramified h] [IsAffineHom h] [LocallyOfFiniteType h] : IsReduced X := by
  haveI : IsAffine X := isAffine_of_isAffineHom h
  set φ : CommRingCat.of K ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ h.appTop
    with hφ
  letI : Algebra K Γ(X, ⊤) := φ.hom.toAlgebra
  have hiso : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).surjective
  have hfu : RingHom.FormallyUnramified φ.hom := by
    rw [hφ]
    exact RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective hiso)
      (HasRingHomProperty.iff_of_isAffine.mp ‹FormallyUnramified h›)
  have hft : RingHom.FiniteType φ.hom := by
    rw [hφ]
    exact RingHom.finiteType_stableUnderComposition _ _
      (RingHom.FiniteType.of_surjective _ hiso)
      (HasRingHomProperty.iff_of_isAffine.mp ‹LocallyOfFiniteType h›)
  haveI : Algebra.FormallyUnramified K Γ(X, ⊤) := hfu
  haveI : Algebra.FiniteType K Γ(X, ⊤) := hft
  haveI : _root_.IsReduced Γ(X, ⊤) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_isAffine_isReduced X

end AlgebraicGeometry
