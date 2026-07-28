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

/-!
# A finite flat morphism with REDUCED geometric fibres is étale

This is the "fibrewise criterion" half of the finite-flat/étale dictionary, and the exact
complement of `Fermat/FLT/Mathlib/AlgebraicGeometry/FinrankGeometricPoints.lean`: that file turns
a rank computation into reducedness of a geometric fibre, and this one turns reducedness of every
geometric fibre into étaleness of the morphism.

* `AlgebraicGeometry.etale_of_isReduced_pullback` — the headline statement, assembled from the two
  leaves below.
* `AlgebraicGeometry.isNilpotent_ker_SpecMap` — a small proven bridge: `Spec` of a ring map with
  nilpotent kernel is an infinitesimal thickening in the sense
  `AlgebraicGeometry.FormallyUnramified.hom_ext` wants.

**No characteristic hypothesis appears anywhere here, and none is needed**: over `𝔽_p`,
`ker F ⊆ 𝔾ₐ` is finite flat and NOT étale, but its geometric fibre `Spec 𝔽̄_p[x]/(x^p)` is not
reduced, so the hypothesis is unsatisfiable there rather than being false.  The characteristic
enters only where a CONSUMER proves reducedness (over a `ℚ`-base, by Cartier).
-/

@[expose] public section

open CategoryTheory Limits

universe u

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

/-- **LEAF: a finite flat morphism with reduced geometric fibres has étale fibres.**

Fixing `y : Y` and writing `κ = κ(y)`, `Ω = AlgebraicClosure κ`, the statement is that the finite
`κ`-algebra `A₀` presenting the fibre is étale.  The hypothesis supplies reducedness of
`X ×_Y Spec Ω`, i.e. of `Ω ⊗[κ] A₀`, and the two steps are:

1. *Alg-closed base.*  `Ω ⊗[κ] A₀` is a finite REDUCED algebra over an algebraically closed field,
   hence `≃ₐ[Ω] ∀ m : MaximalSpectrum, Ω` (`IsArtinianRing.equivPi` together with
   `Algebra.finrank_quotient_maximal_eq_one` from `FinrankGeometricPoints.lean`), hence
   `Algebra.Etale Ω (Ω ⊗[κ] A₀)` by `Algebra.Etale.iff_exists_algEquiv_prod`.
2. *Descent.*  `Ω` is faithfully flat over `κ`, so
   `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat` gives `Algebra.Etale κ A₀`.

The formalisation cost is neither of those two steps but the identification of `Ω ⊗[κ] A₀` with
the geometric fibre: `pullback h (Spec.map (algebraMap κ Ω) ≫ Y.fromSpecResidueField y)` is, by
pullback pasting, `pullback (h.fiberToSpecResidueField y) (Spec.map (algebraMap κ Ω))`, and
`AlgebraicGeometry.pullbackSpecIso` turns that into `Spec (A₀ ⊗[κ] Ω)` once
`AlgebraicGeometry.exists_algebra_iso_of_isFinite` (`FinrankGeometricPoints.lean`) has presented
the fibre as `Spec A₀`.

Only algebraically closed `K` are used, which is what a consumer with a `geom_cyclic`-style
hypothesis can supply; reducedness at a general field-valued point is not needed and would not be
available. -/
theorem etale_fiberToSpecResidueField_of_isReduced_pullback {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsFinite h] [AlgebraicGeometry.Flat h]
    (hred : ∀ (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (CommRingCat.of K) ⟶ Y),
      IsReduced (pullback h g))
    (y : Y) : AlgebraicGeometry.Etale (h.fiberToSpecResidueField y) :=
  sorry

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

end AlgebraicGeometry
