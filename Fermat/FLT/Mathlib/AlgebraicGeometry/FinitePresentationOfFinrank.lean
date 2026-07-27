/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Finite + flat + constant rank ⟹ locally of finite presentation

Mathlib has one direction of the "finite locally free" dictionary: a finite, flat, **locally
finitely presented** morphism has locally constant rank
(`AlgebraicGeometry.Scheme.Hom.isLocallyConstant_finrank`).  It does **not** have the converse,
which is what a consumer wanting to *deduce* finite presentation needs.  This file supplies it,
in the form actually used (a globally constant rank):

* `Module.finitePresentation_of_rankAtStalk_const` — the commutative-algebra statement: a finite
  flat module whose `rankAtStalk` is constant is finitely presented.
* `AlgebraicGeometry.locallyOfFinitePresentation_of_finrank_const` — its scheme-theoretic shadow.

**The constancy hypothesis is not removable.**  "Finite + flat ⟹ finitely presented" is FALSE,
and the counterexample is even a `ℚ`-algebra: `R = ∏_{n : ℕ} ℚ` is von Neumann regular, so every
`R`-module is flat; let `I ⊆ R` be the ideal of finitely supported sequences.  Then `R ⧸ I` is
cyclic, hence module-finite, and flat, but `I` is not finitely generated so `R ⧸ I` is not
finitely presented.  Its rank function is `1` on `V I` and `0` off it — a set that is closed and
not open, i.e. exactly a failure of local constancy.

## Proof

`Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant` (mathlib) turns the constant rank
into: for every prime `p` there is `a ∉ p` with `M` free over `R_a`.  The set of such `a` therefore
meets the complement of every maximal ideal, so it spans the unit ideal, and
`Module.FinitePresentation.of_localizationSpan` glues the free (hence finitely presented) pieces.
The scheme statement follows by the standard two-step reduction to `Spec S ⟶ Spec R`, using that
`LocallyOfFinitePresentation` is Zariski-local at the target.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

/-- **A finite flat module of constant rank is finitely presented.**

See the module docstring for the `∏_ℕ ℚ` counterexample showing the rank hypothesis cannot be
dropped. -/
theorem Module.finitePresentation_of_rankAtStalk_const
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] {n : ℕ}
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) M p = n) :
    Module.FinitePresentation R M := by
  classical
  set s : Set R := {a : R | Module.Free (Localization.Away a) (LocalizedModule.Away a M)} with hs
  have hspan : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI : m.IsPrime := hm.isPrime
    obtain ⟨a, hane, hfree⟩ :=
      Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M m
        (fun m' _ => by rw [h, h])
    exact hane (hle (Ideal.subset_span (show a ∈ s from hfree)))
  refine Module.FinitePresentation.of_localizationSpan s hspan (fun g => ?_)
  haveI : Module.Free (Localization.Away g.1) (LocalizedModule.Away g.1 M) := g.2
  exact Module.finitePresentation_of_projective _ _

namespace AlgebraicGeometry

/-- **A finite flat morphism of constant rank is locally of finite presentation.**

The converse of `AlgebraicGeometry.Scheme.Hom.isLocallyConstant_finrank`, for a globally constant
rank.  Note that `Scheme.Hom.finrank` is defined without any hypotheses on `f`, so the statement
needs no instance juggling at the use site. -/
theorem locallyOfFinitePresentation_of_finrank_const {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Flat f] {n : ℕ} (h : ∀ y, f.finrank y = n) :
    LocallyOfFinitePresentation f := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover
      (P := @LocallyOfFinitePresentation) Y.affineCover]
    intro i
    dsimp only [Scheme.Cover.pullbackHom]
    haveI hfin : IsFinite (Limits.pullback.snd f (Y.affineCover.f i)) :=
      MorphismProperty.pullback_snd (P := @IsFinite) f _ inferInstance
    haveI hflat : Flat (Limits.pullback.snd f (Y.affineCover.f i)) :=
      MorphismProperty.pullback_snd (P := @Flat) f _ inferInstance
    refine this (Limits.pullback.snd f (Y.affineCover.f i)) (n := n) (fun y => ?_) ⟨_, rfl⟩
    rw [Scheme.Hom.finrank_pullback_snd]
    exact h _
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    rw [← MorphismProperty.cancel_left_of_respectsIso
      @LocallyOfFinitePresentation X.isoSpec.inv]
    refine this (n := n) _ _ (fun y => ?_) ⟨_, rfl⟩
    rw [Scheme.Hom.finrank_comp_left_of_isIso]
    exact h y
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff,
    LocallyOfFinitePresentation.SpecMap_iff] at *
  algebraize [φ.hom]
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank ‹_› ‹_›] at h
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap] at h
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finitePresentation_algebraMap]
  haveI : Module.FinitePresentation R S :=
    Module.finitePresentation_of_rankAtStalk_const (n := n) (fun p => h p)
  infer_instance

end AlgebraicGeometry
