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

/-- **LEAF: a finite flat morphism whose fibres are étale over their residue fields is étale.**

This is the fibrewise criterion for étaleness, and it is the piece mathlib does NOT have: it has
`Algebra.Smooth.of_formallySmooth_fiber` (flat + finitely presented + smooth fibres ⟹ smooth) and
`AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`, but nothing that upgrades ÉTALE
fibres to an étale morphism, and `Smooth` cannot be improved to `Etale` without a relative-dimension
input that this development does not have.

**THE ROUTE, which needs no smoothness and no relative dimension.**  `Etale` splits as
`Flat ∧ FormallyUnramified ∧ LocallyOfFinitePresentation`
(`AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified`), and two of the three are hypotheses
here, so the whole content is `FormallyUnramified h`.  Since `FormallyUnramified` is a
`HasRingHomProperty` for `RingHom.FormallyUnramified`, it may be checked on affine charts
`R = Γ(Y, U)`, `S = Γ(X, h⁻¹U)`, where `S` is a finite flat finitely presented `R`-algebra, and
there `Algebra.formallyUnramified_iff` reduces it to `Subsingleton Ω[S⁄R]`.  Now:

1. `Ω[S⁄R]` is a finitely generated `S`-module, hence a finitely generated `R`-module because `S`
   is module-finite over `R`.
2. For every maximal ideal `p` of `R`, base change of Kähler differentials
   (`KaehlerDifferential.tensorKaehlerEquiv`, with `Algebra.IsPushout R S κ(p) (κ(p) ⊗[R] S)`)
   identifies `κ(p) ⊗[R] Ω[S⁄R]` with `Ω[(κ(p) ⊗[R] S)⁄κ(p)]`, which vanishes because the fibre
   `κ(p) ⊗[R] S` is étale — that is exactly the hypothesis, read affine-locally.
3. Nakayama: a finitely generated `R`-module `M` with `M ⧸ pM = 0` for every maximal `p` is zero.
   (`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` applied to a maximal ideal
   containing the annihilator.)

Step 2 is the only step that touches the hypothesis, and it is where the affine-chart translation
between the SCHEME fibre `h.fiberToSpecResidueField y` and the ALGEBRA fibre `κ(p) ⊗[R] S` has to
be made; that translation, not the commutative algebra, is the bulk of the work. -/
theorem etale_of_etale_fiberToSpecResidueField {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsFinite h] [AlgebraicGeometry.Flat h] [LocallyOfFinitePresentation h]
    (hfib : ∀ y : Y, AlgebraicGeometry.Etale (h.fiberToSpecResidueField y)) :
    AlgebraicGeometry.Etale h :=
  sorry

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
