/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module


public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Artinian.Module

/-!
# Descent of factorisations from geometric points, over a base field that is NOT closed

A closed subscheme of a scheme over a field `k` is detected by the `k̄`-points of any
FINITE REDUCED `k`-scheme mapping to it.  This is the tool a "same geometric points ⟹
same closed subscheme" argument needs when the base field is `ℚ` rather than `ℚ̄`.

## Main results

* `AlgebraicGeometry.exists_factor_of_isSchemeTheoreticallyDominant` — a factorisation
  through a CLOSED IMMERSION descends along a scheme-theoretically dominant morphism.
  This is `IsClosedImmersion.lift` plus `Scheme.Hom.ker_comp`, and it is the whole of the
  descent: "factors through `j`" is `j.ker ≤ ·.ker`, and a dominant morphism does not
  change the kernel of what it is composed into.
* `AlgebraicGeometry.exists_factor_of_geomSections_of_isReduced_of_isFinite'` — the
  algebraically-closed-base statement: a morphism out of a finite reduced `K`-scheme
  factors through anything its `K`-points factor through.
* `AlgebraicGeometry.exists_factor_of_geomPoints_of_isFinite` — the theorem this module
  exists for: `Z` finite over `Spec k` with REDUCED GEOMETRIC FIBRE, and a morphism
  `a : Z ⟶ X` every `k̄`-point of which factors through a closed immersion `j`, factors
  through `j`.

## Provenance, and the duplication this file deliberately carries

`algEquivPiOfIsAlgClosed'`, `exists_sigmaSpec_iso_of_isReduced_of_isFinite'` and
`exists_factor_of_geomSections_of_isReduced_of_isFinite'` are COPIES, under primed names
and in the `AlgebraicGeometry` namespace, of `MazurIsogenyPrimeJ.algEquivPiOfIsAlgClosed`,
`MazurIsogenyPrimeJ.exists_sigmaSpec_iso_of_isReduced_of_isFinite` and
`MazurIsogenyPrimeJ.exists_factor_of_geomSections_of_isReduced_of_isFinite` in
`Fermat/FLT/FreyCurve/MazurTorsion.lean` (proven there 2026-07-30, unchanged here except
for the namespace).  They are copied rather than cited because the consumer —
`Fermat.Gamma0Datum.ker_of_geomFibrePt`, `MazurTorsion.lean:21831` — is declared roughly
18 000 lines ABOVE them in that same file, so Lean cannot see them from there.  The three
statements are generic scheme theory with no elliptic curve and no level structure in
them, so this module, which imports only mathlib, is where they belong.

**The `MazurIsogenyPrimeJ` copies should be DELETED and their consumers re-pointed here**;
that is a separate edit in a heavily-contended region of a 100 000-line file and is left to
whoever next works in it.  The names differ (namespace and prime), so nothing collides in
the meantime.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Factorisation through a CLOSED IMMERSION descends along a scheme-theoretically
dominant morphism.**

`IsClosedImmersion.lift` turns "`a` factors through `j`" into the inequality of ideal
sheaves `j.ker ≤ a.ker`, and `Scheme.Hom.ker_comp` says `(q ≫ a).ker = q.ker.map a`, which
for `q.ker = ⊥` is `a.ker` by `IdealSheafData.map_bot`.  So the hypothesis gives
`j.ker ≤ (z ≫ j).ker = (q ≫ a).ker = a.ker`.

No finiteness, no reducedness and no hypothesis on `Z'`, `Z`, `X` or `Y`: the content is
entirely in the ideal-sheaf calculus. -/
theorem exists_factor_of_isSchemeTheoreticallyDominant {Z' Z X Y : Scheme.{u}} (q : Z' ⟶ Z)
    [IsSchemeTheoreticallyDominant q] (j : Y ⟶ X) [IsClosedImmersion j] (a : Z ⟶ X)
    (h : ∃ z : Z' ⟶ Y, z ≫ j = q ≫ a) : ∃ b : Z ⟶ Y, b ≫ j = a := by
  obtain ⟨z, hz⟩ := h
  have h1 : (q ≫ a).ker = a.ker := by
    rw [Scheme.Hom.ker_comp, q.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have h2 : j.ker ≤ (z ≫ j).ker := by
    rw [Scheme.Hom.ker_comp, ← Scheme.IdealSheafData.map_bot (f := j)]
    exact Scheme.IdealSheafData.map_mono _ bot_le
  rw [hz, h1] at h2
  exact ⟨IsClosedImmersion.lift j a h2, IsClosedImmersion.lift_fac j a h2⟩

/-- **A FINITE REDUCED algebra over an algebraically closed field is a finite PRODUCT OF
COPIES of the field.**  Copy of `MazurIsogenyPrimeJ.algEquivPiOfIsAlgClosed`; see the module
docstring. -/
noncomputable def algEquivPiOfIsAlgClosed' (K : Type) [Field K] [IsAlgClosed K]
    (A : Type) [CommRing A] [Algebra K A] [Module.Finite K A] [_root_.IsReduced A] :
    A ≃ₐ[K] (MaximalSpectrum A → K) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  refine (IsArtinianRing.equivPi A).restrictScalars K |>.trans (AlgEquiv.piCongrRight ?_)
  intro 𝔪
  haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  haveI : Field (A ⧸ 𝔪.asIdeal) := Ideal.Quotient.field _
  haveI : Module.Finite K (A ⧸ 𝔪.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K 𝔪.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral K (A ⧸ 𝔪.asIdeal) := Algebra.IsIntegral.of_finite K _
  exact (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ 𝔪.asIdeal))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral)).symm

/-- **A FINITE REDUCED scheme over an algebraically closed field IS A FINITE DISJOINT UNION
OF COPIES OF THE BASE.**  Copy of
`MazurIsogenyPrimeJ.exists_sigmaSpec_iso_of_isReduced_of_isFinite`; see the module
docstring. -/
theorem exists_sigmaSpec_iso_of_isReduced_of_isFinite' {K : Type} [Field K]
    [IsAlgClosed K] {C : Scheme.{0}} (π : C ⟶ Spec (CommRingCat.of K))
    [IsFinite π] [AlgebraicGeometry.IsReduced C] :
    ∃ (ι : Type) (_ : Finite ι) (p : (∐ fun _ : ι => Spec (CommRingCat.of K)) ⟶ C),
      IsIso p ∧
        ∀ i : ι, (Sigma.ι (fun _ : ι => Spec (CommRingCat.of K)) i ≫ p) ≫ π = 𝟙 _ := by
  haveI : IsAffine C := isAffine_of_isAffineHom π
  set ρ : CommRingCat.of K ⟶ Γ(C, ⊤) := Spec.preimage (C.isoSpec.inv ≫ π) with hρdef
  have hmap : Spec.map ρ = C.isoSpec.inv ≫ π := Spec.map_preimage _
  haveI : IsFinite (Spec.map ρ) := by rw [hmap]; infer_instance
  have hfin : ρ.hom.Finite := (IsFinite.SpecMap_iff ρ).mp inferInstance
  letI : Algebra K Γ(C, ⊤) := ρ.hom.toAlgebra
  haveI : Module.Finite K Γ(C, ⊤) := hfin
  haveI : _root_.IsReduced ↑Γ(C, ⊤) := AlgebraicGeometry.IsReduced.component_reduced ⊤
  haveI : IsArtinianRing ↑Γ(C, ⊤) := IsArtinianRing.of_finite K _
  set ι := MaximalSpectrum ↑Γ(C, ⊤) with hι
  haveI : Finite ι := inferInstance
  set e : ↑Γ(C, ⊤) ≃ₐ[K] (ι → K) := algEquivPiOfIsAlgClosed' K _ with he
  set g : Spec (CommRingCat.of (ι → K)) ⟶ C :=
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.isoSpec.inv with hg
  haveI : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) :=
    e.toRingEquiv.toCommRingCatIso.isIso_hom
  haveI : IsIso g := by rw [hg]; infer_instance
  have hsec : ∀ i : ι, (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ι => K) i)) ≫ g)
      ≫ π = 𝟙 _ := by
    intro i
    rw [hg, Category.assoc, Category.assoc, ← hmap, ← Spec.map_comp, ← Spec.map_comp,
      Category.assoc]
    rw [show ρ ≫ CommRingCat.ofHom e.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom (Pi.evalRingHom (fun _ : ι => K) i) = 𝟙 (CommRingCat.of K) from ?_]
    · exact Spec.map_id _
    · ext k
      exact congrArg (fun z : ι → K => z i) (e.commutes k)
  refine ⟨ι, inferInstance, sigmaSpec (fun _ : ι => CommRingCat.of K) ≫ g, inferInstance,
    fun i => ?_⟩
  rw [← Category.assoc, ι_sigmaSpec]
  exact hsec i

/-- **A MORPHISM OUT OF A FINITE REDUCED SCHEME over an algebraically closed field FACTORS
through anything its `K`-POINTS factor through.**  Copy of
`MazurIsogenyPrimeJ.exists_factor_of_geomSections_of_isReduced_of_isFinite`; see the module
docstring. -/
theorem exists_factor_of_geomSections_of_isReduced_of_isFinite' {K : Type} [Field K]
    [IsAlgClosed K] {C X Z : Scheme.{0}} (π : C ⟶ Spec (CommRingCat.of K))
    [IsFinite π] [AlgebraicGeometry.IsReduced C] (a : C ⟶ X) (j : Z ⟶ X)
    (h : ∀ w : Spec (CommRingCat.of K) ⟶ C, w ≫ π = 𝟙 _ →
      ∃ z : Spec (CommRingCat.of K) ⟶ Z, z ≫ j = w ≫ a) :
    ∃ b : C ⟶ Z, b ≫ j = a := by
  classical
  obtain ⟨ι, hιfin, p, hp, hsec⟩ := exists_sigmaSpec_iso_of_isReduced_of_isFinite' π
  haveI := hιfin
  haveI := hp
  choose z hz using fun i : ι => h _ (hsec i)
  have key : Sigma.desc z ≫ j = p ≫ a := by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp only [← Category.assoc, Sigma.ι_desc]
    exact hz i
  refine ⟨(asIso p).inv ≫ Sigma.desc z, ?_⟩
  rw [Category.assoc, key, asIso_inv, IsIso.inv_hom_id_assoc]

/-- **A MORPHISM OUT OF A FINITE SCHEME OVER A FIELD `k` WITH REDUCED GEOMETRIC FIBRE
FACTORS through any closed immersion its `k̄`-POINTS factor through.**

This is the tool for a "same geometric points ⟹ same closed subscheme" argument over a base
field that is NOT algebraically closed, where the sections of `Z` over the base are far too
few to see anything.

**The proof is the two lemmas above, in series, and nothing else.**  Write `Z̄` for
`Z ×_k k̄`.  Its structure map is finite (base change), it is reduced by hypothesis, and its
`k̄`-SECTIONS are exactly the `k̄`-POINTS of `Z` (that is `pullback.condition`), so
`exists_factor_of_geomSections_of_isReduced_of_isFinite'` factors `Z̄ ⟶ Z ⟶ X` through `j`.
Then `Z̄ ⟶ Z` is scheme-theoretically dominant — it is the base change of the dominant
`Spec k̄ ⟶ Spec k` along `π`, and the flatness that stability needs is FREE because the base
is the spectrum of a field — so
`exists_factor_of_isSchemeTheoreticallyDominant` brings the factorisation down to `Z`.

**`IsClosedImmersion j` is load-bearing here and is not in the algebraically closed
statement above**: over `k̄` the factorisation is assembled from the components of a
coproduct and no property of `j` is used, whereas descending it is the statement that
`j.ker ≤ a.ker` may be checked after a dominant base change, which is about a closed
subscheme and not about an arbitrary morphism.

**The reducedness hypothesis is on the GEOMETRIC FIBRE, not on `Z`.**  Over a base field of
characteristic zero the two are equivalent, but the geometric-fibre form is what the
consumers have in hand (`CyclicSubgroupOfOrder.isReduced_geomFibre_of_specQBase` is stated
that way) and it is the honest hypothesis: over `k = 𝔽_p(t)` the reduced `Z = Spec k[x]/(xᵖ−t)`
has a non-reduced geometric fibre and one `k̄`-point, and the conclusion fails for it. -/
theorem exists_factor_of_geomPoints_of_isFinite {k K : Type} [Field k] [Field K]
    [IsAlgClosed K] {Z X Y : Scheme.{0}} (π : Z ⟶ Spec (CommRingCat.of k)) [IsFinite π]
    (alg : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    [IsSchemeTheoreticallyDominant alg] [QuasiCompact alg]
    (hred : AlgebraicGeometry.IsReduced (pullback π alg))
    (j : Y ⟶ X) [IsClosedImmersion j] (a : Z ⟶ X)
    (hgeom : ∀ w : Spec (CommRingCat.of K) ⟶ Z, w ≫ π = alg →
      ∃ y : Spec (CommRingCat.of K) ⟶ Y, y ≫ j = w ≫ a) :
    ∃ b : Z ⟶ Y, b ≫ j = a := by
  haveI := hred
  refine exists_factor_of_isSchemeTheoreticallyDominant (pullback.fst π alg) j a ?_
  refine exists_factor_of_geomSections_of_isReduced_of_isFinite' (pullback.snd π alg)
    (pullback.fst π alg ≫ a) j ?_
  intro w hw
  have hbase : (w ≫ pullback.fst π alg) ≫ π = alg := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp]
  obtain ⟨y, hy⟩ := hgeom _ hbase
  exact ⟨y, by rw [hy, Category.assoc]⟩

end AlgebraicGeometry
