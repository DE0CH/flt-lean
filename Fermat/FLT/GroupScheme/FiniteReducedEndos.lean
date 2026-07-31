/-
FiniteReducedEndos.lean — own work for the Fermat project.

# A finite REDUCED scheme over a field has only finitely many endomorphisms over that field

This is the finiteness input that Lagrange's theorem needs when it is applied
to a finite étale group scheme over a field.  There is no group structure here
and no characteristic hypothesis: the statement is about a finite morphism
`p : X ⟶ Spec K` with `X` reduced, and it says that

    {v : X ⟶ X // v ≫ p = p}

is a FINITE type.  Applied to `X = ker φ` of a finite homomorphism of abelian
schemes over `ℚ` — reduced by Cartier's theorem — it makes the group of
relative points of the kernel finite, so that `Nat.card` of that group kills
its tautological point.

## The two steps

1. `finite_algHom_of_isReduced` — **algebra.**  For a field `K`, a
   module-finite `K`-algebra `A` and a REDUCED artinian `K`-algebra `B`, the
   set `A →ₐ[K] B` is finite.  A reduced artinian ring embeds in the product of
   its residue fields at the (finitely many) maximal ideals, so an algebra map
   into `B` is determined by its finitely many composites with the quotient
   maps `B ⟶ B ⧸ 𝔪`, and each of those lives in a finite set because mathlib
   knows `Finite (A →ₐ[K] L)` for `L` a FIELD and `A` module-finite over `K`.

   Reducedness of the TARGET is what makes this true, and it cannot be dropped:
   `ℚ[x]/(x²) →ₐ[ℚ] ℚ[x]/(x²)`, `x ↦ a·x`, is a one-parameter family.

2. `finite_homOver_of_isFinite_of_isReduced` — **geometry.**  A finite morphism
   is affine, so `X ≅ Spec Γ(X, ⊤)` (`Scheme.isoSpec`), `Γ(X, ⊤)` is a
   module-finite `K`-algebra (`Scheme.Hom.finite_appTop`) and it is reduced
   (`AlgebraicGeometry.IsReduced.component_reduced`).  Full faithfulness of
   `Spec` (`Spec.preimage`, `Spec.map_preimage`) turns an endomorphism of `X`
   over `Spec K` into a `K`-algebra endomorphism of `Γ(X, ⊤)`, injectively, and
   step 1 applies.
-/
module

public import Fermat.FLT.GroupScheme.AffineGroupHopf
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Artinian.Instances
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace Fermat

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
/-- **Finiteness of `K`-algebra maps out of a module-finite `K`-algebra into a
REDUCED artinian one.**

`B` reduced artinian embeds in `∏_𝔪 B ⧸ 𝔪` (the intersection of the maximal
ideals is the nilradical, which is `0`), so `f ↦ (𝔪 ↦ mk 𝔪 ∘ f)` is injective;
each factor is finite because the target is a FIELD and `A` is module-finite
over `K`, and there are finitely many maximal ideals.

**Reducedness of the TARGET is load-bearing.**  Witness: `A = B = ℚ[x]/(x²)`,
`f_a : x ↦ a·x` for `a : ℚ` is a `ℚ`-algebra endomorphism for every `a`, so
`A →ₐ[ℚ] B` is infinite. -/
theorem finite_algHom_of_isReduced (K A B : Type u) [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] [CommRing B] [Algebra K B] [IsArtinianRing B] [IsReduced B] :
    Finite (A →ₐ[K] B) := by
  classical
  refine Finite.of_injective
    (fun f : A →ₐ[K] B => fun I : MaximalSpectrum B =>
      (Ideal.Quotient.mkₐ K I.asIdeal).comp f) ?_
  intro f g h
  ext x
  have hx : ∀ I : MaximalSpectrum B, f x - g x ∈ I.asIdeal := by
    intro I
    have h' := congrFun h I
    have h2 : Ideal.Quotient.mk I.asIdeal (f x) = Ideal.Quotient.mk I.asIdeal (g x) :=
      congrArg (fun t : A →ₐ[K] B ⧸ I.asIdeal => t x) h'
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 h2
  have hmem : f x - g x ∈ nilradical B := by
    rw [IsArtinianRing.nilradical_eq_iInf]
    exact Ideal.mem_iInf.2 hx
  rw [nilradical_eq_zero] at hmem
  have : f x - g x = 0 := hmem
  linear_combination (norm := ring_nf) this

/-- **A FINITE REDUCED SCHEME OVER A FIELD HAS ONLY FINITELY MANY
ENDOMORPHISMS OVER THAT FIELD.**

`p` finite makes `X` affine, so `X ≅ Spec Γ(X, ⊤)` with `Γ(X, ⊤)` a
module-finite `K`-algebra, reduced because `X` is; full faithfulness of `Spec`
sends `v` to a `K`-algebra endomorphism of `Γ(X, ⊤)` injectively, and
`finite_algHom_of_isReduced` counts those.

**`IsReduced X` is load-bearing** — the witness of `finite_algHom_of_isReduced`
is `X = Spec ℚ[x]/(x²)` over `Spec ℚ`, finite and NOT reduced, whose
endomorphisms over `Spec ℚ` are the `x ↦ a·x`, one for every `a : ℚ`. -/
theorem finite_homOver_of_isFinite_of_isReduced {X : Scheme.{u}} {K : Type u} [Field K]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsFinite p] [AlgebraicGeometry.IsReduced X] :
    Finite {v : X ⟶ X // v ≫ p = p} := by
  haveI : IsAffine X := isAffine_of_isAffineHom p
  let kA : CommRingCat.of K ⟶ Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop
  letI : Algebra K (Γ(X, ⊤) : CommRingCat.{u}) := kA.hom.toAlgebra
  have key : X.isoSpec.hom ≫ Spec.map kA = p := by
    have h := Scheme.isoSpec_hom_naturality (X := X) (Y := Spec (CommRingCat.of K)) p
    rw [Scheme.isoSpec_Spec_hom] at h
    rw [show kA = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop from rfl,
      Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have keyinv : X.isoSpec.inv ≫ p = Spec.map kA := by
    rw [← key, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  haveI : Module.Finite K (Γ(X, ⊤) : CommRingCat.{u}) := by
    have h1 : (p.appTop).hom.Finite := p.finite_appTop
    have h2 : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Finite := by
      apply RingHom.Finite.of_surjective
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    exact h1.comp h2
  haveI : IsArtinianRing (Γ(X, ⊤) : CommRingCat.{u}) := IsArtinianRing.of_finite K _
  haveI := finite_algHom_of_isReduced K (Γ(X, ⊤) : CommRingCat.{u}) (Γ(X, ⊤) : CommRingCat.{u})
  refine Finite.of_injective
    (fun v : {v : X ⟶ X // v ≫ p = p} =>
      ({ toRingHom := (Spec.preimage (X.isoSpec.inv ≫ v.1 ≫ X.isoSpec.hom)).hom
         commutes' := fun r => by
           have hkf : kA ≫ Spec.preimage (X.isoSpec.inv ≫ v.1 ≫ X.isoSpec.hom) = kA := by
             apply Spec.map_injective
             rw [Spec.map_comp, Spec.map_preimage, Category.assoc, Category.assoc, key, v.2,
               keyinv]
           exact congrArg (fun t => CommRingCat.Hom.hom t r) hkf } :
        (Γ(X, ⊤) : CommRingCat.{u}) →ₐ[K] (Γ(X, ⊤) : CommRingCat.{u}))) ?_
  intro v w hvw
  have h1 : Spec.preimage (X.isoSpec.inv ≫ v.1 ≫ X.isoSpec.hom)
      = Spec.preimage (X.isoSpec.inv ≫ w.1 ≫ X.isoSpec.hom) := by
    refine CommRingCat.hom_ext ?_
    exact congrArg (fun t : (Γ(X, ⊤) : CommRingCat.{u}) →ₐ[K] (Γ(X, ⊤) : CommRingCat.{u}) =>
      t.toRingHom) hvw
  have h2 : X.isoSpec.inv ≫ v.1 ≫ X.isoSpec.hom = X.isoSpec.inv ≫ w.1 ≫ X.isoSpec.hom := by
    rw [← Spec.map_preimage (X.isoSpec.inv ≫ v.1 ≫ X.isoSpec.hom),
      ← Spec.map_preimage (X.isoSpec.inv ≫ w.1 ≫ X.isoSpec.hom), h1]
  refine Subtype.ext ?_
  have h3 := congrArg (fun t => X.isoSpec.hom ≫ t ≫ X.isoSpec.inv) h2
  simpa [Category.assoc] using h3

end Fermat

end
