/-
AffineGroupHopf.lean — own work for the Fermat project.

# A finite affine group scheme over a field is `Spec` of a finite Hopf algebra

This module supplies the purely formal half of the affine group-scheme /
Hopf-algebra dictionary, in exactly the direction this development needs:
from a **functorial group structure on the points** of a finite affine
`K`-scheme `X` to a **Hopf-algebra structure on `Γ(X, ⊤)`**.

There is no arithmetic here and no hypothesis on `K` beyond commutativity
of the ring: everything is Yoneda plus the `Γ ⊣ Spec` anti-equivalence.

## The two steps

1. `nonempty_grpObj_of_yoneda` — **Yoneda**.  Mathlib's
   `CategoryTheory.GrpObj.ofRepresentableBy` turns a representable presheaf
   of groups into a group object.  Applied in `C = (CommAlgCat K)ᵒᵖ`, whose
   cartesian monoidal structure is the tensor product of `K`-algebras, it
   turns a functorial group structure on `A →ₐ[K] R` into a **cogroup
   structure on `A`**.  Mathlib's
   `instance (A : (CommAlgCat R)ᵒᵖ) [GrpObj A] : HopfAlgebra R A.unop`
   (`Mathlib/Algebra/Category/CommHopfAlgCat.lean`) then supplies the Hopf
   algebra: coassociativity, counitality and the antipode identities are
   *derived* from the group-object diagrams, so nothing has to be checked in
   tensor-product form.

   `hopfAlgebraOfGrpObj` exists only to name that instance at an object of
   the shape `op (CommAlgCat.of K A)`: instance search cannot solve the
   higher-order unification `↥(?X.unop) =?= A`, while a direct application
   at `?X := op (CommAlgCat.of K A)` typechecks by `rfl`.

2. `exists_hopfAlgebra_of_ptsFunctor` — **`Γ ⊣ Spec`**.  A finite morphism
   is affine, so `X` is affine and `X ≅ Spec Γ(X, ⊤)`; `Spec` is fully
   faithful (`Spec.homEquiv`), so morphisms `Spec R ⟶ X` over `Spec K` are
   exactly `K`-algebra maps `Γ(X, ⊤) →ₐ[K] R`.  Transporting the given
   group structure along that bijection and feeding it to step 1 gives the
   Hopf algebra; finiteness of `Γ(X, ⊤)` as a `K`-module is
   `Scheme.Hom.finite_appTop`.
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace Fermat

/-- **The Hopf-algebra structure mathlib attaches to a cogroup object of `CommAlgCat K`**,
named at an object of the form `op (CommAlgCat.of K A)`.

This is `inferInstance`, and it has to be written by hand only because instance search
will not solve `↥(?X.unop) =?= A`. -/
@[implicit_reducible] def hopfAlgebraOfGrpObj (K : Type u) [CommRing K]
    (X : (CommAlgCat.{u} K)ᵒᵖ) [GrpObj X] : HopfAlgebra K X.unop := inferInstance

/-- **Yoneda: a functorial group structure on the `R`-points of `Spec A` makes `A` a
cogroup algebra**, hence (through mathlib's `CommHopfAlgCat` bridge) a Hopf algebra.

`F` is the functor of points as a presheaf of groups on `CommAlgCat K`, `α` identifies its
value at `R` with the `K`-algebra maps `A →ₐ[K] R`, and `hα` is naturality. -/
theorem nonempty_grpObj_of_yoneda (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]
    (F : CommAlgCat.{u} K ⥤ GrpCat.{u})
    (α : ∀ R : CommAlgCat.{u} K, (A →ₐ[K] R) ≃ F.obj R)
    (hα : ∀ (R S : CommAlgCat.{u} K) (ψ : R ⟶ S) (v : A →ₐ[K] R),
      α S (ψ.hom.comp v) = F.map ψ (α R v)) :
    Nonempty (GrpObj (op (CommAlgCat.of K A))) := by
  classical
  let C := (CommAlgCat.{u} K)ᵒᵖ
  let Y : C := op (CommAlgCat.of K A)
  let G : Cᵒᵖ ⥤ GrpCat.{u} :=
    { obj := fun Z => F.obj Z.unop.unop
      map := fun {Z Z'} φ => F.map φ.unop.unop
      map_id := fun Z => F.map_id _
      map_comp := fun {Z Z' Z''} φ φ' => F.map_comp _ _ }
  let e : (G ⋙ forget _).RepresentableBy Y :=
    { homEquiv := fun {Z} => (CategoryTheory.opEquiv Z Y).trans
        (Equiv.trans ⟨fun h => h.hom, fun ψ => ConcreteCategory.ofHom ψ,
          fun h => by simp, fun ψ => by simp⟩ (α Z.unop))
      homEquiv_comp := fun {Z Z'} h k => hα Z'.unop Z.unop h.unop k.unop.hom }
  exact ⟨GrpObj.ofRepresentableBy Y G e⟩

/-- **The `R`-points of a scheme `X` over an affine base `Spec K`.** -/
abbrev SchemePts {X : Scheme.{u}} {K : Type u} [CommRing K] (p : X ⟶ Spec (CommRingCat.of K))
    (R : CommAlgCat.{u} K) : Type u :=
  {v : Spec (CommRingCat.of (R : Type u)) ⟶ X //
    v ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K R))}

/-- **A finite affine group scheme over `Spec K` is `Spec` of a finite commutative Hopf
`K`-algebra.**

The group structure is supplied as a functor `F` on `CommAlgCat K` together with an
identification `β` of `F.obj R` with the `R`-points of `X` over `Spec K`, and the
compatibility `hβ` of `F.map` with base change. -/
theorem exists_hopfAlgebra_of_ptsFunctor {X : Scheme.{u}} {K : Type u} [CommRing K]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsFinite p]
    (F : CommAlgCat.{u} K ⥤ GrpCat.{u})
    (β : ∀ R : CommAlgCat.{u} K, SchemePts p R ≃ F.obj R)
    (hβ : ∀ (R S : CommAlgCat.{u} K) (ψ : R ⟶ S) (a : SchemePts p R) (b : SchemePts p S),
      b.1 = Spec.map (CommRingCat.ofHom ψ.hom.toRingHom) ≫ a.1 → β S b = F.map ψ (β R a)) :
    ∃ (A : Type u) (_ : CommRing A) (_ : HopfAlgebra K A) (_ : Module.Finite K A),
      Nonempty (X ≅ Spec (CommRingCat.of A)) := by
  classical
  haveI : IsAffine X := isAffine_of_isAffineHom p
  let kA : CommRingCat.of K ⟶ Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop
  letI : Algebra K (Γ(X, ⊤) : CommRingCat.{u}) := kA.hom.toAlgebra
  -- the structure morphism, read through `isoSpec`
  have key : X.isoSpec.hom ≫ Spec.map kA = p := by
    have h := Scheme.isoSpec_hom_naturality (X := X) (Y := Spec (CommRingCat.of K)) p
    rw [Scheme.isoSpec_Spec_hom] at h
    rw [show kA = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop from rfl,
      Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have keyinv : X.isoSpec.inv ≫ p = Spec.map kA := by
    rw [← key, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  -- the geometric half of the Yoneda equivalence: `Γ ⊣ Spec`
  let α : ∀ R : CommAlgCat.{u} K,
      ((Γ(X, ⊤) : CommRingCat.{u}) →ₐ[K] R) ≃ SchemePts p R := fun R =>
    { toFun := fun φ => ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.isoSpec.inv, by
        rw [Category.assoc, keyinv, ← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        exact φ.commutes x⟩
      invFun := fun v =>
        { toRingHom := (Spec.preimage (v.1 ≫ X.isoSpec.hom)).hom
          commutes' := fun r => by
            have : kA ≫ Spec.preimage (v.1 ≫ X.isoSpec.hom)
                = CommRingCat.ofHom (algebraMap K R) := by
              apply Spec.map_injective
              rw [Spec.map_comp, Spec.map_preimage, Category.assoc, key, v.2]
            exact congrArg (fun t => CommRingCat.Hom.hom t r) this }
      left_inv := fun φ => by
        apply AlgHom.coe_ringHom_injective
        show (Spec.preimage ((Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.isoSpec.inv) ≫
          X.isoSpec.hom)).hom = φ.toRingHom
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Spec.preimage_map]
        rfl
      right_inv := fun v => by
        apply Subtype.ext
        show Spec.map (CommRingCat.ofHom (Spec.preimage (v.1 ≫ X.isoSpec.hom)).hom) ≫
          X.isoSpec.inv = v.1
        rw [show CommRingCat.ofHom (Spec.preimage (v.1 ≫ X.isoSpec.hom)).hom
              = Spec.preimage (v.1 ≫ X.isoSpec.hom) from rfl,
          Spec.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id] }
  -- Yoneda
  obtain ⟨gr⟩ := nonempty_grpObj_of_yoneda K (Γ(X, ⊤) : CommRingCat.{u}) F
    (fun R => (α R).trans (β R))
    (fun R S ψ v => by
      refine hβ R S ψ (α R v) (α S (ψ.hom.comp v)) ?_
      show Spec.map (CommRingCat.ofHom (ψ.hom.comp v).toRingHom) ≫ X.isoSpec.inv
        = Spec.map (CommRingCat.ofHom ψ.hom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom v.toRingHom) ≫ X.isoSpec.inv
      rw [← Category.assoc, ← Spec.map_comp]
      rfl)
  letI := gr
  letI : HopfAlgebra K (Γ(X, ⊤) : CommRingCat.{u}) :=
    hopfAlgebraOfGrpObj K (op (CommAlgCat.of K (Γ(X, ⊤) : CommRingCat.{u})))
  haveI : Module.Finite K (Γ(X, ⊤) : CommRingCat.{u}) := by
    have h1 : (p.appTop).hom.Finite := p.finite_appTop
    have h2 : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).Finite := by
      apply RingHom.Finite.of_surjective
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    exact h1.comp h2
  exact ⟨Γ(X, ⊤), inferInstance, inferInstance, inferInstance, ⟨X.isoSpec⟩⟩

end Fermat

end
