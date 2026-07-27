/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The rank of a finite flat morphism at a REDUCED geometric fibre is its number of points

For a finite flat morphism `h : X ⟶ Y` and a geometric point `g : Spec K ⟶ Y` (`K`
algebraically closed), the fibre `X ×_Y Spec K` is `Spec A` for a finite `K`-algebra `A`, and
`Scheme.Hom.finrank h` at the image point is `dim_K A`.  If that fibre is **reduced** then `A`
is a product of copies of `K`, so its dimension is exactly the number of `K`-points:

* `AlgebraicGeometry.Scheme.Hom.finrank_eq_card_geometricPoints` — the headline statement,
  `h.finrank (g y) = Nat.card {s : Spec K ⟶ X // s ≫ h = g}`.

Reducedness is the whole content and it is **not** free: in residue characteristic `p` a finite
flat group scheme such as `ker F ⊆ 𝔾_a` has one geometric point and rank `p`.  In characteristic
zero it is Cartier's theorem.  This file isolates everything *except* that input, so a consumer
supplies reducedness alone.

The two halves are separately useful and both are stated here:

* `Algebra.finrank_eq_card_algHom` — a finite **reduced** algebra over an algebraically closed
  field has `dim_K A = #(A →ₐ[K] K)`.  Without reducedness only `≤` holds, and that direction is
  mathlib's `card_algHom_le_finrank`.
* `AlgebraicGeometry.fibrePointEquivAlgHom` — the geometric half: `K`-points of `X` over `g` are
  in bijection with `K`-algebra maps out of the fibre algebra.  This is the translation that a
  consumer working with functors of points needs, and it holds with no hypothesis on the fibre.

`AlgebraicGeometry.exists_algebra_iso_of_isFinite` (an affine morphism to `Spec K` presents its
source as `Spec` of a `K`-algebra) is the glue and is stated separately because the `K`-algebra
it produces, `Γ(P, ⊤)` with the structure map read through `Spec.homEquiv`, is not canonical
enough to be an instance.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace Algebra

variable (K A : Type u) [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
  [Module.Finite K A]

section

variable {A}

instance moduleFiniteQuotientMaximal (m : MaximalSpectrum A) : Module.Finite K (A ⧸ m.asIdeal) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal).toLinearMap
    Ideal.Quotient.mk_surjective

/-- The `K`-algebra map `A →ₐ[K] K` cutting out a maximal ideal of a finite algebra over an
algebraically closed field: the residue field at a maximal ideal is `K` itself. -/
noncomputable def algHomOfMaximal (m : MaximalSpectrum A) : A →ₐ[K] K :=
  haveI : m.asIdeal.IsMaximal := m.isMaximal
  haveI : m.asIdeal.IsPrime := m.isMaximal.isPrime
  haveI : IsDomain (A ⧸ m.asIdeal) := Ideal.Quotient.isDomain _
  haveI : Algebra.IsIntegral K (A ⧸ m.asIdeal) := Algebra.IsIntegral.of_finite K _
  (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm.toAlgHom.comp
      (Ideal.Quotient.mkₐ K m.asIdeal)

theorem algHomOfMaximal_apply_eq_zero_iff (m : MaximalSpectrum A) (x : A) :
    algHomOfMaximal K m x = 0 ↔ x ∈ m.asIdeal := by
  haveI : m.asIdeal.IsMaximal := m.isMaximal
  haveI : m.asIdeal.IsPrime := m.isMaximal.isPrime
  haveI : IsDomain (A ⧸ m.asIdeal) := Ideal.Quotient.isDomain _
  haveI : Algebra.IsIntegral K (A ⧸ m.asIdeal) := Algebra.IsIntegral.of_finite K _
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (map_eq_zero_iff _ (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral).symm.injective)

theorem algHomOfMaximal_injective : Function.Injective (algHomOfMaximal K (A := A)) := by
  intro m m' hmm
  refine MaximalSpectrum.ext (Ideal.ext fun x => ?_)
  rw [← algHomOfMaximal_apply_eq_zero_iff K m x, ← algHomOfMaximal_apply_eq_zero_iff K m' x, hmm]

end

/-- Over an algebraically closed field every residue field of a finite algebra is the base field
itself. -/
theorem finrank_quotient_maximal_eq_one (m : MaximalSpectrum A) :
    Module.finrank K (A ⧸ m.asIdeal) = 1 := by
  haveI : m.asIdeal.IsMaximal := m.isMaximal
  haveI : m.asIdeal.IsPrime := m.isMaximal.isPrime
  haveI : IsDomain (A ⧸ m.asIdeal) := Ideal.Quotient.isDomain _
  haveI : Algebra.IsIntegral K (A ⧸ m.asIdeal) := Algebra.IsIntegral.of_finite K _
  have hb : Function.Bijective (algebraMap K (A ⧸ m.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m.asIdeal)) hb).toLinearEquiv.finrank_eq ▸ by
    simp

/-- **A finite REDUCED algebra over an algebraically closed field has rank equal to its number of
`K`-points.**

Reducedness is essential: `K[x]/(x²)` has rank `2` and a single `K`-point.  Without it only `≤`
holds, which is mathlib's `card_algHom_le_finrank`. -/
theorem finrank_eq_card_algHom [IsReduced A] :
    Module.finrank K A = Nat.card (A →ₐ[K] K) := by
  haveI : IsArtinianRing A := isArtinian_of_tower K inferInstance
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have hpi : Module.finrank K A = Nat.card (MaximalSpectrum A) := by
    have e : A ≃ₐ[K] ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal :=
      (IsArtinianRing.equivPi A).restrictScalars K
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp [finrank_quotient_maximal_eq_one, Nat.card_eq_fintype_card]
  rw [hpi]
  refine le_antisymm (Nat.card_le_card_of_injective _ (algHomOfMaximal_injective K)) ?_
  exact (card_algHom_le_finrank K A K).trans_eq hpi

end Algebra

namespace AlgebraicGeometry

/-- **An affine morphism to `Spec K` presents its source as `Spec` of a `K`-algebra**, and a
finite one presents it as `Spec` of a module-finite `K`-algebra. -/
theorem exists_algebra_iso_of_isFinite {P : Scheme.{u}} {K : Type u} [CommRing K]
    (q : P ⟶ Spec (CommRingCat.of K)) [IsFinite q] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A) (_ : Module.Finite K A)
      (e : P ≅ Spec (CommRingCat.of A)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) = q := by
  haveI : IsAffine P := isAffine_of_isAffineHom q
  let ψ : CommRingCat.of K ⟶ Γ(P, ⊤) := Spec.homEquiv (P.isoSpec.inv ≫ q)
  letI : Algebra K Γ(P, ⊤) := ψ.hom.toAlgebra
  have h1 : CommRingCat.ofHom (algebraMap K Γ(P, ⊤)) = ψ := rfl
  have h2 : P.isoSpec.hom ≫ Spec.map ψ = q := by simp [ψ]
  have hfin : IsFinite (Spec.map ψ) := by
    have hh : Spec.map ψ = P.isoSpec.inv ≫ q := by rw [← h2]; simp
    rw [hh]; infer_instance
  rw [IsFinite.SpecMap_iff] at hfin
  exact ⟨Γ(P, ⊤), inferInstance, inferInstance,
    (RingHom.finite_algebraMap (A := K) (B := Γ(P, ⊤))).mp hfin, P.isoSpec,
    by rw [h1]; exact h2⟩

section FibrePoints

variable {X Y : Scheme.{u}} (h : X ⟶ Y) {K : Type u} [CommRing K]
    (g : Spec (CommRingCat.of K) ⟶ Y) {A : Type u} [CommRing A] [Algebra K A]
    (e : pullback h g ≅ Spec (CommRingCat.of A))

/-- The morphism `Spec K ⟶ Spec A` attached to a `K`-point of `X` over `g`. -/
noncomputable def fibrePointHom (s : {s : Spec (CommRingCat.of K) ⟶ X // s ≫ h = g}) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A) :=
  pullback.lift s.1 (𝟙 _) (by rw [s.2, Category.id_comp]) ≫ e.hom

omit [Algebra K A] in
theorem fibrePointHom_comp_fst (s : {s : Spec (CommRingCat.of K) ⟶ X // s ≫ h = g}) :
    fibrePointHom h g e s ≫ e.inv ≫ pullback.fst h g = s.1 := by
  rw [fibrePointHom, Category.assoc, ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp,
    pullback.lift_fst]

theorem ofHom_algHom_comp (φ : A →ₐ[K] K) :
    CommRingCat.ofHom (algebraMap K A) ≫ CommRingCat.ofHom φ.toRingHom
      = 𝟙 (CommRingCat.of K) := by
  ext r; exact φ.commutes r

variable (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) = pullback.snd h g)

include he

theorem eInv_comp_snd : e.inv ≫ pullback.snd h g
    = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]

theorem fibrePointHom_comp (s : {s : Spec (CommRingCat.of K) ⟶ X // s ≫ h = g}) :
    fibrePointHom h g e s ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) = 𝟙 _ := by
  rw [fibrePointHom, Category.assoc, he, pullback.lift_snd]

/-- The `K`-algebra map out of the fibre algebra attached to a `K`-point of `X` over `g`. -/
noncomputable def algHomOfFibrePoint (s : {s : Spec (CommRingCat.of K) ⟶ X // s ≫ h = g}) :
    A →ₐ[K] K :=
  { __ := (Spec.preimage (fibrePointHom h g e s)).hom
    commutes' := fun r => by
      have hc := congrArg Spec.preimage (fibrePointHom_comp h g e he s)
      rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id] at hc
      exact congrArg (fun f => CommRingCat.Hom.hom f r) hc }

theorem algHomOfFibrePoint_apply (s) (x : A) :
    algHomOfFibrePoint h g e he s x = (Spec.preimage (fibrePointHom h g e s)).hom x := rfl

theorem fibrePointOfAlgHom_cond (φ : A →ₐ[K] K) :
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ e.inv ≫ pullback.fst h g) ≫ h = g := by
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (e.inv),
    eInv_comp_snd h g e he, ← Category.assoc, ← Spec.map_comp, ofHom_algHom_comp φ,
    Spec.map_id, Category.id_comp]

/-- **`K`-points of `X` over `g` are exactly the `K`-algebra maps out of the fibre algebra.**

No hypothesis on the fibre is needed: this is the universal property of the pullback plus the
`Γ ⊣ Spec` adjunction, and it is the translation a consumer working with functors of points
needs in order to count geometric points. -/
noncomputable def fibrePointEquivAlgHom :
    {s : Spec (CommRingCat.of K) ⟶ X // s ≫ h = g} ≃ (A →ₐ[K] K) where
  toFun s := algHomOfFibrePoint h g e he s
  invFun φ := ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ e.inv ≫ pullback.fst h g,
    fibrePointOfAlgHom_cond h g e he φ⟩
  left_inv s := by
    refine Subtype.ext ?_
    show Spec.map (CommRingCat.ofHom (algHomOfFibrePoint h g e he s).toRingHom)
        ≫ e.inv ≫ pullback.fst h g = s.1
    have hid : CommRingCat.ofHom (algHomOfFibrePoint h g e he s).toRingHom
        = Spec.preimage (fibrePointHom h g e s) := rfl
    rw [hid, Spec.map_preimage]
    exact fibrePointHom_comp_fst h g e s
  right_inv φ := by
    have hlift : pullback.lift
        (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ e.inv ≫ pullback.fst h g) (𝟙 _)
        (by rw [fibrePointOfAlgHom_cond h g e he φ, Category.id_comp])
        = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ e.inv := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, Category.assoc]
      · rw [pullback.lift_snd, Category.assoc, eInv_comp_snd h g e he, ← Spec.map_comp,
          ofHom_algHom_comp φ, Spec.map_id]
    have hfp : fibrePointHom h g e
        (⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ e.inv ≫ pullback.fst h g,
          fibrePointOfAlgHom_cond h g e he φ⟩)
        = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
      rw [fibrePointHom, hlift, Category.assoc, e.inv_hom_id, Category.comp_id]
    refine AlgHom.ext fun x => ?_
    rw [algHomOfFibrePoint_apply, hfp, Spec.preimage_map]
    rfl

end FibrePoints

/-- **The rank of a finite flat morphism, read off from an affine presentation of a fibre over a
field.** -/
theorem finrank_eq_finrank_of_iso {X Y : Scheme.{u}} (h : X ⟶ Y) [Flat h] [IsFinite h]
    {K : Type u} [Field K] (g : Spec (CommRingCat.of K) ⟶ Y)
    {A : Type u} [CommRing A] [Algebra K A] [Module.Finite K A]
    (e : pullback h g ≅ Spec (CommRingCat.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) = pullback.snd h g)
    (y : Spec (CommRingCat.of K)) :
    h.finrank (g y) = Module.finrank K A := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    rw [Flat.SpecMap_iff]
    exact (RingHom.flat_algebraMap_iff (R := K) (S := A)).mpr inferInstance
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    rw [IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := K) (B := A)).mpr inferInstance
  rw [← Scheme.Hom.finrank_pullback_snd h g y, ← he, Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

/-- **The rank of a finite flat morphism at a point equals the number of geometric points of the
fibre there, PROVIDED that fibre is reduced.**

This is the whole "finite flat + reduced geometric fibres ⟹ the rank is the point count"
dictionary, with reducedness left as the single hypothesis a consumer must supply.  It is not
removable: over `𝔽_p`, `ker F ⊆ 𝔾_a` is finite flat of rank `p` with one geometric point. -/
theorem Scheme.Hom.finrank_eq_card_geometricPoints {X Y : Scheme.{u}} (h : X ⟶ Y)
    [Flat h] [IsFinite h] {K : Type u} [Field K] [IsAlgClosed K]
    (g : Spec (CommRingCat.of K) ⟶ Y) (hred : IsReduced (pullback h g))
    (y : Spec (CommRingCat.of K)) :
    h.finrank (g y) = Nat.card {s : Spec (CommRingCat.of K) ⟶ X // s ≫ h = g} := by
  obtain ⟨A, _, _, _, e, he⟩ := exists_algebra_iso_of_isFinite (pullback.snd h g)
  haveI : IsReduced (Spec (CommRingCat.of A)) := isReduced_of_isOpenImmersion e.inv
  haveI : _root_.IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).mp inferInstance
  rw [finrank_eq_finrank_of_iso h g e he y, Algebra.finrank_eq_card_algHom K A]
  exact (Nat.card_congr (fibrePointEquivAlgHom h g e he)).symm

end AlgebraicGeometry
