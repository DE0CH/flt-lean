/-
HopfKaehler.lean — own work for the Fermat project.

# Fontaine's translation isomorphism: the Kähler differentials of a
# commutative Hopf algebra are extended from the base

For a commutative Hopf algebra `G` over a commutative ring `R` the
module of Kähler differentials is INDUCED FROM THE BASE,
`Ω[G⁄R] ≅ G ⊗[R] ω_G` with `ω_G = I/I²` the co-Lie module at the
identity (`I = ker ε` the augmentation ideal).  Geometrically this is
the statement that translation by the generic point trivialises the
sheaf of differentials of a group scheme.  References: Fontaine,
*Il n'y a pas de variété abélienne sur ℤ*, §1; Oort–Tate 1970 §1;
Tate, *Finite flat group schemes*, §2, in Cornell–Silverman–Stevens.

The route, and what is PROVEN here:

* the SHEAR map `θ (a ⊗ b) = (a ⊗ 1) · Δ b` is an algebra
  AUTOMORPHISM of `G ⊗[R] G` (`shear_comp_shearInv`,
  `shearInv_comp_shear`).  Its inverse `θ' (a ⊗ b) = (a ⊗ 1) · ψ b`,
  `ψ b = Σ S(b₁) ⊗ b₂`, is where the ANTIPODE is spent — a bialgebra
  would not suffice;
* `θ` carries the multiplication onto the augmentation,
  `p ∘ θ = μ` (`aug_comp_shear`), where `p (a ⊗ b) = a · ε b`;
* consequently `θ` transports the Kähler differentials
  `Ω[G⁄R] = ker(μ)/ker(μ)²` onto the conormal module of the
  augmentation, `G`-linearly
  (`kaehlerEquivKerAugCotangent`).

The proofs of the two antipode identities are Sweedler-free: they are
computations in the CONVOLUTION GROUP `WithConv (G →ₐ[R] G ⊗[R] G)`,
where `ψ = includeLeft⁻¹ ⋆ includeRight` and `Δ = includeLeft ⋆
includeRight`, so that `θ ∘ ψ = includeRight` is `inv_mul_cancel_left`.
Post-composition with an algebra map is a monoid map for convolution
(`AlgHom.comp_convMul_distrib`), which is what makes this work.

The remaining step is pure commutative algebra with no Hopf content —
that the conormal module of a base-changed augmentation is the base
change of the conormal module (`cotangent_ker_augOf_equiv`) — and it
needed no new development either: mathlib already has it as
`Ideal.tensorCotangentEquiv`, so all that was required was the
identification `ker (augOf φ) = J · (A ⊗[R] B)` of `ker_augOf_eq`.

**This module is sorry-free**, and with it
`exists_kaehler_linearEquiv_baseChange_of_hopf_package` in
`HardlyRamified/ModThree.lean` is PROVEN.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section

open scoped TensorProduct
open Bialgebra HopfAlgebra WithConv Coalgebra

noncomputable section

namespace FontaineTranslation


variable {R G : Type*} [CommRing R] [CommRing G] [HopfAlgebra R G]

/-! ### Convolution wrappers (all `rfl`-level over `WithConv`) -/

section Conv
variable {B : Type*} [CommRing B] [Algebra R B]

/-- Convolution product of two algebra maps out of a Hopf algebra. -/
def cmul (f g : G →ₐ[R] B) : G →ₐ[R] B := (toConv f * toConv g).ofConv

/-- Convolution unit. -/
def cone : G →ₐ[R] B := (Algebra.ofId R B).comp (counitAlgHom R G)

/-- Convolution inverse (precomposition with the antipode). -/
def cinv (f : G →ₐ[R] B) : G →ₐ[R] B := f.comp (antipodeAlgHom R G)

lemma cmul_def (f g : G →ₐ[R] B) :
    cmul f g = (Algebra.TensorProduct.lmul' R).comp
      ((Algebra.TensorProduct.map f g).comp (comulAlgHom R G)) := rfl

lemma cmul_cone (f : G →ₐ[R] B) : cmul f cone = f :=
  congrArg WithConv.ofConv (mul_one (toConv f))

variable {C : Type*} [CommRing C] [Algebra R C]

lemma comp_cmul (h : B →ₐ[R] C) (f g : G →ₐ[R] B) :
    h.comp (cmul f g) = cmul (h.comp f) (h.comp g) :=
  AlgHom.comp_convMul_distrib h (toConv f) (toConv g)

lemma comp_cinv (h : B →ₐ[R] C) (f : G →ₐ[R] B) :
    h.comp (cinv f) = cinv (h.comp f) :=
  (AlgHom.comp_assoc _ _ _).symm

end Conv

section ConvGroup
variable {B : Type*} [CommRing B] [Bialgebra R B]

lemma cinv_cmul_cancel_left (f g : G →ₐ[R] B) : cmul (cinv f) (cmul f g) = g :=
  congrArg WithConv.ofConv (inv_mul_cancel_left (toConv f) (toConv g))

lemma cmul_cinv_cancel_left (f g : G →ₐ[R] B) : cmul f (cmul (cinv f) g) = g :=
  congrArg WithConv.ofConv (mul_inv_cancel_left (toConv f) (toConv g))

end ConvGroup

/-- The base change `A ⊗[R] B →ₐ[R] A` of an augmentation `φ : B →ₐ[R] R`. -/
def augOf {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : B →ₐ[R] R) : A ⊗[R] B →ₐ[R] A :=
  Algebra.TensorProduct.lift (AlgHom.id R A) ((Algebra.ofId R A).comp φ)
    (fun _ _ => Commute.all _ _)


/-! ### The shear automorphism -/

variable (R G)

/-- The shear map `θ (a ⊗ b) = (a ⊗ 1) · Δ b`. -/
def shear : G ⊗[R] G →ₐ[R] G ⊗[R] G :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft (comulAlgHom R G)
    (fun _ _ => Commute.all _ _)

/-- `ψ b = Σ S(b₁) ⊗ b₂`. -/
def psi : G →ₐ[R] G ⊗[R] G :=
  (Algebra.TensorProduct.map (antipodeAlgHom R G) (AlgHom.id R G)).comp (comulAlgHom R G)

/-- The inverse shear `θ' (a ⊗ b) = (a ⊗ 1) · ψ b`. -/
def shearInv : G ⊗[R] G →ₐ[R] G ⊗[R] G :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft (psi R G)
    (fun _ _ => Commute.all _ _)

/-- The augmentation `p (a ⊗ b) = a · ε b` of `G ⊗ G` as a `G`-algebra. -/
def aug : G ⊗[R] G →ₐ[R] G := augOf (counitAlgHom R G)

variable {R G}

@[simp] lemma shear_tmul (a b : G) :
    shear R G (a ⊗ₜ[R] b) = (a ⊗ₜ[R] (1 : G)) * comul b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

@[simp] lemma shearInv_tmul (a b : G) :
    shearInv R G (a ⊗ₜ[R] b) = (a ⊗ₜ[R] (1 : G)) * psi R G b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

@[simp] lemma augOf_tmul {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : B →ₐ[R] R) (a : A) (b : B) :
    augOf (A := A) φ (a ⊗ₜ[R] b) = a * algebraMap R A (φ b) :=
  Algebra.TensorProduct.lift_tmul (AlgHom.id R A) ((Algebra.ofId R A).comp φ)
    (fun _ _ => Commute.all _ _) a b

@[simp] lemma aug_tmul (a b : G) :
    aug R G (a ⊗ₜ[R] b) = a * algebraMap R G (counit b) :=
  augOf_tmul _ _ _

@[simp] lemma shear_comp_includeLeft :
    (shear R G).comp Algebra.TensorProduct.includeLeft
      = (Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G) :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

@[simp] lemma shear_comp_includeRight :
    (shear R G).comp Algebra.TensorProduct.includeRight = comulAlgHom R G :=
  Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

@[simp] lemma shearInv_comp_includeLeft :
    (shearInv R G).comp Algebra.TensorProduct.includeLeft
      = (Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G) :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)

@[simp] lemma shearInv_comp_includeRight :
    (shearInv R G).comp Algebra.TensorProduct.includeRight = psi R G :=
  Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)

@[simp] lemma aug_comp_includeLeft :
    (aug R G).comp Algebra.TensorProduct.includeLeft = AlgHom.id R G := by
  ext a
  simp [Algebra.TensorProduct.includeLeft_apply]

@[simp] lemma aug_comp_includeRight :
    (aug R G).comp Algebra.TensorProduct.includeRight
      = (Algebra.ofId R G).comp (counitAlgHom R G) := by
  ext b
  simp [Algebra.TensorProduct.includeRight_apply, Algebra.ofId]

/-- `Δ = includeLeft ⋆ includeRight`. -/
lemma cmul_includeLeft_includeRight :
    cmul (Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G)
      (Algebra.TensorProduct.includeRight) = comulAlgHom R G := by
  rw [cmul_def]
  have h : (Algebra.TensorProduct.lmul' R).comp
      (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G)
        (Algebra.TensorProduct.includeRight : G →ₐ[R] G ⊗[R] G))
      = AlgHom.id R (G ⊗[R] G) := by
    ext x <;> simp
  rw [← AlgHom.comp_assoc, h, AlgHom.id_comp]

/-- `ψ = includeLeft⁻¹ ⋆ includeRight`. -/
lemma cmul_cinv_includeLeft_includeRight :
    cmul (cinv (Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G))
      (Algebra.TensorProduct.includeRight) = psi R G := by
  rw [cmul_def]
  have h : (Algebra.TensorProduct.lmul' R).comp
      (Algebra.TensorProduct.map
        (cinv (Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G))
        (Algebra.TensorProduct.includeRight : G →ₐ[R] G ⊗[R] G))
      = Algebra.TensorProduct.map (antipodeAlgHom R G) (AlgHom.id R G) := by
    ext x <;> simp [cinv]
  rw [← AlgHom.comp_assoc, h]
  rfl

/-- `θ ∘ ψ = includeRight` — this is where the antipode is spent. -/
lemma shear_comp_psi :
    (shear R G).comp (psi R G) = (Algebra.TensorProduct.includeRight : G →ₐ[R] G ⊗[R] G) := by
  rw [← cmul_cinv_includeLeft_includeRight, comp_cmul, comp_cinv, shear_comp_includeLeft,
    shear_comp_includeRight, ← cmul_includeLeft_includeRight, cinv_cmul_cancel_left]

/-- `θ' ∘ Δ = includeRight`. -/
lemma shearInv_comp_comul :
    (shearInv R G).comp (comulAlgHom R G)
      = (Algebra.TensorProduct.includeRight : G →ₐ[R] G ⊗[R] G) := by
  rw [← cmul_includeLeft_includeRight, comp_cmul, shearInv_comp_includeLeft,
    shearInv_comp_includeRight, ← cmul_cinv_includeLeft_includeRight, cmul_cinv_cancel_left]

/-- `p ∘ Δ = id`: the counit axiom. -/
lemma aug_comp_comul : (aug R G).comp (comulAlgHom R G) = AlgHom.id R G := by
  rw [← cmul_includeLeft_includeRight, comp_cmul, aug_comp_includeLeft, aug_comp_includeRight,
    show ((Algebra.ofId R G).comp (counitAlgHom R G)) = (cone : G →ₐ[R] G) from rfl, cmul_cone]

@[simp] lemma shear_psi_apply (b : G) : shear R G (psi R G b) = (1 : G) ⊗ₜ[R] b :=
  AlgHom.congr_fun shear_comp_psi b

@[simp] lemma shearInv_comul_apply (b : G) :
    shearInv R G (comul b) = (1 : G) ⊗ₜ[R] b :=
  AlgHom.congr_fun shearInv_comp_comul b

@[simp] lemma aug_comul_apply (b : G) : aug R G (comul b) = b :=
  AlgHom.congr_fun aug_comp_comul b

lemma shear_comp_shearInv : (shear R G).comp (shearInv R G) = AlgHom.id R (G ⊗[R] G) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [Algebra.TensorProduct.tmul_mul_tmul]

lemma shearInv_comp_shear : (shearInv R G).comp (shear R G) = AlgHom.id R (G ⊗[R] G) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- `p ∘ θ = μ`: the shear carries the augmentation onto the multiplication. -/
lemma aug_comp_shear :
    (aug R G).comp (shear R G) = Algebra.TensorProduct.lmul' R := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp


/-! ### Transfer of the cotangent module along the shear -/

variable (R G)

/-- The shear as a `G`-algebra map, `G` acting through the LEFT factor. -/
def shearG : (G ⊗[R] G) →ₐ[G] (G ⊗[R] G) where
  toFun := shear R G
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun a => by simp [Algebra.TensorProduct.algebraMap_apply]

/-- The inverse shear as a `G`-algebra map. -/
def shearInvG : (G ⊗[R] G) →ₐ[G] (G ⊗[R] G) where
  toFun := shearInv R G
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := fun a => by simp [Algebra.TensorProduct.algebraMap_apply, psi]

variable {R G}

lemma ker_lmul'_le_comap :
    KaehlerDifferential.ideal R G ≤ (RingHom.ker (aug R G)).comap (shearG R G) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  show aug R G (shear R G x) = 0
  rw [← AlgHom.comp_apply, aug_comp_shear, hx]

lemma ker_aug_le_comap :
    RingHom.ker (aug R G) ≤ (KaehlerDifferential.ideal R G).comap (shearInvG R G) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  show Algebra.TensorProduct.lmul' R (shearInv R G x) = 0
  rw [← AlgHom.comp_apply, ← aug_comp_shear, AlgHom.comp_apply, AlgHom.comp_apply]
  show aug R G ((shear R G) ((shearInv R G) x)) = 0
  rw [← AlgHom.comp_apply (shear R G), shear_comp_shearInv, AlgHom.id_apply, hx]

/-- **The shear transports the Kähler differentials onto the conormal module of the
augmentation.** -/
def kaehlerEquivKerAugCotangent :
    Ω[G⁄R] ≃ₗ[G] (RingHom.ker (aug R G)).Cotangent where
  __ := Ideal.mapCotangent (R := G) _ _ (shearG R G) ker_lmul'_le_comap
  invFun := Ideal.mapCotangent (R := G) _ _ (shearInvG R G) ker_aug_le_comap
  left_inv x := by
    obtain ⟨x, rfl⟩ := (KaehlerDifferential.ideal R G).toCotangent_surjective x
    show Ideal.mapCotangent _ _ (shearInvG R G) ker_aug_le_comap
      (Ideal.mapCotangent _ _ (shearG R G) ker_lmul'_le_comap
        ((KaehlerDifferential.ideal R G).toCotangent x)) = _
    rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    congr 1
    ext
    show shearInv R G (shear R G (x : G ⊗[R] G)) = (x : G ⊗[R] G)
    rw [← AlgHom.comp_apply, shearInv_comp_shear, AlgHom.id_apply]
  right_inv x := by
    obtain ⟨x, rfl⟩ := (RingHom.ker (aug R G)).toCotangent_surjective x
    show Ideal.mapCotangent _ _ (shearG R G) ker_lmul'_le_comap
      (Ideal.mapCotangent _ _ (shearInvG R G) ker_aug_le_comap
        ((RingHom.ker (aug R G)).toCotangent x)) = _
    rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    congr 1
    ext
    show shear R G (shearInv R G (x : G ⊗[R] G)) = (x : G ⊗[R] G)
    rw [← AlgHom.comp_apply, shear_comp_shearInv, AlgHom.id_apply]

/-! ### The conormal module of a base-changed augmentation (the remaining step) -/

/-- `rid ∘ (id ⊗ φ) = augOf φ`: the augmentation of the base change is the base change of
the augmentation, read through `A ⊗[R] R ≃ A`. -/
lemma rid_comp_map_eq_augOf {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : B →ₐ[R] R) :
    (Algebra.TensorProduct.rid R R A).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R A) φ) = augOf (A := A) φ := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [augOf, Algebra.TensorProduct.lift_tmul, Algebra.smul_def, mul_comm]

/-- **The kernel of a base-changed augmentation is the extended augmentation ideal.**
An augmentation `φ : B →ₐ[R] R` is surjective (it is split by `algebraMap R B`), so
`Algebra.TensorProduct.lTensor_ker` applies. -/
lemma ker_augOf_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : B →ₐ[R] R) :
    RingHom.ker (augOf (A := A) φ)
      = (RingHom.ker φ).map
          (Algebra.TensorProduct.includeRight.toRingHom : B →+* A ⊗[R] B) := by
  have hsurj : Function.Surjective φ := fun r => ⟨algebraMap R B r, φ.commutes r⟩
  show RingHom.ker (augOf (A := A) φ)
      = Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) (RingHom.ker φ)
  rw [← Algebra.TensorProduct.lTensor_ker (A := A) φ hsurj]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, ← rid_comp_map_eq_augOf (A := A) φ]
  simp only [AlgHom.comp_apply]
  exact ⟨fun h => (Algebra.TensorProduct.rid R R A).injective (by simpa using h),
    fun h => by rw [h]; simp⟩

/-- **The conormal module of a base-changed augmentation is the base change of the
conormal module** (PROVEN 2026-07-26).

Let `φ : B →ₐ[R] R` be an augmentation with augmentation ideal `J = ker φ`, and let
`augOf φ : A ⊗[R] B →ₐ[R] A` be its base change along `R → A`, with kernel `K`.  Then
`K/K² ≅ A ⊗[R] (J/J²)`, `A`-linearly.

There is NO Hopf content here, and — the point worth recording — there is no new
commutative algebra either: mathlib already has the whole statement as
`Ideal.tensorCotangentEquiv` (`Mathlib/RingTheory/Ideal/CotangentBaseChange.lean`,
flat base change of a cotangent space).  All that is needed is the identification
`ker (augOf φ) = J · (A ⊗[R] B)` of `ker_augOf_eq`. -/
theorem cotangent_ker_augOf_equiv
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Flat R A]
    (φ : B →ₐ[R] R) :
    Nonempty ((RingHom.ker (augOf (A := A) φ)).Cotangent
      ≃ₗ[A] A ⊗[R] (RingHom.ker φ).Cotangent) :=
  ⟨((Ideal.Cotangent.equivOfEq _ _ (ker_augOf_eq (A := A) φ)).restrictScalars A).trans
    ((RingHom.ker φ).tensorCotangentEquiv R A).symm⟩

/-- **Fontaine's translation isomorphism**: the Kähler differentials of a commutative
Hopf algebra are extended from the base. -/
theorem exists_kaehler_equiv_baseChange_of_hopf
    (R G : Type) [CommRing R] [CommRing G] [HopfAlgebra R G] [Module.Flat R G] :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M),
      Nonempty (Ω[G⁄R] ≃ₗ[G] G ⊗[R] M) := by
  refine ⟨(RingHom.ker (counitAlgHom R G)).Cotangent, inferInstance, inferInstance, ?_⟩
  obtain ⟨e⟩ := cotangent_ker_augOf_equiv (A := G) (counitAlgHom R G)
  exact ⟨kaehlerEquivKerAugCotangent.trans e⟩


end FontaineTranslation
