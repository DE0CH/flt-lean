/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang
-/
module

public import Fermat.FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import Fermat.FLT.QuaternionAlgebra.NumberField
public import Fermat.FLT.DivisionAlgebra.Finiteness
public import Fermat.FLT.AutomorphicForm.GroupTheoryStuff
public import Fermat.FLT.AutomorphicForm.Stuff
public import Fermat.FLT.Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!

# Definition of automorphic forms on a totally definite quaternion algebra

## Main definitions

In the `TotallyDefiniteQuaternionAlgebra` namespace:

* `WeightTwoAutomorphicForm F D R` -- weight 2
  R-valued automorphic forms for the totally definite quaternion algebra `D` over
  the totally real field `F`. Defined as locally-constant functions
  `φ : Dˣ \ (D ⊗ 𝔸_F^∞)ˣ → R` which are right-invariant by some compact open subgroup
  (i.e. ∃ U_φ such that `φ(gu)=φ(g)` for all `u ∈ U`) and have trivial central character
  (i.e. `φ(zg)=φ(g)` for all `z ∈ (𝔸_F^∞)ˣ`).

* `LevelStruct F R`: A structure containing a compact open and a character on it.
* `LevelStruct.form ℒ D`: The submodule `S(U, χ)` of `WeightTwoAutomorphicForm F D R`.

* `LocalLevelStruct F R`: A structure containing a compact open and a character on it.

## VENDOR PROVENANCE AND STATUS (2026-07-27) — READ BEFORE RELEASING

This module and its import closure (109 modules, 20,688 lines: adele rings,
restricted products, Haar characters, totally definite quaternion algebras and
their Hecke algebras) are VENDORED from the reference project `~/cs/FLT`, whose
mathlib pin (`81a5d2`) differs from ours (`a3364fa`). The whole closure builds
green here. Two pin-drift repairs were needed and both are commented at their
sites: `RestrictedProduct.instModuleRestrictedProduct` (an anonymous instance
whose Lean-generated name encoded the root module `FLT`), and one
`Algebra.smul_def` step in `Fermat/FLT/DivisionAlgebra/Finiteness.lean`.

**Axiom policy.** The reference discharges one statement in this closure —
`isFiniteRelIndex_Δ` below — with its tactic `knownin1980s`, i.e.
`axiom knownin1980s {P : Prop} : P`, which proves anything. That module is NOT
vendored; the single use became an ordinary sorried leaf.

**Decomposed 2026-07-27.** `isFiniteRelIndex_Δ` is now proven from two smaller
statements, `index_ray_ne_zero` (finiteness of a ray class group of `F` — no `D`,
no definiteness) and `relIndex_unitsOrder_ne_zero` (Voight 17.7.13: the unit
group of an order in a TOTALLY DEFINITE quaternion algebra is finite modulo the
centre).

**Both halves were then closed the same day, on two branches, and this release
carries both.**

* **`index_ray_ne_zero` PROVEN** from Fujisaki's lemma at `D = F`
  (`NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset F F`) via the
  transport `tensorLid` and the abelian double-coset surjection
  `index_sup_ne_zero_of_finite_doubleCoset`. This required adding
  `public import Fermat.FLT.DivisionAlgebra.Finiteness` to this module; that adds
  NO modules to any consumer's cone, since the only module importing this one
  (`…/QuaternionAlgebra/FiniteDimensional.lean`) already imported `Finiteness`.
* **`relIndex_unitsOrder_ne_zero` PROVEN** from
  `relIndex_range_algebraMap_units_ne_zero` (the same statement with the level
  structure and the double-coset representative `g` stripped off), and that in
  turn from two leaves that separate the two classical inputs:
  `finite_normOne_units_inf_comap` (definite archimedean: `{Nm = 1} ∩ V` is
  finite) and `relIndex_normImage_ne_zero` (Dirichlet units mod fourth powers;
  no definiteness).

**Both of those were then PROVEN in turn (2026-07-28), from three smaller leaves.**
The closure's only unproven statements are now:

* `comap_le_range_units_integers_of_isCompact` — a COMPACT subgroup of `𝔸ᶠ[F]ˣ`
  meets `Fˣ` inside `(𝓞 F)ˣ`. Pure `F`-arithmetic: no `D`, no definiteness.
  (Dirichlet's unit theorem itself is NOT a leaf — mathlib's `Monoid.FG (𝓞 K)ˣ`
  supplies it, via `subgroup_fg_of_le_fg`.)
* `isCompact_normOne_infiniteAdele` — `{x ∈ D ⊗ 𝔸^∞ : Nm(x) = 1}` is compact. Now
  PROVEN (2026-07-28), decomposed over the infinite places into three new leaves —
  `exists_ringEquiv_quaternion_of_isTotallyDefinite` (`D ⊗ F_v ≃+* ℍ` topologically —
  now the ONLY consumer of `IsQuaternionAlgebra.IsTotallyDefinite` in the file),
  `norm_infiniteAdele_apply` (the norm is componentwise) and
  `continuous_infiniteAdeleTensorPiEquiv_symm` (the decomposition is a homeomorphism).
  The last two are definiteness-free. The place-local half
  `isCompact_normOne_completion` is PROVEN, on the way proving
  `norm_quaternion_eq_normSq_sq` (`Nm_{ℍ/ℝ} = normSq²`, absent from the pin) and
  `isCompact_normOne_quaternion`.
* `finite_setOf_tmul_mem_of_isCompact` — `D` is discrete and closed in `D ⊗ 𝔸_F`,
  so `D ∩ (compact × compact)` is finite. Uses neither definiteness nor total
  reality; it is the `[Ring D]` form of `Aux.T_finite` in
  `Fermat/FLT/DivisionAlgebra/Finiteness.lean`.

**This subtree is currently FREE-FLOATING.** Nothing in the transitive cone of
`fermat_last_theorem` consumes it yet. It was vendored to close the "the pin has
no Hilbert modular forms" obstruction recorded at
`carayol_threeadic_realization_of_heckePackage`
(`Fermat/FLT/Modularity/KhareWintenberger.lean`); see that leaf's docstring for
the one obstruction that remains before it can be consumed there — the
quaternionic formalization needs `[F : ℚ]` EVEN, which that leaf does not
assume. Release this together with its first consumer, not before.

-/

@[expose] public section

/-

# Definition of automorphic forms on a totally definite quaternion algebra

## Main definitions

In the `TotallyDefiniteQuaternionAlgebra` namespace:

* `WeightTwoAutomorphicForm F D R` -- weight 2
  R-valued automorphic forms for the totally definite quaternion algebra `D` over
  the totally real field `F`. Defined as locally-constant functions
  `φ : Dˣ \ (D ⊗ 𝔸_F^∞)ˣ → R` which are right-invariant by some compact open subgroup
  (i.e. ∃ U_φ such that `φ(gu)=φ(g)` for all `u ∈ U`) and have trivial central character
  (i.e. `φ(zg)=φ(g)` for all `z ∈ (𝔸_F^∞)ˣ`).

* `WeightTwoAutomorphicFormOfLevel U R` -- weight 2 R-valued automorphic forms of
  level `U`, i.e. `U`-invariant elements of `WeightTwoAutomorphicForm F D R`.
  It is a nontrivial theorem that if `U` is open and `R` is Noetherian then this space
  is a finitely-generated `R`-module; this follows from Fujisaki's lemma.

-/

attribute [-simp] RingHom.toMonoidHom_eq_coe

suppress_compilation

open IsQuaternionAlgebra.NumberField

open scoped FLT

variable (F : Type*) [Field F] [NumberField F] -- if F isn't totally real all the definitions
-- below are garbage mathematically but they typecheck.

variable (D : Type*) [Ring D] [Algebra F D] [WithRigidification F D]
  -- If D isn't totally definite then all the
  -- definitions below are garbage mathematically but they typecheck.

namespace TotallyDefiniteQuaternionAlgebra

open scoped TensorProduct NumberField Adele

local notation "𝓓ˣ" => MonoidHom.range (WithRigidification.unitsIncl F D)
local notation "𝓕ˣ" =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap F M₂(𝔸ᶠ[F]))))
local notation "𝔸ˣ" F =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F]))))

variable {F} in
lemma range_unitsMap_finiteAdeleRing_le_center : (𝔸ˣ F) ≤ .center _ := by
  rintro _ ⟨x, rfl⟩
  simp [Subgroup.mem_center_iff, Units.ext_iff, Algebra.commutes]

open IsDedekindDomain

instance : CommRing (FiniteAdeleRing (𝓞 F) F) := inferInstance
instance : Ring (D ⊗[F] FiniteAdeleRing (𝓞 F) F) := inferInstance

/-- `Dfx` is an abbreviation for $(D\otimes_F\mathbb{A}_F^\infty)^\times.$ -/
abbrev Dfx := (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ

open scoped TensorProduct.RightActions in
/--
This definition is made in mathlib-generality but is *not* the definition of a
weight 2 automorphic form unless `Dˣ` is compact mod centre at infinity.
This hypothesis will be true if `D` is a totally definite quaternion algebra
over a totally real field.
-/
structure WeightTwoAutomorphicForm
  -- defined over R
  (R : Type*) [AddCommMonoid R] where
  /-- The function underlying an automorphic form. -/
  toFun : GL₂(𝔸ᶠ[F]) → R
  left_invt (δ : Dˣ) (g : GL₂(𝔸ᶠ[F])) : toFun (WithRigidification.unitsIncl _ _ δ * g) = (toFun g)
  right_invt : ∃ (U : Subgroup GL₂(𝔸ᶠ[F])), IsOpen (U : Set GL₂(𝔸ᶠ[F])) ∧
    ∀ g, ∀ u ∈ U, toFun (g * u) = toFun g
  trivial_central_char (z : (𝔸ᶠ[F])ˣ) (g : GL₂(𝔸ᶠ[F])) : toFun (z • g) = toFun g

attribute [simp] WeightTwoAutomorphicForm.left_invt WeightTwoAutomorphicForm.trivial_central_char

variable {F D}

namespace WeightTwoAutomorphicForm

section add_comm_group

variable {R : Type*} [AddCommGroup R]

instance : CoeFun (WeightTwoAutomorphicForm F D R) (fun _ ↦ GL₂(𝔸ᶠ[F]) → R) where
  coe := toFun

attribute [coe] WeightTwoAutomorphicForm.toFun

@[ext]
theorem ext (φ ψ : WeightTwoAutomorphicForm F D R) (h : ∀ x, φ x = ψ x) : φ = ψ := by
  cases φ; cases ψ; simp only [mk.injEq]; ext; apply h

@[simp]
lemma left_invt' (f : WeightTwoAutomorphicForm F D R)
    (δ : MonoidHom.range (WithRigidification.unitsIncl F D)) (g : GL₂(𝔸ᶠ[F])) :
    f (δ * g) = f g := by obtain ⟨_, δ, rfl⟩ := δ; simp

@[simp]
lemma trivial_central_char' (f : WeightTwoAutomorphicForm F D R)
    (z : (𝔸ᶠ[F])ˣ) (g : GL₂(𝔸ᶠ[F])) :
    f (z.map (algebraMap _ _).toMonoidHom * g) = f g := by
  convert f.trivial_central_char z g using 2; ext1; simp [Units.smul_def, Algebra.smul_def]

@[simp]
lemma trivial_central_char_right (f : WeightTwoAutomorphicForm F D R)
    (z : (𝔸ᶠ[F])ˣ) (g : GL₂(𝔸ᶠ[F])) :
    f (g * z.map (algebraMap _ _).toMonoidHom) = f g := by
  rw [← f.trivial_central_char' z g]; congr 1; ext1; simp [Algebra.commutes]

/-- The zero automorphic form for a totally definite quaterion algebra. -/
def zero : (WeightTwoAutomorphicForm F D R) where
  toFun := 0
  left_invt δ _ := by simp
  -- this used to be `by simp` but now it times out doing some crazy typeclass search for
  -- `DiscreteTopology (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ`
  right_invt := ⟨⊤, by simp only [Subgroup.coe_top, isOpen_univ, Subgroup.mem_top,
    Pi.zero_apply, imp_self, implies_true, and_self]⟩
  trivial_central_char _ z := by simp

instance : Zero (WeightTwoAutomorphicForm F D R) where
  zero := zero

@[simp]
theorem zero_apply (x : GL₂(𝔸ᶠ[F])) : (0 : WeightTwoAutomorphicForm F D R) x = 0 := rfl

/-- Negation on the space of automorphic forms over a totally definite quaternion algebra. -/
def neg (φ : WeightTwoAutomorphicForm F D R) : WeightTwoAutomorphicForm F D R where
  toFun x := - φ x
  left_invt δ g := by simp [left_invt]
  right_invt := by
    obtain ⟨U, hU⟩ := φ.right_invt
    simp_all only [neg_inj, right_invt]
  trivial_central_char g z := by simp [trivial_central_char]

instance : Neg (WeightTwoAutomorphicForm F D R) where
  neg := neg

@[simp, norm_cast]
theorem neg_apply (φ : WeightTwoAutomorphicForm F D R) (x : GL₂(𝔸ᶠ[F])) :
    (-φ : WeightTwoAutomorphicForm F D R) x = -(φ x) := rfl

/-- Addition on the space of automorphic forms over a totally definite quaternion algebra. -/
def add (φ ψ : WeightTwoAutomorphicForm F D R) : WeightTwoAutomorphicForm F D R where
  toFun x := φ x + ψ x
  left_invt := by simp [left_invt]
  right_invt := by
    obtain ⟨U, hU⟩ := φ.right_invt
    obtain ⟨V, hV⟩ := ψ.right_invt
    use U ⊓ V
    simp_all only [Subgroup.coe_inf, IsOpen.inter, Subgroup.mem_inf, implies_true, and_self]
  trivial_central_char := by simp [trivial_central_char]

instance : Add (WeightTwoAutomorphicForm F D R) where
  add := add

@[simp, norm_cast]
theorem add_apply (φ ψ : WeightTwoAutomorphicForm F D R) :
    ⇑(φ + ψ) = ⇑φ + ⇑ψ := rfl

instance addCommGroup : AddCommGroup (WeightTwoAutomorphicForm F D R) where
  add := (· + ·)
  add_assoc := by intros; ext; simp [add_assoc];
  zero := 0
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  nsmul := nsmulRec
  neg := (-·)
  zsmul := zsmulRec
  neg_add_cancel := by intros; ext; simp
  add_comm := by intros; ext; simp [add_comm]

@[simp, norm_cast]
theorem finsetSum_toFun {ι : Type*} (s : Finset ι)
    (f : ι → WeightTwoAutomorphicForm F D R) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) := by
  classical induction s using Finset.induction <;> simp_all; rfl

open scoped Pointwise

open ConjAct

open scoped TensorProduct.RightActions in
/-- The adelic group action on the space of automorphic forms over a totally definite
quaternion algebra. -/
def groupSMul (g : GL₂(𝔸ᶠ[F])) (φ : WeightTwoAutomorphicForm F D R) :
    WeightTwoAutomorphicForm F D R where
  toFun x := φ (x * g)
  left_invt δ x := by simp [left_invt, mul_assoc]
  right_invt := by
    obtain ⟨U, hU⟩ := φ.right_invt
    refine ⟨(toConjAct g) • U, ?_, ?_⟩
    · replace hU := hU.1
      exact isOpen_smul hU (toConjAct g)
    · rintro k x ⟨u, hu, rfl⟩
      simp only [MulDistribMulAction.toMonoidEnd_apply, MulDistribMulAction.toMonoidHom_apply,
        smul_def, ofConjAct_toConjAct, ← hU.2 (k * g) u hu]
      group
  trivial_central_char z x := by simp [smul_mul_assoc]

instance : SMul GL₂(𝔸ᶠ[F]) (WeightTwoAutomorphicForm F D R) where
  smul := groupSMul

@[simp]
lemma groupSMul_apply (g : GL₂(𝔸ᶠ[F]))
    (φ : WeightTwoAutomorphicForm F D R) (x : GL₂(𝔸ᶠ[F])) :
    (g • φ) x = φ (x * g) := rfl

@[simp]
lemma unitsMap_smul (φ : WeightTwoAutomorphicForm F D R) (x : 𝔸ᶠ[F]ˣ) :
    x.map (algebraMap _ M₂(𝔸ᶠ[F])).toMonoidHom • φ = φ := by ext; simp

attribute [instance low] Units.instMulAction

instance mulAction :
    MulAction GL₂(𝔸ᶠ[F]) (WeightTwoAutomorphicForm F D R) where
  smul := groupSMul
  one_smul φ := by ext; simp only [groupSMul_apply, mul_one]
  mul_smul g h φ := by ext; simp only [groupSMul_apply, mul_assoc]

instance distribMulAction : DistribMulAction GL₂(𝔸ᶠ[F])
    (WeightTwoAutomorphicForm F D R) where
  __ := mulAction
  smul_zero g := by ext; simp
  smul_add g φ ψ := by ext; simp

lemma isOpen_stabilizer (f : WeightTwoAutomorphicForm F D R) :
    IsOpen (X := GL₂(𝔸ᶠ[F])) (MulAction.stabilizer GL₂(𝔸ᶠ[F]) f) :=
  have ⟨_, hU, H⟩ := f.right_invt
  Subgroup.isOpen_mono (fun _ hx ↦ ext _ _ fun _ ↦ H _ _ hx) hU

open IsDedekindDomain.FiniteAdeleRing

noncomputable
instance (v : HeightOneSpectrum (𝓞 F)) :
    DistribMulAction GL₂(v.adicCompletion F) (WeightTwoAutomorphicForm F D R) :=
  .compHom _ (GL2.finiteAdeleIncl v)

lemma adicCompletion_smul_def (v : HeightOneSpectrum (𝓞 F)) (g : GL₂(v.adicCompletion F))
    (x : WeightTwoAutomorphicForm F D R) : g • x = GL2.finiteAdeleIncl v g • x := rfl

@[simp] lemma _root_.IsDedekindDomain.FiniteAdeleRing.toAdicCompletion_apply
    (v : HeightOneSpectrum (𝓞 F)) (x) :
    IsDedekindDomain.FiniteAdeleRing.toAdicCompletion v x = x v := rfl

@[simp] lemma FiniteAdeleRing.coe_zero : ⇑(0 : 𝔸ᶠ[𝓞 F, F]) = 0 := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma unitsMap_adicCompletion_smul (v : HeightOneSpectrum (𝓞 F))
    (φ : WeightTwoAutomorphicForm F D R) (x : (v.adicCompletion F)ˣ) :
    x.map (algebraMap _ M₂(v.adicCompletion F)).toMonoidHom • φ = φ := by
  classical
  convert unitsMap_smul φ (x.map (RestrictedProduct.mulSingleHom _ _)) using 1
  ext
  simp only [adicCompletion_smul_def, groupSMul_apply]
  congr 2
  refine GL2.ext _ _ fun w ↦ ?_
  obtain rfl | h := eq_or_ne w v
  · simp only [GL2.toAdicCompletion_finiteAdeleIncl_same]
    ext1
    simp [GL2.toAdicCompletion, Matrix.algebraMap_eq_diagonal, RestrictedProduct.mulSingleHom,
      RestrictedProduct.mulSingle]
  · simp only [ne_eq, h, not_false_eq_true, GL2.toAdicCompletion_finiteAdeleIncl_of_ne]
    ext1
    simp [GL2.toAdicCompletion, Matrix.algebraMap_eq_diagonal, RestrictedProduct.mulSingleHom,
      RestrictedProduct.mulSingle, h]

end add_comm_group

section comm_ring

variable {R S M : Type*} [CommRing R] [Semiring S] [AddCommGroup M] [Module R M] [Module S M]

/-- The scalar action on the space of weight 2 automorphic forms on a totally definite
quaternion algebra. -/
def ringSMul (r : S) (φ : WeightTwoAutomorphicForm F D M) :
    WeightTwoAutomorphicForm F D M where
      toFun g := r • φ g
      left_invt := by simp [left_invt]
      right_invt := by
        obtain ⟨U, hU⟩ := φ.right_invt
        use U
        simp_all only [implies_true, and_self]
      trivial_central_char g z := by simp only [trivial_central_char]

instance : SMul S (WeightTwoAutomorphicForm F D M) where
  smul := ringSMul

@[simp]
lemma smul_apply (r : S) (φ : WeightTwoAutomorphicForm F D M)
    (g : GL₂(𝔸ᶠ[F])) :
    (r • φ) g = r • (φ g) := rfl

instance module : Module S (WeightTwoAutomorphicForm F D M) where
  one_smul g := by ext; simp [smul_apply]
  mul_smul r s g := by ext; simp [smul_apply, mul_smul]
  smul_zero r := by ext; simp [smul_apply]
  smul_add r f g := by ext; simp [smul_apply, smul_add]
  add_smul r s g := by ext; simp [smul_apply, add_smul]
  zero_smul g := by ext; simp [smul_apply]

instance : SMulCommClass GL₂(𝔸ᶠ[F]) S (WeightTwoAutomorphicForm F D M) where
  smul_comm r g φ := by ext; simp [smul_apply]

instance : SMulCommClass S GL₂(𝔸ᶠ[F]) (WeightTwoAutomorphicForm F D M) := .symm _ _ _

instance (v : HeightOneSpectrum (𝓞 F)) :
    SMulCommClass GL₂(v.adicCompletion F) S (WeightTwoAutomorphicForm F D M) where
  smul_comm _ _ _ := by rw [adicCompletion_smul_def, adicCompletion_smul_def, smul_comm]

instance (v : HeightOneSpectrum (𝓞 F)) :
    SMulCommClass S GL₂(v.adicCompletion F) (WeightTwoAutomorphicForm F D M) := .symm _ _ _

/-- Mapping an automorphic form along a linear map. -/
@[simps]
def mapₗ {N : Type*} [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) :
    WeightTwoAutomorphicForm F D M →ₗ[R] WeightTwoAutomorphicForm F D N where
  toFun f :=
  { toFun := φ ∘ f
    left_invt := by simp
    right_invt := by
      obtain ⟨U, hU, H⟩ := f.right_invt
      exact ⟨U, hU, by simp +contextual [H]⟩
    trivial_central_char := by simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

end comm_ring

end WeightTwoAutomorphicForm

variable (R : Type*) [CommRing R]

local notation "ιD" => WithRigidification.unitsIncl F D
local notation "ι𝔸" => Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F])))
local notation "ℙ(" K ")" => HeightOneSpectrum (𝓞 K)
local notation "𝒪_[" K ", " v "]" => HeightOneSpectrum.adicCompletionIntegers K v

instance : (𝔸ˣ F).Normal := Subgroup.normal_of_le_center _ <| by
  rintro _ ⟨x, rfl⟩
  simp [Subgroup.mem_center_iff, Units.ext_iff, (Algebra.commute_algebraMap_left ..).eq]

open ConjAct Pointwise

variable {R} {M : Type*} [AddCommGroup M] [Module R M]

namespace WeightTwoAutomorphicForm

variable (F R) in
/-- The structure of an compact open `U`,
and a continuous character on `U` that is trivial on `𝔸ᶠˣ`. -/
structure LevelStruct where
  /-- The open compact subgroup. -/
  U : Subgroup GL₂(𝔸ᶠ[F])
  isCompact_U : IsCompact (X := GL₂(𝔸ᶠ[F])) U
  isOpen_U : IsOpen (X := GL₂(𝔸ᶠ[F])) U
  /-- The character on the open compact. -/
  χ : U →* R
  range_unitsMap_le_ker_χ : (𝔸ˣ F).subgroupOf U ≤ χ.ker
  isOpen_ker : IsOpen (X := U) χ.ker

namespace LevelStruct

variable (ℒ : LevelStruct F R)

/-- `U 𝔸ᶠˣ` of a `LevelStruct`. -/
abbrev UA : Subgroup GL₂(𝔸ᶠ[F]) := ℒ.U ⊔ 𝔸ˣ F

/-- The character extended onto `U 𝔸ᶠˣ` -/
def χA : ℒ.UA →* R :=
  MonoidHom.liftOfSurjective' (Subgroup.prodToSupOfRight _ _
    ((range_unitsMap_finiteAdeleRing_le_center ..).trans (Subgroup.center_le_centralizer _)))
    (Subgroup.prodToSupOfRight_surjective _ _ _)
    ⟨ℒ.χ.coprod 1, by
      rintro ⟨x, ⟨_, y, rfl⟩⟩ hx
      replace hx : x.1 * y.map (algebraMap _ _).toMonoidHom = 1 := by
        simpa [Subtype.ext_iff] using hx
      simp only [MonoidHom.mem_ker, MonoidHom.coprod_apply, MonoidHom.one_apply, mul_one]
      refine ℒ.range_unitsMap_le_ker_χ ⟨y⁻¹, ?_⟩
      simpa [← mul_eq_one_iff_inv_eq']⟩

@[simp]
lemma χA_inclusion_left (x) : ℒ.χA (Subgroup.inclusion le_sup_left x) = ℒ.χ x := by
  trans ℒ.χA ((Subgroup.prodToSupOfRight _ _ ((range_unitsMap_finiteAdeleRing_le_center ..).trans
    (Subgroup.center_le_centralizer _))) (x, 1))
  · congr 1; ext; simp
  · simp [χA]

@[simp]
lemma χA_inclusion_right (x) : ℒ.χA (Subgroup.inclusion le_sup_right x) = 1 := by
  trans ℒ.χA ((Subgroup.prodToSupOfRight _ _ ((range_unitsMap_finiteAdeleRing_le_center ..).trans
    (Subgroup.center_le_centralizer _))) (1, x))
  · congr 1; ext; simp
  · simp [χA]

lemma isOpen_UA : IsOpen (X := GL₂(𝔸ᶠ[F])) ℒ.UA := Subgroup.isOpen_mono le_sup_left ℒ.isOpen_U

lemma isOfFinOrder_χ : IsOfFinOrder ℒ.χ := by
  have : CompactSpace ℒ.U := isCompact_iff_compactSpace.mp ℒ.isCompact_U
  have : ℒ.χ.ker.FiniteIndex := .of_compactSpace _ ℒ.isOpen_ker
  refine isOfFinOrder_iff_pow_eq_one.mpr
    ⟨ℒ.χ.ker.index, (Subgroup.index_ne_zero_iff_finite.mpr inferInstance).bot_lt, ?_⟩
  ext x
  trans QuotientGroup.kerLift' ℒ.χ (QuotientGroup.mk x) ^ ℒ.χ.ker.index
  · simp
  rw [← map_pow, Subgroup.index]
  simp only [pow_card_eq_one', map_one, MonoidHom.one_apply]

lemma isOfFinOrder_χA :
    IsOfFinOrder ℒ.χA := by
  obtain ⟨n, hn, H⟩ := isOfFinOrder_iff_pow_eq_one.mp ℒ.isOfFinOrder_χ
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  ext u
  obtain ⟨⟨u, _, ⟨z, rfl⟩⟩, rfl⟩ := Subgroup.prodToSupOfRight_surjective _ _
    ((range_unitsMap_finiteAdeleRing_le_center ..).trans (Subgroup.center_le_centralizer _)) u
  simpa [χA] using congr($H u)

lemma isOfFinOrder_χ_apply (x : ℒ.U) :
    IsOfFinOrder (ℒ.χ x) := by
  obtain ⟨n, hn, H⟩ := isOfFinOrder_iff_pow_eq_one.mp ℒ.isOfFinOrder_χ
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congr($H x)⟩

lemma isOfFinOrder_χA_apply (x : ℒ.UA) :
    IsOfFinOrder (ℒ.χA x) := by
  obtain ⟨n, hn, H⟩ := isOfFinOrder_iff_pow_eq_one.mp ℒ.isOfFinOrder_χA
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congr($H x)⟩

variable (D) in
/-- `Δ_g := U 𝔸ˣ ∩ g⁻¹ Dˣ g` -/
def Δ (g : GL₂(𝔸ᶠ[F])) : Subgroup GL₂(𝔸ᶠ[F]) :=
  ℒ.UA ⊓ toConjAct g⁻¹ • 𝓓ˣ

/-- `Fˣ ≤ Δ_g` -/
lemma range_units_le_range (g : GL₂(𝔸ᶠ[F])) : 𝓕ˣ ≤ ℒ.Δ D g := by
  rintro _ ⟨x, rfl⟩
  refine ⟨Subgroup.mem_sup_right ⟨x.map (algebraMap _ _).toMonoidHom, ?_⟩, _,
    ⟨x.map (algebraMap _ _).toMonoidHom, rfl⟩, ?_⟩
  · simp [Units.ext_iff, ← IsScalarTower.algebraMap_apply, RingHom.toMonoidHom_eq_coe]
  · ext1
    simp [toConjAct_inv_smul', ← Algebra.commutes, RingHom.toMonoidHom_eq_coe]

/--
Second isomorphism theorem, index form: if `Z` is central and `M ⊓ Z` has finite
index in `Z`, then `M` has finite index in `M ⊔ Z`.

Proof: `M ⊔ Z = M · Z` because `Z` is normal, so the composite
`Z ↪ M ⊔ Z ↠ (M ⊔ Z)/M` is surjective (`m z` and `z` differ by the central `m`),
and it kills `M ⊓ Z`; hence `(M ⊔ Z)/M` is a quotient of the finite `Z/(M ⊓ Z)`. -/
theorem relIndex_sup_ne_zero_of_le_center {G : Type*} [Group G] {M Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) (h : (M ⊓ Z).relIndex Z ≠ 0) :
    M.relIndex (M ⊔ Z) ≠ 0 := by
  haveI : Z.Normal := Subgroup.normal_of_le_center _ hZ
  rw [Subgroup.relIndex, Subgroup.index_ne_zero_iff_finite] at h ⊢
  have key : ∀ a b : ↥Z, a⁻¹ * b ∈ (M ⊓ Z).subgroupOf Z →
      (⟨(a : G), Subgroup.mem_sup_right a.2⟩ : ↥(M ⊔ Z))⁻¹ *
        ⟨(b : G), Subgroup.mem_sup_right b.2⟩ ∈ M.subgroupOf (M ⊔ Z) := by
    intro a b hab
    rw [Subgroup.mem_subgroupOf] at hab ⊢
    exact hab.1
  refine Finite.of_surjective
    (f := (Quotient.map' (fun z : ↥Z => (⟨(z : G), Subgroup.mem_sup_right z.2⟩ : ↥(M ⊔ Z)))
      (fun a b hab => QuotientGroup.leftRel_apply.mpr
        (key a b (QuotientGroup.leftRel_apply.mp hab))) :
      ↥Z ⧸ ((M ⊓ Z).subgroupOf Z) → ↥(M ⊔ Z) ⧸ (M.subgroupOf (M ⊔ Z)))) ?_
  refine fun q => Quotient.inductionOn' q fun x => ?_
  have hxmem : (x : G) ∈ (M : Set G) * (Z : Set G) := by
    rw [← Subgroup.mul_normal]; exact x.2
  obtain ⟨m, hm, z, hz, hmz⟩ := hxmem
  rw [SetLike.mem_coe] at hm hz
  refine ⟨Quotient.mk'' ⟨z, hz⟩, ?_⟩
  rw [Quotient.map'_mk'']
  refine Quotient.sound' ?_
  rw [QuotientGroup.leftRel_apply]
  show (z : G)⁻¹ * (x : G) ∈ M
  have hc : (z : G)⁻¹ * (x : G) = m := by
    rw [← hmz]
    show (z : G)⁻¹ * (m * z) = m
    rw [Subgroup.mem_center_iff.mp (hZ hz) m, inv_mul_cancel_left]
  rw [hc]
  exact hm

/--
Companion to `relIndex_sup_ne_zero_of_le_center`, for a FINITE normal subgroup instead of
a central one: if `N` is normal and finite then `H` has finite index in `H ⊔ N`.

Proof: `N` normal gives `H ⊔ N = N · H` as sets, so every `x ∈ H ⊔ N` is `n h`, and then
`n⁻¹ x = h ∈ H`; hence `n ↦ [n]` is a surjection from the finite `N` onto `(H ⊔ N)/H`. -/
theorem relIndex_sup_ne_zero_of_normal {G : Type*} [Group G] {H N : Subgroup G} [N.Normal]
    (hN : Finite N) : H.relIndex (H ⊔ N) ≠ 0 := by
  rw [Subgroup.relIndex, Subgroup.index_ne_zero_iff_finite]
  refine Finite.of_surjective
    (f := fun n : ↥N ↦ (QuotientGroup.mk (s := H.subgroupOf (H ⊔ N))
      (⟨(n : G), Subgroup.mem_sup_right n.2⟩ : ↥(H ⊔ N)))) ?_
  refine fun q ↦ Quotient.inductionOn' q fun x ↦ ?_
  have hx : (x : G) ∈ (N : Set G) * (H : Set G) := by
    rw [← Subgroup.normal_mul, sup_comm]; exact x.2
  obtain ⟨n, hn, h, hh, hnh⟩ := hx
  rw [SetLike.mem_coe] at hn hh
  refine ⟨⟨n, hn⟩, Quotient.sound' ?_⟩
  rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
  show (n : G)⁻¹ * (x : G) ∈ H
  rw [← hnh, inv_mul_cancel_left]
  exact hh

/--
The purely group-theoretic half of `isFiniteRelIndex_Δ`.

Let `Z` be central, `P ≤ Z ⊓ Γ`, and `W` any subgroup. Writing
`Δ := (W ⊔ Z) ⊓ Γ`, the "central-part" map `Δ → Z/(Z ⊓ W)`, `w z ↦ z`, has kernel
`W ⊓ Γ` and carries `P` onto the image of `P`; so `Δ` is covered by finitely many
cosets of `P ⊔ (W ⊓ Γ)` as soon as `P ⊔ (Z ⊓ W)` has finite index in `Z`.

Formally the proof avoids constructing that map: since `P` is normal (being
central) the modular law gives `(P ⊔ W) ⊓ Δ = P ⊔ (W ⊓ Γ)`, so it suffices to
bound `[W ⊔ Z : P ⊔ W]`, which is `relIndex_sup_ne_zero_of_le_center`.

Applied with `Z = 𝔸ᶠˣ`, `W = U`, `Γ = g⁻¹ Dˣ g` and `P = Fˣ`, this reduces
finiteness of `Δ_g/Fˣ` to the two arithmetic inputs
`relIndex_ray_ne_zero` and `relIndex_unitsOrder_ne_zero`. -/
theorem relIndex_sup_inf_ne_zero_of_le_center {G : Type*} [Group G]
    {Z W Γ P : Subgroup G} (hZ : Z ≤ Subgroup.center G) (hPZ : P ≤ Z) (hPΓ : P ≤ Γ)
    (h : (P ⊔ (Z ⊓ W)).relIndex Z ≠ 0) :
    (P ⊔ (W ⊓ Γ)).relIndex ((W ⊔ Z) ⊓ Γ) ≠ 0 := by
  haveI : P.Normal := Subgroup.normal_of_le_center _ (hPZ.trans hZ)
  have hPΔ : P ≤ (W ⊔ Z) ⊓ Γ := le_inf (hPZ.trans le_sup_right) hPΓ
  have hKΔ : P ⊔ (W ⊓ Γ) ≤ (W ⊔ Z) ⊓ Γ :=
    sup_le hPΔ (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
  have hKM : P ⊔ (W ⊓ Γ) ≤ P ⊔ W := sup_le le_sup_left (inf_le_left.trans le_sup_right)
  have hmod : (P ⊔ W) ⊓ ((W ⊔ Z) ⊓ Γ) = P ⊔ (W ⊓ Γ) := by
    refine le_antisymm ?_ (le_inf hKM hKΔ)
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Subgroup.mem_inf] at hx2
    have hx1' : x ∈ (P : Set G) * (W : Set G) := by
      rw [← Subgroup.normal_mul]; exact hx1
    obtain ⟨p, hp, w, hw, rfl⟩ := hx1'
    rw [SetLike.mem_coe] at hp hw
    refine Subgroup.mul_mem_sup hp ⟨hw, ?_⟩
    have hrw : w = p⁻¹ * (p * w) := by group
    rw [hrw]
    exact Γ.mul_mem (Γ.inv_mem (hPΓ hp)) hx2.2
  rw [← hmod, Subgroup.inf_relIndex_right]
  refine mt (Subgroup.relIndex_eq_zero_of_le_right
    (show (W ⊔ Z) ⊓ Γ ≤ W ⊔ Z from inf_le_left)) ?_
  have hWZ : W ⊔ Z = (P ⊔ W) ⊔ Z := by
    rw [sup_assoc]
    exact (sup_eq_right.mpr (hPZ.trans le_sup_right)).symm
  rw [hWZ]
  refine relIndex_sup_ne_zero_of_le_center hZ ?_
  refine mt (Subgroup.relIndex_eq_zero_of_le_left
    (show P ⊔ (Z ⊓ W) ≤ (P ⊔ W) ⊓ Z from
      sup_le (le_inf le_sup_left hPZ)
        (le_inf (inf_le_right.trans le_sup_right) inf_le_left))) h

/--
In a COMMUTATIVE group, finiteness of the double-coset space `H ＼ G ／ K` implies
that `H ⊔ K` has finite index.

The map is `H a K ↦ a (H ⊔ K)`; it is well defined because `a⁻¹ (h a k) = h k`
by commutativity, and it is visibly surjective, so `G ⧸ (H ⊔ K)` is a quotient of
the finite double-coset space. (Commutativity — or normality of `H` — is genuinely
needed: `a⁻¹ h a` need not lie in `H` otherwise.) -/
theorem index_sup_ne_zero_of_finite_doubleCoset {G : Type*} [CommGroup G] (H K : Subgroup G)
    (hfin : Finite (DoubleCoset.Quotient (H : Set G) (K : Set G))) :
    (H ⊔ K).index ≠ 0 := by
  haveI := hfin
  refine Subgroup.index_ne_zero_iff_finite.mpr (Finite.of_surjective
    (α := DoubleCoset.Quotient (H : Set G) (K : Set G))
    (Quotient.lift (fun a : G => (QuotientGroup.mk a : G ⧸ (H ⊔ K))) ?_) ?_)
  · intro a b hab
    obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.rel_iff.mp hab
    refine QuotientGroup.eq.mpr ?_
    have h : a⁻¹ * (x * a * y) = x * y := by
      rw [mul_comm x a, mul_assoc, inv_mul_cancel_left]
    rw [h]
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)
  · intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨DoubleCoset.mk H K a, rfl⟩

variable (F) in
open scoped TensorProduct.RightActions in
/--
The `𝔸ᶠ`-algebra isomorphism `F ⊗[F] 𝔸ᶠ ≃ 𝔸ᶠ`, where the source carries the
RIGHT-action `𝔸ᶠ`-algebra structure. This is the `D = F` case of
`WithRigidification.algEquiv`, and it is built the same way: commute the factors
(an `𝔸ᶠ`-algebra map by `rfl`, since both algebra maps send `s` to the tensor with
`s` in the `𝔸ᶠ` slot), then apply `Algebra.TensorProduct.rid`.

`Algebra.TensorProduct.lid F 𝔸ᶠ` will not do here: it is only `F`-linear, whereas
the module topology on `F ⊗[F] 𝔸ᶠ` is the `𝔸ᶠ`-module topology, so continuity is
obtained from `IsModuleTopology.continuous_of_linearMap` only for an `𝔸ᶠ`-linear
map. -/
noncomputable def tensorLid : F ⊗[F] 𝔸ᶠ[F] ≃ₐ[𝔸ᶠ[F]] 𝔸ᶠ[F] :=
  AlgEquiv.trans
    { __ := Algebra.TensorProduct.comm F F 𝔸ᶠ[F], commutes' := fun _ => rfl }
    (Algebra.TensorProduct.rid F 𝔸ᶠ[F] 𝔸ᶠ[F])

open scoped TensorProduct.RightActions in
/--
**(PROVEN 2026-07-27 — finiteness of a ray class group.)**

For every OPEN subgroup `W ≤ 𝔸ᶠ[F]ˣ`, the subgroup `Fˣ · W` has finite index in
`𝔸ᶠ[F]ˣ`. Equivalently `Finite (Fˣ ＼ 𝔸ᶠ[F]ˣ ／ W)`: the ray class group of `F`
of the conductor cut out by `W` is finite.

**The openness hypothesis is load-bearing**: for `W = ⊥` the statement is false,
since `Fˣ` has infinite index in `𝔸ᶠ[F]ˣ`. Why it suffices: `W ⊓ 𝒪̂ˣ` is open in
the COMPACT group `𝒪̂ˣ`, hence of finite index there, and
`𝔸ᶠ[F]ˣ / (Fˣ · 𝒪̂ˣ) ≅ Cl(F)` is finite; so
`[𝔸ᶠ[F]ˣ : Fˣ · W] ≤ |Cl(F)| · [𝒪̂ˣ : W ⊓ 𝒪̂ˣ] < ∞`.

**Proof.** This is Fujisaki's lemma for the (one-dimensional, commutative)
division algebra `D = F` over itself:
`NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset F F`, proven in
`Fermat/FLT/DivisionAlgebra/Finiteness.lean`. Two transports are used:
(i) `tensorLid F : F ⊗[F] 𝔸ᶠ ≃ₐ[𝔸ᶠ] 𝔸ᶠ` above, continuous for the module
topology, carrying `incl₁ F F` to `Units.map (algebraMap F 𝔸ᶠ)`; and (ii)
`index_sup_ne_zero_of_finite_doubleCoset` above, the abelian double-coset-to-quotient
surjection. Compare `TotallyDefiniteQuaternionAlgebra.finite_doubleCoset` in
`Fermat/FLT/AutomorphicForm/QuaternionAlgebra/FiniteDimensional.lean`, which
performs exactly transport (i) for the quaternionic `D`.

The openness of `W` is consumed exactly once, as the hypothesis of
`finiteDoubleCoset` applied to the pullback of `W` along `Units.map (tensorLid F)`.

Note this statement does NOT mention `D` at all, nor total definiteness: it is a
statement about `F` alone. -/
theorem index_ray_ne_zero (W : Subgroup 𝔸ᶠ[F]ˣ) (hW : IsOpen (W : Set 𝔸ᶠ[F]ˣ)) :
    (MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap F 𝔸ᶠ[F]))) ⊔ W).index ≠ 0 := by
  refine index_sup_ne_zero_of_finite_doubleCoset _ _ ?_
  refine (NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset F F
    (U := W.comap (Units.map (tensorLid F).toMonoidHom))
    (hW.preimage (Units.continuous_map (by
      exact IsModuleTopology.continuous_of_linearMap (tensorLid F).toLinearMap)))).of_equiv _
    (DoubleCoset.quotientEquiv _ _ _ _ (Units.mapEquiv (tensorLid F).toMulEquiv) ?_ rfl)
  rw [← MulEquiv.coe_toEquiv, Equiv.preimage_eq_iff_eq_image, ← Set.range_comp]
  dsimp
  congr 1
  ext x : 2
  simp [tensorLid]
  exact Algebra.algebraMap_eq_smul_one _

/-- The form of `index_ray_ne_zero` consumed by `isFiniteRelIndex_Δ`: `Fˣ · (𝔸ᶠˣ ∩ U)`
has finite index in `𝔸ᶠˣ`, both viewed inside `GL₂(𝔸ᶠ)` as scalar matrices.
Transported along `Units.map (algebraMap 𝔸ᶠ M₂(𝔸ᶠ))`, whose range is `𝔸ᶠˣ` and
which is continuous for the module topology. -/
theorem relIndex_ray_ne_zero (ℒ : LevelStruct F R) :
    Subgroup.relIndex (𝓕ˣ ⊔ ((𝔸ˣ F) ⊓ ℒ.U)) (𝔸ˣ F) ≠ 0 := by
  have hrange : (⊤ : Subgroup 𝔸ᶠ[F]ˣ).map
      (Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F])))) = 𝔸ˣ F :=
    (MonoidHom.range_eq_map _).symm
  have hle : (MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap F 𝔸ᶠ[F]))) ⊔
      ℒ.U.comap (Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F]))))) ≤
      (𝓕ˣ ⊔ ((𝔸ˣ F) ⊓ ℒ.U)).comap
        (Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F])))) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      refine Subgroup.mem_comap.mpr (Subgroup.mem_sup_left ⟨x, ?_⟩)
      simp [Units.ext_iff, ← IsScalarTower.algebraMap_apply, RingHom.toMonoidHom_eq_coe]
    · intro x hx
      exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_right ⟨⟨x, rfl⟩, hx⟩)
  rw [← hrange, ← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
  rw [← hrange] at hle
  intro h0
  have hcont : Continuous (Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F])))) :=
    Units.continuous_map (by
      exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F])))
  exact index_ray_ne_zero (F := F)
    (ℒ.U.comap (Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F])))))
    (ℒ.isOpen_U.preimage hcont)
    (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le hle))

/-! ### General group theory and topology used by Voight 17.7.13

Two lemmas with no arithmetic content, kept dot-free so that they do not create
nested `Subgroup`/`Group` namespaces inside `TotallyDefiniteQuaternionAlgebra`. -/

/-- A subgroup of a finitely generated subgroup of a COMMUTATIVE group is finitely
generated. (`ℤ` is Noetherian, so a f.g. `ℤ`-module has f.g. submodules.) -/
theorem subgroup_fg_of_le_fg {A : Type*} [CommGroup A] {H K : Subgroup A}
    (hK : K.FG) (hHK : H ≤ K) : H.FG := by
  haveI hKfg : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hK
  haveI hfin : Module.Finite ℤ (Additive K) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have h1 : (AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup (H.subgroupOf K))).FG :=
    IsNoetherian.noetherian _
  rw [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup,
    ← Subgroup.fg_iff_add_fg] at h1
  haveI : Group.FG (H.subgroupOf K) := (Group.fg_iff_subgroup_fg _).mpr h1
  haveI : Group.FG H := Group.fg_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hHK).surjective
  exact (Group.fg_iff_subgroup_fg H).mp inferInstance

/-- An OPEN subgroup meets a COMPACT subgroup in finite relative index: `U ⊓ C` is open
in the compact group `C`, so `C/(U ⊓ C)` is discrete and compact, hence finite. -/
theorem relIndex_ne_zero_of_isCompact_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (C U : Subgroup G) (hC : IsCompact (C : Set G))
    (hU : IsOpen (U : Set G)) : (C ⊓ U).relIndex C ≠ 0 := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hopen : IsOpen ((U.subgroupOf C : Subgroup C) : Set C) :=
    hU.preimage continuous_subtype_val
  haveI : Finite (C ⧸ U.subgroupOf C) := Subgroup.quotient_finite_of_isOpen _ hopen
  rw [Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
  exact Subgroup.index_ne_zero_of_finite

/-! ### The three homomorphisms out of `Fˣ` and `GL₂(𝔸ᶠ)` used below -/

variable (F) in
/-- `Fˣ →* 𝔸ᶠˣ`. -/
abbrev unitsAlgebraMapAdele : Fˣ →* 𝔸ᶠ[F]ˣ :=
  Units.map (RingHom.toMonoidHom (algebraMap F 𝔸ᶠ[F]))

variable (F) in
/-- `Fˣ →* GL₂(𝔸ᶠ)`, the scalar matrices. -/
abbrev unitsAlgebraMapMatrix : Fˣ →* GL₂(𝔸ᶠ[F]) :=
  Units.map (RingHom.toMonoidHom (algebraMap F M₂(𝔸ᶠ[F])))

variable (F) in
/-- `GL₂(𝔸ᶠ) →* 𝔸ᶠˣ`, the `𝔸ᶠ`-algebra norm of `M₂(𝔸ᶠ)` restricted to units.
On `M₂` it is `m ↦ det(m)²`, so on the image of `Dˣ` it computes `Nm_{D/F}` — see
`unitsNormMatrix_unitsIncl`. -/
abbrev unitsNormMatrix : GL₂(𝔸ᶠ[F]) →* 𝔸ᶠ[F]ˣ :=
  Units.map (Algebra.norm 𝔸ᶠ[F] (S := M₂(𝔸ᶠ[F])))

omit [WithRigidification F D] in
lemma continuous_unitsNormMatrix : Continuous (unitsNormMatrix F) := by
  refine Units.continuous_map ?_
  have h : ⇑(Algebra.norm 𝔸ᶠ[F] (S := M₂(𝔸ᶠ[F]))) = fun m : M₂(𝔸ᶠ[F]) => m.det ^ 2 := by
    ext m; simp
  rw [h]
  fun_prop

omit [WithRigidification F D] in
lemma unitsAlgebraMapMatrix_eq : unitsAlgebraMapMatrix F =
    (Units.map (RingHom.toMonoidHom (algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F])))).comp
      (unitsAlgebraMapAdele F) := by
  ext x
  simp [← IsScalarTower.algebraMap_apply, RingHom.toMonoidHom_eq_coe]

/-- `Nm_{M₂(𝔸ᶠ)/𝔸ᶠ} ∘ ι = Nm_{D/F}` on `Dˣ`. This is `WithRigidification.det_incl_sq`
packaged as an identity of maps into `𝔸ᶠˣ`. -/
lemma unitsNormMatrix_unitsIncl [IsQuaternionAlgebra F D] (d : Dˣ) :
    unitsNormMatrix F (WithRigidification.unitsIncl F D d) =
      unitsAlgebraMapAdele F (Units.map (Algebra.norm F (S := D)) d) := by
  ext1
  simpa using WithRigidification.det_incl_sq F (d : D)

omit [WithRigidification F D] in
/-- `Nm(λ · 1) = λ⁴` for a scalar matrix, since `finrank 𝔸ᶠ M₂(𝔸ᶠ) = 4`. -/
lemma unitsNormMatrix_unitsAlgebraMapMatrix (x : Fˣ) :
    unitsNormMatrix F (unitsAlgebraMapMatrix F x) = (unitsAlgebraMapAdele F x) ^ 4 := by
  ext1
  have h4 : Module.finrank 𝔸ᶠ[F] M₂(𝔸ᶠ[F]) = 4 := by
    simp [Module.finrank_matrix]
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.val_pow_eq_pow_val]
  rw [show ((algebraMap F M₂(𝔸ᶠ[F])) (x : F)) = algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F])
      (algebraMap F 𝔸ᶠ[F] (x : F)) from (IsScalarTower.algebraMap_apply _ _ _ _)]
  rw [Algebra.norm_algebraMap, h4]

omit [NumberField F] [WithRigidification F D] in
/-- `Nm_{D/F}(λ · 1) = λ⁴`, since `finrank F D = 4`. -/
lemma norm_units_algebraMap_eq_pow [IsQuaternionAlgebra F D] (x : Fˣ) :
    Units.map (Algebra.norm F (S := D)) (x.map (algebraMap F D).toMonoidHom) = x ^ 4 := by
  ext1
  simp [IsQuaternionAlgebra.finrank_eq_four F D]

omit [WithRigidification F D] in
/--
**(sorry leaf — "a compact subgroup of `𝔸ᶠˣ` is integral".)**

If `C ≤ 𝔸ᶠ[F]ˣ` is COMPACT then `Fˣ ∩ C` consists of units of `𝓞 F`.

**Why it is true.** Let `x ∈ Fˣ` with `j(x) ∈ C`. Since `C` is a subgroup, every power
`j(x)^n = j(xⁿ)` lies in `C`. Compactness of `C` makes `Units.val '' C` compact in `𝔸ᶠ`,
hence its image under the (continuous) evaluation `𝔸ᶠ → Fᵥ` is compact, hence bounded:
`|xⁿ|ᵥ ≤ c` for all `n`, which forces `|x|ᵥ ≤ 1`. The same applied to `x⁻¹` gives
`|x|ᵥ = 1` at every finite place `v`, and then
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one` puts both `x` and
`x⁻¹` in `𝓞 F`.

**COMPACTNESS is load-bearing**: for `C = 𝔸ᶠˣ` the conclusion is false, since
`Fˣ ⊄ (𝓞 F)ˣ`.

Note this statement mentions neither `D` nor definiteness: it is about `F` alone. -/
theorem comap_le_range_units_integers_of_isCompact (C : Subgroup 𝔸ᶠ[F]ˣ)
    (hC : IsCompact (C : Set 𝔸ᶠ[F]ˣ)) :
    C.comap (unitsAlgebraMapAdele F) ≤
      MonoidHom.range (Units.map (algebraMap (𝓞 F) F).toMonoidHom) :=
  sorry

omit [WithRigidification F D] in
/-- If `C ≤ 𝔸ᶠ[F]ˣ` is COMPACT then `Fˣ ∩ C` is finitely generated: by
`comap_le_range_units_integers_of_isCompact` it is a subgroup of the image of `(𝓞 F)ˣ`,
which is finitely generated by Dirichlet's unit theorem (`Monoid.FG (𝓞 K)ˣ`). -/
theorem fg_comap_unitsAlgebraMapAdele_of_isCompact (C : Subgroup 𝔸ᶠ[F]ˣ)
    (hC : IsCompact (C : Set 𝔸ᶠ[F]ˣ)) : (C.comap (unitsAlgebraMapAdele F)).FG := by
  haveI : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  refine subgroup_fg_of_le_fg ?_ (comap_le_range_units_integers_of_isCompact C hC)
  exact (Group.fg_iff_subgroup_fg _).mp
    (Group.fg_range (Units.map (algebraMap (𝓞 F) F).toMonoidHom))

/-! ### The two halves of Voight 17.7.13 -/

section Archimedean

open scoped TensorProduct.RightActions

/-! #### Decomposition of `isCompact_normOne_infiniteAdele` over the infinite places

`isCompact_normOne_infiniteAdele` is PROVEN below from the three leaves in this
subsection. The three are mutually independent and can be owned separately; only
the FIRST carries any definiteness (see the audit on it).

The route is the obvious one: `𝔸_F^∞ = ∏_v F_v` *definitionally* (mathlib's
`NumberField.InfiniteAdeleRing K` is the `def` `(v : InfinitePlace K) → v.Completion`),
so `D ⊗_F 𝔸_F^∞ ≃ ∏_v (D ⊗_F F_v)` by `tensorPiEquivPiTensor`, the algebra norm is
computed componentwise along that decomposition, and a product of compacts is compact
(`isCompact_univ_pi`, Tychonoff — no finiteness of the place set is needed).

**Why not `DinfTensorPiEquivPiTensor`.** The docstring this replaced pointed at
`NumberField.AdeleRing.DivisionAlgebra.Aux.InfiniteAdeleRing.DinfTensorPiEquivPiTensor`
in `Fermat/FLT/DivisionAlgebra/Finiteness.lean`, which is exactly this decomposition
and is even already a `≃L[ℝ]`. It is NOT usable here as it stands: the whole of
`Finiteness.lean` sits under `variable (D) [DivisionRing D]`, and so do the `Algebra ℝ`,
`Module.Finite ℝ` and `IsModuleTopology ℝ` instances on `D ⊗[K] v.Completion` that its
continuity proof runs on — while here `D` is only a `[Ring D]`. (Verified by probe: with
`[Ring D] [IsQuaternionAlgebra F D]` the `v.Completion`- and `𝔸^∞`-module topologies on
`D ⊗[F] v.Completion` and `D ⊗[F] 𝔸^∞` DO resolve, but every `ℝ`-structure on them fails
to synthesize.) This is the same `[DivisionRing D]`-vs-`[Ring D]` obstruction that
`finite_setOf_tmul_mem_of_isCompact` records below. Two ways out, both open:
relax `Finiteness.lean` to `[Ring D]` (it only ever uses `Module.Finite F D`), or derive
`DivisionRing D` here from total definiteness via
`IsQuaternionAlgebra.nomepty_algEquiv_matrix_or_forall_isUnit` — the second is available
to `continuous_infiniteAdeleTensorPiEquiv_symm` (which is stated with definiteness in
scope) but costs a `Ring D` instance-diamond check. -/

variable (F D) in
/-- The decomposition `D ⊗_F 𝔸_F^∞ ≃ ∏_v (D ⊗_F F_v)` over the infinite places, as an
`F`-linear equivalence. This is just `tensorPiEquivPiTensor` (`D` is finite free over the
field `F`), ascribed at the source type `D ⊗[F] 𝔸_F^∞` rather than at the unfolded
`D ⊗[F] ((v : InfinitePlace F) → v.Completion)`: the two are definitionally equal, but
instance search is keyed on the head symbol, so `Algebra (𝔸_F^∞) (D ⊗[F] 𝔸_F^∞)` is not
found at the unfolded form and `Algebra.norm (𝔸_F^∞) (e.symm y)` fails to elaborate
without this ascription. -/
def infiniteAdeleTensorPiEquiv [IsQuaternionAlgebra F D] :
    (D ⊗[F] (NumberField.InfiniteAdeleRing F)) ≃ₗ[F]
      Π v : NumberField.InfinitePlace F, D ⊗[F] v.Completion :=
  tensorPiEquivPiTensor F D NumberField.InfinitePlace.Completion

variable (F D) in
/--
`Quaternion ℝ ≃ₗ[ℝ] (Fin 4 → ℝ)`, at the type `Quaternion ℝ` ITSELF.

`Quaternion R` is a `def` for `ℍ[R,-1,0,-1]`, and mathlib's `QuaternionAlgebra.basisOneIJK`
is stated at the latter. The two are definitionally equal but their `Algebra ℝ _` instance
terms are not syntactically equal, so `rw [Algebra.norm_eq_matrix_det basisOneIJK]` does NOT
fire against a goal stated at `Quaternion ℝ` (checked: "did not find an occurrence of the
pattern"). Hence this basis, rebuilt at `Quaternion ℝ`. -/
def linEquivTupleQuaternion : Quaternion ℝ ≃ₗ[ℝ] (Fin 4 → ℝ) where
  __ := Quaternion.equivTuple ℝ
  map_add' _ _ := by funext i; fin_cases i <;> rfl
  map_smul' _ _ := by funext i; fin_cases i <;> rfl

/-- The `1, i, j, k` basis of `Quaternion ℝ` over `ℝ`. -/
def basisQuaternion : Module.Basis (Fin 4) ℝ (Quaternion ℝ) := .ofEquivFun linEquivTupleQuaternion

lemma basisQuaternion_repr (z : Quaternion ℝ) (i : Fin 4) :
    basisQuaternion.repr z i = ![z.re, z.imI, z.imJ, z.imK] i := rfl

lemma basisQuaternion_apply (i : Fin 4) :
    basisQuaternion i = ![(1 : Quaternion ℝ), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩] i := by
  refine basisQuaternion.ext_elem fun j => ?_
  rw [Module.Basis.repr_self]
  -- NOTE the trailing `rfl`: in a bare scratch module `simp` closes every branch here, but
  -- inside this file's simp scope it leaves the four `(1 : Quaternion ℝ).re = 1`-shaped
  -- component goals of the `i = 0` case open. They are all `rfl`.
  fin_cases i <;> fin_cases j <;> simp [basisQuaternion_repr] <;> rfl

set_option maxHeartbeats 4000000 in
/--
**PROVEN.** The `ℝ`-algebra norm of the Hamilton quaternions is the SQUARE of the reduced
norm: `Nm_{ℍ/ℝ}(q) = normSq(q)² = ‖q‖⁴`.

Absent from the pin — `grep Algebra.norm` over `Mathlib/Algebra/Quaternion.lean` and
`Mathlib/Analysis/Quaternion.lean` finds nothing — and mathlib-shaped, so it should go
upstream eventually.

Proved by exhibiting the left-multiplication matrix in the `1, i, j, k` basis explicitly
and expanding its determinant. Two traps, both cost a cycle here: `Matrix.det_fin_four`
does NOT exist (only `det_fin_three`), so the expansion is by `Matrix.det_succ_row_zero`
plus `Fin.sum_univ_succ`; and that expansion leaves `Fin.succAbove` index terms which
`simp` cannot reduce unless `Fin.succAbove` is itself in the simp set — while adding
`Fin.lt_def` instead makes `simp` loop (via `Fin.val_fin_lt`) and blow the recursion
depth. Establishing the matrix as an explicit `!![…]` FIRST, so every index is a numeral,
is what makes the whole thing go. -/
theorem norm_quaternion_eq_normSq_sq (q : Quaternion ℝ) :
    Algebra.norm ℝ q = (Quaternion.normSq q) ^ 2 := by
  have hM : Algebra.leftMulMatrix basisQuaternion q =
      !![q.re, -q.imI, -q.imJ, -q.imK;
         q.imI, q.re, -q.imK, q.imJ;
         q.imJ, q.imK, q.re, -q.imI;
         q.imK, -q.imJ, q.imI, q.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply,
        basisQuaternion_repr, basisQuaternion_apply]
  rw [Algebra.norm_eq_matrix_det basisQuaternion, hM]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Quaternion.normSq_def']
  ring

/--
**PROVEN.** `{q ∈ ℍ : Nm_{ℍ/ℝ}(q) = 1}` is the UNIT SPHERE, hence compact.

`Nm(q) = normSq(q)² = (‖q‖‖q‖)²` by `norm_quaternion_eq_normSq_sq` and
`Quaternion.normSq_eq_norm_mul_self`, so `Nm(q) = 1 ↔ ‖q‖ = 1` (both directions by
`nlinarith` off `norm_nonneg`), and `ℍ` is a `ProperSpace`, so `isCompact_sphere` applies.

**This is where definiteness cashes out.** The corresponding set for the SPLIT algebra
`M₂(ℝ)` is `{det = ±1} = SL₂^±(ℝ)`, which is closed and UNBOUNDED — `diag(t, t⁻¹)` for
`t → ∞` — hence not compact. The whole content of `IsTotallyDefinite` in this file is
that the archimedean completions are `ℍ` and not `M₂(ℝ)`. -/
theorem isCompact_normOne_quaternion :
    IsCompact {q : Quaternion ℝ | Algebra.norm ℝ q = 1} := by
  have hs : {q : Quaternion ℝ | Algebra.norm ℝ q = 1} = Metric.sphere (0 : Quaternion ℝ) 1 := by
    ext q
    simp only [Set.mem_setOf_eq, norm_quaternion_eq_normSq_sq, Metric.mem_sphere, dist_zero_right,
      Quaternion.normSq_eq_norm_mul_self]
    constructor
    · intro h
      have h0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
      have h1 : ‖q‖ * ‖q‖ = 1 := by nlinarith [mul_nonneg h0 h0]
      nlinarith
    · intro h; rw [h]; norm_num
  rw [hs]
  exact isCompact_sphere _ _

variable (F D) in
omit [NumberField F] [WithRigidification F D] in
/--
**PROVEN.** (This is the ONLY carrier of `IsTotallyDefinite` left in this file.)

At an infinite place `v` of the totally real `F`, with `D` totally definite, the completion
`D ⊗_F F_v` is RING-ISOMORPHIC to `ℍ` by a HOMEOMORPHISM compatible with `F_v ≃+* ℝ`.

**Why it is true.** `F` totally real makes `v` real, so
`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal` gives `F_v ≃+* ℝ` and
`IsQuaternionAlgebra.IsTotallyDefinite.cond v hv` gives `ℝ ⊗[F,v] D ≃ₐ[ℝ] ℍ`, where the
`Algebra F ℝ` is the one induced by `embedding_of_isReal hv`. Composing
`D ⊗[F] F_v ≃ D ⊗[F] ℝ ≃ ℝ ⊗[F] D ≃ ℍ` gives the ring equivalence; the middle step is the
`Algebra.TensorProduct.comm` already packaged here as `tensorCommRight`. It is a
homeomorphism because it is `ℝ`-linear between two finite-dimensional spaces carrying
module topologies (`IsModuleTopology F_v (D ⊗[F] v.Completion)` DOES resolve at `[Ring D]`;
`ℍ` is a finite-dimensional normed space), so
`IsModuleTopology.continuous_of_linearMap` applies in both directions.

**The statement is PINNED, not merely existential.** The compatibility clause forces the
`ℝ`-algebra structure: any `e` satisfying it makes
`Algebra.norm_eq_of_equiv_equiv (ringEquivRealOfIsReal _) e` applicable, which is all the
consumer uses, so no adversarial witness (a post-composed automorphism of `ℍ`, say) can
satisfy the clauses while breaking `isCompact_normOne_completion` — every automorphism of
`ℍ` is norm-preserving precisely because the norm is defined from the algebra structure.

**CORRECTION (2026-07-28).** The previous docstring said the compatibility of
`ringEquivRealOfIsReal` with `algebraMap F v.Completion` and `embedding_of_isReal hv` was
"the one input that has not been located in the pin". That is FALSE: the pin has
`NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe`, and with it the
compatibility `hφ` below is a one-line `simp`. There was no missing input.

**The proof.** `φ := ringEquivRealOfIsReal hv : F_v ≃+* ℝ` is an `F`-algebra equivalence
for the `Algebra F ℝ` that `IsTotallyDefinite` uses (`AlgEquiv.ofRingEquiv hφ`), so
`Algebra.TensorProduct.congr .refl φₐ` gives `D ⊗[F] F_v ≃ₐ[F] D ⊗[F] ℝ`; then
`Algebra.TensorProduct.comm` and `IsTotallyDefinite.cond v hv` land in `ℍ`. Note this uses
`Algebra.TensorProduct.comm` DIRECTLY rather than the `tensorCommRight` wrapper the old
docstring pointed at: that wrapper is declared BELOW this leaf in the file, and only its
`F`-algebra (not `ℝ`-algebra) content is needed here, so inlining avoids a hoist.

**Continuity is `IsModuleTopology.continuous_of_linearMapₛₗ` in both directions**, which is
what makes the `[Ring D]`-vs-`[DivisionRing D]` obstruction recorded above irrelevant here:
no `ℝ`-structure on `D ⊗[F] F_v` is ever needed. Forwards, `e` is `φ`-SEMIlinear out of
`D ⊗[F] F_v`, which carries the `F_v`-module topology; backwards, `e.symm` is
`φ.symm`-semilinear out of `ℍ`, which carries the `ℝ`-module topology by
`isModuleTopologyOfFiniteDimensional`. Both `φ` and `φ.symm` are continuous because
`ringEquivRealOfIsReal` is an isometry (`isometry_extensionEmbeddingOfIsReal`,
`isometryEquivRealOfIsReal`). Semilinearity in each direction is exactly the pinning clause
`hcomp` plus `Algebra.smul_def`, so the clause is not decoration — the proof consumes it.

**Both hypotheses are load-bearing**, and this leaf is where they are consumed. Drop
definiteness and take `D = M₂(F)` split at `v`: `D ⊗ F_v ≃ M₂(ℝ)`, which is not isomorphic
to `ℍ` (it has zero divisors). Drop total reality and let `v` be complex: `D ⊗ ℂ ≃ M₂(ℂ)`
always — a quaternion algebra is split by `ℂ`, definite or not. So a proof of this leaf
that does not use `IsTotallyDefinite` is proving something else. -/
theorem exists_ringEquiv_quaternion_of_isTotallyDefinite [NumberField.IsTotallyReal F]
    [IsQuaternionAlgebra F D] [IsQuaternionAlgebra.IsTotallyDefinite F D]
    (v : NumberField.InfinitePlace F) :
    ∃ e : (D ⊗[F] v.Completion) ≃+* Quaternion ℝ, Continuous e ∧ Continuous e.symm ∧
      (algebraMap ℝ (Quaternion ℝ)).comp
          (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
            (NumberField.IsTotallyReal.isReal v) : v.Completion →+* ℝ)
        = (e : (D ⊗[F] v.Completion) →+* Quaternion ℝ).comp
            (algebraMap v.Completion (D ⊗[F] v.Completion)) := by
  have hv : v.IsReal := NumberField.IsTotallyReal.isReal v
  set φ : v.Completion ≃+* ℝ :=
    NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv with hφdef
  letI : Algebra F ℝ := (NumberField.InfinitePlace.embedding_of_isReal hv).toAlgebra
  -- the compatibility the old docstring called a missing input: it is `simp` from
  -- `extensionEmbeddingOfIsReal_coe`, which the pin has.
  have hφ : ∀ x : F, φ (algebraMap F v.Completion x) = algebraMap F ℝ x := by
    intro x
    simp [hφdef, NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal]
    rfl
  let φₐ : v.Completion ≃ₐ[F] ℝ := AlgEquiv.ofRingEquiv hφ
  let e₁ : D ⊗[F] v.Completion ≃ₐ[F] D ⊗[F] ℝ :=
    Algebra.TensorProduct.congr AlgEquiv.refl φₐ
  let e₂ : D ⊗[F] ℝ ≃ₐ[F] ℝ ⊗[F] D := Algebra.TensorProduct.comm F D ℝ
  let e₃ : ℝ ⊗[F] D ≃ₐ[ℝ] Quaternion ℝ := (IsQuaternionAlgebra.IsTotallyDefinite.cond v hv).some
  set e : (D ⊗[F] v.Completion) ≃+* Quaternion ℝ :=
    e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃.toRingEquiv) with hedef
  -- The pinning clause, proven FIRST because both continuity proofs consume it: it is
  -- exactly the semilinearity of `e` over `φ`.
  have hcomp : ∀ y : v.Completion,
      e (algebraMap v.Completion (D ⊗[F] v.Completion) y)
        = algebraMap ℝ (Quaternion ℝ) (φ y) := by
    intro y
    have h1 : algebraMap v.Completion (D ⊗[F] v.Completion) y = (1 : D) ⊗ₜ[F] y := rfl
    have h2 : e ((1 : D) ⊗ₜ[F] y) = e₃ (algebraMap ℝ (ℝ ⊗[F] D) (φ y)) := rfl
    rw [h1, h2, AlgEquiv.commutes]
  refine ⟨e, ?_, ?_, RingHom.ext fun y => (hcomp y).symm⟩
  · -- `e` is `φ`-semilinear out of `D ⊗[F] F_v`, which has the `F_v`-module topology.
    have hσ : Continuous (φ : v.Completion →+* ℝ) :=
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).continuous
    exact IsModuleTopology.continuous_of_linearMapₛₗ (B' := Quaternion ℝ) hσ
      { toFun := e
        map_add' := map_add e
        map_smul' := fun c x => by
          simp only [Algebra.smul_def, map_mul, hcomp, RingHom.coe_coe] }
  · -- `e.symm` is `φ.symm`-semilinear out of `ℍ`, which has the `ℝ`-module topology.
    haveI : IsModuleTopology ℝ (Quaternion ℝ) := isModuleTopologyOfFiniteDimensional
    have hσ : Continuous ((φ.symm : ℝ →+* v.Completion)) :=
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous
    have hsymm : ∀ r : ℝ, e.symm (algebraMap ℝ (Quaternion ℝ) r)
        = algebraMap v.Completion (D ⊗[F] v.Completion) (φ.symm r) := by
      intro r
      apply e.injective
      rw [RingEquiv.apply_symm_apply, hcomp, RingEquiv.apply_symm_apply]
    exact IsModuleTopology.continuous_of_linearMapₛₗ (B' := D ⊗[F] v.Completion) hσ
      { toFun := e.symm
        map_add' := map_add e.symm
        map_smul' := fun r q => by
          simp only [Algebra.smul_def, map_mul, hsymm, RingHom.coe_coe] }

variable (F D) in
omit [NumberField F] [WithRigidification F D] in
/--
**PROVEN** (assembly) from `exists_ringEquiv_quaternion_of_isTotallyDefinite` and
`isCompact_normOne_quaternion`.

At an infinite place `v`, `{z ∈ D ⊗_F F_v : Nm_{(D ⊗ F_v)/F_v}(z) = 1}` is COMPACT.

**BOTH hypotheses are load-bearing**, and they are consumed entirely inside
`exists_ringEquiv_quaternion_of_isTotallyDefinite`; see the counterexamples there
(`SL₂^±(ℝ)` at a split real place, `SL₂^±(ℂ)` at a complex one).

**The assembly proven here.** `Algebra.norm_eq_of_equiv_equiv` — exactly the lemma for a
simultaneous change of BASE RING and ALGEBRA — turns `Nm_{F_v}(z)` into
`e₁.symm (Nm_ℝ (e z))`, so the set is `e.symm '' {q : ℍ | Nm_ℝ q = 1}`; `e₁.symm` is a ring
equivalence, hence injective and unital, which is what converts `e₁.symm (·) = 1` into
`(·) = 1`. The image of the compact `{Nm_ℝ = 1}` under the continuous `e.symm` is
compact. -/
theorem isCompact_normOne_completion [NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D] (v : NumberField.InfinitePlace F) :
    IsCompact {z : D ⊗[F] v.Completion | Algebra.norm v.Completion z = 1} := by
  obtain ⟨e, _he, hes, hcomp⟩ := exists_ringEquiv_quaternion_of_isTotallyDefinite F D v
  have hs : {z : D ⊗[F] v.Completion | Algebra.norm v.Completion z = 1}
      = ⇑e.symm '' {q : Quaternion ℝ | Algebra.norm ℝ q = 1} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    rw [Algebra.norm_eq_of_equiv_equiv _ e hcomp z]
    constructor
    · intro hz
      exact ⟨e z, by
        have := (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
          (NumberField.IsTotallyReal.isReal v)).symm.injective
            (a₁ := Algebra.norm ℝ (e z)) (a₂ := 1) (by simpa using hz)
        simpa using this, by simp⟩
    · rintro ⟨q, hq, rfl⟩
      simp [hq]
  rw [hs]
  exact isCompact_normOne_quaternion.image hes

variable (F D) in
/--
**(sorry leaf — the algebra norm is computed componentwise along the decomposition.)**

**Why it is true.** Pick an `F`-basis `b` of `D`. Then `b ⊗ₜ 1` is an `𝔸^∞`-basis of
`D ⊗_F 𝔸^∞` and simultaneously a `F_v`-basis of `D ⊗_F F_v` for every `v`, and
`infiniteAdeleTensorPiEquiv` carries the one to the other (`tensorPi_equiv_piTensor_apply`
sends `d ⊗ₜ a` to `fun v ↦ d ⊗ₜ a v`, so it fixes `b i ⊗ₜ 1` placewise) and is a RING map.
Hence `Algebra.leftMulMatrix` of `x` in the first basis, evaluated at `v`, is
`Algebra.leftMulMatrix` of the `v`-component in the second. Now `Algebra.norm` is the
determinant of that matrix (`Algebra.norm_eq_matrix_det`) and evaluation at `v` is the
RING HOM `Pi.evalRingHom _ v : 𝔸^∞ →+* F_v`, so it commutes with `det` by
`RingHom.map_det`. No definiteness and no total reality: this is pure base-change
bookkeeping, true for any finite free `D`.

**One input has to be re-proven here.** `tensorPiEquivPiTensor` is multiplicative on
`Dinf` — that is `tensorPi_equiv_piTensor_map_mul` in `Fermat/FLT/DivisionAlgebra/Finiteness.lean`
— but that lemma is stated under `variable (D) [DivisionRing D]`, so it is not applicable
at `[Ring D]`. Its proof is four lines (`TensorProduct.induction_on` twice, then `funext`
and `simp [tensorPi_equiv_piTensor_apply]`) and uses nothing about `D` beyond its ring
structure, so restating it here (or relaxing it there) is the cheap fix. -/
theorem norm_infiniteAdele_apply [IsQuaternionAlgebra F D]
    (x : D ⊗[F] (NumberField.InfiniteAdeleRing F)) (v : NumberField.InfinitePlace F) :
    Algebra.norm (NumberField.InfiniteAdeleRing F) x v =
      Algebra.norm v.Completion (infiniteAdeleTensorPiEquiv F D x v) :=
  sorry

variable (F D) in
/--
**(sorry leaf — the decomposition is a homeomorphism.)**

`(infiniteAdeleTensorPiEquiv F D).symm` is CONTINUOUS. (Only this direction is used;
the forward direction is not needed, because the target set is exhibited as an IMAGE.)

**Why it is true.** Fix an `F`-basis `b = (b i)` of `D`, finite since `finrank F D = 4`.
For `y : ∏_v (D ⊗_F F_v)` one has
`(infiniteAdeleTensorPiEquiv F D).symm y = ∑ i, b i ⊗ₜ (fun v ↦ c_i (y v))`,
where `c_i : D ⊗_F F_v →ₗ[F_v] F_v` is the `i`-th coordinate against the `F_v`-basis
`b ⊗ₜ 1`. Each `c_i` is continuous because `D ⊗_F F_v` carries the `F_v`-MODULE topology
(`IsModuleTopology F_v (D ⊗[F] v.Completion)` — this instance DOES resolve at `[Ring D]`,
unlike its `ℝ` counterpart) and `IsModuleTopology.continuous_of_linearMap` makes every
linear map out of a module-topology module continuous. So `y ↦ (fun v ↦ c_i (y v))` is
continuous into `𝔸^∞` by `continuous_pi` composed with the projections, and
`a ↦ b i ⊗ₜ a : 𝔸^∞ → D ⊗_F 𝔸^∞` is continuous for the same reason applied to
`IsModuleTopology.self`. A finite sum of continuous maps is continuous.

**Alternative, cheaper if the diamond is benign:** this is literally
`DinfTensorPiEquivPiTensor`'s `continuous_invFun` field, already proven in
`Fermat/FLT/DivisionAlgebra/Finiteness.lean` — but only for `[DivisionRing D]`. Total
definiteness IS in scope on this declaration, and it does give `DivisionRing D` (via
`IsQuaternionAlgebra.nomepty_algEquiv_matrix_or_forall_isUnit`: the matrix alternative is
killed because `ℝ ⊗ M₂(F) ≃ M₂(ℝ)` has zero divisors and `ℍ` does not). The cost is that
`letI : DivisionRing D := .ofIsUnitOrEqZero …` must have its `toRing` field DEFEQ to the
ambient `Ring D`, or the `TopologicalSpace (D ⊗[F] v.Completion)` in the goal is a
different instance from the one that lemma is about. `DivisionRing.ofIsUnitOrEqZero`
elaborates fine here (verified by probe); the defeq of the derived topology is the part
that has not been checked. -/
theorem continuous_infiniteAdeleTensorPiEquiv_symm [NumberField.IsTotallyReal F]
    [IsQuaternionAlgebra F D] [IsQuaternionAlgebra.IsTotallyDefinite F D] :
    Continuous (infiniteAdeleTensorPiEquiv F D).symm :=
  sorry

/--
**PROVEN** (assembly) from `isCompact_normOne_completion`, `norm_infiniteAdele_apply` and
`continuous_infiniteAdeleTensorPiEquiv_symm`, the three leaves immediately above.

`{x ∈ D ⊗_F 𝔸_F^∞ : Nm_{(D ⊗ 𝔸^∞)/𝔸^∞}(x) = 1}` is COMPACT.

**Why it is true.** `F` is totally real, so every infinite place `v` is real and
`𝔸_F^∞ = ∏_v ℝ`; hence `D ⊗_F 𝔸_F^∞ = ∏_v (D ⊗_{F,v} ℝ)`. Total definiteness says
each factor is `ℍ`, where the algebra norm over `ℝ` is `Nm(x) = nrd(x)² = |x|⁴`.
So the set is the product over `v` of the unit spheres of `ℍ`, hence compact.

**BOTH hypotheses are load-bearing.** At a real place where `D` splits, or at a
complex place, `Nm = det²` and `{det = ±1}` is `SL₂^±(ℝ)`, which is not compact;
the statement then fails for `D = M₂(F)`. They are consumed entirely inside
`isCompact_normOne_completion`; the assembly here is formal.

**The assembly proven here.** The set is the image under
`(infiniteAdeleTensorPiEquiv F D).symm` of `Set.univ.pi (fun v ↦ {z | Nm_{F_v} z = 1})`:
membership transfers by `norm_infiniteAdele_apply` together with the fact that `1` and
equality in `𝔸^∞ = ∏_v F_v` are componentwise (both hold by `rfl`, `𝔸^∞` being a `def`
for the `Pi` type). That product is compact by `isCompact_univ_pi` — Tychonoff, so the
place set does not need to be finite — and the image of a compact under a continuous map
is compact. -/
theorem isCompact_normOne_infiniteAdele [NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D] :
    IsCompact {x : D ⊗[F] (NumberField.InfiniteAdeleRing F) |
      Algebra.norm (NumberField.InfiniteAdeleRing F) x = 1} := by
  classical
  have hTc : IsCompact (Set.univ.pi fun v : NumberField.InfinitePlace F =>
      {z : D ⊗[F] v.Completion | Algebra.norm v.Completion z = 1}) :=
    isCompact_univ_pi fun v => isCompact_normOne_completion F D v
  have hset : {x : D ⊗[F] (NumberField.InfiniteAdeleRing F) |
        Algebra.norm (NumberField.InfiniteAdeleRing F) x = 1}
      = ⇑(infiniteAdeleTensorPiEquiv F D).symm '' (Set.univ.pi
          fun v : NumberField.InfinitePlace F =>
            {z : D ⊗[F] v.Completion | Algebra.norm v.Completion z = 1}) := by
    ext x
    constructor
    · intro hx
      refine ⟨infiniteAdeleTensorPiEquiv F D x, fun v _ => ?_, by simp⟩
      show Algebra.norm v.Completion (infiniteAdeleTensorPiEquiv F D x v) = 1
      rw [← norm_infiniteAdele_apply F D x v]
      rw [show Algebra.norm (NumberField.InfiniteAdeleRing F) x = 1 from hx]
      rfl
    · rintro ⟨y, hy, rfl⟩
      show Algebra.norm (NumberField.InfiniteAdeleRing F)
        ((infiniteAdeleTensorPiEquiv F D).symm y) = 1
      funext v
      rw [norm_infiniteAdele_apply F D, LinearEquiv.apply_symm_apply]
      exact hy v (Set.mem_univ v)
  rw [hset]
  exact hTc.image (continuous_infiniteAdeleTensorPiEquiv_symm F D)

/--
**(sorry leaf — `D` is discrete and closed in `D ⊗ 𝔸_F`.)**

An element of `D` confined to a COMPACT set in the archimedean direction and to a
COMPACT set in the finite direction ranges over a FINITE set.

**Why it is true.** `D ⊗_F 𝔸_F = (D ⊗ 𝔸^∞) × (D ⊗ 𝔸_f)`, and the rigidification
`WithRigidification.algEquiv` identifies `D ⊗ 𝔸_f` topologically with `M₂(𝔸ᶠ)`
carrying `d ↦ WithRigidification.incl d`. So the set in question is the preimage in
`D` of a compact subset of `D ⊗ 𝔸_F`; `D` is discrete and closed there, and a
discrete subset of a compact set is finite.

This is exactly the pattern of
`NumberField.AdeleRing.DivisionAlgebra.Aux.T_finite_extracted1` and `T_finite` in
`Fermat/FLT/DivisionAlgebra/Finiteness.lean` (`D_discrete`,
`discrete_includeLeft_subgroup`, `inter_Discrete`), which are stated there for `D`
a DIVISION ring; only `Module.Finite F D` is used mathematically. Reusing them
either needs those statements relaxed to `[Ring D]`, or `DivisionRing D` derived
from total definiteness (`IsQuaternionAlgebra.nomepty_algEquiv_matrix_or_forall_isUnit`
plus `ℍ` having no zero divisors while `M₂(ℝ)` does).

Note neither definiteness nor total reality is needed here: this is discreteness. -/
theorem finite_setOf_tmul_mem_of_isCompact [IsQuaternionAlgebra F D]
    (Zi : Set (D ⊗[F] (NumberField.InfiniteAdeleRing F))) (hZi : IsCompact Zi)
    (Zf : Set M₂(𝔸ᶠ[F])) (hZf : IsCompact Zf) :
    {d : D | (d ⊗ₜ[F] (1 : NumberField.InfiniteAdeleRing F)) ∈ Zi ∧
      WithRigidification.incl (F := F) d ∈ Zf}.Finite :=
  sorry

/-- `B ⊗[R] A ≃ₐ[A] A ⊗[R] B`: the right-action version of `Algebra.TensorProduct.comm`,
built exactly as the first factor of `WithRigidification.algEquiv`. -/
def tensorCommRight (R B A : Type*) [CommRing R] [CommRing A] [Ring B]
    [Algebra R A] [Algebra R B] : B ⊗[R] A ≃ₐ[A] A ⊗[R] B :=
  { __ := Algebra.TensorProduct.comm R B A, commutes' _ := rfl }

@[simp] lemma tensorCommRight_tmul (R B A : Type*) [CommRing R] [CommRing A] [Ring B]
    [Algebra R A] [Algebra R B] (b : B) (a : A) :
    tensorCommRight R B A (b ⊗ₜ[R] a) = a ⊗ₜ[R] b := rfl

omit [NumberField F] [WithRigidification F D] in
/-- The `𝔸_F^∞`-algebra norm of `d ⊗ₜ 1` is the image of the `F`-algebra norm of `d`;
this is `Algebra.norm_one_tmul` transported along `tensorCommRight`. -/
lemma norm_tmul_one_infiniteAdele [IsQuaternionAlgebra F D] (d : D) :
    Algebra.norm (NumberField.InfiniteAdeleRing F)
      (d ⊗ₜ[F] (1 : NumberField.InfiniteAdeleRing F)) =
      algebraMap F (NumberField.InfiniteAdeleRing F) (Algebra.norm F d) := by
  rw [← Algebra.norm_one_tmul F (NumberField.InfiniteAdeleRing F) (B := D) d,
    ← Algebra.norm_eq_of_algEquiv (tensorCommRight F D (NumberField.InfiniteAdeleRing F))
      (d ⊗ₜ[F] (1 : NumberField.InfiniteAdeleRing F)), tensorCommRight_tmul]

/--
**PROVEN** from `isCompact_normOne_infiniteAdele` and `finite_setOf_tmul_mem_of_isCompact`.

For `V` a COMPACT subgroup of `GL₂(𝔸ᶠ)`, the group of `d ∈ Dˣ` with `ι(d) ∈ V` and
`Nm_{D/F}(d) = 1` is FINITE. Here `ι = WithRigidification.unitsIncl F D`, and
`Units.map (Algebra.norm F)` is the norm map `Dˣ →* Fˣ`.

**Why it is true, and where each hypothesis is used.** For a quaternion algebra
`Nm_{D/F} = nrd²` (see `WithRigidification.det_incl_sq`), so `Nm(d) = 1` says
`nrd(d) = ±1`. `F` totally real and `D` totally definite give `D ⊗_{F,v} ℝ ≃ ℍ`
at every infinite place, where `nrd` is the POSITIVE DEFINITE norm form; so
`nrd(d) = ±1` forces `nrd(d) = 1` and confines `d` to a product of spheres — a
compact subset of `D ⊗_ℚ ℝ`. Compactness of `V` confines `d` at the finite
places. So `d` ranges over `D ∩ (compact subset of D ⊗ 𝔸_F)`, and `D` is DISCRETE
and closed in `D ⊗ 𝔸_F`, whence finiteness.

**Both hypotheses are load-bearing.** At a real place where `D` splits, or at a
complex place, `nrd = det` and `det(d) = ±1` bounds nothing (`SL₂(ℝ)` is not
compact); the conclusion then fails for `D = M₂(F)`, whose corresponding group is
commensurable with `SL₂(𝒪_F)`.

**The assembly proven here.** The map `d ↦ (d : D)` is injective on the subgroup, and
sends it into the set of `d : D` with `d ⊗ₜ 1` in the compact `{Nm = 1}` (by
`norm_tmul_one_infiniteAdele`, since `Nm_{D/F}(d) = 1`) and with
`WithRigidification.incl d ∈ Units.val '' V` (compact, since `V` is). Total
definiteness enters ONLY through `isCompact_normOne_infiniteAdele`. -/
theorem finite_normOne_units_inf_comap [NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D] (V : Subgroup GL₂(𝔸ᶠ[F]))
    (hV : IsCompact (X := GL₂(𝔸ᶠ[F])) (V : Set GL₂(𝔸ᶠ[F]))) :
    Finite ((Units.map (Algebra.norm F (S := D))).ker ⊓
      V.comap (WithRigidification.unitsIncl F D) : Subgroup Dˣ) := by
  set Zi : Set (D ⊗[F] (NumberField.InfiniteAdeleRing F)) :=
    {x | Algebra.norm (NumberField.InfiniteAdeleRing F) x = 1} with hZidef
  set Zf : Set M₂(𝔸ᶠ[F]) := Units.val '' V with hZfdef
  set T : Set D := {d : D | (d ⊗ₜ[F] (1 : NumberField.InfiniteAdeleRing F)) ∈ Zi ∧
      WithRigidification.incl (F := F) d ∈ Zf} with hTdef
  have hTfin : T.Finite := finite_setOf_tmul_mem_of_isCompact (D := D) Zi
    (isCompact_normOne_infiniteAdele (D := D)) Zf (hV.image Units.continuous_val)
  haveI : Finite T := hTfin
  refine Finite.of_injective (β := T) (fun x => ⟨(x.1 : D), ?_, ?_⟩) ?_
  · have hker : Algebra.norm F ((x.1 : D)) = 1 := by
      have h : (x.1 : Dˣ) ∈ (Units.map (Algebra.norm F (S := D))).ker := x.2.1
      rw [MonoidHom.mem_ker] at h
      simpa [Units.ext_iff] using h
    simp only [hZidef, Set.mem_setOf_eq, norm_tmul_one_infiniteAdele (D := D), hker, map_one]
  · have hVmem : WithRigidification.unitsIncl F D x.1 ∈ V := x.2.2
    exact ⟨_, hVmem, rfl⟩
  · intro a b hab
    exact Subtype.ext (Units.ext (congrArg Subtype.val hab))

end Archimedean

/--
**PROVEN** from `comap_le_range_units_integers_of_isCompact` (the only remaining
sorry beneath it). NO definiteness.

Writing `A := {d ∈ Dˣ : ι(d) ∈ V}` and `P := Fˣ ⊆ Dˣ`, the norm image `Nm(A ⊓ P)`
has finite index in `Nm(A)`, for `V` a compact OPEN subgroup of `GL₂(𝔸ᶠ)`.

**The proof run here**, with `j : Fˣ →* 𝔸ᶠˣ` (`unitsAlgebraMapAdele`),
`sc : Fˣ →* GL₂(𝔸ᶠ)` the scalars (`unitsAlgebraMapMatrix`) and
`NM : GL₂(𝔸ᶠ) →* 𝔸ᶠˣ` the `𝔸ᶠ`-algebra norm of `M₂` (`unitsNormMatrix`,
so `NM(m) = det(m)²`). Put

* `C := NM(V) ≤ 𝔸ᶠˣ`, COMPACT (continuous image of a compact set), and `Q := j⁻¹(C)`;
* `V₀ ≤ 𝔸ᶠˣ` the scalars lying in `V`, OPEN (preimage of `V` under a continuous map),
  and `W := j⁻¹(V₀) = sc⁻¹(V)`;
* `Y := Q ⊓ W = j⁻¹(C ⊓ V₀)`.

Then, in order:

1. `Nm(A) ≤ Q`, because `j(Nm d) = NM(ι d)` (`unitsNormMatrix_unitsIncl`, i.e.
   `WithRigidification.det_incl_sq`) and `ι d ∈ V`;
2. `Nm(A ⊓ P) = W⁴` exactly, because `ι(λ·1) = sc λ`
   (`WithRigidification.unitsIncl_algebraMap`) and `Nm(λ·1) = λ⁴`
   (`norm_units_algebraMap_eq_pow`, since `finrank F D = 4`);
3. `W⁴ ≤ Y`, because `j(λ⁴) = NM(sc λ) ∈ C` (`unitsNormMatrix_unitsAlgebraMapMatrix`);
4. `[Q : Y] ≠ 0` from `relIndex_ne_zero_of_isCompact_of_isOpen` at `C ⊓ V₀ ≤ C`,
   pulled back along `j` by `Subgroup.relIndex_comap_ne_zero`;
5. `[Y : Y⁴] ≠ 0` by mathlib's `Subgroup.isFiniteRelIndex_map_powMonoidHom_of_fg`,
   `Y` being finitely generated by `fg_comap_unitsAlgebraMapAdele_of_isCompact` and
   `subgroup_fg_of_le_fg`; since `Y⁴ ≤ W⁴ ≤ Y` this gives `[Y : W⁴] ≠ 0`, and with
   (4), `[Q : W⁴] ≠ 0`;
6. finally `Nm(A ⊓ P) = W⁴ ≤ Nm(A) ≤ Q`, so `[Nm(A) : Nm(A ⊓ P)]` divides
   `[Q : W⁴]` by `Subgroup.relIndex_mul_relIndex`.

**`IsCompact` and `IsOpen` are BOTH load-bearing here** — compactness of `V` makes
`C` compact, which is what forces `Q ≤ 𝒪_Fˣ` (step 5's finite generation);
openness makes `V₀` open, which is step 4. Total definiteness is NOT used:
this half is a statement about `F` and the level, not about the archimedean places
of `D`, which is why the hypothesis is deliberately absent. -/
theorem relIndex_normImage_ne_zero [IsQuaternionAlgebra F D] (V : Subgroup GL₂(𝔸ᶠ[F]))
    (hVc : IsCompact (X := GL₂(𝔸ᶠ[F])) (V : Set GL₂(𝔸ᶠ[F])))
    (hVo : IsOpen (X := GL₂(𝔸ᶠ[F])) (V : Set GL₂(𝔸ᶠ[F]))) :
    Subgroup.relIndex
      (Subgroup.map (Units.map (Algebra.norm F (S := D)))
        (V.comap (WithRigidification.unitsIncl F D) ⊓
          MonoidHom.range (Units.map (algebraMap F D).toMonoidHom)))
      (Subgroup.map (Units.map (Algebra.norm F (S := D)))
        (V.comap (WithRigidification.unitsIncl F D))) ≠ 0 := by
  set N : Dˣ →* Fˣ := Units.map (Algebra.norm F (S := D)) with hN
  set A : Subgroup Dˣ := V.comap (WithRigidification.unitsIncl F D) with hA
  set P : Subgroup Dˣ := MonoidHom.range (Units.map (algebraMap F D).toMonoidHom) with hP
  set C : Subgroup 𝔸ᶠ[F]ˣ := V.map (unitsNormMatrix F) with hC
  set Q : Subgroup Fˣ := C.comap (unitsAlgebraMapAdele F) with hQ
  set V₀ : Subgroup 𝔸ᶠ[F]ˣ :=
    V.comap (Units.map (RingHom.toMonoidHom (algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F])))) with hV₀
  set W : Subgroup Fˣ := V₀.comap (unitsAlgebraMapAdele F) with hW
  set Y : Subgroup Fˣ := Q ⊓ W with hY
  have hCcomp : IsCompact ((C : Set 𝔸ᶠ[F]ˣ)) := hVc.image continuous_unitsNormMatrix
  -- membership in `W` is membership of the scalar matrix in `V`
  have hmemW : ∀ x : Fˣ, x ∈ W ↔ unitsAlgebraMapMatrix F x ∈ V := by
    intro x
    rw [hW, Subgroup.mem_comap, hV₀, Subgroup.mem_comap, unitsAlgebraMapMatrix_eq (F := F)]
    rfl
  -- (1) the norm image of `A` lands in `Q`
  have hS1 : Subgroup.map N A ≤ Q := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_comap.mpr
      (Subgroup.mem_map.mpr ⟨_, hd, unitsNormMatrix_unitsIncl (D := D) d⟩)
  -- (2) the norm image of `A ⊓ P` is the group of fourth powers of `W`
  have hS2 : Subgroup.map N (A ⊓ P) = W.map (powMonoidHom 4) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨hdA, hdP⟩ := Subgroup.mem_inf.mp hd
      obtain ⟨x, rfl⟩ := hdP
      refine Subgroup.mem_map.mpr ⟨x, ?_, ?_⟩
      · rw [hmemW]
        have hx : WithRigidification.unitsIncl F D (x.map (algebraMap F D).toMonoidHom) ∈ V := hdA
        rwa [WithRigidification.unitsIncl_algebraMap] at hx
      · simpa [powMonoidHom] using (norm_units_algebraMap_eq_pow (D := D) x).symm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_map.mpr ⟨x.map (algebraMap F D).toMonoidHom,
        Subgroup.mem_inf.mpr ⟨?_, ⟨x, rfl⟩⟩, ?_⟩
      · show WithRigidification.unitsIncl F D _ ∈ V
        rw [WithRigidification.unitsIncl_algebraMap]
        exact (hmemW x).mp hx
      · simpa [powMonoidHom] using norm_units_algebraMap_eq_pow (D := D) x
  -- (3) fourth powers of `W` lie in `Y`
  have hWQ : W.map (powMonoidHom 4) ≤ Q := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_comap.mpr
      (Subgroup.mem_map.mpr ⟨unitsAlgebraMapMatrix F x, (hmemW x).mp hx, ?_⟩)
    rw [unitsNormMatrix_unitsAlgebraMapMatrix]
    simp [powMonoidHom]
  have hS3 : W.map (powMonoidHom 4) ≤ Y := by
    refine le_inf hWQ ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact W.pow_mem hx 4
  -- (4) `Y` has finite index in `Q`
  have hS4 : Y.relIndex Q ≠ 0 := by
    have hscal : Continuous (fun x : 𝔸ᶠ[F] => (algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F])) x) := by
      refine continuous_matrix fun i j => ?_
      simp only [Matrix.algebraMap_matrix_apply]
      split <;> fun_prop
    have hopen : IsOpen ((V₀ : Set 𝔸ᶠ[F]ˣ)) := hVo.preimage (Units.continuous_map hscal)
    have hkey := relIndex_ne_zero_of_isCompact_of_isOpen C V₀ hCcomp hopen
    have h2 := Subgroup.relIndex_comap_ne_zero (unitsAlgebraMapAdele F) hkey
    rwa [Subgroup.comap_inf] at h2
  -- (5) `Y` is finitely generated, so its fourth powers have finite index in it
  have hYfg : Y.FG :=
    subgroup_fg_of_le_fg (fg_comap_unitsAlgebraMapAdele_of_isCompact C hCcomp) inf_le_left
  have hS5 : (Y.map (powMonoidHom 4)).relIndex Y ≠ 0 :=
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp
      (Subgroup.isFiniteRelIndex_map_powMonoidHom_of_fg hYfg (by norm_num))
  have hS6 : (W.map (powMonoidHom 4)).relIndex Y ≠ 0 := fun h0 =>
    hS5 (Subgroup.relIndex_eq_zero_of_le_left (Subgroup.map_mono inf_le_right) h0)
  have hS7 : (W.map (powMonoidHom 4)).relIndex Q ≠ 0 := Subgroup.relIndex_ne_zero_trans hS6 hS4
  -- (6) conclude
  have hle1 : Subgroup.map N (A ⊓ P) ≤ Subgroup.map N A := Subgroup.map_mono inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hS1
  intro h0
  rw [h0, zero_mul] at hmul
  rw [hS2] at hmul
  exact hS7 hmul.symm

/--
**Voight, Lemma 17.7.13, in its textbook form**: for `V ≤ GL₂(𝔸ᶠ)` compact open,
`Fˣ` has finite index in `{d ∈ Dˣ : ι(d) ∈ V}`. PROVEN here from the two theorems
above; no level structure, no double-coset representative `g`.

The proof is the classical two-step argument, run inside the group `A` itself.
Write `N : Dˣ →* Fˣ` for the norm, `A := V.comap ι`, `P := Fˣ`, and let
`M := N ∘ A.subtype : A →* Fˣ`. Then

* `[P ⊔ ker M : P] ≠ 0` because `ker M = A ⊓ ker N` is FINITE
  (`finite_normOne_units_inf_comap`) and normal in `A`, by
  `relIndex_sup_ne_zero_of_normal`;
* `[A : P ⊔ ker M] ≠ 0` because `P ⊔ ker M = M⁻¹(M(P))` (`Subgroup.comap_map_eq`),
  so that index is `[M(A) : M(P)]`, which is `relIndex_normImage_ne_zero`;

and the two multiply to `[A : P]` by `Subgroup.relIndex_mul_index`. -/
theorem relIndex_range_algebraMap_units_ne_zero [NumberField.IsTotallyReal F]
    [IsQuaternionAlgebra F D] [IsQuaternionAlgebra.IsTotallyDefinite F D]
    (V : Subgroup GL₂(𝔸ᶠ[F])) (hVc : IsCompact (X := GL₂(𝔸ᶠ[F])) (V : Set GL₂(𝔸ᶠ[F])))
    (hVo : IsOpen (X := GL₂(𝔸ᶠ[F])) (V : Set GL₂(𝔸ᶠ[F]))) :
    Subgroup.relIndex (MonoidHom.range (Units.map (algebraMap F D).toMonoidHom))
      (V.comap (WithRigidification.unitsIncl F D)) ≠ 0 := by
  set N : Dˣ →* Fˣ := Units.map (Algebra.norm F (S := D)) with hNdef
  set A : Subgroup Dˣ := V.comap (WithRigidification.unitsIncl F D) with hAdef
  set P : Subgroup Dˣ := MonoidHom.range (Units.map (algebraMap F D).toMonoidHom) with hPdef
  set M : A →* Fˣ := N.comp A.subtype with hMdef
  have hMker : M.ker = N.ker.subgroupOf A := rfl
  have hfin : Finite M.ker := by
    haveI : Finite ((N.ker ⊓ A : Subgroup Dˣ)) := finite_normOne_units_inf_comap V hVc
    rw [hMker, ← Subgroup.inf_subgroupOf_right]
    exact Finite.of_equiv _
      (Subgroup.subgroupOfEquivOfLe (H := N.ker ⊓ A) (K := A) inf_le_right).symm.toEquiv
  have h1 : (P.subgroupOf A).relIndex (P.subgroupOf A ⊔ M.ker) ≠ 0 :=
    relIndex_sup_ne_zero_of_normal hfin
  have h2 : (P.subgroupOf A ⊔ M.ker).index ≠ 0 := by
    rw [← Subgroup.comap_map_eq, Subgroup.index_comap]
    have e1 : Subgroup.map M (P.subgroupOf A) = Subgroup.map N (A ⊓ P) := by
      rw [hMdef, ← Subgroup.map_map, Subgroup.subgroupOf, Subgroup.map_comap_eq,
        Subgroup.range_subtype]
    have e2 : M.range = Subgroup.map N A := by
      rw [hMdef, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [e1, e2]
    exact relIndex_normImage_ne_zero V hVc hVo
  rw [Subgroup.relIndex, ← Subgroup.relIndex_mul_index (le_sup_left (b := M.ker))]
  exact mul_ne_zero h1 h2

/--
**Voight, Lemma 17.7.13: the unit group of an order in a totally definite
quaternion algebra is finite modulo the centre.** PROVEN 2026-07-27 from
`relIndex_range_algebraMap_units_ne_zero`. `finite_normOne_units_inf_comap` and
`relIndex_normImage_ne_zero` beneath it were PROVEN 2026-07-28; the three leaves
that remain beneath THEM are `comap_le_range_units_integers_of_isCompact`,
`isCompact_normOne_infiniteAdele` and `finite_setOf_tmul_mem_of_isCompact`.

`Fˣ` has finite index in `U ∩ g⁻¹ Dˣ g`.

This is the arithmetic heart of `isFiniteRelIndex_Δ`, and the only place in this
file where total definiteness is used.

**Statement is FALSE without total definiteness**: for split `D = M₂(F)` the
group is commensurable with `SL₂(𝒪_F)`, which is infinite modulo `Fˣ`. The
`[IsQuaternionAlgebra.IsTotallyDefinite F D]` hypothesis is therefore load-bearing
and must not be dropped. (It is consumed, through this declaration, by
`finite_normOne_units_inf_comap`.)

**The reduction proven here** is bookkeeping, and it is worth saying exactly what
it removes. Let `ι := WithRigidification.unitsIncl F D : Dˣ ↪ GL₂(𝔸ᶠ)` and
`f := (g⁻¹ · g) ∘ ι`, still injective, with `range f = g⁻¹ Dˣ g`. Then

* `f(U.comap f) = U ⊓ g⁻¹ Dˣ g` (`Subgroup.map_comap_eq`), so by
  `Subgroup.relIndex_comap` the whole index may be computed inside `Dˣ`;
* `𝓕ˣ.comap f = Fˣ` because `𝓕ˣ` consists of scalar matrices, hence is
  conjugation-invariant, and `ι` is injective;
* `U.comap f = (g U g⁻¹).comap ι`, and `g U g⁻¹` is again compact open.

So the leaf becomes `relIndex_range_algebraMap_units_ne_zero` at `V := g U g⁻¹`:
`g`, the level structure and `GL₂` conjugation all disappear. -/
theorem relIndex_unitsOrder_ne_zero [NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D] (ℒ : LevelStruct F R) (g : GL₂(𝔸ᶠ[F])) :
    Subgroup.relIndex 𝓕ˣ (ℒ.U ⊓ toConjAct g⁻¹ • 𝓓ˣ) ≠ 0 := by
  set f : Dˣ →* GL₂(𝔸ᶠ[F]) :=
    (MulDistribMulAction.toMonoidEnd (ConjAct GL₂(𝔸ᶠ[F])) GL₂(𝔸ᶠ[F]) (toConjAct g⁻¹)).comp
      (WithRigidification.unitsIncl F D) with hfdef
  have hfapp : ∀ d : Dˣ, f d = toConjAct g⁻¹ • WithRigidification.unitsIncl F D d :=
    fun _ ↦ rfl
  have hfrange : f.range = toConjAct g⁻¹ • 𝓓ˣ := MonoidHom.range_comp _ _
  have hmap : Subgroup.map f (ℒ.U.comap f) = ℒ.U ⊓ toConjAct g⁻¹ • 𝓓ˣ := by
    rw [Subgroup.map_comap_eq, hfrange, inf_comm]
  rw [← hmap, ← Subgroup.relIndex_comap]
  have hcentral : ∀ x : Fˣ, toConjAct g⁻¹ • (x.map (algebraMap F M₂(𝔸ᶠ[F])).toMonoidHom)
      = x.map (algebraMap F M₂(𝔸ᶠ[F])).toMonoidHom := by
    intro x
    ext1
    rw [ConjAct.toConjAct_inv_smul]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [← Algebra.commutes]
    simp [mul_assoc]
  have hcomapF : (𝓕ˣ : Subgroup GL₂(𝔸ᶠ[F])).comap f
      = MonoidHom.range (Units.map (algebraMap F D).toMonoidHom) := by
    ext d
    simp only [Subgroup.mem_comap, MonoidHom.mem_range, hfapp]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply WithRigidification.unitsIncl_injective F D
      rw [WithRigidification.unitsIncl_algebraMap]
      rw [← hcentral x] at hx
      simpa using congrArg (fun z : GL₂(𝔸ᶠ[F]) ↦ (toConjAct g⁻¹)⁻¹ • z) hx
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [WithRigidification.unitsIncl_algebraMap, hcentral]⟩
  have hcomapU : ℒ.U.comap f
      = (toConjAct g • ℒ.U).comap (WithRigidification.unitsIncl F D) := by
    ext d
    simp only [Subgroup.mem_comap, hfapp, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ← ConjAct.toConjAct_inv]
  rw [hcomapF, hcomapU]
  exact relIndex_range_algebraMap_units_ne_zero _
    (ℒ.isCompact_U.image (continuous_const_smul _)) (ℒ.isOpen_U.smul _)

/--
`[Δ_g : Fˣ]` is finite.
Since `g⁻¹ U g` is compact open, `g⁻¹ U g ⊆ x⁻¹GL₂(∏ 𝒪_{Fᵥ})x` for some `x`.
Let `𝒪 := x⁻¹M₂(∏ 𝒪_{Fᵥ})x ∩ D`.
Then `𝒪` is an order (why?) and `Δ_g/Fˣ ↪ 𝒪¹ := { x ∈ 𝒪 | N(x) = 1 }`,
where the latter is finite because it is discrete and bounded in `D ⊗_{ℚ} ℝ = ∏ ℍ`
(See Lemma 17.7.13 in Voight).

**AXIOM-POLICY NOTE (vendoring, 2026-07-27).** In the reference FLT project this
instance is discharged by the tactic `knownin1980s`, which is
`axiom knownin1980s {P : Prop} : P` — a proof of an ARBITRARY proposition, i.e. an
inconsistency-grade axiom. This project admits only `propext`, `Classical.choice`
and `Quot.sound`, and its root gate `#assert_no_sorry fermat_last_theorem` enforces
that. So the axiom is NOT vendored: the whole module `FLT.Assumptions.KnownIn1980s`
is dropped, and its single use in the vendored closure — this one — became an
ordinary sorried leaf with its statement written out in full.

**DECOMPOSED 2026-07-27.** This instance is now PROVEN from the lemmas above.
The group theory (`relIndex_sup_ne_zero_of_le_center`,
`relIndex_sup_inf_ne_zero_of_le_center`, `relIndex_sup_ne_zero_of_normal`), the
transport `relIndex_ray_ne_zero`, `index_ray_ne_zero`, and (2026-07-27, second
pass) the whole of `relIndex_unitsOrder_ne_zero` and
`relIndex_range_algebraMap_units_ne_zero` are proven. The two halves of Voight
17.7.13, `finite_normOne_units_inf_comap` (the archimedean half — the only
consumer of `IsQuaternionAlgebra.IsTotallyDefinite` in this file) and
`relIndex_normImage_ne_zero` (the Dirichlet-units half, no definiteness), were
then PROVEN 2026-07-28. THREE sorried leaves remain beneath them:

* `comap_le_range_units_integers_of_isCompact` — a compact subgroup of `𝔸ᶠ[F]ˣ`
  meets `Fˣ` inside `(𝓞 F)ˣ`. Statement about `F` alone.
* `isCompact_normOne_infiniteAdele` — `{Nm = 1}` is compact in `D ⊗ 𝔸^∞`. PROVEN
  2026-07-28 by decomposition over the infinite places, as is its place-local half
  `isCompact_normOne_completion`. The three leaves beneath them are
  `exists_ringEquiv_quaternion_of_isTotallyDefinite` (`D ⊗ F_v ≃+* ℍ` topologically —
  where total definiteness is now consumed, here and nowhere else),
  `norm_infiniteAdele_apply` and `continuous_infiniteAdeleTensorPiEquiv_symm` (both
  definiteness-free).
* `finite_setOf_tmul_mem_of_isCompact` — `D` is discrete and closed in `D ⊗ 𝔸_F`.

`index_ray_ne_zero` — finiteness of a ray class group of `F`, which does not
mention `D` — was the third leaf on this list and is now PROVEN from the
Fujisaki lemma at `D = F`
(`NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset`), via the
tensor-product transport `tensorLid` and the abelian double-coset surjection
`index_sup_ne_zero_of_finite_doubleCoset`.

Those two are now the only unproven statements in the vendored closure;
everything else is proven. -/
@[nolint unusedArguments]
instance isFiniteRelIndex_Δ [NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D] (ℒ : LevelStruct F R) (g : GL₂(𝔸ᶠ[F])) :
    Subgroup.IsFiniteRelIndex 𝓕ˣ (ℒ.Δ D g) := by
  haveI : (𝓕ˣ : Subgroup GL₂(𝔸ᶠ[F])).Normal := Subgroup.normal_of_le_center _ (by
    rintro _ ⟨x, rfl⟩
    simp [Subgroup.mem_center_iff, Units.ext_iff, Algebra.commutes])
  have hPZ : (𝓕ˣ : Subgroup GL₂(𝔸ᶠ[F])) ≤ 𝔸ˣ F := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x.map (algebraMap _ _).toMonoidHom, by
      simp [Units.ext_iff, ← IsScalarTower.algebraMap_apply, RingHom.toMonoidHom_eq_coe]⟩
  have hPΓ : (𝓕ˣ : Subgroup GL₂(𝔸ᶠ[F])) ≤ toConjAct g⁻¹ • 𝓓ˣ :=
    (ℒ.range_units_le_range (D := D) g).trans inf_le_right
  refine Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr ?_
  refine Subgroup.relIndex_ne_zero_trans ?_
    (relIndex_sup_inf_ne_zero_of_le_center
      (range_unitsMap_finiteAdeleRing_le_center (F := F)) hPZ hPΓ ℒ.relIndex_ray_ne_zero)
  rw [Subgroup.relIndex_sup_left]
  exact ℒ.relIndex_unitsOrder_ne_zero (D := D) g

/-- `Dˣ＼GL₂(𝔸 F)／U` is notation for the type of double cosets by the image of `Dˣ` in
`GL₂(𝔸ᶠ[F])` and by `U`. -/
scoped[FLT] notation D "ˣ＼GL₂(𝔸 " F ")／" U:max =>
  DoubleCoset.Quotient (G := GL₂(𝔸ᶠ[F])) (MonoidHom.range <| WithRigidification.unitsIncl F D) U

instance : 𝓕ˣ.Normal := Subgroup.normal_of_le_center _ (by
  rintro _ ⟨x, rfl⟩
  simp [Subgroup.mem_center_iff, Units.ext_iff, Algebra.commutes])

variable (D) in
/-- The index `[U 𝔸ˣ ∩ g⁻¹ Dˣ g : Fˣ]` as a function on `Dˣ\GL₂(𝔸)/U`. -/
def ΔIndex (g : Dˣ＼GL₂(𝔸 F)／ℒ.UA) : ℕ :=
  g.lift (fun g ↦ 𝓕ˣ.relIndex (ℒ.Δ D g)) <| fun g₁ g₂ e ↦ by
    obtain ⟨_, ⟨d, rfl⟩, u, hu, rfl⟩ := DoubleCoset.rel_iff.mp e
    have h₁ : (toConjAct (ιD d))⁻¹ • 𝓓ˣ = 𝓓ˣ :=
      Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer ⟨d⁻¹, rfl⟩)
    dsimp [Δ]
    simp only [mul_inv_rev, mul_smul, h₁]
    conv_rhs => rw [← Subgroup.relIndex_map_map_of_injective (f :=
      (MulDistribMulAction.toMulEquiv _ (ConjAct.toConjAct u)).toMonoidHom) _ _
      (MulDistribMulAction.toMulEquiv _ (ConjAct.toConjAct u)).injective,
      Subgroup.map_inf _ _ _
        (by exact (MulDistribMulAction.toMulEquiv _ (ConjAct.toConjAct u)).injective)]
    congr 2
    · exact (Subgroup.conjAct_pointwise_smul_eq_self
        ((Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge trivial)).symm
    · exact (Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hu)).symm
    · change _ = toConjAct u • ((toConjAct u)⁻¹ • (toConjAct g₁)⁻¹ • 𝓓ˣ)
      simp [← mul_smul]

@[simp]
lemma ΔIndex_mk (g : GL₂(𝔸ᶠ[F])) :
    ℒ.ΔIndex D (DoubleCoset.mk _ _ g) = 𝓕ˣ.relIndex (ℒ.Δ D g) := rfl

lemma isOpen_map_ker : IsOpen (X := GL₂(𝔸ᶠ[F])) (ℒ.χ.ker.map ℒ.U.subtype) :=
  ℒ.isOpen_U.isOpenEmbedding_subtypeVal.isOpenMap _ ℒ.isOpen_ker

variable (D M) in
/-- The subspace of modular forms of a given level. -/
def form : Submodule R (WeightTwoAutomorphicForm F D M) where
  carrier := { f | ∀ x : ℒ.U, x • f = ℒ.χ x • f }
  add_mem' {f g} hf hg x := by simp only [Set.mem_setOf_eq] at hf hg; simp [hf, hg]
  zero_mem' := by simp
  smul_mem' r f hf x := by
    simp only [Set.mem_setOf_eq] at hf
    rw [smul_comm, hf, smul_comm]

instance {F D R M S : Type*} [Field F] [NumberField F] [Ring D] [Algebra F D]
    [WithRigidification F D] [CommRing R] [AddCommGroup M] [Module R M] [Semiring S]
    [Module S M] [SMulCommClass R S M] : SMulCommClass R S (WeightTwoAutomorphicForm F D M) where
  smul_comm r s f := by ext; simp [smul_comm]

instance {F D R M S : Type*} [Field F] [NumberField F] [Ring D] [Algebra F D]
    [WithRigidification F D] [CommRing R] [AddCommGroup M] [Module R M] [Semiring S] [SMul R S]
    [Module S M] [IsScalarTower R S M] : IsScalarTower R S (WeightTwoAutomorphicForm F D M) where
  smul_assoc r s f := by ext; simp

variable (D M) in
/-- Should not be used directly. -/
abbrev formSubmodule (S : Type*) [Semiring S] [Module S M] [SMulCommClass R S M] :
    Submodule S (WeightTwoAutomorphicForm F D M) where
  __ := ℒ.form D M
  smul_mem' c x hx u := by rw [smul_comm, hx u, ← smul_comm]

/-- A constructor for forms in `S(U, χ)`. -/
@[simps]
def mkForm
    (f : GL₂(𝔸ᶠ[F]) → M)
    (left_invt : ∀ d g, f (ιD d * g) = f g)
    (right_invt : ∀ g, ∀ u : ℒ.U, f (g * ↑u) = ℒ.χ u • f g)
    (trivial_central_char : ∀ z : 𝔸ᶠ[𝓞 F, F]ˣ, ∀ g, f (z • g) = f g) :
    ℒ.form D M where
  val.toFun := f
  val.left_invt := left_invt
  val.right_invt := ⟨_, ℒ.isOpen_map_ker, by rintro g _ ⟨x, hx, rfl⟩; simp_all⟩
  val.trivial_central_char := trivial_central_char
  property g := by ext; exact right_invt _ _

@[simp]
lemma form_mul_coe (ℒ : LevelStruct F R) (f : ℒ.form D M) (x : GL₂(𝔸ᶠ[F])) (u : ℒ.U) :
    f.1 (x * u) = ℒ.χ u • f.1 x := congr($(f.2 u) x)

@[simp]
lemma form_mul_coe' (ℒ : LevelStruct F R) (f : ℒ.form D M) (x : GL₂(𝔸ᶠ[F])) (u : ℒ.UA) :
    f.1 (x * u) = ℒ.χA u • f.1 x := by
  obtain ⟨⟨u, _, ⟨z, rfl⟩⟩, rfl⟩ := Subgroup.prodToSupOfRight_surjective _ _
    ((range_unitsMap_finiteAdeleRing_le_center ..).trans (Subgroup.center_le_centralizer _)) u
  simp [χA, ← mul_assoc]

lemma apply_mul_eq_χA_smul
    (f) (hf : f ∈ ℒ.form D M) (u : ℒ.UA) (g) : f (g * u) = ℒ.χA u • f g :=
  ℒ.form_mul_coe' ⟨f, hf⟩ g u

instance {F D R M S : Type*} [Field F] [NumberField F] [Ring D] [Algebra F D]
    [WithRigidification F D] [CommRing R] [AddCommGroup M] [Module R M] [Semiring S]
    [Module S M] [SMulCommClass R S M] (ℒ : LevelStruct F R) : Module S (ℒ.form D M) :=
  inferInstanceAs <| Module S <| ℒ.formSubmodule D M S

@[simp]
lemma coe_smul
    {F D R M S : Type*} [Field F] [NumberField F] [Ring D] [Algebra F D]
    [WithRigidification F D] [CommRing R] [AddCommGroup M] [Module R M] [Semiring S]
    [Module S M] [SMulCommClass R S M] (ℒ : LevelStruct F R) (s : S) (f : ℒ.form D M) :
    (s • f).1 = s • f.1 := rfl

instance {F D R M S T : Type*} [Field F] [NumberField F] [Ring D] [Algebra F D]
    [WithRigidification F D] [CommRing R] [AddCommGroup M] [Module R M] [Semiring S]
    [Module S M] [SMulCommClass R S M] [Semiring T]
    [Module T M] [SMulCommClass R T M] [SMulCommClass S T M]
    (ℒ : LevelStruct F R) : SMulCommClass S T (ℒ.form D M) where
  smul_comm r s m := by ext; simp [smul_comm]

instance {F D R M S T : Type*} [Field F] [NumberField F] [Ring D] [Algebra F D]
    [WithRigidification F D] [CommRing R] [AddCommGroup M] [Module R M] [CommRing S]
    [Module S M] [SMulCommClass R S M] [Semiring T] [Algebra S T]
    [Module T M] [SMulCommClass R T M] [IsScalarTower S T M] (ℒ : LevelStruct F R) :
    IsScalarTower S T (ℒ.form D M) :=
  inferInstanceAs <| IsScalarTower S T <| ℒ.formSubmodule D M T

/-- A constructor for forms in `S(U, χ)` which instead asks for behaviour on `U 𝔸ˣ`. -/
abbrev mkFormA
    (f : GL₂(𝔸ᶠ[F]) → M)
    (left_invt : ∀ d g, f (ιD d * g) = f g)
    (right_invt : ∀ g, ∀ u : ℒ.UA, f (g * ↑u) = ℒ.χA u • f g) :
    ℒ.form D M :=
  ℒ.mkForm f left_invt (fun g u ↦ by simpa using right_invt g (Subgroup.inclusion le_sup_left u))
    (fun z g ↦ by
      convert right_invt g (Subgroup.inclusion le_sup_right ⟨_, z, rfl⟩) using 2
      · ext1
        simp [Algebra.smul_def, Units.smul_def, Algebra.commutes]
      · simp [-Subgroup.inclusion_mk])

/-- Mapping a `LevelStruct` along a ring hom. -/
@[simps]
protected noncomputable abbrev map {R' : Type*} [CommRing R'] (ℒ : LevelStruct F R) (f : R →+* R') :
    LevelStruct F R' where
  __ := ℒ
  χ := f.toMonoidHom.comp ℒ.χ
  range_unitsMap_le_ker_χ := ℒ.range_unitsMap_le_ker_χ.trans (MonoidHom.ker_le_ker_comp _ _)
  isOpen_ker := Subgroup.isOpen_mono (MonoidHom.ker_le_ker_comp _ _) ℒ.isOpen_ker

lemma form_map {R' M : Type*} [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M]
    [Module R' M] [IsScalarTower R R' M] (ℒ : LevelStruct F R) :
    ((ℒ.map (algebraMap R R')).form D M).restrictScalars R = ℒ.form D M := by
  ext; simp [form]

@[ext (iff := false)]
protected lemma ext (ℒ ℒ' : LevelStruct F R) (H : ℒ.U = ℒ'.U)
    (H' : ℒ.χ.comp (Subgroup.inclusion H.ge) = ℒ'.χ) : ℒ = ℒ' := by
  obtain ⟨U, _, _, χ⟩ := ℒ
  obtain ⟨U', _, _, χ'⟩ := ℒ'
  obtain rfl : U = U' := H
  obtain rfl : χ = χ' := H'
  rfl

open scoped Pointwise in
instance : SMul GL₂(𝔸ᶠ[F]) (LevelStruct F R) where
  smul g ℒ :=
  { U := ConjAct.toConjAct g • ℒ.U
    isCompact_U := ℒ.isCompact_U.image (continuous_const_smul _)
    isOpen_U := ℒ.isOpen_U.smul _
    χ := ℒ.χ.comp (Subgroup.equivSMul _ _).symm.toMonoidHom
    range_unitsMap_le_ker_χ := by
      rintro ⟨_, hu⟩ ⟨u, rfl⟩
      have : (toConjAct g)⁻¹ • u.map (algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F])).toMonoidHom =
          u.map (algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F])).toMonoidHom := by
        ext1; simp [toConjAct_inv_smul', ← Algebra.commutes]
      have hu' : u.map (algebraMap 𝔸ᶠ[F] M₂(𝔸ᶠ[F])).toMonoidHom ∈ ℒ.U :=
        this ▸ Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hu
      simpa [Subtype.ext_iff, smul_eq_iff_eq_inv_smul, this, hu'] using
        ℒ.range_unitsMap_le_ker_χ (x := ⟨_, hu'⟩) ⟨u, rfl⟩
    isOpen_ker := by
      rw [← MonoidHom.comap_ker]
      refine ℒ.isOpen_ker.preimage (continuous_induced_rng.mpr ?_)
      convert show Continuous fun x : ↑(toConjAct g • ℒ.U) ↦ (toConjAct g)⁻¹ • x.1 by fun_prop
      simp }

@[simp]
lemma smul_U (g : GL₂(𝔸ᶠ[F])) (ℒ : LevelStruct F R) : (g • ℒ).U = ConjAct.toConjAct g • ℒ.U := rfl

lemma smul_χ (g : GL₂(𝔸ᶠ[F])) (ℒ : LevelStruct F R) :
    (g • ℒ).χ = ℒ.χ.comp (Subgroup.equivSMul _ _).symm.toMonoidHom := rfl

@[simp]
lemma smul_χ_apply (g : GL₂(𝔸ᶠ[F])) (ℒ : LevelStruct F R) (a) :
    (g • ℒ).χ a = ℒ.χ ⟨ConjAct.toConjAct g⁻¹ • a, ((Subgroup.equivSMul _ _).symm a).2⟩ := rfl

open scoped Pointwise in
instance : MulAction GL₂(𝔸ᶠ[F]) (LevelStruct F R) where
  mul_smul g₁ g₂ ℒ := by
    ext1
    · simp [mul_smul]
    ext a
    simp only [MonoidHom.coe_comp, Function.comp_apply, smul_χ_apply]
    simp [mul_smul]
    rfl
  one_smul ℒ := by
    ext1
    · exact one_smul _ _
    · ext a
      simp only [MonoidHom.coe_comp, Function.comp_apply, smul_χ_apply]
      simp
      rfl

open scoped Pointwise

variable (D) in
/-- A level struct is sufficiently small if the associated character has finite order coprime
to `[Δ_g : Fˣ]` for all `g`. -/
class IsSufficientlySmall (ℒ : LevelStruct F R) where
  coprime_ΔIndex : ∀ g, (orderOf ℒ.χ).Coprime (ℒ.ΔIndex D g)

export LevelStruct.IsSufficientlySmall (coprime_ΔIndex)

variable (D) in
lemma toConjAct_smul_le_ker_χA [ℒ.IsSufficientlySmall D] (g : GL₂(𝔸ᶠ[F])) :
    (toConjAct g • 𝓓ˣ).subgroupOf ℒ.UA ≤ ℒ.χA.ker := by
  refine Subgroup.le_ker_of_le_ker_of_coprime_relIndex _ (orderOf ℒ.χ)
    (K₁ := 𝓕ˣ.subgroupOf _) ?_ ?_ ?_
  · ext x
    obtain ⟨⟨u, _, ⟨z, rfl⟩⟩, rfl⟩ := Subgroup.prodToSupOfRight_surjective _ _
      ((range_unitsMap_finiteAdeleRing_le_center ..).trans (Subgroup.center_le_centralizer _)) x
    simpa [LevelStruct.χA, -pow_orderOf_eq_one] using
      congr($(pow_orderOf_eq_one ℒ.χ) u)
  · simp only [Subgroup.subgroupOf, Subgroup.relIndex_comap, Subgroup.map_comap_eq,
      Subgroup.range_subtype]
    exact ℒ.coprime_ΔIndex (DoubleCoset.mk _ _ g⁻¹)
  · rintro ⟨x, hx⟩ ⟨u, rfl⟩
    exact ℒ.χA_inclusion_right ⟨_, u.map (algebraMap _ _).toMonoidHom, rfl⟩

lemma χA_eq_of_exists_mul_mul_eq [ℒ.IsSufficientlySmall D] (u v : ℒ.UA)
    (huv : ∃ g d d', ιD d * g * u = ιD d' * g * v) : ℒ.χA u = ℒ.χA v := by
  apply ((Group.isUnit v⁻¹).map ℒ.χA).mul_right_cancel
  simp only [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨g, d, d', e⟩ := huv
  refine ℒ.toConjAct_smul_le_ker_χA (D := D) g⁻¹ ?_
  suffices ∃ x, ιD x = g * u * v⁻¹ * g⁻¹ by
    simpa [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        toConjAct_smul, mul_assoc, Subgroup.mem_sup_of_normal_right]
  refine ⟨d⁻¹ * d', ?_⟩
  simp [eq_mul_inv_iff_mul_eq]
  simpa [mul_assoc, inv_mul_eq_iff_eq_mul] using e.symm

/-- Given a section to the projection `Dˣ＼GL₂(𝔸ᶠ[F])／U → GL₂(𝔸ᶠ[F])`,
`S(U, χ)` is isomorphic to the finite free module with basis `Dˣ＼GL₂(𝔸ᶠ[F])／U`. -/
@[simps apply, simps -isSimp symm_apply]
def formEquivOfSection (S : Type*) [Semiring S] [Module S M] [SMulCommClass R S M]
    [ℒ.IsSufficientlySmall D]
    (σ : Dˣ＼GL₂(𝔸 F)／ℒ.UA → GL₂(𝔸ᶠ[F])) (δ : GL₂(𝔸ᶠ[F]) → Dˣ)
    (u : GL₂(𝔸ᶠ[F]) → ℒ.UA)
    (H : ∀ g : GL₂(𝔸ᶠ[F]), σ (DoubleCoset.mk 𝓓ˣ ℒ.UA g) = ιD (δ g) * g * u g) :
    ℒ.form D M ≃ₗ[S] ((Dˣ＼GL₂(𝔸 F)／ℒ.UA) → M) where
  toFun f x := f.1 (σ x)
  map_add' f g := by ext x; simp [-MonoidHom.coe_range]
  map_smul' r f := by ext x; simp [-MonoidHom.coe_range]
  invFun f :=
    ℒ.mkFormA (fun g ↦ ℒ.χA (u g)⁻¹ • f (DoubleCoset.mk _ _ g)) (fun d g ↦ by
    congr 1
    · refine map_inv_eq_iff.mpr ?_
      refine ℒ.χA_eq_of_exists_mul_mul_eq _ _ ⟨g, δ (ιD d * g) * d, δ g, ?_⟩
      rw [map_mul, mul_assoc _ (ιD d) g, ← H, ← H]
      congr 1
      exact .symm <| (DoubleCoset.eq ..).mpr ⟨_, ⟨d, rfl⟩, 1, by simp, by simp⟩
    · congr 1; exact .symm <| (DoubleCoset.eq ..).mpr ⟨_, ⟨d, rfl⟩, 1, by simp, by simp⟩) (by
    intro g a
    rw [← mul_smul, mul_comm (ℒ.χA _) (ℒ.χA _), ← map_mul]
    congr 1
    · rw [map_inv_eq_map_comm, mul_inv_rev, inv_inv]
      refine ℒ.χA_eq_of_exists_mul_mul_eq _ _ ⟨g * a, δ g, δ (g * a), ?_⟩
      rw [← H]
      simp only [← mul_assoc, Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_cancel_right, ← H]
      congr 1
      exact (DoubleCoset.eq ..).mpr ⟨1, by simp, a, a.2, by simp⟩
    · congr 1
      exact .symm <| (DoubleCoset.eq ..).mpr ⟨1, by simp, a, a.2, by simp⟩)
  left_inv f := by
    ext v
    trans ℒ.χA (u v)⁻¹ • ℒ.χA (u v) • f.1 v
    · have := ℒ.apply_mul_eq_χA_smul _ f.2
      simp_all [mul_assoc]
    · rw [← mul_smul, ← map_mul, inv_mul_cancel]; simp
  right_inv f := by
    ext x
    have : DoubleCoset.mk 𝓓ˣ ℒ.UA (σ x) = x := by
      obtain ⟨x, rfl⟩ := Quotient.mk''_surjective x
      exact .symm <| (DoubleCoset.eq ..).mpr ⟨_, ⟨_, rfl⟩, _, by simp, H ..⟩
    trans ℒ.χA 1 • f x; swap; · simp
    dsimp
    rw [LevelStruct.mkForm_coe_toFun]
    congr 1
    · rw [map_inv_eq_map_comm, inv_one]
      exact ℒ.χA_eq_of_exists_mul_mul_eq _ _ ⟨σ x, 1, (δ (σ x)), by simp [← H, this]⟩
    · simp [this]

/-- If `U` is sufficiently small,
`S(U, χ)` is isomorphic to the finite free module with basis `Dˣ＼GL₂(𝔸ᶠ[F])／U`. -/
def formEquiv (S : Type*) [Semiring S] [Module S M] [SMulCommClass R S M]
    [ℒ.IsSufficientlySmall D] :
    ℒ.form D M ≃ₗ[S] ((Dˣ＼GL₂(𝔸 F)／ℒ.UA) → M) :=
  formEquivOfSection _ _
    DoubleCoset.σ (fun x ↦ (DoubleCoset.σLeft 𝓓ˣ ℒ.UA x).2.choose⁻¹)
      (Inv.inv ∘ DoubleCoset.σRight 𝓓ˣ ℒ.UA) fun x ↦ by
    rw [map_inv, (DoubleCoset.σLeft 𝓓ˣ ℒ.UA x).2.choose_spec]
    simp_rw [mul_assoc, eq_inv_mul_iff_mul_eq]
    simp [eq_mul_inv_iff_mul_eq, DoubleCoset.σ_spec]

open IsDedekindDomain.FiniteAdeleRing

variable (R) in
/-- A somewhat arbitrarily chosen level of an automorphic form. -/
@[simps]
def _root_.TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.levelStruct
    (f : WeightTwoAutomorphicForm F D M) :
    LevelStruct F R where
  U := MulAction.stabilizer _ f ⊓ GL2.maximalCompact _
  isCompact_U :=
    GL2.maximalCompact.isCompact.inter_left (Subgroup.isClosed_of_isOpen _ f.isOpen_stabilizer)
  isOpen_U := f.isOpen_stabilizer.inter GL2.maximalCompact.isOpen
  χ := 1
  range_unitsMap_le_ker_χ := by simp
  isOpen_ker := by simp

variable (R) in
lemma _root_.TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.mem_form
    (f : WeightTwoAutomorphicForm F D M) : f ∈ (f.levelStruct R).form D M :=
  fun a ↦ a.2.1.trans (one_smul _ _).symm

instance (f : WeightTwoAutomorphicForm F D M) : (f.levelStruct R).IsSufficientlySmall D where
  coprime_ΔIndex g := by erw [levelStruct_χ, orderOf_one]; simp

variable (D) in
/-- Actually true for all totally definite quaternion algebra `D` but the instance
is provided elsewhere. -/
abbrev IsFinite (ℒ : LevelStruct F R) : Prop := Finite (Dˣ＼GL₂(𝔸 F)／ℒ.UA)

instance (S : Type*) [Semiring S] [Module S M] [SMulCommClass R S M]
    [ℒ.IsSufficientlySmall D] [ℒ.IsFinite D] [Module.Finite S M] :
    Module.Finite S (ℒ.form D M) :=
  .of_surjective _ (ℒ.formEquiv S).symm.surjective

instance (S : Type*) [Semiring S] [Module S M] [SMulCommClass R S M]
    [ℒ.IsSufficientlySmall D] [ℒ.IsFinite D] [Module.Free S M] :
    Module.Free S (ℒ.form D M) :=
  .of_equiv (ℒ.formEquiv S).symm

instance (ℒ : LevelStruct F R) [ℒ.IsFinite D] :
    Fintype (Dˣ＼GL₂(𝔸 F)／ℒ.UA) := Fintype.ofFinite _

section TensorProduct

open TensorProduct

variable (D) in
/-- Mapping automorphic forms of a fixed level along a linear map. -/
@[simps]
def formMap {S N : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (φ : M →ₗ[S] N) :
    ℒ.form D M →ₗ[S] ℒ.form D N where
  toFun f := ⟨mapₗ φ f.1, fun u ↦ by ext; simp [Subgroup.smul_def]⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

variable (D) in
/-- Mapping automorphic forms of a fixed level along a linear equiv. -/
@[simps!]
def formCongr {S N : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (φ : M ≃ₗ[S] N) :
    ℒ.form D M ≃ₗ[S] ℒ.form D N :=
  .ofLinear (ℒ.formMap D φ) (ℒ.formMap D φ.symm) (by ext; simp) (by ext; simp)

variable (D) in
/-- `formMap` as a linear map. -/
@[simps]
def formMapₗ {S T N : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [CommRing T] [Module T N] [SMulCommClass R T N] [SMulCommClass S T N] :
    (M →ₗ[S] N) →ₗ[T] (ℒ.form D M →ₗ[S] ℒ.form D N) where
  toFun φ := ℒ.formMap D φ
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

variable (D M) in
/-- If `U` is sufficiently small, then `M ⊗ S(U, N) = S(U, M ⊗ N)`. -/
def formTensor [ℒ.IsSufficientlySmall D] [ℒ.IsFinite D]
    (S T N : Type*) [CommRing T] [Module T M] [SMulCommClass R T M]
    [AddCommGroup N] [Module R N] [CommRing S] [Module S M] [Module S N] [Algebra S T]
    [Algebra R S] [IsScalarTower R S N] [IsScalarTower R S M] [IsScalarTower S T M] :
    M ⊗[S] ℒ.form D N ≃ₗ[T] ℒ.form D (M ⊗[S] N) :=
  .ofBijective (AlgebraTensorModule.lift (ℒ.formMapₗ D ∘ₗ AlgebraTensorModule.mk _ _ _ _)) <| by
    classical
    let φ : M ⊗[S] ℒ.form D N →ₗ[S] ℒ.form D (M ⊗[S] N) :=
      AlgebraTensorModule.lift (ℒ.formMapₗ D ∘ₗ AlgebraTensorModule.mk _ _ _ _)
    suffices φ = (AlgebraTensorModule.congr (.refl _ _) (ℒ.formEquiv _) ≪≫ₗ
        TensorProduct.piRight _ _ _ _ ≪≫ₗ (ℒ.formEquiv _).symm).toLinearMap by
      change Function.Bijective φ; rw [this]; exact LinearEquiv.bijective _
    ext a f : 3
    refine (ℒ.formEquiv S).eq_symm_apply.mpr ?_
    rfl

@[simp]
lemma formTensor_tmul_apply [ℒ.IsSufficientlySmall D] [ℒ.IsFinite D]
    (S T N : Type*) [CommRing T] [Module T M] [SMulCommClass R T M]
    [AddCommGroup N] [Module R N] [CommRing S] [Module S M] [Module S N] [Algebra S T]
    [Algebra R S] [IsScalarTower R S N] [IsScalarTower R S M] [IsScalarTower S T M]
    (x : M) (f : ℒ.form D N) (g) :
    (ℒ.formTensor D M S T N (x ⊗ₜ f)).1 g = x ⊗ₜ f.1 g := rfl

variable (D M) in
/-- If `U` is sufficiently small, then `M ⊗ S(U, R) = S(U, M)`. -/
def formTensorScalar [ℒ.IsSufficientlySmall D] [ℒ.IsFinite D]
    (S : Type*) [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] :
    M ⊗[R] ℒ.form D R ≃ₗ[S] ℒ.form D M :=
  ℒ.formTensor D M R S R ≪≫ₗ ℒ.formCongr _ (AlgebraTensorModule.rid R S M)

lemma formTensorScalar_tmul [ℒ.IsSufficientlySmall D] [ℒ.IsFinite D]
    (S : Type*) [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    (x : M) (f : ℒ.form D R) :
    ℒ.formTensorScalar D M S (x ⊗ₜ f) = ℒ.formMap _ (LinearMap.toSpanSingleton _ _ x) f := rfl

@[simp]
lemma formTensorScalar_tmul_apply [ℒ.IsSufficientlySmall D] [ℒ.IsFinite D]
    (S : Type*) [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    (x : M) (f : ℒ.form D R) (g) :
    (ℒ.formTensorScalar D M S (x ⊗ₜ f)).1 g = f.1 g • x := rfl

end TensorProduct

instance : PartialOrder (LevelStruct F R) where
  le ℒ ℒ' := ∃ h : (ℒ.U ≤ ℒ'.U), ℒ.χ = ℒ'.χ.comp (Subgroup.inclusion h)
  le_refl _ := ⟨le_rfl, rfl⟩
  le_trans | ℒ₁, ℒ₂, ℒ₃, ⟨h₁₂, e₁₂⟩, ⟨h₂₃, e₂₃⟩ => ⟨h₁₂.trans h₂₃, by rw [e₁₂, e₂₃]; rfl⟩
  le_antisymm
  | ⟨U, _, _, _, _, _⟩, ⟨U', _, _, _, _, _⟩, ⟨h, e⟩, ⟨h', e'⟩ => by
    obtain rfl : U = U' := le_antisymm h h'; congr

/-- Restriction of `LevelStruct` to an open subset. -/
@[simps]
def restrict (ℒ : LevelStruct F R) (U : Subgroup GL₂(𝔸ᶠ[F]))
    (hU : IsOpen (X := GL₂(𝔸ᶠ[F])) U) (hU' : U ≤ ℒ.U) : LevelStruct F R where
  U := U
  isCompact_U := .of_isClosed_subset ℒ.isCompact_U (Subgroup.isClosed_of_isOpen _ hU) hU'
  isOpen_U := hU
  χ := ℒ.χ.comp (Subgroup.inclusion hU')
  range_unitsMap_le_ker_χ x hx := ℒ.range_unitsMap_le_ker_χ (x := Subgroup.inclusion hU' x) hx
  isOpen_ker := Subgroup.isOpen_mono (H₁ := ℒ.χ.ker.comap (Subgroup.inclusion hU'))
    le_rfl (ℒ.isOpen_ker.preimage (by exact continuous_induced_rng.mpr continuous_subtype_val))

lemma restrict_le (ℒ : LevelStruct F R) (U : Subgroup GL₂(𝔸ᶠ[F]))
    (hU : IsOpen (X := GL₂(𝔸ᶠ[F])) U) (hU' : U ≤ ℒ.U) : ℒ.restrict U hU hU' ≤ ℒ :=
  ⟨hU', rfl⟩

instance : SemilatticeInf (LevelStruct F R) where
  inf ℒ ℒ' :=
  ℒ.restrict ((MonoidHom.ker (ℒ.χ.toHomUnits.comp (Subgroup.inclusion inf_le_left) /
      ℒ'.χ.toHomUnits.comp (Subgroup.inclusion inf_le_right))).map ((ℒ.U ⊓ ℒ'.U).subtype)) (by
    refine Subgroup.isOpen_mono (H₁ := _ ⊓ _) ?_ (ℒ.isOpen_map_ker.inter ℒ'.isOpen_map_ker)
    rintro _ ⟨⟨⟨u, hu : u ∈ _⟩, hu₀, rfl⟩, ⟨v, hu'⟩, hu₀', rfl : v = u⟩
    simp_all [div_eq_one, Units.ext_iff (u := ℒ.χ.toHomUnits _)])
    ((Set.image_subset_range ..).trans (by simp +contextual [Set.subset_def]))
  inf_le_left ℒ ℒ' := ℒ.restrict_le _ _ _
  inf_le_right ℒ ℒ' := by
    refine ⟨(Set.image_subset_range ..).trans (by simp +contextual [Set.subset_def]), ?_⟩
    ext ⟨x, hx⟩
    obtain ⟨⟨h, h'⟩, e⟩ : ∃ (H : x ∈ ℒ.U ∧ x ∈ ℒ'.U), ℒ.χ ⟨x, H.1⟩ = ℒ'.χ ⟨x, H.2⟩ := by
      simpa [div_eq_one, Units.ext_iff (u := ℒ.χ.toHomUnits _)] using hx
    simpa
  le_inf ℒ ℒ₁ ℒ₂ h₁ h₂ := by
    refine ⟨fun x hx ↦ ?_, ?_⟩
    · suffices ℒ₁.χ ⟨x, h₁.1 hx⟩ = ℒ₂.χ ⟨x, h₂.1 hx⟩ by
        simpa [h₁.1 hx, h₂.1 hx, div_eq_one, Units.ext_iff (u := ℒ₁.χ.toHomUnits _)]
      exact congr($(h₁.2) ⟨x, hx⟩).symm.trans congr($(h₂.2) ⟨x, hx⟩)
    · ext x; simpa using! congr($(h₁.2) x)

@[gcongr]
lemma U_mono : Monotone fun ℒ : LevelStruct F R ↦ ℒ.U :=
  fun _ _ h ↦ h.1

@[gcongr]
lemma UA_mono : Monotone fun ℒ : LevelStruct F R ↦ ℒ.UA :=
  fun _ _ h ↦ sup_le_sup h.1 le_rfl

@[gcongr]
lemma Δ_mono (g) : Monotone fun ℒ : LevelStruct F R ↦ ℒ.Δ D g :=
  fun _ _ h ↦ inf_le_inf (UA_mono h) le_rfl

@[gcongr]
lemma map_mono {S : Type*} [CommRing S] (f : R →+* S) :
    Monotone fun ℒ : LevelStruct F R ↦ ℒ.map f :=
  fun ℒ ℒ' h ↦ ⟨h.1, by dsimp; rw [h.2]; rfl⟩

@[gcongr]
lemma form_anti : Antitone (form (F := F) (D := D) (R := R) M) :=
  fun _ _ h _ hf x ↦ h.2 ▸ hf ⟨x.1, h.1 x.2⟩

lemma inf_U_le (ℒ ℒ' : LevelStruct F R) : (ℒ ⊓ ℒ').U ≤ ℒ.U ⊓ ℒ'.U :=
  le_inf (U_mono inf_le_left) (U_mono inf_le_right)

lemma inf_U_eq_iff (ℒ ℒ' : LevelStruct F R) :
    (ℒ ⊓ ℒ').U = ℒ.U ⊓ ℒ'.U ↔
      ℒ.χ.comp (Subgroup.inclusion inf_le_left) = ℒ'.χ.comp (Subgroup.inclusion inf_le_right) := by
  refine ⟨fun H ↦ ?_, fun H ↦ (inf_U_le ..).antisymm ?_⟩
  · have := H.symm
    convert (inf_le_left : ℒ ⊓ ℒ' ≤ ℒ).2.symm.trans (inf_le_right : ℒ ⊓ ℒ' ≤ ℒ').2
  · rintro x h
    refine ⟨⟨x, h⟩, ?_, rfl⟩
    simpa [div_eq_one, Units.ext_iff] using congr($H ⟨x, h⟩)

lemma ΔIndex_mul_relIndex (ℒ ℒ' : LevelStruct F R) (h : ℒ ≤ ℒ') (g : GL₂(𝔸ᶠ[F])) :
    ℒ.ΔIndex D (DoubleCoset.mk _ _ g) * (ℒ.Δ D g).relIndex (ℒ'.Δ D g) =
      ℒ'.ΔIndex D (DoubleCoset.mk _ _ g) := by
  exact Subgroup.relIndex_mul_relIndex _ _ _ (ℒ.range_units_le_range ..)
    (inf_le_inf (sup_le_sup h.1 le_rfl) le_rfl)

lemma orderOf_χ_dvd (ℒ ℒ' : LevelStruct F R) (h : ℒ ≤ ℒ') :
    orderOf ℒ.χ ∣ orderOf ℒ'.χ := by
  refine orderOf_dvd_iff_pow_eq_one.mpr (MonoidHom.ext fun x ↦ ?_)
  simpa [h.2, -pow_orderOf_eq_one] using!
    congr($(pow_orderOf_eq_one ℒ'.χ) ⟨x.1, h.1 x.2⟩)

lemma IsSufficientlySmall.of_le (ℒ ℒ' : LevelStruct F R) (H : ℒ ≤ ℒ')
    [ℒ'.IsSufficientlySmall D] : ℒ.IsSufficientlySmall D where
  coprime_ΔIndex g := by
    obtain ⟨g, rfl⟩ := DoubleCoset.mk_surjective _ _ g
    refine .of_dvd (orderOf_χ_dvd _ _ H) ?_ (ℒ'.coprime_ΔIndex (DoubleCoset.mk 𝓓ˣ _ g))
    rw [← ΔIndex_mul_relIndex _ _ H]
    simp

instance (ℒ ℒ' : LevelStruct F R) [ℒ.IsSufficientlySmall D] : (ℒ ⊓ ℒ').IsSufficientlySmall D :=
  .of_le _ _ inf_le_left

instance (ℒ ℒ' : LevelStruct F R) [ℒ'.IsSufficientlySmall D] : (ℒ ⊓ ℒ').IsSufficientlySmall D :=
  .of_le _ _ inf_le_right

instance (ℒ ℒ' : LevelStruct F R) : ℒ.U.IsFiniteRelIndex ℒ'.U :=
  .of_isCompact ℒ.isOpen_U ℒ'.isCompact_U

lemma orderOf_map_χ_dvd
    (ℒ : LevelStruct F R) {S : Type*} [CommRing S] (f : R →+* S) :
    orderOf (ℒ.map f).χ ∣ orderOf ℒ.χ := by
  rw [orderOf_dvd_iff_pow_eq_one]
  ext x
  simp [- map_pow, ← map_pow f, ← MonoidHom.pow_apply ℒ.χ]

instance : CovariantClass GL₂(𝔸ᶠ[F]) (LevelStruct F R) (· • ·) (· ≤ ·) where
  elim g ℒ ℒ' e := by
    refine ⟨smul_mono_right _ e.1, ?_⟩
    ext a
    dsimp only [MonoidHom.coe_comp, Function.comp_apply, smul_χ_apply]
    rw [e.2]
    simp

lemma _root_.smul_le_smul_iff {G α : Type*} [Group G] [MulAction G α] [Preorder α]
    [CovariantClass G α (· • ·) (· ≤ ·)] {g : G} {a b : α} : g • a ≤ g • b ↔ a ≤ b :=
  ⟨fun h ↦ by simpa using smul_mono_right g⁻¹ h, fun h ↦ smul_mono_right g h⟩

lemma _root_.inv_smul_le_iff {G α : Type*} [Group G] [MulAction G α] [Preorder α]
    [CovariantClass G α (· • ·) (· ≤ ·)] {g : G} {a b : α} : g⁻¹ • a ≤ b ↔ a ≤ g • b := by
  rw [← smul_le_smul_iff (g := g)]
  simp

lemma _root_.smul_inf {G α : Type*} [Group G] [MulAction G α] [SemilatticeInf α]
    [CovariantClass G α (· • ·) (· ≤ ·)] (g : G) (a b : α) : g • (a ⊓ b) = g • a ⊓ g • b := by
  refine (smul_inf_le ..).antisymm ?_
  grw [← inv_smul_le_iff, smul_inf_le]
  simp

instance (ℒ : LevelStruct F R) [ℒ.IsSufficientlySmall D] {S : Type*} [CommRing S] (f : R →+* S) :
    (ℒ.map f).IsSufficientlySmall D where
  coprime_ΔIndex g := .of_dvd_left (ℒ.orderOf_map_χ_dvd f) (ℒ.coprime_ΔIndex g)

lemma Subgroup.isFiniteRelIndex_inf_inf
    {G : Type*} [Group G] (H₁ H₂ K : Subgroup G) [H₁.IsFiniteRelIndex H₂]
    (hK : K ≤ Subgroup.centralizer H₂) :
    (H₁ ⊔ K).IsFiniteRelIndex (H₂ ⊔ K) := by
  let f : H₂ ⧸ H₁.subgroupOf H₂ → ↑(H₂ ⊔ K) ⧸ (H₁ ⊔ K).subgroupOf (H₂ ⊔ K) :=
    Quotient.map (Subgroup.inclusion le_sup_left) (fun a b e ↦
      QuotientGroup.leftRel_apply.mpr (le_sup_left (a := H₁) (QuotientGroup.leftRel_apply.mp e:)))
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨a, rfl⟩ := Subgroup.prodToSupOfRight_surjective _ _ hK a
    refine ⟨a.1, ?_⟩
    simpa [f, QuotientGroup.eq] using le_sup_right (b := K) a.2.2
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, Subgroup.finiteIndex_iff_finite_quotient]
  exact .of_surjective _ hf

instance (ℒ ℒ' : LevelStruct F R) : ℒ.UA.IsFiniteRelIndex ℒ'.UA :=
  Subgroup.isFiniteRelIndex_inf_inf _ _ _
    (range_unitsMap_finiteAdeleRing_le_center.trans (Subgroup.center_le_centralizer _))

/-- `(U, χ)` is normal in `(U', χ')` if `U ≤ U'` is normal and `χ'|_U = χ`. -/
class Normal (ℒ ℒ' : LevelStruct F R) : Prop extends (ℒ.U.subgroupOf ℒ'.U).Normal where
  le : ℒ ≤ ℒ'

instance (ℒ : LevelStruct F R) : ℒ.Normal ℒ where
  le := le_rfl
  toNormal := by simp

lemma le_normalizer (ℒ ℒ' : LevelStruct F R) [ℒ.Normal ℒ'] :
    ℒ'.U ≤ Subgroup.normalizer ℒ.U :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (U_mono Normal.le)).mp inferInstance

instance {ℒ ℒ' : LevelStruct F R} [ℒ.Normal ℒ'] : DistribMulAction ℒ'.U (ℒ.form D M) where
  smul u m := ⟨u • m, by
    intro v
    ext x
    have H₁ := congr($(m.2 ⟨_, ((inv_mem (le_normalizer ℒ ℒ' u.2)) _).mp v.2⟩) (x * u))
    have H₂ : ℒ'.χ ⟨(↑u)⁻¹ * ↑v * ↑u, mul_mem (mul_mem (inv_mem u.2)
      (Normal.le.1 v.2)) u.2⟩ = ℒ'.χ (Subgroup.inclusion Normal.le.1 v) := by
      change ℒ'.χ (u⁻¹ * (Subgroup.inclusion Normal.le.1 v) * u) = _
      simp_rw [map_mul, mul_right_comm _ _ (ℒ'.χ u), ← map_mul, inv_mul_cancel, one_mul]
    simp_all [Subgroup.smul_def, mul_assoc, (Normal.le (self := ‹_›)).2]⟩
  mul_smul x y m := Subtype.ext (mul_smul x y m.1)
  one_smul m := Subtype.ext (one_smul _ m.1)
  smul_zero x := Subtype.ext (smul_zero x)
  smul_add x m n := Subtype.ext (smul_add x m.1 n.1)

end LevelStruct

open IsDedekindDomain.FiniteAdeleRing

variable (F R) in
/-- A way to construct `LevelStruct` via a family of local level structs on finitely many finite
places. -/
structure LocalLevelStruct where
  /-- The set of finite places. -/
  S : Finset ℙ(F)
  /-- The open compacts at the given finite places. -/
  US : Π v : ℙ(F), Subgroup GL₂(v.adicCompletion F)
  isCompact_US_of_mem : ∀ v ∈ S, IsCompact (X := GL₂(v.adicCompletion F)) (US v)
  isOpen_US_of_mem: ∀ v ∈ S, IsOpen (X := GL₂(v.adicCompletion F)) (US v)
  US_eq_of_notMem : ∀ v ∉ S, US v = GL2.localFullLevel v
  /-- The characters at the given finite places. -/
  χ : Π v : ℙ(F), US v →* R
  χ_eq_of_notMem : ∀ v ∉ S, χ v = 1
  range_unitsMap_le_ker_χ : ∀ v ∈ S, (Units.map (algebraMap (v.adicCompletion F)
      M₂(v.adicCompletion F)).toMonoidHom).range.subgroupOf (US v) ≤ (χ v).ker
  isOpen_ker_χ_of_mem : ∀ v ∈ S, IsOpen ((χ v).ker : Set (US v))

namespace LocalLevelStruct

variable (ℒ : LocalLevelStruct F R) (v : ℙ(F))

lemma isOpen_US : IsOpen (X := GL₂(v.adicCompletion F)) (ℒ.US v) := by
  if h : v ∈ ℒ.S then exact ℒ.isOpen_US_of_mem _ h else
    exact ℒ.US_eq_of_notMem _ h ▸ GL2.localFullLevel.isOpen v

lemma isCompact_US : IsCompact (X := GL₂(v.adicCompletion F)) (ℒ.US v) := by
  if h : v ∈ ℒ.S then exact ℒ.isCompact_US_of_mem _ h else
    exact ℒ.US_eq_of_notMem _ h ▸ GL2.localFullLevel.isCompact v

/-- The `LevelStruct` constructed via a `LocalLevelStruct`. -/
@[simps -isSimp]
def toStruct : LevelStruct F R where
  U :=
  { carrier := { x | ∀ v, GL2.toAdicCompletion v x ∈ ℒ.US v }
    mul_mem' := by simp +contextual only [Set.mem_setOf_eq, map_mul, mul_mem, implies_true]
    one_mem' := by dsimp; simp only [map_one, one_mem, implies_true]
    inv_mem' := by dsimp; simp only [map_inv, inv_mem_iff, imp_self, implies_true] }
  isCompact_U := by
    classical
    rw [← GL2.restrictedProduct.toHomeomorph.symm.isCompact_preimage]
    convert! RestrictedProduct.isCompact_forall_mem_of_eventually_subset ?_ ℒ.US
      ℒ.isCompact_US ?_
    · exact fun v ↦ M2.units_localFullLevel v ▸ GL2.localFullLevel.isOpen v
    · exact Filter.eventually_of_mem ℒ.S.finite_toSet.compl_mem_cofinite fun v hv ↦
        M2.units_localFullLevel v ▸ (ℒ.US_eq_of_notMem v hv).le
  isOpen_U := by
    classical
    rw [← GL2.restrictedProduct.toHomeomorph.symm.isOpen_preimage]
    convert! RestrictedProduct.isOpen_forall_mem_of_eventually_eq ?_ ℒ.US
      ℒ.isOpen_US ?_ using 1
    · exact fun v ↦ M2.units_localFullLevel v ▸ GL2.localFullLevel.isOpen v
    · exact Filter.eventually_of_mem ℒ.S.finite_toSet.compl_mem_cofinite fun v hv ↦
        M2.units_localFullLevel v ▸ (ℒ.US_eq_of_notMem v hv).symm
  χ := ∏ v ∈ ℒ.S, (ℒ.χ v).comp (((GL2.toAdicCompletion v).comp
    (Subgroup.subtype _)).codRestrict _ (by rintro ⟨x, hx⟩; exact hx v))
  range_unitsMap_le_ker_χ := by
    rintro ⟨_, hg⟩ ⟨g, rfl⟩
    simp only [MonoidHom.mem_ker, MonoidHom.finsetProd_apply, MonoidHom.coe_comp,
      Function.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_subtype]
    refine Finset.prod_eq_one fun v hv ↦ ℒ.range_unitsMap_le_ker_χ v hv
      ⟨g.map (FiniteAdeleRing.toAdicCompletion v).toMonoidHom, ?_⟩
    ext1
    simp [GL2.toAdicCompletion, Matrix.algebraMap_eq_diagonal]
  isOpen_ker := by
    let : TopologicalSpace R := ⊥
    have : DiscreteTopology R := ⟨rfl⟩
    have := ℒ.isOpen_ker_χ_of_mem
    simp only [← MonoidHom.continuous_iff_isOpen_ker] at this ⊢
    eta_expand
    simp only [MonoidHom.finsetProd_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.codRestrict_apply, Subgroup.coe_subtype]
    refine continuous_finsetProd _ fun v hv ↦ (this v hv).comp ?_
    exact continuous_induced_rng.mpr
      ((GL2.continuous_toAdicCompletion _).comp continuous_subtype_val)

open scoped Classical in
/-- The inclusion of the local open subgroup into the global one. -/
noncomputable
def incl : ℒ.US v →* ℒ.toStruct.U :=
  ((GL2.finiteAdeleIncl v).comp (Subgroup.subtype _)).codRestrict _ <| by
  rintro ⟨x, hx⟩ w
  obtain rfl | h := eq_or_ne w v
  · simpa
  · simp [h]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma χ_incl (x) : ℒ.toStruct.χ (ℒ.incl v x) = ℒ.χ v x := by
  simp only [toStruct_χ, MonoidHom.finsetProd_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.codRestrict_apply]
  refine (Finset.prod_eq_single v ?_ ?_).trans ?_
  · intro w hw hvw
    convert (ℒ.χ w).map_one
    exact GL2.toAdicCompletion_finiteAdeleIncl_of_ne _ _ _ hvw
  · intro hv; simp [ℒ.χ_eq_of_notMem v hv]
  · congr 1
    ext1
    exact GL2.toAdicCompletion_finiteAdeleIncl_same _ _

-- Issues with `RingHom.toMonoidHom_eq_coe` being simp.
attribute [nolint simpNF]
  trivial_central_char
  trivial_central_char'
  trivial_central_char_right
  unitsMap_smul
  unitsMap_adicCompletion_smul
  LevelStruct.χA_inclusion_left
  LevelStruct.χA_inclusion_right
  LevelStruct.smul_χ_apply
  LevelStruct.formEquivOfSection_apply


end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LocalLevelStruct
