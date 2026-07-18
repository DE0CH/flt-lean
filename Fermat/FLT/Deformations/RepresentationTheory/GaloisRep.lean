/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import Fermat.FLT.Deformations.RepresentationTheory.Etale
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
-- `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`, used to state the
-- cyclotomic-at-Frobenius leaf below in THIS module's elaboration context
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Fermat.FLT.DedekindDomain.AdicValuation
-- `mem_completionIdeal_iff`, used in the 3-is-a-unit step of the
-- Frobenius/roots-of-unity assembly
-- `HasEnoughRootsOfUnity (AlgebraicClosure ℚ) (3 ^ i)` instances for the
-- cyclotomic-character derivation

/-!
# Galois representations

The type `GaloisRep K A M` of `A`-linear continuous representations of the
absolute Galois group of a field `K` on an `A`-module `M`, together with the
basic API (kernel, etc.).
-/

@[expose] public section

open NumberField

universe uK

variable {K : Type uK} {L : Type*} [Field K] [Field L]
variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {B : Type*} [CommRing B] [TopologicalSpace B]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {n : Type*} [Fintype n] [DecidableEq n]

variable [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v

variable (K A M) in
/-- `GaloisRep K A M` are the `A`-linear galois reps of a field `K` on the `A`-module `M`. -/
def GaloisRep :=
  letI := moduleTopology A (Module.End A M)
  Γ K →ₜ* Module.End A M

noncomputable instance : FunLike (GaloisRep K A M) (Γ K) (Module.End A M) :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.instFunLike

instance : MonoidHomClass (GaloisRep K A M) (Γ K) (Module.End A M) :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.instMonoidHomClass

omit [NumberField K] in
@[ext]
lemma GaloisRep.ext {ρ ρ' : GaloisRep K A M} (H : ∀ σ, ρ σ = ρ' σ) : ρ = ρ' :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.ext H

/-- The kernel of a galois rep. -/
noncomputable nonrec
abbrev GaloisRep.ker (ρ : GaloisRep K A M) : Subgroup (Γ K) :=
  letI := moduleTopology A (Module.End A M)
  ρ.ker

/-- A field extension induces a map between galois reps.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures. -/
noncomputable
def GaloisRep.map (ρ : GaloisRep K A M) (f : K →+* L) : GaloisRep L A M :=
  letI := moduleTopology A (Module.End A M)
  ρ.comp (Field.absoluteGaloisGroup.map f)

-- remark: `.toMonoidHom` added in bump to v4.30.0-rc1

variable (K A n) in
/-- A framed galois rep is a galois rep with a distinguished basis.
We implement it by via a galois rep on `Aⁿ`. -/
abbrev FramedGaloisRep := GaloisRep K A (n → A)


/-- We can conjugate a galois rep by a linear isomorphism on the space. -/
noncomputable
def GaloisRep.conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) : GaloisRep K A N :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology A (Module.End A N)
  let e' : Module.End A M ≃A[A] Module.End A N :=
    .ofIsModuleTopology <| LinearEquiv.conjAlgEquiv A e
  e'.toContinuousAlgHom.toContinuousMonoidHom.comp ρ

omit [NumberField K] in
lemma GaloisRep.conj_apply (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (σ : Γ K) :
    ρ.conj e σ = e.conj (ρ σ) := rfl







-- **TODO** this should be frame_unframe maybe?


variable [IsTopologicalRing A]







/-- The determinant of a galois rep. -/
noncomputable
def GaloisRep.det (ρ : GaloisRep K A M) : Γ K →ₜ* A :=
  letI := moduleTopology A (Module.End A M)
  .comp ⟨LinearMap.det, IsModuleTopology.continuous_det⟩ ρ

open TensorProduct in
variable (B) in
/-- Make a `A`-linear galois rep on `M` into a `B`-linear rep on `B ⊗ M`. -/
noncomputable
def GaloisRep.baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) : GaloisRep K B (B ⊗[A] M) :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology B (Module.End B (B ⊗[A] M))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite B (Module.End B (B ⊗[A] M))⟩
  letI := IsModuleTopology.toContinuousAdd B (Module.End B (B ⊗[A] M))
  let F : Module.End A M →+* Module.End B (B ⊗[A] M) := Module.End.baseChangeHom A B M
  have : Continuous F := by
    have : IsTopologicalSemiring (Module.End B (B ⊗[A] M)) := ⟨⟩
    have : Continuous (algebraMap A (Module.End B (B ⊗[A] M))) := by
      rw [IsScalarTower.algebraMap_eq A B, RingHom.coe_comp]
      exact (continuous_algebraMap _ _).comp (continuous_algebraMap _ _)
    exact IsModuleTopology.continuous_of_ringHom (R := A) F (by simpa [F])
  .comp ⟨F, this⟩ ρ

omit [IsTopologicalRing A] [NumberField K] in
open TensorProduct in
@[simp]
lemma GaloisRep.baseChange_tmul [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) (σ : Γ K) (r : B) (x : M) :
    ρ.baseChange B σ (r ⊗ₜ x) = r ⊗ₜ (ρ σ x) := rfl

omit [IsTopologicalRing A] [NumberField K] in
lemma GaloisRep.ker_baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) :
    ρ.ker ≤ (ρ.baseChange B).ker := by
  intro _; simp +contextual [baseChange]




omit [NumberField K] in
variable (B) in






/-- Given a (global) galois rep, this is the local galois rep at a finite prime `v`.
Note: this fixes an arbitrary embedding `Kᵃˡᵍ → Kᵥᵃˡᵍ`, or equivalently,
an arbitrary choice of valuation on `Kᵃˡᵍ` extending `v`. -/
noncomputable
abbrev GaloisRep.toLocal (ρ : GaloisRep K A M) (v : Ω K) : GaloisRep (v.adicCompletion K) A M :=
  ρ.map (algebraMap _ _)

omit [IsTopologicalRing A] in
/-- `toLocal` evaluates by precomposition with the induced map of absolute
Galois groups (an exposed `rfl`-lemma: downstream modules cannot unfold the
definition through the module-system export). -/
lemma GaloisRep.toLocal_apply (ρ : GaloisRep K A M) (v : Ω K)
    (σ : Γ (v.adicCompletion K)) :
    ρ.toLocal v σ =
      ρ (Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) σ) :=
  rfl

universe v u
variable {R : Type u} [CommRing R]

/-- The class of galois reps unramified at `v`. -/
class GaloisRep.IsUnramifiedAt (ρ : GaloisRep K A M) (v : Ω K) : Prop where
  localInertiaGroup_le :
    letI := moduleTopology A (Module.End A M)
    localInertiaGroup v ≤ (ρ.toLocal v).ker


instance [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsUnramifiedAt v] :
    (ρ.baseChange B).IsUnramifiedAt v :=
  ⟨(GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)).trans
    (((ρ.toLocal v).ker_baseChange (B := B)))⟩

variable [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]

/-- The characteristic polynomial of the frobenious conjugacy class at `v` under `ρ`. -/
noncomputable
def GaloisRep.charFrob (ρ : GaloisRep K A M) : Polynomial A := (ρ.toLocal v Frobᵥ).charpoly

-- shortcut instance for next theorem: needed after mathlib #34045
noncomputable instance : CommRing Kᵥ := inferInstance


section Flat

set_option linter.unusedVariables false in
/-- The underlying space of a galois rep. This is a type class synonym that allows `G` to act
on it via `ρ`. -/
@[nolint unusedArguments]
def GaloisRep.Space (ρ : GaloisRep K A M) : Type _ := M

instance (ρ : GaloisRep K A M) : AddCommGroup ρ.Space := inferInstanceAs (AddCommGroup M)

-- dirty hack
set_option backward.isDefEq.respectTransparency false in
noncomputable instance (ρ : GaloisRep K A M) : DistribMulAction (Γ K) ρ.Space where
  smul g v := ρ g v
  one_smul b := by unfold HSMul.hSMul; simp [instHSMul]
  mul_smul := by unfold HSMul.hSMul; simp [instHSMul]
  smul_zero := by unfold HSMul.hSMul; simp [instHSMul]
  smul_add := by unfold HSMul.hSMul; simp [instHSMul]

open TensorProduct in
/-- A galois rep `ρ : Γ K → Aut_A(M)` has a flat prolongation at `v` if `M` (when viewed as a
`Γ Kᵥ`) module is isomorphic to the geometric points of a finite etale hopf algebra over `Kᵥ`, and
there exists an finite flat hopf algebra over `𝒪ᵥ` whose generic fiber is isomorphic to it.
In particular this requires `M` (and by extension `A`) to have finite cardinality.

Note that the `Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G)` condition is redundant because `Kᵥ` has char 0
and all finite flat group schemes over `Kᵥ` are etale.
But this would be hard to prove in general, while in the applications they would come from
finite groups so it would be easy to show that they are etale. If this turns out to not be the case,
we can remove this condition and state the aforementioned result as a sorry.
-/
def GaloisRep.HasFlatProlongationAt (ρ : GaloisRep K A M) : Prop :=
  ∃ (G : Type uK) (_ : CommRing G) (_ : HopfAlgebra 𝒪ᵥ G)
    (_ : Module.Flat 𝒪ᵥ G) (_ : Module.Finite 𝒪ᵥ G) (_ : Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G))
    (f : Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Kᵥᵃˡᵍ) →+[Γ Kᵥ] (ρ.toLocal v).Space),
    Function.Bijective f

omit [IsTopologicalRing A] [Module.Free A M] [Module.Finite A M] in
/-- `HasFlatProlongationAt` transports along a `Γ Kᵥ`-equivariant additive
isomorphism of underlying spaces: the Hopf-algebra witness is reused verbatim
and the geometric-points identification is composed with the isomorphism. -/
lemma GaloisRep.HasFlatProlongationAt.of_equiv {A' : Type*} [CommRing A']
    [TopologicalSpace A'] {M' : Type*} [AddCommGroup M'] [Module A' M']
    {ρ₁ : GaloisRep K A M} {ρ₂ : GaloisRep K A' M'}
    (h : ρ₁.HasFlatProlongationAt v)
    (e : (ρ₁.toLocal v).Space ≃+ (ρ₂.toLocal v).Space)
    (he : ∀ (g : Γ Kᵥ) (x : (ρ₁.toLocal v).Space), e (g • x) = g • e x) :
    ρ₂.HasFlatProlongationAt v := by
  obtain ⟨G, i1, i2, i3, i4, i5, f, hbij⟩ := h
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  exact ⟨G, i1, i2, i3, i4, i5,
    { toFun := fun x => e (f x)
      map_smul' := fun g x => by
        show e (f (g • x)) = g • e (f x)
        rw [map_smul f g x, he]
      map_zero' := by simp
      map_add' := fun a b => by simp },
    e.bijective.comp hbij⟩

set_option warn.sorry false in
/-- **The residue cardinality at the `p`-place is `p`** (sorry node): the
maximal ideal of the integral closure of `𝒪ᵥ` in `Kᵥᵃˡᵍ` lies over the
maximal ideal of `𝒪ᵥ`, whose residue field is `𝓞_ℚ ⧸ (p) ≅ ZMod p` through
`ResidueFieldEquivCompletionResidueField`. This is the `q` of the
`IsArithFrobAt` specification. -/
theorem natCard_residue_under_padicPlace
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    Nat.card ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hp.toHeightOneSpectrumRingOfIntegersRat) ⧸
      ((IsLocalRing.maximalIdeal (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat)))).under
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))) = p :=
  sorry

set_option warn.sorry false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The arithmetic Frobenius raises `3`-power roots of unity to the
`p`-th power** (sorry node — the unramified local content): at a prime
`p ∉ {2, 3}`, the `3`-power roots of unity are unramified, the arithmetic
Frobenius reduces to `x ↦ x^p` on the residue field, and roots of unity of
order coprime to `p` inject into the residue field, so the action is
exactly `ζ ↦ ζ^p`. Stated in the `modularCyclotomicCharacter.unique`
hypothesis shape. -/
theorem adicArithFrob_rootsOfUnity_pow
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (n : ℕ) :
    ∀ t ∈ rootsOfUnity (3 ^ n) (AlgebraicClosure ℚ),
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hp.toHeightOneSpectrumRingOfIntegersRat)).toRingEquiv) t =
        t ^ ((p : ZMod (3 ^ n)).val) := by
  intro t ht
  classical
  -- the `q` of the Frobenius specification is `p` (the residue cardinality)
  have hq := natCard_residue_under_padicPlace p hp hp5
  set v := hp.toHeightOneSpectrumRingOfIntegersRat with hv
  set f := algebraMap ℚ
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) with hf
  -- the root of unity, its power identity, and its image under the chosen
  -- embedding of algebraic closures
  have htL : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (3 ^ n)
      = 1 := by
    have h1 := (mem_rootsOfUnity _ _).mp ht
    calc ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (3 ^ n)
        = ((t ^ (3 ^ n) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
          push_cast; rfl
      _ = 1 := by rw [h1]; rfl
  set ζ : AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) :=
    AlgebraicClosure.map f ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    with hζdef
  have hζpow : ζ ^ (3 ^ n) = 1 := by
    rw [hζdef, ← map_pow, htL, map_one]
  -- the image is integral over the completion integers (it kills `X^{3ⁿ}-1`)
  have hint : IsIntegral
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v) ζ := by
    refine ⟨Polynomial.X ^ (3 ^ n) - 1, ?_, ?_⟩
    · have := Polynomial.monic_X_pow_sub_C
        (R := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (1 : _) (n := 3 ^ n) (by positivity)
      simpa [Polynomial.C_1] using this
    · simp [Polynomial.eval₂_sub, hζpow]
  set ζ' : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) :=
    ⟨ζ, hint⟩ with hζ'def
  have hζ'pow : ζ' ^ (3 ^ n) = 1 := by
    apply Subtype.ext
    push_cast [hζ'def]
    exact hζpow
  -- `3` is a unit at the `p`-place (`p ≠ 3`), so `3ⁿ` avoids the maximal ideal
  have h3notin : ((3 : ℕ) ^ n : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) ∉
      IsLocalRing.maximalIdeal _ := by
    -- `3 ∉ (p)`, so `3` is a unit in `𝒪ᵥ`, hence in the integral closure
    have h3compl : (3 : NumberField.RingOfIntegers ℚ) ∈
        v.asIdeal.primeCompl := by
      intro hmem
      have hdvd := (Nat.Prime.mem_toHeightOneSpectrumRingOfIntegersRat_asIdeal
        hp _).mp hmem
      rw [map_ofNat] at hdvd
      have hle := Int.le_of_dvd (by norm_num) hdvd
      omega
    have hint1 : IsDedekindDomain.HeightOneSpectrum.intValuation v
        (3 : NumberField.RingOfIntegers ℚ) = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl
        v _).mpr h3compl
    -- the completed valuation of `3`, assembled in mathlib's own coercion
    -- spelling (the MazurTorsion pattern)
    have hK := (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
        (v := v) (K := ℚ) (3 : NumberField.RingOfIntegers ℚ)).trans
      ((IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap
        (v := v) (K := ℚ) (3 : NumberField.RingOfIntegers ℚ)).trans hint1)
    have hunit : IsUnit ((3 : ℕ) :
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v) := by
      by_contra hnu
      have hmem := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have hlt := (IsDedekindDomain.HeightOneSpectrum.mem_completionIdeal_iff
        (K := ℚ) (v := v) _).mp hmem
      open scoped algebraMap in
      have hlt' : Valued.v (((3 : NumberField.RingOfIntegers ℚ)) :
          IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) < 1 := by
        convert hlt using 2
        -- residual cast equation: the record-built `𝓞ℚ`-coercion of `3` into
        -- the one-field-structure completion vs the subtype-val of the
        -- `ℕ`-cast — `{toCompletion := ↑((WithVal.equiv _).symm ↑3)} = ↑↑3`
        sorry
      -- residual: `hK`'s and `hlt'`'s `↑3` differ in an invisible instance
      -- path (class-6); the contradiction `1 < 1` is one bridge away
      sorry
    have hunitIC : IsUnit (((3 : ℕ) ^ n) : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))) := by
      have h1 := hunit.map (algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
        (IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))))
      rw [map_natCast] at h1
      have := h1.pow n
      push_cast
      exact this
    intro hmem
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) (by
      push_cast at hunitIC ⊢
      exact hunitIC)
  -- the Frobenius specification on the integral closure
  have hfrob := AlgHom.IsArithFrobAt.apply_of_pow_eq_one
    (Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob (v := v))
    hζ'pow (by exact_mod_cast h3notin)
  rw [hq] at hfrob
  -- read the specification off in `Kᵥᵃˡᵍ`
  have hfrobK : Field.AbsoluteGaloisGroup.adicArithFrob v ζ = ζ ^ p := by
    have h1 := hfrob
    rw [MulSemiringAction.toAlgHom_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [IntegralClosure.coe_smul] at h2
    have h3 : ((⟨ζ, hint⟩ : IntegralClosure _ _) ^ p).1 = ζ ^ p :=
      SubmonoidClass.coe_pow _ _
    simpa [hζ'def, AlgEquiv.smul_def] using h2.trans h3
  -- globalize through the chosen embedding, which is injective
  have hsq := Field.absoluteGaloisGroup.lift_map f
    (Field.AbsoluteGaloisGroup.adicArithFrob v)
    ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
  have hmain : (Field.absoluteGaloisGroup.map f
      (Field.AbsoluteGaloisGroup.adicArithFrob v))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ p := by
    apply (AlgebraicClosure.map f).injective
    rw [hsq, map_pow]
    exact hfrobK
  -- the goal's `toRingEquiv` application is the automorphism application
  show (Field.absoluteGaloisGroup.map f
      (Field.AbsoluteGaloisGroup.adicArithFrob v))
      ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
  rw [hmain]
  -- the exponent-mod juggle: `t^p = t^(p mod 3ⁿ)` since `t^{3ⁿ} = 1`
  haveI : NeZero (3 ^ n) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hval : ((p : ZMod (3 ^ n))).val = p % 3 ^ n := ZMod.val_natCast _ p
  conv_lhs => rw [show p = 3 ^ n * (p / 3 ^ n) + p % 3 ^ n from
    (Nat.div_add_mod p (3 ^ n)).symm]
  rw [pow_add, pow_mul, htL, one_pow, one_mul, hval]

/-- **The 3-adic cyclotomic character at an arithmetic Frobenius** (DERIVED
2026-07-18 from the roots-of-unity action leaf, by `3`-adic continuity:
`PadicInt.ext_of_toZModPow` reduces the identity to every level `3ⁿ`, where
`cyclotomicCharacter.toZModPow` and `modularCyclotomicCharacter.unique`
identify the character value with `p` from the action). Stated in THIS
module so that the Frobenius-image element elaborates identically to
`GaloisRep.toLocal_apply`'s right-hand side (the module-system's opaque
exports make cross-module respellings non-defeq). -/
theorem cyclotomicCharacter_adicArithFrob {R : Type*} [CommRing R]
    [Algebra ℤ_[3] R]
    (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    algebraMap ℤ_[3] R
      (cyclotomicCharacter (AlgebraicClosure ℚ) 3
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
            hp.toHeightOneSpectrumRingOfIntegersRat))
          (Field.AbsoluteGaloisGroup.adicArithFrob
            hp.toHeightOneSpectrumRingOfIntegersRat)).toRingEquiv)) =
      (p : R) := by
  have hval : ((cyclotomicCharacter (AlgebraicClosure ℚ) 3
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hp.toHeightOneSpectrumRingOfIntegersRat))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hp.toHeightOneSpectrumRingOfIntegersRat)).toRingEquiv) :
      ℤ_[3]ˣ) : ℤ_[3]) = ((p : ℕ) : ℤ_[3]) := by
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    rw [map_natCast, cyclotomicCharacter.toZModPow]
    exact (modularCyclotomicCharacter.unique
      (hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ)
        (3 ^ n))
      _ _ (adicArithFrob_rootsOfUnity_pow p hp hp5 n)).symm
  rw [hval, map_natCast]

/-- A galois rep `ρ : Γ K → Aut_A(M)` is flat at `v` if `A/I ⊗ M` has a flat prolongation at `v`
for all open ideals `I`. -/
class GaloisRep.IsFlatAt [IsLocalRing A] (ρ : GaloisRep K A M) : Prop where
  cond : ∀ (I : Ideal A), IsOpen (I : Set A) →
    (ρ.baseChange (A ⧸ I)).HasFlatProlongationAt v

end Flat

/-- A Galois representation is a representation (note that we
are forgetting topological information here). -/
def GaloisRep.toRepresentation (ρ : GaloisRep K A M) : Representation A (Γ K) M :=
  letI := moduleTopology A (Module.End A M) -- ?!
  ρ.toMonoidHom

/-- Irreducibility of a Galois representation over a field. -/
def GaloisRep.IsIrreducible {k : Type*} [Field k] [TopologicalSpace k] [Module k M]
    (ρ : GaloisRep K k M) : Prop := ρ.toRepresentation.IsIrreducible
