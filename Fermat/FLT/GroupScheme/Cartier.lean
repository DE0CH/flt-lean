/-
Cartier.lean — own work for the Fermat project.

# Cartier's theorem: a finite commutative Hopf algebra in characteristic zero is reduced

Let `K` be a field of characteristic zero and `A` a commutative Hopf
algebra over `K` which is finite-dimensional as a `K`-vector space.
Then `A` is REDUCED — equivalently, the finite group scheme `Spec A`
over `K` is étale.  This is Cartier's theorem (SGA 3, VI_B 1.6.1;
Oort, *Commutative Group Schemes*; Waterhouse, *Introduction to Affine
Group Schemes*, Thm. 11.4; Tate, *Finite flat group schemes*, §3.7 in
Cornell–Silverman–Stevens).

## The proof

Write `ε` for the counit and `I = ker ε` for the augmentation ideal.

1. **The heart: `I = I²`** (`isIdempotentElem_ker_counit`).  Suppose not.
   Then there is a `K`-linear functional `D : A →ₗ[K] K` killing `I²`
   and `1`, with `D x = 1` for some `x ∈ I`; such a `D` is a POINT
   DERIVATION, `D (ab) = ε a · D b + D a · ε b`.  Translating it by the
   comultiplication produces a genuine `K`-derivation `∂` of `A`:
   concretely `a + ∂ a · t` is the image of `a` under the algebra map
   `A ⟶ A ⊗ A ⟶ A[t]/(t²)` built from `Δ` and `a ↦ ε a + D a · t`, and
   `∂` is a derivation *because that composite is an algebra map*
   (`derivationOfPointDerivation`).  Its two defining properties are
   `ε ∘ ∂ = D` and the Leibniz rule.

   Now put `J = (x)` and `u = ∂ x`, so `ε x = 0` and `ε u = 1`.  A
   derivation lowers the `J`-adic filtration by one step
   (`derivation_mem_pow`), hence `∂ⁿ (Jᵐ) ⊆ J` whenever `m > n`; and a
   direct induction (`derivation_iterate_pow_mul`) gives
   `∂ⁿ (xⁿ · y) ≡ n! · uⁿ · y  (mod J)`.  Applying `ε`:

   * `ε (∂ⁿ (xᵐ)) = 0` for `m > n`;
   * `ε (∂ⁿ (xⁿ)) = n!`, which is NONZERO because `char K = 0`.

   This triangular pairing between the functionals `ε ∘ ∂ⁿ` and the
   powers `xᵐ` forces `(xᵐ)_{m : ℕ}` to be `K`-linearly independent
   (`linearIndependent_pow_of_pointDerivation`), contradicting
   `Module.Finite K A`.  **This is where characteristic zero enters, and
   it is the only place**: in characteristic `p` the pairing degenerates
   at `n = p`, and indeed `k[t]/(tᵖ)` with `t` primitive — the Hopf
   algebra of `α_p ⊆ 𝔾_a` — is a finite non-reduced commutative Hopf
   algebra.

2. **`I = I²` ⟹ `Ω[A⁄K] = 0`.**  This is Fontaine's translation
   isomorphism `Ω[A⁄K] ≅ A ⊗_K (I/I²)`, already proven sorry-free in
   `Fermat/FLT/GroupScheme/HopfKaehler.lean`; it is the only step that
   uses the antipode.

3. **`Ω[A⁄K] = 0` ⟹ `A` reduced.**  `Subsingleton Ω[A⁄K]` is by
   definition `Algebra.FormallyUnramified K A`, and mathlib's
   `Algebra.FormallyUnramified.isReduced_of_field` concludes.
-/
module

public import Fermat.FLT.GroupScheme.HopfKaehler
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

open scoped TensorProduct
open Bialgebra HopfAlgebra Coalgebra

noncomputable section

namespace CartierTheorem

/-! ### A derivation lowers an adic filtration by one step -/

section DerivationFiltration

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- A derivation carries `J ^ (k + 1)` into `J ^ k`. -/
theorem derivation_mem_pow (D : Derivation K A A) (J : Ideal A) (k : ℕ) :
    ∀ a ∈ J ^ (k + 1), D a ∈ J ^ k := by
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro m hm n hn
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      refine add_mem ?_ (Ideal.mul_mem_right _ _ hn)
      rw [pow_succ']
      exact Ideal.mul_mem_mul hm (ih n hn)
    · intro y z hy hz
      rw [map_add]
      exact add_mem hy hz

/-- Iterating: `∂ⁿ` carries `J ^ (n + 1)` into `J`. -/
theorem derivation_iterate_mem (D : Derivation K A A) (J : Ideal A) (n : ℕ) :
    ∀ a ∈ J ^ (n + 1), ((D.toLinearMap : Module.End K A) ^ n) a ∈ J := by
  induction n with
  | zero => intro a ha; simpa using ha
  | succ n ih =>
    intro a ha
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (derivation_mem_pow D J (n + 1) a ha)

/-- **The diagonal computation.** Modulo the ideal `(x)`, the `n`-th iterate of a
derivation `∂` applied to `xⁿ · y` is `n! · (∂x)ⁿ · y`. -/
theorem derivation_iterate_pow_mul (D : Derivation K A A) (x : A) (n : ℕ) :
    ∀ y : A, ((D.toLinearMap : Module.End K A) ^ n) (x ^ n * y)
      - (Nat.factorial n) • (D x ^ n * y) ∈ Ideal.span {x} := by
  induction n with
  | zero => intro y; simp
  | succ n ih =>
    intro y
    have hstep : (D.toLinearMap : Module.End K A) (x ^ (n + 1) * y)
        = x ^ (n + 1) * D y + (n + 1) • (x ^ n * (D x * y)) := by
      show D (x ^ (n + 1) * y) = _
      rw [D.leibniz, D.leibniz_pow]
      simp only [smul_eq_mul, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    have h1 : ((D.toLinearMap : Module.End K A) ^ n) (x ^ (n + 1) * D y) ∈ Ideal.span {x} := by
      refine derivation_iterate_mem D (Ideal.span {x}) n _ ?_
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self x) (n + 1))
    have h2 := ih (D x * y)
    have h3 : ((D.toLinearMap : Module.End K A) ^ (n + 1)) (x ^ (n + 1) * y)
        - (Nat.factorial (n + 1)) • (D x ^ (n + 1) * y)
        = ((D.toLinearMap : Module.End K A) ^ n) (x ^ (n + 1) * D y)
          + (n + 1) • (((D.toLinearMap : Module.End K A) ^ n) (x ^ n * (D x * y))
            - (Nat.factorial n) • (D x ^ n * (D x * y))) := by
      rw [pow_succ, Module.End.mul_apply, hstep, map_add, map_nsmul, smul_sub,
        Nat.factorial_succ, smul_smul]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [h3]
    exact add_mem h1 (nsmul_mem h2 (n + 1))

end DerivationFiltration

/-! ### Point derivations of a bialgebra, and the invariant derivation they induce -/

section PointDerivation

open FontaineTranslation

variable {K A : Type*} [Field K] [CommRing A] [HopfAlgebra K A]

/-- The LEFT augmentation `a ⊗ b ↦ ε(a) · b` of `A ⊗[K] A` as an `A`-algebra through the
right factor.  (`FontaineTranslation.aug` is the right-hand one.) -/
def augL : A ⊗[K] A →ₐ[K] A :=
  Algebra.TensorProduct.lift (cone : A →ₐ[K] A) (AlgHom.id K A) (fun _ _ => Commute.all _ _)

@[simp] lemma augL_tmul (a b : A) :
    (augL : A ⊗[K] A →ₐ[K] A) (a ⊗ₜ[K] b) = algebraMap K A (counit a) * b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- The convolution unit is a left unit (the mirror of `FontaineTranslation.cmul_cone`). -/
lemma cone_cmul {B : Type*} [CommRing B] [Algebra K B] (f : A →ₐ[K] B) :
    cmul cone f = f :=
  congrArg WithConv.ofConv (one_mul (WithConv.toConv f))

/-- The left counitality law, in algebra-map form. -/
lemma augL_comp_comul : (augL : A ⊗[K] A →ₐ[K] A).comp (comulAlgHom K A) = AlgHom.id K A := by
  rw [← cmul_includeLeft_includeRight, comp_cmul,
    show (augL : A ⊗[K] A →ₐ[K] A).comp Algebra.TensorProduct.includeLeft = cone from
      Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _),
    show (augL : A ⊗[K] A →ₐ[K] A).comp Algebra.TensorProduct.includeRight = AlgHom.id K A from
      Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)]
  exact cone_cmul _

@[simp] lemma augL_comul_apply (a : A) : (augL : A ⊗[K] A →ₐ[K] A) (comul a) = a :=
  AlgHom.congr_fun augL_comp_comul a

@[simp] lemma fst_inl_add_inr (α β : A) :
    TrivSqZeroExt.fst (TrivSqZeroExt.inl α + TrivSqZeroExt.inr β : DualNumber A) = α := by
  simp

@[simp] lemma snd_inl_add_inr (α β : A) :
    TrivSqZeroExt.snd (TrivSqZeroExt.inl α + TrivSqZeroExt.inr β : DualNumber A) = β := by
  simp

variable (D : A →ₗ[K] K)
variable (hmul : ∀ a b : A, D (a * b) = counitAlgHom K A a * D b + D a * counitAlgHom K A b)
variable (hone : D 1 = 0)

include hone in
lemma pointDerivation_algebraMap (k : K) : D (algebraMap K A k) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hone, smul_zero]

include hmul hone

/-- The `K`-algebra map `A ⟶ A[t]/(t²)`, `a ↦ ε a + (D a)·t`, attached to a point derivation
`D`.  That this is an ALGEBRA map is exactly the point-derivation identity `hmul`. -/
def pointDual : A →ₐ[K] DualNumber A where
  toFun a := TrivSqZeroExt.inl (algebraMap K A (counitAlgHom K A a))
    + TrivSqZeroExt.inr (algebraMap K A (D a))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp only [fst_inl_add_inr, snd_inl_add_inr, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
        map_one, hone, map_zero]
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp only [fst_inl_add_inr, snd_inl_add_inr, TrivSqZeroExt.fst_mul, DualNumber.snd_mul,
        hmul, map_mul, map_add]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp only [fst_inl_add_inr, snd_inl_add_inr, TrivSqZeroExt.fst_zero,
        TrivSqZeroExt.snd_zero, map_zero]
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp only [fst_inl_add_inr, snd_inl_add_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, add_zero, zero_add, map_add]
  commutes' k := by
    have hcomm : counitAlgHom K A (algebraMap K A k) = k := (counitAlgHom K A).commutes k
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp only [fst_inl_add_inr, snd_inl_add_inr, TrivSqZeroExt.algebraMap_eq_inl',
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, hcomm,
        pointDerivation_algebraMap D hone, map_zero]

@[simp] lemma fst_pointDual (a : A) :
    TrivSqZeroExt.fst (pointDual D hmul hone a) = algebraMap K A (counitAlgHom K A a) := by
  show TrivSqZeroExt.fst (TrivSqZeroExt.inl (algebraMap K A (counitAlgHom K A a))
    + TrivSqZeroExt.inr (algebraMap K A (D a)) : DualNumber A) = _
  simp only [fst_inl_add_inr]

@[simp] lemma snd_pointDual (a : A) :
    TrivSqZeroExt.snd (pointDual D hmul hone a) = algebraMap K A (D a) := by
  show TrivSqZeroExt.snd (TrivSqZeroExt.inl (algebraMap K A (counitAlgHom K A a))
    + TrivSqZeroExt.inr (algebraMap K A (D a)) : DualNumber A) = _
  simp only [snd_inl_add_inr]

/-- The sheared form `a ⊗ b ↦ a · (ε b + (D b)·t)`. -/
def shearDual : A ⊗[K] A →ₐ[K] DualNumber A :=
  Algebra.TensorProduct.lift (TrivSqZeroExt.inlAlgHom K A A) (pointDual D hmul hone)
    (fun _ _ => Commute.all _ _)

@[simp] lemma shearDual_tmul (a b : A) :
    shearDual D hmul hone (a ⊗ₜ[K] b)
      = TrivSqZeroExt.inl a * pointDual D hmul hone b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- `a ↦ a + (∂a)·t`, the composite `A ⟶ A ⊗ A ⟶ A[t]/(t²)`. -/
def phiDual : A →ₐ[K] DualNumber A := (shearDual D hmul hone).comp (comulAlgHom K A)

lemma fstHom_comp_shearDual :
    (TrivSqZeroExt.fstHom K A A).comp (shearDual D hmul hone) = aug K A := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [Algebra.ofId]

/-- The first component of `φ` is the identity: this is the right counitality law. -/
@[simp] lemma fst_phiDual (a : A) : TrivSqZeroExt.fst (phiDual D hmul hone a) = a := by
  show (TrivSqZeroExt.fstHom K A A) ((shearDual D hmul hone) (comul a)) = a
  rw [← AlgHom.comp_apply, fstHom_comp_shearDual, aug_comul_apply]

/-- **The invariant derivation attached to a point derivation.**  It is a derivation
*because* `φ = (id ⊗ e_D) ∘ Δ` is an algebra map into the dual numbers. -/
def pointDerivation : Derivation K A A where
  toFun a := TrivSqZeroExt.snd (phiDual D hmul hone a)
  map_add' a b := by simp [map_add]
  map_smul' k a := by simp [map_smul]
  map_one_eq_zero' := by simp [map_one]
  leibniz' a b := by
    show TrivSqZeroExt.snd (phiDual D hmul hone (a * b)) = _
    rw [map_mul, TrivSqZeroExt.snd_mul, fst_phiDual, fst_phiDual]
    simp [smul_eq_mul, mul_comm]

@[simp] lemma pointDerivation_apply (a : A) :
    pointDerivation D hmul hone a = TrivSqZeroExt.snd (phiDual D hmul hone a) := rfl

lemma counit_snd_shearDual :
    (counitAlgHom K A).toLinearMap ∘ₗ
        ((TrivSqZeroExt.sndHom A A).restrictScalars K ∘ₗ (shearDual D hmul hone).toLinearMap)
      = D ∘ₗ (augL : A ⊗[K] A →ₐ[K] A).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  have hk : ∀ (k : K) (c : A), D (algebraMap K A k * c) = k * D c := by
    intro k c
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  simp [hk]

/-- **`ε ∘ ∂ = D`.** -/
lemma counit_pointDerivation (a : A) :
    counitAlgHom K A (pointDerivation D hmul hone a) = D a := by
  have h := LinearMap.congr_fun (counit_snd_shearDual D hmul hone) (comul a)
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, TrivSqZeroExt.sndHom_apply,
    AlgHom.toLinearMap_apply, augL_comul_apply] at h
  show counitAlgHom K A (TrivSqZeroExt.snd (shearDual D hmul hone (comul a))) = D a
  exact h

end PointDerivation

/-! ### Cartier's theorem -/

section Cartier

variable (K A : Type*) [Field K] [CharZero K] [CommRing A] [HopfAlgebra K A] [Module.Finite K A]

/-- **The heart of Cartier's theorem**: in characteristic zero the augmentation ideal of a
finite-dimensional commutative Hopf algebra is idempotent, `I = I²`. -/
theorem isIdempotentElem_ker_counit :
    IsIdempotentElem (RingHom.ker (counitAlgHom K A)) := by
  classical
  show RingHom.ker (counitAlgHom K A) * RingHom.ker (counitAlgHom K A)
    = RingHom.ker (counitAlgHom K A)
  refine le_antisymm Ideal.mul_le_left ?_
  by_contra hcon
  obtain ⟨x, hxI, hxII⟩ := SetLike.not_le_iff_exists.mp hcon
  have hmemI : ∀ z : A, z ∈ RingHom.ker (counitAlgHom K A) ↔ counitAlgHom K A z = 0 :=
    fun _ => RingHom.mem_ker
  -- A `K`-linear functional killing `I²` and `1`, with `D x = 1`.
  have hxS : x ∉ (Submodule.restrictScalars K
      (RingHom.ker (counitAlgHom K A) * RingHom.ker (counitAlgHom K A)) ⊔ (K ∙ (1 : A))) := by
    intro hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hy' : y ∈ RingHom.ker (counitAlgHom K A) * RingHom.ker (counitAlgHom K A) := hy
    have hzI : (k • (1 : A)) ∈ RingHom.ker (counitAlgHom K A) := by
      have hrw : k • (1 : A) = x - y := by rw [← hyz]; ring
      rw [hrw]
      exact sub_mem hxI (Ideal.mul_le_left hy')
    have hk : k = 0 := by
      rw [hmemI] at hzI
      simpa [Algebra.smul_def] using hzI
    exact hxII (by rw [← hyz, hk]; simpa using hy')
  obtain ⟨f, hfx, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxS inferInstance
  have hfzero : ∀ y ∈ (Submodule.restrictScalars K
      (RingHom.ker (counitAlgHom K A) * RingHom.ker (counitAlgHom K A)) ⊔ (K ∙ (1 : A))),
      f y = 0 := by
    intro y hy
    have h2 : f y ∈ Submodule.map f (Submodule.restrictScalars K
      (RingHom.ker (counitAlgHom K A) * RingHom.ker (counitAlgHom K A)) ⊔ (K ∙ (1 : A))) :=
      Submodule.mem_map_of_mem hy
    rw [hfS] at h2
    simpa using h2
  set D : A →ₗ[K] K := (f x)⁻¹ • f with hD
  have hDx : D x = 1 := by simp [hD, inv_mul_cancel₀ hfx]
  have hone : D 1 = 0 := by
    have := hfzero 1 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    simp [hD, this]
  have hDII : ∀ y ∈ RingHom.ker (counitAlgHom K A) * RingHom.ker (counitAlgHom K A),
      D y = 0 := by
    intro y hy
    have := hfzero y (Submodule.mem_sup_left hy)
    simp [hD, this]
  -- the point-derivation identity
  have hlin : ∀ (k : K) (c : A), D (algebraMap K A k * c) = k * D c := by
    intro k c
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hmul : ∀ a b : A, D (a * b) = counitAlgHom K A a * D b + D a * counitAlgHom K A b := by
    intro a b
    have ha : a - algebraMap K A (counitAlgHom K A a) ∈ RingHom.ker (counitAlgHom K A) := by
      rw [hmemI]; simp
    have hb : b - algebraMap K A (counitAlgHom K A b) ∈ RingHom.ker (counitAlgHom K A) := by
      rw [hmemI]; simp
    have hprod : D ((a - algebraMap K A (counitAlgHom K A a)) *
        (b - algebraMap K A (counitAlgHom K A b))) = 0 :=
      hDII _ (Ideal.mul_mem_mul ha hb)
    have hexp : (a - algebraMap K A (counitAlgHom K A a)) *
        (b - algebraMap K A (counitAlgHom K A b))
        = a * b - algebraMap K A (counitAlgHom K A a) * b
          - algebraMap K A (counitAlgHom K A b) * a
          + algebraMap K A (counitAlgHom K A a * counitAlgHom K A b) * 1 := by
      rw [map_mul]; ring
    rw [hexp] at hprod
    simp only [map_add, map_sub, hlin, hone, mul_zero, add_zero] at hprod
    linear_combination hprod
  -- the induced derivation
  have hu : counitAlgHom K A (pointDerivation D hmul hone x) = 1 := by
    rw [counit_pointDerivation, hDx]
  have hcx : counitAlgHom K A x = 0 := (hmemI x).mp hxI
  have hspan : ∀ z ∈ Ideal.span ({x} : Set A), counitAlgHom K A z = 0 := by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_mul, hcx, mul_zero]
  have hdiag : ∀ n : ℕ, counitAlgHom K A
      ((((pointDerivation D hmul hone).toLinearMap : Module.End K A) ^ n) (x ^ n))
      = (Nat.factorial n : K) := by
    intro n
    have h := derivation_iterate_pow_mul (pointDerivation D hmul hone) x n 1
    rw [mul_one, mul_one] at h
    have h2 := hspan _ h
    have h3 : counitAlgHom K A ((pointDerivation D hmul hone) x ^ n) = 1 := by
      rw [map_pow, hu, one_pow]
    rw [map_sub, map_nsmul, h3, sub_eq_zero] at h2
    simpa using h2
  have hoff : ∀ n m : ℕ, n < m → counitAlgHom K A
      ((((pointDerivation D hmul hone).toLinearMap : Module.End K A) ^ n) (x ^ m)) = 0 := by
    intro n m hnm
    refine hspan _ (derivation_iterate_mem (pointDerivation D hmul hone)
      (Ideal.span {x}) n _ ?_)
    exact Ideal.pow_le_pow_right hnm (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self x) m)
  -- the powers of `x` are linearly independent
  have hLI : LinearIndependent K (fun m : ℕ => x ^ m) := by
    rw [linearIndependent_iff']
    intro s c hsum
    by_contra hcc
    push_neg at hcc
    obtain ⟨i0, hi0s, hi0⟩ := hcc
    have htne : (s.filter (fun i => c i ≠ 0)).Nonempty :=
      ⟨i0, Finset.mem_filter.mpr ⟨hi0s, hi0⟩⟩
    obtain ⟨hms, hcm⟩ :=
      Finset.mem_filter.mp ((s.filter (fun i => c i ≠ 0)).min'_mem htne)
    have happ := congrArg (fun z : A => counitAlgHom K A
      ((((pointDerivation D hmul hone).toLinearMap : Module.End K A) ^
        ((s.filter (fun i => c i ≠ 0)).min' htne)) z)) hsum
    simp only [map_zero, map_sum, map_smul, smul_eq_mul] at happ
    rw [Finset.sum_eq_single ((s.filter (fun i => c i ≠ 0)).min' htne)] at happ
    · rw [hdiag] at happ
      rcases mul_eq_zero.mp happ with h | h
      · exact hcm h
      · exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) h
    · intro j hjs hjm
      by_cases hcj : c j = 0
      · simp [hcj]
      · have hjt : j ∈ s.filter (fun i => c i ≠ 0) := Finset.mem_filter.mpr ⟨hjs, hcj⟩
        rw [hoff _ j (lt_of_le_of_ne (Finset.min'_le _ j hjt) (Ne.symm hjm)), mul_zero]
    · intro h; exact absurd hms h
  have : Finite ℕ := hLI.finite_of_isNoetherian
  exact not_finite ℕ

/-- `Ω[A⁄K]` vanishes: Fontaine's translation isomorphism turns `I = I²` into this. -/
theorem subsingleton_kaehlerDifferential : Subsingleton (Ω[A⁄K]) := by
  have hcot : Subsingleton ((RingHom.ker (counitAlgHom K A)).Cotangent) :=
    (Ideal.cotangent_subsingleton_iff _).mpr (isIdempotentElem_ker_counit K A)
  obtain ⟨e⟩ := FontaineTranslation.cotangent_ker_augOf_equiv (R := K) (A := A) (B := A)
    (counitAlgHom K A)
  have htens : ∀ z : A ⊗[K] (RingHom.ker (counitAlgHom K A)).Cotangent, z = 0 := by
    intro z
    induction z with
    | zero => rfl
    | tmul a m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
    | add p q hp hq => rw [hp, hq, add_zero]
  have hzero : ∀ w : (RingHom.ker (FontaineTranslation.augOf (A := A)
      (counitAlgHom K A))).Cotangent, w = 0 := by
    intro w
    exact e.injective (by rw [htens (e w), map_zero])
  haveI hker : Subsingleton ((RingHom.ker (FontaineTranslation.aug K A)).Cotangent) := by
    constructor
    intro u v
    exact (hzero u).trans (hzero v).symm
  exact FontaineTranslation.kaehlerEquivKerAugCotangent.toEquiv.subsingleton

instance formallyUnramified_of_charZero : Algebra.FormallyUnramified K A :=
  ⟨subsingleton_kaehlerDifferential K A⟩

include K in
/-- **CARTIER'S THEOREM.**  A commutative Hopf algebra which is finite-dimensional over a
field of characteristic zero is reduced. -/
theorem isReduced_of_charZero : IsReduced A :=
  Algebra.FormallyUnramified.isReduced_of_field K A

end Cartier

end CartierTheorem
