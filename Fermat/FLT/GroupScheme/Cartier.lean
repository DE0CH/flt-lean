/-
Cartier.lean — own work for the Fermat project.

# Cartier's theorem: a finite commutative group scheme in characteristic
# zero is reduced

Let `K` be a field of characteristic zero and `A` a commutative
`K`-bialgebra that is finite-dimensional as a `K`-vector space.  Then `A`
is REDUCED — equivalently, `Spec A` is a reduced (indeed étale) scheme.
This is Cartier's theorem (SGA 3, VI_B 1.6.1; Oort, *Commutative group
schemes*; Waterhouse, *Introduction to Affine Group Schemes*, Thm. 11.4;
Tate, *Finite flat group schemes*, §3.7 in Cornell-Silverman-Stevens).

## The proof, and where characteristic zero is spent

The whole content is `primitive_eq_zero`: **a finite-dimensional
bialgebra over a field of characteristic zero has no nonzero primitive
functional**, where `f : A →ₗ[K] K` is *primitive* when
`f (a * b) = f a * ε b + ε a * f b`.  Given such an `f`, the convolution
powers `f^{⋆n}` in `WithConv (A →ₗ[K] K)` assemble into the FORMAL
EXPONENTIAL

  `ψ : A →ₐ[K] K⟦t⟧`,  `ψ a = ∑ₙ (f^{⋆n} a / n!) tⁿ`,

which is where `1/n!` — hence `CharZero K` — is spent.  That `ψ` is
multiplicative is the identity

  `f^{⋆n} (a b) = ∑_{i+j=n} C(n,i) · f^{⋆i}(a) · f^{⋆j}(b)`   (`key`)

and this is proved WITHOUT Sweedler notation, in the same style as
`HopfKaehler.lean`: multiplication `μ : A ⊗ A → A` is a coalgebra map
(`Bialgebra.mulCoalgHom`), so `g ↦ g ∘ μ` is a ring map of convolution
rings; primitivity says it sends `f` to `pL f + qL f` (the two
"one-sided" copies of `f` on `A ⊗ A`); those two commute because
`pL f * qL g = push (tp f g) = qL g * pL f`; and then the identity is
just `Commute.add_pow'`.

Finally `A` is finite over `K`, so every `ψ a` is integral over `K`;
`K⟦t⟧` is a domain, and an integral element of it with zero constant
term must vanish (its minimal polynomial would be divisible by `X`,
hence equal to `X`).  So `ψ a` is a constant, its degree-one coefficient
`f a` is zero, and `f = 0`.

From there:

* `ker_counit_isIdempotentElem` — the augmentation ideal `I = ker ε`
  satisfies `I = I²`.  If not, a `K`-functional separating `I` from
  `I² ⊔ K·1` is primitive, contradicting the above.  (Extension off
  `I` uses `A = K·1 ⊕ I`.)
* `subsingleton_kaehlerDifferential` — `Ω[A⁄K] ≅ A ⊗_K (I/I²) = 0` by
  Fontaine's translation isomorphism, which is
  `FontaineTranslation.kaehlerEquivKerAugCotangent` together with
  `FontaineTranslation.cotangent_ker_augOf_equiv` from
  `Fermat/FLT/GroupScheme/HopfKaehler.lean` (sorry-free).  **This is the
  only step that needs the ANTIPODE**; everything above holds for a
  bialgebra.
* `isReduced_of_finite_hopfAlgebra` — `Ω = 0` is
  `Algebra.FormallyUnramified K A`, and mathlib's
  `Algebra.FormallyUnramified.isReduced_of_field` concludes.

**Characteristic zero is essential**: over `𝔽̄_p` the kernel of Frobenius
on `𝔾_a` is a finite flat group scheme of rank `p` with a single,
non-reduced geometric point, and its coordinate ring `k[x]/(xᵖ)` has the
nonzero primitive functional `x ↦ 1`.

**This module is sorry-free.**
-/
module

public import Fermat.FLT.GroupScheme.HopfKaehler
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open scoped TensorProduct
open Coalgebra Bialgebra WithConv LinearMap

noncomputable section

namespace Cartier

section Bialg

variable {K A : Type*} [Field K] [CommRing A] [Bialgebra K A]

/-- pullback along multiplication -/
def mComp (f : WithConv (A →ₗ[K] K)) : WithConv (A ⊗[K] A →ₗ[K] K) :=
  toConv (f.ofConv ∘ₗ (Bialgebra.mulCoalgHom K A).toLinearMap)

lemma mComp_apply (f : WithConv (A →ₗ[K] K)) (a b : A) :
    mComp f (a ⊗ₜ[K] b) = f (a * b) := by
  simp [mComp]

lemma mComp_mul (f g : WithConv (A →ₗ[K] K)) :
    mComp (f * g) = mComp f * mComp g := by
  have := LinearMap.convMul_comp_coalgHom_distrib f g (Bialgebra.mulCoalgHom K A)
  simpa [mComp] using congrArg toConv this

lemma mComp_one : mComp (1 : WithConv (A →ₗ[K] K)) = 1 := by
  simp only [mComp, LinearMap.convOne_def, ofConv_toConv]
  rw [LinearMap.comp_assoc, (Bialgebra.mulCoalgHom K A).counit_comp]

/-- tensor of two functionals -/
def tp (f g : WithConv (A →ₗ[K] K)) : WithConv (A ⊗[K] A →ₗ[K] K ⊗[K] K) :=
  toConv (TensorProduct.map f.ofConv g.ofConv)

lemma tp_mul (f g h k : WithConv (A →ₗ[K] K)) :
    tp f h * tp g k = tp (f * g) (h * k) :=
  TensorProduct.map_convMul_map

/-- collapse `K ⊗ K` -/
def push (u : WithConv (A ⊗[K] A →ₗ[K] K ⊗[K] K)) : WithConv (A ⊗[K] A →ₗ[K] K) :=
  toConv ((Algebra.TensorProduct.lmul' (S := K) K).toLinearMap ∘ₗ u.ofConv)

lemma push_mul (u v : WithConv (A ⊗[K] A →ₗ[K] K ⊗[K] K)) :
    push (u * v) = push u * push v := by
  have := LinearMap.algHom_comp_convMul_distrib (Algebra.TensorProduct.lmul' (S := K) K) u v
  simpa [push] using congrArg toConv this

lemma conv_ext {u v : WithConv (A ⊗[K] A →ₗ[K] K)}
    (h : ∀ a b : A, u (a ⊗ₜ[K] b) = v (a ⊗ₜ[K] b)) : u = v := by
  have : u.ofConv = v.ofConv := TensorProduct.ext' h
  simpa using congrArg toConv this

lemma push_tp_apply (f g : WithConv (A →ₗ[K] K)) (a b : A) :
    push (tp f g) (a ⊗ₜ[K] b) = f a * g b := by
  simp [push, tp]

/-- `f` on the left tensor factor -/
def pL (f : WithConv (A →ₗ[K] K)) : WithConv (A ⊗[K] A →ₗ[K] K) := push (tp f 1)

/-- `f` on the right tensor factor -/
def qL (f : WithConv (A →ₗ[K] K)) : WithConv (A ⊗[K] A →ₗ[K] K) := push (tp 1 f)

lemma one_apply (a : A) : (1 : WithConv (A →ₗ[K] K)) a = Coalgebra.counit a := by
  simp [LinearMap.convOne_def]

lemma pL_one : pL (1 : WithConv (A →ₗ[K] K)) = 1 := by
  refine conv_ext fun a b => ?_
  rw [pL, push_tp_apply, one_apply, one_apply, one_apply]
  exact mul_comm _ _

lemma qL_one : qL (1 : WithConv (A →ₗ[K] K)) = 1 := by
  refine conv_ext fun a b => ?_
  rw [qL, push_tp_apply, one_apply, one_apply, one_apply]
  exact mul_comm _ _

lemma pL_mul (f g : WithConv (A →ₗ[K] K)) : pL (f * g) = pL f * pL g := by
  simp only [pL, ← push_mul, tp_mul, one_mul]

lemma qL_mul (f g : WithConv (A →ₗ[K] K)) : qL (f * g) = qL f * qL g := by
  simp only [qL, ← push_mul, tp_mul, one_mul]

lemma pL_pow (f : WithConv (A →ₗ[K] K)) : ∀ n : ℕ, pL (f ^ n) = pL f ^ n
  | 0 => by simpa using pL_one
  | (n+1) => by rw [pow_succ, pow_succ, pL_mul, pL_pow f n]

lemma qL_pow (f : WithConv (A →ₗ[K] K)) : ∀ n : ℕ, qL (f ^ n) = qL f ^ n
  | 0 => by simpa using qL_one
  | (n+1) => by rw [pow_succ, pow_succ, qL_mul, qL_pow f n]

lemma mComp_pow (f : WithConv (A →ₗ[K] K)) : ∀ n : ℕ, mComp (f ^ n) = mComp f ^ n
  | 0 => by simpa using mComp_one
  | (n+1) => by rw [pow_succ, pow_succ, mComp_mul, mComp_pow f n]

lemma commute_pL_qL (f g : WithConv (A →ₗ[K] K)) : Commute (pL f) (qL g) := by
  show pL f * qL g = qL g * pL f
  simp only [pL, qL, ← push_mul, tp_mul, one_mul, mul_one]

/-- A functional is *primitive* when `f(ab) = f(a)ε(b) + ε(a)f(b)`. -/
def IsPrimitive (f : WithConv (A →ₗ[K] K)) : Prop := mComp f = pL f + qL f

lemma isPrimitive_iff (f : WithConv (A →ₗ[K] K)) :
    IsPrimitive f ↔ ∀ a b : A, f (a * b) = f a * Coalgebra.counit b + Coalgebra.counit a * f b := by
  constructor
  · intro h a b
    have := congrArg (fun u : WithConv (A ⊗[K] A →ₗ[K] K) => u (a ⊗ₜ[K] b)) h
    simpa [mComp_apply, pL, qL, push_tp_apply, one_apply] using this
  · intro h
    refine conv_ext fun a b => ?_
    simp only [mComp_apply, pL, qL]
    exact h a b

lemma conv_sum_apply {ι : Type*} (s : Finset ι) (F : ι → WithConv (A ⊗[K] A →ₗ[K] K))
    (x : A ⊗[K] A) : (∑ i ∈ s, F i) x = ∑ i ∈ s, (F i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; simp

lemma conv_nsmul_apply (c : ℕ) (u : WithConv (A ⊗[K] A →ₗ[K] K)) (x : A ⊗[K] A) :
    (c • u) x = (c : K) * (u x) := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [succ_nsmul]
      have h : ((c • u + u : WithConv (A ⊗[K] A →ₗ[K] K))) x = (c • u) x + u x := by simp
      rw [h, ih]
      push_cast
      ring

theorem key (f : WithConv (A →ₗ[K] K)) (hf : IsPrimitive f) (n : ℕ) (a b : A) :
    (f ^ n) (a * b)
      = ∑ m ∈ Finset.antidiagonal n, (n.choose m.1 : K) * ((f ^ m.1) a * (f ^ m.2) b) := by
  have h1 : mComp (f ^ n) = (pL f + qL f) ^ n := by rw [mComp_pow, hf]
  have h2 := (commute_pL_qL f f).add_pow' n
  have := congrArg (fun u : WithConv (A ⊗[K] A →ₗ[K] K) => u (a ⊗ₜ[K] b)) (h1.trans h2)
  simp only [mComp_apply] at this
  rw [this, conv_sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hpq : ∀ u v : WithConv (A →ₗ[K] K), (pL u * qL v) (a ⊗ₜ[K] b) = u a * v b := by
    intro u v
    have h : pL u * qL v = push (tp u v) := by
      simp only [pL, qL, ← push_mul, tp_mul, one_mul, mul_one]
    rw [h, push_tp_apply]
  rw [conv_nsmul_apply, ← pL_pow, ← qL_pow, hpq]

lemma convMul_one_eval (f g : WithConv (A →ₗ[K] K)) : (f * g) (1 : A) = f 1 * g 1 := by
  rw [LinearMap.convMul_apply]
  simp [Bialgebra.comul_one, Algebra.TensorProduct.one_def]

lemma pow_one_eval (f : WithConv (A →ₗ[K] K)) : ∀ n : ℕ, (f ^ n) (1 : A) = (f 1) ^ n
  | 0 => by simpa using one_apply (K := K) (1 : A)
  | (n+1) => by rw [pow_succ, pow_succ, convMul_one_eval, pow_one_eval f n]

lemma eval_one_eq_zero (f : WithConv (A →ₗ[K] K)) (hf : IsPrimitive f) : f (1 : A) = 0 := by
  have := (isPrimitive_iff f).1 hf 1 1
  simpa using this

section CharZero

variable [CharZero K]

/-- The formal exponential `a ↦ ∑ (f^{⋆n} a / n!) t^n` of a primitive functional. -/
def psi (f : WithConv (A →ₗ[K] K)) (hf : IsPrimitive f) : A →ₐ[K] PowerSeries K where
  toFun a := PowerSeries.mk fun n => (n.factorial : K)⁻¹ * (f ^ n) a
  map_one' := by
    ext n
    rw [PowerSeries.coeff_mk, pow_one_eval, eval_one_eq_zero f hf]
    cases n with
    | zero => simp
    | succ n => simp
  map_mul' a b := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, key f hf n a b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_antidiagonal] at hm
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    have hle : m.1 ≤ n := hm ▸ Nat.le_add_right _ _
    have hfac : (n.choose m.1) * (m.1).factorial * (m.2).factorial = n.factorial := by
      have := Nat.choose_mul_factorial_mul_factorial hle
      rwa [show n - m.1 = m.2 by omega] at this
    have h1 : ((m.1).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : ((m.2).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hcast : ((n.choose m.1 : K)) * ((m.1).factorial : K) * ((m.2).factorial : K)
        = (n.factorial : K) := by exact_mod_cast congrArg (Nat.cast : ℕ → K) hfac
    have hC : ((n.choose m.1 : K)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hle).ne'
    rw [← hcast]
    field_simp
  map_zero' := by ext n; simp
  map_add' a b := by ext n; simp [mul_add]
  commutes' r := by
    ext n
    rw [PowerSeries.coeff_mk, Algebra.algebraMap_eq_smul_one, map_smul, pow_one_eval,
      eval_one_eq_zero f hf]
    cases n with
    | zero => simp
    | succ n => simp

lemma coeff_psi (f : WithConv (A →ₗ[K] K)) (hf : IsPrimitive f) (a : A) (n : ℕ) :
    PowerSeries.coeff n (psi f hf a) = (n.factorial : K)⁻¹ * (f ^ n) a := by
  show PowerSeries.coeff n (PowerSeries.mk fun n => (n.factorial : K)⁻¹ * (f ^ n) a) = _
  rw [PowerSeries.coeff_mk]

/-- **Cartier's key vanishing**: over a field of characteristic zero, a finite-dimensional
bialgebra has no nonzero primitive functionals. -/
theorem primitive_eq_zero [Module.Finite K A] (f : WithConv (A →ₗ[K] K))
    (hf : IsPrimitive f) (a : A) : f a = 0 := by
  haveI : Algebra.IsIntegral K A := Algebra.IsIntegral.of_finite K A
  have _hdom : IsDomain (PowerSeries K) := inferInstance
  set ψ := psi f hf with hψ
  set s : PowerSeries K := ψ a with hs
  set c : PowerSeries K := s - algebraMap K (PowerSeries K) (PowerSeries.constantCoeff s)
    with hc
  have hcc : PowerSeries.constantCoeff c = 0 := by simp [hc]
  have hint : IsIntegral K c := by
    refine IsIntegral.sub ?_ ?_
    · exact (Algebra.IsIntegral.isIntegral (R := K) a).map ψ
    · exact isIntegral_algebraMap
  have hc0 : c = 0 := by
    by_contra hne
    have hirr : Irreducible (minpoly K c) := minpoly.irreducible hint
    have haev : Polynomial.aeval c (minpoly K c) = 0 := minpoly.aeval K c
    let φ : PowerSeries K →ₐ[K] K :=
      { PowerSeries.constantCoeff with commutes' := fun r => by simp }
    have hφc : φ c = 0 := hcc
    have : Polynomial.aeval (φ c) (minpoly K c) = 0 := by
      rw [Polynomial.aeval_algHom_apply, haev, map_zero]
    rw [hφc] at this
    have hcoeff : (minpoly K c).coeff 0 = 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using this
    obtain ⟨Q, hQ⟩ := Polynomial.X_dvd_iff.mpr hcoeff
    have hu : IsUnit Q := by
      rcases hirr.isUnit_or_isUnit hQ with h | h
      · exact absurd h Polynomial.not_isUnit_X
      · exact h
    have hQu : IsUnit (Polynomial.aeval c Q) := hu.map (Polynomial.aeval c)
    rw [hQ, map_mul, Polynomial.aeval_X] at haev
    rcases mul_eq_zero.mp haev with h | h
    · exact hne h
    · exact hQu.ne_zero h
  have : PowerSeries.coeff 1 s = 0 := by
    have : PowerSeries.coeff 1 c = 0 := by rw [hc0]; simp
    rw [hc] at this
    simpa using this
  rw [hs, coeff_psi] at this
  simpa using this

/-- **The augmentation ideal of a finite-dimensional bialgebra in characteristic zero is
idempotent.** -/
theorem ker_counit_isIdempotentElem [Module.Finite K A] :
    IsIdempotentElem (RingHom.ker (Bialgebra.counitAlgHom K A)) := by
  classical
  set I : Ideal A := RingHom.ker (Bialgebra.counitAlgHom K A) with hI
  refine le_antisymm Ideal.mul_le_left ?_
  intro x hx
  by_contra hxx
  set W : Submodule K A := Submodule.restrictScalars K (I * I) ⊔ (K ∙ (1 : A)) with hW
  have hxW : x ∉ W := by
    intro hmem
    rw [hW, Submodule.mem_sup] at hmem
    obtain ⟨w, hw, z, hz, hwz⟩ := hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have hw' : w ∈ I * I := hw
    have hwI : w ∈ I := Ideal.mul_le_left hw'
    have hcI : c • (1 : A) ∈ I := by
      have : c • (1 : A) = x - w := by rw [← hwz]; ring
      rw [this]
      exact Ideal.sub_mem _ hx hwI
    have hc0 : c = 0 := by
      have := hcI
      rw [hI, RingHom.mem_ker] at this
      simpa using this
    rw [hc0] at hwz
    simp at hwz
    exact hxx (hwz ▸ hw')
  have hne : Submodule.Quotient.mk (p := W) x ≠ 0 := by
    simpa [Submodule.Quotient.mk_eq_zero] using hxW
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero K hne
  set f : A →ₗ[K] K := g ∘ₗ W.mkQ with hf
  have hfW : ∀ z ∈ W, f z = 0 := fun z hz => by
    simp [hf, (Submodule.Quotient.mk_eq_zero W).2 hz]
  have hf1 : f (1 : A) = 0 := hfW 1 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hfII : ∀ z ∈ I * I, f z = 0 := fun z hz => hfW z (Submodule.mem_sup_left hz)
  have hprim : IsPrimitive (toConv f) := by
    refine (isPrimitive_iff (toConv f)).2 fun a b => ?_
    have ha : a - algebraMap K A (Coalgebra.counit a) ∈ I := by
      rw [hI, RingHom.mem_ker]
      simp [Bialgebra.counitAlgHom_apply]
    have hb : b - algebraMap K A (Coalgebra.counit b) ∈ I := by
      rw [hI, RingHom.mem_ker]
      simp [Bialgebra.counitAlgHom_apply]
    have hmul := hfII _ (Ideal.mul_mem_mul ha hb)
    have hexp : (a - algebraMap K A (Coalgebra.counit a))
          * (b - algebraMap K A (Coalgebra.counit b))
        = a * b - (Coalgebra.counit b : K) • a - (Coalgebra.counit a : K) • b
          + ((Coalgebra.counit a : K) * (Coalgebra.counit b : K)) • (1 : A) := by
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [hexp] at hmul
    simp only [map_sub, map_add, map_smul, smul_eq_mul, hf1, mul_zero, add_zero] at hmul
    show f (a * b) = f a * Coalgebra.counit b + Coalgebra.counit a * f b
    linear_combination hmul
  exact hg (by simpa [hf] using primitive_eq_zero (toConv f) hprim x)

end CharZero


end Bialg

/-! ### The Hopf steps: Fontaine's translation isomorphism and reducedness -/

section Hopf

variable (K A : Type*) [Field K] [CharZero K] [CommRing A] [HopfAlgebra K A]
  [Module.Finite K A]

/-- **The Kähler differentials of a finite-dimensional Hopf algebra in characteristic
zero vanish.**  `Ω[A⁄K] ≅ A ⊗_K (I/I²)` (Fontaine's translation isomorphism, proven in
`HopfKaehler.lean`) and `I = I²` by `ker_counit_isIdempotentElem`. -/
theorem subsingleton_kaehlerDifferential : Subsingleton (Ω[A⁄K]) := by
  have hI : Subsingleton (RingHom.ker (Bialgebra.counitAlgHom K A)).Cotangent :=
    (Ideal.cotangent_subsingleton_iff _).2 (ker_counit_isIdempotentElem (K := K) (A := A))
  obtain ⟨e⟩ := FontaineTranslation.cotangent_ker_augOf_equiv (R := K) (A := A)
    (Bialgebra.counitAlgHom K A)
  have htensor : Subsingleton (A ⊗[K] (RingHom.ker (Bialgebra.counitAlgHom K A)).Cotangent) := by
    have hz : ∀ z : A ⊗[K] (RingHom.ker (Bialgebra.counitAlgHom K A)).Cotangent, z = 0 := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul a m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    exact ⟨fun x y => by rw [hz x, hz y]⟩
  have haug : Subsingleton (RingHom.ker (FontaineTranslation.aug K A)).Cotangent :=
    e.toEquiv.subsingleton
  exact (FontaineTranslation.kaehlerEquivKerAugCotangent (R := K) (G := A)).toEquiv.subsingleton

include K in
/-- **CARTIER'S THEOREM.**  A finite-dimensional commutative Hopf algebra over a field of
characteristic zero is reduced. -/
theorem isReduced_of_finite_hopfAlgebra : IsReduced A := by
  haveI : Algebra.FormallyUnramified K A := ⟨subsingleton_kaehlerDifferential K A⟩
  exact Algebra.FormallyUnramified.isReduced_of_field K A

end Hopf

end Cartier
