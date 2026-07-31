/-
NumberField/MixedSpaceTraceForm.lean — own work for the Fermat project.

# The trace form on the Euclidean mixed space of a number field

This file supplies the **metric bridge** between the trace form `Tr_{K/ℚ}` of a number
field and the Euclidean structure that mathlib puts on `NumberField.mixedEmbedding.
euclidean.mixedSpace K`.  It exists for one consumer,
`heckeIdealTheta_functionalEquation` in
`Fermat/FLT/GaloisRepresentation/HardlyRamified/ModThree.lean`, whose route needs the
`ℤ`-dual (in the sense of `LinearMap.BilinForm.dualSubmodule`, which is what mathlib's
Poisson summation `zlattice_theta_transform` is stated with) of the ideal lattice of a
fractional ideal `J` to be identified with the ideal lattice of the trace-dual
`FractionalIdeal.dual ℤ ℚ J = (J·𝔡_K)⁻¹`.

## What is here

* `trace_eq_sum_mult_re` / `trace_eq_sum_real_add_two_sum_complex`: the ADDITIVE analogue
  of `NumberField.InfinitePlace.prod_eq_abs_norm`.  Mathlib has the multiplicative
  statement `∏ w, w x ^ mult w = |N(x)|` but no `InfinitePlace`-indexed trace formula at
  all (checked against the pin, 2026-07-28 and again 2026-07-31); these are proved on the
  template of that lemma.
* `euclidean_inner_apply`: the real inner product of `euclidean.mixedSpace K` in
  coordinates, `Σ_real x_w y_w + Σ_complex Re(conj(x_w)·y_w)`.
* `traceEmbedding`: the canonical embedding with the complex block rescaled by `√2`.
* `mixedConj`: coordinatewise complex conjugation, as a linear ISOMETRY — hence invisible
  to every theta series, which is why it can be absorbed on the dual side.
* `inner_traceEmbedding_mixedConj`: **the bridge.**
  `⟪traceEmbedding a, mixedConj (traceEmbedding b)⟫ = Tr_{K/ℚ}(a·b)`.
* `traceLattice`: the `√2`-rescaled ideal lattice of a fractional ideal, with an `ℝ`-basis
  `traceLatticeBasis` that is a `ℤ`-basis of it.
* `dualSubmodule_traceLattice`: **the payoff.**  The `ℤ`-dual of `traceLattice I` — in
  exactly the `LinearMap.BilinForm.dualSubmodule (innerₗ _)` sense in which mathlib's
  `zlattice_theta_transform` is stated — is `mixedConj` applied to `traceLattice` of the
  trace-dual ideal `FractionalIdeal.dual ℤ ℚ I = (I·𝔡_K)⁻¹`.  Both are packaged for the
  consumer as `TraceFormBridge`, proven by `traceFormBridge`.

The proof of `dualSubmodule_traceLattice` is the biorthogonality argument and nothing more:
`traceLatticeBasis I` is an `ℝ`-basis of the mixed space that `ℤ`-spans the lattice, the
bridge says `⟪traceEmbedding (b j), mixedConj (traceEmbedding (b.traceDual i))⟫ =
Tr(b j · b.traceDual i) = δ_{ij}`, so `mixedConj ∘ traceEmbedding ∘ b.traceDual` IS the
`LinearMap.BilinForm.dualBasis` (`dualBasis_eq_iff`), and
`dualSubmodule_span_of_basis` + `Submodule.traceDual_span_of_basis` finish it.  Note that
NO covolume computation and no double-dual argument is needed — the dual basis pins the
dual lattice on the nose.

## Why the `√2` and the conjugation are both forced

Mathlib's Euclidean structure on the mixed space is `Σ_real x_w² + Σ_complex |x_w|²`
(`euclidean.stdOrthonormalBasis`, built from `Complex.orthonormalBasisOneI`).  The trace
form is `Tr(xy) = Σ_real σ_w x σ_w y + 2·Σ_complex Re(σ_w x σ_w y)`: the complex block is
DOUBLED, which the `√2` rescaling supplies.  And the Euclidean pairing conjugates its
second argument (`Re(conj(x)·y)`) whereas the trace form does not, which the conjugation
supplies.  Neither is cosmetic: with the undoubled metric the `ℤ`-dual of an ideal lattice
is NOT a rescaled ideal lattice at all in mixed signature `(r₁ > 0, r₂ > 0)` — it is the
image of one under the coordinatewise scaling by `2` on the complex block, which is not a
homothety and therefore not invisible to a theta sum.  With the doubled metric,
`covol(σ J) = N(J)·√|d_K|` and `covol(σ (J𝔡)⁻¹) = 1/(N(J)·√|d_K|)` are exact reciprocals,
which is the source of the functional-equation constant `1`.

## Provenance

The four trace lemmas were written by `flt-lean-272` and preserved as the git blob tag
`flt-lean-272-trace-over-places`; they were never committed because nothing consumed them
and they would have been free-floating.  They are lifted here verbatim (modulo the
namespace) together with the bridge that consumes them and the consumer that consumes it.
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.NumberTheory.NumberField.FractionalIdeal

@[expose] public section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Finset
open scoped ComplexConjugate

namespace Fermat.MixedSpaceTrace

variable {K : Type*} [Field K] [NumberField K]

/-! ### The trace as a sum over infinite places -/

open scoped Classical in
/-- The fibre of `InfinitePlace.mk` over `w` is `{embedding w, conjugate (embedding w)}`. -/
theorem filter_mk_eq (w : InfinitePlace K) :
    ({φ : K →+* ℂ | mk φ = w} : Finset (K →+* ℂ))
      = {embedding w, ComplexEmbedding.conjugate (embedding w)} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, ComplexEmbedding.conjugate]
  conv_lhs =>
    rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate, star_involutive.eq_iff]

open scoped Classical in
/-- The sum of `φ x` over the embeddings inducing a fixed place `w`. -/
theorem sum_fiber_eq (w : InfinitePlace K) (x : K) :
    ∑ φ ∈ ({φ : K →+* ℂ | mk φ = w} : Finset (K →+* ℂ)), φ x
      = (mult w : ℂ) * (((embedding w) x).re : ℂ) := by
  rw [filter_mk_eq w]
  by_cases hw : IsReal w
  · have hconj : ComplexEmbedding.conjugate (embedding w) = embedding w :=
      conjugate_embedding_eq_of_isReal hw
    have him : ((embedding w) x).im = 0 := by
      have h := congrArg (fun f : K →+* ℂ => f x) hconj
      simp only [ComplexEmbedding.conjugate_coe_eq] at h
      exact Complex.conj_eq_iff_im.mp h
    rw [hconj, Finset.pair_eq_singleton, Finset.sum_singleton, mult_isReal ⟨w, hw⟩]
    exact Complex.ext (by simp) (by simp [him])
  · have hne : embedding w ≠ ComplexEmbedding.conjugate (embedding w) := by
      intro h
      exact hw (isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [Finset.sum_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.add_conj,
      mult_isComplex ⟨w, not_isReal_iff_isComplex.mp hw⟩]
    push_cast
    ring

open scoped Classical in
/-- **The trace as a sum over infinite places** — the additive analogue of
`NumberField.InfinitePlace.prod_eq_abs_norm`. -/
theorem trace_eq_sum_mult_re (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℝ)
      = ∑ w : InfinitePlace K, (mult w : ℝ) * ((embedding w) x).re := by
  have hC : ((Algebra.trace ℚ K x : ℚ) : ℂ)
      = ∑ w : InfinitePlace K, (mult w : ℂ) * (((embedding w) x).re : ℂ) := by
    have h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ K x) = ∑ σ : K →ₐ[ℚ] ℂ, σ x :=
      _root_.trace_eq_sum_embeddings ℂ
    have h2 : ∑ φ : K →+* ℂ, φ x = ∑ σ : K →ₐ[ℚ] ℂ, σ x :=
      Fintype.sum_equiv RingHom.equivRatAlgHom (fun φ => φ x) (fun σ => σ x)
        (fun _ => by simp [RingHom.equivRatAlgHom_apply])
    have h3 : ∑ w : InfinitePlace K,
          ∑ φ ∈ ({φ : K →+* ℂ | mk φ = w} : Finset (K →+* ℂ)), φ x
        = ∑ φ : K →+* ℂ, φ x :=
      Finset.sum_fiberwise Finset.univ (fun φ => mk φ) (fun φ => φ x)
    have h0 : ((Algebra.trace ℚ K x : ℚ) : ℂ) = (algebraMap ℚ ℂ) (Algebra.trace ℚ K x) := by
      simp [eq_ratCast]
    rw [h0, h1, ← h2, ← h3]
    exact Finset.sum_congr rfl fun w _ => sum_fiber_eq w x
  have h4 := congrArg Complex.re hC
  simpa using h4

open scoped Classical in
/-- The real/complex split: `Tr(x) = ∑_{w real} σ_w x + 2·∑_{w complex} Re(σ_w x)`. -/
theorem trace_eq_sum_real_add_two_sum_complex (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℝ)
      = (∑ w : {w : InfinitePlace K // IsReal w}, ((embedding w.1) x).re)
        + 2 * ∑ w : {w : InfinitePlace K // IsComplex w}, ((embedding w.1) x).re := by
  rw [trace_eq_sum_mult_re x,
    InfinitePlace.sum_eq_sum_add_sum (fun w => (mult w : ℝ) * ((embedding w) x).re)]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by rw [mult_isReal w, Nat.cast_one, one_mul]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by rw [mult_isComplex w]; norm_num

/-! ### The Euclidean mixed space: the inner product, in coordinates -/

variable (K) in
open scoped Classical in
/-- The real inner product of the Euclidean mixed space, in coordinates. -/
theorem euclidean_inner_apply (x y : euclidean.mixedSpace K) :
    inner ℝ x y
      = (∑ w : {w : InfinitePlace K // IsReal w}, x.ofLp.1.ofLp w * y.ofLp.1.ofLp w)
        + ∑ w : {w : InfinitePlace K // IsComplex w},
            (conj (x.ofLp.2.ofLp w) * y.ofLp.2.ofLp w).re := by
  rw [WithLp.prod_inner_apply, PiLp.inner_apply]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by simp [RCLike.inner_apply, mul_comm]
  · rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun w _ => by
      rw [real_inner_eq_re_inner ℂ]; simp [RCLike.inner_apply, mul_comm]

/-! ### The trace embedding and the conjugation isometry -/

variable (K) in
/-- The `√2`-rescaled canonical embedding of `K` into the Euclidean mixed space,
`a ↦ ((σ_w a)_{w real}, (√2·σ_w a)_{w complex})`.

Its point is `inner_traceEmbedding_mixedConj` below: the Euclidean inner product of
`traceEmbedding a` against the coordinatewise CONJUGATE of `traceEmbedding b` is exactly
`Tr_{K/ℚ}(a·b)`.  The rescaling is forced — the Euclidean structure that mathlib puts on
`euclidean.mixedSpace K` is `Σ_real x² + Σ_complex |x|²`, whereas the trace form is
`Σ_real + 2·Σ_complex Re`, and `√2` on the complex block is exactly the difference. -/
noncomputable def traceEmbedding (a : K) : euclidean.mixedSpace K :=
  WithLp.toLp 2
    (WithLp.toLp 2 (fun w : {w : InfinitePlace K // IsReal w} => embedding_of_isReal w.prop a),
      WithLp.toLp 2 (fun w : {w : InfinitePlace K // IsComplex w} =>
        (Real.sqrt 2 : ℂ) * w.1.embedding a))

omit [NumberField K] in
@[simp]
theorem traceEmbedding_fst (a : K) (w : {w : InfinitePlace K // IsReal w}) :
    (traceEmbedding K a).ofLp.1.ofLp w = embedding_of_isReal w.prop a := rfl

omit [NumberField K] in
@[simp]
theorem traceEmbedding_snd (a : K) (w : {w : InfinitePlace K // IsComplex w}) :
    (traceEmbedding K a).ofLp.2.ofLp w = (Real.sqrt 2 : ℂ) * w.1.embedding a := rfl

variable (K) in
open scoped Classical in
/-- Coordinatewise complex conjugation on the Euclidean mixed space.  It is a linear
isometry, hence invisible to every theta series; it is the discrepancy between the
`ℤ`-dual of an ideal lattice and the ideal lattice of the trace-dual ideal. -/
noncomputable def mixedConj : euclidean.mixedSpace K ≃ₗᵢ[ℝ] euclidean.mixedSpace K :=
  LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ _)
    (LinearIsometryEquiv.piLpCongrRight 2 fun _ : {w : InfinitePlace K // IsComplex w} =>
      Complex.conjLIE)

open scoped Classical in
@[simp]
theorem mixedConj_fst (x : euclidean.mixedSpace K) (w : {w : InfinitePlace K // IsReal w}) :
    (mixedConj K x).ofLp.1.ofLp w = x.ofLp.1.ofLp w := rfl

open scoped Classical in
@[simp]
theorem mixedConj_snd (x : euclidean.mixedSpace K) (w : {w : InfinitePlace K // IsComplex w}) :
    (mixedConj K x).ofLp.2.ofLp w = conj (x.ofLp.2.ofLp w) := rfl

variable (K) in
open scoped Classical in
/-- **The metric bridge**: the Euclidean inner product of the `√2`-rescaled canonical
embedding of `a` against the conjugate of that of `b` is the trace form `Tr_{K/ℚ}(a·b)`.

This is the one genuinely new algebraic input identified by the survey of
`heckeIdealTheta_functionalEquation`: mathlib carries no `InfinitePlace`-indexed trace
formula at all, and this is what lets the `ℤ`-dual of an ideal lattice be computed. -/
theorem inner_traceEmbedding_mixedConj (a b : K) :
    inner ℝ (traceEmbedding K a) (mixedConj K (traceEmbedding K b))
      = ((Algebra.trace ℚ K (a * b) : ℚ) : ℝ) := by
  rw [euclidean_inner_apply, trace_eq_sum_real_add_two_sum_complex, Finset.mul_sum]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedConj_fst, traceEmbedding_fst, traceEmbedding_fst, ← map_mul,
      ← embedding_of_isReal_apply w.prop, Complex.ofReal_re]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedConj_snd, traceEmbedding_snd, traceEmbedding_snd, map_mul, map_mul,
      Complex.conj_ofReal]
    rw [show ((Real.sqrt 2 : ℝ) : ℂ) * (conj ((embedding w.1) a)) *
        (((Real.sqrt 2 : ℝ) : ℂ) * conj ((embedding w.1) b))
        = (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) *
          conj (((embedding w.1) a) * ((embedding w.1) b)) by
      rw [map_mul]; ring]
    rw [h2, ← map_mul]
    simp

section TraceLattice

open Module
open scoped nonZeroDivisors Classical

variable (K) in
/-- The `√2`-rescaled identification of the mixed space with the Euclidean mixed space. -/
noncomputable def traceMixedEquiv : mixedSpace K ≃ₗ[ℝ] euclidean.mixedSpace K :=
  ((LinearEquiv.refl ℝ ({w : InfinitePlace K // IsReal w} → ℝ)).prodCongr
      (LinearEquiv.smulOfUnit
        (M := ({w : InfinitePlace K // IsComplex w} → ℂ))
        (Units.mk0 (Real.sqrt 2) (by positivity)))) ≪≫ₗ
    (euclidean.toMixed K).symm.toLinearEquiv

theorem traceMixedEquiv_mixedEmbedding (a : K) :
    traceMixedEquiv K (mixedEmbedding K a) = traceEmbedding K a := by
  refine (euclidean.toMixed K).injective ?_
  refine Prod.ext (funext fun w => rfl) (funext fun w => ?_)
  show ((Real.sqrt 2 : ℝ) • (mixedEmbedding K a).2) w = (Real.sqrt 2 : ℂ) * w.1.embedding a
  simp [Complex.real_smul]

variable (K) in
/-- `traceEmbedding` as a `ℤ`-linear map. -/
noncomputable def traceEmbeddingₗ : K →ₗ[ℤ] euclidean.mixedSpace K :=
  ((traceMixedEquiv K).restrictScalars ℤ : mixedSpace K →ₗ[ℤ] euclidean.mixedSpace K) ∘ₗ
    (mixedEmbedding K).toIntAlgHom.toLinearMap

@[simp]
theorem traceEmbeddingₗ_apply (a : K) : traceEmbeddingₗ K a = traceEmbedding K a :=
  traceMixedEquiv_mixedEmbedding a

/-! ### The ideal lattices of the trace form -/

variable (K) in
/-- An `ℝ`-basis of the Euclidean mixed space that is a `ℤ`-basis of the `√2`-rescaled
ideal lattice of `I`. -/
noncomputable def traceLatticeBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Free.ChooseBasisIndex ℤ ↥((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) ℝ
      (euclidean.mixedSpace K) :=
  (fractionalIdealLatticeBasis K I).map (traceMixedEquiv K)

theorem traceLatticeBasis_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (i) :
    traceLatticeBasis K I i = traceEmbedding K (basisOfFractionalIdeal K I i) := by
  rw [traceLatticeBasis, Basis.map_apply, fractionalIdealLatticeBasis_apply,
    traceMixedEquiv_mixedEmbedding]

variable (K) in
/-- The `√2`-rescaled ideal lattice of `I` inside the Euclidean mixed space. -/
noncomputable def traceLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  Submodule.span ℤ (Set.range (traceLatticeBasis K I))

theorem traceLattice_eq_map (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceLattice K I = Submodule.map (traceEmbeddingₗ K)
      (Submodule.restrictScalars ℤ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) := by
  have hspan : Submodule.restrictScalars ℤ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      = Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) := by
    ext x
    simpa using (mem_span_basisOfFractionalIdeal K).symm
  rw [traceLattice, hspan, ← Submodule.span_image, ← Set.range_comp]
  exact congrArg (Submodule.span ℤ) (congrArg Set.range
    (funext fun i => by simpa using traceLatticeBasis_apply I i))

/-! ### The dual lattice -/

theorem innerₗ_nondegenerate :
    LinearMap.BilinForm.Nondegenerate (innerₗ (euclidean.mixedSpace K)) := by
  constructor
  · intro x hx
    have h : inner ℝ x x = 0 := by simpa using hx x
    exact inner_self_eq_zero.mp h
  · intro y hy
    have h : inner ℝ y y = 0 := by simpa using hy y
    exact inner_self_eq_zero.mp h

variable (K) in
/-- The trace-dual of a unit fractional ideal, as a unit fractional ideal:
`dualIdeal I = (I·𝔡_K)⁻¹`. -/
noncomputable def dualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (isUnit_iff_ne_zero.mpr (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)).unit

theorem coe_dualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((dualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      = Submodule.traceDual ℤ ℚ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  rw [show ((dualIdeal K I : FractionalIdeal (𝓞 K)⁰ K)) = FractionalIdeal.dual ℤ ℚ I from
    IsUnit.unit_spec _]
  exact FractionalIdeal.coe_dual ℤ ℚ I.ne_zero

variable (K) in
/-- **Sub-leaf (B)**: the `ℤ`-dual of the trace ideal lattice of `I` is the trace ideal
lattice of the trace-dual ideal `(I·𝔡_K)⁻¹`, transported by the conjugation ISOMETRY. -/
theorem dualSubmodule_traceLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K)) (traceLattice K I)
      = Submodule.map ((mixedConj K).toLinearEquiv.restrictScalars ℤ :
          euclidean.mixedSpace K →ₗ[ℤ] euclidean.mixedSpace K) (traceLattice K (dualIdeal K I)) := by
  classical
  have hdb : ⇑(LinearMap.BilinForm.dualBasis (innerₗ (euclidean.mixedSpace K))
        innerₗ_nondegenerate (traceLatticeBasis K I))
      = fun i => mixedConj K (traceEmbedding K ((basisOfFractionalIdeal K I).traceDual i)) := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro i j
    rw [traceLatticeBasis_apply]
    have key : inner ℝ (traceEmbedding K (basisOfFractionalIdeal K I j))
        (mixedConj K (traceEmbedding K ((basisOfFractionalIdeal K I).traceDual i)))
        = ((Algebra.trace ℚ K (basisOfFractionalIdeal K I j *
            (basisOfFractionalIdeal K I).traceDual i) : ℚ) : ℝ) :=
      inner_traceEmbedding_mixedConj K _ _
    show inner ℝ (mixedConj K (traceEmbedding K ((basisOfFractionalIdeal K I).traceDual i)))
        (traceEmbedding K (basisOfFractionalIdeal K I j)) = _
    rw [real_inner_comm, key, Basis.trace_mul_traceDual]
    split_ifs <;> simp
  have hspan : Submodule.restrictScalars ℤ
        (Submodule.traceDual ℤ ℚ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
      = Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I).traceDual) := by
    refine Submodule.traceDual_span_of_basis ℤ _ _ ?_
    ext x
    simpa using (mem_span_basisOfFractionalIdeal K).symm
  rw [traceLattice_eq_map (dualIdeal K I), coe_dualIdeal, hspan, traceLattice,
    LinearMap.BilinForm.dualSubmodule_span_of_basis _ innerₗ_nondegenerate, hdb,
    ← Submodule.map_comp, Submodule.map_span, ← Set.range_comp]
  exact congrArg (Submodule.span ℤ) (congrArg Set.range (funext fun i => by simp))

/-! ### The packaged bridge -/

variable (K) in
/-- **Sub-leaf (B) of `heckeIdealTheta_functionalEquation`, packaged as a `Prop`** so that
a consumer can state it as a hypothesis without having to `open scoped Classical` itself
(the `Inner` instance on `euclidean.mixedSpace K` goes through `Fintype {w // IsReal w}`,
which needs a `DecidablePred`).  Both conjuncts are PROVEN — see `traceFormBridge`.

* the METRIC identification: the Euclidean inner product of `traceEmbedding a` against
  the conjugate of `traceEmbedding b` is `Tr_{K/ℚ}(a·b)`;
* the DUAL-LATTICE identification: the `ℤ`-dual of the trace ideal lattice of `I`, in
  exactly the `LinearMap.BilinForm.dualSubmodule (innerₗ _)` sense in which mathlib's
  Poisson summation `zlattice_theta_transform` is stated, is the trace ideal lattice of
  the trace-dual ideal `(I·𝔡_K)⁻¹`, moved by the conjugation ISOMETRY `mixedConj` — and
  an isometry is invisible to a theta sum, which is the whole point. -/
def TraceFormBridge : Prop :=
  (∀ a b : K, inner ℝ (traceEmbedding K a) (mixedConj K (traceEmbedding K b))
      = ((Algebra.trace ℚ K (a * b) : ℚ) : ℝ)) ∧
  (∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      LinearMap.BilinForm.dualSubmodule (innerₗ (euclidean.mixedSpace K)) (traceLattice K I)
        = Submodule.map ((mixedConj K).toLinearEquiv.restrictScalars ℤ :
            euclidean.mixedSpace K →ₗ[ℤ] euclidean.mixedSpace K)
            (traceLattice K (dualIdeal K I)))

variable (K) in
/-- **Sub-leaf (B) is closed.** -/
theorem traceFormBridge : TraceFormBridge K :=
  ⟨inner_traceEmbedding_mixedConj K, dualSubmodule_traceLattice K⟩

end TraceLattice

end Fermat.MixedSpaceTrace
