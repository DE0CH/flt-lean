/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The trace form of a number field, as a pairing on the mixed space

Material destined for Mathlib.

Mathlib has the MULTIPLICATIVE statement relating a number field's arithmetic to
its infinite places — `NumberField.InfinitePlace.prod_eq_abs_norm`,
`∏ w, w x ^ mult w = |N(x)|` — but not the additive one, and it carries no
`InfinitePlace`-indexed trace formula at all (checked against the pin
2026-07-28 and again 2026-07-30: grepping
`Mathlib/NumberTheory/NumberField/CanonicalEmbedding/` for `traceForm` /
`Algebra.trace` returns nothing).

This file supplies that gap in four steps, ending at the identification that
`heckeIdealTheta_functionalEquation`'s sub-leaf (B) needs:

* `Fermat.TraceForm.trace_eq_sum_mult_re` —
  `Tr_{K/ℚ}(x) = ∑_w mult(w)·Re(σ_w x)`, the additive analogue of
  `prod_eq_abs_norm`, proved on that lemma's own template
  (`trace_eq_sum_embeddings`, `RingHom.equivRatAlgHom`,
  `Finset.sum_fiberwise`);
* `Fermat.TraceForm.trace_eq_sum_real_add_two_sum_complex` — its real/complex
  split `Tr(x) = ∑_{w real} σ_w x + 2·∑_{w complex} Re(σ_w x)`;
* `Fermat.TraceForm.trace_mul_eq_mixedPairing` — the trace FORM read off the
  mixed embedding: `Tr(x·y) = ∑_{w real} σ_w x·σ_w y
  + 2·∑_{w complex} Re(σ_w x·σ_w y)`;
* `Fermat.TraceForm.trace_mul_eq_mixedInner` — the same, written with the real
  inner product of `ℂ`, which forces the conjugation into view:
  `Tr(x·y) = ∑_{w real} x_w y_w + 2·∑_{w complex} ⟪x_w, conj y_w⟫_ℝ`.
  The doubling on the complex block and that conjugation are exactly the two
  discrepancies between the trace form and the metric of
  `NumberField.mixedEmbedding.euclidean.mixedSpace`
  (`Σ_real x_w² + Σ_complex |x_w|²`);
* `Fermat.TraceForm.mem_traceDual_iff_mixedPairing_isInt` — the consumer:
  `Submodule.traceDual ℤ ℚ I` is exactly the dual of `I` for that pairing.

## What this is for, and what it is NOT

The sorry leaf `heckeIdealTheta_functionalEquation`
(`GaloisRepresentation/HardlyRamified/ModThree.lean`) records a three-part cut
of Hecke's unit-domain theta functional equation — (A) the integral
representation over a fundamental domain `𝔉` for the units, (B) the
identification of the LATTICE dual of `mixedEmbedding.idealLattice K J` with
the ideal lattice of the trace-dual `(J·𝔡_K)⁻¹`, and (C) invariance of `𝔉`
under `y ↦ y⁻¹` — and names (B) as "the only one with no analysis in it and
the right place to start".

This file is the algebraic half of (B), and only that half. What (B) still
needs on top of it, none of which is here:

* transport along `mixedEmbedding.euclidean.toMixed` (with
  `volumePreserving_toMixed`) into an inner-product space, together with the
  `√2`-rescaling of the complex block that the doubling above makes explicit;
* `ZLattice.comap` bookkeeping identifying the transported
  `mixedEmbedding.idealLattice K J` with a `ZLattice` of the ambient
  Euclidean space, as `NumberField.Ideal.Asymptotics` does it;
* the passage from `Submodule.traceDual` to the FRACTIONAL ideal
  `(J·𝔡_K)⁻¹` — mathlib's `FractionalIdeal.dual`, `differentIdeal` and
  `NumberField.absNorm_differentIdeal` (`N𝔡 = |d_K|`) are the named inputs;
* the covolume computation, `mixedEmbedding.covolume_idealLattice`.

A universe obstruction is also recorded there and is unaffected by this file:
`euclidean.mixedSpace K` lives in `K`'s universe while the Poisson hypothesis
`hθ` quantifies over `E : Type`, so `hθ` cannot be applied to the mixed space
directly.

## Provenance

`filter_mk_eq`, `sum_fiber_eq`, `trace_eq_sum_mult_re` and
`trace_eq_sum_real_add_two_sum_complex` were proved and verified against this
pin on 2026-07-28 by the previous owner of that leaf, who deliberately did NOT
commit them because nothing consumed them, and preserved them as the git blob
tag `flt-lean-272-trace-over-places` with the instruction that a successor
"commit them TOGETHER with the assembly that consumes them".
`trace_mul_eq_mixedPairing`, `trace_mul_eq_mixedInner` and
`mem_traceDual_iff_mixedPairing_isInt` are that assembly, added 2026-07-30.
The four lifted lemmas are unchanged apart from being renamed into this
namespace.
-/

@[expose] public section

open NumberField NumberField.InfinitePlace Finset

namespace Fermat.TraceForm

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- The fibre of `NumberField.InfinitePlace.mk` over `w` is exactly
`{embedding w, conjugate (embedding w)}` — a singleton at a real place and a
genuine pair at a complex one. -/
theorem filter_mk_eq (w : InfinitePlace K) :
    ({φ : K →+* ℂ | mk φ = w} : Finset (K →+* ℂ))
      = {embedding w, ComplexEmbedding.conjugate (embedding w)} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, ComplexEmbedding.conjugate]
  conv_lhs =>
    rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate, star_involutive.eq_iff]

open scoped Classical in
/-- The sum of `φ x` over the complex embeddings inducing a fixed infinite place
`w` is `mult w · Re(σ_w x)`: one real term at a real place, and `z + z̄ = 2 Re z`
at a complex one. -/
theorem sum_fiber_eq (w : InfinitePlace K) (x : K) :
    ∑ φ ∈ ({φ : K →+* ℂ | mk φ = w} : Finset (K →+* ℂ)), φ x
      = (mult w : ℂ) * (((embedding w) x).re : ℂ) := by
  rw [filter_mk_eq w]
  by_cases hw : IsReal w
  · -- one embedding, and it is real-valued
    have hconj : ComplexEmbedding.conjugate (embedding w) = embedding w :=
      conjugate_embedding_eq_of_isReal hw
    have him : ((embedding w) x).im = 0 := by
      have h := congrArg (fun f : K →+* ℂ => f x) hconj
      simp only [ComplexEmbedding.conjugate_coe_eq] at h
      exact Complex.conj_eq_iff_im.mp h
    rw [hconj, Finset.pair_eq_singleton, Finset.sum_singleton, mult_isReal ⟨w, hw⟩]
    exact Complex.ext (by simp) (by simp [him])
  · -- two distinct conjugate embeddings
    have hne : embedding w ≠ ComplexEmbedding.conjugate (embedding w) := by
      intro h
      exact hw (isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [Finset.sum_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.add_conj,
      mult_isComplex ⟨w, not_isReal_iff_isComplex.mp hw⟩]
    push_cast
    ring

open scoped Classical in
/-- **The trace as a sum over infinite places** — the additive analogue of
`NumberField.InfinitePlace.prod_eq_abs_norm`.  For `x` in a number field `K`,
`Tr_{K/ℚ}(x) = ∑_w mult(w) · Re(σ_w x)`: a real place contributes `σ_w x` and
each complex place contributes `2·Re(σ_w x)`. -/
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
/-- The real/complex split: `Tr(x) = ∑_{w real} σ_w x + 2·∑_{w complex} Re(σ_w x)`.
This is the shape in which the trace form is compared with the mixed-space inner
product `Σ_real x y + Σ_complex Re(x ȳ)`. -/
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

open scoped Classical in
/-- **The trace FORM of a number field, read off the mixed embedding.**  For
`x y : K`,

`Tr_{K/ℚ}(x·y) = ∑_{w real} x_w·y_w + 2·∑_{w complex} Re(x_w·y_w)`,

where `x_w` denotes the `w`-component of `NumberField.mixedEmbedding K x`.
Note the second factor is `y_w`, NOT its conjugate: the trace form is the
BILINEAR pairing, and turning it into the (sesquilinear) inner product of the
mixed space is what `trace_mul_eq_mixedInner` does. -/
theorem trace_mul_eq_mixedPairing (x y : K) :
    ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ)
      = (∑ w : {w : InfinitePlace K // IsReal w},
            (mixedEmbedding K x).1 w * (mixedEmbedding K y).1 w)
        + 2 * ∑ w : {w : InfinitePlace K // IsComplex w},
            ((mixedEmbedding K x).2 w * (mixedEmbedding K y).2 w).re := by
  rw [trace_eq_sum_real_add_two_sum_complex (x * y)]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp only [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
    rw [map_mul, ← embedding_of_isReal_apply w.2 x, ← embedding_of_isReal_apply w.2 y,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  · congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex, map_mul]

open scoped Classical in
/-- **The trace form is the mixed-space INNER product, after conjugating one
argument and doubling the complex block.**  For `x y : K`,

`Tr_{K/ℚ}(x·y) = ∑_{w real} x_w·y_w + 2·∑_{w complex} ⟪x_w, conj y_w⟫_ℝ`.

The two discrepancies from `NumberField.mixedEmbedding.euclidean.mixedSpace`'s
own metric `Σ_real x_w² + Σ_complex |x_w|²` are therefore exactly: the factor
`2` on complex places (a `√2` rescaling of that block), and the coordinatewise
complex conjugation.  The conjugation is a linear isometry of the mixed space,
so it is invisible to every theta sum — which is why the constant in the
functional equation is `1`. -/
theorem trace_mul_eq_mixedInner (x y : K) :
    ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ)
      = (∑ w : {w : InfinitePlace K // IsReal w},
            (mixedEmbedding K x).1 w * (mixedEmbedding K y).1 w)
        + 2 * ∑ w : {w : InfinitePlace K // IsComplex w},
            inner ℝ ((mixedEmbedding K x).2 w)
              ((starRingEnd ℂ) ((mixedEmbedding K y).2 w)) := by
  have key : ∀ w : {w : InfinitePlace K // IsComplex w},
      ((mixedEmbedding K x).2 w * (mixedEmbedding K y).2 w).re
        = inner ℝ ((mixedEmbedding K x).2 w)
            ((starRingEnd ℂ) ((mixedEmbedding K y).2 w)) := by
    intro w
    rw [Complex.inner]
    simp [← map_mul, mul_comm]
  rw [trace_mul_eq_mixedPairing x y]
  simp_rw [key]

open scoped Classical in
/-- **The trace-dual of a module is its dual for the mixed-space pairing.**
`x` lies in `Submodule.traceDual ℤ ℚ I` — mathlib's `Iᵛ`, the submodule
`{x | ∀ y ∈ I, Tr(x·y) ∈ ℤ}` whose fractional-ideal incarnation
`FractionalIdeal.dual` is `(I·𝔡_K)⁻¹` — exactly when the mixed-space pairing of
`x` against every `y ∈ I` is a rational integer.

This is the algebraic content of sub-leaf (B) of
`heckeIdealTheta_functionalEquation`: it says the ARITHMETIC dual and the
GEOMETRIC dual of an ideal lattice are the same subset of `K`.  What is left
for (B) is the transport of that statement across
`mixedEmbedding.euclidean.toMixed` into a genuine `ZLattice` duality
(`LinearMap.BilinForm.dualSubmodule`), with the `√2` and the covolume — see the
module docstring. -/
theorem mem_traceDual_iff_mixedPairing_isInt
    {I : Submodule (NumberField.RingOfIntegers K) K} {x : K} :
    x ∈ Submodule.traceDual ℤ ℚ I ↔
      ∀ y ∈ I, ∃ n : ℤ,
        (∑ w : {w : InfinitePlace K // IsReal w},
            (mixedEmbedding K x).1 w * (mixedEmbedding K y).1 w)
          + 2 * ∑ w : {w : InfinitePlace K // IsComplex w},
              inner ℝ ((mixedEmbedding K x).2 w)
                ((starRingEnd ℂ) ((mixedEmbedding K y).2 w)) = (n : ℝ) := by
  rw [Submodule.mem_traceDual]
  refine forall₂_congr fun y _ => ?_
  rw [Algebra.traceForm_apply]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← trace_mul_eq_mixedInner x y, ← hn]
    simp
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h1 : ((Algebra.trace ℚ K (x * y) : ℚ) : ℝ) = ((n : ℚ) : ℝ) := by
      rw [trace_mul_eq_mixedInner x y, hn]; push_cast; ring
    have h2 : (Algebra.trace ℚ K (x * y) : ℚ) = (n : ℚ) := by exact_mod_cast h1
    simpa using h2.symm

end Fermat.TraceForm
