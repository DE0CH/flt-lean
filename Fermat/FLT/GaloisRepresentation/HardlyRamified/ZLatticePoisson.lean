/-
n-dimensional Poisson summation at the Gaussian — the ℤ-lattice theta
transformation law.  Helper module for the sorried leaf
`zlattice_theta_transform` of
`Fermat.FLT.GaloisRepresentation.HardlyRamified.ModThree`.
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The theta transformation law for `ℤ`-lattices

For a full-rank `ℤ`-lattice `L` in a finite-dimensional real inner
product space `E` (with its canonical Lebesgue measure) and `t > 0`,

`∑_{v ∈ L} exp (−π t⁻¹ ‖v‖²)
    = covol(L)⁻¹ · t^{n/2} · ∑_{w ∈ L∨} exp (−π t ‖w‖²)`,

where `n = dim_ℝ E` and `L∨` is the dual lattice of `L` under the
inner product.  This is Poisson summation at the Gaussian
`exp (−π t⁻¹ ‖·‖²)`.

The proof is genuine `n`-dimensional Poisson summation, built from
mathlib's multivariate Fourier series on the unit torus
(`Mathlib.Analysis.Fourier.AddCircleMulti`) together with
`n`-dimensional Gaussian Fourier self-duality
(`fourier_gaussian_innerProductSpace`):

1. periodize the Gaussian `g = exp (−a ‖·‖²)` over `L` and pull it
   back to the unit torus `(ℝ/ℤ)^ι` along a `ℤ`-basis of `L`
   (`torusGaussian`);
2. compute its multivariate Fourier coefficients: unfolding the
   integral over a fundamental domain of `L` shows the `k`-th
   coefficient equals `covol(L)⁻¹ · 𝓕 g (w_k)`, where `w_k` is the
   point of the dual lattice indexed by `k` in the dual basis
   (`mFourierCoeff_torusGaussian`);
3. the coefficients decay like a Gaussian along the dual lattice, so
   they are summable and the Fourier series converges pointwise
   (`UnitAddTorus.hasSum_mFourier_series_apply_of_summable`);
   evaluating at `0` yields the transformation law
   (`ZLatticePoisson.zlattice_theta_transform`).
-/

@[expose] public section

open MeasureTheory Submodule Module UnitAddTorus
open scoped Real RealInnerProductSpace FourierTransform NNReal ENNReal

namespace ZLatticePoisson

local instance : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩

/-! ## Summability lemmas -/

/-- Geometric-comparison summability of the one-dimensional Gaussian
over `ℤ`. -/
theorem summable_exp_neg_int_sq {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℤ => Real.exp (-c * (m : ℝ) ^ 2) := by
  have key : ∀ n : ℕ, Real.exp (-c * (n : ℝ) ^ 2) ≤ Real.exp (-c) ^ n := by
    intro n
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h2 : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
      exact_mod_cast h2
    nlinarith [hn, hc]
  have hgeo : Summable fun n : ℕ => Real.exp (-c) ^ n :=
    summable_geometric_of_lt_one (Real.exp_nonneg _)
      (by rw [Real.exp_lt_one_iff]; linarith)
  refine Summable.of_nat_of_neg ?_ ?_
  · exact Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) key hgeo
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeo
    simpa using key n

/-- Summability over `ι → ℤ` (`ι` finite) of a product of nonnegative
summable one-variable factors, by induction on the cardinality. -/
theorem summable_pi_int_prod {ι : Type*} [Fintype ι] {f : ℤ → ℝ}
    (hf0 : ∀ m, 0 ≤ f m) (hf : Summable f) :
    Summable fun m : ι → ℤ => ∏ i, f (m i) := by
  have key : ∀ n : ℕ, Summable fun m : Fin n → ℤ => ∏ i, f (m i) := by
    intro n
    induction n with
    | zero =>
      have h : (fun m : Fin 0 → ℤ => ∏ i, f (m i)) = fun _ => 1 := by
        funext m; simp
      rw [h]
      exact .of_finite
    | succ n ih =>
      have hprod : Summable fun p : (Fin n → ℤ) × ℤ => (∏ i, f (p.1 i)) * f p.2 :=
        ih.mul_of_nonneg hf (fun m => Finset.prod_nonneg fun i _ => hf0 _) hf0
      refine (Equiv.summable_iff (Fin.succFunEquiv ℤ n).symm).mp (hprod.congr fun p => ?_)
      show (∏ i, f (p.1 i)) * f p.2 = ∏ i : Fin (n + 1), f ((Fin.succFunEquiv ℤ n).symm p i)
      have happ : ((Fin.succFunEquiv ℤ n).symm p) = Fin.append p.1 (fun _ => p.2) := by
        have hu : (uniqueElim p.2 : Fin 1 → ℤ) = fun _ => p.2 :=
          funext fun j => uniqueElim_const _ _
        funext i
        simp [Fin.succFunEquiv, Fin.appendEquiv, hu]
      rw [happ, Fin.prod_univ_add (f := fun i => f (Fin.append p.1 (fun _ => p.2) i))]
      simp [Fin.append_left, Fin.append_right]
  have h2 : Summable fun m : Fin (Fintype.card ι) → ℤ =>
      ∏ i : ι, f (m (Fintype.equivFin ι i)) :=
    (key _).congr fun m => ((Fintype.equivFin ι).prod_comp fun j => f (m j)).symm
  refine (Equiv.summable_iff ((Fintype.equivFin ι).arrowCongr (Equiv.refl ℤ)).symm).mp
    (h2.congr fun m => ?_)
  exact Finset.prod_congr rfl fun i _ => by simp [Equiv.arrowCongr]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Gaussian summability over the `ℤ`-span of an `ℝ`-basis, in
coordinates: the quadratic form `‖∑ mᵢ • cᵢ‖²` dominates a positive
multiple of `∑ mᵢ²` (anti-Lipschitz bound for the coordinate
isomorphism), so the Gaussian is dominated by a summable product of
one-dimensional Gaussians. -/
theorem summable_exp_neg_zspan_sq {ι : Type*} [Fintype ι]
    (c : Basis ι ℝ E) {a : ℝ} (ha : 0 < a) :
    Summable fun m : ι → ℤ => Real.exp (-a * ‖∑ i, (m i : ℝ) • c i‖ ^ 2) := by
  set C : ℝ := max ‖(c.equivFunL : E →L[ℝ] (ι → ℝ))‖ 1 with hC_def
  have hx : ∀ x : ι → ℝ, ‖x‖ ≤ C * ‖c.equivFun.symm x‖ := by
    intro x
    have h1 : c.equivFunL (c.equivFun.symm x) = x := by
      show c.equivFun (c.equivFun.symm x) = x
      exact c.equivFun.apply_symm_apply x
    calc ‖x‖ = ‖c.equivFunL (c.equivFun.symm x)‖ := by rw [h1]
      _ ≤ ‖(c.equivFunL : E →L[ℝ] (ι → ℝ))‖ * ‖c.equivFun.symm x‖ := by
          exact ContinuousLinearMap.le_opNorm
            (c.equivFunL : E →L[ℝ] (ι → ℝ)) (c.equivFun.symm x)
      _ ≤ C * ‖c.equivFun.symm x‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  set n1 : ℝ := (Fintype.card ι : ℝ) + 1 with hn1_def
  have hn1 : (0 : ℝ) < n1 := by positivity
  set a' : ℝ := a / (C ^ 2 * n1) with ha'_def
  have ha' : 0 < a' := by positivity
  have hbound : ∀ m : ι → ℤ,
      Real.exp (-a * ‖∑ i, (m i : ℝ) • c i‖ ^ 2) ≤ ∏ i, Real.exp (-a' * (m i : ℝ) ^ 2) := by
    intro m
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    have hSx : c.equivFun.symm (fun i => (m i : ℝ)) = ∑ i, (m i : ℝ) • c i := by
      rw [Basis.equivFun_symm_apply]
    have h1 : ‖(fun i => (m i : ℝ))‖ ≤ C * ‖∑ i, (m i : ℝ) • c i‖ := by
      rw [← hSx]; exact hx _
    have h2 : ∑ i, (m i : ℝ) ^ 2 ≤ n1 * ‖(fun i => (m i : ℝ))‖ ^ 2 := by
      have hterm : ∀ i : ι, (m i : ℝ) ^ 2 ≤ ‖(fun i => (m i : ℝ))‖ ^ 2 := by
        intro i
        have h3 : ‖(fun i => (m i : ℝ)) i‖ ≤ ‖(fun i => (m i : ℝ))‖ :=
          norm_le_pi_norm (fun i => (m i : ℝ)) i
        have h4 : ‖(fun i => (m i : ℝ)) i‖ = |(m i : ℝ)| := by simp
        rw [h4] at h3
        nlinarith [h3, sq_abs ((m i : ℝ)), abs_nonneg ((m i : ℝ))]
      calc ∑ i, (m i : ℝ) ^ 2 ≤ ∑ _i : ι, ‖(fun i => (m i : ℝ))‖ ^ 2 :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = (Fintype.card ι : ℝ) * ‖(fun i => (m i : ℝ))‖ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ n1 * ‖(fun i => (m i : ℝ))‖ ^ 2 := by
            have hle : (Fintype.card ι : ℝ) ≤ n1 := by rw [hn1_def]; linarith
            nlinarith [hle, sq_nonneg ‖(fun i => (m i : ℝ))‖]
    have h3 : ‖(fun i => (m i : ℝ))‖ ^ 2 ≤ C ^ 2 * ‖∑ i, (m i : ℝ) • c i‖ ^ 2 := by
      nlinarith [h1, norm_nonneg (fun i => (m i : ℝ)), norm_nonneg (∑ i, (m i : ℝ) • c i)]
    have hsum : ∑ i, (-a' * (m i : ℝ) ^ 2) = -(a' * ∑ i, (m i : ℝ) ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    have h4 : a' * ∑ i, (m i : ℝ) ^ 2 ≤ a * ‖∑ i, (m i : ℝ) • c i‖ ^ 2 := by
      have h5 : a' * ∑ i, (m i : ℝ) ^ 2 ≤ a' * (n1 * ‖(fun i => (m i : ℝ))‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 ha'.le
      have h6 : a' * (n1 * ‖(fun i => (m i : ℝ))‖ ^ 2)
          ≤ a' * (n1 * (C ^ 2 * ‖∑ i, (m i : ℝ) • c i‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hn1.le) ha'.le
      have h7 : a' * (n1 * (C ^ 2 * ‖∑ i, (m i : ℝ) • c i‖ ^ 2))
          = a * ‖∑ i, (m i : ℝ) • c i‖ ^ 2 := by
        have hCn : C ^ 2 * n1 ≠ 0 := by positivity
        rw [ha'_def, div_mul_eq_mul_div, div_eq_iff hCn]
        ring
      linarith [h5, h6, h7]
    linarith [h4]
  refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hbound ?_
  exact summable_pi_int_prod (f := fun z : ℤ => Real.exp (-a' * (z : ℝ) ^ 2))
    (fun z => (Real.exp_pos _).le) (summable_exp_neg_int_sq ha')

omit [MeasurableSpace E] [BorelSpace E] in
/-- Gaussian summability over a `ℤ`-lattice: reindex
`summable_exp_neg_zspan_sq` along a `ℤ`-basis of `L`. -/
theorem summable_exp_neg_norm_sq (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {a : ℝ} (ha : 0 < a) :
    Summable fun v : L => Real.exp (-a * ‖(v : E)‖ ^ 2) := by
  classical
  set b := Module.Free.chooseBasis ℤ L with hb
  have hcoe : ∀ m : Module.Free.ChooseBasisIndex ℤ L → ℤ,
      ((b.equivFun.symm m : L) : E) = ∑ i, (m i : ℝ) • b.ofZLatticeBasis ℝ L i := by
    intro m
    rw [Basis.equivFun_symm_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SetLike.val_smul, Basis.ofZLatticeBasis_apply, ← Int.cast_smul_eq_zsmul ℝ]
  refine (Equiv.summable_iff b.equivFun.symm.toEquiv).mp ?_
  refine (summable_exp_neg_zspan_sq (b.ofZLatticeBasis ℝ L) ha).congr fun m => ?_
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv]
  rw [hcoe m]

/-! ## The periodized Gaussian -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- Continuity of the `L`-periodization of the Gaussian
`exp (−a ‖·‖²)`: on every metric ball the series is uniformly
dominated by a summable Gaussian along `L`. -/
theorem continuous_periodization (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {a : ℝ} (ha : 0 < a) :
    Continuous fun u : E => ∑' v : L, Complex.exp (-(a : ℂ) * ‖u + (v : E)‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  set R : ℝ := ‖u₀‖ + 1 with hR_def
  have hR : 0 < R := by positivity
  have hmem : u₀ ∈ Metric.ball (0 : E) R := by
    simp only [Metric.mem_ball, dist_zero_right, hR_def]
    linarith
  refine ContinuousOn.continuousAt ?_ (Metric.isOpen_ball.mem_nhds hmem)
  refine continuousOn_tsum
    (u := fun v : L => Real.exp (2 * a * R ^ 2) * Real.exp (-(a / 2) * ‖(v : E)‖ ^ 2))
    (fun v => Continuous.continuousOn (by fun_prop))
    ((summable_exp_neg_norm_sq L (by positivity : (0:ℝ) < a / 2)).mul_left _) ?_
  intro v u hu
  have hu' : ‖u‖ ≤ R := by
    have h := Metric.mem_ball.mp hu
    rw [dist_zero_right] at h
    exact h.le
  have hnorm : ‖Complex.exp (-(a : ℂ) * ‖u + (v : E)‖ ^ 2)‖
      = Real.exp (-a * ‖u + (v : E)‖ ^ 2) := by
    rw [show (-(a : ℂ) * (‖u + (v : E)‖ : ℂ) ^ 2)
        = ((-a * ‖u + (v : E)‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_exp, Complex.ofReal_re]
  rw [hnorm, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : ‖(v : E)‖ ≤ ‖u + (v : E)‖ + R := by
    have h2 : (v : E) = (u + (v : E)) - u := by abel
    calc ‖(v : E)‖ = ‖(u + (v : E)) - u‖ := by rw [← h2]
      _ ≤ ‖u + (v : E)‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ ‖u + (v : E)‖ + R := by linarith
  have h2 : ‖(v : E)‖ ^ 2 ≤ (‖u + (v : E)‖ + R) ^ 2 := by
    nlinarith [h1, hR, hu', norm_nonneg (v : E), norm_nonneg (u + (v : E))]
  nlinarith [h2, ha, hR, sq_nonneg (‖u + (v : E)‖ - R), norm_nonneg (u + (v : E))]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The periodization of the Gaussian is `L`-periodic. -/
theorem periodization_vadd (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (a : ℝ) (v₀ : L) (u : E) :
    ∑' v : L, Complex.exp (-(a : ℂ) * ‖(u + (v₀ : E)) + (v : E)‖ ^ 2) =
      ∑' v : L, Complex.exp (-(a : ℂ) * ‖u + (v : E)‖ ^ 2) := by
  rw [← Equiv.tsum_eq (Equiv.addLeft v₀)
    (fun v : L => Complex.exp (-(a : ℂ) * ‖u + (v : E)‖ ^ 2))]
  refine tsum_congr fun v => ?_
  have harg : u + ((Equiv.addLeft v₀ v : L) : E) = (u + (v₀ : E)) + (v : E) := by
    have : ((Equiv.addLeft v₀ v : L) : E) = (v₀ : E) + (v : E) := by
      simp [Equiv.coe_addLeft]
    rw [this]
    abel
  rw [harg]

/-! ## Unfolding over a fundamental domain -/

/-- The integral of `character × periodization` over a fundamental
domain of `L` is the Fourier integral of the Gaussian at the
dual-lattice point `w`: unfold `∫_E = ∑_{m ∈ L} ∫_{FD}` for the
integrable function `χ_w · g`, use `⟪m, w⟫ ∈ ℤ` to strip the character
along `L`, and swap the sum and the integral (justified by the same
unfolding for `∫⁻ ‖g‖`). -/
theorem setIntegral_char_mul_periodization {ι : Type*} [Fintype ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (c : Basis ι ℝ E) (hc : span ℤ (Set.range c) = L)
    {a : ℝ} (ha : 0 < a) {w : E}
    (hw : w ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L) :
    ∫ u in ZSpan.fundamentalDomain c,
        Complex.exp (((-2 * Real.pi * ⟪u, w⟫ : ℝ) : ℂ) * Complex.I) *
          ∑' v : L, Complex.exp (-(a : ℂ) * ‖u + (v : E)‖ ^ 2) =
      𝓕 (fun v : E => Complex.exp (-(a : ℂ) * ‖v‖ ^ 2)) w := by
  classical
  set g : E → ℂ := fun v => Complex.exp (-(a : ℂ) * ‖v‖ ^ 2) with hg_def
  set χ : E → ℂ :=
    fun u => Complex.exp (((-2 * Real.pi * ⟪u, w⟫ : ℝ) : ℂ) * Complex.I) with hχ_def
  show (∫ u in ZSpan.fundamentalDomain c, χ u * ∑' v : L, g (u + (v : E))) = 𝓕 g w
  set φ : E → ℂ := fun v => χ v * g v with hφ_def
  have hχ_cont : Continuous χ := by fun_prop
  have hχ_norm : ∀ u, ‖χ u‖ = 1 := fun u => Complex.norm_exp_ofReal_mul_I _
  have hgi : Integrable g := by
    have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (V := E) (b := (a : ℂ)) (by simpa using ha) 0 0
    rw [hg_def]
    simpa [neg_mul] using h
  have hφi : Integrable φ :=
    hgi.bdd_mul hχ_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => (hχ_norm u).le)
  have hFD : IsAddFundamentalDomain L (ZSpan.fundamentalDomain c) volume := by
    have h := ZSpan.isAddFundamentalDomain c (volume : Measure E)
    rwa [hc] at h
  haveI : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  haveI : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  have h𝓕 : 𝓕 g w = ∫ v, φ v := by
    rw [Real.fourier_eq']
    simp only [smul_eq_mul]
    rfl
  have hvadd : ∀ (m : L) (u : E), (m +ᵥ u : E) = (m : E) + u := fun _ _ => rfl
  have hunfold : ∫ v, φ v =
      ∑' m : L, ∫ u in ZSpan.fundamentalDomain c, φ ((m : E) + u) := by
    have h := hFD.integral_eq_tsum'' φ hφi
    simpa [hvadd] using h
  have hchar : ∀ (m : L) (u : E), φ ((m : E) + u) = χ u * g ((m : E) + u) := by
    intro m u
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (hw (m : E) m.2)
    have hzin : ⟪(m : E), w⟫ = (z : ℝ) := by
      rw [real_inner_comm]
      have hz' : ((z : ℝ)) = ⟪w, (m : E)⟫ := by simpa using hz
      exact hz'.symm
    show χ ((m : E) + u) * g ((m : E) + u) = χ u * g ((m : E) + u)
    congr 1
    rw [hχ_def]
    simp only []
    rw [inner_add_left, hzin]
    rw [show (((-2 * Real.pi * ((z : ℝ) + ⟪u, w⟫) : ℝ) : ℂ) * Complex.I)
        = ((-2 * Real.pi * ⟪u, w⟫ : ℝ) : ℂ) * Complex.I
          + ((-z : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hswap : ∑' m : L, ∫ u in ZSpan.fundamentalDomain c, χ u * g ((m : E) + u) =
      ∫ u in ZSpan.fundamentalDomain c, ∑' m : L, χ u * g ((m : E) + u) := by
    refine (integral_tsum (fun m => Continuous.aestronglyMeasurable (by fun_prop)) ?_).symm
    have hnorm_eq : ∀ (m : L) (u : E), ‖χ u * g ((m : E) + u)‖ₑ = ‖φ ((m : E) + u)‖ₑ := by
      intro m u; rw [← hchar]
    calc ∑' m : L, ∫⁻ u in ZSpan.fundamentalDomain c, ‖χ u * g ((m : E) + u)‖ₑ
        = ∑' m : L, ∫⁻ u in ZSpan.fundamentalDomain c, ‖φ ((m : E) + u)‖ₑ :=
          tsum_congr fun m => lintegral_congr fun u => hnorm_eq m u
      _ = ∫⁻ u, ‖φ u‖ₑ := by
          have h := hFD.lintegral_eq_tsum'' fun u => ‖φ u‖ₑ
          simpa [hvadd] using h.symm
      _ ≠ ⊤ := hφi.2.ne
  have hpull : ∀ u : E, ∑' m : L, χ u * g ((m : E) + u) =
      χ u * ∑' v : L, g (u + (v : E)) := by
    intro u
    rw [tsum_mul_left]
    congr 1
    exact tsum_congr fun m => by rw [add_comm ((m : E)) u]
  calc ∫ u in ZSpan.fundamentalDomain c, χ u * ∑' v : L, g (u + (v : E))
      = ∫ u in ZSpan.fundamentalDomain c, ∑' m : L, χ u * g ((m : E) + u) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show χ u * ∑' v : L, g (u + (v : E)) = ∑' m : L, χ u * g ((m : E) + u)
        exact (hpull u).symm
    _ = ∑' m : L, ∫ u in ZSpan.fundamentalDomain c, χ u * g ((m : E) + u) := hswap.symm
    _ = ∑' m : L, ∫ u in ZSpan.fundamentalDomain c, φ ((m : E) + u) :=
        tsum_congr fun m =>
          integral_congr_ae (Filter.Eventually.of_forall fun u => (hchar m u).symm)
    _ = ∫ v, φ v := hunfold.symm
    _ = 𝓕 g w := h𝓕.symm

/-! ## The torus Gaussian -/

/-- The `L`-periodized Gaussian pulled back to the unit torus along the
coordinates of the `ℝ`-basis `c` (a `ℤ`-basis of `L`): the value at
`x` is `∑_{v ∈ L} exp (−a ‖(∑ x̃ᵢ cᵢ) + v‖²)` where `x̃ᵢ ∈ [0,1)` is
the canonical representative of `xᵢ`. -/
noncomputable def torusGaussian {ι : Type*} [Fintype ι] (L : Submodule ℤ E)
    (c : Basis ι ℝ E) (a : ℝ) (x : UnitAddTorus ι) : ℂ :=
  ∑' v : L, Complex.exp (-(a : ℂ) *
    ‖c.equivFun.symm (fun i => ((AddCircle.equivIco 1 0 (x i) : ℝ))) + (v : E)‖ ^ 2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Evaluation of `torusGaussian` at the class of a concrete point
`x : ι → ℝ`: the `[0,1)`-representative differs from `x` by an element
of `L`, so the periodization takes the same value at both. -/
theorem torusGaussian_coe {ι : Type*} [Fintype ι] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (c : Basis ι ℝ E) (hc : span ℤ (Set.range c) = L) (a : ℝ) (x : ι → ℝ) :
    torusGaussian L c a (fun i => ((x i : ℝ) : AddCircle (1 : ℝ))) =
      ∑' v : L, Complex.exp (-(a : ℂ) * ‖c.equivFun.symm x + (v : E)‖ ^ 2) := by
  classical
  have key : ∀ i : ι, ∃ z : ℤ,
      ((AddCircle.equivIco 1 0 (((x i : ℝ) : AddCircle (1 : ℝ))) : ℝ)) = x i + z := by
    intro i
    have h1 : (((AddCircle.equivIco 1 0 (((x i : ℝ) : AddCircle (1 : ℝ)))) : ℝ) :
        AddCircle (1 : ℝ)) = ((x i : ℝ) : AddCircle (1 : ℝ)) :=
      AddCircle.coe_equivIco
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h1)
    refine ⟨-z, ?_⟩
    have hz' : (z : ℝ) =
        -((AddCircle.equivIco 1 0 (((x i : ℝ) : AddCircle (1 : ℝ))) : ℝ)) + x i := by
      simpa [zsmul_eq_mul] using hz
    push_cast
    linarith [hz']
  choose z hz using key
  have harg : (fun i => ((AddCircle.equivIco 1 0 (((x i : ℝ) : AddCircle (1 : ℝ))) : ℝ)))
      = fun i => x i + ((z i : ℝ)) := funext hz
  show (∑' v : L, Complex.exp (-(a : ℂ) *
      ‖c.equivFun.symm (fun i =>
        ((AddCircle.equivIco 1 0 (((x i : ℝ) : AddCircle (1 : ℝ))) : ℝ))) + (v : E)‖ ^ 2)) = _
  rw [harg]
  have hsplit : c.equivFun.symm (fun i => x i + (z i : ℝ))
      = c.equivFun.symm x + c.equivFun.symm (fun i => (z i : ℝ)) := by
    rw [← map_add]
    rfl
  have hmem : c.equivFun.symm (fun i => (z i : ℝ)) ∈ L := by
    rw [← hc, Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  rw [hsplit]
  exact periodization_vadd L a ⟨_, hmem⟩ (c.equivFun.symm x)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Continuity of `torusGaussian`, by descending the continuous
periodization along the open quotient map `(ι → ℝ) → (ℝ/ℤ)^ι`. -/
theorem continuous_torusGaussian {ι : Type*} [Fintype ι] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (c : Basis ι ℝ E) (hc : span ℤ (Set.range c) = L) {a : ℝ} (ha : 0 < a) :
    Continuous (torusGaussian L c a) := by
  have hmk : IsOpenQuotientMap
      (fun (x : ι → ℝ) => (fun i => ((x i : ℝ) : AddCircle (1 : ℝ)))) :=
    IsOpenQuotientMap.piMap fun i => QuotientAddGroup.isOpenQuotientMap_mk
  rw [← hmk.continuous_comp_iff]
  have heq : (torusGaussian L c a) ∘
      (fun (x : ι → ℝ) => (fun i => ((x i : ℝ) : AddCircle (1 : ℝ))))
      = fun x : ι → ℝ =>
          ∑' v : L, Complex.exp (-(a : ℂ) * ‖c.equivFun.symm x + (v : E)‖ ^ 2) :=
    funext fun x => torusGaussian_coe L c hc a x
  rw [heq]
  exact (continuous_periodization L ha).comp
    (LinearMap.continuous_of_finiteDimensional
      (c.equivFun.symm : (ι → ℝ) →ₗ[ℝ] E))

/-- The multivariate Fourier character at the class of a concrete
point, as a complex exponential. -/
theorem mFourier_neg_coe {ι : Type*} [Fintype ι] (k : ι → ℤ) (x : ι → ℝ) :
    mFourier (-k) (fun i => ((x i : ℝ) : AddCircle (1 : ℝ))) =
      Complex.exp (((-2 * Real.pi * ∑ i, (k i : ℝ) * x i : ℝ) : ℂ) * Complex.I) := by
  show (∏ i, fourier ((-k) i) (((x i : ℝ) : AddCircle (1 : ℝ)))) = _
  have h1 : ∀ i : ι, fourier ((-k) i) (((x i : ℝ) : AddCircle (1 : ℝ)))
      = Complex.exp (((-2 * Real.pi * ((k i : ℝ) * x i) : ℝ) : ℂ) * Complex.I) := by
    intro i
    rw [fourier_coe_apply]
    congr 1
    simp only [Pi.neg_apply]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => h1 i, ← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 2
  rw [Finset.mul_sum]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Inner product of a coordinate vector against an integer combination
of the dual basis: `⟪∑ xⱼ cⱼ, ∑ kᵢ Dᵢ⟫ = ∑ kᵢ xᵢ`. -/
theorem inner_equivFun_symm_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hN : (innerₗ E).Nondegenerate) (c : Basis ι ℝ E) (k : ι → ℤ) (x : ι → ℝ) :
    ⟪c.equivFun.symm x,
        ∑ i, (k i : ℝ) • LinearMap.BilinForm.dualBasis (innerₗ E) hN c i⟫
      = ∑ i, (k i : ℝ) * x i := by
  have hd : ∀ i j : ι,
      ⟪c j, LinearMap.BilinForm.dualBasis (innerₗ E) hN c i⟫
        = if j = i then 1 else 0 := by
    intro i j
    rw [real_inner_comm]
    exact LinearMap.BilinForm.apply_dualBasis_left hN c i j
  rw [Basis.equivFun_symm_apply, sum_inner]
  have hj : ∀ j : ι,
      ⟪x j • c j, ∑ i, (k i : ℝ) • LinearMap.BilinForm.dualBasis (innerₗ E) hN c i⟫
        = (k j : ℝ) * x j := by
    intro j
    rw [real_inner_smul_left, inner_sum]
    simp only [real_inner_smul_right, hd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [mul_comm]
  rw [Finset.sum_congr rfl fun j _ => hj j]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The integer combinations of the dual basis lie in the dual
lattice. -/
theorem sum_dualBasis_mem_dualSubmodule {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ E) (hN : (innerₗ E).Nondegenerate) (c : Basis ι ℝ E)
    (hc : span ℤ (Set.range c) = L) (k : ι → ℤ) :
    (∑ i, (k i : ℝ) • LinearMap.BilinForm.dualBasis (innerₗ E) hN c i)
      ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by
  rw [← hc, LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ E) hN c]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Nondegeneracy of the real inner product as a bilinear form. -/
theorem innerₗ_nondegenerate : (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro y hy
    exact inner_self_eq_zero.mp (hy y)

/-! ## The Fourier coefficients of the torus Gaussian -/

/-- The multivariate Fourier coefficients of the torus Gaussian: the
`k`-th coefficient is `covol(L)⁻¹` times the Fourier integral of the
Gaussian at the dual-lattice point `∑ kᵢ • Dᵢ` (`D` the dual basis of
`c`).  Proved by unfolding the torus integral to the `Ioc`-unit box,
passing to the `Ico` box (the boundary is null), transporting along
the coordinate isomorphism onto the `ZSpan` fundamental domain (the
Jacobian is `covol(L)⁻¹` by uniqueness of additive Haar measure), and
applying `setIntegral_char_mul_periodization`. -/
theorem mFourierCoeff_torusGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (c : Basis ι ℝ E) (hc : span ℤ (Set.range c) = L)
    (hN : (innerₗ E).Nondegenerate) {a : ℝ} (ha : 0 < a) (k : ι → ℤ) :
    mFourierCoeff (torusGaussian L c a) k =
      (ZLattice.covolume L)⁻¹ •
        𝓕 (fun v : E => Complex.exp (-(a : ℂ) * ‖v‖ ^ 2))
          (∑ i, (k i : ℝ) • LinearMap.BilinForm.dualBasis (innerₗ E) hN c i) := by
  classical
  set w : E := ∑ i, (k i : ℝ) • LinearMap.BilinForm.dualBasis (innerₗ E) hN c i with hw_def
  have hw_mem : w ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by
    rw [hw_def]; exact sum_dualBasis_mem_dualSubmodule L hN c hc k
  set h : E → ℂ := fun u =>
    Complex.exp (((-2 * Real.pi * ⟪u, w⟫ : ℝ) : ℂ) * Complex.I) *
      ∑' v : L, Complex.exp (-(a : ℂ) * ‖u + (v : E)‖ ^ 2) with hh_def
  have hh_cont : Continuous h := by
    refine Continuous.mul ?_ (continuous_periodization L ha)
    fun_prop
  -- Step A: the coefficient as an `Ioc`-box integral of `h ∘ CV`.
  have hstepA : mFourierCoeff (torusGaussian L c a) k =
      ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ℝ)) (0 + 1)},
        h (c.equivFun.symm x) := by
    rw [mFourierCoeff_eq_integral (torusGaussian L c a) k fun _ => (0 : ℝ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (mFourier (-k)) (fun i => ((x i : ℝ) : AddCircle (1 : ℝ))) •
        torusGaussian L c a (fun i => ((x i : ℝ) : AddCircle (1 : ℝ)))
      = h (c.equivFun.symm x)
    rw [smul_eq_mul, mFourier_neg_coe, torusGaussian_coe L c hc a x]
    have hinner : ⟪c.equivFun.symm x, w⟫ = ∑ i, (k i : ℝ) * x i := by
      rw [hw_def]; exact inner_equivFun_symm_dual hN c k x
    show Complex.exp (((-2 * Real.pi * ∑ i, (k i : ℝ) * x i : ℝ) : ℂ) * Complex.I) *
        (∑' v : L, Complex.exp (-(a : ℂ) * ‖c.equivFun.symm x + (v : E)‖ ^ 2))
      = Complex.exp (((-2 * Real.pi * ⟪c.equivFun.symm x, w⟫ : ℝ) : ℂ) * Complex.I) *
        ∑' v : L, Complex.exp (-(a : ℂ) * ‖c.equivFun.symm x + (v : E)‖ ^ 2)
    rw [hinner]
  -- Step B: pass from the `Ioc` box to the `Ico` box.
  have hres : (volume : Measure (ι → ℝ)).restrict
        {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ℝ)) (0 + 1)}
      = volume.restrict {x : ι → ℝ | ∀ i, x i ∈ Set.Ico ((0 : ℝ)) 1} := by
    refine Measure.restrict_congr_set ?_
    have hnull : (volume : Measure (ι → ℝ))
        (⋃ i : ι, ({x : ι → ℝ | x i = 0} ∪ {x : ι → ℝ | x i = 1})) = 0 := by
      refine measure_iUnion_null fun i => measure_union_null ?_ ?_ <;>
        · rw [volume_pi]
          exact Measure.pi_hyperplane _ i _
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null ?_ hnull
      rintro x ⟨hx1, hx2⟩
      rw [Set.mem_setOf_eq, not_forall] at hx2
      obtain ⟨i, hi⟩ := hx2
      have h1 := hx1 i
      simp only [Set.mem_Ioc, zero_add] at h1
      simp only [Set.mem_Ico, not_and, not_lt] at hi
      refine Set.mem_iUnion.mpr ⟨i, Or.inr ?_⟩
      have : (1 : ℝ) ≤ x i := hi h1.1.le
      exact le_antisymm h1.2 this |>.symm ▸ rfl
    · refine measure_mono_null ?_ hnull
      rintro x ⟨hx1, hx2⟩
      rw [Set.mem_setOf_eq, not_forall] at hx2
      obtain ⟨i, hi⟩ := hx2
      have h1 := hx1 i
      simp only [Set.mem_Ico] at h1
      simp only [Set.mem_Ioc, zero_add, not_and, not_le] at hi
      refine Set.mem_iUnion.mpr ⟨i, Or.inl ?_⟩
      rcases lt_or_eq_of_le h1.1 with h2 | h2
      · exact absurd (hi h2) (not_lt.mpr h1.2.le)
      · exact h2.symm
  -- Step C: transport along the coordinate isomorphism.
  have hCVcont : Continuous ⇑(c.equivFun.symm) :=
    LinearMap.continuous_of_finiteDimensional
      (c.equivFun.symm : (ι → ℝ) →ₗ[ℝ] E)
  have hCVinv_cont : Continuous ⇑(c.equivFun) :=
    LinearMap.continuous_of_finiteDimensional (c.equivFun : E →ₗ[ℝ] (ι → ℝ))
  have hCVmeas : Measurable ⇑(c.equivFun.symm) := hCVcont.measurable
  haveI hHaar :
      (Measure.map (⇑(c.equivFun.symm)) (volume : Measure (ι → ℝ))).IsAddHaarMeasure := by
    have h := (c.equivFun.symm.toAddEquiv).isAddHaarMeasure_map
      (volume : Measure (ι → ℝ)) hCVcont (by simpa using hCVinv_cont)
    simpa using h
  set κ : ℝ≥0 := Measure.addHaarScalarFactor
    (Measure.map (⇑(c.equivFun.symm)) (volume : Measure (ι → ℝ)))
    (volume : Measure E) with hκ_def
  have huniq : Measure.map (⇑(c.equivFun.symm)) (volume : Measure (ι → ℝ)) =
      κ • (volume : Measure E) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hpre : ⇑(c.equivFun.symm) ⁻¹' (ZSpan.fundamentalDomain c)
      = {x : ι → ℝ | ∀ i, x i ∈ Set.Ico ((0 : ℝ)) 1} := by
    ext x
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, Set.mem_setOf_eq]
    refine forall_congr' fun i => ?_
    have hrepr : c.repr (c.equivFun.symm x) i = x i := by
      have h1 : c.equivFun (c.equivFun.symm x) = x := c.equivFun.apply_symm_apply x
      calc c.repr (c.equivFun.symm x) i
          = c.equivFun (c.equivFun.symm x) i := by rw [Basis.equivFun_apply]
        _ = x i := by rw [h1]
    rw [hrepr]
  have hFDmeas : MeasurableSet (ZSpan.fundamentalDomain c) :=
    ZSpan.fundamentalDomain_measurableSet c
  have hvolbox :
      (volume : Measure (ι → ℝ)) {x : ι → ℝ | ∀ i, x i ∈ Set.Ico ((0 : ℝ)) 1} = 1 := by
    have hbox : {x : ι → ℝ | ∀ i, x i ∈ Set.Ico ((0 : ℝ)) 1}
        = Set.pi Set.univ fun _ : ι => Set.Ico (0 : ℝ) 1 := by
      ext x; simp [Set.mem_pi]
    rw [hbox, volume_pi_pi]
    simp [Real.volume_Ico]
  have hκ1 : (κ : ℝ≥0∞) * (volume : Measure E) (ZSpan.fundamentalDomain c) = 1 := by
    have h1 : Measure.map (⇑(c.equivFun.symm)) (volume : Measure (ι → ℝ))
        (ZSpan.fundamentalDomain c) = 1 := by
      rw [Measure.map_apply hCVmeas hFDmeas, hpre, hvolbox]
    rw [huniq] at h1
    simpa [Measure.smul_apply, smul_eq_mul] using h1
  have hFD : IsAddFundamentalDomain L (ZSpan.fundamentalDomain c)
      (volume : Measure E) := by
    have h := ZSpan.isAddFundamentalDomain c (volume : Measure E)
    rwa [hc] at h
  have hcovol : ZLattice.covolume L
      = ((volume : Measure E) (ZSpan.fundamentalDomain c)).toReal := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hFD, measureReal_def]
  have hκreal : (κ : ℝ) = (ZLattice.covolume L)⁻¹ := by
    have h1 : (κ : ℝ) * ZLattice.covolume L = 1 := by
      have h2 := congrArg ENNReal.toReal hκ1
      rw [ENNReal.toReal_mul, ENNReal.toReal_one, ENNReal.coe_toReal] at h2
      rw [hcovol]
      exact h2
    have hpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
    field_simp [hpos.ne']
    linarith [h1]
  have hstepC : ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Set.Ico ((0 : ℝ)) 1},
        h (c.equivFun.symm x)
      = (κ : ℝ) • ∫ u in ZSpan.fundamentalDomain c, h u := by
    rw [← hpre,
      ← MeasureTheory.setIntegral_map hFDmeas hh_cont.aestronglyMeasurable
        hCVmeas.aemeasurable,
      huniq, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  -- Step D: the fundamental-domain integral is the Fourier integral.
  have hstepD : ∫ u in ZSpan.fundamentalDomain c, h u
      = 𝓕 (fun v : E => Complex.exp (-(a : ℂ) * ‖v‖ ^ 2)) w :=
    setIntegral_char_mul_periodization L c hc ha hw_mem
  rw [hstepA, hres, hstepC, hstepD, hκreal]

/-! ## The theta transformation law -/

/-- **`n`-dimensional `ℤ`-lattice Poisson summation — the theta
transformation law.**  For a full-rank `ℤ`-lattice `L` in a
finite-dimensional real inner product space `E` and `t > 0`,
`θ_L(1/t) = covol(L)⁻¹ · t^{n/2} · θ_{L∨}(t)` where
`θ_M(u) = ∑_{v ∈ M} exp (−π u ‖v‖²)` and `L∨` is the dual lattice. -/
theorem zlattice_theta_transform
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (t : ℝ) (ht : 0 < t) :
    ∑' v : L, Real.exp (-Real.pi * t⁻¹ * ‖(v : E)‖ ^ 2) =
      (ZLattice.covolume L)⁻¹ * t ^ ((Module.finrank ℝ E : ℝ) / 2) *
        ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
          Real.exp (-Real.pi * t * ‖(w : E)‖ ^ 2) := by
  classical
  set a : ℝ := Real.pi * t⁻¹ with ha_def
  have ha : 0 < a := by positivity
  set b0 := Module.Free.chooseBasis ℤ L with hb0
  set c := b0.ofZLatticeBasis ℝ L with hc_def
  have hc : span ℤ (Set.range c) = L := b0.ofZLatticeBasis_span ℝ
  have hN : (innerₗ E).Nondegenerate := innerₗ_nondegenerate
  set F : C(UnitAddTorus (Module.Free.ChooseBasisIndex ℤ L), ℂ) :=
    ⟨torusGaussian L c a, continuous_torusGaussian L c hc ha⟩ with hF_def
  -- the real coefficient values
  set r : (Module.Free.ChooseBasisIndex ℤ L → ℤ) → ℝ := fun k =>
    (ZLattice.covolume L)⁻¹ * t ^ ((Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (-Real.pi * t *
        ‖∑ i, (k i : ℝ) • LinearMap.BilinForm.dualBasis (innerₗ E) hN c i‖ ^ 2)
    with hr_def
  have hcoeff : ∀ k, mFourierCoeff (⇑F) k = ((r k : ℝ) : ℂ) := by
    intro k
    have hF_coe : ⇑F = torusGaussian L c a := rfl
    rw [hF_coe, mFourierCoeff_torusGaussian L c hc hN ha k,
      fourier_gaussian_innerProductSpace (by simpa using ha)]
    have hπa : ((Real.pi : ℂ) / ((a : ℝ) : ℂ)) = ((t : ℝ) : ℂ) := by
      rw [ha_def]
      push_cast
      field_simp
    have hcpow : ((t : ℝ) : ℂ) ^ ((Module.finrank ℝ E : ℂ) / 2)
        = ((t ^ ((Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht.le]
      push_cast
      ring_nf
    have hexp : (-(Real.pi : ℂ) ^ 2 *
          (‖∑ i, (k i : ℝ) • LinearMap.BilinForm.dualBasis (innerₗ E) hN c i‖ : ℂ) ^ 2 /
            ((a : ℝ) : ℂ))
        = ((-Real.pi * t *
            ‖∑ i, (k i : ℝ) • LinearMap.BilinForm.dualBasis (innerₗ E) hN c i‖ ^ 2 : ℝ) : ℂ) := by
      rw [ha_def]
      push_cast
      field_simp
    rw [hπa, hcpow, hexp, ← Complex.ofReal_exp, hr_def]
    rw [Complex.real_smul]
    push_cast
    ring
  have hrsummable : Summable r := by
    rw [hr_def]
    refine Summable.mul_left _ ?_
    refine (summable_exp_neg_zspan_sq (E := E)
      (LinearMap.BilinForm.dualBasis (innerₗ E) hN c)
      (mul_pos Real.pi_pos ht)).congr fun m => ?_
    congr 1
    ring
  have hsummable : Summable (mFourierCoeff (⇑F)) := by
    have h1 : mFourierCoeff (⇑F) = fun k => ((r k : ℝ) : ℂ) := funext hcoeff
    rw [h1]
    exact Complex.summable_ofReal.mpr hrsummable
  have hFS := hasSum_mFourier_series_apply_of_summable (f := F) hsummable 0
  have hm1 : ∀ k : Module.Free.ChooseBasisIndex ℤ L → ℤ,
      mFourier k (0 : UnitAddTorus (Module.Free.ChooseBasisIndex ℤ L)) = (1 : ℂ) := by
    intro k
    show (∏ i, fourier (k i)
      ((0 : UnitAddTorus (Module.Free.ChooseBasisIndex ℤ L)) i)) = 1
    simp
  have hF0 : (F 0 : ℂ) = ∑' k, ((r k : ℝ) : ℂ) := by
    rw [← hFS.tsum_eq]
    refine tsum_congr fun k => ?_
    rw [hm1, smul_eq_mul, mul_one, hcoeff]
  -- evaluate `F 0` as the left-hand theta value
  have hzero : (0 : UnitAddTorus (Module.Free.ChooseBasisIndex ℤ L))
      = fun _i => ((0 : ℝ) : AddCircle (1 : ℝ)) := by
    funext i
    exact (QuotientAddGroup.mk_zero _).symm
  have hlhs : (F 0 : ℂ)
      = ((∑' v : L, Real.exp (-Real.pi * t⁻¹ * ‖(v : E)‖ ^ 2) : ℝ) : ℂ) := by
    have hF0' : (F 0 : ℂ) = torusGaussian L c a 0 := rfl
    rw [hF0', hzero, torusGaussian_coe L c hc a fun _ => (0 : ℝ)]
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun v => ?_
    have h0fun : (fun _ : Module.Free.ChooseBasisIndex ℤ L => (0 : ℝ))
        = (0 : Module.Free.ChooseBasisIndex ℤ L → ℝ) := rfl
    have harg : (-(a : ℂ) * (‖(v : E)‖ : ℂ) ^ 2)
        = ((-Real.pi * t⁻¹ * ‖(v : E)‖ ^ 2 : ℝ) : ℂ) := by
      rw [ha_def]; push_cast; ring
    rw [h0fun, map_zero, zero_add, harg, ← Complex.ofReal_exp]
  -- reindex the dual sum along the dual basis
  have hspan : span ℤ
      (Set.range ⇑(LinearMap.BilinForm.dualBasis (innerₗ E) hN c))
      = LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by
    conv_rhs => rw [← hc]
    rw [LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ E) hN c]
  set bD := (LinearMap.BilinForm.dualBasis (innerₗ E) hN c).restrictScalars ℤ
    with hbD_def
  set eD : (Module.Free.ChooseBasisIndex ℤ L → ℤ) ≃
      LinearMap.BilinForm.dualSubmodule (innerₗ E) L :=
    bD.equivFun.symm.toEquiv.trans (LinearEquiv.ofEq _ _ hspan).toEquiv with heD_def
  have heD_coe : ∀ m, ((eD m : E))
      = ∑ i, (m i : ℝ) • LinearMap.BilinForm.dualBasis (innerₗ E) hN c i := by
    intro m
    show (((LinearEquiv.ofEq _ _ hspan) (bD.equivFun.symm m) : _) : E) = _
    rw [LinearEquiv.coe_ofEq_apply, Basis.equivFun_symm_apply]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, hbD_def, Basis.restrictScalars_apply,
      ← Int.cast_smul_eq_zsmul ℝ]
  have hrhs : (∑' k, ((r k : ℝ) : ℂ))
      = (((ZLattice.covolume L)⁻¹ * t ^ ((Module.finrank ℝ E : ℝ) / 2) *
          ∑' w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L,
            Real.exp (-Real.pi * t * ‖(w : E)‖ ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum]
    congr 1
    rw [hr_def, tsum_mul_left]
    congr 1
    rw [← Equiv.tsum_eq eD fun w : LinearMap.BilinForm.dualSubmodule (innerₗ E) L =>
      Real.exp (-Real.pi * t * ‖(w : E)‖ ^ 2)]
    exact tsum_congr fun k => by rw [heD_coe k]
  have hfinal := hlhs.symm.trans (hF0.trans hrhs)
  exact_mod_cast hfinal

end ZLatticePoisson
