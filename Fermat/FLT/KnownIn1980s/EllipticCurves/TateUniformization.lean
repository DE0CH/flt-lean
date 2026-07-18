/-
TateUniformization.lean — own work for the Fermat project.

# Evaluation infrastructure for the Tate uniformisation

`TateCurveConstruction.lean` proves the *formal* Weierstrass equation
`Y² + XY = X³ + a₄X + a₆` for the uniformisation series
`X(u,q), Y(u,q) ∈ ℚ(u)⟦q⟧` (Silverman, ATAEC V.3). To feed the
uniformisation core `exists_tateCurveEquivSepClosure`, those formal
identities must be *evaluated* at points `(u₀, q₀)` of a
nonarchimedean local field `k` with `|q₀| < |u₀| ≤ 1`, `u₀ ∉ q₀^ℤ`.

`RatFunc.eval` is not a ring homomorphism (denominators can vanish),
so the evaluation is routed through the subring where all the
uniformisation coefficients actually live: every coefficient of
`X`, `Y`, `a₄`, `a₆` — and hence of any polynomial combination of
them — is a `ℚ`-linear combination of `uᵈ`, `u⁻ᵈ`, `(1-u)⁻ᵉ`. This
file therefore introduces

* `TateCurve.CoeffRing`: the localization `ℚ[T][1/(T(1-T))]`,
  a genuine ring;
* `TateCurve.coeffRingToRatFunc : CoeffRing →+* RatFunc ℚ`, the
  canonical (injective) inclusion, along which the formal series of
  `TateCurveConstruction.lean` will be recognised as `CoeffRing`-series;
* `TateCurve.coeffRingEval u₀ hu` for `u₀ ∈ k` with `u₀(1-u₀) ≠ 0`:
  the evaluation `CoeffRing →+* k`, an honest ring homomorphism.

Subsequent blocks (future iterations): the `CoeffRing`-lifts of the
four series, the nonarchimedean summability of their evaluations on
the fundamental annulus `|q₀| < |u₀| ≤ 1`, the evaluated Weierstrass
equation (from the formal identity, by the `evalInt`-style
ring-homomorphism pushes), and the finite-level uniformisation
`kˣ/q₀^ℤ ≃+ E_{q₀}(k)` feeding `exists_tateCurveEquivSepClosure`.
-/
module

public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateCurveConstruction
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateParameter
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

import Fermat.FLT.KnownIn1980s.EllipticCurves.TateCurve

@[expose] public section

noncomputable section

namespace TateCurve

/-- The coefficient ring `ℚ[T][1/(T(1-T))]` of the Tate uniformisation
series: the smallest ring containing `ℚ[u]` in which `u` and `1 - u`
are invertible. Every coefficient of the series `X`, `Y`, `a₄`, `a₆`
of `TateCurveConstruction.lean` lies in (the image in `ℚ(u)` of) this
ring, and — unlike on all of `ℚ(u)` — evaluation at any point
`u₀ ∈ k` with `u₀(1-u₀) ≠ 0` is a ring homomorphism on it. -/
abbrev CoeffRing : Type :=
  Localization.Away (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ)

/-- `T(1-T)` maps to a unit of `ℚ(u)`: it is a nonzero element of a
field. -/
theorem isUnit_ratFuncX_mul_one_sub :
    IsUnit (algebraMap (Polynomial ℚ) (RatFunc ℚ)
      (Polynomial.X * (1 - Polynomial.X))) := by
  refine isUnit_iff_ne_zero.mpr ?_
  rw [map_ne_zero_iff _ (RatFunc.algebraMap_injective (K := ℚ))]
  intro h0
  have h1 := congrArg (Polynomial.eval (1 / 2 : ℚ)) h0
  simp at h1
  norm_num at h1

/-- The canonical inclusion `ℚ[T][1/(T(1-T))] → ℚ(u)`, through which
the coefficients of the uniformisation series will be recognised as
elements of `CoeffRing`. -/
def coeffRingToRatFunc : CoeffRing →+* RatFunc ℚ :=
  Localization.awayLift (algebraMap (Polynomial ℚ) (RatFunc ℚ)) _
    isUnit_ratFuncX_mul_one_sub

@[simp]
theorem coeffRingToRatFunc_algebraMap (p : Polynomial ℚ) :
    coeffRingToRatFunc (algebraMap (Polynomial ℚ) CoeffRing p) =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) p := by
  rw [coeffRingToRatFunc]
  exact IsLocalization.lift_eq _ p

/-- The inclusion of the coefficient ring in `ℚ(u)` is injective: an
element is `a/(T(1-T))ⁿ`, and its image vanishes only if the image of
`a` does, hence only if `a = 0`. -/
theorem coeffRingToRatFunc_injective :
    Function.Injective coeffRingToRatFunc := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, hmk⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ)) x
  obtain ⟨n, hn⟩ := s.2
  have hs : coeffRingToRatFunc (algebraMap (Polynomial ℚ) CoeffRing s.1) =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) s.1 :=
    coeffRingToRatFunc_algebraMap s.1
  -- clear the denominator: `x·s = a` in `CoeffRing`
  have hxs : x * algebraMap (Polynomial ℚ) CoeffRing s.1 =
      algebraMap (Polynomial ℚ) CoeffRing a := by
    rw [← hmk]
    exact IsLocalization.mk'_spec _ a s
  have himg : algebraMap (Polynomial ℚ) (RatFunc ℚ) a = 0 := by
    have h1 := congrArg coeffRingToRatFunc hxs
    rw [map_mul, hx, zero_mul, coeffRingToRatFunc_algebraMap] at h1
    exact h1.symm
  have ha : a = 0 := by
    apply RatFunc.algebraMap_injective (K := ℚ)
    rw [himg, map_zero]
  rw [← hmk, ha, IsLocalization.mk'_eq_iff_eq_mul, zero_mul, map_zero]

/-! ### The variable `u` and its inverses in the coefficient ring -/

/-- `T` is a unit of `CoeffRing`: it divides the inverted element
`T(1-T)`. -/
theorem isUnit_uA :
    IsUnit (algebraMap (Polynomial ℚ) CoeffRing Polynomial.X) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := CoeffRing) (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

/-- `1 - T` is a unit of `CoeffRing`: it divides the inverted element
`T(1-T)`. -/
theorem isUnit_vA :
    IsUnit (algebraMap (Polynomial ℚ) CoeffRing (1 - Polynomial.X)) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := CoeffRing) (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

/-- The variable `u = T` of the coefficient ring, as a unit. -/
noncomputable def uA : CoeffRingˣ := isUnit_uA.unit

/-- The unit `1 - u` of the coefficient ring. -/
noncomputable def vA : CoeffRingˣ := isUnit_vA.unit

@[simp]
theorem coe_uA : (uA : CoeffRing) =
    algebraMap (Polynomial ℚ) CoeffRing Polynomial.X := rfl

@[simp]
theorem coe_vA : (vA : CoeffRing) =
    algebraMap (Polynomial ℚ) CoeffRing (1 - Polynomial.X) := rfl

/-! ### The `CoeffRing`-lifts of the uniformisation series

The series `X`, `Y`, `a₄`, `a₆` of `TateCurveConstruction.lean` have
all their coefficients in the image of `CoeffRing`; these are the
lifts, with the bridge lemmas (`map_XA` etc.) identifying their images
in `ℚ(u)⟦q⟧` with the originals. -/

open scoped ArithmeticFunction.sigma

/-- The `CoeffRing`-lift of the divisor-sum series
`s k = ∑ σₖ(n) qⁿ`. -/
noncomputable def sA (j : ℕ) : PowerSeries CoeffRing :=
  .mk fun n ↦ (σ j n : CoeffRing)

/-- The `CoeffRing`-lift of `TateCurve.a₄ = -5s₃`. -/
noncomputable def a₄A : PowerSeries CoeffRing := -5 * sA 3

/-- The `CoeffRing`-lift of `TateCurve.a₆ = -(5s₃+7s₅)/12`
(the division is exact on each coefficient: `12 ∣ 5σ₃(n) + 7σ₅(n)`,
implemented — as in `TateCurve.a₆Formal` — coefficientwise over `ℤ`
and cast). -/
noncomputable def a₆A : PowerSeries CoeffRing :=
  .mk fun n ↦ ((-((5 * σ 3 n + 7 * σ 5 n : ℤ) / 12) : ℤ) : CoeffRing)

/-- The `CoeffRing`-lift of the `x`-coordinate series `TateCurve.X`. -/
noncomputable def XA : PowerSeries CoeffRing :=
  .C ((uA : CoeffRing) * ((vA⁻¹ : CoeffRingˣ) : CoeffRing) ^ 2) +
    .mk fun n ↦ ∑ d ∈ n.divisors,
      (d : CoeffRing) * (((uA : CoeffRingˣ) : CoeffRing) ^ d +
        ((uA⁻¹ : CoeffRingˣ) : CoeffRing) ^ d - 2)

/-- The `CoeffRing`-lift of the `y`-coordinate series `TateCurve.Y`. -/
noncomputable def YA : PowerSeries CoeffRing :=
  .C (((uA : CoeffRingˣ) : CoeffRing) ^ 2 *
      ((vA⁻¹ : CoeffRingˣ) : CoeffRing) ^ 3) +
    .mk fun n ↦ ∑ d ∈ n.divisors,
      ((d.choose 2 : CoeffRing) * ((uA : CoeffRingˣ) : CoeffRing) ^ d -
        ((d + 1).choose 2 : CoeffRing) *
          ((uA⁻¹ : CoeffRingˣ) : CoeffRing) ^ d + (d : CoeffRing))

/-! ### Bridges: the lifts map to the original series in `ℚ(u)⟦q⟧` -/

theorem coeffRingToRatFunc_uA :
    coeffRingToRatFunc ((uA : CoeffRingˣ) : CoeffRing) = RatFunc.X := by
  rw [coe_uA, coeffRingToRatFunc_algebraMap, RatFunc.algebraMap_X]

theorem coeffRingToRatFunc_vA :
    coeffRingToRatFunc ((vA : CoeffRingˣ) : CoeffRing) =
      1 - RatFunc.X := by
  rw [coe_vA, coeffRingToRatFunc_algebraMap, map_sub, map_one,
    RatFunc.algebraMap_X]

theorem coeffRingToRatFunc_uA_inv :
    coeffRingToRatFunc ((uA⁻¹ : CoeffRingˣ) : CoeffRing) =
      (RatFunc.X : RatFunc ℚ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← coeffRingToRatFunc_uA, ← map_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, map_one]

theorem coeffRingToRatFunc_vA_inv :
    coeffRingToRatFunc ((vA⁻¹ : CoeffRingˣ) : CoeffRing) =
      (1 - RatFunc.X : RatFunc ℚ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← coeffRingToRatFunc_vA, ← map_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, map_one]

theorem map_sA (j : ℕ) :
    (sA j).map coeffRingToRatFunc = TateCurve.s j := by
  ext n
  simp [sA, TateCurve.s, PowerSeries.coeff_map, PowerSeries.coeff_mk]

theorem map_a₄A : a₄A.map coeffRingToRatFunc = TateCurve.a₄ := by
  rw [a₄A, TateCurve.a₄, map_mul, map_neg, map_ofNat, map_sA]

theorem map_a₆A : a₆A.map coeffRingToRatFunc = TateCurve.a₆ := by
  ext n
  have hdvd := TateCurve.dvd_five_sigma_three_add_seven_sigma_five n
  have h5C : ((5 : PowerSeries (RatFunc ℚ))) = PowerSeries.C (5 : RatFunc ℚ) :=
    (map_ofNat (PowerSeries.C (R := RatFunc ℚ)) 5).symm
  have h7C : ((7 : PowerSeries (RatFunc ℚ))) = PowerSeries.C (7 : RatFunc ℚ) :=
    (map_ofNat (PowerSeries.C (R := RatFunc ℚ)) 7).symm
  simp only [PowerSeries.coeff_map, a₆A, TateCurve.a₆, TateCurve.s,
    PowerSeries.coeff_mk, map_intCast, PowerSeries.coeff_smul, map_neg,
    map_add, h5C, h7C, PowerSeries.coeff_C_mul, smul_eq_mul]
  rw [Int.cast_neg, Int.cast_div_charZero hdvd]
  push_cast
  field_simp

theorem map_XA : XA.map coeffRingToRatFunc = TateCurve.X := by
  ext n
  rw [PowerSeries.coeff_map, XA, TateCurve.X]
  simp only [map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk,
    apply_ite coeffRingToRatFunc, map_zero, map_sum]
  congr 1
  · split_ifs with h
    · rw [map_mul, map_pow, coeffRingToRatFunc_uA, coeffRingToRatFunc_vA_inv,
        div_eq_mul_inv, inv_pow]
    · rfl
  · refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [map_mul, map_sub, map_add, map_pow, map_pow, map_natCast,
      map_ofNat, coeffRingToRatFunc_uA, coeffRingToRatFunc_uA_inv]

theorem map_YA : YA.map coeffRingToRatFunc = TateCurve.Y := by
  ext n
  rw [PowerSeries.coeff_map, YA, TateCurve.Y]
  simp only [map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk,
    apply_ite coeffRingToRatFunc, map_zero, map_sum]
  congr 1
  · split_ifs with h
    · rw [map_mul, map_pow, map_pow, coeffRingToRatFunc_uA,
        coeffRingToRatFunc_vA_inv, div_eq_mul_inv, inv_pow]
    · rfl
  · refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, map_natCast,
      map_natCast, map_natCast, coeffRingToRatFunc_uA,
      coeffRingToRatFunc_uA_inv]

section Evaluation

variable {k : Type*} [Field k] [CharZero k]

/-- `u₀(1-u₀)` is a unit of `k` when `u₀ ≠ 0` and `u₀ ≠ 1`. -/
theorem isUnit_aeval_of_ne (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1) :
    IsUnit (Polynomial.aeval u₀
      (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ)) := by
  refine isUnit_iff_ne_zero.mpr ?_
  rw [map_mul, Polynomial.aeval_X, map_sub, map_one, Polynomial.aeval_X]
  exact mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))

/-- **Evaluation of the coefficient ring at a point of `k`**: for
`u₀ ∈ k` with `u₀ ≠ 0`, `u₀ ≠ 1`, the ring homomorphism
`ℚ[T][1/(T(1-T))] → k` sending `T ↦ u₀`. This is the honest
(homomorphic) replacement for `RatFunc.eval` on the subring where the
Tate uniformisation series live. -/
def coeffRingEval (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1) :
    CoeffRing →+* k :=
  Localization.awayLift ((Polynomial.aeval u₀ :
    Polynomial ℚ →ₐ[ℚ] k) : Polynomial ℚ →+* k) _
    (isUnit_aeval_of_ne u₀ h0 h1)

@[simp]
theorem coeffRingEval_algebraMap (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (p : Polynomial ℚ) :
    coeffRingEval u₀ h0 h1 (algebraMap (Polynomial ℚ) CoeffRing p) =
      Polynomial.aeval u₀ p := by
  rw [coeffRingEval]
  exact IsLocalization.lift_eq _ p

theorem coeffRingEval_uA (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1) :
    coeffRingEval u₀ h0 h1 ((uA : CoeffRingˣ) : CoeffRing) = u₀ := by
  rw [coe_uA, coeffRingEval_algebraMap, Polynomial.aeval_X]

theorem coeffRingEval_vA (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1) :
    coeffRingEval u₀ h0 h1 ((vA : CoeffRingˣ) : CoeffRing) = 1 - u₀ := by
  rw [coe_vA, coeffRingEval_algebraMap, map_sub, map_one, Polynomial.aeval_X]

theorem coeffRingEval_uA_inv (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1) :
    coeffRingEval u₀ h0 h1 ((uA⁻¹ : CoeffRingˣ) : CoeffRing) = u₀⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  calc coeffRingEval u₀ h0 h1 ((uA⁻¹ : CoeffRingˣ) : CoeffRing) * u₀
      = coeffRingEval u₀ h0 h1 ((uA⁻¹ : CoeffRingˣ) : CoeffRing) *
        coeffRingEval u₀ h0 h1 ((uA : CoeffRingˣ) : CoeffRing) := by
        rw [coeffRingEval_uA u₀ h0 h1]
    _ = 1 := by
        rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          map_one]

theorem coeffRingEval_vA_inv (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1) :
    coeffRingEval u₀ h0 h1 ((vA⁻¹ : CoeffRingˣ) : CoeffRing) =
      (1 - u₀)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  calc coeffRingEval u₀ h0 h1 ((vA⁻¹ : CoeffRingˣ) : CoeffRing) * (1 - u₀)
      = coeffRingEval u₀ h0 h1 ((vA⁻¹ : CoeffRingˣ) : CoeffRing) *
        coeffRingEval u₀ h0 h1 ((vA : CoeffRingˣ) : CoeffRing) := by
        rw [coeffRingEval_vA u₀ h0 h1]
    _ = 1 := by
        rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          map_one]

/-- **Evaluation of a `CoeffRing`-series at a point `(u₀, q₀)` of a
topological field** (junk value if the series does not converge): the
two-variable analogue of `TateCurve.evalInt`, specialising the
coefficient variable to `u₀` through the ring homomorphism
`coeffRingEval` and summing against powers of `q₀`. On a
nonarchimedean local field, for `|q₀| < |u₀| ≤ 1` the evaluations of
`XA`, `YA`, `a₄A`, `a₆A` all converge (fundamental-annulus estimates —
next block). -/
noncomputable def evalA [TopologicalSpace k] (u₀ q₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) (F : PowerSeries CoeffRing) : k :=
  ∑' n : ℕ, coeffRingEval u₀ h0 h1 (PowerSeries.coeff n F) * q₀ ^ n

end Evaluation

section Annulus

open ValuativeRel

variable {k : Type*} [Field k] [TopologicalSpace k] [ValuativeRel k]
  [IsNonarchimedeanLocalField k] [CharZero k]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The explicit form of the higher coefficients of `XA` evaluated at
`u₀`. -/
theorem coeffRingEval_coeff_XA (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    {n : ℕ} (hn : n ≠ 0) :
    coeffRingEval u₀ h0 h1 (PowerSeries.coeff n XA) =
      ∑ d ∈ n.divisors, (d : k) * (u₀ ^ d + u₀⁻¹ ^ d - 2) := by
  rw [XA, map_add, PowerSeries.coeff_C, if_neg hn, zero_add,
    PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [map_mul, map_sub, map_add, map_pow, map_pow, map_natCast,
    map_ofNat, coeffRingEval_uA, coeffRingEval_uA_inv]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- **Fundamental-annulus coefficient bound for `XA`**: for
`|u₀| ≤ 1` the `n`-th coefficient of `XA` evaluated at `u₀` has
valuation at most `|u₀|⁻ⁿ` — each divisor term `d(u₀ᵈ + u₀⁻ᵈ - 2)`
is dominated by the `u₀⁻ᵈ` summand, and `d ≤ n`. -/
theorem valuation_coeffRingEval_XA_le (u₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) (hu : valuation k u₀ ≤ 1) {n : ℕ} (hn : n ≠ 0) :
    valuation k (coeffRingEval u₀ h0 h1 (PowerSeries.coeff n XA)) ≤
      ((valuation k u₀) ^ n)⁻¹ := by
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  have hone : (1 : ValueGroupWithZero k) ≤ ((valuation k u₀) ^ n)⁻¹ := by
    rw [one_le_inv₀ (pow_pos (zero_lt_iff.mpr hv0) n)]
    exact pow_le_one₀ zero_le hu
  rw [coeffRingEval_coeff_XA u₀ h0 h1 hn]
  refine Valuation.map_sum_le _ fun d hd ↦ ?_
  have hdn : d ≤ n := Nat.divisor_le hd
  rw [map_mul]
  have hd1 : valuation k (d : k) ≤ 1 := by
    have h := valuation_intCast_le_one (R := k) d
    simpa using h
  have hsum : valuation k (u₀ ^ d + u₀⁻¹ ^ d - 2) ≤
      ((valuation k u₀) ^ n)⁻¹ := by
    have ha : valuation k (u₀ ^ d) ≤ ((valuation k u₀) ^ n)⁻¹ := by
      rw [map_pow]
      exact le_trans (pow_le_one₀ zero_le hu) hone
    have hb : valuation k (u₀⁻¹ ^ d) ≤ ((valuation k u₀) ^ n)⁻¹ := by
      rw [map_pow, map_inv₀, ← inv_pow]
      refine pow_le_pow_right' ?_ hdn
      rw [one_le_inv₀ (zero_lt_iff.mpr hv0)]
      exact hu
    have hc : valuation k (2 : k) ≤ ((valuation k u₀) ^ n)⁻¹ := by
      refine le_trans ?_ hone
      have h := valuation_intCast_le_one (R := k) 2
      simpa using h
    calc valuation k (u₀ ^ d + u₀⁻¹ ^ d - 2)
        ≤ max (valuation k (u₀ ^ d + u₀⁻¹ ^ d)) (valuation k (2 : k)) :=
          Valuation.map_sub _ _ _
      _ ≤ ((valuation k u₀) ^ n)⁻¹ := by
          refine max_le ?_ hc
          exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)
  calc valuation k ((d : k)) * valuation k (u₀ ^ d + u₀⁻¹ ^ d - 2)
      ≤ 1 * ((valuation k u₀) ^ n)⁻¹ := mul_le_mul' hd1 hsum
    _ = ((valuation k u₀) ^ n)⁻¹ := one_mul _

/-- **Summability of the evaluated `x`-series on the fundamental
annulus** `|q₀| < |u₀| ≤ 1`: term `n ≥ 1` has valuation at most
`(|q₀|/|u₀|)ⁿ = |q₀u₀⁻¹|ⁿ` by the coefficient bound, and
`|q₀u₀⁻¹| < 1`, so the nonarchimedean criterion applies (the `n = 0`
term is split off, since the constant coefficient `u₀/(1-u₀)²` obeys
no annulus bound). -/
theorem summable_evalA_XA (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq : valuation k q₀ < valuation k u₀) :
    Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n XA) * q₀ ^ n := by
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  have hw : valuation k (q₀ * u₀⁻¹) < 1 := by
    rw [map_mul, map_inv₀]
    calc valuation k q₀ * (valuation k u₀)⁻¹
        < valuation k u₀ * (valuation k u₀)⁻¹ :=
          mul_lt_mul_of_pos_right hq (zero_lt_iff.mpr (inv_ne_zero hv0))
      _ = 1 := mul_inv_cancel₀ hv0
  rw [← summable_nat_add_iff 1]
  refine summable_of_valuation_le_pow hw (fun n ↦ n + 1)
    (fun N ↦ (Set.finite_Iio N).subset fun i hi ↦ Set.mem_Iio.mpr
      (lt_trans (Nat.lt_succ_self i) hi)) (fun n ↦ ?_)
  rw [map_mul, map_pow]
  have hb := valuation_coeffRingEval_XA_le u₀ h0 h1 hu
    (Nat.succ_ne_zero n)
  calc valuation k (coeffRingEval u₀ h0 h1
        (PowerSeries.coeff (n + 1) XA)) * valuation k q₀ ^ (n + 1)
      ≤ ((valuation k u₀) ^ (n + 1))⁻¹ * valuation k q₀ ^ (n + 1) :=
        mul_le_mul_left hb _
    _ = valuation k (q₀ * u₀⁻¹) ^ (n + 1) := by
        rw [map_mul, map_inv₀, mul_pow, inv_pow]
        exact mul_comm _ _

end Annulus

end TateCurve

end
