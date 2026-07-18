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

public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateCurve

import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Ring

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

/-! ### The formal Weierstrass equation over the coefficient ring -/

/-- **The formal Weierstrass equation over `CoeffRing`**: pulled back
from `TateCurve.weierstrass_equation` (in `ℚ(u)⟦q⟧`, proven by the
complex-analytic descent of `TateCurveConstruction.lean`) along the
injective inclusion `coeffRingToRatFunc`. -/
theorem weierstrass_equation_A :
    YA ^ 2 + XA * YA = XA ^ 3 + a₄A * XA + a₆A := by
  have hinj : Function.Injective
      (PowerSeries.map coeffRingToRatFunc) := by
    intro P Q h
    ext n
    refine coeffRingToRatFunc_injective ?_
    have h1 := congrArg (PowerSeries.coeff n) h
    rwa [PowerSeries.coeff_map, PowerSeries.coeff_map] at h1
  apply hinj
  simp only [map_add, map_mul, map_pow, map_XA, map_YA, map_a₄A,
    map_a₆A]
  exact TateCurve.weierstrass_equation

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

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The explicit form of the higher coefficients of `YA` evaluated at
`u₀`. -/
theorem coeffRingEval_coeff_YA (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    {n : ℕ} (hn : n ≠ 0) :
    coeffRingEval u₀ h0 h1 (PowerSeries.coeff n YA) =
      ∑ d ∈ n.divisors, ((d.choose 2 : k) * u₀ ^ d -
        ((d + 1).choose 2 : k) * u₀⁻¹ ^ d + (d : k)) := by
  rw [YA, map_add, PowerSeries.coeff_C, if_neg hn, zero_add,
    PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [map_add, map_sub, map_mul, map_mul, map_pow, map_pow, map_natCast,
    map_natCast, map_natCast, coeffRingEval_uA, coeffRingEval_uA_inv]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- **Fundamental-annulus coefficient bound for `YA`**: for
`|u₀| ≤ 1` the `n`-th coefficient of `YA` evaluated at `u₀` has
valuation at most `|u₀|⁻ⁿ`. -/
theorem valuation_coeffRingEval_YA_le (u₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) (hu : valuation k u₀ ≤ 1) {n : ℕ} (hn : n ≠ 0) :
    valuation k (coeffRingEval u₀ h0 h1 (PowerSeries.coeff n YA)) ≤
      ((valuation k u₀) ^ n)⁻¹ := by
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  have hone : (1 : ValueGroupWithZero k) ≤ ((valuation k u₀) ^ n)⁻¹ := by
    rw [one_le_inv₀ (zero_lt_iff.mpr (pow_ne_zero n hv0))]
    exact pow_le_one₀ zero_le hu
  have hnat : ∀ m : ℕ, valuation k (m : k) ≤ 1 := by
    intro m
    have h := valuation_intCast_le_one (R := k) m
    simpa using h
  rw [coeffRingEval_coeff_YA u₀ h0 h1 hn]
  refine Valuation.map_sum_le _ fun d hd ↦ ?_
  have hdn : d ≤ n := Nat.divisor_le hd
  have ha : valuation k ((d.choose 2 : k) * u₀ ^ d) ≤
      ((valuation k u₀) ^ n)⁻¹ := by
    rw [map_mul, map_pow]
    calc valuation k ((d.choose 2 : k)) * valuation k u₀ ^ d
        ≤ 1 * 1 := mul_le_mul' (hnat _) (pow_le_one₀ zero_le hu)
      _ = 1 := one_mul _
      _ ≤ _ := hone
  have hb : valuation k (((d + 1).choose 2 : k) * u₀⁻¹ ^ d) ≤
      ((valuation k u₀) ^ n)⁻¹ := by
    rw [map_mul, map_pow, map_inv₀]
    have hpow : ((valuation k u₀)⁻¹) ^ d ≤ ((valuation k u₀) ^ n)⁻¹ := by
      rw [← inv_pow]
      refine pow_le_pow_right' ?_ hdn
      rw [one_le_inv₀ (zero_lt_iff.mpr hv0)]
      exact hu
    calc valuation k (((d + 1).choose 2 : k)) * ((valuation k u₀)⁻¹) ^ d
        ≤ 1 * ((valuation k u₀) ^ n)⁻¹ := mul_le_mul' (hnat _) hpow
      _ = ((valuation k u₀) ^ n)⁻¹ := one_mul _
  have hc : valuation k ((d : k)) ≤ ((valuation k u₀) ^ n)⁻¹ :=
    le_trans (hnat d) hone
  calc valuation k ((d.choose 2 : k) * u₀ ^ d -
        ((d + 1).choose 2 : k) * u₀⁻¹ ^ d + (d : k))
      ≤ max (valuation k ((d.choose 2 : k) * u₀ ^ d -
          ((d + 1).choose 2 : k) * u₀⁻¹ ^ d)) (valuation k ((d : k))) :=
        Valuation.map_add _ _ _
    _ ≤ ((valuation k u₀) ^ n)⁻¹ := by
        refine max_le ?_ hc
        exact le_trans (Valuation.map_sub _ _ _) (max_le ha hb)

/-- **Summability of the evaluated `y`-series on the fundamental
annulus** `|q₀| < |u₀| ≤ 1` (mirror of `summable_evalA_XA`). -/
theorem summable_evalA_YA (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq : valuation k q₀ < valuation k u₀) :
    Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n YA) * q₀ ^ n := by
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
  have hb := valuation_coeffRingEval_YA_le u₀ h0 h1 hu
    (Nat.succ_ne_zero n)
  calc valuation k (coeffRingEval u₀ h0 h1
        (PowerSeries.coeff (n + 1) YA)) * valuation k q₀ ^ (n + 1)
      ≤ ((valuation k u₀) ^ (n + 1))⁻¹ * valuation k q₀ ^ (n + 1) :=
        mul_le_mul_left hb _
    _ = valuation k (q₀ * u₀⁻¹) ^ (n + 1) := by
        rw [map_mul, map_inv₀, mul_pow, inv_pow]
        exact mul_comm _ _

/-- **Additivity of the evaluation** on summable series. -/
theorem evalA_add (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    {F G : PowerSeries CoeffRing}
    (hF : Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n F) * q₀ ^ n)
    (hG : Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n G) * q₀ ^ n) :
    evalA u₀ q₀ h0 h1 (F + G) =
      evalA u₀ q₀ h0 h1 F + evalA u₀ q₀ h0 h1 G := by
  rw [evalA, evalA, evalA, ← hF.tsum_add hG]
  congr 1
  funext n
  rw [map_add, map_add, add_mul]

omit [CharZero k] in
/-- The nonarchimedean Cauchy-product summability over `k`, stated for
the original topology (the uniform structure is installed only inside
the proof, so no instance mixing leaks into applications). -/
theorem summable_mul_prod {f g : ℕ → k} (hf : Summable f)
    (hg : Summable g) : Summable fun i : ℕ × ℕ ↦ f i.1 * g i.2 := by
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  exact Summable.mul_of_nonarchimedean hf hg

set_option maxHeartbeats 1000000 in
/-- **Multiplicativity of the evaluation** on summable series: the
nonarchimedean Cauchy product, regrouped along antidiagonals into the
power-series product coefficients. -/
theorem evalA_mul (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    {F G : PowerSeries CoeffRing}
    (hF : Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n F) * q₀ ^ n)
    (hG : Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n G) * q₀ ^ n) :
    evalA u₀ q₀ h0 h1 (F * G) =
      evalA u₀ q₀ h0 h1 F * evalA u₀ q₀ h0 h1 G := by
  set f : ℕ → k :=
    fun n ↦ coeffRingEval u₀ h0 h1 (PowerSeries.coeff n F) * q₀ ^ n
    with hfdef
  set g : ℕ → k :=
    fun n ↦ coeffRingEval u₀ h0 h1 (PowerSeries.coeff n G) * q₀ ^ n
    with hgdef
  have key := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal (A := ℕ)
    hF hG (summable_mul_prod hF hG)
  rw [evalA, evalA, evalA, key]
  congr 1
  funext n
  rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hpn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  rw [hfdef, hgdef, map_mul]
  rw [← hpn, pow_add]
  ring

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The coefficients of `a₄A` evaluate to plain integers. -/
theorem coeffRingEval_coeff_a₄A (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (n : ℕ) :
    coeffRingEval u₀ h0 h1 (PowerSeries.coeff n a₄A) =
      ((-5 * σ 3 n : ℤ) : k) := by
  have h5C : ((5 : PowerSeries CoeffRing)) = PowerSeries.C (5 : CoeffRing) :=
    (map_ofNat (PowerSeries.C (R := CoeffRing)) 5).symm
  rw [a₄A, neg_mul, map_neg, h5C, PowerSeries.coeff_C_mul, sA,
    PowerSeries.coeff_mk, map_neg, map_mul, map_ofNat, map_natCast]
  push_cast
  ring

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The coefficients of `a₆A` evaluate to plain integers. -/
theorem coeffRingEval_coeff_a₆A (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (n : ℕ) :
    coeffRingEval u₀ h0 h1 (PowerSeries.coeff n a₆A) =
      ((-((5 * σ 3 n + 7 * σ 5 n : ℤ) / 12) : ℤ) : k) := by
  rw [a₆A, PowerSeries.coeff_mk, map_intCast]

/-- Summability of the evaluated `a₄`-series: integer coefficients,
`|q₀| < 1`. -/
theorem summable_evalA_a₄A (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hq : valuation k q₀ < 1) :
    Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n a₄A) * q₀ ^ n := by
  refine summable_of_valuation_le_pow hq (fun n ↦ n)
    (fun N ↦ Set.finite_Iio N) fun n ↦ ?_
  rw [coeffRingEval_coeff_a₄A, map_mul, map_pow]
  calc valuation k (((-5 * σ 3 n : ℤ) : k)) * valuation k q₀ ^ n
      ≤ 1 * valuation k q₀ ^ n :=
        mul_le_mul_left (valuation_intCast_le_one _) _
    _ = valuation k q₀ ^ n := one_mul _

/-- Summability of the evaluated `a₆`-series: integer coefficients,
`|q₀| < 1`. -/
theorem summable_evalA_a₆A (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hq : valuation k q₀ < 1) :
    Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n a₆A) * q₀ ^ n := by
  refine summable_of_valuation_le_pow hq (fun n ↦ n)
    (fun N ↦ Set.finite_Iio N) fun n ↦ ?_
  rw [coeffRingEval_coeff_a₆A, map_mul, map_pow]
  calc valuation k (((-((5 * σ 3 n + 7 * σ 5 n : ℤ) / 12) : ℤ) : k)) *
        valuation k q₀ ^ n
      ≤ 1 * valuation k q₀ ^ n :=
        mul_le_mul_left (valuation_intCast_le_one _) _
    _ = valuation k q₀ ^ n := one_mul _

/-- Summability of the evaluated product series: the Cauchy product of
the two evaluated series regrouped into the product coefficients. -/
theorem summable_evalA_mul (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    {F G : PowerSeries CoeffRing}
    (hF : Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n F) * q₀ ^ n)
    (hG : Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n G) * q₀ ^ n) :
    Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n (F * G)) * q₀ ^ n := by
  set f : ℕ → k :=
    fun n ↦ coeffRingEval u₀ h0 h1 (PowerSeries.coeff n F) * q₀ ^ n
    with hfdef
  set g : ℕ → k :=
    fun n ↦ coeffRingEval u₀ h0 h1 (PowerSeries.coeff n G) * q₀ ^ n
    with hgdef
  have h := summable_sum_mul_antidiagonal_of_summable_mul (A := ℕ)
    (summable_mul_prod hF hG)
  refine h.congr fun n ↦ ?_
  rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hpn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  rw [hfdef, hgdef, map_mul]
  rw [← hpn, pow_add]
  ring

/-- Summability of the evaluated sum series. -/
theorem summable_evalA_add (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    {F G : PowerSeries CoeffRing}
    (hF : Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n F) * q₀ ^ n)
    (hG : Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n G) * q₀ ^ n) :
    Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n (F + G)) * q₀ ^ n := by
  refine (hF.add hG).congr fun n ↦ ?_
  rw [map_add, map_add, add_mul]

/-- **The evaluated Weierstrass equation** (Silverman ATAEC V.3.1(c),
algebraic half): at every point `(u₀, q₀)` of the fundamental annulus
`|q₀| < |u₀| ≤ 1`, `|q₀| < 1`, the values `x = X(u₀,q₀)`,
`y = Y(u₀,q₀)` of the uniformisation series satisfy
`y² + xy = x³ + a₄(q₀)x + a₆(q₀)` — the affine equation of the Tate
curve. Derived from the formal identity `weierstrass_equation_A` by
pushing the evaluation through sums and Cauchy products. -/
theorem evalA_weierstrass (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq1 : valuation k q₀ < 1)
    (hq : valuation k q₀ < valuation k u₀) :
    evalA u₀ q₀ h0 h1 YA ^ 2 +
      evalA u₀ q₀ h0 h1 XA * evalA u₀ q₀ h0 h1 YA =
    evalA u₀ q₀ h0 h1 XA ^ 3 +
      evalA u₀ q₀ h0 h1 a₄A * evalA u₀ q₀ h0 h1 XA +
      evalA u₀ q₀ h0 h1 a₆A := by
  have hX := summable_evalA_XA u₀ q₀ h0 h1 hu hq
  have hY := summable_evalA_YA u₀ q₀ h0 h1 hu hq
  have h4 := summable_evalA_a₄A u₀ q₀ h0 h1 hq1
  have h6 := summable_evalA_a₆A u₀ q₀ h0 h1 hq1
  have hYY := summable_evalA_mul u₀ q₀ h0 h1 hY hY
  have hXY := summable_evalA_mul u₀ q₀ h0 h1 hX hY
  have hXX := summable_evalA_mul u₀ q₀ h0 h1 hX hX
  have hXXX := summable_evalA_mul u₀ q₀ h0 h1 hXX hX
  have h4X := summable_evalA_mul u₀ q₀ h0 h1 h4 hX
  -- the formal identity in product-normal form
  have hWE : YA * YA + XA * YA = XA * XA * XA + a₄A * XA + a₆A := by
    linear_combination weierstrass_equation_A
  calc evalA u₀ q₀ h0 h1 YA ^ 2 +
        evalA u₀ q₀ h0 h1 XA * evalA u₀ q₀ h0 h1 YA
      = evalA u₀ q₀ h0 h1 (YA * YA) + evalA u₀ q₀ h0 h1 (XA * YA) := by
        rw [evalA_mul u₀ q₀ h0 h1 hY hY, evalA_mul u₀ q₀ h0 h1 hX hY]
        ring
    _ = evalA u₀ q₀ h0 h1 (YA * YA + XA * YA) :=
        (evalA_add u₀ q₀ h0 h1 hYY hXY).symm
    _ = evalA u₀ q₀ h0 h1 (XA * XA * XA + a₄A * XA + a₆A) := by rw [hWE]
    _ = evalA u₀ q₀ h0 h1 (XA * XA * XA + a₄A * XA) +
        evalA u₀ q₀ h0 h1 a₆A :=
        evalA_add u₀ q₀ h0 h1
          (summable_evalA_add u₀ q₀ h0 h1 hXXX h4X) h6
    _ = evalA u₀ q₀ h0 h1 (XA * XA * XA) +
        evalA u₀ q₀ h0 h1 (a₄A * XA) + evalA u₀ q₀ h0 h1 a₆A := by
        rw [evalA_add u₀ q₀ h0 h1 hXXX h4X]
    _ = evalA u₀ q₀ h0 h1 XA ^ 3 +
        evalA u₀ q₀ h0 h1 a₄A * evalA u₀ q₀ h0 h1 XA +
        evalA u₀ q₀ h0 h1 a₆A := by
        rw [evalA_mul u₀ q₀ h0 h1 hXX hX, evalA_mul u₀ q₀ h0 h1 hX hX,
          evalA_mul u₀ q₀ h0 h1 h4 hX]
        ring

/-- The evaluated `a₄A` is the Tate curve coefficient `a₄(q₀)`:
both sides equal the evaluation of the integral formal series
`a₄Formal`. -/
theorem evalA_a₄A (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hq : valuation k q₀ < 1) :
    evalA u₀ q₀ h0 h1 a₄A = WeierstrassCurve.tateA₄ q₀ := by
  rw [WeierstrassCurve.tateA₄_eq_evalInt q₀ hq, TateCurve.evalInt, evalA]
  congr 1
  funext n
  rw [coeffRingEval_coeff_a₄A, TateCurve.coeff_a₄Formal]

/-- The evaluated `a₆A` is the Tate curve coefficient `a₆(q₀)`. -/
theorem evalA_a₆A (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hq : valuation k q₀ < 1) :
    evalA u₀ q₀ h0 h1 a₆A = WeierstrassCurve.tateA₆ q₀ := by
  rw [WeierstrassCurve.tateA₆_eq_evalInt q₀ hq, TateCurve.evalInt, evalA]
  congr 1
  funext n
  rw [coeffRingEval_coeff_a₆A, TateCurve.coeff_a₆Formal]

/-- **The uniformisation values lie on the Tate curve** (the affine
form): for `(u₀, q₀)` in the fundamental annulus, the pair
`(X(u₀,q₀), Y(u₀,q₀))` satisfies the affine Weierstrass equation of
`tateCurve q₀`. -/
theorem evalA_mem_tateCurve (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq1 : valuation k q₀ < 1)
    (hq : valuation k q₀ < valuation k u₀) :
    (WeierstrassCurve.tateCurve q₀).toAffine.Equation
      (evalA u₀ q₀ h0 h1 XA) (evalA u₀ q₀ h0 h1 YA) := by
  have hWE := evalA_weierstrass u₀ q₀ h0 h1 hu hq1 hq
  rw [evalA_a₄A u₀ q₀ h0 h1 hq1, evalA_a₆A u₀ q₀ h0 h1 hq1] at hWE
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.tateCurve]
  linear_combination hWE

omit [CharZero k] in
/-- **Fundamental-domain normalization** (half of ATAEC V.3.1(e)'s
setup): for `0 < |q| < 1`, every nonzero `u ∈ k` has a `q`-power
translate `u·q⁻ᵐ` in the half-open annulus `|q| < |u·q⁻ᵐ| ≤ 1`; `m`
is the floor of `log_{|q|}|u|`, obtained from the archimedean property
of the rank-one value group (`exists_pow_valuation_lt`) and minimal
choice. -/
theorem exists_zpow_mul_mem_annulus (q : k) (hq0 : q ≠ 0)
    (hq : valuation k q < 1) (u : k) (hu0 : u ≠ 0) :
    ∃ m : ℤ, valuation k q < valuation k (u * q ^ (-m)) ∧
      valuation k (u * q ^ (-m)) ≤ 1 := by
  have hvq0 : valuation k q ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using hq0
  have hvu0 : valuation k u ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using hu0
  -- the valuation of the translate
  have hval : ∀ m : ℤ, valuation k (u * q ^ (-m)) =
      valuation k u * (valuation k q) ^ (-m : ℤ) := by
    intro m
    rw [map_mul, map_zpow₀]
  -- reduce to the value-group statement: find `m` with
  -- `v(q)^(m+1) < v(u) ≤ v(q)^m`
  suffices h : ∃ m : ℤ, (valuation k q) ^ (m + 1) < valuation k u ∧
      valuation k u ≤ (valuation k q) ^ m by
    obtain ⟨m, hlow, hhigh⟩ := h
    refine ⟨m, ?_, ?_⟩
    · rw [hval]
      calc valuation k q
          = (valuation k q) ^ (m + 1) * ((valuation k q) ^ (-m : ℤ)) := by
            rw [← zpow_add₀ hvq0]
            norm_num
        _ < valuation k u * ((valuation k q) ^ (-m : ℤ)) :=
            mul_lt_mul_of_pos_right hlow
              (zero_lt_iff.mpr (zpow_ne_zero _ hvq0))
    · rw [hval]
      calc valuation k u * (valuation k q) ^ (-m : ℤ)
          ≤ (valuation k q) ^ m * (valuation k q) ^ (-m : ℤ) :=
            mul_le_mul_left hhigh _
        _ = 1 := by
            rw [← zpow_add₀ hvq0]
            norm_num
  -- two cases on `v(u) ≤ 1`
  rcases le_or_gt (valuation k u) 1 with hle | hgt
  · -- least `N` with `v(q)^N < v(u)`
    have hex : ∃ N : ℕ, (valuation k q) ^ N < valuation k u :=
      exists_pow_valuation_lt q hq (Units.mk0 _ hvu0)
    classical
    set N₀ := Nat.find hex with hN₀def
    have hN₀ : (valuation k q) ^ N₀ < valuation k u := Nat.find_spec hex
    have hN₀pos : N₀ ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hN₀
      exact absurd hle (not_le.mpr hN₀)
    have hmin : ¬ (valuation k q) ^ (N₀ - 1) < valuation k u :=
      Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hN₀pos) one_pos)
    refine ⟨(N₀ : ℤ) - 1, ?_, ?_⟩
    · have : ((N₀ : ℤ) - 1) + 1 = (N₀ : ℤ) := by ring
      rw [this, zpow_natCast]
      exact hN₀
    · rw [show ((N₀ : ℤ) - 1) = ((N₀ - 1 : ℕ) : ℤ) by omega, zpow_natCast]
      exact not_lt.mp hmin
  · -- `v(u) > 1`: find the least `M` with `v(u)·v(q)^M ≤ 1`
    have hvuinv0 : (valuation k u)⁻¹ ≠ 0 := inv_ne_zero hvu0
    have hex : ∃ M : ℕ, valuation k u * (valuation k q) ^ M ≤ 1 := by
      obtain ⟨N, hN⟩ := exists_pow_valuation_lt q hq
        (Units.mk0 _ hvuinv0)
      refine ⟨N, ?_⟩
      have h1 : valuation k u * (valuation k q) ^ N <
          valuation k u * (valuation k u)⁻¹ :=
        mul_lt_mul_of_pos_left hN (zero_lt_iff.mpr hvu0)
      rw [mul_inv_cancel₀ hvu0] at h1
      exact h1.le
    classical
    set M₀ := Nat.find hex with hM₀def
    have hM₀ : valuation k u * (valuation k q) ^ M₀ ≤ 1 := Nat.find_spec hex
    have hM₀pos : M₀ ≠ 0 := by
      intro h0
      rw [h0, pow_zero, mul_one] at hM₀
      exact absurd hgt (not_lt.mpr hM₀)
    have hmin : ¬ valuation k u * (valuation k q) ^ (M₀ - 1) ≤ 1 :=
      Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hM₀pos) one_pos)
    rw [not_le] at hmin
    refine ⟨-(M₀ : ℤ), ?_, ?_⟩
    · have hexp : (-(M₀ : ℤ) + 1) = -((M₀ - 1 : ℕ) : ℤ) := by omega
      rw [hexp]
      calc (valuation k q) ^ (-((M₀ - 1 : ℕ) : ℤ))
          = 1 * (valuation k q) ^ (-((M₀ - 1 : ℕ) : ℤ)) := (one_mul _).symm
        _ < (valuation k u * (valuation k q) ^ (M₀ - 1)) *
            (valuation k q) ^ (-((M₀ - 1 : ℕ) : ℤ)) :=
            mul_lt_mul_of_pos_right hmin
              (zero_lt_iff.mpr (zpow_ne_zero _ hvq0))
        _ = valuation k u := by
            rw [mul_assoc, ← zpow_natCast (valuation k q) (M₀ - 1),
              ← zpow_add₀ hvq0]
            norm_num
    · calc valuation k u
          = (valuation k u * (valuation k q) ^ M₀) *
            (valuation k q) ^ (-(M₀ : ℤ)) := by
            rw [mul_assoc, ← zpow_natCast (valuation k q) M₀,
              ← zpow_add₀ hvq0]
            norm_num
        _ ≤ 1 * (valuation k q) ^ (-(M₀ : ℤ)) :=
            mul_le_mul_left hM₀ _
        _ = (valuation k q) ^ (-(M₀ : ℤ)) := one_mul _

omit [CharZero k] in
/-- The Tate curve at any `0 < |q₀| < 1` has nonvanishing discriminant:
its discriminant is the evaluation of `ΔFormal`, of valuation exactly
`|q₀| ≠ 0`. -/
theorem tateCurve_Δ_ne_zero (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq : valuation k q₀ < 1) :
    (WeierstrassCurve.tateCurve q₀).Δ ≠ 0 := by
  rw [WeierstrassCurve.Δ_tateCurve_eq_evalInt q₀ hq]
  have h := TateCurve.valuation_evalInt_eq q₀ hq0 hq
    TateCurve.constantCoeff_ΔFormal TateCurve.coeff_one_ΔFormal
  intro h0
  rw [h0, map_zero] at h
  exact hq0 (by rwa [eq_comm, map_eq_zero] at h)

/-- **Nonsingularity of the uniformisation values**: on the
fundamental annulus, `(X(u₀,q₀), Y(u₀,q₀))` is a nonsingular point of
the Tate curve (the curve is smooth as `Δ ≠ 0`). -/
theorem nonsingular_evalA (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hq0 : q₀ ≠ 0) (hu : valuation k u₀ ≤ 1) (hq1 : valuation k q₀ < 1)
    (hq : valuation k q₀ < valuation k u₀) :
    (WeierstrassCurve.tateCurve q₀).toAffine.Nonsingular
      (evalA u₀ q₀ h0 h1 XA) (evalA u₀ q₀ h0 h1 YA) :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (tateCurve_Δ_ne_zero q₀ hq0 hq1)).mp
    (evalA_mem_tateCurve u₀ q₀ h0 h1 hu hq1 hq)

/-- **The uniformisation point of an annulus parameter**: the affine
point `(X(u₀,q₀), Y(u₀,q₀))` of the Tate curve attached to `u₀` in
the fundamental annulus, `u₀ ≠ 1`. The point map `kˣ/q₀^ℤ → E_{q₀}(k)`
sends the class of `u` to `annulusPoint` of its unique annulus
representative (`exists_zpow_mul_mem_annulus`), and the class of `1`
to zero. -/
noncomputable def annulusPoint (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hq0 : q₀ ≠ 0) (hu : valuation k u₀ ≤ 1) (hq1 : valuation k q₀ < 1)
    (hq : valuation k q₀ < valuation k u₀) :
    (WeierstrassCurve.tateCurve q₀).toAffine.Point :=
  .some (evalA u₀ q₀ h0 h1 XA) (evalA u₀ q₀ h0 h1 YA)
    (nonsingular_evalA u₀ q₀ h0 h1 hq0 hu hq1 hq)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- **The annulus is a strict fundamental domain**: the `q`-power
normalising exponent of `exists_zpow_mul_mem_annulus` is unique — two
translates of `u` in the half-open annulus `(|q|, 1]` coincide, since
their ratio `|q|^(m'-m)` would otherwise leave the interval
`(|q|, |q|⁻¹)`. -/
theorem annulus_exponent_unique (q : k) (hq0 : q ≠ 0)
    (hq : valuation k q < 1) (u : k) {m m' : ℤ}
    (hm : valuation k q < valuation k (u * q ^ (-m)) ∧
      valuation k (u * q ^ (-m)) ≤ 1)
    (hm' : valuation k q < valuation k (u * q ^ (-m')) ∧
      valuation k (u * q ^ (-m')) ≤ 1) :
    m = m' := by
  have hvq0 : valuation k q ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using hq0
  -- valuations of the translates
  have hval : ∀ n : ℤ, valuation k (u * q ^ (-n)) =
      valuation k u * (valuation k q) ^ (-n : ℤ) := by
    intro n
    rw [map_mul, map_zpow₀]
  -- w.l.o.g. via a symmetric auxiliary claim
  have key : ∀ a b : ℤ, a < b →
      valuation k q < valuation k (u * q ^ (-a)) →
      valuation k (u * q ^ (-b)) ≤ 1 → False := by
    intro a b hab hlow hhigh
    -- `v(u·q⁻ᵇ) = v(u·q⁻ᵃ)·v(q)^(a-b)` with `a - b ≤ -1`
    have hratio : valuation k (u * q ^ (-b)) =
        valuation k (u * q ^ (-a)) * (valuation k q) ^ (a - b) := by
      rw [hval, hval, mul_assoc, ← zpow_add₀ hvq0]
      congr 1
      ring_nf
    -- so `v(u·q⁻ᵇ) > v(q)·v(q)^(a-b) = v(q)^(a-b+1) ≥ 1` as `a-b+1 ≤ 0`
    have hgt : 1 < valuation k (u * q ^ (-b)) := by
      have h2 : valuation k q * (valuation k q) ^ ((a : ℤ) - b) <
          valuation k (u * q ^ (-a)) * (valuation k q) ^ ((a : ℤ) - b) :=
        mul_lt_mul_of_pos_right hlow
          (zero_lt_iff.mpr (zpow_ne_zero _ hvq0))
      have h3 : (1 : ValueGroupWithZero k) ≤
          valuation k q * (valuation k q) ^ ((a : ℤ) - b) := by
        rw [show valuation k q * (valuation k q) ^ ((a : ℤ) - b) =
            (valuation k q) ^ ((a : ℤ) - b + 1) from by
          rw [zpow_add₀ hvq0, zpow_one, mul_comm]]
        obtain ⟨n, hn⟩ : ∃ n : ℕ, -((a : ℤ) - b + 1) = n :=
          ⟨(-((a : ℤ) - b + 1)).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
        rw [show ((a : ℤ) - b + 1) = -(n : ℤ) by omega, zpow_neg,
          one_le_inv₀ (zero_lt_iff.mpr (zpow_ne_zero _ hvq0)),
          zpow_natCast]
        exact pow_le_one₀ zero_le hq.le
      calc (1 : ValueGroupWithZero k)
          ≤ valuation k q * (valuation k q) ^ ((a : ℤ) - b) := h3
        _ < valuation k (u * q ^ (-a)) * (valuation k q) ^ ((a : ℤ) - b) :=
            h2
        _ = valuation k (u * q ^ (-b)) := hratio.symm
    exact absurd hhigh (not_le.mpr hgt)
  rcases lt_trichotomy m m' with h | h | h
  · exact (key m m' h hm.1 hm'.2).elim
  · exact h
  · exact (key m' m h hm'.1 hm.2).elim

/-- **The uniformisation point map** `kˣ → E_{q₀}(k)` (on nonzero
field elements; it will descend to `kˣ/q₀^ℤ`): normalise `u` into the
fundamental annulus by the canonical exponent
(`exists_zpow_mul_mem_annulus`, unique by
`annulus_exponent_unique`), send the representative `1` (the class of
`q₀^ℤ`) to zero and any other representative to its affine
uniformisation point. -/
noncomputable def pointMap (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq : valuation k q₀ < 1) (u : k) (hu0 : u ≠ 0) :
    (WeierstrassCurve.tateCurve q₀).toAffine.Point :=
  haveI := Classical.decEq k
  if h1 : u * q₀ ^
      (-(exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose) = 1 then 0
  else
    annulusPoint
      (u * q₀ ^ (-(exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose))
      q₀ (mul_ne_zero hu0 (zpow_ne_zero _ hq0)) h1 hq0
      (exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose_spec.2 hq
      (exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose_spec.1

/-- **The point map is invariant under `q₀`-power translation**: the
canonical annulus representative of `q₀ʲ·u` is that of `u` (exponents
shift by `j`, unique by `annulus_exponent_unique`), so the point map
descends to the quotient `kˣ/q₀^ℤ`. -/
theorem pointMap_zpow_mul (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq : valuation k q₀ < 1) (u : k) (hu0 : u ≠ 0) (j : ℤ) :
    pointMap q₀ hq0 hq (q₀ ^ j * u)
      (mul_ne_zero (zpow_ne_zero _ hq0) hu0) =
    pointMap q₀ hq0 hq u hu0 := by
  have hm := (exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose_spec
  have hm' := (exists_zpow_mul_mem_annulus q₀ hq0 hq (q₀ ^ j * u)
    (mul_ne_zero (zpow_ne_zero _ hq0) hu0)).choose_spec
  have hshift : (q₀ ^ j * u) * q₀ ^
      (-((exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose + j)) =
      u * q₀ ^ (-(exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose) := by
    rw [mul_comm (q₀ ^ j) u, mul_assoc, ← zpow_add₀ hq0]
    congr 2
    ring
  have huniq : (exists_zpow_mul_mem_annulus q₀ hq0 hq (q₀ ^ j * u)
      (mul_ne_zero (zpow_ne_zero _ hq0) hu0)).choose =
      (exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose + j := by
    refine annulus_exponent_unique q₀ hq0 hq (q₀ ^ j * u) hm' ?_
    rw [hshift]
    exact hm
  have hrep : (q₀ ^ j * u) * q₀ ^
      (-(exists_zpow_mul_mem_annulus q₀ hq0 hq (q₀ ^ j * u)
        (mul_ne_zero (zpow_ne_zero _ hq0) hu0)).choose) =
      u * q₀ ^ (-(exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose) := by
    rw [huniq, hshift]
  unfold pointMap
  simp only [hrep]
  split_ifs with ha hb hc
  · rfl
  · exact absurd (hrep ▸ ha) hb
  · exact absurd (hrep.symm ▸ hc) ha
  · rfl

/-- The point map depends only on the value of the parameter (its
nonvanishing proof is irrelevant). -/
theorem pointMap_congr {q₀ : k} {hq0 : q₀ ≠ 0} {hq : valuation k q₀ < 1}
    {u v : k} {hu : u ≠ 0} {hv : v ≠ 0} (h : u = v) :
    pointMap q₀ hq0 hq u hu = pointMap q₀ hq0 hq v hv := by
  subst h
  rfl

/-- **The point map on the quotient** `kˣ/q^ℤ → E_q(k)`: the class of
`u` goes to `pointMap u`, well-defined by `pointMap_zpow_mul`. -/
noncomputable def pointMapQuot (q : kˣ) (hq : valuation k (q : k) < 1) :
    (kˣ ⧸ Subgroup.zpowers q) →
      (WeierstrassCurve.tateCurve (q : k)).toAffine.Point := by
  refine Quotient.lift
    (fun u : kˣ ↦ pointMap (q : k) q.ne_zero hq (u : k) u.ne_zero) ?_
  intro a b hab
  obtain ⟨j, hj⟩ := QuotientGroup.leftRel_apply.mp hab
  have hval : ((b : k)) = ((q : k)) ^ j * (a : k) := by
    have h1 : a * q ^ j = b := by
      have h2 := congrArg (fun x : kˣ ↦ a * x) hj
      simpa using h2
    rw [← h1]
    push_cast
    ring
  calc pointMap (q : k) q.ne_zero hq (a : k) a.ne_zero
      = pointMap (q : k) q.ne_zero hq (((q : k)) ^ j * (a : k))
          (mul_ne_zero (zpow_ne_zero _ q.ne_zero) a.ne_zero) :=
        (pointMap_zpow_mul (q : k) q.ne_zero hq (a : k) a.ne_zero j).symm
    _ = pointMap (q : k) q.ne_zero hq (b : k) b.ne_zero :=
        pointMap_congr hval.symm

/-- The identity class goes to zero: the canonical annulus
representative of `1` is `1` itself. -/
theorem pointMap_one (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq : valuation k q₀ < 1) :
    pointMap q₀ hq0 hq 1 one_ne_zero = 0 := by
  have hspec := (exists_zpow_mul_mem_annulus q₀ hq0 hq 1
    one_ne_zero).choose_spec
  have h0 : (exists_zpow_mul_mem_annulus q₀ hq0 hq 1
      one_ne_zero).choose = 0 := by
    refine annulus_exponent_unique q₀ hq0 hq 1 hspec ⟨?_, ?_⟩
    · simpa using hq
    · simp
  have hcond : (1 : k) * q₀ ^
      (-(exists_zpow_mul_mem_annulus q₀ hq0 hq 1
        one_ne_zero).choose) = 1 := by
    rw [h0]
    simp
  unfold pointMap
  rw [dif_pos hcond]

/-- **The kernel of the point map**: `pointMap u = 0` exactly when `u`
is a power of `q₀` — the class of `u` in `kˣ/q₀^ℤ` is trivial. -/
theorem pointMap_eq_zero_iff (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq : valuation k q₀ < 1) (u : k) (hu0 : u ≠ 0) :
    pointMap q₀ hq0 hq u hu0 = 0 ↔ ∃ m : ℤ, u = q₀ ^ m := by
  constructor
  · intro h
    unfold pointMap at h
    split_ifs at h with h1
    · refine ⟨(exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose, ?_⟩
      have h3 : u * q₀ ^
          (-(exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose) *
          q₀ ^ (exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose
          = u := by
        rw [mul_assoc, ← zpow_add₀ hq0]
        simp
      calc u = u * q₀ ^
            (-(exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose) *
            q₀ ^ (exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose :=
            h3.symm
        _ = 1 * q₀ ^
            (exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose := by
            rw [h1]
        _ = q₀ ^
            (exists_zpow_mul_mem_annulus q₀ hq0 hq u hu0).choose :=
            one_mul _
    · exact absurd h (by simp [annulusPoint])
  · rintro ⟨m, rfl⟩
    calc pointMap q₀ hq0 hq (q₀ ^ m) hu0
        = pointMap q₀ hq0 hq (q₀ ^ m * 1)
          (mul_ne_zero (zpow_ne_zero _ hq0) one_ne_zero) :=
          pointMap_congr (mul_one _).symm
      _ = pointMap q₀ hq0 hq 1 one_ne_zero :=
          pointMap_zpow_mul q₀ hq0 hq 1 one_ne_zero m
      _ = 0 := pointMap_one q₀ hq0 hq

@[simp]
theorem pointMapQuot_mk (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) :
    pointMapQuot q hq (QuotientGroup.mk u) =
      pointMap (q : k) q.ne_zero hq (u : k) u.ne_zero :=
  rfl

/-- **The quotient point map has trivial kernel** (as a pointed map):
the class of `u` goes to zero exactly when it is the trivial class. -/
theorem pointMapQuot_eq_zero_iff (q : kˣ)
    (hq : valuation k (q : k) < 1) (u : kˣ) :
    pointMapQuot q hq (QuotientGroup.mk u) = 0 ↔
      (QuotientGroup.mk u : kˣ ⧸ Subgroup.zpowers q) = 1 := by
  rw [pointMapQuot_mk, pointMap_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    have hu : u = q ^ m := by
      ext
      push_cast
      exact hm
    rw [hu, QuotientGroup.eq_one_iff]
    exact zpow_mem (Subgroup.mem_zpowers q) m
  · intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      ((QuotientGroup.eq_one_iff u).mp h)
    refine ⟨m, ?_⟩
    rw [← hm]
    push_cast
    rfl

end Annulus

end TateCurve

end
