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

public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateCurve
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateCurveConstruction
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateParameter
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Data.PNat.Equiv

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

omit [CharZero k] in
/-- Ultrametric bound for a convergent sum: the valuation of the sum is
at most any common bound of the terms. -/
theorem valuation_tsum_le {ι : Type*} {f : ι → k} (hf : Summable f)
    (c : ValueGroupWithZero k) (hbound : ∀ n, valuation k (f n) ≤ c) :
    valuation k (∑' n, f n) ≤ c := by
  by_contra hlt
  rw [not_le] at hlt
  have hpart : ∀ s : Finset ι, valuation k (∑ n ∈ s, f n) ≤ c :=
    fun s => Valuation.map_sum_le _ fun n _ => hbound n
  have hS : HasSum f (∑' n, f n) := hf.hasSum
  simp only [HasSum, SummationFilter.unconditional_filter,
    (IsValuativeTopology.hasBasis_nhds (∑' n, f n)).tendsto_right_iff] at hS
  obtain ⟨s, hs⟩ := (hS (Units.mk0 _ (ne_of_gt
    (lt_of_le_of_lt zero_le hlt))) trivial).exists
  simp only [Set.mem_setOf_eq] at hs
  refine absurd ?_ (lt_irrefl (valuation k (∑' n, f n)))
  calc valuation k (∑' n, f n)
      = valuation k ((∑ n ∈ s, f n) - ((∑ n ∈ s, f n) - ∑' n, f n)) := by
        rw [sub_sub_cancel]
    _ ≤ max (valuation k (∑ n ∈ s, f n))
        (valuation k ((∑ n ∈ s, f n) - ∑' n, f n)) :=
        Valuation.map_sub _ _ _
    _ < valuation k (∑' n, f n) :=
        max_lt (lt_of_le_of_lt (hpart s) hlt) hs


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
/-! ### Naturality of `evalA … XA` under valuative extensions

For the gluing of the finite-level uniformisation to a separable
closure (`TateSepClosure.lean`), the evaluation series needs to commute
with a valuative extension `k → l` of nonarchimedean local fields — the
analogue of `TateCurve.evalInt_map` (`TateCurveBaseChange.lean`) for
the two-variable coefficient ring, on the fundamental annulus. -/

section Naturality

variable {l : Type*} [Field l] [ValuativeRel l] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] [CharZero l] [Algebra k l]
  [ValuativeExtension k l]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k]
  [ValuativeRel l] [TopologicalSpace l] [IsNonarchimedeanLocalField l] in
/-- **The coefficient-ring evaluation commutes with a valuative
extension**: `coeffRingEval` is built from `Polynomial.aeval`, whose
naturality under any ring homomorphism reduces the claim to checking
it on the two generators of `ℚ[X]` (constants, where it is
`ℚ`-hom-uniqueness, and `X`, where both sides are `algebraMap k l u₀`
by definition). -/
theorem coeffRingEval_map (u₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (h0' : algebraMap k l u₀ ≠ 0) (h1' : algebraMap k l u₀ ≠ 1)
    (F : CoeffRing) :
    algebraMap k l (coeffRingEval u₀ h0 h1 F) =
      coeffRingEval (algebraMap k l u₀) h0' h1' F := by
  have hext : ((algebraMap k l).comp (coeffRingEval u₀ h0 h1)).comp
        (algebraMap (Polynomial ℚ) CoeffRing) =
      (coeffRingEval (algebraMap k l u₀) h0' h1').comp
        (algebraMap (Polynomial ℚ) CoeffRing) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, coeffRingEval_algebraMap,
        Polynomial.aeval_C]
      exact RingHom.congr_fun (Subsingleton.elim
        ((algebraMap k l).comp (algebraMap ℚ k)) (algebraMap ℚ l)) a
    · simp only [RingHom.comp_apply, coeffRingEval_algebraMap,
        Polynomial.aeval_X]
  have hfull : (algebraMap k l).comp (coeffRingEval u₀ h0 h1) =
      coeffRingEval (algebraMap k l u₀) h0' h1' :=
    IsLocalization.ringHom_ext
      (Submonoid.powers (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ))
      hext
  exact RingHom.congr_fun hfull F

omit [CharZero k] in
/-- Ultrametric bound for a `HasSum`, transported from a uniform bound
on the tail after splitting off the first `N` terms (mirror of
`valuation_tsum_le` for an arbitrary partial-sum remainder, using
`hasSum_nat_add_iff` to identify the remainder as the sum of the
shifted sequence). -/
theorem valuation_hasSum_sub_sum_le {f : ℕ → k} {a : k} (hf : HasSum f a)
    (N : ℕ) (c : ValueGroupWithZero k)
    (hbound : ∀ n, valuation k (f (n + N)) ≤ c) :
    valuation k (a - ∑ i ∈ Finset.range N, f i) ≤ c := by
  have hshift : HasSum (fun n => f (n + N)) (a - ∑ i ∈ Finset.range N, f i) :=
    (hasSum_nat_add_iff N).mpr (by rw [sub_add_cancel]; exact hf)
  rw [← hshift.tsum_eq]
  exact valuation_tsum_le hshift.summable c hbound

set_option maxHeartbeats 1000000 in
/-- **`evalA … XA` commutes with a valuative extension**, on the
fundamental annulus: mirror of `TateCurve.evalInt_map`, using
`coeffRingEval_map` for the finite-sum part and transporting the
`k`-side tail bound (`valuation_coeffRingEval_XA_le`) along the
strictly monotone map of value groups
(`ValuativeExtension.mapValueGroupWithZero`) for one half of the
sandwich, with a freshly proven `l`-side tail bound for the other
half — no continuity argument is needed. -/
theorem evalA_XA_map (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq : valuation k q₀ < valuation k u₀)
    (h0' : algebraMap k l u₀ ≠ 0) (h1' : algebraMap k l u₀ ≠ 1) :
    algebraMap k l (evalA u₀ q₀ h0 h1 XA) =
      evalA (algebraMap k l u₀) (algebraMap k l q₀) h0' h1' XA := by
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  set w : k := q₀ * u₀⁻¹ with hwdef
  have hw : valuation k w < 1 := by
    rw [hwdef, map_mul, map_inv₀]
    calc valuation k q₀ * (valuation k u₀)⁻¹
        < valuation k u₀ * (valuation k u₀)⁻¹ :=
          mul_lt_mul_of_pos_right hq (zero_lt_iff.mpr (inv_ne_zero hv0))
      _ = 1 := mul_inv_cancel₀ hv0
  have hu' : valuation l (algebraMap k l u₀) ≤ 1 := by
    rw [← ValuativeExtension.mapValueGroupWithZero_valuation]
    calc ValuativeExtension.mapValueGroupWithZero k l (valuation k u₀)
        ≤ ValuativeExtension.mapValueGroupWithZero k l 1 :=
          ValuativeExtension.mapValueGroupWithZero_strictMono.monotone hu
      _ = 1 := map_one _
  have hq' : valuation l (algebraMap k l q₀) <
      valuation l (algebraMap k l u₀) := by
    rw [← ValuativeExtension.mapValueGroupWithZero_valuation,
      ← ValuativeExtension.mapValueGroupWithZero_valuation]
    exact ValuativeExtension.mapValueGroupWithZero_strictMono hq
  have hw' : valuation l (algebraMap k l w) < 1 :=
    TateCurve.valuation_algebraMap_lt_one hw
  have hwmap : algebraMap k l w =
      algebraMap k l q₀ * (algebraMap k l u₀)⁻¹ := by
    rw [hwdef, map_mul, map_inv₀]
  set fk : ℕ → k := fun n => coeffRingEval u₀ h0 h1
    (PowerSeries.coeff n XA) * q₀ ^ n with hfkdef
  set fl : ℕ → l := fun n => coeffRingEval (algebraMap k l u₀) h0' h1'
    (PowerSeries.coeff n XA) * (algebraMap k l q₀) ^ n with hfldef
  have hsumk : Summable fk := summable_evalA_XA u₀ q₀ h0 h1 hu hq
  have hsuml : Summable fl := summable_evalA_XA (algebraMap k l u₀)
    (algebraMap k l q₀) h0' h1' hu' hq'
  set a : k := ∑' n, fk n with hadef
  set a' : l := ∑' n, fl n with ha'def
  rw [show evalA u₀ q₀ h0 h1 XA = a from rfl,
    show evalA (algebraMap k l u₀) (algebraMap k l q₀) h0' h1' XA = a' from rfl]
  rw [← sub_eq_zero]
  by_contra hcon
  obtain ⟨N, hN⟩ := exists_pow_valuation_lt (algebraMap k l w) hw'
    (Units.mk0 (valuation l (algebraMap k l a - a'))
      ((valuation l).ne_zero_iff.mpr hcon))
  set N' : ℕ := max N 1 with hN'def
  have hN'1 : 1 ≤ N' := le_max_right N 1
  have hN' : valuation l (algebraMap k l w) ^ N' <
      valuation l (algebraMap k l a - a') :=
    lt_of_le_of_lt (pow_le_pow_right_of_le_one' hw'.le (le_max_left N 1)) hN
  have hmapsum : algebraMap k l (∑ i ∈ Finset.range N', fk i) =
      ∑ i ∈ Finset.range N', fl i := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hfkdef, hfldef, map_mul, map_pow, coeffRingEval_map]
  have hktail : valuation k (a - ∑ i ∈ Finset.range N', fk i) ≤
      valuation k w ^ N' :=
    valuation_hasSum_sub_sum_le hsumk.hasSum N' (valuation k w ^ N')
      fun n => by
        have hb := valuation_coeffRingEval_XA_le u₀ h0 h1 hu
          (show n + N' ≠ 0 by omega)
        rw [hfkdef]
        show valuation k (coeffRingEval u₀ h0 h1
            (PowerSeries.coeff (n + N') XA) * q₀ ^ (n + N')) ≤ _
        rw [map_mul, map_pow]
        calc valuation k (coeffRingEval u₀ h0 h1
              (PowerSeries.coeff (n + N') XA)) * valuation k q₀ ^ (n + N')
            ≤ ((valuation k u₀) ^ (n + N'))⁻¹ * valuation k q₀ ^ (n + N') :=
              mul_le_mul_left hb _
          _ = valuation k w ^ (n + N') := by
              rw [hwdef, map_mul, map_inv₀, mul_pow, inv_pow]
              exact mul_comm _ _
          _ ≤ valuation k w ^ N' :=
              pow_le_pow_right_of_le_one' hw.le (le_add_self)
  have hltail : valuation l (a' - ∑ i ∈ Finset.range N', fl i) ≤
      valuation l (algebraMap k l w) ^ N' :=
    valuation_hasSum_sub_sum_le hsuml.hasSum N'
      (valuation l (algebraMap k l w) ^ N') fun n => by
        have hb := valuation_coeffRingEval_XA_le (algebraMap k l u₀) h0' h1'
          hu' (show n + N' ≠ 0 by omega)
        rw [hfldef]
        show valuation l (coeffRingEval (algebraMap k l u₀) h0' h1'
            (PowerSeries.coeff (n + N') XA) *
            (algebraMap k l q₀) ^ (n + N')) ≤ _
        rw [map_mul, map_pow]
        calc valuation l (coeffRingEval (algebraMap k l u₀) h0' h1'
              (PowerSeries.coeff (n + N') XA)) *
              valuation l (algebraMap k l q₀) ^ (n + N')
            ≤ ((valuation l (algebraMap k l u₀)) ^ (n + N'))⁻¹ *
                valuation l (algebraMap k l q₀) ^ (n + N') :=
              mul_le_mul_left hb _
          _ = valuation l (algebraMap k l w) ^ (n + N') := by
              rw [hwmap, map_mul, map_inv₀, mul_pow, inv_pow]
              exact mul_comm _ _
          _ ≤ valuation l (algebraMap k l w) ^ N' :=
              pow_le_pow_right_of_le_one' hw'.le (le_add_self)
  have h1 : valuation l (algebraMap k l a -
      ∑ i ∈ Finset.range N', fl i) ≤ valuation l (algebraMap k l w) ^ N' := by
    rw [← hmapsum, ← map_sub]
    calc valuation l (algebraMap k l (a - ∑ i ∈ Finset.range N', fk i))
        = ValuativeExtension.mapValueGroupWithZero k l
            (valuation k (a - ∑ i ∈ Finset.range N', fk i)) :=
          (ValuativeExtension.mapValueGroupWithZero_valuation _).symm
      _ ≤ ValuativeExtension.mapValueGroupWithZero k l (valuation k w ^ N') :=
          ValuativeExtension.mapValueGroupWithZero_strictMono.monotone hktail
      _ = valuation l (algebraMap k l w) ^ N' := by
          rw [map_pow, ValuativeExtension.mapValueGroupWithZero_valuation]
  refine absurd ?_ (lt_irrefl (valuation l (algebraMap k l a - a')))
  calc valuation l (algebraMap k l a - a')
      = valuation l ((algebraMap k l a - ∑ i ∈ Finset.range N', fl i) -
          (a' - ∑ i ∈ Finset.range N', fl i)) := by congr 1; ring
    _ ≤ max _ _ := Valuation.map_sub _ _ _
    _ ≤ valuation l (algebraMap k l w) ^ N' := max_le h1 hltail
    _ < _ := hN'

set_option maxHeartbeats 1000000 in
/-- **`evalA … YA` commutes with a valuative extension**, on the
fundamental annulus: mirror of `TateCurve.evalInt_map`, using
`coeffRingEval_map` for the finite-sum part and transporting the
`k`-side tail bound (`valuation_coeffRingEval_YA_le`) along the
strictly monotone map of value groups
(`ValuativeExtension.mapValueGroupWithZero`) for one half of the
sandwich, with a freshly proven `l`-side tail bound for the other
half — no continuity argument is needed. -/
theorem evalA_YA_map (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq : valuation k q₀ < valuation k u₀)
    (h0' : algebraMap k l u₀ ≠ 0) (h1' : algebraMap k l u₀ ≠ 1) :
    algebraMap k l (evalA u₀ q₀ h0 h1 YA) =
      evalA (algebraMap k l u₀) (algebraMap k l q₀) h0' h1' YA := by
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  set w : k := q₀ * u₀⁻¹ with hwdef
  have hw : valuation k w < 1 := by
    rw [hwdef, map_mul, map_inv₀]
    calc valuation k q₀ * (valuation k u₀)⁻¹
        < valuation k u₀ * (valuation k u₀)⁻¹ :=
          mul_lt_mul_of_pos_right hq (zero_lt_iff.mpr (inv_ne_zero hv0))
      _ = 1 := mul_inv_cancel₀ hv0
  have hu' : valuation l (algebraMap k l u₀) ≤ 1 := by
    rw [← ValuativeExtension.mapValueGroupWithZero_valuation]
    calc ValuativeExtension.mapValueGroupWithZero k l (valuation k u₀)
        ≤ ValuativeExtension.mapValueGroupWithZero k l 1 :=
          ValuativeExtension.mapValueGroupWithZero_strictMono.monotone hu
      _ = 1 := map_one _
  have hq' : valuation l (algebraMap k l q₀) <
      valuation l (algebraMap k l u₀) := by
    rw [← ValuativeExtension.mapValueGroupWithZero_valuation,
      ← ValuativeExtension.mapValueGroupWithZero_valuation]
    exact ValuativeExtension.mapValueGroupWithZero_strictMono hq
  have hw' : valuation l (algebraMap k l w) < 1 :=
    TateCurve.valuation_algebraMap_lt_one hw
  have hwmap : algebraMap k l w =
      algebraMap k l q₀ * (algebraMap k l u₀)⁻¹ := by
    rw [hwdef, map_mul, map_inv₀]
  set fk : ℕ → k := fun n => coeffRingEval u₀ h0 h1
    (PowerSeries.coeff n YA) * q₀ ^ n with hfkdef
  set fl : ℕ → l := fun n => coeffRingEval (algebraMap k l u₀) h0' h1'
    (PowerSeries.coeff n YA) * (algebraMap k l q₀) ^ n with hfldef
  have hsumk : Summable fk := summable_evalA_YA u₀ q₀ h0 h1 hu hq
  have hsuml : Summable fl := summable_evalA_YA (algebraMap k l u₀)
    (algebraMap k l q₀) h0' h1' hu' hq'
  set a : k := ∑' n, fk n with hadef
  set a' : l := ∑' n, fl n with ha'def
  rw [show evalA u₀ q₀ h0 h1 YA = a from rfl,
    show evalA (algebraMap k l u₀) (algebraMap k l q₀) h0' h1' YA = a' from rfl]
  rw [← sub_eq_zero]
  by_contra hcon
  obtain ⟨N, hN⟩ := exists_pow_valuation_lt (algebraMap k l w) hw'
    (Units.mk0 (valuation l (algebraMap k l a - a'))
      ((valuation l).ne_zero_iff.mpr hcon))
  set N' : ℕ := max N 1 with hN'def
  have hN'1 : 1 ≤ N' := le_max_right N 1
  have hN' : valuation l (algebraMap k l w) ^ N' <
      valuation l (algebraMap k l a - a') :=
    lt_of_le_of_lt (pow_le_pow_right_of_le_one' hw'.le (le_max_left N 1)) hN
  have hmapsum : algebraMap k l (∑ i ∈ Finset.range N', fk i) =
      ∑ i ∈ Finset.range N', fl i := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hfkdef, hfldef, map_mul, map_pow, coeffRingEval_map]
  have hktail : valuation k (a - ∑ i ∈ Finset.range N', fk i) ≤
      valuation k w ^ N' :=
    valuation_hasSum_sub_sum_le hsumk.hasSum N' (valuation k w ^ N')
      fun n => by
        have hb := valuation_coeffRingEval_YA_le u₀ h0 h1 hu
          (show n + N' ≠ 0 by omega)
        rw [hfkdef]
        show valuation k (coeffRingEval u₀ h0 h1
            (PowerSeries.coeff (n + N') YA) * q₀ ^ (n + N')) ≤ _
        rw [map_mul, map_pow]
        calc valuation k (coeffRingEval u₀ h0 h1
              (PowerSeries.coeff (n + N') YA)) * valuation k q₀ ^ (n + N')
            ≤ ((valuation k u₀) ^ (n + N'))⁻¹ * valuation k q₀ ^ (n + N') :=
              mul_le_mul_left hb _
          _ = valuation k w ^ (n + N') := by
              rw [hwdef, map_mul, map_inv₀, mul_pow, inv_pow]
              exact mul_comm _ _
          _ ≤ valuation k w ^ N' :=
              pow_le_pow_right_of_le_one' hw.le (le_add_self)
  have hltail : valuation l (a' - ∑ i ∈ Finset.range N', fl i) ≤
      valuation l (algebraMap k l w) ^ N' :=
    valuation_hasSum_sub_sum_le hsuml.hasSum N'
      (valuation l (algebraMap k l w) ^ N') fun n => by
        have hb := valuation_coeffRingEval_YA_le (algebraMap k l u₀) h0' h1'
          hu' (show n + N' ≠ 0 by omega)
        rw [hfldef]
        show valuation l (coeffRingEval (algebraMap k l u₀) h0' h1'
            (PowerSeries.coeff (n + N') YA) *
            (algebraMap k l q₀) ^ (n + N')) ≤ _
        rw [map_mul, map_pow]
        calc valuation l (coeffRingEval (algebraMap k l u₀) h0' h1'
              (PowerSeries.coeff (n + N') YA)) *
              valuation l (algebraMap k l q₀) ^ (n + N')
            ≤ ((valuation l (algebraMap k l u₀)) ^ (n + N'))⁻¹ *
                valuation l (algebraMap k l q₀) ^ (n + N') :=
              mul_le_mul_left hb _
          _ = valuation l (algebraMap k l w) ^ (n + N') := by
              rw [hwmap, map_mul, map_inv₀, mul_pow, inv_pow]
              exact mul_comm _ _
          _ ≤ valuation l (algebraMap k l w) ^ N' :=
              pow_le_pow_right_of_le_one' hw'.le (le_add_self)
  have h1 : valuation l (algebraMap k l a -
      ∑ i ∈ Finset.range N', fl i) ≤ valuation l (algebraMap k l w) ^ N' := by
    rw [← hmapsum, ← map_sub]
    calc valuation l (algebraMap k l (a - ∑ i ∈ Finset.range N', fk i))
        = ValuativeExtension.mapValueGroupWithZero k l
            (valuation k (a - ∑ i ∈ Finset.range N', fk i)) :=
          (ValuativeExtension.mapValueGroupWithZero_valuation _).symm
      _ ≤ ValuativeExtension.mapValueGroupWithZero k l (valuation k w ^ N') :=
          ValuativeExtension.mapValueGroupWithZero_strictMono.monotone hktail
      _ = valuation l (algebraMap k l w) ^ N' := by
          rw [map_pow, ValuativeExtension.mapValueGroupWithZero_valuation]
  refine absurd ?_ (lt_irrefl (valuation l (algebraMap k l a - a')))
  calc valuation l (algebraMap k l a - a')
      = valuation l ((algebraMap k l a - ∑ i ∈ Finset.range N', fl i) -
          (a' - ∑ i ∈ Finset.range N', fl i)) := by congr 1; ring
    _ ≤ max _ _ := Valuation.map_sub _ _ _
    _ ≤ valuation l (algebraMap k l w) ^ N' := max_le h1 hltail
    _ < _ := hN'

omit [CharZero k] [CharZero l] in
/-- **The Tate curve is functorial in a valuative extension**: mapping
`E_{q₀}` over `k` along `algebraMap k l` gives `E_{algebraMap k l q₀}`
over `l` — the coefficients `a₄(q₀)`, `a₆(q₀)` are `evalInt`-evaluations
of fixed integral power series (`WeierstrassCurve.tateA₄_eq_evalInt`,
`WeierstrassCurve.tateA₆_eq_evalInt`), which commute with the
extension by `evalInt_map`. -/
theorem tateCurve_map (q₀ : k) (hq0 : valuation k q₀ < 1) :
    (WeierstrassCurve.tateCurve q₀).map (algebraMap k l) =
      WeierstrassCurve.tateCurve (algebraMap k l q₀) := by
  have hq0' : valuation l (algebraMap k l q₀) < 1 :=
    valuation_algebraMap_lt_one hq0
  have h4 : algebraMap k l (WeierstrassCurve.tateA₄ q₀) =
      WeierstrassCurve.tateA₄ (algebraMap k l q₀) := by
    rw [WeierstrassCurve.tateA₄_eq_evalInt q₀ hq0, evalInt_map q₀ hq0,
      ← WeierstrassCurve.tateA₄_eq_evalInt (algebraMap k l q₀) hq0']
  have h6 : algebraMap k l (WeierstrassCurve.tateA₆ q₀) =
      WeierstrassCurve.tateA₆ (algebraMap k l q₀) := by
    rw [WeierstrassCurve.tateA₆_eq_evalInt q₀ hq0, evalInt_map q₀ hq0,
      ← WeierstrassCurve.tateA₆_eq_evalInt (algebraMap k l q₀) hq0']
  simp only [WeierstrassCurve.tateCurve, WeierstrassCurve.map, map_one,
    map_zero, h4, h6]

end Naturality


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


omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The constant coefficient of `XA` evaluates to `u₀/(1-u₀)²`. -/
theorem coeffRingEval_coeff_XA_zero (u₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) :
    coeffRingEval u₀ h0 h1 (PowerSeries.coeff 0 XA) =
      u₀ / (1 - u₀) ^ 2 := by
  rw [XA, map_add, PowerSeries.coeff_C, if_pos rfl, PowerSeries.coeff_mk]
  simp only [Nat.divisors_zero, Finset.sum_empty, add_zero]
  rw [map_mul, map_pow, coeffRingEval_uA, coeffRingEval_vA_inv,
    div_eq_mul_inv, inv_pow]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The constant coefficient of `YA` evaluates to `u₀²/(1-u₀)³`. -/
theorem coeffRingEval_coeff_YA_zero (u₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) :
    coeffRingEval u₀ h0 h1 (PowerSeries.coeff 0 YA) =
      u₀ ^ 2 / (1 - u₀) ^ 3 := by
  rw [YA, map_add, PowerSeries.coeff_C, if_pos rfl, PowerSeries.coeff_mk]
  simp only [Nat.divisors_zero, Finset.sum_empty, add_zero]
  rw [map_mul, map_pow, map_pow, coeffRingEval_uA, coeffRingEval_vA_inv,
    div_eq_mul_inv, inv_pow]

/-- For a parameter already in the fundamental annulus, the canonical
exponent is `0` and the point map is the annulus point directly. -/
theorem pointMap_of_mem_annulus (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq : valuation k q₀ < 1) (u₀ : k) (hu0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hlow : valuation k q₀ < valuation k u₀)
    (hhigh : valuation k u₀ ≤ 1) :
    pointMap q₀ hq0 hq u₀ hu0 =
      annulusPoint u₀ q₀ hu0 h1 hq0 hhigh hq hlow := by
  have h0 : (exists_zpow_mul_mem_annulus q₀ hq0 hq u₀ hu0).choose = 0 := by
    refine annulus_exponent_unique q₀ hq0 hq u₀
      (exists_zpow_mul_mem_annulus q₀ hq0 hq u₀ hu0).choose_spec
      ⟨?_, ?_⟩
    · simpa using hlow
    · simpa using hhigh
  have hrep : u₀ * q₀ ^
      (-(exists_zpow_mul_mem_annulus q₀ hq0 hq u₀ hu0).choose) = u₀ := by
    rw [h0]
    simp
  unfold pointMap
  simp only [hrep]
  split_ifs with ha
  · exact absurd (hrep ▸ ha) h1
  · rfl

omit [CharZero k] in
/-- The geometric series is summable on the open unit disc. -/
theorem summable_geometric_nonarch (x : k) (hx : valuation k x < 1) :
    Summable (fun n : ℕ ↦ x ^ n) :=
  summable_of_valuation_le_pow hx (fun n ↦ n) (fun N ↦ Set.finite_Iio N)
    (fun n ↦ by rw [map_pow])

omit [CharZero k] in
/-- **The nonarchimedean geometric series**: for `|x| < 1`,
`∑ xⁿ = (1-x)⁻¹` — telescoping against the shift, no norm needed. -/
theorem tsum_geometric_nonarch (x : k) (hx : valuation k x < 1) :
    (∑' n : ℕ, x ^ n) = (1 - x)⁻¹ := by
  have hxne : x ≠ 1 := by
    rintro rfl
    simp at hx
  have hsum := summable_geometric_nonarch x hx
  have h0 := hsum.tsum_eq_zero_add
  rw [pow_zero] at h0
  have hmul : x * (∑' n : ℕ, x ^ n) = (∑' n : ℕ, x ^ n) - 1 := by
    have hx1 : (∑' n : ℕ, x ^ (n + 1)) = (∑' n : ℕ, x ^ n) - 1 := by
      linear_combination -h0
    rw [← hx1, ← tsum_mul_left]
    exact tsum_congr fun n ↦ by ring
  refine eq_inv_of_mul_eq_one_left ?_
  linear_combination -hmul

omit [CharZero k] in
/-- `∑ n·xⁿ` is summable on the open unit disc. -/
theorem summable_nat_mul_geometric_nonarch (x : k)
    (hx : valuation k x < 1) :
    Summable (fun n : ℕ ↦ (n : k) * x ^ n) := by
  refine summable_of_valuation_le_pow hx (fun n ↦ n)
    (fun N ↦ Set.finite_Iio N) (fun n ↦ ?_)
  rw [map_mul, map_pow]
  calc valuation k ((n : k)) * valuation k x ^ n
      ≤ 1 * valuation k x ^ n := by
        refine mul_le_mul_left ?_ _
        have h := valuation_intCast_le_one (R := k) n
        simpa using h
    _ = valuation k x ^ n := one_mul _

omit [CharZero k] in
/-- **The nonarchimedean derivative-geometric series**: for `|x| < 1`,
`∑ n·xⁿ = x/(1-x)²` — the Cauchy square of the geometric series
counted along antidiagonals, minus the geometric series. -/
theorem tsum_nat_mul_geometric_nonarch (x : k)
    (hx : valuation k x < 1) :
    (∑' n : ℕ, (n : k) * x ^ n) = x / (1 - x) ^ 2 := by
  have hxne : x ≠ 1 := by
    rintro rfl
    simp at hx
  have h1x : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne)
  have hsum := summable_geometric_nonarch x hx
  have hnsum := summable_nat_mul_geometric_nonarch x hx
  have hkey := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal (A := ℕ)
    hsum hsum (summable_mul_prod hsum hsum)
  have hterm : ∀ n : ℕ,
      (∑ kl ∈ Finset.antidiagonal n, x ^ kl.1 * x ^ kl.2) =
      ((n : k) + 1) * x ^ n := by
    intro n
    have h1 : ∀ kl ∈ Finset.antidiagonal n,
        x ^ kl.1 * x ^ kl.2 = x ^ n := by
      intro kl hkl
      rw [← pow_add, Finset.mem_antidiagonal.mp hkl]
    rw [Finset.sum_congr rfl h1, Finset.sum_const,
      Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    push_cast
    ring
  rw [tsum_geometric_nonarch x hx] at hkey
  have h2 : (∑' n : ℕ, ((n : k) + 1) * x ^ n) =
      (1 - x)⁻¹ * (1 - x)⁻¹ := by
    rw [hkey]
    exact tsum_congr fun n ↦ (hterm n).symm
  have hsplit : (∑' n : ℕ, ((n : k) + 1) * x ^ n) =
      (∑' n : ℕ, (n : k) * x ^ n) + (∑' n : ℕ, x ^ n) := by
    rw [← hnsum.tsum_add hsum]
    exact tsum_congr fun n ↦ by ring
  have h3 : (∑' n : ℕ, (n : k) * x ^ n) =
      (1 - x)⁻¹ * (1 - x)⁻¹ - (1 - x)⁻¹ := by
    rw [tsum_geometric_nonarch x hx] at hsplit
    linear_combination hsplit.symm.trans h2
  rw [h3]
  field_simp
  ring

omit [CharZero k] in
/-- A summable double series over `ℕ+ × ℕ+` has sum the iterated sum
of its rows (`k`-version of the construction file's
`hasSum_prod_pnat`). -/
theorem hasSum_prod_pnat_nonarch {T : ℕ+ × ℕ+ → k} {F : ℕ+ → k}
    (hsum : Summable T)
    (hfib : ∀ n : ℕ+, HasSum (fun m : ℕ+ ↦ T (n, m)) (F n)) :
    HasSum T (∑' n : ℕ+, F n) := by
  simpa [hsum.tsum_prod' (fun n ↦ (hfib n).summable),
    tsum_congr fun n ↦ (hfib n).tsum_eq] using hsum.hasSum

omit [CharZero k] in
/-- Collecting a double series `∑_{n,m} g(m)x^{nm}` by powers of `x`
(`k`-version of the construction file's `hasSum_divisor_collect`): the
coefficient of `x^N` is the divisor sum `∑_{d ∣ N} g d`. -/
theorem hasSum_divisor_collect_nonarch (g : ℕ → k) {x : k} {S : k}
    (hT : HasSum
      (fun p : ℕ+ × ℕ+ ↦ g (p.2 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) S) :
    HasSum (fun N : ℕ+ ↦
      (∑ d ∈ (N : ℕ).divisors, g d) * x ^ (N : ℕ)) S := by
  apply ((sigmaAntidiagonalEquivProd.hasSum_iff).mpr hT).sigma
  intro N
  have h2 := hasSum_fintype (fun c : ((N : ℕ).divisorsAntidiagonal) ↦
    (g c.1.2 * x ^ (c.1.1 * c.1.2) : k))
  have hval : (∑ c : ((N : ℕ).divisorsAntidiagonal),
      (g c.1.2 * x ^ (c.1.1 * c.1.2) : k))
      = (∑ d ∈ (N : ℕ).divisors, g d) * x ^ (N : ℕ) := by
    rw [Finset.univ_eq_attach,
      Finset.sum_attach ((N : ℕ).divisorsAntidiagonal)
        (fun p ↦ (g p.2 * x ^ (p.1 * p.2) : k)),
      show (∑ p ∈ (N : ℕ).divisorsAntidiagonal,
          (g p.2 * x ^ (p.1 * p.2) : k))
          = ∑ p ∈ (N : ℕ).divisorsAntidiagonal, (g p.2 * x ^ (N : ℕ) : k)
        from Finset.sum_congr rfl fun p hp ↦ by
          rw [(Nat.mem_divisorsAntidiagonal.mp hp).1],
      ← Finset.sum_mul, Nat.sum_divisorsAntidiagonal' (f := fun _ d ↦ (g d : k))]
  rw [hval] at h2
  refine h2.congr_fun fun c ↦ ?_
  simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
    divisorsAntidiagonalFactors, PNat.mk_coe]

omit [CharZero k] in
/-- Two-index summability of the Lambert double series in the general
window `|q₀| < 1`, `|q₀·w| < 1` (allowing `|w| > 1`, as for
`w = u₀⁻¹` with `u₀` interior to the annulus). -/
theorem summable_lambert_prod' (w q₀ : k) (hq : valuation k q₀ < 1)
    (hqw : valuation k (q₀ * w) < 1) :
    Summable (fun p : ℕ+ × ℕ+ ↦
      ((p.2 : ℕ) : k) * w ^ (p.2 : ℕ) * q₀ ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  have hfin : ∀ N : ℕ, {p : ℕ+ × ℕ+ |
      (fun p : ℕ+ × ℕ+ ↦ (p.1 : ℕ) * (p.2 : ℕ)) p < N}.Finite := by
    intro N
    have hinj : Function.Injective
        (fun p : ℕ+ × ℕ+ ↦ ((p.1 : ℕ), (p.2 : ℕ))) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (PNat.coe_injective hab.1) (PNat.coe_injective hab.2)
    refine Set.Finite.subset
      (((Set.finite_Iio N).prod (Set.finite_Iio N)).preimage
        hinj.injOn) ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    constructor
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_right _ p.2.pos) hp
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ p.1.pos) hp
  have hj1 : ∀ j : ℕ+, valuation k (((j : ℕ) : k)) ≤ 1 := by
    intro j
    have h := valuation_intCast_le_one (R := k) (j : ℕ)
    simpa using h
  -- the term bound `v(j·wʲ·q^{mj}) ≤ v(qw)ʲ·v(q)^{(m-1)j}`
  have hbound : ∀ p : ℕ+ × ℕ+,
      valuation k (((p.2 : ℕ) : k) * w ^ (p.2 : ℕ) *
        q₀ ^ ((p.1 : ℕ) * (p.2 : ℕ))) ≤
      valuation k (q₀ * w) ^ (p.2 : ℕ) *
        valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) := by
    intro p
    have hm1 : ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ) =
        (p.1 : ℕ) * (p.2 : ℕ) := by
      calc ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ)
          = (((p.1 : ℕ) - 1) + 1) * (p.2 : ℕ) := by ring
        _ = (p.1 : ℕ) * (p.2 : ℕ) := by
            rw [Nat.sub_add_cancel p.1.pos]
    rw [map_mul, map_mul, map_pow, map_pow, ← hm1, pow_add, map_mul]
    calc valuation k (((p.2 : ℕ) : k)) * valuation k w ^ (p.2 : ℕ) *
          (valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) *
            valuation k q₀ ^ (p.2 : ℕ))
        ≤ 1 * valuation k w ^ (p.2 : ℕ) *
          (valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) *
            valuation k q₀ ^ (p.2 : ℕ)) := by
          exact mul_le_mul_left
            (mul_le_mul_left (hj1 p.2) _) _
      _ = (valuation k q₀ * valuation k w) ^ (p.2 : ℕ) *
          valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) := by
          rw [one_mul, mul_pow, mul_comm
            (valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)))
            (valuation k q₀ ^ (p.2 : ℕ)), ← mul_assoc, mul_comm
            (valuation k w ^ (p.2 : ℕ)) (valuation k q₀ ^ (p.2 : ℕ)),
            mul_assoc]
  -- run the criterion with the larger of `q₀`, `q₀w`
  rcases le_total (valuation k q₀) (valuation k (q₀ * w)) with hle | hle
  · refine summable_of_valuation_le_pow (q := q₀ * w) hqw
      (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ)) hfin (fun p ↦ ?_)
    refine le_trans (hbound p) ?_
    have hm1 : ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ) =
        (p.1 : ℕ) * (p.2 : ℕ) := by
      calc ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ)
          = (((p.1 : ℕ) - 1) + 1) * (p.2 : ℕ) := by ring
        _ = (p.1 : ℕ) * (p.2 : ℕ) := by
            rw [Nat.sub_add_cancel p.1.pos]
    calc valuation k (q₀ * w) ^ (p.2 : ℕ) *
          valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ))
        ≤ valuation k (q₀ * w) ^ (p.2 : ℕ) *
          valuation k (q₀ * w) ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) :=
          mul_le_mul_right (pow_le_pow_left' hle _) _
      _ = valuation k (q₀ * w) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
          rw [← pow_add, add_comm, hm1]
  · refine summable_of_valuation_le_pow (q := q₀) hq
      (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ)) hfin (fun p ↦ ?_)
    refine le_trans (hbound p) ?_
    have hm1 : ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ) =
        (p.1 : ℕ) * (p.2 : ℕ) := by
      calc ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ)
          = (((p.1 : ℕ) - 1) + 1) * (p.2 : ℕ) := by ring
        _ = (p.1 : ℕ) * (p.2 : ℕ) := by
            rw [Nat.sub_add_cancel p.1.pos]
    calc valuation k (q₀ * w) ^ (p.2 : ℕ) *
          valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ))
        ≤ valuation k q₀ ^ (p.2 : ℕ) *
          valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) :=
          mul_le_mul_left (pow_le_pow_left' hle _) _
      _ = valuation k q₀ ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
          rw [← pow_add, add_comm, hm1]

omit [CharZero k] in
/-- Per-row sums in the general window: `|q₀ᵐw| ≤ |q₀w| < 1` for
`m ≥ 1`. -/
theorem hasSum_lambert_row' (w q₀ : k) (hq : valuation k q₀ < 1)
    (hqw : valuation k (q₀ * w) < 1) (m : ℕ+) :
    HasSum (fun j : ℕ+ ↦
      ((j : ℕ) : k) * w ^ (j : ℕ) * q₀ ^ ((m : ℕ) * (j : ℕ)))
      (q₀ ^ (m : ℕ) * w / (1 - q₀ ^ (m : ℕ) * w) ^ 2) := by
  set x : k := q₀ ^ (m : ℕ) * w with hxdef
  have hx : valuation k x < 1 := by
    have hm1 : ((m : ℕ) - 1) + 1 = (m : ℕ) := by
      have := m.pos
      omega
    rw [hxdef, ← hm1, pow_add, pow_one, mul_assoc, map_mul, map_pow]
    calc valuation k q₀ ^ ((m : ℕ) - 1) * valuation k (q₀ * w)
        ≤ 1 * valuation k (q₀ * w) :=
          mul_le_mul_left (pow_le_one₀ zero_le hq.le) _
      _ = valuation k (q₀ * w) := one_mul _
      _ < 1 := hqw
  have hN : HasSum (fun j : ℕ ↦ ((j : ℕ) : k) * x ^ j)
      (x / (1 - x) ^ 2) := by
    have h := (summable_nat_mul_geometric_nonarch x hx).hasSum
    rwa [tsum_nat_mul_geometric_nonarch x hx] at h
  have hP : HasSum (fun j : ℕ+ ↦ ((j : ℕ) : k) * x ^ (j : ℕ))
      (x / (1 - x) ^ 2) := by
    rw [← Function.Injective.hasSum_iff
      (f := fun j : ℕ ↦ ((j : ℕ) : k) * x ^ j)
      PNat.coe_injective ?_] at hN
    · exact hN
    · intro n hn
      have hn0 : n = 0 := by
        by_contra h0
        exact hn ⟨⟨n, Nat.pos_of_ne_zero h0⟩, rfl⟩
      simp [hn0]
  refine hP.congr_fun fun j ↦ ?_
  rw [hxdef, mul_pow, ← pow_mul]
  ring

omit [CharZero k] in
/-- **The one-sided Lambert identity in the general window**
`|q₀| < 1`, `|q₀w| < 1`. -/
theorem hasSum_lambert_side' (w q₀ : k) (hq : valuation k q₀ < 1)
    (hqw : valuation k (q₀ * w) < 1) :
    HasSum (fun N : ℕ+ ↦
      (∑ d ∈ (N : ℕ).divisors, (d : k) * w ^ d) * q₀ ^ (N : ℕ))
      (∑' m : ℕ+, q₀ ^ (m : ℕ) * w / (1 - q₀ ^ (m : ℕ) * w) ^ 2) := by
  refine hasSum_divisor_collect_nonarch
    (g := fun d ↦ (d : k) * w ^ d) ?_
  have hT := hasSum_prod_pnat_nonarch
    (summable_lambert_prod' w q₀ hq hqw)
    (fun m ↦ hasSum_lambert_row' w q₀ hq hqw m)
  refine hT.congr_fun fun p ↦ ?_
  ring

omit [CharZero k] in
/-- The `σ₁`-series over `ℕ+` is summable on `|q₀| < 1`. -/
theorem summable_sigma_one_nonarch (q₀ : k) (hq : valuation k q₀ < 1) :
    Summable (fun N : ℕ+ ↦
      (∑ d ∈ (N : ℕ).divisors, (d : k)) * q₀ ^ (N : ℕ)) := by
  refine summable_of_valuation_le_pow hq (fun N ↦ (N : ℕ))
    (fun M ↦ Set.Finite.subset ((Set.finite_Iio M).preimage
      PNat.coe_injective.injOn) fun N hN ↦ hN) (fun N ↦ ?_)
  rw [map_mul, map_pow]
  have h1 : valuation k ((∑ d ∈ (N : ℕ).divisors, (d : k))) ≤ 1 := by
    refine Valuation.map_sum_le _ fun d _ ↦ ?_
    have h := valuation_intCast_le_one (R := k) d
    simpa using h
  calc valuation k ((∑ d ∈ (N : ℕ).divisors, (d : k))) *
        valuation k q₀ ^ (N : ℕ)
      ≤ 1 * valuation k q₀ ^ (N : ℕ) := mul_le_mul_left h1 _
    _ = valuation k q₀ ^ (N : ℕ) := one_mul _

set_option maxHeartbeats 1000000 in
/-- **The bilateral form of the evaluated `x`-series** (Silverman,
ATAEC V.3, the `ℤ`-indexed description): on the fundamental annulus,
`X(u₀,q₀) = u₀/(1-u₀)² + ∑_{m≥1}[q₀ᵐu₀/(1-q₀ᵐu₀)² +
q₀ᵐu₀⁻¹/(1-q₀ᵐu₀⁻¹)²] - 2∑_N σ₁(N)q₀^N` — the `m ≥ 1` and `m ≤ -1`
halves of `∑_{m∈ℤ} q₀ᵐu₀/(1-q₀ᵐu₀)²` (the negative half rewritten by
the involution `v ↦ v⁻¹` fixing `v/(1-v)²`), the manifestly
`u₀ ↦ q₀u₀`-invariant description of `X`. -/
theorem evalA_XA_bilateral (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq1 : valuation k q₀ < 1)
    (hq : valuation k q₀ < valuation k u₀) :
    evalA u₀ q₀ h0 h1 XA =
      u₀ / (1 - u₀) ^ 2 +
      ((∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀ / (1 - q₀ ^ (m : ℕ) * u₀) ^ 2) +
       (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 2) -
       2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ))) := by
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  have hqu : valuation k (q₀ * u₀) < 1 := by
    rw [map_mul]
    calc valuation k q₀ * valuation k u₀
        ≤ valuation k q₀ * 1 := mul_le_mul_right hu _
      _ = valuation k q₀ := mul_one _
      _ < 1 := hq1
  have hquinv : valuation k (q₀ * u₀⁻¹) < 1 := by
    rw [map_mul, map_inv₀]
    calc valuation k q₀ * (valuation k u₀)⁻¹
        < valuation k u₀ * (valuation k u₀)⁻¹ :=
          mul_lt_mul_of_pos_right hq
            (zero_lt_iff.mpr (inv_ne_zero hv0))
      _ = 1 := mul_inv_cancel₀ hv0
  have hSu := hasSum_lambert_side' u₀ q₀ hq1 hqu
  have hSuinv := hasSum_lambert_side' u₀⁻¹ q₀ hq1 hquinv
  have hSσ := (summable_sigma_one_nonarch q₀ hq1).hasSum
  have htail : HasSum (fun N : ℕ+ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff (N : ℕ) XA) *
        q₀ ^ (N : ℕ))
      ((∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀ / (1 - q₀ ^ (m : ℕ) * u₀) ^ 2) +
       (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 2) -
       2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ))) := by
    refine ((hSu.add hSuinv).sub (hSσ.mul_left 2)).congr_fun
      fun N ↦ ?_
    rw [coeffRingEval_coeff_XA u₀ h0 h1 N.pos.ne', Finset.sum_mul,
      Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    ring
  have htailN : HasSum (fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff (n + 1) XA) *
        q₀ ^ (n + 1))
      ((∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀ / (1 - q₀ ^ (m : ℕ) * u₀) ^ 2) +
       (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 2) -
       2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ))) := by
    have h := (Equiv.pnatEquivNat.symm.hasSum_iff).mpr htail
    refine h.congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply,
      Nat.succPNat_coe]
  have hfull := (hasSum_nat_add_iff
    (f := fun n : ℕ ↦ coeffRingEval u₀ h0 h1
      (PowerSeries.coeff n XA) * q₀ ^ n) 1).mp htailN
  rw [Finset.range_one, Finset.sum_singleton] at hfull
  have hf0 : coeffRingEval u₀ h0 h1 (PowerSeries.coeff 0 XA) *
      q₀ ^ 0 = u₀ / (1 - u₀) ^ 2 := by
    rw [coeffRingEval_coeff_XA_zero, pow_zero, mul_one]
  rw [hf0] at hfull
  rw [evalA, hfull.tsum_eq]
  ring

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- Reindexing an `ℕ+`-series by the successor bijection with `ℕ`. -/
theorem tsum_pnat_eq_tsum_succPNat (g : ℕ+ → k) :
    (∑' m : ℕ+, g m) = ∑' n : ℕ, g n.succPNat := by
  rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm g]
  exact tsum_congr fun n ↦ by
    simp only [Equiv.pnatEquivNat_symm_apply]

omit [CharZero k] in
/-- Splitting off the first term of a summable `ℕ+`-series. -/
theorem tsum_pnat_eq_add_shift {f : ℕ+ → k} (hf : Summable f) :
    (∑' m : ℕ+, f m) = f 1 + ∑' m : ℕ+, f (m + 1) := by
  have hsum : Summable (fun n : ℕ ↦ f n.succPNat) := by
    have h := (Equiv.pnatEquivNat.symm.summable_iff).mpr hf
    refine h.congr fun n ↦ ?_
    simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply]
  rw [tsum_pnat_eq_tsum_succPNat f,
    tsum_pnat_eq_tsum_succPNat (fun m ↦ f (m + 1)),
    hsum.tsum_eq_zero_add]
  rfl

/-- **The bilateral `x`-value**: the `ℤ`-indexed description of the
Tate `x`-coordinate, defined for any parameters (junk off the
convergence window `|q₀| < |u₀| < |q₀|⁻¹`). On the fundamental
annulus it agrees with `evalA … XA` (`evalA_XA_bilateral`). -/
noncomputable def bilateralX (u₀ q₀ : k) : k :=
  u₀ / (1 - u₀) ^ 2 +
    ((∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀ / (1 - q₀ ^ (m : ℕ) * u₀) ^ 2) +
     (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
        (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 2) -
     2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
        q₀ ^ (N : ℕ)))

/-- `evalA_XA_bilateral`, restated through `bilateralX`. -/
theorem evalA_XA_eq_bilateralX (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq1 : valuation k q₀ < 1)
    (hq : valuation k q₀ < valuation k u₀) :
    evalA u₀ q₀ h0 h1 XA = bilateralX u₀ q₀ :=
  evalA_XA_bilateral u₀ q₀ h0 h1 hu hq1 hq

/-- **`bilateralX` commutes with a valuative extension of
nonarchimedean local fields**, on the fundamental annulus: transport
`evalA_XA_map` through the bridge `evalA_XA_eq_bilateralX`. -/
theorem bilateralX_map {l : Type*} [Field l] [ValuativeRel l]
    [TopologicalSpace l] [IsNonarchimedeanLocalField l] [CharZero l]
    [Algebra k l] [ValuativeExtension k l]
    (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq1 : valuation k q₀ < 1)
    (hq : valuation k q₀ < valuation k u₀)
    (h0' : algebraMap k l u₀ ≠ 0) (h1' : algebraMap k l u₀ ≠ 1)
    (hu' : valuation l (algebraMap k l u₀) ≤ 1)
    (hq1' : valuation l (algebraMap k l q₀) < 1)
    (hq' : valuation l (algebraMap k l q₀) < valuation l (algebraMap k l u₀)) :
    algebraMap k l (bilateralX u₀ q₀) =
      bilateralX (algebraMap k l u₀) (algebraMap k l q₀) := by
  rw [← evalA_XA_eq_bilateralX u₀ q₀ h0 h1 hu hq1 hq,
    evalA_XA_map u₀ q₀ h0 h1 hu hq h0' h1',
    evalA_XA_eq_bilateralX (algebraMap k l u₀) (algebraMap k l q₀) h0' h1'
      hu' hq1' hq']

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- The Möbius-type involution fixing the Lambert kernel:
`v⁻¹/(1-v⁻¹)² = v/(1-v)²`. -/
theorem lambert_kernel_inv (v : k) (hv : v ≠ 0) :
    v⁻¹ / (1 - v⁻¹) ^ 2 = v / (1 - v) ^ 2 := by
  rcases eq_or_ne v 1 with rfl | hv1
  · simp
  · have h1 : (1 - v) ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have h2 : (1 - v⁻¹) ≠ 0 := by
      intro h0
      have : v⁻¹ = 1 := by linear_combination -h0
      exact hv1 (by
        have := congrArg (v * ·) this
        simpa [mul_inv_cancel₀ hv] using this.symm)
    field_simp
    ring

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- **Involution invariance of the bilateral `x`-value**:
`bilateralX u₀⁻¹ = bilateralX u₀` — the substitution `u₀ ↦ u₀⁻¹`
exchanges the two half-sums termwise (the Lambert kernel is
`v ↦ v⁻¹`-invariant) and fixes the constant term. -/
theorem bilateralX_inv (u₀ q₀ : k) (h0 : u₀ ≠ 0) :
    bilateralX u₀⁻¹ q₀ = bilateralX u₀ q₀ := by
  rw [bilateralX, bilateralX, inv_inv]
  have hconst : u₀⁻¹ / (1 - u₀⁻¹) ^ 2 = u₀ / (1 - u₀) ^ 2 :=
    lambert_kernel_inv u₀ h0
  rw [hconst]
  ring

omit [CharZero k] in
/-- The Lambert-term family is summable in the general window: the
rows of the summable double series sum to it fiberwise. -/
theorem summable_lambert_terms (w q₀ : k) (hq : valuation k q₀ < 1)
    (hqw : valuation k (q₀ * w) < 1) :
    Summable (fun m : ℕ+ ↦
      q₀ ^ (m : ℕ) * w / (1 - q₀ ^ (m : ℕ) * w) ^ 2) :=
  ((summable_lambert_prod' w q₀ hq hqw).hasSum.prod_fiberwise
    (fun m ↦ hasSum_lambert_row' w q₀ hq hqw m)).summable

omit [CharZero k] in
/-- Summability of an `ℕ+`-family follows from summability of its
shift. -/
theorem summable_pnat_of_shift {f : ℕ+ → k}
    (hf : Summable fun m : ℕ+ ↦ f (m + 1)) : Summable f := by
  have hpn : ∀ n : ℕ, (n + 1).succPNat = n.succPNat + 1 := by
    intro n
    apply PNat.coe_injective
    simp [Nat.succPNat]
  have hN : Summable (fun n : ℕ ↦ f (n + 1).succPNat) := by
    have h := (Equiv.pnatEquivNat.symm.summable_iff).mpr hf
    refine h.congr fun n ↦ ?_
    simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply]
    exact congrArg f (hpn n).symm
  have h2 : Summable (fun n : ℕ ↦ f n.succPNat) :=
    (summable_nat_add_iff 1).mp hN
  exact (Equiv.pnatEquivNat.symm.summable_iff).mp
    (h2.congr fun n ↦ by
      simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply])

omit [CharZero k] in
set_option maxHeartbeats 1000000 in
/-- **Shift invariance of the bilateral `x`-value** (the translation
identity, Silverman V.3.1(a)): `bilateralX (q₀u₀) q₀ = bilateralX u₀ q₀`
on the annulus — the constant term of the shifted parameter is the
first term of the `u₀`-half-sum, and the first term of the shifted
inverse half-sum is the `u₀`-constant; everything else reindexes by
one step. -/
theorem bilateralX_shift (u₀ q₀ : k) (h0 : u₀ ≠ 0) (hq0 : q₀ ≠ 0)
    (hq1 : valuation k q₀ < 1) (hqu : valuation k (q₀ * u₀) < 1)
    (hquinv : valuation k (q₀ * u₀⁻¹) < 1) :
    bilateralX (q₀ * u₀) q₀ = bilateralX u₀ q₀ := by
  have hq2u : valuation k (q₀ * (q₀ * u₀)) < 1 := by
    rw [map_mul]
    calc valuation k q₀ * valuation k (q₀ * u₀)
        ≤ 1 * valuation k (q₀ * u₀) :=
          mul_le_mul_left hq1.le _
      _ = valuation k (q₀ * u₀) := one_mul _
      _ < 1 := hqu
  have hS1 := summable_lambert_terms u₀ q₀ hq1 hqu
  have hS2 := summable_lambert_terms (q₀ * u₀) q₀ hq1 hq2u
  have hS3 := summable_lambert_terms u₀⁻¹ q₀ hq1 hquinv
  -- the shifted-inverse family: its shift is the `u₀⁻¹`-family
  have hS4 : Summable (fun m : ℕ+ ↦
      q₀ ^ (m : ℕ) * (q₀ * u₀)⁻¹ /
        (1 - q₀ ^ (m : ℕ) * (q₀ * u₀)⁻¹) ^ 2) := by
    refine summable_pnat_of_shift (hS3.congr fun m ↦ ?_)
    have hterm : q₀ ^ ((m + 1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹ =
        q₀ ^ (m : ℕ) * u₀⁻¹ := by
      rw [mul_inv, PNat.add_coe, PNat.one_coe, pow_succ]
      field_simp
    rw [hterm]
  -- the two shift computations
  have hshift2 : (∑' m : ℕ+, q₀ ^ (m : ℕ) * (q₀ * u₀) /
      (1 - q₀ ^ (m : ℕ) * (q₀ * u₀)) ^ 2) =
      (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀ /
        (1 - q₀ ^ (m : ℕ) * u₀) ^ 2) -
      q₀ * u₀ / (1 - q₀ * u₀) ^ 2 := by
    have h := tsum_pnat_eq_add_shift hS1
    have hcongr : (∑' m : ℕ+, q₀ ^ ((m + 1 : ℕ+) : ℕ) * u₀ /
        (1 - q₀ ^ ((m + 1 : ℕ+) : ℕ) * u₀) ^ 2) =
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * (q₀ * u₀) /
          (1 - q₀ ^ (m : ℕ) * (q₀ * u₀)) ^ 2) := by
      refine tsum_congr fun m ↦ ?_
      rw [show q₀ ^ ((m + 1 : ℕ+) : ℕ) * u₀ =
          q₀ ^ (m : ℕ) * (q₀ * u₀) from by
        rw [PNat.add_coe, PNat.one_coe, pow_succ]
        ring]
    rw [hcongr] at h
    have h1 : q₀ ^ ((1 : ℕ+) : ℕ) * u₀ / (1 - q₀ ^ ((1 : ℕ+) : ℕ) * u₀) ^ 2
        = q₀ * u₀ / (1 - q₀ * u₀) ^ 2 := by
      norm_num
    rw [h1] at h
    linear_combination -h
  have hshift4 : (∑' m : ℕ+, q₀ ^ (m : ℕ) * (q₀ * u₀)⁻¹ /
      (1 - q₀ ^ (m : ℕ) * (q₀ * u₀)⁻¹) ^ 2) =
      u₀⁻¹ / (1 - u₀⁻¹) ^ 2 +
      (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
        (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 2) := by
    have h := tsum_pnat_eq_add_shift hS4
    have h1 : q₀ ^ ((1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹ /
        (1 - q₀ ^ ((1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹) ^ 2
        = u₀⁻¹ / (1 - u₀⁻¹) ^ 2 := by
      rw [show q₀ ^ ((1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹ = u₀⁻¹ from by
        rw [mul_inv, PNat.one_coe, pow_one]
        field_simp]
    have hcongr : (∑' m : ℕ+,
        q₀ ^ ((m + 1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹ /
          (1 - q₀ ^ ((m + 1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹) ^ 2) =
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 2) := by
      refine tsum_congr fun m ↦ ?_
      rw [show q₀ ^ ((m + 1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹ =
          q₀ ^ (m : ℕ) * u₀⁻¹ from by
        rw [mul_inv, PNat.add_coe, PNat.one_coe, pow_succ]
        field_simp]
    rw [h1, hcongr] at h
    exact h
  -- assemble
  rw [bilateralX, bilateralX, hshift2, hshift4,
    lambert_kernel_inv u₀ h0]
  ring

omit [CharZero k] in
/-- `∑ (n+1)xⁿ` is summable on the open unit disc. -/
theorem summable_add_one_mul_geometric_nonarch (x : k)
    (hx : valuation k x < 1) :
    Summable (fun n : ℕ ↦ ((n : k) + 1) * x ^ n) := by
  have h := (summable_nat_mul_geometric_nonarch x hx).add
    (summable_geometric_nonarch x hx)
  refine h.congr fun n ↦ ?_
  ring

omit [CharZero k] in
/-- `∑ (n+1)xⁿ = (1-x)⁻²` on the open unit disc. -/
theorem tsum_add_one_mul_geometric_nonarch (x : k)
    (hx : valuation k x < 1) :
    (∑' n : ℕ, ((n : k) + 1) * x ^ n) = ((1 - x)⁻¹) ^ 2 := by
  have hxne : x ≠ 1 := by
    rintro rfl
    simp at hx
  have h1x : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne)
  have hsplit : (∑' n : ℕ, ((n : k) + 1) * x ^ n) =
      (∑' n : ℕ, (n : k) * x ^ n) + (∑' n : ℕ, x ^ n) := by
    rw [← (summable_nat_mul_geometric_nonarch x hx).tsum_add
      (summable_geometric_nonarch x hx)]
    exact tsum_congr fun n ↦ by ring
  rw [hsplit, tsum_nat_mul_geometric_nonarch x hx,
    tsum_geometric_nonarch x hx]
  field_simp
  ring

omit [CharZero k] in
/-- The Gauss sum in binomial form:
`∑_{i<n+1} (i+1) = C(n+2, 2)`. -/
theorem sum_range_add_one_eq_choose (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i + 1)) = (n + 2).choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ (n + 2) 1,
      Nat.choose_one_right]
    simp only [show Nat.succ 1 = 2 from rfl]
    omega

omit [CharZero k] in
set_option maxHeartbeats 1000000 in
/-- **The nonarchimedean geometric cube**:
`∑ C(n+2,2)xⁿ = (1-x)⁻³` — the Cauchy product of `(1-x)⁻²` and the
geometric series, with the antidiagonal counted by the Gauss sum. -/
theorem tsum_choose_two_geometric_nonarch (x : k)
    (hx : valuation k x < 1) :
    (∑' n : ℕ, (((n + 2).choose 2 : ℕ) : k) * x ^ n) =
      ((1 - x)⁻¹) ^ 3 := by
  have hplus := summable_add_one_mul_geometric_nonarch x hx
  have hgeom := summable_geometric_nonarch x hx
  have hterm : ∀ n : ℕ,
      (∑ kl ∈ Finset.antidiagonal n,
        ((kl.1 : k) + 1) * x ^ kl.1 * x ^ kl.2) =
      (((n + 2).choose 2 : ℕ) : k) * x ^ n := by
    intro n
    have h1 : ∀ kl ∈ Finset.antidiagonal n,
        ((kl.1 : k) + 1) * x ^ kl.1 * x ^ kl.2 =
        ((kl.1 : k) + 1) * x ^ n := by
      intro kl hkl
      rw [mul_assoc, ← pow_add, Finset.mem_antidiagonal.mp hkl]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    congr 1
    have hcast : (∑ i ∈ Finset.range (n + 1), ((i : k) + 1)) =
        ((∑ i ∈ Finset.range (n + 1), (i + 1) : ℕ) : k) := by
      push_cast
      ring
    rw [hcast, sum_range_add_one_eq_choose]
  have hv2 := tsum_add_one_mul_geometric_nonarch x hx
  have hv1 := tsum_geometric_nonarch x hx
  set f : ℕ → k := fun n ↦ ((n : k) + 1) * x ^ n with hfdef
  set g : ℕ → k := fun n ↦ x ^ n with hgdef
  have hkey := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal (A := ℕ)
    hplus hgeom (summable_mul_prod hplus hgeom)
  rw [hv2, hv1] at hkey
  calc (∑' n : ℕ, (((n + 2).choose 2 : ℕ) : k) * x ^ n)
      = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 :=
        tsum_congr fun n ↦ (hterm n).symm
    _ = ((1 - x)⁻¹) ^ 2 * (1 - x)⁻¹ := hkey.symm
    _ = ((1 - x)⁻¹) ^ 3 := by ring

omit [CharZero k] in
/-- The cube series is summable. -/
theorem summable_choose_two_geometric_nonarch (v : k)
    (hv : valuation k v < 1) :
    Summable (fun n : ℕ ↦ (((n + 2).choose 2 : ℕ) : k) * v ^ n) := by
  refine summable_of_valuation_le_pow hv (fun n ↦ n)
    (fun N ↦ Set.finite_Iio N) (fun n ↦ ?_)
  rw [map_mul, map_pow]
  calc valuation k ((((n + 2).choose 2 : ℕ) : k)) * valuation k v ^ n
      ≤ 1 * valuation k v ^ n := by
        refine mul_le_mul_left ?_ _
        have h := valuation_intCast_le_one (R := k) ((n + 2).choose 2)
        simpa using h
    _ = valuation k v ^ n := one_mul _

omit [CharZero k] in
/-- The first `Y`-kernel: `∑ⱼ C(j,2)vʲ = v²/(1-v)³`. -/
theorem tsum_choose_two_self_geometric_nonarch (v : k)
    (hv : valuation k v < 1) :
    (∑' j : ℕ, ((j.choose 2 : ℕ) : k) * v ^ j) =
      v ^ 2 / (1 - v) ^ 3 := by
  have hvne : v ≠ 1 := by
    rintro rfl
    simp at hv
  have h1v : (1 - v) ≠ 0 := sub_ne_zero.mpr (Ne.symm hvne)
  have hcubeHS : HasSum
      (fun n : ℕ ↦ (((n + 2).choose 2 : ℕ) : k) * v ^ n)
      (((1 - v)⁻¹) ^ 3) := by
    have h := (summable_choose_two_geometric_nonarch v hv).hasSum
    rwa [tsum_choose_two_geometric_nonarch v hv] at h
  have hshifted : HasSum (fun n : ℕ ↦
      (((n + 2).choose 2 : ℕ) : k) * v ^ (n + 2))
      (v ^ 2 * ((1 - v)⁻¹) ^ 3) := by
    refine (hcubeHS.mul_left (v ^ 2)).congr_fun fun n ↦ ?_
    rw [pow_add]
    ring
  have hfull := (hasSum_nat_add_iff
    (f := fun j : ℕ ↦ ((j.choose 2 : ℕ) : k) * v ^ j) 2).mp hshifted
  have hzero : (∑ i ∈ Finset.range 2,
      ((i.choose 2 : ℕ) : k) * v ^ i) = 0 := by
    simp [Finset.sum_range_succ]
  rw [hzero, add_zero] at hfull
  rw [hfull.tsum_eq]
  field_simp

omit [CharZero k] in
/-- The second `Y`-kernel: `∑ⱼ C(j+1,2)vʲ = v/(1-v)³`. -/
theorem tsum_choose_two_succ_geometric_nonarch (v : k)
    (hv : valuation k v < 1) :
    (∑' j : ℕ, (((j + 1).choose 2 : ℕ) : k) * v ^ j) =
      v / (1 - v) ^ 3 := by
  have hvne : v ≠ 1 := by
    rintro rfl
    simp at hv
  have h1v : (1 - v) ≠ 0 := sub_ne_zero.mpr (Ne.symm hvne)
  have hcubeHS : HasSum
      (fun n : ℕ ↦ (((n + 2).choose 2 : ℕ) : k) * v ^ n)
      (((1 - v)⁻¹) ^ 3) := by
    have h := (summable_choose_two_geometric_nonarch v hv).hasSum
    rwa [tsum_choose_two_geometric_nonarch v hv] at h
  have hshifted : HasSum (fun n : ℕ ↦
      ((((n + 1) + 1).choose 2 : ℕ) : k) * v ^ (n + 1))
      (v * ((1 - v)⁻¹) ^ 3) := by
    refine (hcubeHS.mul_left v).congr_fun fun n ↦ ?_
    rw [pow_succ]
    ring
  have hfull := (hasSum_nat_add_iff
    (f := fun j : ℕ ↦ (((j + 1).choose 2 : ℕ) : k) * v ^ j) 1).mp
    hshifted
  have hzero : (∑ i ∈ Finset.range 1,
      (((i + 1).choose 2 : ℕ) : k) * v ^ i) = 0 := by
    simp
  rw [hzero, add_zero] at hfull
  rw [hfull.tsum_eq]
  field_simp

omit [CharZero k] in
/-- **The general one-sided Lambert identity**: for coefficients `a`
of valuation at most `1` whose power series sums to `g` on the open
unit disc, `∑_N (∑_{d∣N} a(d)wᵈ)q₀^N = ∑_m g(q₀ᵐw)` in the window
`|q₀| < 1`, `|q₀w| < 1`. Instantiates to the `x`-series
(`a = id`, `g = v/(1-v)²`) and to both `y`-kernels
(`a = C(·,2)`, `g = v²/(1-v)³` and `a = C(·+1,2)`, `g = v/(1-v)³`). -/
theorem hasSum_lambert_general (a : ℕ → k) (g : k → k)
    (ha : ∀ j : ℕ, valuation k (a j) ≤ 1) (w q₀ : k)
    (hq : valuation k q₀ < 1) (hqw : valuation k (q₀ * w) < 1)
    (hg : ∀ v₀ : k, valuation k v₀ < 1 →
      HasSum (fun j : ℕ+ ↦ a (j : ℕ) * v₀ ^ (j : ℕ)) (g v₀)) :
    HasSum (fun N : ℕ+ ↦
      (∑ d ∈ (N : ℕ).divisors, a d * w ^ d) * q₀ ^ (N : ℕ))
      (∑' m : ℕ+, g (q₀ ^ (m : ℕ) * w)) := by
  -- the double series is summable (the general-window two-case bound)
  have hfin : ∀ N : ℕ, {p : ℕ+ × ℕ+ |
      (fun p : ℕ+ × ℕ+ ↦ (p.1 : ℕ) * (p.2 : ℕ)) p < N}.Finite := by
    intro N
    have hinj : Function.Injective
        (fun p : ℕ+ × ℕ+ ↦ ((p.1 : ℕ), (p.2 : ℕ))) := by
      intro x y hxy
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext (PNat.coe_injective hxy.1) (PNat.coe_injective hxy.2)
    refine Set.Finite.subset
      (((Set.finite_Iio N).prod (Set.finite_Iio N)).preimage
        hinj.injOn) ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    exact ⟨lt_of_le_of_lt (Nat.le_mul_of_pos_right _ p.2.pos) hp,
      lt_of_le_of_lt (Nat.le_mul_of_pos_left _ p.1.pos) hp⟩
  have hbound : ∀ p : ℕ+ × ℕ+,
      valuation k (a (p.2 : ℕ) * w ^ (p.2 : ℕ) *
        q₀ ^ ((p.1 : ℕ) * (p.2 : ℕ))) ≤
      valuation k (q₀ * w) ^ (p.2 : ℕ) *
        valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) := by
    intro p
    have hm1 : ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ) =
        (p.1 : ℕ) * (p.2 : ℕ) := by
      calc ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ)
          = (((p.1 : ℕ) - 1) + 1) * (p.2 : ℕ) := by ring
        _ = (p.1 : ℕ) * (p.2 : ℕ) := by
            rw [Nat.sub_add_cancel p.1.pos]
    rw [map_mul, map_mul, map_pow, map_pow, ← hm1, pow_add, map_mul]
    calc valuation k (a (p.2 : ℕ)) * valuation k w ^ (p.2 : ℕ) *
          (valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) *
            valuation k q₀ ^ (p.2 : ℕ))
        ≤ 1 * valuation k w ^ (p.2 : ℕ) *
          (valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) *
            valuation k q₀ ^ (p.2 : ℕ)) := by
          exact mul_le_mul_left
            (mul_le_mul_left (ha (p.2 : ℕ)) _) _
      _ = (valuation k q₀ * valuation k w) ^ (p.2 : ℕ) *
          valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) := by
          rw [one_mul, mul_pow, mul_comm
            (valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)))
            (valuation k q₀ ^ (p.2 : ℕ)), ← mul_assoc, mul_comm
            (valuation k w ^ (p.2 : ℕ)) (valuation k q₀ ^ (p.2 : ℕ)),
            mul_assoc]
  have hsummable : Summable (fun p : ℕ+ × ℕ+ ↦
      a (p.2 : ℕ) * w ^ (p.2 : ℕ) * q₀ ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
    rcases le_total (valuation k q₀) (valuation k (q₀ * w)) with hle | hle
    · refine summable_of_valuation_le_pow (q := q₀ * w) hqw
        (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ)) hfin (fun p ↦ ?_)
      refine le_trans (hbound p) ?_
      have hm1 : ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ) =
          (p.1 : ℕ) * (p.2 : ℕ) := by
        calc ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ)
            = (((p.1 : ℕ) - 1) + 1) * (p.2 : ℕ) := by ring
          _ = (p.1 : ℕ) * (p.2 : ℕ) := by
              rw [Nat.sub_add_cancel p.1.pos]
      calc valuation k (q₀ * w) ^ (p.2 : ℕ) *
            valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ))
          ≤ valuation k (q₀ * w) ^ (p.2 : ℕ) *
            valuation k (q₀ * w) ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) :=
            mul_le_mul_right (pow_le_pow_left' hle _) _
        _ = valuation k (q₀ * w) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
            rw [← pow_add, add_comm, hm1]
    · refine summable_of_valuation_le_pow (q := q₀) hq
        (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ)) hfin (fun p ↦ ?_)
      refine le_trans (hbound p) ?_
      have hm1 : ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ) =
          (p.1 : ℕ) * (p.2 : ℕ) := by
        calc ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ)
            = (((p.1 : ℕ) - 1) + 1) * (p.2 : ℕ) := by ring
          _ = (p.1 : ℕ) * (p.2 : ℕ) := by
              rw [Nat.sub_add_cancel p.1.pos]
      calc valuation k (q₀ * w) ^ (p.2 : ℕ) *
            valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ))
          ≤ valuation k q₀ ^ (p.2 : ℕ) *
            valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) :=
            mul_le_mul_left (pow_le_pow_left' hle _) _
        _ = valuation k q₀ ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
            rw [← pow_add, add_comm, hm1]
  -- rows sum to `g(q₀ᵐw)`
  have hrow : ∀ m : ℕ+, HasSum (fun j : ℕ+ ↦
      a (j : ℕ) * w ^ (j : ℕ) * q₀ ^ ((m : ℕ) * (j : ℕ)))
      (g (q₀ ^ (m : ℕ) * w)) := by
    intro m
    have hx : valuation k (q₀ ^ (m : ℕ) * w) < 1 := by
      have hm1 : ((m : ℕ) - 1) + 1 = (m : ℕ) := by
        have := m.pos
        omega
      rw [← hm1, pow_add, pow_one, mul_assoc, map_mul, map_pow]
      calc valuation k q₀ ^ ((m : ℕ) - 1) * valuation k (q₀ * w)
          ≤ 1 * valuation k (q₀ * w) :=
            mul_le_mul_left (pow_le_one₀ zero_le hq.le) _
        _ = valuation k (q₀ * w) := one_mul _
        _ < 1 := hqw
    refine (hg _ hx).congr_fun fun j ↦ ?_
    rw [mul_pow, ← pow_mul]
    ring
  -- assemble
  refine hasSum_divisor_collect_nonarch (g := fun d ↦ a d * w ^ d) ?_
  have hT := hasSum_prod_pnat_nonarch hsummable hrow
  refine hT.congr_fun fun p ↦ ?_
  ring

omit [CharZero k] in
/-- The first `Y`-kernel as an `ℕ+`-`HasSum` (the `j = 0` term
vanishes: `C(0,2) = 0`). -/
theorem hasSum_pnat_choose_two_self (v : k)
    (hv : valuation k v < 1) :
    HasSum (fun j : ℕ+ ↦ (((j : ℕ).choose 2 : ℕ) : k) * v ^ (j : ℕ))
      (v ^ 2 / (1 - v) ^ 3) := by
  have hsummable : Summable
      (fun j : ℕ ↦ ((j.choose 2 : ℕ) : k) * v ^ j) := by
    refine summable_of_valuation_le_pow hv (fun n ↦ n)
      (fun N ↦ Set.finite_Iio N) (fun n ↦ ?_)
    rw [map_mul, map_pow]
    calc valuation k (((n.choose 2 : ℕ) : k)) * valuation k v ^ n
        ≤ 1 * valuation k v ^ n := by
          refine mul_le_mul_left ?_ _
          have h := valuation_intCast_le_one (R := k) (n.choose 2)
          simpa using h
      _ = valuation k v ^ n := one_mul _
  have hN : HasSum (fun j : ℕ ↦ ((j.choose 2 : ℕ) : k) * v ^ j)
      (v ^ 2 / (1 - v) ^ 3) := by
    have h := hsummable.hasSum
    rwa [tsum_choose_two_self_geometric_nonarch v hv] at h
  rw [← Function.Injective.hasSum_iff
    (f := fun j : ℕ ↦ ((j.choose 2 : ℕ) : k) * v ^ j)
    PNat.coe_injective ?_] at hN
  · exact hN
  · intro n hn
    have hn0 : n = 0 := by
      by_contra h0
      exact hn ⟨⟨n, Nat.pos_of_ne_zero h0⟩, rfl⟩
    simp [hn0]

omit [CharZero k] in
/-- The second `Y`-kernel as an `ℕ+`-`HasSum` (the `j = 0` term
vanishes: `C(1,2) = 0`). -/
theorem hasSum_pnat_choose_two_succ (v : k)
    (hv : valuation k v < 1) :
    HasSum (fun j : ℕ+ ↦
      ((((j : ℕ) + 1).choose 2 : ℕ) : k) * v ^ (j : ℕ))
      (v / (1 - v) ^ 3) := by
  have hsummable : Summable
      (fun j : ℕ ↦ (((j + 1).choose 2 : ℕ) : k) * v ^ j) := by
    refine summable_of_valuation_le_pow hv (fun n ↦ n)
      (fun N ↦ Set.finite_Iio N) (fun n ↦ ?_)
    rw [map_mul, map_pow]
    calc valuation k ((((n + 1).choose 2 : ℕ) : k)) *
          valuation k v ^ n
        ≤ 1 * valuation k v ^ n := by
          refine mul_le_mul_left ?_ _
          have h := valuation_intCast_le_one (R := k) ((n + 1).choose 2)
          simpa using h
      _ = valuation k v ^ n := one_mul _
  have hN : HasSum (fun j : ℕ ↦ (((j + 1).choose 2 : ℕ) : k) * v ^ j)
      (v / (1 - v) ^ 3) := by
    have h := hsummable.hasSum
    rwa [tsum_choose_two_succ_geometric_nonarch v hv] at h
  rw [← Function.Injective.hasSum_iff
    (f := fun j : ℕ ↦ (((j + 1).choose 2 : ℕ) : k) * v ^ j)
    PNat.coe_injective ?_] at hN
  · exact hN
  · intro n hn
    have hn0 : n = 0 := by
      by_contra h0
      exact hn ⟨⟨n, Nat.pos_of_ne_zero h0⟩, rfl⟩
    simp [hn0]

set_option maxHeartbeats 1000000 in
/-- **The bilateral form of the evaluated `y`-series** (Silverman
ATAEC V.3, `ℤ`-indexed): on the fundamental annulus,
`Y(u₀,q₀) = u₀²/(1-u₀)³ + ∑_{m≥1}(q₀ᵐu₀)²/(1-q₀ᵐu₀)³ -
∑_{m≥1}(q₀ᵐu₀⁻¹)/(1-q₀ᵐu₀⁻¹)³ + ∑σ₁(N)q₀^N`. -/
theorem evalA_YA_bilateral (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq1 : valuation k q₀ < 1)
    (hq : valuation k q₀ < valuation k u₀) :
    evalA u₀ q₀ h0 h1 YA =
      u₀ ^ 2 / (1 - u₀) ^ 3 +
      ((∑' m : ℕ+, (q₀ ^ (m : ℕ) * u₀) ^ 2 /
          (1 - q₀ ^ (m : ℕ) * u₀) ^ 3) -
       (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 3) +
       (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ))) := by
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  have hqu : valuation k (q₀ * u₀) < 1 := by
    rw [map_mul]
    calc valuation k q₀ * valuation k u₀
        ≤ valuation k q₀ * 1 := mul_le_mul_right hu _
      _ = valuation k q₀ := mul_one _
      _ < 1 := hq1
  have hquinv : valuation k (q₀ * u₀⁻¹) < 1 := by
    rw [map_mul, map_inv₀]
    calc valuation k q₀ * (valuation k u₀)⁻¹
        < valuation k u₀ * (valuation k u₀)⁻¹ :=
          mul_lt_mul_of_pos_right hq
            (zero_lt_iff.mpr (inv_ne_zero hv0))
      _ = 1 := mul_inv_cancel₀ hv0
  have hbin1 : ∀ j : ℕ, valuation k (((j.choose 2 : ℕ) : k)) ≤ 1 := by
    intro j
    have h := valuation_intCast_le_one (R := k) (j.choose 2)
    simpa using h
  have hbin2 : ∀ j : ℕ,
      valuation k ((((j + 1).choose 2 : ℕ) : k)) ≤ 1 := by
    intro j
    have h := valuation_intCast_le_one (R := k) ((j + 1).choose 2)
    simpa using h
  have hS1 := hasSum_lambert_general
    (fun j ↦ ((j.choose 2 : ℕ) : k)) (fun v ↦ v ^ 2 / (1 - v) ^ 3)
    hbin1 u₀ q₀ hq1 hqu
    (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_self v₀ hv₀)
  have hS2 := hasSum_lambert_general
    (fun j ↦ (((j + 1).choose 2 : ℕ) : k)) (fun v ↦ v / (1 - v) ^ 3)
    hbin2 u₀⁻¹ q₀ hq1 hquinv
    (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_succ v₀ hv₀)
  have hSσ := (summable_sigma_one_nonarch q₀ hq1).hasSum
  have htail : HasSum (fun N : ℕ+ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff (N : ℕ) YA) *
        q₀ ^ (N : ℕ))
      ((∑' m : ℕ+, (q₀ ^ (m : ℕ) * u₀) ^ 2 /
          (1 - q₀ ^ (m : ℕ) * u₀) ^ 3) -
       (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 3) +
       (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ))) := by
    refine ((hS1.sub hS2).add hSσ).congr_fun fun N ↦ ?_
    rw [coeffRingEval_coeff_YA u₀ h0 h1 N.pos.ne', Finset.sum_mul,
      Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    ring
  have htailN : HasSum (fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff (n + 1) YA) *
        q₀ ^ (n + 1))
      ((∑' m : ℕ+, (q₀ ^ (m : ℕ) * u₀) ^ 2 /
          (1 - q₀ ^ (m : ℕ) * u₀) ^ 3) -
       (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 3) +
       (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ))) := by
    have h := (Equiv.pnatEquivNat.symm.hasSum_iff).mpr htail
    refine h.congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply,
      Nat.succPNat_coe]
  have hfull := (hasSum_nat_add_iff
    (f := fun n : ℕ ↦ coeffRingEval u₀ h0 h1
      (PowerSeries.coeff n YA) * q₀ ^ n) 1).mp htailN
  rw [Finset.range_one, Finset.sum_singleton] at hfull
  have hf0 : coeffRingEval u₀ h0 h1 (PowerSeries.coeff 0 YA) *
      q₀ ^ 0 = u₀ ^ 2 / (1 - u₀) ^ 3 := by
    rw [coeffRingEval_coeff_YA_zero, pow_zero, mul_one]
  rw [hf0] at hfull
  rw [evalA, hfull.tsum_eq]
  ring

/-- **The bilateral `y`-value** (junk off the wide window). -/
noncomputable def bilateralY (u₀ q₀ : k) : k :=
  u₀ ^ 2 / (1 - u₀) ^ 3 +
    ((∑' m : ℕ+, (q₀ ^ (m : ℕ) * u₀) ^ 2 /
        (1 - q₀ ^ (m : ℕ) * u₀) ^ 3) -
     (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
        (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 3) +
     (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
        q₀ ^ (N : ℕ)))

/-- `evalA_YA_bilateral`, restated through `bilateralY`. -/
theorem evalA_YA_eq_bilateralY (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq1 : valuation k q₀ < 1)
    (hq : valuation k q₀ < valuation k u₀) :
    evalA u₀ q₀ h0 h1 YA = bilateralY u₀ q₀ :=
  evalA_YA_bilateral u₀ q₀ h0 h1 hu hq1 hq

/-- **`bilateralY` commutes with a valuative extension**, mirroring
`bilateralX_map`. -/
theorem bilateralY_map {l : Type*} [Field l] [ValuativeRel l]
    [TopologicalSpace l] [IsNonarchimedeanLocalField l] [CharZero l]
    [Algebra k l] [ValuativeExtension k l]
    (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : valuation k u₀ ≤ 1) (hq1 : valuation k q₀ < 1)
    (hq : valuation k q₀ < valuation k u₀)
    (h0' : algebraMap k l u₀ ≠ 0) (h1' : algebraMap k l u₀ ≠ 1)
    (hu' : valuation l (algebraMap k l u₀) ≤ 1)
    (hq1' : valuation l (algebraMap k l q₀) < 1)
    (hq' : valuation l (algebraMap k l q₀) < valuation l (algebraMap k l u₀)) :
    algebraMap k l (bilateralY u₀ q₀) =
      bilateralY (algebraMap k l u₀) (algebraMap k l q₀) := by
  rw [← evalA_YA_eq_bilateralY u₀ q₀ h0 h1 hu hq1 hq,
    evalA_YA_map u₀ q₀ h0 h1 hu hq h0' h1',
    evalA_YA_eq_bilateralY (algebraMap k l u₀) (algebraMap k l q₀) h0' h1'
      hu' hq1' hq']

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- The second `Y`-kernel under inversion:
`v⁻¹/(1-v⁻¹)³ = -(v²/(1-v)³)`. -/
theorem y_kernel_succ_inv (v : k) (hv : v ≠ 0) (hv1 : v ≠ 1) :
    v⁻¹ / (1 - v⁻¹) ^ 3 = -(v ^ 2 / (1 - v) ^ 3) := by
  have h1 : (1 - v) ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have h2 : (1 - v⁻¹) ≠ 0 := by
    intro h0
    have hinv : v⁻¹ = 1 := by linear_combination -h0
    exact hv1 (by
      have := congrArg (v * ·) hinv
      simpa [mul_inv_cancel₀ hv] using this.symm)
  field_simp
  ring

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- The mixed constant identity behind `Y(u⁻¹) = -Y(u) - X(u)`:
`(u⁻¹)²/(1-u⁻¹)³ = -(u²/(1-u)³) - u/(1-u)²`. -/
theorem y_constant_inv (u : k) (hu : u ≠ 0) (hu1 : u ≠ 1) :
    (u⁻¹) ^ 2 / (1 - u⁻¹) ^ 3 = -(u ^ 2 / (1 - u) ^ 3) - u / (1 - u) ^ 2 := by
  have h1 : (1 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have h2 : (1 - u⁻¹) ≠ 0 := by
    intro h0
    have hinv : u⁻¹ = 1 := by linear_combination -h0
    exact hu1 (by
      have := congrArg (u * ·) hinv
      simpa [mul_inv_cancel₀ hu] using this.symm)
  field_simp
  ring

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- The pointwise relation between the three kernels:
`w²/(1-w)³ = w/(1-w)³ - w/(1-w)²`. -/
theorem y_kernel_relation (w : k) (h1w : (1 : k) - w ≠ 0) :
    w ^ 2 / (1 - w) ^ 3 = w / (1 - w) ^ 3 - w / (1 - w) ^ 2 := by
  field_simp
  ring

omit [CharZero k] in
/-- Term-family summability for the general Lambert data. -/
theorem summable_lambert_terms_general (a : ℕ → k) (g : k → k)
    (ha : ∀ j : ℕ, valuation k (a j) ≤ 1) (w q₀ : k)
    (hq : valuation k q₀ < 1) (hqw : valuation k (q₀ * w) < 1)
    (hg : ∀ v₀ : k, valuation k v₀ < 1 →
      HasSum (fun j : ℕ+ ↦ a (j : ℕ) * v₀ ^ (j : ℕ)) (g v₀)) :
    Summable (fun m : ℕ+ ↦ g (q₀ ^ (m : ℕ) * w)) := by
  -- the double series is summable (the general-window two-case bound)
  have hfin : ∀ N : ℕ, {p : ℕ+ × ℕ+ |
      (fun p : ℕ+ × ℕ+ ↦ (p.1 : ℕ) * (p.2 : ℕ)) p < N}.Finite := by
    intro N
    have hinj : Function.Injective
        (fun p : ℕ+ × ℕ+ ↦ ((p.1 : ℕ), (p.2 : ℕ))) := by
      intro x y hxy
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext (PNat.coe_injective hxy.1) (PNat.coe_injective hxy.2)
    refine Set.Finite.subset
      (((Set.finite_Iio N).prod (Set.finite_Iio N)).preimage
        hinj.injOn) ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    exact ⟨lt_of_le_of_lt (Nat.le_mul_of_pos_right _ p.2.pos) hp,
      lt_of_le_of_lt (Nat.le_mul_of_pos_left _ p.1.pos) hp⟩
  have hbound : ∀ p : ℕ+ × ℕ+,
      valuation k (a (p.2 : ℕ) * w ^ (p.2 : ℕ) *
        q₀ ^ ((p.1 : ℕ) * (p.2 : ℕ))) ≤
      valuation k (q₀ * w) ^ (p.2 : ℕ) *
        valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) := by
    intro p
    have hm1 : ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ) =
        (p.1 : ℕ) * (p.2 : ℕ) := by
      calc ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ)
          = (((p.1 : ℕ) - 1) + 1) * (p.2 : ℕ) := by ring
        _ = (p.1 : ℕ) * (p.2 : ℕ) := by
            rw [Nat.sub_add_cancel p.1.pos]
    rw [map_mul, map_mul, map_pow, map_pow, ← hm1, pow_add, map_mul]
    calc valuation k (a (p.2 : ℕ)) * valuation k w ^ (p.2 : ℕ) *
          (valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) *
            valuation k q₀ ^ (p.2 : ℕ))
        ≤ 1 * valuation k w ^ (p.2 : ℕ) *
          (valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) *
            valuation k q₀ ^ (p.2 : ℕ)) := by
          exact mul_le_mul_left
            (mul_le_mul_left (ha (p.2 : ℕ)) _) _
      _ = (valuation k q₀ * valuation k w) ^ (p.2 : ℕ) *
          valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) := by
          rw [one_mul, mul_pow, mul_comm
            (valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)))
            (valuation k q₀ ^ (p.2 : ℕ)), ← mul_assoc, mul_comm
            (valuation k w ^ (p.2 : ℕ)) (valuation k q₀ ^ (p.2 : ℕ)),
            mul_assoc]
  have hsummable : Summable (fun p : ℕ+ × ℕ+ ↦
      a (p.2 : ℕ) * w ^ (p.2 : ℕ) * q₀ ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
    rcases le_total (valuation k q₀) (valuation k (q₀ * w)) with hle | hle
    · refine summable_of_valuation_le_pow (q := q₀ * w) hqw
        (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ)) hfin (fun p ↦ ?_)
      refine le_trans (hbound p) ?_
      have hm1 : ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ) =
          (p.1 : ℕ) * (p.2 : ℕ) := by
        calc ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ)
            = (((p.1 : ℕ) - 1) + 1) * (p.2 : ℕ) := by ring
          _ = (p.1 : ℕ) * (p.2 : ℕ) := by
              rw [Nat.sub_add_cancel p.1.pos]
      calc valuation k (q₀ * w) ^ (p.2 : ℕ) *
            valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ))
          ≤ valuation k (q₀ * w) ^ (p.2 : ℕ) *
            valuation k (q₀ * w) ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) :=
            mul_le_mul_right (pow_le_pow_left' hle _) _
        _ = valuation k (q₀ * w) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
            rw [← pow_add, add_comm, hm1]
    · refine summable_of_valuation_le_pow (q := q₀) hq
        (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ)) hfin (fun p ↦ ?_)
      refine le_trans (hbound p) ?_
      have hm1 : ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ) =
          (p.1 : ℕ) * (p.2 : ℕ) := by
        calc ((p.1 : ℕ) - 1) * (p.2 : ℕ) + (p.2 : ℕ)
            = (((p.1 : ℕ) - 1) + 1) * (p.2 : ℕ) := by ring
          _ = (p.1 : ℕ) * (p.2 : ℕ) := by
              rw [Nat.sub_add_cancel p.1.pos]
      calc valuation k (q₀ * w) ^ (p.2 : ℕ) *
            valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ))
          ≤ valuation k q₀ ^ (p.2 : ℕ) *
            valuation k q₀ ^ (((p.1 : ℕ) - 1) * (p.2 : ℕ)) :=
            mul_le_mul_left (pow_le_pow_left' hle _) _
        _ = valuation k q₀ ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
            rw [← pow_add, add_comm, hm1]
  -- rows sum to `g(q₀ᵐw)`
  have hrow : ∀ m : ℕ+, HasSum (fun j : ℕ+ ↦
      a (j : ℕ) * w ^ (j : ℕ) * q₀ ^ ((m : ℕ) * (j : ℕ)))
      (g (q₀ ^ (m : ℕ) * w)) := by
    intro m
    have hx : valuation k (q₀ ^ (m : ℕ) * w) < 1 := by
      have hm1 : ((m : ℕ) - 1) + 1 = (m : ℕ) := by
        have := m.pos
        omega
      rw [← hm1, pow_add, pow_one, mul_assoc, map_mul, map_pow]
      calc valuation k q₀ ^ ((m : ℕ) - 1) * valuation k (q₀ * w)
          ≤ 1 * valuation k (q₀ * w) :=
            mul_le_mul_left (pow_le_one₀ zero_le hq.le) _
        _ = valuation k (q₀ * w) := one_mul _
        _ < 1 := hqw
    refine (hg _ hx).congr_fun fun j ↦ ?_
    rw [mul_pow, ← pow_mul]
    ring
  exact (hsummable.hasSum.prod_fiberwise hrow).summable

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- Terms of the Lambert sums are away from the pole:
`1 - q₀ᵐw ≠ 0` when `|q₀w| < 1`. -/
theorem one_sub_pow_mul_ne_zero (w q₀ : k)
    (hq : valuation k q₀ < 1) (hqw : valuation k (q₀ * w) < 1)
    (m : ℕ+) : (1 : k) - q₀ ^ (m : ℕ) * w ≠ 0 := by
  intro h0
  have hval : valuation k (q₀ ^ (m : ℕ) * w) < 1 := by
    have hm1 : ((m : ℕ) - 1) + 1 = (m : ℕ) := by
      have := m.pos
      omega
    rw [← hm1, pow_add, pow_one, mul_assoc, map_mul, map_pow]
    calc valuation k q₀ ^ ((m : ℕ) - 1) * valuation k (q₀ * w)
        ≤ 1 * valuation k (q₀ * w) :=
          mul_le_mul_left (pow_le_one₀ zero_le hq.le) _
      _ = valuation k (q₀ * w) := one_mul _
      _ < 1 := hqw
  have heq : q₀ ^ (m : ℕ) * w = 1 := by linear_combination -h0
  rw [heq] at hval
  simp at hval

omit [CharZero k] in
set_option maxHeartbeats 1000000 in
/-- **Inversion antisymmetry of the bilateral `y`-value**:
`bilateralY u₀⁻¹ = -(bilateralY u₀) - bilateralX u₀` in the wide
window — the negation law of the Tate parametrisation at the level of
the `ℤ`-indexed sums, via the pointwise kernel relation
`kernel₁ = kernel₂ - kernelX` applied on both parameter arguments,
and the mixed constant identity. -/
theorem bilateralY_inv (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hq1 : valuation k q₀ < 1) (hqu : valuation k (q₀ * u₀) < 1)
    (hquinv : valuation k (q₀ * u₀⁻¹) < 1) :
    bilateralY u₀⁻¹ q₀ = -(bilateralY u₀ q₀) - bilateralX u₀ q₀ := by
  have hbin1 : ∀ j : ℕ, valuation k (((j.choose 2 : ℕ) : k)) ≤ 1 := by
    intro j
    have h := valuation_intCast_le_one (R := k) (j.choose 2)
    simpa using h
  have hbin2 : ∀ j : ℕ,
      valuation k ((((j + 1).choose 2 : ℕ) : k)) ≤ 1 := by
    intro j
    have h := valuation_intCast_le_one (R := k) ((j + 1).choose 2)
    simpa using h
  -- summabilities of the four kernel families
  have hS2inv := summable_lambert_terms_general
    (fun j ↦ (((j + 1).choose 2 : ℕ) : k)) (fun v ↦ v / (1 - v) ^ 3)
    hbin2 u₀⁻¹ q₀ hq1 hquinv
    (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_succ v₀ hv₀)
  have hSXinv := summable_lambert_terms u₀⁻¹ q₀ hq1 hquinv
  have hS1u := summable_lambert_terms_general
    (fun j ↦ ((j.choose 2 : ℕ) : k)) (fun v ↦ v ^ 2 / (1 - v) ^ 3)
    hbin1 u₀ q₀ hq1 hqu
    (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_self v₀ hv₀)
  have hSXu := summable_lambert_terms u₀ q₀ hq1 hqu
  -- split the two `kernel₁`/`kernel₂` sums by the kernel relation
  have hsplit1 : (∑' m : ℕ+, (q₀ ^ (m : ℕ) * u₀⁻¹) ^ 2 /
      (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 3) =
      (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
        (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 3) -
      (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
        (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 2) := by
    rw [← hS2inv.tsum_sub hSXinv]
    exact tsum_congr fun m ↦
      y_kernel_relation _ (one_sub_pow_mul_ne_zero u₀⁻¹ q₀ hq1 hquinv m)
  have hsplit2 : (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀ /
      (1 - q₀ ^ (m : ℕ) * u₀) ^ 3) =
      (∑' m : ℕ+, (q₀ ^ (m : ℕ) * u₀) ^ 2 /
        (1 - q₀ ^ (m : ℕ) * u₀) ^ 3) +
      (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀ /
        (1 - q₀ ^ (m : ℕ) * u₀) ^ 2) := by
    rw [← hS1u.tsum_add hSXu]
    refine tsum_congr fun m ↦ ?_
    have h := y_kernel_relation (q₀ ^ (m : ℕ) * u₀)
      (one_sub_pow_mul_ne_zero u₀ q₀ hq1 hqu m)
    linear_combination -h
  rw [bilateralY, bilateralY, bilateralX, inv_inv, hsplit1, hsplit2,
    y_constant_inv u₀ h0 h1]
  ring

omit [CharZero k] in
set_option maxHeartbeats 1000000 in
/-- **Shift invariance of the bilateral `y`-value** (translation
identity for `Y`): `bilateralY (q₀u₀) q₀ = bilateralY u₀ q₀` in the
wide window — the shifted constant is the first `kernel₁`-term, and
the first term of the shifted inverse half-sum is
`kernel₂(u₀⁻¹) = -const₁(u₀)`, restoring the constant. -/
theorem bilateralY_shift (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hq0 : q₀ ≠ 0) (hq1 : valuation k q₀ < 1)
    (hqu : valuation k (q₀ * u₀) < 1)
    (hquinv : valuation k (q₀ * u₀⁻¹) < 1) :
    bilateralY (q₀ * u₀) q₀ = bilateralY u₀ q₀ := by
  have hbin1 : ∀ j : ℕ, valuation k (((j.choose 2 : ℕ) : k)) ≤ 1 := by
    intro j
    have h := valuation_intCast_le_one (R := k) (j.choose 2)
    simpa using h
  have hbin2 : ∀ j : ℕ,
      valuation k ((((j + 1).choose 2 : ℕ) : k)) ≤ 1 := by
    intro j
    have h := valuation_intCast_le_one (R := k) ((j + 1).choose 2)
    simpa using h
  have hS1u := summable_lambert_terms_general
    (fun j ↦ ((j.choose 2 : ℕ) : k)) (fun v ↦ v ^ 2 / (1 - v) ^ 3)
    hbin1 u₀ q₀ hq1 hqu
    (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_self v₀ hv₀)
  have hS2inv := summable_lambert_terms_general
    (fun j ↦ (((j + 1).choose 2 : ℕ) : k)) (fun v ↦ v / (1 - v) ^ 3)
    hbin2 u₀⁻¹ q₀ hq1 hquinv
    (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_succ v₀ hv₀)
  -- the shifted inverse family: its shift is the `u₀⁻¹`-family
  have hS2' : Summable (fun m : ℕ+ ↦
      q₀ ^ (m : ℕ) * (q₀ * u₀)⁻¹ /
        (1 - q₀ ^ (m : ℕ) * (q₀ * u₀)⁻¹) ^ 3) := by
    refine summable_pnat_of_shift (hS2inv.congr fun m ↦ ?_)
    have hterm : q₀ ^ ((m + 1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹ =
        q₀ ^ (m : ℕ) * u₀⁻¹ := by
      rw [mul_inv, PNat.add_coe, PNat.one_coe, pow_succ]
      field_simp
    rw [hterm]
  -- shift computation for the `kernel₁`-half
  have hshift1 : (∑' m : ℕ+, (q₀ ^ (m : ℕ) * (q₀ * u₀)) ^ 2 /
      (1 - q₀ ^ (m : ℕ) * (q₀ * u₀)) ^ 3) =
      (∑' m : ℕ+, (q₀ ^ (m : ℕ) * u₀) ^ 2 /
        (1 - q₀ ^ (m : ℕ) * u₀) ^ 3) -
      (q₀ * u₀) ^ 2 / (1 - q₀ * u₀) ^ 3 := by
    have h := tsum_pnat_eq_add_shift hS1u
    have hcongr : (∑' m : ℕ+, (q₀ ^ ((m + 1 : ℕ+) : ℕ) * u₀) ^ 2 /
        (1 - q₀ ^ ((m + 1 : ℕ+) : ℕ) * u₀) ^ 3) =
        (∑' m : ℕ+, (q₀ ^ (m : ℕ) * (q₀ * u₀)) ^ 2 /
          (1 - q₀ ^ (m : ℕ) * (q₀ * u₀)) ^ 3) := by
      refine tsum_congr fun m ↦ ?_
      rw [show q₀ ^ ((m + 1 : ℕ+) : ℕ) * u₀ =
          q₀ ^ (m : ℕ) * (q₀ * u₀) from by
        rw [PNat.add_coe, PNat.one_coe, pow_succ]
        ring]
    rw [hcongr] at h
    have h1 : (q₀ ^ ((1 : ℕ+) : ℕ) * u₀) ^ 2 /
        (1 - q₀ ^ ((1 : ℕ+) : ℕ) * u₀) ^ 3 =
        (q₀ * u₀) ^ 2 / (1 - q₀ * u₀) ^ 3 := by
      norm_num
    rw [h1] at h
    linear_combination -h
  -- shift computation for the `kernel₂`-half
  have hshift2 : (∑' m : ℕ+, q₀ ^ (m : ℕ) * (q₀ * u₀)⁻¹ /
      (1 - q₀ ^ (m : ℕ) * (q₀ * u₀)⁻¹) ^ 3) =
      u₀⁻¹ / (1 - u₀⁻¹) ^ 3 +
      (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
        (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 3) := by
    have h := tsum_pnat_eq_add_shift hS2'
    have h1 : q₀ ^ ((1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹ /
        (1 - q₀ ^ ((1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹) ^ 3 =
        u₀⁻¹ / (1 - u₀⁻¹) ^ 3 := by
      rw [show q₀ ^ ((1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹ = u₀⁻¹ from by
        rw [mul_inv, PNat.one_coe, pow_one]
        field_simp]
    have hcongr : (∑' m : ℕ+,
        q₀ ^ ((m + 1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹ /
          (1 - q₀ ^ ((m + 1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹) ^ 3) =
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 3) := by
      refine tsum_congr fun m ↦ ?_
      rw [show q₀ ^ ((m + 1 : ℕ+) : ℕ) * (q₀ * u₀)⁻¹ =
          q₀ ^ (m : ℕ) * u₀⁻¹ from by
        rw [mul_inv, PNat.add_coe, PNat.one_coe, pow_succ]
        field_simp]
    rw [h1, hcongr] at h
    exact h
  -- the exchanged constant: `kernel₂(u₀⁻¹) = -const₁(u₀)`
  have hexch : u₀⁻¹ / (1 - u₀⁻¹) ^ 3 = -(u₀ ^ 2 / (1 - u₀) ^ 3) :=
    y_kernel_succ_inv u₀ h0 h1
  rw [bilateralY, bilateralY, hshift1, hshift2, hexch]
  ring

/-! ### The point map through bilateral coordinates

The addition law is proven against the affine chord–tangent group law, whose
inputs are the *coordinates* of the points being added. The bilateral values
`bilateralX`/`bilateralY` are the right coordinate functions for this: they are
`q₀`-shift-invariant (`bilateralX_shift`, `bilateralY_shift`), so they compute
the coordinates of `pointMap w` for any parameter `w` in the extended window
`|q₀|² < |w| ≤ 1` — the window containing all products of two annulus
parameters — without normalising `w` into the annulus first. The two lemmas
below record this: `nonsingular_bilateral` (the bilateral values are a
nonsingular point) and `pointMap_eq_bilateral` (they are THE coordinates of
`pointMap w`). -/

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- Two affine points with equal coordinates are equal (the nonsingularity
proofs are propositionally irrelevant). -/
theorem point_some_congr {W : WeierstrassCurve.Affine k} {x x' y y' : k}
    {h : W.Nonsingular x y} {h' : W.Nonsingular x' y'}
    (hx : x = x') (hy : y = y') :
    (WeierstrassCurve.Affine.Point.some x y h : W.Point) =
      WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx
  subst hy
  rfl

/-- **The bilateral values are a nonsingular point on the extended window**
`|q₀|² < |w| ≤ 1`, `w ∉ {1, q₀}`: for `w` in the fundamental annulus this is
`nonsingular_evalA` through `evalA_XA_eq_bilateralX`; for `|w| ≤ |q₀|` one
`q₀`-shift moves `w` into the annulus and the bilateral values do not move. -/
theorem nonsingular_bilateral (w q₀ : k) (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hwq : w ≠ q₀) (hq0 : q₀ ≠ 0) (hq1 : valuation k q₀ < 1)
    (hlow : valuation k q₀ * valuation k q₀ < valuation k w)
    (hhigh : valuation k w ≤ 1) :
    (WeierstrassCurve.tateCurve q₀).toAffine.Nonsingular
      (bilateralX w q₀) (bilateralY w q₀) := by
  have hqv : valuation k q₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  rcases lt_or_ge (valuation k q₀) (valuation k w) with hgt | hle
  · -- `w` is already in the fundamental annulus
    have := nonsingular_evalA w q₀ hw0 hw1 hq0 hhigh hq1 hgt
    rwa [evalA_XA_eq_bilateralX w q₀ hw0 hw1 hhigh hq1 hgt,
      evalA_YA_eq_bilateralY w q₀ hw0 hw1 hhigh hq1 hgt] at this
  · -- one shift: `w' := w * q₀⁻¹` is in the annulus and `q₀ * w' = w`
    set w' : k := w * q₀⁻¹ with hw'def
    have hw'0 : w' ≠ 0 := mul_ne_zero hw0 (inv_ne_zero hq0)
    have hw'1 : w' ≠ 1 := by
      intro h
      apply hwq
      have h2 : w * q₀⁻¹ * q₀ = 1 * q₀ := by rw [← hw'def, h]
      rwa [mul_assoc, inv_mul_cancel₀ hq0, mul_one, one_mul] at h2
    have hq₀w' : q₀ * w' = w := by
      rw [hw'def, mul_comm w q₀⁻¹, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
    have hvw' : valuation k w' = valuation k w * (valuation k q₀)⁻¹ := by
      rw [hw'def, map_mul, map_inv₀]
    have hw'high : valuation k w' ≤ 1 := by
      rw [hvw']
      calc valuation k w * (valuation k q₀)⁻¹
          ≤ valuation k q₀ * (valuation k q₀)⁻¹ := mul_le_mul_left hle _
        _ = 1 := mul_inv_cancel₀ hqv
    have hw'low : valuation k q₀ < valuation k w' := by
      rw [hvw']
      have hinvpos : (0 : ValueGroupWithZero k) < (valuation k q₀)⁻¹ :=
        zero_lt_iff.mpr (inv_ne_zero hqv)
      have h2 : valuation k q₀ * valuation k q₀ * (valuation k q₀)⁻¹ <
          valuation k w * (valuation k q₀)⁻¹ :=
        (OrderIso.mulRight₀ _ hinvpos).strictMono hlow
      calc valuation k q₀
          = valuation k q₀ * valuation k q₀ * (valuation k q₀)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hqv, mul_one]
        _ < valuation k w * (valuation k q₀)⁻¹ := h2
    -- the shift hypotheses for `u₀ := w'`
    have hqu : valuation k (q₀ * w') < 1 := by
      rw [hq₀w']
      exact lt_of_le_of_lt hle hq1
    have hquinv : valuation k (q₀ * w'⁻¹) < 1 := by
      rw [map_mul, map_inv₀]
      have hinv'pos : (0 : ValueGroupWithZero k) < (valuation k w')⁻¹ :=
        zero_lt_iff.mpr (inv_ne_zero ((Valuation.ne_zero_iff _).mpr hw'0))
      calc valuation k q₀ * (valuation k w')⁻¹
          < valuation k w' * (valuation k w')⁻¹ :=
            (OrderIso.mulRight₀ _ hinv'pos).strictMono hw'low
        _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr hw'0)
    have hX : bilateralX w q₀ = bilateralX w' q₀ := by
      rw [← hq₀w']
      exact bilateralX_shift w' q₀ hw'0 hq0 hq1 hqu hquinv
    have hY : bilateralY w q₀ = bilateralY w' q₀ := by
      rw [← hq₀w']
      exact bilateralY_shift w' q₀ hw'0 hw'1 hq0 hq1 hqu hquinv
    rw [hX, hY]
    have := nonsingular_evalA w' q₀ hw'0 hw'1 hq0 hw'high hq1 hw'low
    rwa [evalA_XA_eq_bilateralX w' q₀ hw'0 hw'1 hw'high hq1 hw'low,
      evalA_YA_eq_bilateralY w' q₀ hw'0 hw'1 hw'high hq1 hw'low] at this

/-- **The point map through bilateral coordinates**: on the extended window
`|q₀|² < |w| ≤ 1`, `w ∉ {1, q₀}`, the point `pointMap w` is the affine point
with coordinates `(bilateralX w, bilateralY w)`. -/
theorem pointMap_eq_bilateral (w q₀ : k) (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hwq : w ≠ q₀) (hq0 : q₀ ≠ 0) (hq1 : valuation k q₀ < 1)
    (hlow : valuation k q₀ * valuation k q₀ < valuation k w)
    (hhigh : valuation k w ≤ 1) :
    pointMap q₀ hq0 hq1 w hw0 =
      WeierstrassCurve.Affine.Point.some (bilateralX w q₀) (bilateralY w q₀)
        (nonsingular_bilateral w q₀ hw0 hw1 hwq hq0 hq1 hlow hhigh) := by
  have hqv : valuation k q₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  rcases lt_or_ge (valuation k q₀) (valuation k w) with hgt | hle
  · -- `w` in the annulus: `pointMap w` is the annulus point of `w` itself
    rw [pointMap_of_mem_annulus q₀ hq0 hq1 w hw0 hw1 hgt hhigh]
    exact point_some_congr
      (evalA_XA_eq_bilateralX w q₀ hw0 hw1 hhigh hq1 hgt)
      (evalA_YA_eq_bilateralY w q₀ hw0 hw1 hhigh hq1 hgt)
  · -- one shift: `w = q₀ * w'` with `w'` in the annulus
    set w' : k := w * q₀⁻¹ with hw'def
    have hw'0 : w' ≠ 0 := mul_ne_zero hw0 (inv_ne_zero hq0)
    have hw'1 : w' ≠ 1 := by
      intro h
      apply hwq
      have h2 : w * q₀⁻¹ * q₀ = 1 * q₀ := by rw [← hw'def, h]
      rwa [mul_assoc, inv_mul_cancel₀ hq0, mul_one, one_mul] at h2
    have hq₀w' : q₀ * w' = w := by
      rw [hw'def, mul_comm w q₀⁻¹, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
    have hvw' : valuation k w' = valuation k w * (valuation k q₀)⁻¹ := by
      rw [hw'def, map_mul, map_inv₀]
    have hw'high : valuation k w' ≤ 1 := by
      rw [hvw']
      calc valuation k w * (valuation k q₀)⁻¹
          ≤ valuation k q₀ * (valuation k q₀)⁻¹ := mul_le_mul_left hle _
        _ = 1 := mul_inv_cancel₀ hqv
    have hw'low : valuation k q₀ < valuation k w' := by
      rw [hvw']
      have hinvpos : (0 : ValueGroupWithZero k) < (valuation k q₀)⁻¹ :=
        zero_lt_iff.mpr (inv_ne_zero hqv)
      have h2 : valuation k q₀ * valuation k q₀ * (valuation k q₀)⁻¹ <
          valuation k w * (valuation k q₀)⁻¹ :=
        (OrderIso.mulRight₀ _ hinvpos).strictMono hlow
      calc valuation k q₀
          = valuation k q₀ * valuation k q₀ * (valuation k q₀)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hqv, mul_one]
        _ < valuation k w * (valuation k q₀)⁻¹ := h2
    have hqu : valuation k (q₀ * w') < 1 := by
      rw [hq₀w']
      exact lt_of_le_of_lt hle hq1
    have hquinv : valuation k (q₀ * w'⁻¹) < 1 := by
      rw [map_mul, map_inv₀]
      have hinv'pos : (0 : ValueGroupWithZero k) < (valuation k w')⁻¹ :=
        zero_lt_iff.mpr (inv_ne_zero ((Valuation.ne_zero_iff _).mpr hw'0))
      calc valuation k q₀ * (valuation k w')⁻¹
          < valuation k w' * (valuation k w')⁻¹ :=
            (OrderIso.mulRight₀ _ hinv'pos).strictMono hw'low
        _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr hw'0)
    -- normalise: `pointMap w = pointMap w'`
    have hnorm : pointMap q₀ hq0 hq1 w hw0 = pointMap q₀ hq0 hq1 w' hw'0 := by
      have h := pointMap_zpow_mul q₀ hq0 hq1 w' hw'0 1
      calc pointMap q₀ hq0 hq1 w hw0
          = pointMap q₀ hq0 hq1 (q₀ ^ (1 : ℤ) * w')
            (mul_ne_zero (zpow_ne_zero _ hq0) hw'0) :=
            pointMap_congr (by rw [zpow_one, hq₀w'])
        _ = pointMap q₀ hq0 hq1 w' hw'0 := h
    rw [hnorm, pointMap_of_mem_annulus q₀ hq0 hq1 w' hw'0 hw'1 hw'low hw'high]
    refine point_some_congr ?_ ?_
    · rw [evalA_XA_eq_bilateralX w' q₀ hw'0 hw'1 hw'high hq1 hw'low]
      rw [show bilateralX w' q₀ = bilateralX w q₀ from by
        conv_rhs => rw [← hq₀w']
        exact (bilateralX_shift w' q₀ hw'0 hq0 hq1 hqu hquinv).symm]
    · rw [evalA_YA_eq_bilateralY w' q₀ hw'0 hw'1 hw'high hq1 hw'low]
      rw [show bilateralY w' q₀ = bilateralY w q₀ from by
        conv_rhs => rw [← hq₀w']
        exact (bilateralY_shift w' q₀ hw'0 hw'1 hq0 hq1 hqu hquinv).symm]

/-! ### The addition law

The homomorphism property of the point map, against the affine chord–tangent
group law. The two *series identities* — the chord case and the tangent case
of Silverman V.3.1(c) — are the sorried leaves `bilateral_add_of_X_ne` and
`bilateral_add_self`; the fibre structure of the `x`-coordinate (two-to-one up
to the involution `u ↦ u⁻¹·q^ℤ`) is the sorried leaf
`eq_or_mul_eq_of_bilateralX_eq`. Everything else — the vertical (inverse)
case via the PROVEN inversion/shift identities, the reduction of arbitrary
parameters to the extended window, and the quotient bookkeeping — is derived
below. -/

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- `negY` of the Tate curve is `(x, y) ↦ -y - x` (`a₁ = 1`, `a₃ = 0`). -/
theorem tateCurve_negY (q₀ x y : k) :
    (WeierstrassCurve.tateCurve q₀).toAffine.negY x y = -y - x := by
  simp [WeierstrassCurve.Affine.negY, WeierstrassCurve.tateCurve]

/-! ### The two-variable coefficient ring and the formal chord identities

The series content of the chord identities lives in a two-variable
analogue of `CoeffRing`: the localization of `ℚ[u][v]` (inner variable
`u`, outer variable `v`) away from `u(1-u)·v(1-v)·(1-uv)`, with three
slot maps `CoeffRing → CoeffRing₂` substituting `T ↦ u`, `T ↦ v`,
`T ↦ uv`. The chord identities are formal identities between the slot
images of `XA`/`YA`, to be descended from the complex-analytic
`analytic_chordX`/`analytic_chordY` of `TateCurveConstruction.lean`
through `ℚ(u)(v)⟦q⟧`. -/

/-- The bivariate localized denominator `u(1-u)·v(1-v)·(1-uv)` in
`ℚ[u][v]` (inner variable `u`, outer variable `v`). -/
def biDenom : Polynomial (Polynomial ℚ) :=
  Polynomial.C (Polynomial.X * (1 - Polynomial.X)) *
    (Polynomial.X * (1 - Polynomial.X)) *
    (1 - Polynomial.C Polynomial.X * Polynomial.X)

/-- The two-variable coefficient ring
`ℚ[u,v][1/(u(1-u)·v(1-v)·(1-uv))]`. -/
abbrev CoeffRing₂ : Type := Localization.Away biDenom

/-- The image of `u` in `CoeffRing₂`. -/
def uElt₂ : CoeffRing₂ :=
  algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
    (Polynomial.C Polynomial.X)

/-- The image of `v` in `CoeffRing₂`. -/
def vElt₂ : CoeffRing₂ :=
  algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂ Polynomial.X

/-- The image of `u·v` in `CoeffRing₂`. -/
def uvElt₂ : CoeffRing₂ :=
  algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
    (Polynomial.C Polynomial.X * Polynomial.X)

/-- The one-variable polynomial ring maps into `CoeffRing₂` by
substituting the variable. -/
def slotPolyHom (t : CoeffRing₂) : Polynomial ℚ →+* CoeffRing₂ :=
  Polynomial.eval₂RingHom
    ((algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂).comp
      ((Polynomial.C).comp (Polynomial.C))) t

/-- The localized denominator itself is a unit in `CoeffRing₂`. -/
theorem isUnit_biDenom_image :
    IsUnit (algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂ biDenom) :=
  IsLocalization.map_units CoeffRing₂
    (⟨biDenom, Submonoid.mem_powers _⟩ :
      Submonoid.powers biDenom)

/-- The three factors of the localized denominator, as units. -/
theorem isUnit_biDenom_factors :
    IsUnit (algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
        (Polynomial.C (Polynomial.X * (1 - Polynomial.X)))) ∧
    IsUnit (algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
        (Polynomial.X * (1 - Polynomial.X))) ∧
    IsUnit (algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
        (1 - Polynomial.C Polynomial.X * Polynomial.X)) := by
  have h := isUnit_biDenom_image
  have hsplit := congrArg
    (algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂)
    (show biDenom = Polynomial.C (Polynomial.X * (1 - Polynomial.X)) *
      (Polynomial.X * (1 - Polynomial.X)) *
      (1 - Polynomial.C Polynomial.X * Polynomial.X) from rfl)
  rw [map_mul, map_mul] at hsplit
  rw [hsplit] at h
  obtain ⟨hab, hc⟩ := IsUnit.mul_iff.mp h
  obtain ⟨ha, hb⟩ := IsUnit.mul_iff.mp hab
  exact ⟨ha, hb, hc⟩

/-- `u(1-u)` is a unit in `CoeffRing₂`. -/
theorem isUnit_u_one_sub_u :
    IsUnit (slotPolyHom uElt₂
      (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ)) := by
  have ha := isUnit_biDenom_factors.1
  convert ha using 1
  simp [slotPolyHom, uElt₂, map_mul, map_sub, map_one]

/-- `v(1-v)` is a unit in `CoeffRing₂`. -/
theorem isUnit_v_one_sub_v :
    IsUnit (slotPolyHom vElt₂
      (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ)) := by
  have hb := isUnit_biDenom_factors.2.1
  convert hb using 1
  simp [slotPolyHom, vElt₂, map_mul, map_sub, map_one]

/-- `uv(1-uv)` is a unit in `CoeffRing₂`. -/
theorem isUnit_uv_one_sub_uv :
    IsUnit (slotPolyHom uvElt₂
      (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ)) := by
  obtain ⟨ha, hb, hc⟩ := isUnit_biDenom_factors
  rw [show (Polynomial.C (Polynomial.X * (1 - Polynomial.X)) :
      Polynomial (Polynomial ℚ)) = Polynomial.C Polynomial.X *
      Polynomial.C (1 - Polynomial.X) from map_mul _ _ _, map_mul] at ha
  rw [map_mul] at hb
  have hCX := (IsUnit.mul_iff.mp ha).1
  have hX := (IsUnit.mul_iff.mp hb).1
  have huv : IsUnit (algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
      (Polynomial.C Polynomial.X * Polynomial.X)) := by
    rw [map_mul]
    exact hCX.mul hX
  have := huv.mul hc
  convert this using 1
  simp [slotPolyHom, uvElt₂, map_mul, map_sub, map_one]

/-- The `u`-slot map `CoeffRing → CoeffRing₂`. -/
def uSlot : CoeffRing →+* CoeffRing₂ :=
  Localization.awayLift (slotPolyHom uElt₂) _ isUnit_u_one_sub_u

/-- The `v`-slot map `CoeffRing → CoeffRing₂`. -/
def vSlot : CoeffRing →+* CoeffRing₂ :=
  Localization.awayLift (slotPolyHom vElt₂) _ isUnit_v_one_sub_v

/-- The `uv`-slot map `CoeffRing → CoeffRing₂`. -/
def uvSlot : CoeffRing →+* CoeffRing₂ :=
  Localization.awayLift (slotPolyHom uvElt₂) _ isUnit_uv_one_sub_uv

/-! ### The rational-function field `ℚ(u)(v)` and its three embeddings -/

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- Evaluation of `ℚ(X)` at a transcendental element of any field
extension, as a ring homomorphism (the abstract form of the complex
`evalAtHom` of `TateCurveConstruction.lean`). -/
noncomputable def substHom {K L : Type*} [Field K] [Field L]
    [Algebra K L] (t : L) (ht : Transcendental K t) : RatFunc K →+* L where
  toFun r := (RatFunc.algEquivOfTranscendental t ht r : L)
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp

theorem substHom_ratFuncX {K L : Type*} [Field K] [Field L]
    [Algebra K L] (t : L) (ht : Transcendental K t) :
    substHom t ht RatFunc.X = t := by
  simp [substHom]

/-- Transfer of transcendence from the coefficient field `ℚ(u)` down to
`ℚ`, through the uniqueness of ring homomorphisms out of `ℚ` (no
scalar-tower instances needed — the `ℚ`-algebra diamond on
`RatFunc (RatFunc ℚ)` makes towers unusable). -/
theorem transcendental_of_transcendental_ratFunc
    {x : RatFunc (RatFunc ℚ)} (h : Transcendental (RatFunc ℚ) x) :
    Transcendental ℚ x := by
  intro halg
  obtain ⟨q, hq0, hqev⟩ := halg
  refine h ⟨q.map (algebraMap ℚ (RatFunc ℚ)), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff
      (algebraMap ℚ (RatFunc ℚ)).injective).mpr hq0
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))).comp
          (algebraMap ℚ (RatFunc ℚ))
        = algebraMap ℚ (RatFunc (RatFunc ℚ)) from Subsingleton.elim _ _]
    rw [Polynomial.aeval_def] at hqev
    exact hqev

/-- The outer variable of `ℚ(u)(v)` is transcendental over `ℚ`. -/
theorem transcendental_outerX :
    Transcendental ℚ (RatFunc.X (K := RatFunc ℚ)) := by
  have h : Transcendental (RatFunc ℚ) (RatFunc.X (K := RatFunc ℚ)) :=
    RatFunc.transcendental_X
  exact transcendental_of_transcendental_ratFunc h

/-- The element `u·v` of `ℚ(u)(v)` (constant `u` times the outer
variable). -/
noncomputable def uvGen : RatFunc (RatFunc ℚ) :=
  RatFunc.C (RatFunc.X : RatFunc ℚ) * RatFunc.X

/-- `u·v` is transcendental over `ℚ`. -/
theorem transcendental_uvGen : Transcendental ℚ uvGen := by
  unfold uvGen
  refine transcendental_of_transcendental_ratFunc ?_
  intro h1
  have h2 : IsAlgebraic (RatFunc ℚ)
      ((RatFunc.C (RatFunc.X : RatFunc ℚ))⁻¹ : RatFunc (RatFunc ℚ)) := by
    rw [← map_inv₀]
    exact isAlgebraic_algebraMap _
  have h3 := h2.mul h1
  rw [inv_mul_cancel_left₀ (by
    simpa using RatFunc.X_ne_zero (K := ℚ))] at h3
  exact RatFunc.transcendental_X (K := RatFunc ℚ) h3

/-- `X` is transcendental over `ℚ` in `ℚ(u)` (stated instance-robustly:
only hom-uniqueness out of `ℚ` is used, no algebra-structure
comparison). -/
theorem transcendental_ratFuncX_Q :
    Transcendental ℚ (RatFunc.X : RatFunc ℚ) := by
  intro halg
  obtain ⟨q, hq0, hqev⟩ := halg
  refine hq0 (RatFunc.algebraMap_injective (K := ℚ) ?_)
  rw [map_zero, ← hqev, Polynomial.aeval_def]
  have hhom : Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ))
      RatFunc.X = algebraMap (Polynomial ℚ) (RatFunc ℚ) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · exact RingHom.congr_fun (Subsingleton.elim
        ((Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ))
          RatFunc.X).comp (Polynomial.C : ℚ →+* Polynomial ℚ))
        ((algebraMap (Polynomial ℚ) (RatFunc ℚ)).comp
          (Polynomial.C : ℚ →+* Polynomial ℚ))) a
    · simp [RatFunc.algebraMap_X]
  exact (RingHom.congr_fun hhom q).symm

/-- The constant `u` of `ℚ(u)(v)` is transcendental over `ℚ`. -/
theorem transcendental_CX :
    Transcendental ℚ
      (RatFunc.C (RatFunc.X : RatFunc ℚ) : RatFunc (RatFunc ℚ)) := by
  intro halg
  obtain ⟨q, hq0, hqev⟩ := halg
  refine transcendental_ratFuncX_Q ⟨q, hq0, ?_⟩
  have hC : Function.Injective
      (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) :=
    RingHom.injective _
  apply hC
  rw [map_zero, ← hqev, Polynomial.aeval_def, Polynomial.aeval_def,
    Polynomial.hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

/-- The constant embedding `ℚ(u) → ℚ(u)(v)` (as a substitution, for
uniformity with the other two slots). -/
noncomputable def uEmbR : RatFunc ℚ →+* RatFunc (RatFunc ℚ) :=
  substHom (RatFunc.C (RatFunc.X : RatFunc ℚ)) transcendental_CX

/-- The substitution `u ↦ v` as `ℚ(u) → ℚ(u)(v)`. -/
noncomputable def vEmbR : RatFunc ℚ →+* RatFunc (RatFunc ℚ) :=
  substHom (RatFunc.X : RatFunc (RatFunc ℚ)) transcendental_outerX

/-- The substitution `u ↦ u·v` as `ℚ(u) → ℚ(u)(v)`. -/
noncomputable def uvEmbR : RatFunc ℚ →+* RatFunc (RatFunc ℚ) :=
  substHom uvGen transcendental_uvGen

/-! ### The injection `CoeffRing₂ → ℚ(u)(v)` and the slot compatibilities -/

/-- The canonical map `ℚ[u][v] → ℚ(u)(v)`. -/
noncomputable def biPolyToRatFunc :
    Polynomial (Polynomial ℚ) →+* RatFunc (RatFunc ℚ) :=
  (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ))).comp
    (Polynomial.mapRingHom (algebraMap (Polynomial ℚ) (RatFunc ℚ)))

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- `biPolyToRatFunc` is injective. -/
theorem biPolyToRatFunc_injective : Function.Injective biPolyToRatFunc := by
  have h1 : Function.Injective
      ⇑(algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ))) :=
    RatFunc.algebraMap_injective (K := RatFunc ℚ)
  have h2 : Function.Injective
      ⇑(Polynomial.mapRingHom (algebraMap (Polynomial ℚ) (RatFunc ℚ))) := by
    simpa [Polynomial.coe_mapRingHom] using
      Polynomial.map_injective _ (RatFunc.algebraMap_injective (K := ℚ))
  rw [biPolyToRatFunc, RingHom.coe_comp]
  exact h1.comp h2

/-- The image of the localized denominator is a unit of `ℚ(u)(v)`. -/
theorem isUnit_biPolyToRatFunc_biDenom :
    IsUnit (biPolyToRatFunc biDenom) := by
  refine isUnit_iff_ne_zero.mpr ?_
  rw [show (biPolyToRatFunc biDenom : RatFunc (RatFunc ℚ))
      = biPolyToRatFunc biDenom from rfl]
  intro h0
  have hne : biDenom ≠ 0 := by
    intro hz
    have h1 := congrArg
      (Polynomial.eval ((Polynomial.C (1/2 : ℚ)) : Polynomial ℚ)) hz
    unfold biDenom at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero] at h1
    have h2 := congrArg (Polynomial.eval (1/2 : ℚ)) h1
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero] at h2
    norm_num at h2
  exact hne (biPolyToRatFunc_injective (by simpa using h0))

/-- The lift `CoeffRing₂ → ℚ(u)(v)`. -/
noncomputable def coeffRing₂ToRatFunc :
    CoeffRing₂ →+* RatFunc (RatFunc ℚ) :=
  Localization.awayLift biPolyToRatFunc _ isUnit_biPolyToRatFunc_biDenom

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- The inclusion of the two-variable coefficient ring in `ℚ(u)(v)` is
injective. -/
theorem coeffRing₂ToRatFunc_injective :
    Function.Injective coeffRing₂ToRatFunc := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, hmk⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers biDenom) x
  have hxs : x * algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂ s.1 =
      algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂ a := by
    rw [← hmk]
    exact IsLocalization.mk'_spec _ a s
  have himg : biPolyToRatFunc a = 0 := by
    have h1 := congrArg coeffRing₂ToRatFunc hxs
    rw [map_mul, hx, zero_mul,
      show coeffRing₂ToRatFunc (algebraMap (Polynomial (Polynomial ℚ))
        CoeffRing₂ a) = biPolyToRatFunc a from IsLocalization.lift_eq _ _]
      at h1
    exact h1.symm
  have ha : a = 0 := by
    apply biPolyToRatFunc_injective
    rw [himg, map_zero]
  rw [← hmk, ha, IsLocalization.mk'_eq_iff_eq_mul, zero_mul, map_zero]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- The generic slot compatibility: composing the `ℚ(u)(v)`-injection
with a slot map is the corresponding substitution composed with the
one-variable injection, provided the generators match. -/
theorem coeffRing₂ToRatFunc_slot (t₂ : CoeffRing₂)
    (tR : RatFunc (RatFunc ℚ)) (htR : Transcendental ℚ tR)
    (hunit : IsUnit (slotPolyHom t₂
      (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ)))
    (hval : coeffRing₂ToRatFunc t₂ = tR) :
    coeffRing₂ToRatFunc.comp
        (Localization.awayLift (slotPolyHom t₂) _ hunit) =
      (substHom tR htR).comp coeffRingToRatFunc := by
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ))
    ?_
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · exact RingHom.congr_fun (Subsingleton.elim
      (((coeffRing₂ToRatFunc.comp (Localization.awayLift (slotPolyHom t₂)
        _ hunit)).comp (algebraMap (Polynomial ℚ) CoeffRing)).comp
        (Polynomial.C : ℚ →+* Polynomial ℚ))
      ((((substHom tR htR).comp coeffRingToRatFunc).comp
        (algebraMap (Polynomial ℚ) CoeffRing)).comp
        (Polynomial.C : ℚ →+* Polynomial ℚ))) a
  · simp only [RingHom.comp_apply]
    rw [show (Localization.awayLift (slotPolyHom t₂) _ hunit)
        (algebraMap (Polynomial ℚ) CoeffRing Polynomial.X)
        = slotPolyHom t₂ Polynomial.X from IsLocalization.lift_eq _ _,
      show coeffRingToRatFunc
        (algebraMap (Polynomial ℚ) CoeffRing Polynomial.X)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X from
        IsLocalization.lift_eq _ _,
      RatFunc.algebraMap_X, substHom_ratFuncX,
      show slotPolyHom t₂ Polynomial.X = t₂ by simp [slotPolyHom]]
    exact hval

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- The generator values of the injection. -/
theorem coeffRing₂ToRatFunc_uElt₂ :
    coeffRing₂ToRatFunc uElt₂ = RatFunc.C (RatFunc.X : RatFunc ℚ) := by
  rw [show uElt₂ = algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
      (Polynomial.C Polynomial.X) from rfl,
    show coeffRing₂ToRatFunc (algebraMap (Polynomial (Polynomial ℚ))
      CoeffRing₂ (Polynomial.C Polynomial.X)) = biPolyToRatFunc
      (Polynomial.C Polynomial.X) from IsLocalization.lift_eq _ _]
  simp [biPolyToRatFunc]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
theorem coeffRing₂ToRatFunc_vElt₂ :
    coeffRing₂ToRatFunc vElt₂ = (RatFunc.X : RatFunc (RatFunc ℚ)) := by
  rw [show vElt₂ = algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
      Polynomial.X from rfl,
    show coeffRing₂ToRatFunc (algebraMap (Polynomial (Polynomial ℚ))
      CoeffRing₂ Polynomial.X) = biPolyToRatFunc Polynomial.X from
      IsLocalization.lift_eq _ _]
  simp [biPolyToRatFunc]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
theorem coeffRing₂ToRatFunc_uvElt₂ :
    coeffRing₂ToRatFunc uvElt₂ = uvGen := by
  rw [show uvElt₂ = algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
      (Polynomial.C Polynomial.X * Polynomial.X) from rfl,
    show coeffRing₂ToRatFunc (algebraMap (Polynomial (Polynomial ℚ))
      CoeffRing₂ (Polynomial.C Polynomial.X * Polynomial.X))
      = biPolyToRatFunc (Polynomial.C Polynomial.X * Polynomial.X) from
      IsLocalization.lift_eq _ _]
  simp [biPolyToRatFunc, uvGen]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- The three slot compatibilities. -/
theorem coeffRing₂ToRatFunc_uSlot :
    coeffRing₂ToRatFunc.comp uSlot = uEmbR.comp coeffRingToRatFunc :=
  coeffRing₂ToRatFunc_slot uElt₂ _ transcendental_CX
    isUnit_u_one_sub_u coeffRing₂ToRatFunc_uElt₂

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
theorem coeffRing₂ToRatFunc_vSlot :
    coeffRing₂ToRatFunc.comp vSlot = vEmbR.comp coeffRingToRatFunc :=
  coeffRing₂ToRatFunc_slot vElt₂ _ transcendental_outerX
    isUnit_v_one_sub_v coeffRing₂ToRatFunc_vElt₂

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
theorem coeffRing₂ToRatFunc_uvSlot :
    coeffRing₂ToRatFunc.comp uvSlot = uvEmbR.comp coeffRingToRatFunc :=
  coeffRing₂ToRatFunc_slot uvElt₂ _ transcendental_uvGen
    isUnit_uv_one_sub_uv coeffRing₂ToRatFunc_uvElt₂

/-! ### The two-variable descent from the analytic chord identities -/

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- `substHom` is compatible with the coefficient algebra. -/
theorem substHom_algebraMap {K L : Type*} [Field K] [Field L]
    [Algebra K L] (t : L) (ht : Transcendental K t) (c : K) :
    substHom t ht (algebraMap K (RatFunc K) c) = algebraMap K L c := by
  have h := (RatFunc.algEquivOfTranscendental t ht).commutes c
  have h2 := congrArg Subtype.val h
  simpa [substHom] using h2

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- Ring homomorphisms out of `ℚ(X)` into a field are determined by the
image of `X`. -/
theorem ratFuncQ_ringHom_ext {L : Type*} [Field L]
    {f g : RatFunc ℚ →+* L} (h : f RatFunc.X = g RatFunc.X) : f = g := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℚ)) ?_
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have hsub : (f.comp (algebraMap (Polynomial ℚ) (RatFunc ℚ))).comp
        (Polynomial.C : ℚ →+* Polynomial ℚ)
        = (g.comp (algebraMap (Polynomial ℚ) (RatFunc ℚ))).comp
          (Polynomial.C : ℚ →+* Polynomial ℚ) := Subsingleton.elim _ _
    exact RingHom.congr_fun hsub a
  · simp only [RingHom.comp_apply, RatFunc.algebraMap_X]
    exact h

/-- A transcendental complex number of modulus in `(1/4, 1/2)`:
`liouvilleNumber 2 − 1`. -/
theorem exists_transcendental_quarter_half :
    ∃ u₀ : ℂ, Transcendental ℚ u₀ ∧ 1/4 < ‖u₀‖ ∧ ‖u₀‖ < 1/2 := by
  set L : ℝ := liouvilleNumber 2 with hLdef
  have htL : Transcendental ℤ L :=
    transcendental_liouvilleNumber le_rfl
  have hps := LiouvilleNumber.partialSum_add_remainder (m := 2)
    one_lt_two 2
  have hrem_pos := LiouvilleNumber.remainder_pos (m := 2) one_lt_two 2
  have hrem_lt := LiouvilleNumber.remainder_lt 2 (le_refl (2 : ℝ))
  have hpsval : LiouvilleNumber.partialSum 2 2 = 5/4 := by
    rw [LiouvilleNumber.partialSum]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hL_lb : (5/4 : ℝ) < L := by
    rw [hLdef, ← hps, hpsval]
    linarith
  have hL_ub : L < 21/16 := by
    have h16 : LiouvilleNumber.remainder 2 2 < 1/16 := by
      have := hrem_lt
      norm_num [Nat.factorial] at this
      linarith
    rw [hLdef, ← hps, hpsval]
    linarith
  haveI : Algebra.IsAlgebraic ℤ ℚ :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := ℚ)).mpr
      inferInstance
  have htLQ : Transcendental ℚ L :=
    (Algebra.IsAlgebraic.transcendental_iff ℤ ℚ).mp htL
  have htL1 : Transcendental ℚ (L - 1) := by
    intro halg
    exact htLQ (by simpa using halg.add (isAlgebraic_one (R := ℚ) (A := ℝ)))
  refine ⟨((L - 1 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · have hcast := (transcendental_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
      (algebraMap ℝ ℂ).injective).mpr htL1
    simpa using hcast
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- `ℚ(u)` is countable (via the numerator/denominator pair). -/
theorem countable_ratFuncQ : Countable (RatFunc ℚ) := by
  haveI : Countable (Polynomial ℚ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    calc Cardinal.mk (Polynomial ℚ) ≤ max (Cardinal.mk ℚ) Cardinal.aleph0 :=
          Polynomial.cardinalMk_le_max
      _ ≤ Cardinal.aleph0 := by
          rw [max_le_iff]
          exact ⟨Cardinal.mk_le_aleph0, le_refl _⟩
  have hinj : Function.Injective
      (fun r : RatFunc ℚ => (r.num, r.denom)) := by
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    rw [← RatFunc.num_div_denom a, ← RatFunc.num_div_denom b,
      hab.1, hab.2]
  exact Function.Injective.countable hinj

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- Existence of a second-slot transcendental: a real in `(1/2, 1)`
transcendental over the (countable) image of `ℚ(u₀)`. -/
theorem exists_transcendental_pair (u₀ : ℂ) (hu : Transcendental ℚ u₀) :
    ∃ v₀ : ℂ,
      (letI : Algebra (RatFunc ℚ) ℂ := (Blueprint.evalAtHom u₀ hu).toAlgebra
       Transcendental (RatFunc ℚ) v₀) ∧ 1/2 < ‖v₀‖ ∧ ‖v₀‖ < 1 := by
  letI : Algebra (RatFunc ℚ) ℂ := (Blueprint.evalAtHom u₀ hu).toAlgebra
  haveI : Countable (RatFunc ℚ) := countable_ratFuncQ
  have halg : {x : ℂ | IsAlgebraic (RatFunc ℚ) x}.Countable :=
    Algebraic.countable (RatFunc ℚ) ℂ
  by_contra hno
  have hsub : ((↑) : ℝ → ℂ) '' Set.Ioo (1/2 : ℝ) 1 ⊆
      {x : ℂ | IsAlgebraic (RatFunc ℚ) x} := by
    rintro z ⟨x, ⟨hx1, hx2⟩, rfl⟩
    by_contra htr
    refine hno ⟨(x : ℂ), htr, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      exact hx1
    · rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      exact hx2
  have hIoo : (Set.Ioo (1/2 : ℝ) 1).Countable :=
    Set.countable_of_injective_of_countable_image
      (fun x _ y _ h => Complex.ofReal_injective h) (halg.mono hsub)
  exact not_le_of_gt Cardinal.aleph0_lt_continuum
    (Cardinal.mk_Ioo_real (by norm_num : (1/2 : ℝ) < 1) ▸
      Cardinal.le_aleph0_iff_set_countable.mpr hIoo)

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- The archimedean Cauchy product for an arbitrary coefficient
homomorphism into `ℂ` (mirror of `hasSum_evalAt_mul`). -/
theorem hasSum_homC_mul {R : Type*} [CommRing R] (E : R →+* ℂ) {q : ℂ}
    {F G : PowerSeries R} {A B : ℂ}
    (hF : HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n F) * q ^ n) A)
    (hG : HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n G) * q ^ n) B) :
    HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n (F * G)) * q ^ n)
      (A * B) := by
  have hprod := hasSum_sum_range_mul_of_summable_norm
    hF.summable.norm hG.summable.norm
  rw [hF.tsum_eq, hG.tsum_eq] at hprod
  refine hprod.congr_fun fun n ↦ ?_
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y ↦ (E ((PowerSeries.coeff x) F) * q ^ x) *
      (E ((PowerSeries.coeff y) G) * q ^ y)), map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [map_mul, ← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
theorem hasSum_homC_add {R : Type*} [CommRing R] (E : R →+* ℂ) {q : ℂ}
    {F G : PowerSeries R} {A B : ℂ}
    (hF : HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n F) * q ^ n) A)
    (hG : HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n G) * q ^ n) B) :
    HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n (F + G)) * q ^ n)
      (A + B) := by
  refine (hF.add hG).congr_fun fun n ↦ ?_
  rw [map_add, map_add, add_mul]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
theorem hasSum_homC_neg {R : Type*} [CommRing R] (E : R →+* ℂ) {q : ℂ}
    {F : PowerSeries R} {A : ℂ}
    (hF : HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n F) * q ^ n) A) :
    HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n (-F)) * q ^ n) (-A) := by
  refine hF.neg.congr_fun fun n ↦ ?_
  rw [map_neg, map_neg, neg_mul]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
theorem hasSum_homC_sub {R : Type*} [CommRing R] (E : R →+* ℂ) {q : ℂ}
    {F G : PowerSeries R} {A B : ℂ}
    (hF : HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n F) * q ^ n) A)
    (hG : HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n G) * q ^ n) B) :
    HasSum (fun n : ℕ ↦ E (PowerSeries.coeff n (F - G)) * q ^ n)
      (A - B) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact hasSum_homC_add E hF (hasSum_homC_neg E hG)

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- Transcendence transfer at the complex level: transcendental over the
image of `ℚ(u₀)` implies transcendental over `ℚ`. -/
theorem transcendental_of_pair (u₀ : ℂ) (hu : Transcendental ℚ u₀)
    {x : ℂ}
    (h : letI : Algebra (RatFunc ℚ) ℂ := (Blueprint.evalAtHom u₀ hu).toAlgebra
      Transcendental (RatFunc ℚ) x) :
    Transcendental ℚ x := by
  letI : Algebra (RatFunc ℚ) ℂ := (Blueprint.evalAtHom u₀ hu).toAlgebra
  intro halg
  obtain ⟨q, hq0, hqev⟩ := halg
  refine h ⟨q.map (algebraMap ℚ (RatFunc ℚ)),
    (Polynomial.map_ne_zero_iff (algebraMap ℚ (RatFunc ℚ)).injective).mpr
      hq0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    show (algebraMap (RatFunc ℚ) ℂ).comp (algebraMap ℚ (RatFunc ℚ))
      = algebraMap ℚ ℂ from Subsingleton.elim _ _]
  rw [Polynomial.aeval_def] at hqev
  exact hqev

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [CharZero k] in
/-- Algebraicity lifts from `ℚ` to the image of `ℚ(u₀)`. -/
theorem isAlgebraic_pair_of_isAlgebraic (u₀ : ℂ) (hu : Transcendental ℚ u₀)
    {x : ℂ} (h : IsAlgebraic ℚ x) :
    letI : Algebra (RatFunc ℚ) ℂ := (Blueprint.evalAtHom u₀ hu).toAlgebra
    IsAlgebraic (RatFunc ℚ) x := by
  letI : Algebra (RatFunc ℚ) ℂ := (Blueprint.evalAtHom u₀ hu).toAlgebra
  obtain ⟨q, hq0, hqev⟩ := h
  refine ⟨q.map (algebraMap ℚ (RatFunc ℚ)),
    (Polynomial.map_ne_zero_iff (algebraMap ℚ (RatFunc ℚ)).injective).mpr
      hq0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    show (algebraMap (RatFunc ℚ) ℂ).comp (algebraMap ℚ (RatFunc ℚ))
      = algebraMap ℚ ℂ from Subsingleton.elim _ _]
  rw [Polynomial.aeval_def] at hqev
  exact hqev

/-- **The chord `X`-identity in `ℚ(u)(v)⟦q⟧`** (DERIVED by the
two-variable descent from `analytic_chordX`: one algebraically
independent transcendental pair suffices, since the evaluation is an
injective field homomorphism). -/
theorem chordX_ratFunc₂ :
    (PowerSeries.map uvEmbR TateCurve.X + PowerSeries.map uEmbR TateCurve.X
        + PowerSeries.map vEmbR TateCurve.X) *
      (PowerSeries.map uEmbR TateCurve.X
        - PowerSeries.map vEmbR TateCurve.X) ^ 2 =
    (PowerSeries.map uEmbR TateCurve.Y
        - PowerSeries.map vEmbR TateCurve.Y) ^ 2 +
      (PowerSeries.map uEmbR TateCurve.Y
        - PowerSeries.map vEmbR TateCurve.Y) *
        (PowerSeries.map uEmbR TateCurve.X
          - PowerSeries.map vEmbR TateCurve.X) := by
  obtain ⟨u₀, hu₀t, hu₀l, hu₀h⟩ := exists_transcendental_quarter_half
  letI : Algebra (RatFunc ℚ) ℂ := (Blueprint.evalAtHom u₀ hu₀t).toAlgebra
  obtain ⟨v₀, hv₀t, hv₀l, hv₀h⟩ := exists_transcendental_pair u₀ hu₀t
  set H : RatFunc (RatFunc ℚ) →+* ℂ := substHom v₀ hv₀t with hHdef
  have hHinj : Function.Injective H := H.injective
  have hu₀0 : (0 : ℝ) < ‖u₀‖ := lt_trans (by norm_num) hu₀l
  have hv₀0 : (0 : ℝ) < ‖v₀‖ := lt_trans (by norm_num) hv₀l
  have hu₀ne : u₀ ≠ 0 := norm_pos_iff.mp hu₀0
  have huv_l : (1/8 : ℝ) < ‖u₀ * v₀‖ := by
    rw [norm_mul]
    nlinarith
  have huv_h : ‖u₀ * v₀‖ < 1 := by
    rw [norm_mul]
    nlinarith
  have hv₀ℚ : Transcendental ℚ v₀ := transcendental_of_pair u₀ hu₀t hv₀t
  have huvt : Transcendental ℚ (u₀ * v₀) := by
    intro halg
    have h1 := isAlgebraic_pair_of_isAlgebraic u₀ hu₀t halg
    have h2 : IsAlgebraic (RatFunc ℚ)
        (algebraMap (RatFunc ℚ) ℂ (RatFunc.X)⁻¹) :=
      isAlgebraic_algebraMap _
    have h3 := h2.mul h1
    have hval : algebraMap (RatFunc ℚ) ℂ (RatFunc.X)⁻¹ * (u₀ * v₀) = v₀ := by
      have hX : algebraMap (RatFunc ℚ) ℂ RatFunc.X = u₀ :=
        Blueprint.evalAtHom_ratFuncX u₀ hu₀t
      rw [map_inv₀, hX]
      field_simp
    rw [hval] at h3
    exact hv₀t h3
  -- the three hom compatibilities
  have hHalg : ∀ r : RatFunc ℚ,
      H (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ)) r)
        = Blueprint.evalAtHom u₀ hu₀t r := fun r =>
    substHom_algebraMap v₀ hv₀t r
  have hCeq : (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ))
      = algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ)) := by
    refine RingHom.ext fun r => ?_
    rw [RatFunc.algebraMap_eq_C]
  have hCXval : H (RatFunc.C (RatFunc.X : RatFunc ℚ)) = u₀ := by
    rw [hCeq, hHalg, Blueprint.evalAtHom_ratFuncX]
  have hHu : H.comp uEmbR = Blueprint.evalAtHom u₀ hu₀t := by
    refine ratFuncQ_ringHom_ext ?_
    rw [RingHom.comp_apply,
      show uEmbR RatFunc.X = RatFunc.C (RatFunc.X : RatFunc ℚ) from
        substHom_ratFuncX _ _,
      hCXval, Blueprint.evalAtHom_ratFuncX]
  have hHv : H.comp vEmbR = Blueprint.evalAtHom v₀ hv₀ℚ := by
    refine ratFuncQ_ringHom_ext ?_
    rw [RingHom.comp_apply,
      show vEmbR RatFunc.X = (RatFunc.X : RatFunc (RatFunc ℚ)) from
        substHom_ratFuncX _ _,
      show H (RatFunc.X : RatFunc (RatFunc ℚ)) = v₀ from
        substHom_ratFuncX _ _,
      Blueprint.evalAtHom_ratFuncX]
  have hHuv : H.comp uvEmbR = Blueprint.evalAtHom (u₀ * v₀) huvt := by
    refine ratFuncQ_ringHom_ext ?_
    rw [RingHom.comp_apply,
      show uvEmbR RatFunc.X = uvGen from substHom_ratFuncX _ _,
      show H uvGen = u₀ * v₀ by
        rw [uvGen, map_mul, hCXval,
          show H (RatFunc.X : RatFunc (RatFunc ℚ)) = v₀ from
            substHom_ratFuncX _ _],
      Blueprint.evalAtHom_ratFuncX]
  -- the six coefficient-sequence identifications and sums
  have hseq : ∀ (em : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) (t : ℂ)
      (ht : Transcendental ℚ t)
      (hcomp : H.comp em = Blueprint.evalAtHom t ht)
      (F : PowerSeries (RatFunc ℚ)) (n : ℕ),
      H (PowerSeries.coeff n (PowerSeries.map em F))
        = Blueprint.evalAt t (PowerSeries.coeff n F) := by
    intro em t ht hcomp F n
    rw [PowerSeries.coeff_map, ← RingHom.comp_apply, hcomp,
      Blueprint.evalAtHom_apply]
  have hXu : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map uEmbR TateCurve.X)) * q ^ n)
      (Blueprint.XAn u₀ q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_X_eval hu₀t hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq uEmbR u₀ hu₀t hHu]
  have hXv : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map vEmbR TateCurve.X)) * q ^ n)
      (Blueprint.XAn v₀ q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_X_eval hv₀ℚ hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq vEmbR v₀ hv₀ℚ hHv]
  have hXw : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map uvEmbR TateCurve.X)) * q ^ n)
      (Blueprint.XAn (u₀ * v₀) q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_X_eval huvt hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq uvEmbR (u₀ * v₀) huvt hHuv]
  have hYu : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map uEmbR TateCurve.Y)) * q ^ n)
      (Blueprint.YAn u₀ q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_Y_eval hu₀t hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq uEmbR u₀ hu₀t hHu]
  have hYv : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map vEmbR TateCurve.Y)) * q ^ n)
      (Blueprint.YAn v₀ q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_Y_eval hv₀ℚ hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq vEmbR v₀ hv₀ℚ hHv]
  -- vanishing of the difference coefficients
  rw [← sub_eq_zero]
  have hcoeff := Blueprint.coeffs_eq_zero_of_hasSum_punctured
    (fun n => H (PowerSeries.coeff n
      ((PowerSeries.map uvEmbR TateCurve.X + PowerSeries.map uEmbR TateCurve.X
          + PowerSeries.map vEmbR TateCurve.X) *
        (PowerSeries.map uEmbR TateCurve.X
          - PowerSeries.map vEmbR TateCurve.X) ^ 2 -
        ((PowerSeries.map uEmbR TateCurve.Y
            - PowerSeries.map vEmbR TateCurve.Y) ^ 2 +
          (PowerSeries.map uEmbR TateCurve.Y
            - PowerSeries.map vEmbR TateCurve.Y) *
            (PowerSeries.map uEmbR TateCurve.X
              - PowerSeries.map vEmbR TateCurve.X)))))
    (1/8) (by norm_num) ?_
  · ext n
    have h1 := congrFun hcoeff n
    simp only [Pi.zero_apply] at h1
    rw [map_zero]
    exact hHinj (by rw [h1, map_zero])
  · intro q hq0 hq8
    have h1 := hasSum_homC_add H (hasSum_homC_add H (hXw q hq0 hq8)
      (hXu q hq0 hq8)) (hXv q hq0 hq8)
    have h2 := hasSum_homC_sub H (hXu q hq0 hq8) (hXv q hq0 hq8)
    have h3 := hasSum_homC_sub H (hYu q hq0 hq8) (hYv q hq0 hq8)
    have h2sq : HasSum (fun n => H (PowerSeries.coeff n
        ((PowerSeries.map uEmbR TateCurve.X
          - PowerSeries.map vEmbR TateCurve.X) ^ 2)) * q ^ n)
        ((Blueprint.XAn u₀ q - Blueprint.XAn v₀ q) *
          (Blueprint.XAn u₀ q - Blueprint.XAn v₀ q)) := by
      rw [pow_two]
      exact hasSum_homC_mul H h2 h2
    have h3sq : HasSum (fun n => H (PowerSeries.coeff n
        ((PowerSeries.map uEmbR TateCurve.Y
          - PowerSeries.map vEmbR TateCurve.Y) ^ 2)) * q ^ n)
        ((Blueprint.YAn u₀ q - Blueprint.YAn v₀ q) *
          (Blueprint.YAn u₀ q - Blueprint.YAn v₀ q)) := by
      rw [pow_two]
      exact hasSum_homC_mul H h3 h3
    have hL := hasSum_homC_mul H h1 h2sq
    have hR := hasSum_homC_add H h3sq (hasSum_homC_mul H h3 h2)
    have hval : (Blueprint.XAn (u₀ * v₀) q + Blueprint.XAn u₀ q
        + Blueprint.XAn v₀ q) *
        ((Blueprint.XAn u₀ q - Blueprint.XAn v₀ q) *
          (Blueprint.XAn u₀ q - Blueprint.XAn v₀ q)) -
        ((Blueprint.YAn u₀ q - Blueprint.YAn v₀ q) *
          (Blueprint.YAn u₀ q - Blueprint.YAn v₀ q) +
          (Blueprint.YAn u₀ q - Blueprint.YAn v₀ q) *
            (Blueprint.XAn u₀ q - Blueprint.XAn v₀ q)) = 0 := by
      have h := Blueprint.analytic_chordX hq0 (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) huv_h
      linear_combination h
    have hsum := hasSum_homC_sub H hL hR
    rw [hval] at hsum
    exact hsum

/-- **The chord `Y`-identity in `ℚ(u)(v)⟦q⟧`** (DERIVED by the same
two-variable descent from `analytic_chordY`). -/
theorem chordY_ratFunc₂ :
    -(PowerSeries.map uvEmbR TateCurve.Y + PowerSeries.map uvEmbR TateCurve.X) *
      (PowerSeries.map uEmbR TateCurve.X
        - PowerSeries.map vEmbR TateCurve.X) =
    (PowerSeries.map uEmbR TateCurve.Y
        - PowerSeries.map vEmbR TateCurve.Y) *
        (PowerSeries.map uvEmbR TateCurve.X
          - PowerSeries.map uEmbR TateCurve.X) +
      PowerSeries.map uEmbR TateCurve.Y *
        (PowerSeries.map uEmbR TateCurve.X
          - PowerSeries.map vEmbR TateCurve.X) := by
  obtain ⟨u₀, hu₀t, hu₀l, hu₀h⟩ := exists_transcendental_quarter_half
  letI : Algebra (RatFunc ℚ) ℂ := (Blueprint.evalAtHom u₀ hu₀t).toAlgebra
  obtain ⟨v₀, hv₀t, hv₀l, hv₀h⟩ := exists_transcendental_pair u₀ hu₀t
  set H : RatFunc (RatFunc ℚ) →+* ℂ := substHom v₀ hv₀t with hHdef
  have hHinj : Function.Injective H := H.injective
  have hu₀0 : (0 : ℝ) < ‖u₀‖ := lt_trans (by norm_num) hu₀l
  have hv₀0 : (0 : ℝ) < ‖v₀‖ := lt_trans (by norm_num) hv₀l
  have hu₀ne : u₀ ≠ 0 := norm_pos_iff.mp hu₀0
  have huv_l : (1/8 : ℝ) < ‖u₀ * v₀‖ := by
    rw [norm_mul]
    nlinarith
  have huv_h : ‖u₀ * v₀‖ < 1 := by
    rw [norm_mul]
    nlinarith
  have hv₀ℚ : Transcendental ℚ v₀ := transcendental_of_pair u₀ hu₀t hv₀t
  have huvt : Transcendental ℚ (u₀ * v₀) := by
    intro halg
    have h1 := isAlgebraic_pair_of_isAlgebraic u₀ hu₀t halg
    have h2 : IsAlgebraic (RatFunc ℚ)
        (algebraMap (RatFunc ℚ) ℂ (RatFunc.X)⁻¹) :=
      isAlgebraic_algebraMap _
    have h3 := h2.mul h1
    have hval : algebraMap (RatFunc ℚ) ℂ (RatFunc.X)⁻¹ * (u₀ * v₀) = v₀ := by
      have hX : algebraMap (RatFunc ℚ) ℂ RatFunc.X = u₀ :=
        Blueprint.evalAtHom_ratFuncX u₀ hu₀t
      rw [map_inv₀, hX]
      field_simp
    rw [hval] at h3
    exact hv₀t h3
  -- the three hom compatibilities
  have hHalg : ∀ r : RatFunc ℚ,
      H (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ)) r)
        = Blueprint.evalAtHom u₀ hu₀t r := fun r =>
    substHom_algebraMap v₀ hv₀t r
  have hCeq : (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ))
      = algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ)) := by
    refine RingHom.ext fun r => ?_
    rw [RatFunc.algebraMap_eq_C]
  have hCXval : H (RatFunc.C (RatFunc.X : RatFunc ℚ)) = u₀ := by
    rw [hCeq, hHalg, Blueprint.evalAtHom_ratFuncX]
  have hHu : H.comp uEmbR = Blueprint.evalAtHom u₀ hu₀t := by
    refine ratFuncQ_ringHom_ext ?_
    rw [RingHom.comp_apply,
      show uEmbR RatFunc.X = RatFunc.C (RatFunc.X : RatFunc ℚ) from
        substHom_ratFuncX _ _,
      hCXval, Blueprint.evalAtHom_ratFuncX]
  have hHv : H.comp vEmbR = Blueprint.evalAtHom v₀ hv₀ℚ := by
    refine ratFuncQ_ringHom_ext ?_
    rw [RingHom.comp_apply,
      show vEmbR RatFunc.X = (RatFunc.X : RatFunc (RatFunc ℚ)) from
        substHom_ratFuncX _ _,
      show H (RatFunc.X : RatFunc (RatFunc ℚ)) = v₀ from
        substHom_ratFuncX _ _,
      Blueprint.evalAtHom_ratFuncX]
  have hHuv : H.comp uvEmbR = Blueprint.evalAtHom (u₀ * v₀) huvt := by
    refine ratFuncQ_ringHom_ext ?_
    rw [RingHom.comp_apply,
      show uvEmbR RatFunc.X = uvGen from substHom_ratFuncX _ _,
      show H uvGen = u₀ * v₀ by
        rw [uvGen, map_mul, hCXval,
          show H (RatFunc.X : RatFunc (RatFunc ℚ)) = v₀ from
            substHom_ratFuncX _ _],
      Blueprint.evalAtHom_ratFuncX]
  -- the six coefficient-sequence identifications and sums
  have hseq : ∀ (em : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) (t : ℂ)
      (ht : Transcendental ℚ t)
      (hcomp : H.comp em = Blueprint.evalAtHom t ht)
      (F : PowerSeries (RatFunc ℚ)) (n : ℕ),
      H (PowerSeries.coeff n (PowerSeries.map em F))
        = Blueprint.evalAt t (PowerSeries.coeff n F) := by
    intro em t ht hcomp F n
    rw [PowerSeries.coeff_map, ← RingHom.comp_apply, hcomp,
      Blueprint.evalAtHom_apply]
  have hXu : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map uEmbR TateCurve.X)) * q ^ n)
      (Blueprint.XAn u₀ q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_X_eval hu₀t hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq uEmbR u₀ hu₀t hHu]
  have hXv : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map vEmbR TateCurve.X)) * q ^ n)
      (Blueprint.XAn v₀ q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_X_eval hv₀ℚ hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq vEmbR v₀ hv₀ℚ hHv]
  have hXw : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map uvEmbR TateCurve.X)) * q ^ n)
      (Blueprint.XAn (u₀ * v₀) q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_X_eval huvt hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq uvEmbR (u₀ * v₀) huvt hHuv]
  have hYu : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map uEmbR TateCurve.Y)) * q ^ n)
      (Blueprint.YAn u₀ q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_Y_eval hu₀t hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq uEmbR u₀ hu₀t hHu]
  have hYv : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map vEmbR TateCurve.Y)) * q ^ n)
      (Blueprint.YAn v₀ q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_Y_eval hv₀ℚ hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq vEmbR v₀ hv₀ℚ hHv]
  have hYw : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1/8 → HasSum
      (fun n => H (PowerSeries.coeff n
        (PowerSeries.map uvEmbR TateCurve.Y)) * q ^ n)
      (Blueprint.YAn (u₀ * v₀) q) := fun q hq0 hq8 => by
    refine (Blueprint.hasSum_Y_eval huvt hq0 (by linarith) (by linarith)
      ).congr_fun fun n => ?_
    rw [hseq uvEmbR (u₀ * v₀) huvt hHuv]
  rw [← sub_eq_zero]
  have hcoeff := Blueprint.coeffs_eq_zero_of_hasSum_punctured
    (fun n => H (PowerSeries.coeff n
      (-(PowerSeries.map uvEmbR TateCurve.Y
          + PowerSeries.map uvEmbR TateCurve.X) *
        (PowerSeries.map uEmbR TateCurve.X
          - PowerSeries.map vEmbR TateCurve.X) -
        ((PowerSeries.map uEmbR TateCurve.Y
            - PowerSeries.map vEmbR TateCurve.Y) *
            (PowerSeries.map uvEmbR TateCurve.X
              - PowerSeries.map uEmbR TateCurve.X) +
          PowerSeries.map uEmbR TateCurve.Y *
            (PowerSeries.map uEmbR TateCurve.X
              - PowerSeries.map vEmbR TateCurve.X)))))
    (1/8) (by norm_num) ?_
  · ext n
    have h1 := congrFun hcoeff n
    simp only [Pi.zero_apply] at h1
    rw [map_zero]
    exact hHinj (by rw [h1, map_zero])
  · intro q hq0 hq8
    have h1 := hasSum_homC_neg H (hasSum_homC_add H (hYw q hq0 hq8)
      (hXw q hq0 hq8))
    have h2 := hasSum_homC_sub H (hXu q hq0 hq8) (hXv q hq0 hq8)
    have h3 := hasSum_homC_sub H (hYu q hq0 hq8) (hYv q hq0 hq8)
    have h4 := hasSum_homC_sub H (hXw q hq0 hq8) (hXu q hq0 hq8)
    have hL := hasSum_homC_mul H h1 h2
    have hR := hasSum_homC_add H (hasSum_homC_mul H h3 h4)
      (hasSum_homC_mul H (hYu q hq0 hq8) h2)
    have hval : -(Blueprint.YAn (u₀ * v₀) q + Blueprint.XAn (u₀ * v₀) q) *
        (Blueprint.XAn u₀ q - Blueprint.XAn v₀ q) -
        ((Blueprint.YAn u₀ q - Blueprint.YAn v₀ q) *
            (Blueprint.XAn (u₀ * v₀) q - Blueprint.XAn u₀ q) +
          Blueprint.YAn u₀ q *
            (Blueprint.XAn u₀ q - Blueprint.XAn v₀ q)) = 0 := by
      have h := Blueprint.analytic_chordY hq0 (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) huv_h
      linear_combination h
    have hsum := hasSum_homC_sub H hL hR
    rw [hval] at hsum
    exact hsum

/-- **The formal chord `X`-identity** (DERIVED from the `ℚ(u)(v)⟦q⟧`
identity by injectivity of the coefficient inclusion). -/
theorem chordX_formal :
    (PowerSeries.map uvSlot XA + PowerSeries.map uSlot XA
        + PowerSeries.map vSlot XA) *
      (PowerSeries.map uSlot XA - PowerSeries.map vSlot XA) ^ 2 =
    (PowerSeries.map uSlot YA - PowerSeries.map vSlot YA) ^ 2 +
      (PowerSeries.map uSlot YA - PowerSeries.map vSlot YA) *
        (PowerSeries.map uSlot XA - PowerSeries.map vSlot XA) := by
  have hinj : Function.Injective
      (PowerSeries.map coeffRing₂ToRatFunc) := by
    intro P Q h
    ext n
    refine coeffRing₂ToRatFunc_injective ?_
    have h1 := congrArg (PowerSeries.coeff n) h
    rwa [PowerSeries.coeff_map, PowerSeries.coeff_map] at h1
  apply hinj
  have hb : ∀ (sl : CoeffRing →+* CoeffRing₂)
      (em : RatFunc ℚ →+* RatFunc (RatFunc ℚ))
      (hcomp : coeffRing₂ToRatFunc.comp sl = em.comp coeffRingToRatFunc)
      (F : PowerSeries CoeffRing),
      (PowerSeries.map coeffRing₂ToRatFunc) ((PowerSeries.map sl) F)
        = PowerSeries.map em (PowerSeries.map coeffRingToRatFunc F) := by
    intro sl em hcomp F
    rw [← RingHom.comp_apply, ← PowerSeries.map_comp, hcomp,
      PowerSeries.map_comp, RingHom.comp_apply]
  simp only [map_add, map_mul, map_pow, map_sub,
    hb uSlot uEmbR coeffRing₂ToRatFunc_uSlot,
    hb vSlot vEmbR coeffRing₂ToRatFunc_vSlot,
    hb uvSlot uvEmbR coeffRing₂ToRatFunc_uvSlot, map_XA, map_YA]
  exact chordX_ratFunc₂

/-- **The formal chord `Y`-identity** (DERIVED from the `ℚ(u)(v)⟦q⟧`
identity by injectivity of the coefficient inclusion). -/
theorem chordY_formal :
    -(PowerSeries.map uvSlot YA + PowerSeries.map uvSlot XA) *
      (PowerSeries.map uSlot XA - PowerSeries.map vSlot XA) =
    (PowerSeries.map uSlot YA - PowerSeries.map vSlot YA) *
        (PowerSeries.map uvSlot XA - PowerSeries.map uSlot XA) +
      PowerSeries.map uSlot YA *
        (PowerSeries.map uSlot XA - PowerSeries.map vSlot XA) := by
  have hinj : Function.Injective
      (PowerSeries.map coeffRing₂ToRatFunc) := by
    intro P Q h
    ext n
    refine coeffRing₂ToRatFunc_injective ?_
    have h1 := congrArg (PowerSeries.coeff n) h
    rwa [PowerSeries.coeff_map, PowerSeries.coeff_map] at h1
  apply hinj
  have hb : ∀ (sl : CoeffRing →+* CoeffRing₂)
      (em : RatFunc ℚ →+* RatFunc (RatFunc ℚ))
      (hcomp : coeffRing₂ToRatFunc.comp sl = em.comp coeffRingToRatFunc)
      (F : PowerSeries CoeffRing),
      (PowerSeries.map coeffRing₂ToRatFunc) ((PowerSeries.map sl) F)
        = PowerSeries.map em (PowerSeries.map coeffRingToRatFunc F) := by
    intro sl em hcomp F
    rw [← RingHom.comp_apply, ← PowerSeries.map_comp, hcomp,
      PowerSeries.map_comp, RingHom.comp_apply]
  simp only [map_add, map_mul, map_neg, map_sub,
    hb uSlot uEmbR coeffRing₂ToRatFunc_uSlot,
    hb vSlot vEmbR coeffRing₂ToRatFunc_vSlot,
    hb uvSlot uvEmbR coeffRing₂ToRatFunc_uvSlot, map_XA, map_YA]
  exact chordY_ratFunc₂

/-- The bivariate evaluation `ℚ[u][v] →+* k` at `(u₀, v₀)` (inner
variable to `u₀`, outer variable to `v₀`). -/
def biEval (u₀ v₀ : k) : Polynomial (Polynomial ℚ) →+* k :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (algebraMap ℚ k) u₀) v₀

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
@[simp]
theorem biEval_C_X (u₀ v₀ : k) :
    biEval u₀ v₀ (Polynomial.C Polynomial.X) = u₀ := by
  simp [biEval]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
@[simp]
theorem biEval_X (u₀ v₀ : k) : biEval u₀ v₀ Polynomial.X = v₀ := by
  simp [biEval]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The localized denominator evaluates to a unit of `k` on the
nondegenerate locus. -/
theorem isUnit_biEval_biDenom (u₀ v₀ : k) (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1)
    (hv0 : v₀ ≠ 0) (hv1 : v₀ ≠ 1) (hne1 : u₀ * v₀ ≠ 1) :
    IsUnit (biEval u₀ v₀ biDenom) := by
  have hC : ∀ p : Polynomial ℚ, biEval u₀ v₀ (Polynomial.C p)
      = Polynomial.eval₂ (algebraMap ℚ k) u₀ p := fun p => by
    simp [biEval]
  refine isUnit_iff_ne_zero.mpr ?_
  rw [show biDenom = Polynomial.C (Polynomial.X * (1 - Polynomial.X)) *
    (Polynomial.X * (1 - Polynomial.X)) *
    (1 - Polynomial.C Polynomial.X * Polynomial.X) from rfl]
  rw [map_mul, map_mul]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · rw [hC]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub,
      Polynomial.eval₂_one, Polynomial.eval₂_X]
    exact mul_ne_zero hu0 (sub_ne_zero.mpr (Ne.symm hu1))
  · rw [map_mul, map_sub, map_one, biEval_X]
    exact mul_ne_zero hv0 (sub_ne_zero.mpr (Ne.symm hv1))
  · rw [map_sub, map_one, map_mul, biEval_C_X, biEval_X]
    exact sub_ne_zero.mpr (Ne.symm hne1)

/-- **Evaluation of the two-variable coefficient ring at a point
`(u₀, v₀)` of `k²`** in the nondegenerate locus. -/
def coeffRingEval₂ (u₀ v₀ : k) (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1)
    (hv0 : v₀ ≠ 0) (hv1 : v₀ ≠ 1) (hne1 : u₀ * v₀ ≠ 1) :
    CoeffRing₂ →+* k :=
  Localization.awayLift (biEval u₀ v₀) _
    (isUnit_biEval_biDenom u₀ v₀ hu0 hu1 hv0 hv1 hne1)

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
@[simp]
theorem coeffRingEval₂_algebraMap (u₀ v₀ : k) (hu0 : u₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (hv0 : v₀ ≠ 0) (hv1 : v₀ ≠ 1) (hne1 : u₀ * v₀ ≠ 1)
    (p : Polynomial (Polynomial ℚ)) :
    coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1
      (algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂ p) =
      biEval u₀ v₀ p := by
  rw [coeffRingEval₂]
  exact IsLocalization.lift_eq _ p

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `u`-slot bridge: evaluating the `u`-slot image at `(u₀, v₀)` is
the one-variable evaluation at `u₀`. -/
theorem coeffRingEval₂_uSlot (u₀ v₀ : k) (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1)
    (hv0 : v₀ ≠ 0) (hv1 : v₀ ≠ 1) (hne1 : u₀ * v₀ ≠ 1) :
    (coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1).comp uSlot =
      coeffRingEval u₀ hu0 hu1 := by
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ))
    (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [show uSlot (algebraMap (Polynomial ℚ) CoeffRing p)
      = slotPolyHom uElt₂ p from IsLocalization.lift_eq _ p,
    coeffRingEval_algebraMap]
  rw [show slotPolyHom uElt₂ p = Polynomial.eval₂
      ((algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂).comp
        ((Polynomial.C).comp (Polynomial.C))) uElt₂ p from rfl,
    Polynomial.hom_eval₂]
  rw [show coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1 uElt₂ = u₀ by
      rw [show uElt₂ = algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
        (Polynomial.C Polynomial.X) from rfl, coeffRingEval₂_algebraMap,
        biEval_C_X]]
  rw [Polynomial.aeval_def]
  congr 1
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, coeffRingEval₂_algebraMap]
  simp [biEval]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `v`-slot bridge. -/
theorem coeffRingEval₂_vSlot (u₀ v₀ : k) (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1)
    (hv0 : v₀ ≠ 0) (hv1 : v₀ ≠ 1) (hne1 : u₀ * v₀ ≠ 1) :
    (coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1).comp vSlot =
      coeffRingEval v₀ hv0 hv1 := by
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ))
    (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [show vSlot (algebraMap (Polynomial ℚ) CoeffRing p)
      = slotPolyHom vElt₂ p from IsLocalization.lift_eq _ p,
    coeffRingEval_algebraMap]
  rw [show slotPolyHom vElt₂ p = Polynomial.eval₂
      ((algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂).comp
        ((Polynomial.C).comp (Polynomial.C))) vElt₂ p from rfl,
    Polynomial.hom_eval₂]
  rw [show coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1 vElt₂ = v₀ by
      rw [show vElt₂ = algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
        Polynomial.X from rfl, coeffRingEval₂_algebraMap, biEval_X]]
  rw [Polynomial.aeval_def]
  congr 1
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, coeffRingEval₂_algebraMap]
  simp [biEval]

omit [TopologicalSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `uv`-slot bridge. -/
theorem coeffRingEval₂_uvSlot (u₀ v₀ : k) (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1)
    (hv0 : v₀ ≠ 0) (hv1 : v₀ ≠ 1) (hne1 : u₀ * v₀ ≠ 1)
    (hw0 : u₀ * v₀ ≠ 0) :
    (coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1).comp uvSlot =
      coeffRingEval (u₀ * v₀) hw0 hne1 := by
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (Polynomial.X * (1 - Polynomial.X) : Polynomial ℚ))
    (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [show uvSlot (algebraMap (Polynomial ℚ) CoeffRing p)
      = slotPolyHom uvElt₂ p from IsLocalization.lift_eq _ p,
    coeffRingEval_algebraMap]
  rw [show slotPolyHom uvElt₂ p = Polynomial.eval₂
      ((algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂).comp
        ((Polynomial.C).comp (Polynomial.C))) uvElt₂ p from rfl,
    Polynomial.hom_eval₂]
  rw [show coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1 uvElt₂ = u₀ * v₀ by
      rw [show uvElt₂ = algebraMap (Polynomial (Polynomial ℚ)) CoeffRing₂
        (Polynomial.C Polynomial.X * Polynomial.X) from rfl,
        coeffRingEval₂_algebraMap, map_mul, biEval_C_X, biEval_X]]
  rw [Polynomial.aeval_def]
  congr 1
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, coeffRingEval₂_algebraMap]
  simp [biEval]

omit [CharZero k] in
/-- Summability of an evaluated sum series, for an arbitrary
coefficient homomorphism. -/
theorem summable_hom_eval_add {R : Type*} [CommRing R] (E : R →+* k)
    (q₀ : k) {F G : PowerSeries R}
    (hF : Summable fun n : ℕ ↦ E (PowerSeries.coeff n F) * q₀ ^ n)
    (hG : Summable fun n : ℕ ↦ E (PowerSeries.coeff n G) * q₀ ^ n) :
    Summable fun n : ℕ ↦ E (PowerSeries.coeff n (F + G)) * q₀ ^ n := by
  refine (hF.add hG).congr fun n ↦ ?_
  rw [map_add, map_add, add_mul]

omit [CharZero k] in
/-- Summability of an evaluated negated series. -/
theorem summable_hom_eval_neg {R : Type*} [CommRing R] (E : R →+* k)
    (q₀ : k) {F : PowerSeries R}
    (hF : Summable fun n : ℕ ↦ E (PowerSeries.coeff n F) * q₀ ^ n) :
    Summable fun n : ℕ ↦ E (PowerSeries.coeff n (-F)) * q₀ ^ n := by
  refine hF.neg.congr fun n ↦ ?_
  rw [map_neg, map_neg, neg_mul]

omit [CharZero k] in
/-- Summability of an evaluated product series (nonarchimedean Cauchy
product), for an arbitrary coefficient homomorphism. -/
theorem summable_hom_eval_mul {R : Type*} [CommRing R] (E : R →+* k)
    (q₀ : k) {F G : PowerSeries R}
    (hF : Summable fun n : ℕ ↦ E (PowerSeries.coeff n F) * q₀ ^ n)
    (hG : Summable fun n : ℕ ↦ E (PowerSeries.coeff n G) * q₀ ^ n) :
    Summable fun n : ℕ ↦ E (PowerSeries.coeff n (F * G)) * q₀ ^ n := by
  have h := summable_sum_mul_antidiagonal_of_summable_mul (A := ℕ)
    (summable_mul_prod hF hG)
  refine h.congr fun n ↦ ?_
  rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hpn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  rw [map_mul, ← hpn, pow_add]
  ring

omit [CharZero k] in
/-- The evaluated sum series sums to the sum of the evaluations. -/
theorem tsum_hom_eval_add {R : Type*} [CommRing R] (E : R →+* k)
    (q₀ : k) {F G : PowerSeries R}
    (hF : Summable fun n : ℕ ↦ E (PowerSeries.coeff n F) * q₀ ^ n)
    (hG : Summable fun n : ℕ ↦ E (PowerSeries.coeff n G) * q₀ ^ n) :
    ∑' n : ℕ, E (PowerSeries.coeff n (F + G)) * q₀ ^ n =
      (∑' n : ℕ, E (PowerSeries.coeff n F) * q₀ ^ n) +
      ∑' n : ℕ, E (PowerSeries.coeff n G) * q₀ ^ n := by
  rw [← hF.tsum_add hG]
  congr 1
  funext n
  rw [map_add, map_add, add_mul]

omit [CharZero k] in
/-- The evaluated negated series sums to the negated evaluation. -/
theorem tsum_hom_eval_neg {R : Type*} [CommRing R] (E : R →+* k)
    (q₀ : k) {F : PowerSeries R} :
    ∑' n : ℕ, E (PowerSeries.coeff n (-F)) * q₀ ^ n =
      -∑' n : ℕ, E (PowerSeries.coeff n F) * q₀ ^ n := by
  rw [← tsum_neg]
  congr 1
  funext n
  rw [map_neg, map_neg, neg_mul]

set_option maxHeartbeats 1000000 in
omit [CharZero k] in
/-- The evaluated product series sums to the product of the evaluations
(nonarchimedean Mertens), for an arbitrary coefficient homomorphism. -/
theorem tsum_hom_eval_mul {R : Type*} [CommRing R] (E : R →+* k)
    (q₀ : k) {F G : PowerSeries R}
    (hF : Summable fun n : ℕ ↦ E (PowerSeries.coeff n F) * q₀ ^ n)
    (hG : Summable fun n : ℕ ↦ E (PowerSeries.coeff n G) * q₀ ^ n) :
    ∑' n : ℕ, E (PowerSeries.coeff n (F * G)) * q₀ ^ n =
      (∑' n : ℕ, E (PowerSeries.coeff n F) * q₀ ^ n) *
      ∑' n : ℕ, E (PowerSeries.coeff n G) * q₀ ^ n := by
  set f : ℕ → k := fun n ↦ E (PowerSeries.coeff n F) * q₀ ^ n with hfdef
  set g : ℕ → k := fun n ↦ E (PowerSeries.coeff n G) * q₀ ^ n with hgdef
  have key := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal (A := ℕ)
    hF hG (summable_mul_prod hF hG)
  rw [key]
  congr 1
  funext n
  rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hpn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  rw [hfdef, hgdef, map_mul, ← hpn, pow_add]
  ring

/-- **Two-variable evaluation transport for the chord `X`-identity**
(PROVEN): the evaluation `CoeffRing₂ → k` at `(u₀, v₀)` sends q-power
series sums to the corresponding `evalA`-sums along the three slot
bridges, and the evaluated identity follows from the formal one by the
nonarchimedean Cauchy product. -/
theorem evalA_chordX_of_formal
    (hformal : (PowerSeries.map uvSlot XA + PowerSeries.map uSlot XA
        + PowerSeries.map vSlot XA) *
      (PowerSeries.map uSlot XA - PowerSeries.map vSlot XA) ^ 2 =
    (PowerSeries.map uSlot YA - PowerSeries.map vSlot YA) ^ 2 +
      (PowerSeries.map uSlot YA - PowerSeries.map vSlot YA) *
        (PowerSeries.map uSlot XA - PowerSeries.map vSlot XA))
    (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (hv1 : v₀ ≠ 1)
    (hne1 : u₀ * v₀ ≠ 1) (hw0 : u₀ * v₀ ≠ 0)
    (hXu : Summable fun n : ℕ ↦
      coeffRingEval u₀ hu0 hu1 (PowerSeries.coeff n XA) * q₀ ^ n)
    (hXv : Summable fun n : ℕ ↦
      coeffRingEval v₀ hv0 hv1 (PowerSeries.coeff n XA) * q₀ ^ n)
    (hXw : Summable fun n : ℕ ↦
      coeffRingEval (u₀ * v₀) hw0 hne1 (PowerSeries.coeff n XA) * q₀ ^ n)
    (hYu : Summable fun n : ℕ ↦
      coeffRingEval u₀ hu0 hu1 (PowerSeries.coeff n YA) * q₀ ^ n)
    (hYv : Summable fun n : ℕ ↦
      coeffRingEval v₀ hv0 hv1 (PowerSeries.coeff n YA) * q₀ ^ n) :
    (evalA (u₀ * v₀) q₀ hw0 hne1 XA + evalA u₀ q₀ hu0 hu1 XA
        + evalA v₀ q₀ hv0 hv1 XA) *
        (evalA u₀ q₀ hu0 hu1 XA - evalA v₀ q₀ hv0 hv1 XA) ^ 2 =
      (evalA u₀ q₀ hu0 hu1 YA - evalA v₀ q₀ hv0 hv1 YA) ^ 2 +
        (evalA u₀ q₀ hu0 hu1 YA - evalA v₀ q₀ hv0 hv1 YA) *
          (evalA u₀ q₀ hu0 hu1 XA - evalA v₀ q₀ hv0 hv1 XA) := by
  -- the slot bridges identify the evaluated coefficient sequences of the
  -- slot images with the one-variable evaluation sequences
  have hbu := coeffRingEval₂_uSlot u₀ v₀ hu0 hu1 hv0 hv1 hne1
  have hbv := coeffRingEval₂_vSlot u₀ v₀ hu0 hu1 hv0 hv1 hne1
  have hbw := coeffRingEval₂_uvSlot u₀ v₀ hu0 hu1 hv0 hv1 hne1 hw0
  have hsequ : ∀ (F : PowerSeries CoeffRing) (n : ℕ),
      coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1
        (PowerSeries.coeff n (PowerSeries.map uSlot F)) =
      coeffRingEval u₀ hu0 hu1 (PowerSeries.coeff n F) := fun F n => by
    rw [PowerSeries.coeff_map, ← RingHom.comp_apply, hbu]
  have hseqv : ∀ (F : PowerSeries CoeffRing) (n : ℕ),
      coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1
        (PowerSeries.coeff n (PowerSeries.map vSlot F)) =
      coeffRingEval v₀ hv0 hv1 (PowerSeries.coeff n F) := fun F n => by
    rw [PowerSeries.coeff_map, ← RingHom.comp_apply, hbv]
  have hseqw : ∀ (F : PowerSeries CoeffRing) (n : ℕ),
      coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1
        (PowerSeries.coeff n (PowerSeries.map uvSlot F)) =
      coeffRingEval (u₀ * v₀) hw0 hne1 (PowerSeries.coeff n F) :=
    fun F n => by
    rw [PowerSeries.coeff_map, ← RingHom.comp_apply, hbw]
  set E₂ := coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1 with hE₂def
  set uX := PowerSeries.map uSlot XA with huX
  set vX := PowerSeries.map vSlot XA with hvX
  set wX := PowerSeries.map uvSlot XA with hwX
  set uY := PowerSeries.map uSlot YA with huY
  set vY := PowerSeries.map vSlot YA with hvY
  -- transported to the two-variable evaluation
  have sXu : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n uX) * q₀ ^ n :=
    hXu.congr fun n => by rw [hsequ]
  have sXv : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n vX) * q₀ ^ n :=
    hXv.congr fun n => by rw [hseqv]
  have sXw : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n wX) * q₀ ^ n :=
    hXw.congr fun n => by rw [hseqw]
  have sYu : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n uY) * q₀ ^ n :=
    hYu.congr fun n => by rw [hsequ]
  have sYv : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n vY) * q₀ ^ n :=
    hYv.congr fun n => by rw [hseqv]
  -- the five `evalA`-values as two-variable sums
  have hvXu : evalA u₀ q₀ hu0 hu1 XA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n :=
    tsum_congr fun n => by rw [hsequ]
  have hvXv : evalA v₀ q₀ hv0 hv1 XA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n vX) * q₀ ^ n :=
    tsum_congr fun n => by rw [hseqv]
  have hvXw : evalA (u₀ * v₀) q₀ hw0 hne1 XA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n wX) * q₀ ^ n :=
    tsum_congr fun n => by rw [hseqw]
  have hvYu : evalA u₀ q₀ hu0 hu1 YA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n uY) * q₀ ^ n :=
    tsum_congr fun n => by rw [hsequ]
  have hvYv : evalA v₀ q₀ hv0 hv1 YA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n vY) * q₀ ^ n :=
    tsum_congr fun n => by rw [hseqv]
  rw [hvXu, hvXv, hvXw, hvYu, hvYv]
  -- assemble both sides as single evaluated series
  have sXsub : Summable fun n : ℕ ↦
      E₂ (PowerSeries.coeff n (uX - vX)) * q₀ ^ n := by
    rw [sub_eq_add_neg]
    exact summable_hom_eval_add E₂ q₀ sXu (summable_hom_eval_neg E₂ q₀ sXv)
  have sYsub : Summable fun n : ℕ ↦
      E₂ (PowerSeries.coeff n (uY - vY)) * q₀ ^ n := by
    rw [sub_eq_add_neg]
    exact summable_hom_eval_add E₂ q₀ sYu (summable_hom_eval_neg E₂ q₀ sYv)
  have sadd3 : Summable fun n : ℕ ↦
      E₂ (PowerSeries.coeff n (wX + uX + vX)) * q₀ ^ n :=
    summable_hom_eval_add E₂ q₀ (summable_hom_eval_add E₂ q₀ sXw sXu) sXv
  have tXsub : ∑' n : ℕ, E₂ (PowerSeries.coeff n (uX - vX)) * q₀ ^ n
      = (∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n) -
        ∑' n : ℕ, E₂ (PowerSeries.coeff n vX) * q₀ ^ n := by
    rw [sub_eq_add_neg,
      tsum_hom_eval_add E₂ q₀ sXu (summable_hom_eval_neg E₂ q₀ sXv),
      tsum_hom_eval_neg E₂ q₀, ← sub_eq_add_neg]
  have tYsub : ∑' n : ℕ, E₂ (PowerSeries.coeff n (uY - vY)) * q₀ ^ n
      = (∑' n : ℕ, E₂ (PowerSeries.coeff n uY) * q₀ ^ n) -
        ∑' n : ℕ, E₂ (PowerSeries.coeff n vY) * q₀ ^ n := by
    rw [sub_eq_add_neg,
      tsum_hom_eval_add E₂ q₀ sYu (summable_hom_eval_neg E₂ q₀ sYv),
      tsum_hom_eval_neg E₂ q₀, ← sub_eq_add_neg]
  have tadd3 : ∑' n : ℕ, E₂ (PowerSeries.coeff n (wX + uX + vX)) * q₀ ^ n
      = (∑' n : ℕ, E₂ (PowerSeries.coeff n wX) * q₀ ^ n) +
        (∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n) +
        ∑' n : ℕ, E₂ (PowerSeries.coeff n vX) * q₀ ^ n := by
    rw [tsum_hom_eval_add E₂ q₀ (summable_hom_eval_add E₂ q₀ sXw sXu) sXv,
      tsum_hom_eval_add E₂ q₀ sXw sXu]
  -- the product-normal form of the formal identity
  have hF' : (wX + uX + vX) * ((uX - vX) * (uX - vX))
      = (uY - vY) * (uY - vY) + (uY - vY) * (uX - vX) := by
    linear_combination hformal
  calc (∑' n : ℕ, E₂ (PowerSeries.coeff n wX) * q₀ ^ n +
          ∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n +
          ∑' n : ℕ, E₂ (PowerSeries.coeff n vX) * q₀ ^ n) *
        (∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n -
          ∑' n : ℕ, E₂ (PowerSeries.coeff n vX) * q₀ ^ n) ^ 2
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n
          ((wX + uX + vX) * ((uX - vX) * (uX - vX)))) * q₀ ^ n := by
        rw [tsum_hom_eval_mul E₂ q₀ sadd3
            (summable_hom_eval_mul E₂ q₀ sXsub sXsub),
          tsum_hom_eval_mul E₂ q₀ sXsub sXsub, tadd3, tXsub]
        ring
    _ = ∑' n : ℕ, E₂ (PowerSeries.coeff n
          ((uY - vY) * (uY - vY) + (uY - vY) * (uX - vX))) * q₀ ^ n := by
        rw [hF']
    _ = (∑' n : ℕ, E₂ (PowerSeries.coeff n uY) * q₀ ^ n -
          ∑' n : ℕ, E₂ (PowerSeries.coeff n vY) * q₀ ^ n) ^ 2 +
        (∑' n : ℕ, E₂ (PowerSeries.coeff n uY) * q₀ ^ n -
          ∑' n : ℕ, E₂ (PowerSeries.coeff n vY) * q₀ ^ n) *
        (∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n -
          ∑' n : ℕ, E₂ (PowerSeries.coeff n vX) * q₀ ^ n) := by
        rw [tsum_hom_eval_add E₂ q₀
            (summable_hom_eval_mul E₂ q₀ sYsub sYsub)
            (summable_hom_eval_mul E₂ q₀ sYsub sXsub),
          tsum_hom_eval_mul E₂ q₀ sYsub sYsub,
          tsum_hom_eval_mul E₂ q₀ sYsub sXsub, tYsub, tXsub]
        ring

/-- **Two-variable evaluation transport for the chord `Y`-identity**
(PROVEN), mirroring `evalA_chordX_of_formal`. -/
theorem evalA_chordY_of_formal
    (hformal : -(PowerSeries.map uvSlot YA + PowerSeries.map uvSlot XA) *
      (PowerSeries.map uSlot XA - PowerSeries.map vSlot XA) =
    (PowerSeries.map uSlot YA - PowerSeries.map vSlot YA) *
        (PowerSeries.map uvSlot XA - PowerSeries.map uSlot XA) +
      PowerSeries.map uSlot YA *
        (PowerSeries.map uSlot XA - PowerSeries.map vSlot XA))
    (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (hv1 : v₀ ≠ 1)
    (hne1 : u₀ * v₀ ≠ 1) (hw0 : u₀ * v₀ ≠ 0)
    (hXu : Summable fun n : ℕ ↦
      coeffRingEval u₀ hu0 hu1 (PowerSeries.coeff n XA) * q₀ ^ n)
    (hXv : Summable fun n : ℕ ↦
      coeffRingEval v₀ hv0 hv1 (PowerSeries.coeff n XA) * q₀ ^ n)
    (hXw : Summable fun n : ℕ ↦
      coeffRingEval (u₀ * v₀) hw0 hne1 (PowerSeries.coeff n XA) * q₀ ^ n)
    (hYu : Summable fun n : ℕ ↦
      coeffRingEval u₀ hu0 hu1 (PowerSeries.coeff n YA) * q₀ ^ n)
    (hYv : Summable fun n : ℕ ↦
      coeffRingEval v₀ hv0 hv1 (PowerSeries.coeff n YA) * q₀ ^ n)
    (hYw : Summable fun n : ℕ ↦
      coeffRingEval (u₀ * v₀) hw0 hne1 (PowerSeries.coeff n YA) * q₀ ^ n) :
    -(evalA (u₀ * v₀) q₀ hw0 hne1 YA + evalA (u₀ * v₀) q₀ hw0 hne1 XA) *
        (evalA u₀ q₀ hu0 hu1 XA - evalA v₀ q₀ hv0 hv1 XA) =
      (evalA u₀ q₀ hu0 hu1 YA - evalA v₀ q₀ hv0 hv1 YA) *
          (evalA (u₀ * v₀) q₀ hw0 hne1 XA - evalA u₀ q₀ hu0 hu1 XA) +
        evalA u₀ q₀ hu0 hu1 YA *
          (evalA u₀ q₀ hu0 hu1 XA - evalA v₀ q₀ hv0 hv1 XA) := by
  -- the slot bridges identify the evaluated coefficient sequences of the
  -- slot images with the one-variable evaluation sequences
  have hbu := coeffRingEval₂_uSlot u₀ v₀ hu0 hu1 hv0 hv1 hne1
  have hbv := coeffRingEval₂_vSlot u₀ v₀ hu0 hu1 hv0 hv1 hne1
  have hbw := coeffRingEval₂_uvSlot u₀ v₀ hu0 hu1 hv0 hv1 hne1 hw0
  have hsequ : ∀ (F : PowerSeries CoeffRing) (n : ℕ),
      coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1
        (PowerSeries.coeff n (PowerSeries.map uSlot F)) =
      coeffRingEval u₀ hu0 hu1 (PowerSeries.coeff n F) := fun F n => by
    rw [PowerSeries.coeff_map, ← RingHom.comp_apply, hbu]
  have hseqv : ∀ (F : PowerSeries CoeffRing) (n : ℕ),
      coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1
        (PowerSeries.coeff n (PowerSeries.map vSlot F)) =
      coeffRingEval v₀ hv0 hv1 (PowerSeries.coeff n F) := fun F n => by
    rw [PowerSeries.coeff_map, ← RingHom.comp_apply, hbv]
  have hseqw : ∀ (F : PowerSeries CoeffRing) (n : ℕ),
      coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1
        (PowerSeries.coeff n (PowerSeries.map uvSlot F)) =
      coeffRingEval (u₀ * v₀) hw0 hne1 (PowerSeries.coeff n F) :=
    fun F n => by
    rw [PowerSeries.coeff_map, ← RingHom.comp_apply, hbw]
  set E₂ := coeffRingEval₂ u₀ v₀ hu0 hu1 hv0 hv1 hne1 with hE₂def
  set uX := PowerSeries.map uSlot XA with huX
  set vX := PowerSeries.map vSlot XA with hvX
  set wX := PowerSeries.map uvSlot XA with hwX
  set uY := PowerSeries.map uSlot YA with huY
  set vY := PowerSeries.map vSlot YA with hvY
  set wY := PowerSeries.map uvSlot YA with hwY
  have sXu : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n uX) * q₀ ^ n :=
    hXu.congr fun n => by rw [hsequ]
  have sXv : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n vX) * q₀ ^ n :=
    hXv.congr fun n => by rw [hseqv]
  have sXw : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n wX) * q₀ ^ n :=
    hXw.congr fun n => by rw [hseqw]
  have sYu : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n uY) * q₀ ^ n :=
    hYu.congr fun n => by rw [hsequ]
  have sYv : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n vY) * q₀ ^ n :=
    hYv.congr fun n => by rw [hseqv]
  have sYw : Summable fun n : ℕ ↦ E₂ (PowerSeries.coeff n wY) * q₀ ^ n :=
    hYw.congr fun n => by rw [hseqw]
  have hvXu : evalA u₀ q₀ hu0 hu1 XA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n :=
    tsum_congr fun n => by rw [hsequ]
  have hvXv : evalA v₀ q₀ hv0 hv1 XA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n vX) * q₀ ^ n :=
    tsum_congr fun n => by rw [hseqv]
  have hvXw : evalA (u₀ * v₀) q₀ hw0 hne1 XA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n wX) * q₀ ^ n :=
    tsum_congr fun n => by rw [hseqw]
  have hvYu : evalA u₀ q₀ hu0 hu1 YA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n uY) * q₀ ^ n :=
    tsum_congr fun n => by rw [hsequ]
  have hvYv : evalA v₀ q₀ hv0 hv1 YA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n vY) * q₀ ^ n :=
    tsum_congr fun n => by rw [hseqv]
  have hvYw : evalA (u₀ * v₀) q₀ hw0 hne1 YA
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n wY) * q₀ ^ n :=
    tsum_congr fun n => by rw [hseqw]
  rw [hvXu, hvXv, hvXw, hvYu, hvYv, hvYw]
  have sXsub : Summable fun n : ℕ ↦
      E₂ (PowerSeries.coeff n (uX - vX)) * q₀ ^ n := by
    rw [sub_eq_add_neg]
    exact summable_hom_eval_add E₂ q₀ sXu (summable_hom_eval_neg E₂ q₀ sXv)
  have sYsub : Summable fun n : ℕ ↦
      E₂ (PowerSeries.coeff n (uY - vY)) * q₀ ^ n := by
    rw [sub_eq_add_neg]
    exact summable_hom_eval_add E₂ q₀ sYu (summable_hom_eval_neg E₂ q₀ sYv)
  have sWXsub : Summable fun n : ℕ ↦
      E₂ (PowerSeries.coeff n (wX - uX)) * q₀ ^ n := by
    rw [sub_eq_add_neg]
    exact summable_hom_eval_add E₂ q₀ sXw (summable_hom_eval_neg E₂ q₀ sXu)
  have sWadd : Summable fun n : ℕ ↦
      E₂ (PowerSeries.coeff n (wY + wX)) * q₀ ^ n :=
    summable_hom_eval_add E₂ q₀ sYw sXw
  have tXsub : ∑' n : ℕ, E₂ (PowerSeries.coeff n (uX - vX)) * q₀ ^ n
      = (∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n) -
        ∑' n : ℕ, E₂ (PowerSeries.coeff n vX) * q₀ ^ n := by
    rw [sub_eq_add_neg,
      tsum_hom_eval_add E₂ q₀ sXu (summable_hom_eval_neg E₂ q₀ sXv),
      tsum_hom_eval_neg E₂ q₀, ← sub_eq_add_neg]
  have tYsub : ∑' n : ℕ, E₂ (PowerSeries.coeff n (uY - vY)) * q₀ ^ n
      = (∑' n : ℕ, E₂ (PowerSeries.coeff n uY) * q₀ ^ n) -
        ∑' n : ℕ, E₂ (PowerSeries.coeff n vY) * q₀ ^ n := by
    rw [sub_eq_add_neg,
      tsum_hom_eval_add E₂ q₀ sYu (summable_hom_eval_neg E₂ q₀ sYv),
      tsum_hom_eval_neg E₂ q₀, ← sub_eq_add_neg]
  have tWXsub : ∑' n : ℕ, E₂ (PowerSeries.coeff n (wX - uX)) * q₀ ^ n
      = (∑' n : ℕ, E₂ (PowerSeries.coeff n wX) * q₀ ^ n) -
        ∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n := by
    rw [sub_eq_add_neg,
      tsum_hom_eval_add E₂ q₀ sXw (summable_hom_eval_neg E₂ q₀ sXu),
      tsum_hom_eval_neg E₂ q₀, ← sub_eq_add_neg]
  have tWadd : ∑' n : ℕ, E₂ (PowerSeries.coeff n (wY + wX)) * q₀ ^ n
      = (∑' n : ℕ, E₂ (PowerSeries.coeff n wY) * q₀ ^ n) +
        ∑' n : ℕ, E₂ (PowerSeries.coeff n wX) * q₀ ^ n :=
    tsum_hom_eval_add E₂ q₀ sYw sXw
  have hF' : (-(wY + wX)) * (uX - vX)
      = (uY - vY) * (wX - uX) + uY * (uX - vX) := by
    linear_combination hformal
  calc -(∑' n : ℕ, E₂ (PowerSeries.coeff n wY) * q₀ ^ n +
          ∑' n : ℕ, E₂ (PowerSeries.coeff n wX) * q₀ ^ n) *
        (∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n -
          ∑' n : ℕ, E₂ (PowerSeries.coeff n vX) * q₀ ^ n)
      = ∑' n : ℕ, E₂ (PowerSeries.coeff n
          ((-(wY + wX)) * (uX - vX))) * q₀ ^ n := by
        rw [tsum_hom_eval_mul E₂ q₀
            (summable_hom_eval_neg E₂ q₀ sWadd) sXsub,
          tsum_hom_eval_neg E₂ q₀, tWadd, tXsub]
    _ = ∑' n : ℕ, E₂ (PowerSeries.coeff n
          ((uY - vY) * (wX - uX) + uY * (uX - vX))) * q₀ ^ n := by
        rw [hF']
    _ = (∑' n : ℕ, E₂ (PowerSeries.coeff n uY) * q₀ ^ n -
          ∑' n : ℕ, E₂ (PowerSeries.coeff n vY) * q₀ ^ n) *
        (∑' n : ℕ, E₂ (PowerSeries.coeff n wX) * q₀ ^ n -
          ∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n) +
        (∑' n : ℕ, E₂ (PowerSeries.coeff n uY) * q₀ ^ n) *
        (∑' n : ℕ, E₂ (PowerSeries.coeff n uX) * q₀ ^ n -
          ∑' n : ℕ, E₂ (PowerSeries.coeff n vX) * q₀ ^ n) := by
        rw [tsum_hom_eval_add E₂ q₀
            (summable_hom_eval_mul E₂ q₀ sYsub sWXsub)
            (summable_hom_eval_mul E₂ q₀ sYu sXsub),
          tsum_hom_eval_mul E₂ q₀ sYsub sWXsub,
          tsum_hom_eval_mul E₂ q₀ sYu sXsub, tYsub, tWXsub, tXsub]

/-- **The `evalA`-level chord `X`-identity** (DERIVED from the formal
identity and the evaluation transport): for all three parameters in the fundamental annulus,
the chord identity between the `evalA`-sums of the formal `XA`/`YA`.
This is the `k`-evaluation of the two-variable formal chord identity in
`ℚ(u)(v)⟦q⟧`, which descends from `analytic_chordX` of
`TateCurveConstruction.lean`. -/
theorem evalA_chordX (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0) (_hq0 : q₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (hv1 : v₀ ≠ 1)
    (_hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1)
    (hne1 : u₀ * v₀ ≠ 1) (_hneq : u₀ * v₀ ≠ q₀) :
    ∀ (hw0 : u₀ * v₀ ≠ 0) (_hwin : valuation k q₀ < valuation k (u₀ * v₀))
      (_hwhigh : valuation k (u₀ * v₀) ≤ 1),
    (evalA (u₀ * v₀) q₀ hw0 hne1 XA + evalA u₀ q₀ hu0 hu1 XA
        + evalA v₀ q₀ hv0 hv1 XA) *
        (evalA u₀ q₀ hu0 hu1 XA - evalA v₀ q₀ hv0 hv1 XA) ^ 2 =
      (evalA u₀ q₀ hu0 hu1 YA - evalA v₀ q₀ hv0 hv1 YA) ^ 2 +
        (evalA u₀ q₀ hu0 hu1 YA - evalA v₀ q₀ hv0 hv1 YA) *
          (evalA u₀ q₀ hu0 hu1 XA - evalA v₀ q₀ hv0 hv1 XA) :=
  fun hw0 hwin hwhigh =>
    evalA_chordX_of_formal chordX_formal u₀ v₀ q₀ hu0 hv0 hu1 hv1 hne1 hw0
      (summable_evalA_XA u₀ q₀ hu0 hu1 huhigh hulow)
      (summable_evalA_XA v₀ q₀ hv0 hv1 hvhigh hvlow)
      (summable_evalA_XA (u₀ * v₀) q₀ hw0 hne1 hwhigh hwin)
      (summable_evalA_YA u₀ q₀ hu0 hu1 huhigh hulow)
      (summable_evalA_YA v₀ q₀ hv0 hv1 hvhigh hvlow)

/-- **The cleared chord `X`-identity, fundamental-window case** (DERIVED
from the `evalA`-level identity through the bilateral bridges): all
three parameters lie in the fundamental annulus, so all six bilateral
values are `evalA`-sums. -/
theorem bilateral_chordX_cleared_window (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0) (hq0 : q₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (hv1 : v₀ ≠ 1)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1)
    (hne1 : u₀ * v₀ ≠ 1) (hneq : u₀ * v₀ ≠ q₀) :
    valuation k q₀ < valuation k (u₀ * v₀) →
    (bilateralX (u₀ * v₀) q₀ + bilateralX u₀ q₀ + bilateralX v₀ q₀) *
        (bilateralX u₀ q₀ - bilateralX v₀ q₀) ^ 2 =
      (bilateralY u₀ q₀ - bilateralY v₀ q₀) ^ 2 +
        (bilateralY u₀ q₀ - bilateralY v₀ q₀) *
          (bilateralX u₀ q₀ - bilateralX v₀ q₀) := by
  intro hwin
  have hw0 : u₀ * v₀ ≠ 0 := mul_ne_zero hu0 hv0
  have hwhigh : valuation k (u₀ * v₀) ≤ 1 := by
    rw [map_mul]
    calc valuation k u₀ * valuation k v₀ ≤ 1 * valuation k v₀ :=
          mul_le_mul_left huhigh _
      _ = valuation k v₀ := one_mul _
      _ ≤ 1 := hvhigh
  rw [← evalA_XA_eq_bilateralX u₀ q₀ hu0 hu1 huhigh hq1 hulow,
    ← evalA_XA_eq_bilateralX v₀ q₀ hv0 hv1 hvhigh hq1 hvlow,
    ← evalA_XA_eq_bilateralX (u₀ * v₀) q₀ hw0 hne1 hwhigh hq1 hwin,
    ← evalA_YA_eq_bilateralY u₀ q₀ hu0 hu1 huhigh hq1 hulow,
    ← evalA_YA_eq_bilateralY v₀ q₀ hv0 hv1 hvhigh hq1 hvlow]
  exact evalA_chordX u₀ v₀ q₀ hu0 hv0 hq0 hu1 hv1 hq1 hulow huhigh hvlow
    hvhigh hne1 hneq hw0 hwin hwhigh

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- **Extended-annulus coefficient bound for `XA`**: for `1 < |u₀|` the
`n`-th evaluated coefficient has valuation at most `|u₀|ⁿ` (now the
`u₀ᵈ` summand dominates). -/
theorem valuation_coeffRingEval_XA_le_ext (u₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) (hu : 1 < valuation k u₀) {n : ℕ} (hn : n ≠ 0) :
    valuation k (coeffRingEval u₀ h0 h1 (PowerSeries.coeff n XA)) ≤
      (valuation k u₀) ^ n := by
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  have hone : (1 : ValueGroupWithZero k) ≤ (valuation k u₀) ^ n :=
    one_le_pow₀ hu.le
  rw [coeffRingEval_coeff_XA u₀ h0 h1 hn]
  refine Valuation.map_sum_le _ fun d hd ↦ ?_
  have hdn : d ≤ n := Nat.divisor_le hd
  rw [map_mul]
  have hd1 : valuation k (d : k) ≤ 1 := by
    have h := valuation_intCast_le_one (R := k) d
    simpa using h
  have hsum : valuation k (u₀ ^ d + u₀⁻¹ ^ d - 2) ≤
      (valuation k u₀) ^ n := by
    have ha : valuation k (u₀ ^ d) ≤ (valuation k u₀) ^ n := by
      rw [map_pow]
      exact pow_le_pow_right' hu.le hdn
    have hb : valuation k (u₀⁻¹ ^ d) ≤ (valuation k u₀) ^ n := by
      rw [map_pow, map_inv₀]
      refine le_trans ?_ hone
      refine pow_le_one₀ zero_le ?_
      rw [inv_le_one₀ (zero_lt_iff.mpr hv0)]
      exact hu.le
    have hc : valuation k (2 : k) ≤ (valuation k u₀) ^ n := by
      refine le_trans ?_ hone
      have h := valuation_intCast_le_one (R := k) 2
      simpa using h
    calc valuation k (u₀ ^ d + u₀⁻¹ ^ d - 2)
        ≤ max (valuation k (u₀ ^ d + u₀⁻¹ ^ d)) (valuation k (2 : k)) :=
          Valuation.map_sub _ _ _
      _ ≤ (valuation k u₀) ^ n := by
          refine max_le ?_ hc
          exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)
  calc valuation k ((d : k)) * valuation k (u₀ ^ d + u₀⁻¹ ^ d - 2)
      ≤ 1 * (valuation k u₀) ^ n := mul_le_mul' hd1 hsum
    _ = (valuation k u₀) ^ n := one_mul _

/-- **Extended-annulus summability for `XA`** (PROVEN): the evaluated
series also converges on the upper half of the extended annulus
`1 < |u₀| < |q₀|⁻¹` — the coefficient bound is `|u₀|ⁿ`, beaten by
`|q₀u₀| < 1`. -/
theorem summable_evalA_XA_ext (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : 1 < valuation k u₀) (hqu : valuation k (q₀ * u₀) < 1) :
    Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n XA) * q₀ ^ n := by
  rw [← summable_nat_add_iff 1]
  refine summable_of_valuation_le_pow hqu (fun n ↦ n + 1)
    (fun N ↦ (Set.finite_Iio N).subset fun i hi ↦ Set.mem_Iio.mpr
      (lt_trans (Nat.lt_succ_self i) hi)) (fun n ↦ ?_)
  rw [map_mul, map_pow]
  have hb := valuation_coeffRingEval_XA_le_ext u₀ h0 h1 hu
    (Nat.succ_ne_zero n)
  calc valuation k (coeffRingEval u₀ h0 h1
        (PowerSeries.coeff (n + 1) XA)) * valuation k q₀ ^ (n + 1)
      ≤ (valuation k u₀) ^ (n + 1) * valuation k q₀ ^ (n + 1) :=
        mul_le_mul_left hb _
    _ = valuation k (q₀ * u₀) ^ (n + 1) := by
        rw [map_mul, mul_pow]
        exact mul_comm _ _

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- **Extended-annulus coefficient bound for `YA`**. -/
theorem valuation_coeffRingEval_YA_le_ext (u₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) (hu : 1 < valuation k u₀) {n : ℕ} (hn : n ≠ 0) :
    valuation k (coeffRingEval u₀ h0 h1 (PowerSeries.coeff n YA)) ≤
      (valuation k u₀) ^ n := by
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  have hone : (1 : ValueGroupWithZero k) ≤ (valuation k u₀) ^ n :=
    one_le_pow₀ hu.le
  have hnat : ∀ m : ℕ, valuation k (m : k) ≤ 1 := by
    intro m
    have h := valuation_intCast_le_one (R := k) m
    simpa using h
  rw [coeffRingEval_coeff_YA u₀ h0 h1 hn]
  refine Valuation.map_sum_le _ fun d hd ↦ ?_
  have hdn : d ≤ n := Nat.divisor_le hd
  have ha : valuation k ((d.choose 2 : k) * u₀ ^ d) ≤
      (valuation k u₀) ^ n := by
    rw [map_mul, map_pow]
    calc valuation k ((d.choose 2 : k)) * valuation k u₀ ^ d
        ≤ 1 * (valuation k u₀) ^ n :=
          mul_le_mul' (hnat _) (pow_le_pow_right' hu.le hdn)
      _ = (valuation k u₀) ^ n := one_mul _
  have hb : valuation k (((d + 1).choose 2 : k) * u₀⁻¹ ^ d) ≤
      (valuation k u₀) ^ n := by
    rw [map_mul, map_pow, map_inv₀]
    have hpow : ((valuation k u₀)⁻¹) ^ d ≤ (valuation k u₀) ^ n := by
      refine le_trans ?_ hone
      refine pow_le_one₀ zero_le ?_
      rw [inv_le_one₀ (zero_lt_iff.mpr hv0)]
      exact hu.le
    calc valuation k (((d + 1).choose 2 : k)) * ((valuation k u₀)⁻¹) ^ d
        ≤ 1 * (valuation k u₀) ^ n := mul_le_mul' (hnat _) hpow
      _ = (valuation k u₀) ^ n := one_mul _
  have hc : valuation k ((d : k)) ≤ (valuation k u₀) ^ n :=
    le_trans (hnat d) hone
  calc valuation k ((d.choose 2 : k) * u₀ ^ d -
        ((d + 1).choose 2 : k) * u₀⁻¹ ^ d + (d : k))
      ≤ max (valuation k ((d.choose 2 : k) * u₀ ^ d -
          ((d + 1).choose 2 : k) * u₀⁻¹ ^ d)) (valuation k ((d : k))) :=
        Valuation.map_add _ _ _
    _ ≤ (valuation k u₀) ^ n := by
        refine max_le ?_ hc
        exact le_trans (Valuation.map_sub _ _ _) (max_le ha hb)

/-- **Extended-annulus summability for `YA`** (PROVEN). -/
theorem summable_evalA_YA_ext (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (hu : 1 < valuation k u₀) (hqu : valuation k (q₀ * u₀) < 1) :
    Summable fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff n YA) * q₀ ^ n := by
  rw [← summable_nat_add_iff 1]
  refine summable_of_valuation_le_pow hqu (fun n ↦ n + 1)
    (fun N ↦ (Set.finite_Iio N).subset fun i hi ↦ Set.mem_Iio.mpr
      (lt_trans (Nat.lt_succ_self i) hi)) (fun n ↦ ?_)
  rw [map_mul, map_pow]
  have hb := valuation_coeffRingEval_YA_le_ext u₀ h0 h1 hu
    (Nat.succ_ne_zero n)
  calc valuation k (coeffRingEval u₀ h0 h1
        (PowerSeries.coeff (n + 1) YA)) * valuation k q₀ ^ (n + 1)
      ≤ (valuation k u₀) ^ (n + 1) * valuation k q₀ ^ (n + 1) :=
        mul_le_mul_left hb _
    _ = valuation k (q₀ * u₀) ^ (n + 1) := by
        rw [map_mul, mul_pow]
        exact mul_comm _ _

/-- **Extended-annulus bilateral bridge for `X`** (PROVEN — the window
proof only ever used the two Lambert conditions `|q₀u₀| < 1` and
`|q₀u₀⁻¹| < 1`, both of which hold on the upper extended annulus). -/
theorem evalA_XA_eq_bilateralX_ext (u₀ q₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) (hq1 : valuation k q₀ < 1)
    (hu : 1 < valuation k u₀) (hqu : valuation k (q₀ * u₀) < 1) :
    evalA u₀ q₀ h0 h1 XA = bilateralX u₀ q₀ := by
  unfold bilateralX
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  have hquinv : valuation k (q₀ * u₀⁻¹) < 1 := by
    rw [map_mul, map_inv₀]
    calc valuation k q₀ * (valuation k u₀)⁻¹
        ≤ valuation k q₀ * 1 := by
          have hinv : (valuation k u₀)⁻¹ ≤ 1 := by
            rw [inv_le_one₀ (zero_lt_iff.mpr hv0)]
            exact hu.le
          exact mul_le_mul_right hinv _
      _ = valuation k q₀ := mul_one _
      _ < 1 := hq1
  have hSu := hasSum_lambert_side' u₀ q₀ hq1 hqu
  have hSuinv := hasSum_lambert_side' u₀⁻¹ q₀ hq1 hquinv
  have hSσ := (summable_sigma_one_nonarch q₀ hq1).hasSum
  have htail : HasSum (fun N : ℕ+ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff (N : ℕ) XA) *
        q₀ ^ (N : ℕ))
      ((∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀ / (1 - q₀ ^ (m : ℕ) * u₀) ^ 2) +
       (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 2) -
       2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ))) := by
    refine ((hSu.add hSuinv).sub (hSσ.mul_left 2)).congr_fun
      fun N ↦ ?_
    rw [coeffRingEval_coeff_XA u₀ h0 h1 N.pos.ne', Finset.sum_mul,
      Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    ring
  have htailN : HasSum (fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff (n + 1) XA) *
        q₀ ^ (n + 1))
      ((∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀ / (1 - q₀ ^ (m : ℕ) * u₀) ^ 2) +
       (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 2) -
       2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ))) := by
    have h := (Equiv.pnatEquivNat.symm.hasSum_iff).mpr htail
    refine h.congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply,
      Nat.succPNat_coe]
  have hfull := (hasSum_nat_add_iff
    (f := fun n : ℕ ↦ coeffRingEval u₀ h0 h1
      (PowerSeries.coeff n XA) * q₀ ^ n) 1).mp htailN
  rw [Finset.range_one, Finset.sum_singleton] at hfull
  have hf0 : coeffRingEval u₀ h0 h1 (PowerSeries.coeff 0 XA) *
      q₀ ^ 0 = u₀ / (1 - u₀) ^ 2 := by
    rw [coeffRingEval_coeff_XA_zero, pow_zero, mul_one]
  rw [hf0] at hfull
  rw [evalA, hfull.tsum_eq]
  ring

/-- **Extended-annulus bilateral bridge for `Y`** (PROVEN, same
observation as the `X` version). -/
theorem evalA_YA_eq_bilateralY_ext (u₀ q₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) (hq1 : valuation k q₀ < 1)
    (hu : 1 < valuation k u₀) (hqu : valuation k (q₀ * u₀) < 1) :
    evalA u₀ q₀ h0 h1 YA = bilateralY u₀ q₀ := by
  unfold bilateralY
  have hv0 : valuation k u₀ ≠ 0 := by
    simpa [ne_eq, map_eq_zero] using h0
  have hquinv : valuation k (q₀ * u₀⁻¹) < 1 := by
    rw [map_mul, map_inv₀]
    calc valuation k q₀ * (valuation k u₀)⁻¹
        ≤ valuation k q₀ * 1 := by
          have hinv : (valuation k u₀)⁻¹ ≤ 1 := by
            rw [inv_le_one₀ (zero_lt_iff.mpr hv0)]
            exact hu.le
          exact mul_le_mul_right hinv _
      _ = valuation k q₀ := mul_one _
      _ < 1 := hq1
  have hbin1 : ∀ j : ℕ, valuation k (((j.choose 2 : ℕ) : k)) ≤ 1 := by
    intro j
    have h := valuation_intCast_le_one (R := k) (j.choose 2)
    simpa using h
  have hbin2 : ∀ j : ℕ,
      valuation k ((((j + 1).choose 2 : ℕ) : k)) ≤ 1 := by
    intro j
    have h := valuation_intCast_le_one (R := k) ((j + 1).choose 2)
    simpa using h
  have hS1 := hasSum_lambert_general
    (fun j ↦ ((j.choose 2 : ℕ) : k)) (fun v ↦ v ^ 2 / (1 - v) ^ 3)
    hbin1 u₀ q₀ hq1 hqu
    (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_self v₀ hv₀)
  have hS2 := hasSum_lambert_general
    (fun j ↦ (((j + 1).choose 2 : ℕ) : k)) (fun v ↦ v / (1 - v) ^ 3)
    hbin2 u₀⁻¹ q₀ hq1 hquinv
    (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_succ v₀ hv₀)
  have hSσ := (summable_sigma_one_nonarch q₀ hq1).hasSum
  have htail : HasSum (fun N : ℕ+ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff (N : ℕ) YA) *
        q₀ ^ (N : ℕ))
      ((∑' m : ℕ+, (q₀ ^ (m : ℕ) * u₀) ^ 2 /
          (1 - q₀ ^ (m : ℕ) * u₀) ^ 3) -
       (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 3) +
       (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ))) := by
    refine ((hS1.sub hS2).add hSσ).congr_fun fun N ↦ ?_
    rw [coeffRingEval_coeff_YA u₀ h0 h1 N.pos.ne', Finset.sum_mul,
      Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    ring
  have htailN : HasSum (fun n : ℕ ↦
      coeffRingEval u₀ h0 h1 (PowerSeries.coeff (n + 1) YA) *
        q₀ ^ (n + 1))
      ((∑' m : ℕ+, (q₀ ^ (m : ℕ) * u₀) ^ 2 /
          (1 - q₀ ^ (m : ℕ) * u₀) ^ 3) -
       (∑' m : ℕ+, q₀ ^ (m : ℕ) * u₀⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u₀⁻¹) ^ 3) +
       (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ))) := by
    have h := (Equiv.pnatEquivNat.symm.hasSum_iff).mpr htail
    refine h.congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply,
      Nat.succPNat_coe]
  have hfull := (hasSum_nat_add_iff
    (f := fun n : ℕ ↦ coeffRingEval u₀ h0 h1
      (PowerSeries.coeff n YA) * q₀ ^ n) 1).mp htailN
  rw [Finset.range_one, Finset.sum_singleton] at hfull
  have hf0 : coeffRingEval u₀ h0 h1 (PowerSeries.coeff 0 YA) *
      q₀ ^ 0 = u₀ ^ 2 / (1 - u₀) ^ 3 := by
    rw [coeffRingEval_coeff_YA_zero, pow_zero, mul_one]
  rw [hf0] at hfull
  rw [evalA, hfull.tsum_eq]
  ring

/-- **The cleared chord `X`-identity, shifted case** (DERIVED): when
the product falls below the fundamental annulus, replace `v₀` by
`v₀' := v₀/q₀` (upper extended annulus) and the product by
`u₀v₀' = u₀v₀/q₀` (back in the fundamental annulus); the bilateral
values are invariant by the PROVEN shift identities, and the transport
applies with the extended-annulus summabilities and bridges. -/
theorem bilateral_chordX_cleared_shifted (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0) (hq0 : q₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (_hv1 : v₀ ≠ 1)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (_hvhigh : valuation k v₀ ≤ 1)
    (_hne1 : u₀ * v₀ ≠ 1) (hneq : u₀ * v₀ ≠ q₀) :
    valuation k (u₀ * v₀) ≤ valuation k q₀ →
    (bilateralX (u₀ * v₀) q₀ + bilateralX u₀ q₀ + bilateralX v₀ q₀) *
        (bilateralX u₀ q₀ - bilateralX v₀ q₀) ^ 2 =
      (bilateralY u₀ q₀ - bilateralY v₀ q₀) ^ 2 +
        (bilateralY u₀ q₀ - bilateralY v₀ q₀) *
          (bilateralX u₀ q₀ - bilateralX v₀ q₀) := by
  intro hcase
  have hqvne : valuation k q₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have hqpos : (0 : ValueGroupWithZero k) < valuation k q₀ :=
    zero_lt_iff.mpr hqvne
  have huvne : valuation k u₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hu0
  have hupos : (0 : ValueGroupWithZero k) < valuation k u₀ :=
    zero_lt_iff.mpr huvne
  -- in the shifted case `|v₀| < 1` strictly
  have hv₀lt1 : valuation k v₀ < 1 := by
    have h1 : valuation k u₀ * valuation k v₀ < valuation k u₀ * 1 := by
      rw [mul_one]
      calc valuation k u₀ * valuation k v₀
          = valuation k (u₀ * v₀) := (map_mul _ _ _).symm
        _ ≤ valuation k q₀ := hcase
        _ < valuation k u₀ := hulow
    exact lt_of_mul_lt_mul_left' h1
  -- the auxiliary parameters
  set v₀' : k := v₀ * q₀⁻¹ with hv'def
  have hv'0 : v₀' ≠ 0 := mul_ne_zero hv0 (inv_ne_zero hq0)
  have hqv' : q₀ * v₀' = v₀ := by
    rw [hv'def]
    field_simp
  have hv'gt1 : 1 < valuation k v₀' := by
    rw [hv'def, map_mul, map_inv₀]
    have h1 : valuation k q₀ * (valuation k q₀)⁻¹ <
        valuation k v₀ * (valuation k q₀)⁻¹ :=
      (OrderIso.mulRight₀ _ (zero_lt_iff.mpr (inv_ne_zero hqvne))
        ).strictMono hvlow
    rwa [mul_inv_cancel₀ hqvne] at h1
  have hv'1 : v₀' ≠ 1 := by
    intro h1
    apply lt_irrefl (valuation k v₀)
    calc valuation k v₀ = valuation k q₀ := by rw [← hqv', h1, mul_one]
      _ < valuation k v₀ := hvlow
  have hqv'lt : valuation k (q₀ * v₀') < 1 := by
    rw [hqv']
    exact hv₀lt1
  have hvvne : valuation k v₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hv0
  have hq2v : valuation k (q₀ * v₀'⁻¹) < 1 := by
    have hval : q₀ * v₀'⁻¹ = q₀ * q₀ * v₀⁻¹ := by
      rw [hv'def]
      field_simp
    rw [hval, map_mul, map_mul, map_inv₀]
    calc valuation k q₀ * valuation k q₀ * (valuation k v₀)⁻¹
        < valuation k q₀ * valuation k v₀ * (valuation k v₀)⁻¹ := by
          have hinner : valuation k q₀ * valuation k q₀ <
              valuation k q₀ * valuation k v₀ :=
            (OrderIso.mulLeft₀ _ hqpos).strictMono hvlow
          exact (OrderIso.mulRight₀ _ (zero_lt_iff.mpr
            (inv_ne_zero hvvne))).strictMono hinner
      _ = valuation k q₀ := by
          rw [mul_assoc, mul_inv_cancel₀ hvvne, mul_one]
      _ < 1 := hq1
  have hw0 : u₀ * v₀' ≠ 0 := mul_ne_zero hu0 hv'0
  have hqw : q₀ * (u₀ * v₀') = u₀ * v₀ := by
    rw [hv'def]
    field_simp
  have hq2uv : valuation k q₀ * valuation k q₀ <
      valuation k (u₀ * v₀) := by
    rw [map_mul]
    calc valuation k q₀ * valuation k q₀
        < valuation k u₀ * valuation k q₀ :=
          (OrderIso.mulRight₀ _ hqpos).strictMono hulow
      _ < valuation k u₀ * valuation k v₀ :=
          (OrderIso.mulLeft₀ _ hupos).strictMono hvlow
  have hwlow : valuation k q₀ < valuation k (u₀ * v₀') := by
    have h2 : valuation k q₀ * valuation k (u₀ * v₀')
        = valuation k (u₀ * v₀) := by
      rw [← map_mul, hqw]
    have h1 : valuation k q₀ * valuation k q₀ <
        valuation k q₀ * valuation k (u₀ * v₀') := by
      rw [h2]
      exact hq2uv
    exact lt_of_mul_lt_mul_left' h1
  have hwhigh : valuation k (u₀ * v₀') ≤ 1 := by
    have h2 : valuation k q₀ * valuation k (u₀ * v₀')
        = valuation k (u₀ * v₀) := by
      rw [← map_mul, hqw]
    have h1 : valuation k q₀ * valuation k (u₀ * v₀') ≤
        valuation k q₀ * 1 := by
      rw [mul_one, h2]
      exact hcase
    exact (OrderIso.mulLeft₀ _ hqpos).le_iff_le.mp h1
  have hw1 : u₀ * v₀' ≠ 1 := by
    intro h1
    apply hneq
    rw [← hqw, h1, mul_one]
  have hqwlt : valuation k (q₀ * (u₀ * v₀')) < 1 := by
    rw [hqw]
    exact lt_of_le_of_lt hcase hq1
  have hq2w : valuation k (q₀ * (u₀ * v₀')⁻¹) < 1 := by
    have hval : q₀ * (u₀ * v₀')⁻¹ = q₀ * q₀ * (u₀ * v₀)⁻¹ := by
      rw [hv'def]
      field_simp
    rw [hval, map_mul, map_mul, map_inv₀]
    have huv0 : valuation k (u₀ * v₀) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (mul_ne_zero hu0 hv0)
    have h1 : valuation k q₀ * valuation k q₀ *
        (valuation k (u₀ * v₀))⁻¹ <
        valuation k (u₀ * v₀) * (valuation k (u₀ * v₀))⁻¹ :=
      (OrderIso.mulRight₀ _ (zero_lt_iff.mpr (inv_ne_zero huv0))
        ).strictMono hq2uv
    rwa [mul_inv_cancel₀ huv0] at h1
  -- the bilateral values are shift-invariant
  have hXv_eq : bilateralX v₀ q₀ = bilateralX v₀' q₀ := by
    rw [← hqv']
    exact bilateralX_shift v₀' q₀ hv'0 hq0 hq1 hqv'lt hq2v
  have hYv_eq : bilateralY v₀ q₀ = bilateralY v₀' q₀ := by
    rw [← hqv']
    exact bilateralY_shift v₀' q₀ hv'0 hv'1 hq0 hq1 hqv'lt hq2v
  have hXw_eq : bilateralX (u₀ * v₀) q₀ = bilateralX (u₀ * v₀') q₀ := by
    rw [← hqw]
    exact bilateralX_shift (u₀ * v₀') q₀ hw0 hq0 hq1 hqwlt hq2w
  have hYw_eq : bilateralY (u₀ * v₀) q₀ = bilateralY (u₀ * v₀') q₀ := by
    rw [← hqw]
    exact bilateralY_shift (u₀ * v₀') q₀ hw0 hw1 hq0 hq1 hqwlt hq2w
  rw [hXv_eq, hYv_eq, hXw_eq,
    ← evalA_XA_eq_bilateralX u₀ q₀ hu0 hu1 huhigh hq1 hulow,
    ← evalA_XA_eq_bilateralX_ext v₀' q₀ hv'0 hv'1 hq1 hv'gt1 hqv'lt,
    ← evalA_XA_eq_bilateralX (u₀ * v₀') q₀ hw0 hw1 hwhigh hq1 hwlow,
    ← evalA_YA_eq_bilateralY u₀ q₀ hu0 hu1 huhigh hq1 hulow,
    ← evalA_YA_eq_bilateralY_ext v₀' q₀ hv'0 hv'1 hq1 hv'gt1 hqv'lt]
  exact evalA_chordX_of_formal chordX_formal u₀ v₀' q₀ hu0 hv'0 hu1 hv'1
    hw1 hw0
    (summable_evalA_XA u₀ q₀ hu0 hu1 huhigh hulow)
    (summable_evalA_XA_ext v₀' q₀ hv'0 hv'1 hv'gt1 hqv'lt)
    (summable_evalA_XA (u₀ * v₀') q₀ hw0 hw1 hwhigh hwlow)
    (summable_evalA_YA u₀ q₀ hu0 hu1 huhigh hulow)
    (summable_evalA_YA_ext v₀' q₀ hv'0 hv'1 hv'gt1 hqv'lt)

/-- **The cleared chord `X`-identity** (decomposed 2026-07-18 into the
fundamental-window case and the shifted case): a pure polynomial
identity between the six bilateral values at `u₀`, `v₀`, `u₀v₀`, with no
slope, division, or case structure — the series content of the chord
addition (denominator-free Silverman V.3.1(c), `x`-part). -/
theorem bilateral_chordX_cleared (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0) (hq0 : q₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (hv1 : v₀ ≠ 1)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1)
    (hne1 : u₀ * v₀ ≠ 1) (hneq : u₀ * v₀ ≠ q₀) :
    (bilateralX (u₀ * v₀) q₀ + bilateralX u₀ q₀ + bilateralX v₀ q₀) *
        (bilateralX u₀ q₀ - bilateralX v₀ q₀) ^ 2 =
      (bilateralY u₀ q₀ - bilateralY v₀ q₀) ^ 2 +
        (bilateralY u₀ q₀ - bilateralY v₀ q₀) *
          (bilateralX u₀ q₀ - bilateralX v₀ q₀) := by
  rcases lt_or_ge (valuation k q₀) (valuation k (u₀ * v₀)) with hcase | hcase
  · exact bilateral_chordX_cleared_window u₀ v₀ q₀ hu0 hv0 hq0 hu1 hv1 hq1
      hulow huhigh hvlow hvhigh hne1 hneq hcase
  · exact bilateral_chordX_cleared_shifted u₀ v₀ q₀ hu0 hv0 hq0 hu1 hv1 hq1
      hulow huhigh hvlow hvhigh hne1 hneq hcase

/-- **The `evalA`-level chord `Y`-identity** (DERIVED from the formal
identity and the evaluation transport). -/
theorem evalA_chordY (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0) (_hq0 : q₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (hv1 : v₀ ≠ 1)
    (_hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1)
    (hne1 : u₀ * v₀ ≠ 1) (_hneq : u₀ * v₀ ≠ q₀) :
    ∀ (hw0 : u₀ * v₀ ≠ 0) (_hwin : valuation k q₀ < valuation k (u₀ * v₀))
      (_hwhigh : valuation k (u₀ * v₀) ≤ 1),
    -(evalA (u₀ * v₀) q₀ hw0 hne1 YA + evalA (u₀ * v₀) q₀ hw0 hne1 XA) *
        (evalA u₀ q₀ hu0 hu1 XA - evalA v₀ q₀ hv0 hv1 XA) =
      (evalA u₀ q₀ hu0 hu1 YA - evalA v₀ q₀ hv0 hv1 YA) *
          (evalA (u₀ * v₀) q₀ hw0 hne1 XA - evalA u₀ q₀ hu0 hu1 XA) +
        evalA u₀ q₀ hu0 hu1 YA *
          (evalA u₀ q₀ hu0 hu1 XA - evalA v₀ q₀ hv0 hv1 XA) :=
  fun hw0 hwin hwhigh =>
    evalA_chordY_of_formal chordY_formal u₀ v₀ q₀ hu0 hv0 hu1 hv1 hne1 hw0
      (summable_evalA_XA u₀ q₀ hu0 hu1 huhigh hulow)
      (summable_evalA_XA v₀ q₀ hv0 hv1 hvhigh hvlow)
      (summable_evalA_XA (u₀ * v₀) q₀ hw0 hne1 hwhigh hwin)
      (summable_evalA_YA u₀ q₀ hu0 hu1 huhigh hulow)
      (summable_evalA_YA v₀ q₀ hv0 hv1 hvhigh hvlow)
      (summable_evalA_YA (u₀ * v₀) q₀ hw0 hne1 hwhigh hwin)

/-- **The cleared chord `Y`-identity, fundamental-window case** (DERIVED
from the `evalA`-level identity through the bilateral bridges). -/
theorem bilateral_chordY_cleared_window (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0) (hq0 : q₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (hv1 : v₀ ≠ 1)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1)
    (hne1 : u₀ * v₀ ≠ 1) (hneq : u₀ * v₀ ≠ q₀) :
    valuation k q₀ < valuation k (u₀ * v₀) →
    -(bilateralY (u₀ * v₀) q₀ + bilateralX (u₀ * v₀) q₀) *
        (bilateralX u₀ q₀ - bilateralX v₀ q₀) =
      (bilateralY u₀ q₀ - bilateralY v₀ q₀) *
          (bilateralX (u₀ * v₀) q₀ - bilateralX u₀ q₀) +
        bilateralY u₀ q₀ * (bilateralX u₀ q₀ - bilateralX v₀ q₀) := by
  intro hwin
  have hw0 : u₀ * v₀ ≠ 0 := mul_ne_zero hu0 hv0
  have hwhigh : valuation k (u₀ * v₀) ≤ 1 := by
    rw [map_mul]
    calc valuation k u₀ * valuation k v₀ ≤ 1 * valuation k v₀ :=
          mul_le_mul_left huhigh _
      _ = valuation k v₀ := one_mul _
      _ ≤ 1 := hvhigh
  rw [← evalA_XA_eq_bilateralX u₀ q₀ hu0 hu1 huhigh hq1 hulow,
    ← evalA_XA_eq_bilateralX v₀ q₀ hv0 hv1 hvhigh hq1 hvlow,
    ← evalA_XA_eq_bilateralX (u₀ * v₀) q₀ hw0 hne1 hwhigh hq1 hwin,
    ← evalA_YA_eq_bilateralY u₀ q₀ hu0 hu1 huhigh hq1 hulow,
    ← evalA_YA_eq_bilateralY v₀ q₀ hv0 hv1 hvhigh hq1 hvlow,
    ← evalA_YA_eq_bilateralY (u₀ * v₀) q₀ hw0 hne1 hwhigh hq1 hwin]
  exact evalA_chordY u₀ v₀ q₀ hu0 hv0 hq0 hu1 hv1 hq1 hulow huhigh hvlow
    hvhigh hne1 hneq hw0 hwin hwhigh

/-- **The cleared chord `Y`-identity, shifted case** (DERIVED): same
shift-reduction as the `X`-identity. -/
theorem bilateral_chordY_cleared_shifted (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0) (hq0 : q₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (_hv1 : v₀ ≠ 1)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (_hvhigh : valuation k v₀ ≤ 1)
    (_hne1 : u₀ * v₀ ≠ 1) (hneq : u₀ * v₀ ≠ q₀) :
    valuation k (u₀ * v₀) ≤ valuation k q₀ →
    -(bilateralY (u₀ * v₀) q₀ + bilateralX (u₀ * v₀) q₀) *
        (bilateralX u₀ q₀ - bilateralX v₀ q₀) =
      (bilateralY u₀ q₀ - bilateralY v₀ q₀) *
          (bilateralX (u₀ * v₀) q₀ - bilateralX u₀ q₀) +
        bilateralY u₀ q₀ * (bilateralX u₀ q₀ - bilateralX v₀ q₀) := by
  intro hcase
  have hqvne : valuation k q₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have hqpos : (0 : ValueGroupWithZero k) < valuation k q₀ :=
    zero_lt_iff.mpr hqvne
  have huvne : valuation k u₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hu0
  have hupos : (0 : ValueGroupWithZero k) < valuation k u₀ :=
    zero_lt_iff.mpr huvne
  -- in the shifted case `|v₀| < 1` strictly
  have hv₀lt1 : valuation k v₀ < 1 := by
    have h1 : valuation k u₀ * valuation k v₀ < valuation k u₀ * 1 := by
      rw [mul_one]
      calc valuation k u₀ * valuation k v₀
          = valuation k (u₀ * v₀) := (map_mul _ _ _).symm
        _ ≤ valuation k q₀ := hcase
        _ < valuation k u₀ := hulow
    exact lt_of_mul_lt_mul_left' h1
  -- the auxiliary parameters
  set v₀' : k := v₀ * q₀⁻¹ with hv'def
  have hv'0 : v₀' ≠ 0 := mul_ne_zero hv0 (inv_ne_zero hq0)
  have hqv' : q₀ * v₀' = v₀ := by
    rw [hv'def]
    field_simp
  have hv'gt1 : 1 < valuation k v₀' := by
    rw [hv'def, map_mul, map_inv₀]
    have h1 : valuation k q₀ * (valuation k q₀)⁻¹ <
        valuation k v₀ * (valuation k q₀)⁻¹ :=
      (OrderIso.mulRight₀ _ (zero_lt_iff.mpr (inv_ne_zero hqvne))
        ).strictMono hvlow
    rwa [mul_inv_cancel₀ hqvne] at h1
  have hv'1 : v₀' ≠ 1 := by
    intro h1
    apply lt_irrefl (valuation k v₀)
    calc valuation k v₀ = valuation k q₀ := by rw [← hqv', h1, mul_one]
      _ < valuation k v₀ := hvlow
  have hqv'lt : valuation k (q₀ * v₀') < 1 := by
    rw [hqv']
    exact hv₀lt1
  have hvvne : valuation k v₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hv0
  have hq2v : valuation k (q₀ * v₀'⁻¹) < 1 := by
    have hval : q₀ * v₀'⁻¹ = q₀ * q₀ * v₀⁻¹ := by
      rw [hv'def]
      field_simp
    rw [hval, map_mul, map_mul, map_inv₀]
    calc valuation k q₀ * valuation k q₀ * (valuation k v₀)⁻¹
        < valuation k q₀ * valuation k v₀ * (valuation k v₀)⁻¹ := by
          have hinner : valuation k q₀ * valuation k q₀ <
              valuation k q₀ * valuation k v₀ :=
            (OrderIso.mulLeft₀ _ hqpos).strictMono hvlow
          exact (OrderIso.mulRight₀ _ (zero_lt_iff.mpr
            (inv_ne_zero hvvne))).strictMono hinner
      _ = valuation k q₀ := by
          rw [mul_assoc, mul_inv_cancel₀ hvvne, mul_one]
      _ < 1 := hq1
  have hw0 : u₀ * v₀' ≠ 0 := mul_ne_zero hu0 hv'0
  have hqw : q₀ * (u₀ * v₀') = u₀ * v₀ := by
    rw [hv'def]
    field_simp
  have hq2uv : valuation k q₀ * valuation k q₀ <
      valuation k (u₀ * v₀) := by
    rw [map_mul]
    calc valuation k q₀ * valuation k q₀
        < valuation k u₀ * valuation k q₀ :=
          (OrderIso.mulRight₀ _ hqpos).strictMono hulow
      _ < valuation k u₀ * valuation k v₀ :=
          (OrderIso.mulLeft₀ _ hupos).strictMono hvlow
  have hwlow : valuation k q₀ < valuation k (u₀ * v₀') := by
    have h2 : valuation k q₀ * valuation k (u₀ * v₀')
        = valuation k (u₀ * v₀) := by
      rw [← map_mul, hqw]
    have h1 : valuation k q₀ * valuation k q₀ <
        valuation k q₀ * valuation k (u₀ * v₀') := by
      rw [h2]
      exact hq2uv
    exact lt_of_mul_lt_mul_left' h1
  have hwhigh : valuation k (u₀ * v₀') ≤ 1 := by
    have h2 : valuation k q₀ * valuation k (u₀ * v₀')
        = valuation k (u₀ * v₀) := by
      rw [← map_mul, hqw]
    have h1 : valuation k q₀ * valuation k (u₀ * v₀') ≤
        valuation k q₀ * 1 := by
      rw [mul_one, h2]
      exact hcase
    exact (OrderIso.mulLeft₀ _ hqpos).le_iff_le.mp h1
  have hw1 : u₀ * v₀' ≠ 1 := by
    intro h1
    apply hneq
    rw [← hqw, h1, mul_one]
  have hqwlt : valuation k (q₀ * (u₀ * v₀')) < 1 := by
    rw [hqw]
    exact lt_of_le_of_lt hcase hq1
  have hq2w : valuation k (q₀ * (u₀ * v₀')⁻¹) < 1 := by
    have hval : q₀ * (u₀ * v₀')⁻¹ = q₀ * q₀ * (u₀ * v₀)⁻¹ := by
      rw [hv'def]
      field_simp
    rw [hval, map_mul, map_mul, map_inv₀]
    have huv0 : valuation k (u₀ * v₀) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (mul_ne_zero hu0 hv0)
    have h1 : valuation k q₀ * valuation k q₀ *
        (valuation k (u₀ * v₀))⁻¹ <
        valuation k (u₀ * v₀) * (valuation k (u₀ * v₀))⁻¹ :=
      (OrderIso.mulRight₀ _ (zero_lt_iff.mpr (inv_ne_zero huv0))
        ).strictMono hq2uv
    rwa [mul_inv_cancel₀ huv0] at h1
  -- the bilateral values are shift-invariant
  have hXv_eq : bilateralX v₀ q₀ = bilateralX v₀' q₀ := by
    rw [← hqv']
    exact bilateralX_shift v₀' q₀ hv'0 hq0 hq1 hqv'lt hq2v
  have hYv_eq : bilateralY v₀ q₀ = bilateralY v₀' q₀ := by
    rw [← hqv']
    exact bilateralY_shift v₀' q₀ hv'0 hv'1 hq0 hq1 hqv'lt hq2v
  have hXw_eq : bilateralX (u₀ * v₀) q₀ = bilateralX (u₀ * v₀') q₀ := by
    rw [← hqw]
    exact bilateralX_shift (u₀ * v₀') q₀ hw0 hq0 hq1 hqwlt hq2w
  have hYw_eq : bilateralY (u₀ * v₀) q₀ = bilateralY (u₀ * v₀') q₀ := by
    rw [← hqw]
    exact bilateralY_shift (u₀ * v₀') q₀ hw0 hw1 hq0 hq1 hqwlt hq2w
  rw [hXv_eq, hYv_eq, hXw_eq, hYw_eq,
    ← evalA_XA_eq_bilateralX u₀ q₀ hu0 hu1 huhigh hq1 hulow,
    ← evalA_XA_eq_bilateralX_ext v₀' q₀ hv'0 hv'1 hq1 hv'gt1 hqv'lt,
    ← evalA_XA_eq_bilateralX (u₀ * v₀') q₀ hw0 hw1 hwhigh hq1 hwlow,
    ← evalA_YA_eq_bilateralY u₀ q₀ hu0 hu1 huhigh hq1 hulow,
    ← evalA_YA_eq_bilateralY_ext v₀' q₀ hv'0 hv'1 hq1 hv'gt1 hqv'lt,
    ← evalA_YA_eq_bilateralY (u₀ * v₀') q₀ hw0 hw1 hwhigh hq1 hwlow]
  exact evalA_chordY_of_formal chordY_formal u₀ v₀' q₀ hu0 hv'0 hu1 hv'1
    hw1 hw0
    (summable_evalA_XA u₀ q₀ hu0 hu1 huhigh hulow)
    (summable_evalA_XA_ext v₀' q₀ hv'0 hv'1 hv'gt1 hqv'lt)
    (summable_evalA_XA (u₀ * v₀') q₀ hw0 hw1 hwhigh hwlow)
    (summable_evalA_YA u₀ q₀ hu0 hu1 huhigh hulow)
    (summable_evalA_YA_ext v₀' q₀ hv'0 hv'1 hv'gt1 hqv'lt)
    (summable_evalA_YA (u₀ * v₀') q₀ hw0 hw1 hwhigh hwlow)

/-- **The cleared chord `Y`-identity** (decomposed 2026-07-18 into the
fundamental-window case and the shifted case, like the `X`-identity):
the denominator-free form of Silverman V.3.1(c), `y`-part, linear in the
`x`-part output. -/
theorem bilateral_chordY_cleared (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0) (hq0 : q₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (hv1 : v₀ ≠ 1)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1)
    (hne1 : u₀ * v₀ ≠ 1) (hneq : u₀ * v₀ ≠ q₀) :
    -(bilateralY (u₀ * v₀) q₀ + bilateralX (u₀ * v₀) q₀) *
        (bilateralX u₀ q₀ - bilateralX v₀ q₀) =
      (bilateralY u₀ q₀ - bilateralY v₀ q₀) *
          (bilateralX (u₀ * v₀) q₀ - bilateralX u₀ q₀) +
        bilateralY u₀ q₀ * (bilateralX u₀ q₀ - bilateralX v₀ q₀) := by
  rcases lt_or_ge (valuation k q₀) (valuation k (u₀ * v₀)) with hcase | hcase
  · exact bilateral_chordY_cleared_window u₀ v₀ q₀ hu0 hv0 hq0 hu1 hv1 hq1
      hulow huhigh hvlow hvhigh hne1 hneq hcase
  · exact bilateral_chordY_cleared_shifted u₀ v₀ q₀ hu0 hv0 hq0 hu1 hv1 hq1
      hulow huhigh hvlow hvhigh hne1 hneq hcase

/-- **The chord identity** (DERIVED 2026-07-18 from the cleared chord
identities — Silverman V.3.1(c), generic case): for annulus parameters
with distinct bilateral `x`-values, the bilateral values of the product
are the affine chord addition of the bilateral values of the factors.
The division bookkeeping (the slope, `addX`, `addY`) is handled here;
the series content is the two cleared polynomial identities. -/
theorem bilateral_add_of_X_ne [DecidableEq k] (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hv0 : v₀ ≠ 0) (hq0 : q₀ ≠ 0)
    (hu1 : u₀ ≠ 1) (hv1 : v₀ ≠ 1)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1)
    (hX : bilateralX u₀ q₀ ≠ bilateralX v₀ q₀) :
    bilateralX (u₀ * v₀) q₀ =
      (WeierstrassCurve.tateCurve q₀).toAffine.addX (bilateralX u₀ q₀)
        (bilateralX v₀ q₀)
        ((WeierstrassCurve.tateCurve q₀).toAffine.slope (bilateralX u₀ q₀)
          (bilateralX v₀ q₀) (bilateralY u₀ q₀) (bilateralY v₀ q₀)) ∧
    bilateralY (u₀ * v₀) q₀ =
      (WeierstrassCurve.tateCurve q₀).toAffine.addY (bilateralX u₀ q₀)
        (bilateralX v₀ q₀) (bilateralY u₀ q₀)
        ((WeierstrassCurve.tateCurve q₀).toAffine.slope (bilateralX u₀ q₀)
          (bilateralX v₀ q₀) (bilateralY u₀ q₀) (bilateralY v₀ q₀)) := by
  -- the triviality exclusions follow from the distinct `x`-values
  have hqu : valuation k (q₀ * u₀) < 1 := by
    rw [map_mul]
    calc valuation k q₀ * valuation k u₀ ≤ valuation k q₀ * 1 :=
          mul_le_mul_right huhigh _
      _ = valuation k q₀ := mul_one _
      _ < 1 := hq1
  have hquinv : valuation k (q₀ * u₀⁻¹) < 1 := by
    rw [map_mul, map_inv₀]
    have hinvpos : (0 : ValueGroupWithZero k) < (valuation k u₀)⁻¹ :=
      zero_lt_iff.mpr (inv_ne_zero ((Valuation.ne_zero_iff _).mpr hu0))
    calc valuation k q₀ * (valuation k u₀)⁻¹
        < valuation k u₀ * (valuation k u₀)⁻¹ :=
          (OrderIso.mulRight₀ _ hinvpos).strictMono hulow
      _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr hu0)
  have hne1 : u₀ * v₀ ≠ 1 := by
    intro h
    apply hX
    have hv : v₀ = u₀⁻¹ := by
      field_simp at h ⊢
      linear_combination h
    rw [hv, bilateralX_inv u₀ q₀ hu0]
  have hneq : u₀ * v₀ ≠ q₀ := by
    intro h
    apply hX
    have hv : v₀ = q₀ * u₀⁻¹ := by
      field_simp at h ⊢
      linear_combination h
    have hqinv' : valuation k (q₀ * (u₀⁻¹)⁻¹) < 1 := by rwa [inv_inv]
    rw [hv, bilateralX_shift u₀⁻¹ q₀ (inv_ne_zero hu0) hq0 hq1 hquinv hqinv',
      bilateralX_inv u₀ q₀ hu0]
  have hD : bilateralX u₀ q₀ - bilateralX v₀ q₀ ≠ 0 := sub_ne_zero.mpr hX
  have h1 := bilateral_chordX_cleared u₀ v₀ q₀ hu0 hv0 hq0 hu1 hv1 hq1
    hulow huhigh hvlow hvhigh hne1 hneq
  have h2 := bilateral_chordY_cleared u₀ v₀ q₀ hu0 hv0 hq0 hu1 hv1 hq1
    hulow huhigh hvlow hvhigh hne1 hneq
  have hXeq : bilateralX (u₀ * v₀) q₀ =
      (WeierstrassCurve.tateCurve q₀).toAffine.addX (bilateralX u₀ q₀)
        (bilateralX v₀ q₀)
        ((WeierstrassCurve.tateCurve q₀).toAffine.slope (bilateralX u₀ q₀)
          (bilateralX v₀ q₀) (bilateralY u₀ q₀) (bilateralY v₀ q₀)) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hX,
      WeierstrassCurve.Affine.addX,
      show (WeierstrassCurve.tateCurve q₀).toAffine.a₁ = 1 from rfl,
      show (WeierstrassCurve.tateCurve q₀).toAffine.a₂ = 0 from rfl]
    field_simp
    linear_combination h1
  refine ⟨hXeq, ?_⟩
  rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY,
    show (WeierstrassCurve.tateCurve q₀).toAffine.a₁ = 1 from rfl,
    show (WeierstrassCurve.tateCurve q₀).toAffine.a₃ = 0 from rfl,
    ← hXeq, WeierstrassCurve.Affine.slope_of_X_ne hX]
  field_simp
  linear_combination -h2

omit [CharZero k] in
/-- **The vertical case** (PROVEN from the inversion and shift identities):
if the product of two annulus parameters is `1` or `q₀` — the trivial class
— then their bilateral coordinates are related by the Weierstrass negation:
equal `x`-values, `negY`-related `y`-values. -/
theorem bilateral_negY_of_mul_trivial (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1) (hv0 : v₀ ≠ 0)
    (hq0 : q₀ ≠ 0) (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (htriv : u₀ * v₀ = 1 ∨ u₀ * v₀ = q₀) :
    bilateralX v₀ q₀ = bilateralX u₀ q₀ ∧
    bilateralY v₀ q₀ = (WeierstrassCurve.tateCurve q₀).toAffine.negY
      (bilateralX u₀ q₀) (bilateralY u₀ q₀) := by
  have hqu : valuation k (q₀ * u₀) < 1 := by
    rw [map_mul]
    calc valuation k q₀ * valuation k u₀ ≤ valuation k q₀ * 1 :=
          mul_le_mul_right huhigh _
      _ = valuation k q₀ := mul_one _
      _ < 1 := hq1
  have hquinv : valuation k (q₀ * u₀⁻¹) < 1 := by
    rw [map_mul, map_inv₀]
    have hinvpos : (0 : ValueGroupWithZero k) < (valuation k u₀)⁻¹ :=
      zero_lt_iff.mpr (inv_ne_zero ((Valuation.ne_zero_iff _).mpr hu0))
    calc valuation k q₀ * (valuation k u₀)⁻¹
        < valuation k u₀ * (valuation k u₀)⁻¹ :=
          (OrderIso.mulRight₀ _ hinvpos).strictMono hulow
      _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr hu0)
  rw [tateCurve_negY]
  rcases htriv with h1 | hqcase
  · -- `v₀ = u₀⁻¹`
    have hv : v₀ = u₀⁻¹ := by
      field_simp at h1 ⊢
      linear_combination h1
    subst hv
    exact ⟨bilateralX_inv u₀ q₀ hu0,
      bilateralY_inv u₀ q₀ hu0 hu1 hq1 hqu hquinv⟩
  · -- `v₀ = q₀ * u₀⁻¹`
    have hv : v₀ = q₀ * u₀⁻¹ := by
      field_simp at hqcase ⊢
      linear_combination hqcase
    subst hv
    have hinv1 : u₀⁻¹ ≠ 1 := fun h => hu1 (by
      rw [← inv_inv u₀, h, inv_one])
    have hinv0 : u₀⁻¹ ≠ 0 := inv_ne_zero hu0
    have hqu' : valuation k (q₀ * u₀⁻¹) < 1 := hquinv
    have hquinv' : valuation k (q₀ * (u₀⁻¹)⁻¹) < 1 := by
      rwa [inv_inv]
    constructor
    · rw [bilateralX_shift u₀⁻¹ q₀ hinv0 hq0 hq1 hqu' hquinv',
        bilateralX_inv u₀ q₀ hu0]
    · rw [bilateralY_shift u₀⁻¹ q₀ hinv0 hinv1 hq0 hq1 hqu' hquinv',
        bilateralY_inv u₀ q₀ hu0 hu1 hq1 hqu hquinv]

/-- **Silverman's completion lemma** (ATAEC V.3.1.2): a map from a
commutative group to an additive commutative group that takes
infinitely many values and is additive on every pair with
`φ u ≠ ±φ v` is a homomorphism outright. -/
theorem hom_of_partial_hom {G A : Type*} [CommGroup G] [AddCommGroup A]
    (φ : G → A) (hinf : (Set.range φ).Infinite)
    (h : ∀ u v : G, φ u ≠ φ v → φ u ≠ -φ v → φ (u * v) = φ u + φ v)
    (u₁ u₂ : G) : φ (u₁ * u₂) = φ u₁ + φ u₂ := by
  obtain ⟨a, hmem, havoid⟩ := (hinf.sdiff (Set.toFinite
    ({φ u₁, -φ u₁, -φ u₁ + φ u₂, -φ u₁ - φ u₂, φ (u₁ * u₂),
      -φ (u₁ * u₂)} : Set A))).nonempty
  obtain ⟨w, rfl⟩ := hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at havoid
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := havoid
  have e1 : φ (w * u₁) = φ w + φ u₁ := h w u₁ h1 h2
  have e2 : φ (w * u₁) ≠ φ u₂ := by
    rw [e1]
    intro hc
    refine h3 ?_
    rw [← hc]
    abel
  have e3 : φ (w * u₁) ≠ -φ u₂ := by
    rw [e1]
    intro hc
    refine h4 ?_
    rw [sub_eq_add_neg, ← hc]
    abel
  have e4 : φ (w * u₁ * u₂) = φ w + φ u₁ + φ u₂ := by
    rw [h (w * u₁) u₂ e2 e3, e1]
  have e5 : φ (w * (u₁ * u₂)) = φ w + φ (u₁ * u₂) := h w (u₁ * u₂) h5 h6
  have e6 : φ w + φ (u₁ * u₂) = φ w + (φ u₁ + φ u₂) := by
    rw [← e5, ← mul_assoc, e4, add_assoc]
  exact add_left_cancel e6

set_option maxHeartbeats 800000 in
/-- **Head domination on the unit shell**: for `|u₀| = 1` the
`x`-value's valuation is `|1-u₀|⁻²` — the head `u₀/(1-u₀)²` dominates
the Lambert tail, which is bounded by `|q₀|`. -/
theorem valuation_evalA_XA_eq (u₀ q₀ : k) (h0 : u₀ ≠ 0) (h1 : u₀ ≠ 1)
    (_hq0 : q₀ ≠ 0) (hq1 : valuation k q₀ < 1)
    (huval : valuation k u₀ = 1) :
    valuation k (evalA u₀ q₀ h0 h1 XA) =
      ((valuation k (1 - u₀)) ^ 2)⁻¹ := by
  have hulow : valuation k q₀ < valuation k u₀ := by
    rw [huval]
    exact hq1
  have hsum := summable_evalA_XA u₀ q₀ h0 h1 (le_of_eq huval) hulow
  have hone : valuation k (1 - u₀) ≤ 1 := by
    calc valuation k (1 - u₀) ≤ max (valuation k 1) (valuation k u₀) :=
          Valuation.map_sub _ _ _
      _ = 1 := by rw [map_one, huval, max_self]
  have h1u0 : (1 : k) - u₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1uval : valuation k (1 - u₀) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr h1u0
  have hheadval : valuation k (u₀ / (1 - u₀) ^ 2) =
      ((valuation k (1 - u₀)) ^ 2)⁻¹ := by
    rw [map_div₀, map_pow, huval, one_div]
  have htail : valuation k (∑' n : ℕ, coeffRingEval u₀ h0 h1
      (PowerSeries.coeff (n + 1) XA) * q₀ ^ (n + 1)) ≤
      valuation k q₀ := by
    have hsum1 : Summable (fun n : ℕ => coeffRingEval u₀ h0 h1
        (PowerSeries.coeff (n + 1) XA) * q₀ ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr hsum
    refine valuation_tsum_le hsum1 _ fun n => ?_
    rw [map_mul, map_pow]
    have hb := valuation_coeffRingEval_XA_le u₀ h0 h1 (le_of_eq huval)
      (Nat.succ_ne_zero n)
    rw [huval, one_pow, inv_one] at hb
    calc valuation k (coeffRingEval u₀ h0 h1
          (PowerSeries.coeff (n + 1) XA)) * valuation k q₀ ^ (n + 1)
        ≤ 1 * valuation k q₀ ^ (n + 1) := mul_le_mul_left hb _
      _ = valuation k q₀ ^ (n + 1) := one_mul _
      _ ≤ valuation k q₀ ^ 1 :=
          pow_le_pow_right_of_le_one' hq1.le (by omega)
      _ = valuation k q₀ := pow_one _
  have hheadone : (1 : ValueGroupWithZero k) ≤
      ((valuation k (1 - u₀)) ^ 2)⁻¹ := by
    rw [one_le_inv₀ (zero_lt_iff.mpr (pow_ne_zero 2 h1uval))]
    exact pow_le_one₀ zero_le hone
  have hltval : valuation k (∑' n : ℕ, coeffRingEval u₀ h0 h1
      (PowerSeries.coeff (n + 1) XA) * q₀ ^ (n + 1)) <
      valuation k (u₀ / (1 - u₀) ^ 2) := by
    rw [hheadval]
    exact lt_of_le_of_lt htail (lt_of_lt_of_le hq1 hheadone)
  have hsplit : evalA u₀ q₀ h0 h1 XA = u₀ / (1 - u₀) ^ 2 +
      ∑' n : ℕ, coeffRingEval u₀ h0 h1
        (PowerSeries.coeff (n + 1) XA) * q₀ ^ (n + 1) := by
    rw [evalA, hsum.tsum_eq_zero_add, coeffRingEval_coeff_XA_zero,
      pow_zero, mul_one]
  rw [hsplit, (valuation k).map_add_eq_of_lt_left hltval, hheadval]

/-- **The point map takes infinitely many values**: the family
`1 + q₀^(j+1)` lies on the unit shell with `x`-valuations
`|q₀|^(-2(j+1))`, pairwise distinct. -/
theorem pointMap_range_infinite (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq1 : valuation k q₀ < 1) :
    (Set.range (fun x : kˣ =>
      pointMap q₀ hq0 hq1 (x : k) x.ne_zero)).Infinite := by
  have hqv : valuation k q₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have hqpow : ∀ j : ℕ, valuation k (q₀ ^ (j + 1)) < 1 := fun j => by
    rw [map_pow]
    calc valuation k q₀ ^ (j + 1) ≤ valuation k q₀ ^ 1 :=
          pow_le_pow_right_of_le_one' hq1.le (by omega)
      _ = valuation k q₀ := pow_one _
      _ < 1 := hq1
  have huval : ∀ j : ℕ, valuation k (1 + q₀ ^ (j + 1)) = 1 := fun j => by
    have h : valuation k ((1 : k) + q₀ ^ (j + 1)) = valuation k (1 : k) :=
      (valuation k).map_add_eq_of_lt_left
        (by rw [map_one]; exact hqpow j)
    rw [h, map_one]
  have hu0 : ∀ j : ℕ, (1 : k) + q₀ ^ (j + 1) ≠ 0 := fun j => by
    intro hc
    have h := huval j
    rw [hc, map_zero] at h
    exact zero_ne_one h
  have hu1 : ∀ j : ℕ, (1 : k) + q₀ ^ (j + 1) ≠ 1 := fun j => by
    intro hc
    have h : q₀ ^ (j + 1) = 0 := by linear_combination hc
    exact pow_ne_zero (j + 1) hq0 h
  have hsub : ∀ j : ℕ, (1 : k) - (1 + q₀ ^ (j + 1)) = -(q₀ ^ (j + 1)) :=
    fun j => by ring
  have hlow : ∀ m : ℕ, valuation k q₀ <
      valuation k (1 + q₀ ^ (m + 1)) := fun m => by
    rw [huval m]
    exact hq1
  have hhigh : ∀ m : ℕ, valuation k (1 + q₀ ^ (m + 1)) ≤ 1 :=
    fun m => le_of_eq (huval m)
  refine Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => pointMap q₀ hq0 hq1 (1 + q₀ ^ (j + 1)) (hu0 j))
    ?_ ?_
  · intro i j hij
    by_contra hne
    simp only at hij
    rw [pointMap_of_mem_annulus q₀ hq0 hq1 _ (hu0 i) (hu1 i) (hlow i)
        (hhigh i),
      pointMap_of_mem_annulus q₀ hq0 hq1 _ (hu0 j) (hu1 j) (hlow j)
        (hhigh j), annulusPoint, annulusPoint] at hij
    have hX : evalA (1 + q₀ ^ (i + 1)) q₀ (hu0 i) (hu1 i) XA =
        evalA (1 + q₀ ^ (j + 1)) q₀ (hu0 j) (hu1 j) XA := by
      injection hij
    have hXv := congrArg (valuation k) hX
    rw [valuation_evalA_XA_eq _ _ _ _ hq0 hq1 (huval i),
      valuation_evalA_XA_eq _ _ _ _ hq0 hq1 (huval j),
      hsub i, hsub j, (valuation k).map_neg, (valuation k).map_neg,
      map_pow, map_pow] at hXv
    have h2 := inv_injective hXv
    rw [← pow_mul, ← pow_mul] at h2
    rcases Nat.lt_trichotomy i j with hlt | heq | hlt
    · have hstrict : valuation k q₀ ^ ((j + 1) * 2) <
          valuation k q₀ ^ ((i + 1) * 2) :=
        pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr hqv) hq1
          (by omega)
      rw [h2] at hstrict
      exact absurd hstrict (lt_irrefl _)
    · exact hne heq
    · have hstrict : valuation k q₀ ^ ((i + 1) * 2) <
          valuation k q₀ ^ ((j + 1) * 2) :=
        pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr hqv) hq1
          (by omega)
      rw [h2] at hstrict
      exact absurd hstrict (lt_irrefl _)
  · intro j
    exact ⟨Units.mk0 _ (hu0 j), rfl⟩

/-- **The homomorphism property away from equal values** (the proven
vertical and chord branches; the doubling branch is excluded by the
hypothesis, following Silverman's completion-lemma strategy). -/
theorem pointMap_mul_of_ne [DecidableEq k] (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1) (hv0 : v₀ ≠ 0) (hv1 : v₀ ≠ 1)
    (hq0 : q₀ ≠ 0) (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1)
    (hne1 : pointMap q₀ hq0 hq1 u₀ hu0 ≠ pointMap q₀ hq0 hq1 v₀ hv0)
    (hne2 : pointMap q₀ hq0 hq1 u₀ hu0 ≠
      -pointMap q₀ hq0 hq1 v₀ hv0) :
    pointMap q₀ hq0 hq1 (u₀ * v₀) (mul_ne_zero hu0 hv0) =
      pointMap q₀ hq0 hq1 u₀ hu0 + pointMap q₀ hq0 hq1 v₀ hv0 := by
  have hqv : valuation k q₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have hqpos : (0 : ValueGroupWithZero k) < valuation k q₀ :=
    zero_lt_iff.mpr hqv
  have huv : valuation k u₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hu0
  have hupos : (0 : ValueGroupWithZero k) < valuation k u₀ :=
    zero_lt_iff.mpr huv
  have huq : u₀ ≠ q₀ := fun h => absurd hulow (by rw [h]; exact lt_irrefl _)
  have hvq : v₀ ≠ q₀ := fun h => absurd hvlow (by rw [h]; exact lt_irrefl _)
  have hsq_lt : valuation k q₀ * valuation k q₀ < valuation k q₀ :=
    by
      calc valuation k q₀ * valuation k q₀ < 1 * valuation k q₀ :=
            (OrderIso.mulRight₀ _ hqpos).strictMono hq1
        _ = valuation k q₀ := one_mul _
  have hulow2 : valuation k q₀ * valuation k q₀ < valuation k u₀ :=
    lt_trans hsq_lt hulow
  have hvlow2 : valuation k q₀ * valuation k q₀ < valuation k v₀ :=
    lt_trans hsq_lt hvlow
  have hw0 : u₀ * v₀ ≠ 0 := mul_ne_zero hu0 hv0
  have hwlow : valuation k q₀ * valuation k q₀ < valuation k (u₀ * v₀) := by
    rw [map_mul]
    calc valuation k q₀ * valuation k q₀
        < valuation k u₀ * valuation k q₀ :=
          (OrderIso.mulRight₀ _ hqpos).strictMono hulow
      _ < valuation k u₀ * valuation k v₀ :=
          (OrderIso.mulLeft₀ _ hupos).strictMono hvlow
  have hwhigh : valuation k (u₀ * v₀) ≤ 1 := by
    rw [map_mul]
    exact mul_le_one' huhigh hvhigh
  rw [pointMap_eq_bilateral u₀ q₀ hu0 hu1 huq hq0 hq1 hulow2 huhigh,
    pointMap_eq_bilateral v₀ q₀ hv0 hv1 hvq hq0 hq1 hvlow2 hvhigh]
  by_cases htriv : u₀ * v₀ = 1 ∨ u₀ * v₀ = q₀
  · obtain ⟨hXeq, hYeq⟩ := bilateral_negY_of_mul_trivial u₀ v₀ q₀
      hu0 hu1 hv0 hq0 hq1 hulow huhigh htriv
    rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hXeq.symm
      (by rw [hYeq, hXeq, WeierstrassCurve.Affine.negY_negY])]
    rcases htriv with h1 | hqc
    · rw [show pointMap q₀ hq0 hq1 (u₀ * v₀) (mul_ne_zero hu0 hv0) =
        pointMap q₀ hq0 hq1 1 one_ne_zero from pointMap_congr h1]
      exact pointMap_one q₀ hq0 hq1
    · rw [show pointMap q₀ hq0 hq1 (u₀ * v₀) (mul_ne_zero hu0 hv0) =
        pointMap q₀ hq0 hq1 q₀ hq0 from pointMap_congr hqc]
      exact (pointMap_eq_zero_iff q₀ hq0 hq1 q₀ hq0).mpr ⟨1, (zpow_one _).symm⟩
  · rw [not_or] at htriv
    obtain ⟨hw1, hwq⟩ := htriv
    rw [pointMap_eq_bilateral (u₀ * v₀) q₀ hw0 hw1 hwq hq0 hq1 hwlow hwhigh]
    by_cases hX : bilateralX u₀ q₀ = bilateralX v₀ q₀
    · -- equal `x`-values: the `y`-dichotomy contradicts one of the
      -- two exclusion hypotheses
      exfalso
      have hequ : (WeierstrassCurve.tateCurve q₀).toAffine.Equation
          (bilateralX u₀ q₀) (bilateralY u₀ q₀) :=
        (nonsingular_bilateral u₀ q₀ hu0 hu1 huq hq0 hq1 hulow2 huhigh).1
      have heqv : (WeierstrassCurve.tateCurve q₀).toAffine.Equation
          (bilateralX v₀ q₀) (bilateralY v₀ q₀) :=
        (nonsingular_bilateral v₀ q₀ hv0 hv1 hvq hq0 hq1 hvlow2 hvhigh).1
      rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hequ heqv hX with hy | hy
      · refine hne1 ?_
        rw [pointMap_eq_bilateral u₀ q₀ hu0 hu1 huq hq0 hq1 hulow2 huhigh,
          pointMap_eq_bilateral v₀ q₀ hv0 hv1 hvq hq0 hq1 hvlow2 hvhigh]
        exact point_some_congr hX hy
      · refine hne2 ?_
        rw [pointMap_eq_bilateral u₀ q₀ hu0 hu1 huq hq0 hq1 hulow2 huhigh,
          pointMap_eq_bilateral v₀ q₀ hv0 hv1 hvq hq0 hq1 hvlow2 hvhigh,
          WeierstrassCurve.Affine.Point.neg_some]
        exact point_some_congr hX hy
    · obtain ⟨hXX, hYY⟩ := bilateral_add_of_X_ne u₀ v₀ q₀ hu0 hv0 hq0 hu1 hv1
        hq1 hulow huhigh hvlow hvhigh hX
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne hX]
      exact point_some_congr hXX hYY

/-- **The homomorphism property of the point map** (Silverman ATAEC
V.3.1(c)): derived from the vertical and chord cases through the
completion lemma `hom_of_partial_hom` — no doubling formula and no
injectivity are needed. -/
theorem pointMap_mul [DecidableEq k] (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (_hu1 : u₀ ≠ 1) (hv0 : v₀ ≠ 0) (_hv1 : v₀ ≠ 1)
    (hq0 : q₀ ≠ 0) (hq1 : valuation k q₀ < 1)
    (_hulow : valuation k q₀ < valuation k u₀)
    (_huhigh : valuation k u₀ ≤ 1)
    (_hvlow : valuation k q₀ < valuation k v₀)
    (_hvhigh : valuation k v₀ ≤ 1) :
    pointMap q₀ hq0 hq1 (u₀ * v₀) (mul_ne_zero hu0 hv0) =
      pointMap q₀ hq0 hq1 u₀ hu0 + pointMap q₀ hq0 hq1 v₀ hv0 := by
  classical
  have hpart : ∀ x y : kˣ,
      pointMap q₀ hq0 hq1 (x : k) x.ne_zero ≠
        pointMap q₀ hq0 hq1 (y : k) y.ne_zero →
      pointMap q₀ hq0 hq1 (x : k) x.ne_zero ≠
        -pointMap q₀ hq0 hq1 (y : k) y.ne_zero →
      pointMap q₀ hq0 hq1 ((x * y : kˣ) : k) (x * y).ne_zero =
        pointMap q₀ hq0 hq1 (x : k) x.ne_zero +
        pointMap q₀ hq0 hq1 (y : k) y.ne_zero := by
    intro x y hne1 hne2
    obtain ⟨mx, hx1, hx2⟩ :=
      exists_zpow_mul_mem_annulus q₀ hq0 hq1 (x : k) x.ne_zero
    obtain ⟨my, hy1, hy2⟩ :=
      exists_zpow_mul_mem_annulus q₀ hq0 hq1 (y : k) y.ne_zero
    set x' : k := (x : k) * q₀ ^ (-mx) with hx'def
    set y' : k := (y : k) * q₀ ^ (-my) with hy'def
    have hx'0 : x' ≠ 0 := mul_ne_zero x.ne_zero (zpow_ne_zero _ hq0)
    have hy'0 : y' ≠ 0 := mul_ne_zero y.ne_zero (zpow_ne_zero _ hq0)
    have hxeq : pointMap q₀ hq0 hq1 x' hx'0 =
        pointMap q₀ hq0 hq1 (x : k) x.ne_zero := by
      rw [pointMap_congr (show x' = q₀ ^ (-mx) * (x : k) from by
        rw [hx'def]; ring)]
      exact pointMap_zpow_mul q₀ hq0 hq1 (x : k) x.ne_zero (-mx)
    have hyeq : pointMap q₀ hq0 hq1 y' hy'0 =
        pointMap q₀ hq0 hq1 (y : k) y.ne_zero := by
      rw [pointMap_congr (show y' = q₀ ^ (-my) * (y : k) from by
        rw [hy'def]; ring)]
      exact pointMap_zpow_mul q₀ hq0 hq1 (y : k) y.ne_zero (-my)
    have hprodeq : pointMap q₀ hq0 hq1 (x' * y')
        (mul_ne_zero hx'0 hy'0) =
        pointMap q₀ hq0 hq1 ((x * y : kˣ) : k) (x * y).ne_zero := by
      rw [pointMap_congr (show x' * y' =
          q₀ ^ (-(mx + my)) * ((x * y : kˣ) : k) from by
        rw [hx'def, hy'def, Units.val_mul, neg_add, zpow_add₀ hq0]
        ring)]
      exact pointMap_zpow_mul q₀ hq0 hq1 _ (x * y).ne_zero (-(mx + my))
    by_cases hx'1 : x' = 1
    · have hx0' : pointMap q₀ hq0 hq1 (x : k) x.ne_zero = 0 := by
        rw [← hxeq, pointMap_congr hx'1]
        exact pointMap_one q₀ hq0 hq1
      rw [hx0', zero_add]
      calc pointMap q₀ hq0 hq1 ((x * y : kˣ) : k) (x * y).ne_zero
          = pointMap q₀ hq0 hq1 (x' * y') (mul_ne_zero hx'0 hy'0) :=
            hprodeq.symm
        _ = pointMap q₀ hq0 hq1 y' hy'0 :=
            pointMap_congr (by rw [hx'1, one_mul])
        _ = pointMap q₀ hq0 hq1 (y : k) y.ne_zero := hyeq
    · by_cases hy'1 : y' = 1
      · have hy0' : pointMap q₀ hq0 hq1 (y : k) y.ne_zero = 0 := by
          rw [← hyeq, pointMap_congr hy'1]
          exact pointMap_one q₀ hq0 hq1
        rw [hy0', add_zero]
        calc pointMap q₀ hq0 hq1 ((x * y : kˣ) : k) (x * y).ne_zero
            = pointMap q₀ hq0 hq1 (x' * y') (mul_ne_zero hx'0 hy'0) :=
              hprodeq.symm
          _ = pointMap q₀ hq0 hq1 x' hx'0 :=
              pointMap_congr (by rw [hy'1, mul_one])
          _ = pointMap q₀ hq0 hq1 (x : k) x.ne_zero := hxeq
      · have hne1' : pointMap q₀ hq0 hq1 x' hx'0 ≠
            pointMap q₀ hq0 hq1 y' hy'0 := by
          rw [hxeq, hyeq]
          exact hne1
        have hne2' : pointMap q₀ hq0 hq1 x' hx'0 ≠
            -pointMap q₀ hq0 hq1 y' hy'0 := by
          rw [hxeq, hyeq]
          exact hne2
        have h := pointMap_mul_of_ne x' y' q₀ hx'0 hx'1 hy'0 hy'1 hq0 hq1
          hx1 hx2 hy1 hy2 hne1' hne2'
        rw [← hprodeq, h, hxeq, hyeq]
  have htotal := hom_of_partial_hom
    (fun x : kˣ => pointMap q₀ hq0 hq1 (x : k) x.ne_zero)
    (pointMap_range_infinite q₀ hq0 hq1) hpart
    (Units.mk0 u₀ hu0) (Units.mk0 v₀ hv0)
  simp only [Units.val_mul, Units.val_mk0] at htotal
  exact htotal

/-- **The homomorphism property of the uniformisation** (DERIVED
2026-07-18 from the sorried chord/tangent/fibre leaves above — the addition
law, Silverman V.3.1(c)): the point map on `kˣ/q^ℤ` turns multiplication of
unit classes into addition on the Tate curve. The quotient bookkeeping
(normalisation into the fundamental annulus by `pointMap_zpow_mul`, the
trivial classes) is handled here; the geometric content is
`pointMap_mul`. -/
theorem pointMapQuot_add [DecidableEq k] (q : kˣ)
    (hq : valuation k (q : k) < 1)
    (x y : kˣ ⧸ Subgroup.zpowers q) :
    pointMapQuot q hq (x * y) =
      pointMapQuot q hq x + pointMapQuot q hq y := by
  have hq0 : (q : k) ≠ 0 := q.ne_zero
  induction x using QuotientGroup.induction_on with
  | H u =>
  induction y using QuotientGroup.induction_on with
  | H v =>
  rw [show ((QuotientGroup.mk u : kˣ ⧸ Subgroup.zpowers q) *
      QuotientGroup.mk v) = QuotientGroup.mk (u * v) from rfl,
    pointMapQuot_mk, pointMapQuot_mk, pointMapQuot_mk]
  -- normalise `u` and `v` into the fundamental annulus
  obtain ⟨cu, hcu1, hcu2⟩ :=
    exists_zpow_mul_mem_annulus (q : k) hq0 hq (u : k) u.ne_zero
  obtain ⟨cv, hcv1, hcv2⟩ :=
    exists_zpow_mul_mem_annulus (q : k) hq0 hq (v : k) v.ne_zero
  set u' : k := (u : k) * (q : k) ^ (-cu) with hu'def
  set v' : k := (v : k) * (q : k) ^ (-cv) with hv'def
  have hu'0 : u' ≠ 0 := mul_ne_zero u.ne_zero (zpow_ne_zero _ hq0)
  have hv'0 : v' ≠ 0 := mul_ne_zero v.ne_zero (zpow_ne_zero _ hq0)
  have hu'eq : (q : k) ^ cu * u' = (u : k) := by
    rw [hu'def, mul_comm ((u : k)) _, ← mul_assoc, ← zpow_add₀ hq0]
    simp
  have hv'eq : (q : k) ^ cv * v' = (v : k) := by
    rw [hv'def, mul_comm ((v : k)) _, ← mul_assoc, ← zpow_add₀ hq0]
    simp
  -- the point map only sees the annulus representatives
  have hnu : pointMap (q : k) hq0 hq (u : k) u.ne_zero =
      pointMap (q : k) hq0 hq u' hu'0 := by
    calc pointMap (q : k) hq0 hq (u : k) u.ne_zero
        = pointMap (q : k) hq0 hq ((q : k) ^ cu * u')
          (mul_ne_zero (zpow_ne_zero _ hq0) hu'0) :=
          pointMap_congr hu'eq.symm
      _ = pointMap (q : k) hq0 hq u' hu'0 :=
          pointMap_zpow_mul (q : k) hq0 hq u' hu'0 cu
  have hnv : pointMap (q : k) hq0 hq (v : k) v.ne_zero =
      pointMap (q : k) hq0 hq v' hv'0 := by
    calc pointMap (q : k) hq0 hq (v : k) v.ne_zero
        = pointMap (q : k) hq0 hq ((q : k) ^ cv * v')
          (mul_ne_zero (zpow_ne_zero _ hq0) hv'0) :=
          pointMap_congr hv'eq.symm
      _ = pointMap (q : k) hq0 hq v' hv'0 :=
          pointMap_zpow_mul (q : k) hq0 hq v' hv'0 cv
  have hnuv : pointMap (q : k) hq0 hq ((u : k) * (v : k))
      (mul_ne_zero u.ne_zero v.ne_zero) =
      pointMap (q : k) hq0 hq (u' * v') (mul_ne_zero hu'0 hv'0) := by
    have heq : (q : k) ^ (cu + cv) * (u' * v') = (u : k) * (v : k) := by
      rw [zpow_add₀ hq0]
      calc (q : k) ^ cu * (q : k) ^ cv * (u' * v')
          = ((q : k) ^ cu * u') * ((q : k) ^ cv * v') := by ring
        _ = (u : k) * (v : k) := by rw [hu'eq, hv'eq]
    exact (pointMap_congr heq.symm).trans
      (pointMap_zpow_mul (q : k) hq0 hq (u' * v')
        (mul_ne_zero hu'0 hv'0) (cu + cv))
  have hmulc : pointMap (q : k) hq0 hq ((u : k) * (v : k))
      (mul_ne_zero u.ne_zero v.ne_zero) =
      pointMap (q : k) hq0 hq ((u * v : kˣ) : k) (u * v).ne_zero :=
    pointMap_congr (by push_cast; ring)
  rw [← hmulc, hnu, hnv, hnuv]
  -- trivial-class cases
  by_cases hu'1 : u' = 1
  · rw [show pointMap (q : k) hq0 hq u' hu'0 = 0 from by
      rw [pointMap_congr hu'1]; exact pointMap_one (q : k) hq0 hq]
    rw [show pointMap (q : k) hq0 hq (u' * v') (mul_ne_zero hu'0 hv'0) =
      pointMap (q : k) hq0 hq v' hv'0 from
      pointMap_congr (by rw [hu'1, one_mul]), zero_add]
  by_cases hv'1 : v' = 1
  · rw [show pointMap (q : k) hq0 hq v' hv'0 = 0 from by
      rw [pointMap_congr hv'1]; exact pointMap_one (q : k) hq0 hq]
    rw [show pointMap (q : k) hq0 hq (u' * v') (mul_ne_zero hu'0 hv'0) =
      pointMap (q : k) hq0 hq u' hu'0 from
      pointMap_congr (by rw [hv'1, mul_one]), add_zero]
  exact pointMap_mul u' v' (q : k) hu'0 hu'1 hv'0 hv'1 hq0 hq
    hcu1 hcu2 hcv1 hcv2

/-- The image of the trivial class is zero. -/
theorem pointMapQuot_one (q : kˣ) (hq : valuation k (q : k) < 1) :
    pointMapQuot q hq 1 = 0 := by
  have h : (1 : kˣ ⧸ Subgroup.zpowers q) = QuotientGroup.mk 1 := rfl
  rw [h, pointMapQuot_mk]
  have h1 : ((1 : kˣ) : k) = 1 := rfl
  rw [pointMap_congr h1]
  exact pointMap_one (q : k) q.ne_zero hq

set_option maxHeartbeats 1000000 in
/-- **`x`-surjectivity, identity-component case** (PROVEN 2026-07-20 —
Silverman ATAEC V.4, the formal-group half): if `|x| ≥ 1` then `x` is a
`bilateralX`-value on the unit shell. The proof runs the nodal linear
solve `t' = (y - T_Y u)/(x - T_X u)`, `F u = t'/(1+t')` (the
`y`-coordinate selects the branch, so no square-root existence or
characteristic hypotheses are needed): the tails `T_X`, `T_Y` of the
bilateral series beyond their nodal leading terms are bounded by `|q₀|`
and are `|q₀|`-Lipschitz on the shell; `F` is then a `|q₀|`-contraction
fixing the shell, its orbit from the seed `y/(x+y)` converges in the
complete field, and at the fixed point the defect `x - bilateralX u`
satisfies the division-free identity `ε·D² = D³ - N·S` (bounded by
`|q₀|` through the Tate equation) and the factored exclusion identity
`ε·B = 0` with `|B| = |x|²` (the bracket identity
`3Xl² - tXl - 2tYl - Yl = u²/(1-u)⁴` dominates all corrections), so
`ε = 0`. -/
theorem exists_annulus_bilateralX_eq_of_one_le (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq1 : valuation k q₀ < 1) (x y : k)
    (hxy : (WeierstrassCurve.tateCurve q₀).toAffine.Equation x y)
    (hx : 1 ≤ valuation k x) :
    ∃ u : k, u ≠ 0 ∧ u ≠ 1 ∧ valuation k q₀ < valuation k u ∧
      valuation k u ≤ 1 ∧ bilateralX u q₀ = x := by
  -- Step 1 (tail bound): on the unit shell the bilateral series deviates
  -- from its nodal leading term `u/(1-u)²` by at most `|q₀|` — every
  -- shell term `q₀^m u^{±1}/(1-q₀^m u^{±1})²` has a unit denominator
  -- (`|q₀^m u^{±1}| < 1`) and numerator of valuation `|q₀|^m`, and the
  -- divisor-sum series is bounded by `|q₀|` outright
  -- (`valuation_tsum_le` on each of the three constituent series).
  have htsum_pnat : ∀ (f : ℕ+ → k), Summable f →
      ∀ c : ValueGroupWithZero k, (∀ m, valuation k (f m) ≤ c) →
      valuation k (∑' m, f m) ≤ c :=
    fun f hf c hb => valuation_tsum_le hf c hb
  have hqpow_le : ∀ N : ℕ+, valuation k q₀ ^ (N : ℕ) ≤ valuation k q₀ := by
    intro N
    calc valuation k q₀ ^ (N : ℕ) ≤ valuation k q₀ ^ (1 : ℕ) :=
        pow_le_pow_right_of_le_one' (le_of_lt hq1) N.2
      _ = valuation k q₀ := pow_one _
  have hterm_le : ∀ (w : k), valuation k w = 1 → ∀ m : ℕ+,
      valuation k (q₀ ^ (m : ℕ) * w / (1 - q₀ ^ (m : ℕ) * w) ^ 2) ≤
        valuation k q₀ := by
    intro w hw m
    have hsmall : valuation k (q₀ ^ (m : ℕ) * w) < 1 := by
      rw [map_mul, map_pow, hw, mul_one]
      exact pow_lt_one₀ zero_le hq1 m.ne_zero
    rw [map_div₀, map_mul, map_pow, hw, mul_one, map_pow,
      (valuation k).map_one_sub_of_lt hsmall, one_pow, div_one]
    exact hqpow_le m
  have htail : ∀ u : k, valuation k u = 1 → u ≠ 1 →
      valuation k (bilateralX u q₀ - u / (1 - u) ^ 2) ≤
        valuation k q₀ := by
    intro u hu hu1
    have huinv : valuation k u⁻¹ = 1 := by
      rw [map_inv₀, hu, inv_one]
    have hqu : valuation k (q₀ * u) < 1 := by
      rw [map_mul, hu, mul_one]
      exact hq1
    have hquinv : valuation k (q₀ * u⁻¹) < 1 := by
      rw [map_mul, huinv, mul_one]
      exact hq1
    rw [bilateralX, add_sub_cancel_left]
    have hS1 : valuation k
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 2) ≤
          valuation k q₀ :=
      htsum_pnat _ (summable_lambert_terms u q₀ hq1 hqu) _
        (hterm_le u hu)
    have hS2 : valuation k
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * u⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 2) ≤ valuation k q₀ :=
      htsum_pnat _ (summable_lambert_terms u⁻¹ q₀ hq1 hquinv) _
        (hterm_le u⁻¹ huinv)
    have hS3 : valuation k
        (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ)) ≤ valuation k q₀ := by
      refine htsum_pnat _ (summable_sigma_one_nonarch q₀ hq1) _ ?_
      intro N
      rw [map_mul, map_pow]
      have hd1 : valuation k (∑ d ∈ (N : ℕ).divisors, (d : k)) ≤ 1 :=
        Valuation.map_sum_le _ fun d _ => by
          simpa using valuation_intCast_le_one (R := k) d
      calc valuation k (∑ d ∈ (N : ℕ).divisors, (d : k)) *
            valuation k q₀ ^ (N : ℕ)
          ≤ 1 * valuation k q₀ ^ (N : ℕ) := mul_le_mul_left hd1 _
        _ = valuation k q₀ ^ (N : ℕ) := one_mul _
        _ ≤ valuation k q₀ := hqpow_le N
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · exact le_trans (Valuation.map_add _ _ _) (max_le hS1 hS2)
    · rw [map_mul]
      calc valuation k 2 * valuation k
            (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
              q₀ ^ (N : ℕ))
          ≤ 1 * valuation k q₀ := by
            refine mul_le_mul' ?_ hS3
            simpa using valuation_intCast_le_one (R := k) 2
        _ = valuation k q₀ := one_mul _
  -- Step 2 (Lipschitz bound): the deviation is `|q₀|`-Lipschitz on the
  -- unit shell, by the algebraic identity
  -- `u/(1-au)² - v/(1-av)² = (u-v)(1-a²uv)/((1-au)²(1-av)²)` applied
  -- termwise with `a = q₀^m` (and `|u⁻¹-v⁻¹| = |u-v|` on the shell for
  -- the inverse-parameter half; the divisor-sum series cancels).
  have hone_sub_ne : ∀ x : k, valuation k x < 1 → 1 - x ≠ 0 := by
    intro x hx hh
    have h1 := (valuation k).map_one_sub_of_lt hx
    rw [hh, map_zero] at h1
    exact zero_ne_one h1
  have hkey : ∀ a w z : k, 1 - a * w ≠ 0 → 1 - a * z ≠ 0 →
      a * w / (1 - a * w) ^ 2 - a * z / (1 - a * z) ^ 2 =
        a * (w - z) * (1 - a ^ 2 * w * z) /
          ((1 - a * w) ^ 2 * (1 - a * z) ^ 2) := by
    intro a w z h1 h2
    field_simp
    ring
  have hterm_diff_le : ∀ (w z : k), valuation k w = 1 →
      valuation k z = 1 → ∀ m : ℕ+, valuation k
        (q₀ ^ (m : ℕ) * w / (1 - q₀ ^ (m : ℕ) * w) ^ 2 -
         q₀ ^ (m : ℕ) * z / (1 - q₀ ^ (m : ℕ) * z) ^ 2) ≤
        valuation k q₀ * valuation k (w - z) := by
    intro w z hw hz m
    have hsw : valuation k (q₀ ^ (m : ℕ) * w) < 1 := by
      rw [map_mul, map_pow, hw, mul_one]
      exact pow_lt_one₀ zero_le hq1 m.ne_zero
    have hsz : valuation k (q₀ ^ (m : ℕ) * z) < 1 := by
      rw [map_mul, map_pow, hz, mul_one]
      exact pow_lt_one₀ zero_le hq1 m.ne_zero
    have hswz : valuation k ((q₀ ^ (m : ℕ)) ^ 2 * w * z) < 1 := by
      rw [map_mul, map_mul, map_pow, map_pow, hw, hz, mul_one, mul_one]
      exact pow_lt_one₀ zero_le
        (pow_lt_one₀ zero_le hq1 m.ne_zero) two_ne_zero
    rw [hkey _ _ _ (hone_sub_ne _ hsw) (hone_sub_ne _ hsz), map_div₀,
      map_mul, map_mul, map_mul]
    simp only [map_pow]
    rw [(valuation k).map_one_sub_of_lt hsw,
      (valuation k).map_one_sub_of_lt hsz,
      (valuation k).map_one_sub_of_lt hswz]
    simp only [one_pow, mul_one, div_one]
    exact mul_le_mul_left (hqpow_le m) _
  have hlip : ∀ u v : k, valuation k u = 1 → valuation k v = 1 →
      u ≠ 1 → v ≠ 1 →
      valuation k ((bilateralX u q₀ - u / (1 - u) ^ 2) -
          (bilateralX v q₀ - v / (1 - v) ^ 2)) ≤
        valuation k q₀ * valuation k (u - v) := by
    intro u v hu hv hu1 hv1
    have hu0 : u ≠ 0 := by
      intro hh
      rw [hh, map_zero] at hu
      exact zero_ne_one hu
    have hv0 : v ≠ 0 := by
      intro hh
      rw [hh, map_zero] at hv
      exact zero_ne_one hv
    have huinv : valuation k u⁻¹ = 1 := by rw [map_inv₀, hu, inv_one]
    have hvinv : valuation k v⁻¹ = 1 := by rw [map_inv₀, hv, inv_one]
    have hqu : valuation k (q₀ * u) < 1 := by
      rw [map_mul, hu, mul_one]; exact hq1
    have hqv : valuation k (q₀ * v) < 1 := by
      rw [map_mul, hv, mul_one]; exact hq1
    have hquinv : valuation k (q₀ * u⁻¹) < 1 := by
      rw [map_mul, huinv, mul_one]; exact hq1
    have hqvinv : valuation k (q₀ * v⁻¹) < 1 := by
      rw [map_mul, hvinv, mul_one]; exact hq1
    have hinvdiff : valuation k (u⁻¹ - v⁻¹) = valuation k (u - v) := by
      have he : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by
        field_simp
      rw [he, map_div₀, map_mul, hu, hv, mul_one, div_one,
        ← Valuation.map_neg, neg_sub]
    have hSu1 := summable_lambert_terms u q₀ hq1 hqu
    have hSv1 := summable_lambert_terms v q₀ hq1 hqv
    have hSu2 := summable_lambert_terms u⁻¹ q₀ hq1 hquinv
    have hSv2 := summable_lambert_terms v⁻¹ q₀ hq1 hqvinv
    have e1 : bilateralX u q₀ - u / (1 - u) ^ 2 =
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 2) +
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * u⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 2) -
        2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ)) := by
      rw [bilateralX]
      ring
    have e2 : bilateralX v q₀ - v / (1 - v) ^ 2 =
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * v / (1 - q₀ ^ (m : ℕ) * v) ^ 2) +
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * v⁻¹ /
          (1 - q₀ ^ (m : ℕ) * v⁻¹) ^ 2) -
        2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ)) := by
      rw [bilateralX]
      ring
    rw [e1, e2, show ∀ A B C A' B' : k,
        (A + B - 2 * C) - (A' + B' - 2 * C) = (A - A') + (B - B') from
      fun A B C A' B' => by ring]
    rw [← hSu1.tsum_sub hSv1, ← hSu2.tsum_sub hSv2]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · exact valuation_tsum_le (hSu1.sub hSv1) _
        (fun m => hterm_diff_le u v hu hv m)
    · refine le_trans (valuation_tsum_le (hSu2.sub hSv2) _
        (fun m => hterm_diff_le u⁻¹ v⁻¹ huinv hvinv m)) ?_
      rw [hinvdiff]
  -- Y-series analogues of Steps 1–2, needed for the linear solve
  -- `t = (y - T_Y(u))/(x - T_X(u))` in Step 3 (which avoids any
  -- quadratic branch selection).
  have hqpow_le_nat : ∀ n : ℕ, n ≠ 0 →
      valuation k q₀ ^ n ≤ valuation k q₀ := by
    intro n hn
    calc valuation k q₀ ^ n ≤ valuation k q₀ ^ (1 : ℕ) :=
        pow_le_pow_right_of_le_one' (le_of_lt hq1) (Nat.one_le_iff_ne_zero.mpr hn)
      _ = valuation k q₀ := pow_one _
  have hbin1 : ∀ j : ℕ, valuation k (((j.choose 2 : ℕ) : k)) ≤ 1 := by
    intro j
    simpa using valuation_intCast_le_one (R := k) (j.choose 2)
  have hbin2 : ∀ j : ℕ, valuation k ((((j + 1).choose 2 : ℕ) : k)) ≤ 1 := by
    intro j
    simpa using valuation_intCast_le_one (R := k) ((j + 1).choose 2)
  have hS3sum : Summable (fun N : ℕ+ ↦
      (∑ d ∈ (N : ℕ).divisors, (d : k)) * q₀ ^ (N : ℕ)) :=
    summable_sigma_one_nonarch q₀ hq1
  have hS3le : valuation k
      (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
        q₀ ^ (N : ℕ)) ≤ valuation k q₀ := by
    refine htsum_pnat _ hS3sum _ ?_
    intro N
    rw [map_mul, map_pow]
    have hd1 : valuation k (∑ d ∈ (N : ℕ).divisors, (d : k)) ≤ 1 :=
      Valuation.map_sum_le _ fun d _ => by
        simpa using valuation_intCast_le_one (R := k) d
    calc valuation k (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          valuation k q₀ ^ (N : ℕ)
        ≤ 1 * valuation k q₀ ^ (N : ℕ) := mul_le_mul_left hd1 _
      _ = valuation k q₀ ^ (N : ℕ) := one_mul _
      _ ≤ valuation k q₀ := hqpow_le N
  have htermY1_le : ∀ (w : k), valuation k w = 1 → ∀ m : ℕ+,
      valuation k ((q₀ ^ (m : ℕ) * w) ^ 2 /
        (1 - q₀ ^ (m : ℕ) * w) ^ 3) ≤ valuation k q₀ := by
    intro w hw m
    have hsmall : valuation k (q₀ ^ (m : ℕ) * w) < 1 := by
      rw [map_mul, map_pow, hw, mul_one]
      exact pow_lt_one₀ zero_le hq1 m.ne_zero
    rw [map_div₀, map_pow, map_pow,
      (valuation k).map_one_sub_of_lt hsmall, one_pow, div_one,
      map_mul, map_pow, hw, mul_one, ← pow_mul]
    exact hqpow_le_nat _ (by positivity)
  have htermY2_le : ∀ (w : k), valuation k w = 1 → ∀ m : ℕ+,
      valuation k (q₀ ^ (m : ℕ) * w /
        (1 - q₀ ^ (m : ℕ) * w) ^ 3) ≤ valuation k q₀ := by
    intro w hw m
    have hsmall : valuation k (q₀ ^ (m : ℕ) * w) < 1 := by
      rw [map_mul, map_pow, hw, mul_one]
      exact pow_lt_one₀ zero_le hq1 m.ne_zero
    rw [map_div₀, map_pow,
      (valuation k).map_one_sub_of_lt hsmall, one_pow, div_one,
      map_mul, map_pow, hw, mul_one]
    exact hqpow_le m
  have htailY : ∀ u : k, valuation k u = 1 → u ≠ 1 →
      valuation k (bilateralY u q₀ - u ^ 2 / (1 - u) ^ 3) ≤
        valuation k q₀ := by
    intro u hu hu1
    have huinv : valuation k u⁻¹ = 1 := by
      rw [map_inv₀, hu, inv_one]
    have hqu : valuation k (q₀ * u) < 1 := by
      rw [map_mul, hu, mul_one]; exact hq1
    have hquinv : valuation k (q₀ * u⁻¹) < 1 := by
      rw [map_mul, huinv, mul_one]; exact hq1
    have hSY1 : Summable (fun m : ℕ+ ↦
        (q₀ ^ (m : ℕ) * u) ^ 2 / (1 - q₀ ^ (m : ℕ) * u) ^ 3) :=
      summable_lambert_terms_general
        (fun j ↦ ((j.choose 2 : ℕ) : k)) (fun v ↦ v ^ 2 / (1 - v) ^ 3)
        hbin1 u q₀ hq1 hqu
        (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_self v₀ hv₀)
    have hSY2 : Summable (fun m : ℕ+ ↦
        q₀ ^ (m : ℕ) * u⁻¹ / (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) :=
      summable_lambert_terms_general
        (fun j ↦ (((j + 1).choose 2 : ℕ) : k)) (fun v ↦ v / (1 - v) ^ 3)
        hbin2 u⁻¹ q₀ hq1 hquinv
        (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_succ v₀ hv₀)
    rw [bilateralY, add_sub_cancel_left]
    have hb1 : valuation k
        (∑' m : ℕ+, (q₀ ^ (m : ℕ) * u) ^ 2 /
          (1 - q₀ ^ (m : ℕ) * u) ^ 3) ≤ valuation k q₀ :=
      htsum_pnat _ hSY1 _ (htermY1_le u hu)
    have hb2 : valuation k
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * u⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) ≤ valuation k q₀ :=
      htsum_pnat _ hSY2 _ (htermY2_le u⁻¹ huinv)
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hS3le)
    exact le_trans (Valuation.map_sub _ _ _) (max_le hb1 hb2)
  have hkeyY1 : ∀ a w z : k, 1 - a * w ≠ 0 → 1 - a * z ≠ 0 →
      (a * w) ^ 2 / (1 - a * w) ^ 3 - (a * z) ^ 2 / (1 - a * z) ^ 3 =
        a ^ 2 * (w - z) * ((w + z) - 3 * a * w * z + a ^ 3 * w ^ 2 * z ^ 2) /
          ((1 - a * w) ^ 3 * (1 - a * z) ^ 3) := by
    intro a w z h1 h2
    field_simp
    ring
  have hkeyY2 : ∀ a w z : k, 1 - a * w ≠ 0 → 1 - a * z ≠ 0 →
      a * w / (1 - a * w) ^ 3 - a * z / (1 - a * z) ^ 3 =
        a * (w - z) * (1 - 3 * a ^ 2 * w * z + a ^ 3 * w * z * (w + z)) /
          ((1 - a * w) ^ 3 * (1 - a * z) ^ 3) := by
    intro a w z h1 h2
    field_simp
    ring
  have htermY1_diff_le : ∀ (w z : k), valuation k w = 1 →
      valuation k z = 1 → ∀ m : ℕ+, valuation k
        ((q₀ ^ (m : ℕ) * w) ^ 2 / (1 - q₀ ^ (m : ℕ) * w) ^ 3 -
         (q₀ ^ (m : ℕ) * z) ^ 2 / (1 - q₀ ^ (m : ℕ) * z) ^ 3) ≤
        valuation k q₀ * valuation k (w - z) := by
    intro w z hw hz m
    have hsw : valuation k (q₀ ^ (m : ℕ) * w) < 1 := by
      rw [map_mul, map_pow, hw, mul_one]
      exact pow_lt_one₀ zero_le hq1 m.ne_zero
    have hsz : valuation k (q₀ ^ (m : ℕ) * z) < 1 := by
      rw [map_mul, map_pow, hz, mul_one]
      exact pow_lt_one₀ zero_le hq1 m.ne_zero
    rw [hkeyY1 _ _ _ (hone_sub_ne _ hsw) (hone_sub_ne _ hsz), map_div₀,
      map_mul, map_mul, map_mul]
    simp only [map_pow]
    rw [(valuation k).map_one_sub_of_lt hsw,
      (valuation k).map_one_sub_of_lt hsz]
    simp only [one_pow, mul_one, div_one]
    have hbr : valuation k
        ((w + z) - 3 * q₀ ^ (m : ℕ) * w * z +
          (q₀ ^ (m : ℕ)) ^ 3 * w ^ 2 * z ^ 2) ≤ 1 := by
      refine le_trans (Valuation.map_add _ _ _) (max_le
        (le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)) ?_)
      · exact le_trans (Valuation.map_add _ _ _) (max_le (le_of_eq hw)
          (le_of_eq hz))
      · simp only [map_mul, map_pow, hw, hz, mul_one]
        calc valuation k 3 * valuation k q₀ ^ (m : ℕ)
            ≤ 1 * 1 := mul_le_mul'
              (by simpa using valuation_intCast_le_one (R := k) 3)
              (le_trans (hqpow_le m) (le_of_lt hq1))
          _ = 1 := one_mul _
      · simp only [map_mul, map_pow, hw, hz, one_pow, mul_one]
        calc (valuation k q₀ ^ (m : ℕ)) ^ 3
            ≤ 1 ^ 3 := pow_le_pow_left' (le_trans (hqpow_le m)
              (le_of_lt hq1)) 3
          _ = 1 := one_pow _
    calc (valuation k q₀ ^ (m : ℕ)) ^ 2 * valuation k (w - z) *
          valuation k ((w + z) - 3 * q₀ ^ (m : ℕ) * w * z +
            (q₀ ^ (m : ℕ)) ^ 3 * w ^ 2 * z ^ 2)
        ≤ (valuation k q₀ ^ (m : ℕ)) ^ 2 * valuation k (w - z) * 1 :=
          mul_le_mul' (le_refl _) hbr
      _ = (valuation k q₀ ^ (m : ℕ)) ^ 2 * valuation k (w - z) :=
          mul_one _
      _ ≤ valuation k q₀ * valuation k (w - z) := by
          refine mul_le_mul_left ?_ _
          rw [← pow_mul]
          exact hqpow_le_nat _ (by positivity)
  have htermY2_diff_le : ∀ (w z : k), valuation k w = 1 →
      valuation k z = 1 → ∀ m : ℕ+, valuation k
        (q₀ ^ (m : ℕ) * w / (1 - q₀ ^ (m : ℕ) * w) ^ 3 -
         q₀ ^ (m : ℕ) * z / (1 - q₀ ^ (m : ℕ) * z) ^ 3) ≤
        valuation k q₀ * valuation k (w - z) := by
    intro w z hw hz m
    have hsw : valuation k (q₀ ^ (m : ℕ) * w) < 1 := by
      rw [map_mul, map_pow, hw, mul_one]
      exact pow_lt_one₀ zero_le hq1 m.ne_zero
    have hsz : valuation k (q₀ ^ (m : ℕ) * z) < 1 := by
      rw [map_mul, map_pow, hz, mul_one]
      exact pow_lt_one₀ zero_le hq1 m.ne_zero
    rw [hkeyY2 _ _ _ (hone_sub_ne _ hsw) (hone_sub_ne _ hsz), map_div₀,
      map_mul, map_mul, map_mul]
    simp only [map_pow]
    rw [(valuation k).map_one_sub_of_lt hsw,
      (valuation k).map_one_sub_of_lt hsz]
    simp only [one_pow, mul_one, div_one]
    have hbr : valuation k
        (1 - 3 * (q₀ ^ (m : ℕ)) ^ 2 * w * z +
          (q₀ ^ (m : ℕ)) ^ 3 * w * z * (w + z)) ≤ 1 := by
      refine le_trans (Valuation.map_add _ _ _) (max_le
        (le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)) ?_)
      · rw [map_one]
      · simp only [map_mul, map_pow, hw, hz, mul_one]
        calc valuation k 3 * (valuation k q₀ ^ (m : ℕ)) ^ 2
            ≤ 1 * 1 ^ 2 := mul_le_mul'
              (by simpa using valuation_intCast_le_one (R := k) 3)
              (pow_le_pow_left' (le_trans (hqpow_le m) (le_of_lt hq1)) 2)
          _ = 1 := by rw [one_pow, one_mul]
      · simp only [map_mul, map_pow, hw, hz, mul_one]
        calc (valuation k q₀ ^ (m : ℕ)) ^ 3 * valuation k (w + z)
            ≤ 1 ^ 3 * 1 := mul_le_mul'
              (pow_le_pow_left' (le_trans (hqpow_le m) (le_of_lt hq1)) 3)
              (le_trans (Valuation.map_add _ _ _) (max_le (le_of_eq hw)
                (le_of_eq hz)))
          _ = 1 := by rw [one_pow, one_mul]
    calc valuation k q₀ ^ (m : ℕ) * valuation k (w - z) *
          valuation k (1 - 3 * (q₀ ^ (m : ℕ)) ^ 2 * w * z +
            (q₀ ^ (m : ℕ)) ^ 3 * w * z * (w + z))
        ≤ valuation k q₀ ^ (m : ℕ) * valuation k (w - z) * 1 :=
          mul_le_mul' (le_refl _) hbr
      _ = valuation k q₀ ^ (m : ℕ) * valuation k (w - z) := mul_one _
      _ ≤ valuation k q₀ * valuation k (w - z) :=
          mul_le_mul_left (hqpow_le m) _
  have hlipY : ∀ u v : k, valuation k u = 1 → valuation k v = 1 →
      u ≠ 1 → v ≠ 1 →
      valuation k ((bilateralY u q₀ - u ^ 2 / (1 - u) ^ 3) -
          (bilateralY v q₀ - v ^ 2 / (1 - v) ^ 3)) ≤
        valuation k q₀ * valuation k (u - v) := by
    intro u v hu hv hu1 hv1
    have hu0 : u ≠ 0 := by
      intro hh
      rw [hh, map_zero] at hu
      exact zero_ne_one hu
    have hv0 : v ≠ 0 := by
      intro hh
      rw [hh, map_zero] at hv
      exact zero_ne_one hv
    have huinv : valuation k u⁻¹ = 1 := by rw [map_inv₀, hu, inv_one]
    have hvinv : valuation k v⁻¹ = 1 := by rw [map_inv₀, hv, inv_one]
    have hqu : valuation k (q₀ * u) < 1 := by
      rw [map_mul, hu, mul_one]; exact hq1
    have hqv : valuation k (q₀ * v) < 1 := by
      rw [map_mul, hv, mul_one]; exact hq1
    have hquinv : valuation k (q₀ * u⁻¹) < 1 := by
      rw [map_mul, huinv, mul_one]; exact hq1
    have hqvinv : valuation k (q₀ * v⁻¹) < 1 := by
      rw [map_mul, hvinv, mul_one]; exact hq1
    have hinvdiff : valuation k (u⁻¹ - v⁻¹) = valuation k (u - v) := by
      have he : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by
        field_simp
      rw [he, map_div₀, map_mul, hu, hv, mul_one, div_one,
        ← Valuation.map_neg, neg_sub]
    have hSY1u : Summable (fun m : ℕ+ ↦
        (q₀ ^ (m : ℕ) * u) ^ 2 / (1 - q₀ ^ (m : ℕ) * u) ^ 3) :=
      summable_lambert_terms_general
        (fun j ↦ ((j.choose 2 : ℕ) : k)) (fun v ↦ v ^ 2 / (1 - v) ^ 3)
        hbin1 u q₀ hq1 hqu
        (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_self v₀ hv₀)
    have hSY1v : Summable (fun m : ℕ+ ↦
        (q₀ ^ (m : ℕ) * v) ^ 2 / (1 - q₀ ^ (m : ℕ) * v) ^ 3) :=
      summable_lambert_terms_general
        (fun j ↦ ((j.choose 2 : ℕ) : k)) (fun w ↦ w ^ 2 / (1 - w) ^ 3)
        hbin1 v q₀ hq1 hqv
        (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_self v₀ hv₀)
    have hSY2u : Summable (fun m : ℕ+ ↦
        q₀ ^ (m : ℕ) * u⁻¹ / (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) :=
      summable_lambert_terms_general
        (fun j ↦ (((j + 1).choose 2 : ℕ) : k)) (fun v ↦ v / (1 - v) ^ 3)
        hbin2 u⁻¹ q₀ hq1 hquinv
        (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_succ v₀ hv₀)
    have hSY2v : Summable (fun m : ℕ+ ↦
        q₀ ^ (m : ℕ) * v⁻¹ / (1 - q₀ ^ (m : ℕ) * v⁻¹) ^ 3) :=
      summable_lambert_terms_general
        (fun j ↦ (((j + 1).choose 2 : ℕ) : k)) (fun w ↦ w / (1 - w) ^ 3)
        hbin2 v⁻¹ q₀ hq1 hqvinv
        (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_succ v₀ hv₀)
    have e1 : bilateralY u q₀ - u ^ 2 / (1 - u) ^ 3 =
        (∑' m : ℕ+, (q₀ ^ (m : ℕ) * u) ^ 2 /
          (1 - q₀ ^ (m : ℕ) * u) ^ 3) -
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * u⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) +
        (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ)) := by
      rw [bilateralY]
      ring
    have e2 : bilateralY v q₀ - v ^ 2 / (1 - v) ^ 3 =
        (∑' m : ℕ+, (q₀ ^ (m : ℕ) * v) ^ 2 /
          (1 - q₀ ^ (m : ℕ) * v) ^ 3) -
        (∑' m : ℕ+, q₀ ^ (m : ℕ) * v⁻¹ /
          (1 - q₀ ^ (m : ℕ) * v⁻¹) ^ 3) +
        (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
          q₀ ^ (N : ℕ)) := by
      rw [bilateralY]
      ring
    rw [e1, e2, show ∀ A B C A' B' : k,
        (A - B + C) - (A' - B' + C) = (A - A') - (B - B') from
      fun A B C A' B' => by ring]
    rw [← hSY1u.tsum_sub hSY1v, ← hSY2u.tsum_sub hSY2v]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · exact valuation_tsum_le (hSY1u.sub hSY1v) _
        (fun m => htermY1_diff_le u v hu hv m)
    · refine le_trans (valuation_tsum_le (hSY2u.sub hSY2v) _
        (fun m => htermY2_diff_le u⁻¹ v⁻¹ huinv hvinv m)) ?_
      rw [hinvdiff]
  -- Step 3 (seed and contraction; Silverman ATAEC V.4.1).
  -- Coefficient bounds: `|a₄|, |a₆| ≤ |q₀|`.
  have ha₄ : valuation k (WeierstrassCurve.tateA₄ q₀) ≤ valuation k q₀ := by
    rw [WeierstrassCurve.tateA₄_eq_evalInt q₀ hq1]
    calc valuation k (evalInt q₀ a₄Formal)
        ≤ valuation k q₀ ^ 1 := valuation_evalInt_le_pow q₀ hq1
          (fun m hm => by
            interval_cases m
            rw [coeff_a₄Formal]
            simp)
      _ = valuation k q₀ := pow_one _
  have ha₆ : valuation k (WeierstrassCurve.tateA₆ q₀) ≤ valuation k q₀ := by
    rw [WeierstrassCurve.tateA₆_eq_evalInt q₀ hq1]
    calc valuation k (evalInt q₀ a₆Formal)
        ≤ valuation k q₀ ^ 1 := valuation_evalInt_le_pow q₀ hq1
          (fun m hm => by
            interval_cases m
            rw [coeff_a₆Formal]
            simp)
      _ = valuation k q₀ := pow_one _
  -- the explicit equation `y² + xy = x³ + a₄x + a₆`
  have heq : y ^ 2 + x * y =
      x ^ 3 + WeierstrassCurve.tateA₄ q₀ * x + WeierstrassCurve.tateA₆ q₀ := by
    have h1 := ((WeierstrassCurve.tateCurve q₀).toAffine.equation_iff x y).mp hxy
    simpa [WeierstrassCurve.tateCurve] using h1
  -- basic magnitudes: `x ≠ 0`, and the right side has valuation `|x|³`
  have hx0 : x ≠ 0 := by
    intro hh
    rw [hh, map_zero] at hx
    exact absurd (lt_of_lt_of_le zero_lt_one hx) (lt_irrefl _)
  have hX0 : valuation k x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hXcube : (1 : ValueGroupWithZero k) ≤ valuation k x ^ 3 :=
    one_le_pow_of_one_le' hx 3
  have hRHS : valuation k
      (x ^ 3 + WeierstrassCurve.tateA₄ q₀ * x + WeierstrassCurve.tateA₆ q₀) =
      valuation k x ^ 3 := by
    have h1 : valuation k (WeierstrassCurve.tateA₄ q₀ * x +
        WeierstrassCurve.tateA₆ q₀) < valuation k x ^ 3 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        calc valuation k (WeierstrassCurve.tateA₄ q₀) * valuation k x
            ≤ valuation k q₀ * valuation k x := mul_le_mul_left ha₄ _
          _ < 1 * valuation k x :=
              mul_lt_mul_of_pos_right hq1 (zero_lt_iff.mpr hX0)
          _ = valuation k x := one_mul _
          _ ≤ valuation k x ^ 3 := le_self_pow hx (by norm_num)
      · exact lt_of_le_of_lt ha₆ (lt_of_lt_of_le hq1 hXcube)
    rw [add_assoc]
    calc valuation k (x ^ 3 + (WeierstrassCurve.tateA₄ q₀ * x +
          WeierstrassCurve.tateA₆ q₀)) = valuation k (x ^ 3) := by
          exact (valuation k).map_add_eq_of_lt_left (by rwa [map_pow])
      _ = valuation k x ^ 3 := map_pow _ _ _
  -- magnitudes of `y`: `y ≠ 0`, `|y + x| = |y|`, `|y|² = |x|³`, `1 ≤ |y|`
  have hfact : valuation k y * valuation k (y + x) = valuation k x ^ 3 := by
    have h1 : y * (y + x) = y ^ 2 + x * y := by ring
    calc valuation k y * valuation k (y + x)
        = valuation k (y * (y + x)) := (map_mul _ _ _).symm
      _ = valuation k (y ^ 2 + x * y) := by rw [h1]
      _ = valuation k x ^ 3 := by rw [heq]; exact hRHS
  have hy0 : y ≠ 0 := by
    intro hh
    rw [hh, map_zero, zero_mul] at hfact
    exact pow_ne_zero 3 hX0 hfact.symm
  have hY0 : valuation k y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
  have hyx : valuation k (y + x) = valuation k y := by
    rcases lt_trichotomy (valuation k y) (valuation k (y + x)) with h | h | h
    · exfalso
      have hXG : valuation k x = valuation k (y + x) := by
        have he : valuation k x = valuation k (-(y - (y + x))) := by
          congr 1
          ring
        rw [he, Valuation.map_neg, (valuation k).map_sub_eq_of_lt_right h]
      have hG0 : valuation k (y + x) ≠ 0 := hXG ▸ hX0
      have hYG : valuation k y = valuation k (y + x) ^ 2 := by
        have h1 : valuation k y * valuation k (y + x) =
            valuation k (y + x) ^ 2 * valuation k (y + x) := by
          rw [hfact, hXG, pow_succ]
        exact mul_right_cancel₀ hG0 h1
      have hG1 : (1 : ValueGroupWithZero k) ≤ valuation k (y + x) :=
        hXG ▸ hx
      have hGsq : valuation k (y + x) ≤ valuation k (y + x) ^ 2 :=
        le_self_pow hG1 (by norm_num)
      exact absurd (lt_of_le_of_lt (hYG ▸ hGsq) h) (lt_irrefl _)
    · exact h.symm
    · exfalso
      have hXY : valuation k x = valuation k y := by
        have he : valuation k x = valuation k ((y + x) - y) := by
          congr 1
          ring
        rw [he, (valuation k).map_sub_eq_of_lt_right h]
      have hGY : valuation k (y + x) = valuation k y ^ 2 := by
        have h1 : valuation k y * valuation k (y + x) =
            valuation k y * valuation k y ^ 2 := by
          rw [hfact, hXY, pow_succ, mul_comm]
        exact mul_left_cancel₀ hY0 h1
      have hY1 : (1 : ValueGroupWithZero k) ≤ valuation k y := hXY ▸ hx
      have hYsq : valuation k y ≤ valuation k y ^ 2 :=
        le_self_pow hY1 (by norm_num)
      exact absurd (lt_of_le_of_lt (hGY ▸ hYsq) h) (lt_irrefl _)
  have hy2 : valuation k y * valuation k y = valuation k x ^ 3 := by
    rw [← hfact, hyx]
  have hy1 : (1 : ValueGroupWithZero k) ≤ valuation k y := by
    by_contra hcon
    push Not at hcon
    have h1 : valuation k y * valuation k y < 1 :=
      lt_of_le_of_lt (mul_le_mul' le_rfl hcon.le)
        (by rwa [mul_one])
    rw [hy2] at h1
    exact absurd (lt_of_le_of_lt hXcube h1) (lt_irrefl _)
  have hXY_le : valuation k x ≤ valuation k y := by
    by_contra hcon
    push Not at hcon
    have h1 : valuation k y * valuation k y <
        valuation k x * valuation k x :=
      lt_of_le_of_lt (mul_le_mul' le_rfl hcon.le)
        (mul_lt_mul_of_pos_right hcon (zero_lt_iff.mpr hX0))
    have h2 : valuation k x * valuation k x ≤ valuation k x ^ 3 := by
      rw [← sq]
      exact pow_le_pow_right' hx (by norm_num)
    rw [hy2] at h1
    exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
  -- the iteration map `F u = (y - T_Y u) / ((x - T_X u) + (y - T_Y u))`
  -- (the nodal linear solve `t' = (y - T_Y)/(x - T_X)` composed with
  -- `u = t'/(1+t')`, written without nested division)
  set TX : k → k := fun u => bilateralX u q₀ - u / (1 - u) ^ 2 with hTXdef
  set TY : k → k := fun u => bilateralY u q₀ - u ^ 2 / (1 - u) ^ 3
    with hTYdef
  set F : k → k := fun u =>
    (y - TY u) / ((x - TX u) + (y - TY u)) with hFdef
  have hyQ : valuation k q₀ < valuation k y := lt_of_lt_of_le hq1 hy1
  have hxQ : valuation k q₀ < valuation k x := lt_of_lt_of_le hq1 hx
  -- shell magnitudes of the numerator and denominator of `F`
  have hNval : ∀ u : k, valuation k u = 1 → u ≠ 1 →
      valuation k (y - TY u) = valuation k y := by
    intro u hu hu1
    have he : valuation k (y - TY u) = valuation k (-(TY u - y)) := by
      congr 1
      ring
    rw [he, Valuation.map_neg,
      (valuation k).map_sub_eq_of_lt_right
        (lt_of_le_of_lt (htailY u hu hu1) hyQ)]
  have hDval : ∀ u : k, valuation k u = 1 → u ≠ 1 →
      valuation k (x - TX u) = valuation k x := by
    intro u hu hu1
    have he : valuation k (x - TX u) = valuation k (-(TX u - x)) := by
      congr 1
      ring
    rw [he, Valuation.map_neg,
      (valuation k).map_sub_eq_of_lt_right
        (lt_of_le_of_lt (htail u hu hu1) hxQ)]
  have hSval : ∀ u : k, valuation k u = 1 → u ≠ 1 →
      valuation k ((x - TX u) + (y - TY u)) = valuation k y := by
    intro u hu hu1
    have he : valuation k ((x - TX u) + (y - TY u)) =
        valuation k (-((TX u + TY u) - (y + x))) := by
      congr 1
      ring
    rw [he, Valuation.map_neg,
      (valuation k).map_sub_eq_of_lt_right (by
        rw [hyx]
        exact lt_of_le_of_lt (le_trans (Valuation.map_add _ _ _)
          (max_le (htail u hu hu1) (htailY u hu hu1))) hyQ)]
    exact hyx
  have hS0 : ∀ u : k, valuation k u = 1 → u ≠ 1 →
      (x - TX u) + (y - TY u) ≠ 0 := by
    intro u hu hu1 hz
    have h2 := hSval u hu hu1
    rw [hz, map_zero] at h2
    exact hY0 h2.symm
  -- `F` maps the shell into the shell (and never takes the value `1`)
  have hFshell : ∀ u : k, valuation k u = 1 → u ≠ 1 →
      valuation k (F u) = 1 ∧ F u ≠ 1 := by
    intro u hu hu1
    constructor
    · simp only [hFdef]
      rw [map_div₀, hNval u hu hu1, hSval u hu hu1, div_self hY0]
    · intro hh
      simp only [hFdef] at hh
      have h1 : y - TY u = (x - TX u) + (y - TY u) :=
        (div_eq_one_iff_eq (hS0 u hu hu1)).mp hh
      have h2 : x - TX u = 0 :=
        add_right_cancel (h1.symm.trans (zero_add (y - TY u)).symm)
      have h3 := hDval u hu hu1
      rw [h2, map_zero] at h3
      exact hX0 h3.symm
  -- the distance of `F u` from `1` is the constant `|x|/|y|`
  have h1subF : ∀ u : k, valuation k u = 1 → u ≠ 1 →
      valuation k (1 - F u) = valuation k x / valuation k y := by
    intro u hu hu1
    have he : 1 - F u = (x - TX u) / ((x - TX u) + (y - TY u)) := by
      simp only [hFdef]
      rw [eq_div_iff (hS0 u hu hu1), sub_mul, one_mul,
        div_mul_cancel₀ _ (hS0 u hu hu1)]
      ring
    rw [he, map_div₀, hDval u hu hu1, hSval u hu hu1]
  -- `F` is a `|q₀|`-contraction on the shell
  have hFlip : ∀ u v : k, valuation k u = 1 → valuation k v = 1 →
      u ≠ 1 → v ≠ 1 → valuation k (F u - F v) ≤
        valuation k q₀ * valuation k (u - v) := by
    intro u v hu hv hu1 hv1
    have hkeyF : F u - F v =
        ((y - TY u) * (x - TX v) - (y - TY v) * (x - TX u)) /
          (((x - TX u) + (y - TY u)) * ((x - TX v) + (y - TY v))) := by
      simp only [hFdef]
      rw [div_sub_div _ _ (hS0 u hu hu1) (hS0 v hv hv1)]
      congr 1
      ring
    have hvu : valuation k (v - u) = valuation k (u - v) := by
      rw [show v - u = -(u - v) from by ring, Valuation.map_neg]
    have hb1 : valuation k (y * (TX u - TX v)) ≤
        valuation k y * (valuation k q₀ * valuation k (u - v)) := by
      rw [map_mul]
      exact mul_le_mul' le_rfl (hlip u v hu hv hu1 hv1)
    have hb2 : valuation k (x * (TY u - TY v)) ≤
        valuation k y * (valuation k q₀ * valuation k (u - v)) := by
      rw [map_mul]
      calc valuation k x * valuation k (TY u - TY v)
          ≤ valuation k x * (valuation k q₀ * valuation k (u - v)) :=
            mul_le_mul' le_rfl (hlipY u v hu hv hu1 hv1)
        _ ≤ valuation k y * (valuation k q₀ * valuation k (u - v)) :=
            mul_le_mul_left hXY_le _
    have hb3 : valuation k (TY u * (TX v - TX u) +
        TX u * (TY u - TY v)) ≤
        valuation k y * (valuation k q₀ * valuation k (u - v)) := by
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
      · rw [map_mul]
        calc valuation k (TY u) * valuation k (TX v - TX u)
            ≤ valuation k q₀ * (valuation k q₀ * valuation k (u - v)) := by
              refine mul_le_mul' (htailY u hu hu1) ?_
              have h4 := hlip v u hv hu hv1 hu1
              rwa [hvu] at h4
          _ ≤ valuation k y * (valuation k q₀ * valuation k (u - v)) :=
              mul_le_mul_left (le_trans (le_of_lt hq1) hy1) _
      · rw [map_mul]
        calc valuation k (TX u) * valuation k (TY u - TY v)
            ≤ valuation k q₀ * (valuation k q₀ * valuation k (u - v)) :=
              mul_le_mul' (htail u hu hu1) (hlipY u v hu hv hu1 hv1)
          _ ≤ valuation k y * (valuation k q₀ * valuation k (u - v)) :=
              mul_le_mul_left (le_trans (le_of_lt hq1) hy1) _
    have hnum : valuation k
        ((y - TY u) * (x - TX v) - (y - TY v) * (x - TX u)) ≤
        valuation k y * (valuation k q₀ * valuation k (u - v)) := by
      have he : (y - TY u) * (x - TX v) - (y - TY v) * (x - TX u) =
          (y * (TX u - TX v) - x * (TY u - TY v)) +
            (TY u * (TX v - TX u) + TX u * (TY u - TY v)) := by
        ring
      rw [he]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hb3)
      exact le_trans (Valuation.map_sub _ _ _) (max_le hb1 hb2)
    rw [hkeyF, map_div₀, map_mul, hSval u hu hu1, hSval v hv hv1,
      div_le_iff₀ (zero_lt_iff.mpr (mul_ne_zero hY0 hY0))]
    calc valuation k ((y - TY u) * (x - TX v) - (y - TY v) * (x - TX u)) ≤
        valuation k y * (valuation k q₀ * valuation k (u - v)) := hnum
      _ = valuation k q₀ * valuation k (u - v) * valuation k y := by
          rw [mul_comm]
      _ ≤ valuation k q₀ * valuation k (u - v) *
          (valuation k y * valuation k y) := by
          refine mul_le_mul' le_rfl ?_
          calc valuation k y = valuation k y * 1 := (mul_one _).symm
            _ ≤ valuation k y * valuation k y := mul_le_mul' le_rfl hy1
  -- the seed `u₀ = y/(x+y)` lies on the shell and `F` moves it by at
  -- most `|q₀|`
  have hxy0 : x + y ≠ 0 := by
    intro hz
    have h2 : valuation k (y + x) = 0 := by
      rw [show y + x = x + y from by ring, hz, map_zero]
    rw [hyx] at h2
    exact hY0 h2
  have hvxy : valuation k (x + y) = valuation k y := by
    rw [show x + y = y + x from by ring]
    exact hyx
  have hu₀shell : valuation k (y / (x + y)) = 1 ∧ y / (x + y) ≠ 1 := by
    constructor
    · rw [map_div₀, hvxy, div_self hY0]
    · intro hh
      rw [div_eq_one_iff_eq hxy0] at hh
      exact hx0 (add_right_cancel (hh.symm.trans (zero_add y).symm))
  have hseed : valuation k (F (y / (x + y)) - y / (x + y)) ≤
      valuation k q₀ := by
    have hkey : F (y / (x + y)) - y / (x + y) =
        (y * TX (y / (x + y)) - x * TY (y / (x + y))) /
          (((x - TX (y / (x + y))) + (y - TY (y / (x + y)))) * (x + y)) := by
      simp only [hFdef]
      rw [div_sub_div _ _ (hS0 _ hu₀shell.1 hu₀shell.2) hxy0]
      congr 1
      ring
    rw [hkey, map_div₀, map_mul, hSval _ hu₀shell.1 hu₀shell.2, hvxy,
      div_le_iff₀ (zero_lt_iff.mpr (mul_ne_zero hY0 hY0))]
    have hn : valuation k
        (y * TX (y / (x + y)) - x * TY (y / (x + y))) ≤
        valuation k y * valuation k q₀ := by
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
      · rw [map_mul]
        exact mul_le_mul' le_rfl (htail _ hu₀shell.1 hu₀shell.2)
      · rw [map_mul]
        exact mul_le_mul' hXY_le (htailY _ hu₀shell.1 hu₀shell.2)
    calc valuation k (y * TX (y / (x + y)) - x * TY (y / (x + y))) ≤
        valuation k y * valuation k q₀ := hn
      _ = valuation k q₀ * valuation k y := mul_comm _ _
      _ ≤ valuation k q₀ * (valuation k y * valuation k y) := by
          refine mul_le_mul' le_rfl ?_
          calc valuation k y = valuation k y * 1 := (mul_one _).symm
            _ ≤ valuation k y * valuation k y := mul_le_mul' le_rfl hy1
  -- the orbit of the seed under `F`
  set seq : ℕ → k := fun n => F^[n] (y / (x + y)) with hseqdef
  have hseq_zero : seq 0 = y / (x + y) := rfl
  have hseq_succ : ∀ n, seq (n + 1) = F (seq n) := fun n =>
    Function.iterate_succ_apply' F n _
  have hseq_shell : ∀ n, valuation k (seq n) = 1 ∧ seq n ≠ 1 := by
    intro n
    induction n with
    | zero => exact hu₀shell
    | succ n ih =>
      rw [hseq_succ n]
      exact hFshell _ ih.1 ih.2
  have hseq_one_sub : ∀ n, valuation k (1 - seq n) =
      valuation k x / valuation k y := by
    intro n
    cases n with
    | zero =>
      have he : 1 - seq 0 = x / (x + y) := by
        rw [hseq_zero, eq_div_iff hxy0, sub_mul, one_mul,
          div_mul_cancel₀ _ hxy0]
        ring
      rw [he, map_div₀, hvxy]
    | succ n =>
      rw [hseq_succ n]
      exact h1subF _ (hseq_shell n).1 (hseq_shell n).2
  have hdiff : ∀ n, valuation k (seq (n + 1) - seq n) ≤
      valuation k q₀ ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [hseq_succ 0, hseq_zero, pow_one]
      exact hseed
    | succ n ih =>
      rw [hseq_succ (n + 1), hseq_succ n]
      calc valuation k (F (F (seq n)) - F (seq n)) ≤
          valuation k q₀ * valuation k (F (seq n) - seq n) :=
            hFlip _ _ (hFshell _ (hseq_shell n).1 (hseq_shell n).2).1
              (hseq_shell n).1
              (hFshell _ (hseq_shell n).1 (hseq_shell n).2).2
              (hseq_shell n).2
        _ ≤ valuation k q₀ * valuation k q₀ ^ (n + 1) := by
            refine mul_le_mul' le_rfl ?_
            have h5 := ih
            rwa [hseq_succ n] at h5
        _ = valuation k q₀ ^ (n + 2) := by
            rw [← pow_succ']
  -- rank-one analytic structure on `k` (the LocalField recipe), giving a
  -- complete nontrivially normed field whose norm order-embeds the
  -- valuation
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField _ _
  have hbridge_lt : ∀ z c : k, valuation k z < valuation k c ↔ ‖z‖ < ‖c‖ :=
    fun z c => (Valued.toNormedField.norm_lt_iff).symm
  have hbridge_le : ∀ z c : k, valuation k z ≤ valuation k c ↔ ‖z‖ ≤ ‖c‖ :=
    fun z c => (Valued.toNormedField.norm_le_iff).symm
  -- the orbit is Cauchy, by the geometric difference bound
  have hcauchy : CauchySeq seq := by
    refine cauchySeq_of_le_geometric ‖q₀‖ ‖q₀‖ ?_ ?_
    · exact Valued.toNormedField.norm_lt_one_iff.mpr hq1
    · intro n
      rw [dist_eq_norm]
      have h1 : valuation k (seq n - seq (n + 1)) ≤
          valuation k (q₀ ^ (n + 1)) := by
        rw [map_pow]
        have h2 := hdiff n
        rwa [show seq n - seq (n + 1) = -(seq (n + 1) - seq n) from by
          ring, Valuation.map_neg]
      calc ‖seq n - seq (n + 1)‖ ≤ ‖q₀ ^ (n + 1)‖ :=
          (hbridge_le _ _).mp h1
        _ = ‖q₀‖ ^ (n + 1) := norm_pow _ _
        _ = ‖q₀‖ * ‖q₀‖ ^ n := by rw [pow_succ']
  obtain ⟨ustar, hus⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- valuative form of the convergence
  have hconv : ∀ c : k, c ≠ 0 → ∀ᶠ n in Filter.atTop,
      valuation k (seq n - ustar) < valuation k c := by
    intro c hc
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hus ‖c‖
      (norm_pos_iff.mpr hc)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have h2 := hN n hn
    rw [dist_eq_norm] at h2
    exact (hbridge_lt _ _).mpr h2
  -- the limit lies on the shell
  have hustar_val : valuation k ustar = 1 := by
    obtain ⟨n, hn⟩ := (hconv 1 one_ne_zero).exists
    rw [map_one, ← (hseq_shell n).1] at hn
    have he : valuation k ustar =
        valuation k (-((seq n - ustar) - seq n)) := by
      congr 1
      ring
    rw [he, Valuation.map_neg,
      (valuation k).map_sub_eq_of_lt_right hn]
    exact (hseq_shell n).1
  have hustar_ne1 : ustar ≠ 1 := by
    intro hh
    have hXY0 : valuation k x / valuation k y ≠ 0 :=
      div_ne_zero hX0 hY0
    obtain ⟨c, hc⟩ := ValuativeRel.valuation_surjective (K := k)
      (valuation k x / valuation k y)
    have hc0 : c ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hc
      exact hXY0 hc.symm
    obtain ⟨n, hn⟩ := (hconv c hc0).exists
    rw [hc] at hn
    have he : valuation k x / valuation k y =
        valuation k (seq n - ustar) := by
      rw [← hseq_one_sub n,
        show (1 : k) - seq n = -(seq n - ustar) from by rw [hh]; ring,
        Valuation.map_neg]
    rw [← he] at hn
    exact absurd hn (lt_irrefl _)
  -- the limit is a fixed point of `F`
  have hfix : F ustar = ustar := by
    by_contra hne
    have hΔ0 : F ustar - ustar ≠ 0 := sub_ne_zero_of_ne hne
    have hΔv : valuation k (F ustar - ustar) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hΔ0
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (hconv (F ustar - ustar) hΔ0)
    have h1 : valuation k (seq N - ustar) <
        valuation k (F ustar - ustar) := hN N le_rfl
    have h2 : valuation k (seq (N + 1) - ustar) <
        valuation k (F ustar - ustar) := hN (N + 1) (Nat.le_succ N)
    have h3 : valuation k (F ustar - seq (N + 1)) <
        valuation k (F ustar - ustar) := by
      rw [hseq_succ N]
      calc valuation k (F ustar - F (seq N))
          ≤ valuation k q₀ * valuation k (ustar - seq N) :=
            hFlip _ _ hustar_val (hseq_shell N).1 hustar_ne1
              (hseq_shell N).2
        _ ≤ 1 * valuation k (ustar - seq N) :=
            mul_le_mul_left (le_of_lt hq1) _
        _ = valuation k (ustar - seq N) := one_mul _
        _ = valuation k (seq N - ustar) := by
            rw [show ustar - seq N = -(seq N - ustar) from by ring,
              Valuation.map_neg]
        _ < valuation k (F ustar - ustar) := h1
    have h4 : valuation k (F ustar - ustar) <
        valuation k (F ustar - ustar) := by
      calc valuation k (F ustar - ustar)
          = valuation k ((F ustar - seq (N + 1)) +
              (seq (N + 1) - ustar)) := by
            congr 1
            ring
        _ ≤ max (valuation k (F ustar - seq (N + 1)))
            (valuation k (seq (N + 1) - ustar)) :=
            Valuation.map_add _ _ _
        _ < valuation k (F ustar - ustar) := max_lt h3 h2
    exact absurd h4 (lt_irrefl _)
  -- shell facts for the fixed point, and its `D`, `N`, `S` data
  have hu0' : ustar ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hustar_val
    exact zero_ne_one hustar_val
  have hDv : valuation k (x - TX ustar) = valuation k x :=
    hDval ustar hustar_val hustar_ne1
  have hNv : valuation k (y - TY ustar) = valuation k y :=
    hNval ustar hustar_val hustar_ne1
  have hSv : valuation k ((x - TX ustar) + (y - TY ustar)) =
      valuation k y := hSval ustar hustar_val hustar_ne1
  have hD0 : x - TX ustar ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hDv
    exact hX0 hDv.symm
  have hN0 : y - TY ustar ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hNv
    exact hY0 hNv.symm
  have hS0' : (x - TX ustar) + (y - TY ustar) ≠ 0 :=
    hS0 ustar hustar_val hustar_ne1
  -- the fixed point in closed form: `N = u·S`, hence `D = (1-u)·S`
  have hNS : y - TY ustar = ustar *
      ((x - TX ustar) + (y - TY ustar)) := by
    have h1 : F ustar = ustar := hfix
    simp only [hFdef] at h1
    exact (div_eq_iff hS0').mp h1
  have hDS : x - TX ustar = (1 - ustar) *
      ((x - TX ustar) + (y - TY ustar)) := by
    linear_combination -hNS
  have h1u0 : (1 : k) - ustar ≠ 0 :=
    sub_ne_zero_of_ne (Ne.symm hustar_ne1)
  -- the division-free core identity `u·D² = N·S·(1-u)²`
  have hcore : ustar * (x - TX ustar) ^ 2 =
      (y - TY ustar) * ((x - TX ustar) + (y - TY ustar)) *
        (1 - ustar) ^ 2 := by
    linear_combination
      (-(((x - TX ustar) + (y - TY ustar)) * (1 - ustar) ^ 2)) * hNS +
      (ustar * ((x - TX ustar) + (1 - ustar) *
        ((x - TX ustar) + (y - TY ustar)))) * hDS
  -- the division-free defect formulas: `ε·D² = P := D³ - N·S` and
  -- `δ·D = N·ε`
  have hbX : bilateralX ustar q₀ = ustar / (1 - ustar) ^ 2 + TX ustar := by
    rw [hTXdef]
    ring
  have hbY : bilateralY ustar q₀ =
      ustar ^ 2 / (1 - ustar) ^ 3 + TY ustar := by
    rw [hTYdef]
    ring
  have hεmul : (x - bilateralX ustar q₀) * (x - TX ustar) ^ 2 =
      (x - TX ustar) ^ 3 - (y - TY ustar) *
        ((x - TX ustar) + (y - TY ustar)) := by
    rw [hbX]
    field_simp
    linear_combination -hcore
  have hδmul : (y - bilateralY ustar q₀) * (x - TX ustar) =
      (y - TY ustar) * (x - bilateralX ustar q₀) := by
    rw [hbX, hbY]
    field_simp
    linear_combination (ustar * (1 - ustar)) * hNS - ustar ^ 2 * hDS
  -- `|y| ≤ |x|²`
  have hYX2 : valuation k y ≤ valuation k x ^ 2 := by
    by_contra hcon
    push Not at hcon
    have h1 : valuation k x ^ 2 * valuation k x ^ 2 <
        valuation k y * valuation k y :=
      lt_of_le_of_lt (mul_le_mul' hcon.le le_rfl)
        (mul_lt_mul_of_pos_left hcon (zero_lt_iff.mpr hY0))
    rw [hy2, ← pow_add] at h1
    exact absurd (lt_of_le_of_lt (pow_le_pow_right' hx (by norm_num)) h1)
      (lt_irrefl _)
  -- tail values at the fixed point, and small auxiliary bounds
  have hTXv : valuation k (TX ustar) ≤ valuation k q₀ :=
    htail ustar hustar_val hustar_ne1
  have hTYv : valuation k (TY ustar) ≤ valuation k q₀ :=
    htailY ustar hustar_val hustar_ne1
  have hXX2 : valuation k x ≤ valuation k x ^ 2 :=
    le_self_pow hx (by norm_num)
  have hQ1 : valuation k q₀ ≤ 1 := le_of_lt hq1
  have h2v : valuation k (2 : k) ≤ 1 := by
    simpa using valuation_intCast_le_one (R := k) 2
  have h3v : valuation k (3 : k) ≤ 1 := by
    simpa using valuation_intCast_le_one (R := k) 3
  set C := valuation k q₀ * valuation k x ^ 2 with hCdef
  have hQC : valuation k q₀ ≤ C := by
    calc valuation k q₀ = valuation k q₀ * 1 := (mul_one _).symm
      _ ≤ C := mul_le_mul' le_rfl (one_le_pow_of_one_le' hx 2)
  -- the ten tail terms of the defect numerator are all bounded by `C`
  have hb01 : valuation k (-(WeierstrassCurve.tateA₄ q₀ * x)) ≤ C := by
    rw [Valuation.map_neg, map_mul]
    exact mul_le_mul' ha₄ hXX2
  have hb02 : valuation k (WeierstrassCurve.tateA₆ q₀) ≤ C :=
    le_trans ha₆ hQC
  have hb03 : valuation k (3 * x ^ 2 * TX ustar) ≤ C := by
    rw [map_mul, map_mul, map_pow]
    calc valuation k 3 * valuation k x ^ 2 * valuation k (TX ustar)
        ≤ 1 * valuation k x ^ 2 * valuation k q₀ :=
          mul_le_mul' (mul_le_mul' h3v le_rfl) hTXv
      _ = C := by rw [one_mul, mul_comm]
  have hb04 : valuation k (3 * x * TX ustar ^ 2) ≤ C := by
    rw [map_mul, map_mul, map_pow]
    calc valuation k 3 * valuation k x * valuation k (TX ustar) ^ 2
        ≤ 1 * valuation k x ^ 2 * (valuation k q₀ * 1) := by
          refine mul_le_mul' (mul_le_mul' h3v hXX2) ?_
          rw [sq]
          exact mul_le_mul' hTXv (le_trans hTXv hQ1)
      _ = C := by rw [one_mul, mul_one, mul_comm]
  have hb05 : valuation k (TX ustar ^ 3) ≤ C := by
    rw [map_pow]
    refine le_trans ?_ hQC
    calc valuation k (TX ustar) ^ 3
        ≤ valuation k q₀ ^ 3 := pow_le_pow_left' hTXv 3
      _ ≤ valuation k q₀ ^ 1 :=
          pow_le_pow_right_of_le_one' hQ1 (by norm_num)
      _ = valuation k q₀ := pow_one _
  have hb06 : valuation k (2 * y * TY ustar) ≤ C := by
    rw [map_mul, map_mul]
    calc valuation k 2 * valuation k y * valuation k (TY ustar)
        ≤ 1 * valuation k x ^ 2 * valuation k q₀ :=
          mul_le_mul' (mul_le_mul' h2v hYX2) hTYv
      _ = C := by rw [one_mul, mul_comm]
  have hb07 : valuation k (TY ustar ^ 2) ≤ C := by
    rw [map_pow]
    refine le_trans ?_ hQC
    calc valuation k (TY ustar) ^ 2
        ≤ valuation k q₀ ^ 2 := pow_le_pow_left' hTYv 2
      _ ≤ valuation k q₀ ^ 1 :=
          pow_le_pow_right_of_le_one' hQ1 (by norm_num)
      _ = valuation k q₀ := pow_one _
  have hb08 : valuation k (y * TX ustar) ≤ C := by
    rw [map_mul]
    calc valuation k y * valuation k (TX ustar)
        ≤ valuation k x ^ 2 * valuation k q₀ := mul_le_mul' hYX2 hTXv
      _ = C := mul_comm _ _
  have hb09 : valuation k (x * TY ustar) ≤ C := by
    rw [map_mul]
    calc valuation k x * valuation k (TY ustar)
        ≤ valuation k x ^ 2 * valuation k q₀ := mul_le_mul' hXX2 hTYv
      _ = C := mul_comm _ _
  have hb10 : valuation k (TX ustar * TY ustar) ≤ C := by
    rw [map_mul]
    refine le_trans ?_ hQC
    calc valuation k (TX ustar) * valuation k (TY ustar)
        ≤ valuation k q₀ * 1 := mul_le_mul' hTXv (le_trans hTYv hQ1)
      _ = valuation k q₀ := mul_one _
  -- assemble: the defect numerator has valuation at most `C`
  have hPexp : (x - TX ustar) ^ 3 - (y - TY ustar) *
      ((x - TX ustar) + (y - TY ustar)) =
      -(WeierstrassCurve.tateA₄ q₀ * x) - WeierstrassCurve.tateA₆ q₀
        - 3 * x ^ 2 * TX ustar + 3 * x * TX ustar ^ 2 - TX ustar ^ 3
        + 2 * y * TY ustar - TY ustar ^ 2 + y * TX ustar + x * TY ustar
        - TX ustar * TY ustar := by
    linear_combination -heq
  have hPval : valuation k ((x - TX ustar) ^ 3 - (y - TY ustar) *
      ((x - TX ustar) + (y - TY ustar))) ≤ C := by
    rw [hPexp]
    refine le_trans (Valuation.map_sub _ _ _) (max_le
      (le_trans (Valuation.map_add _ _ _) (max_le
        (le_trans (Valuation.map_add _ _ _) (max_le
          (le_trans (Valuation.map_sub _ _ _) (max_le
            (le_trans (Valuation.map_add _ _ _) (max_le
              (le_trans (Valuation.map_sub _ _ _) (max_le
                (le_trans (Valuation.map_add _ _ _) (max_le
                  (le_trans (Valuation.map_sub _ _ _) (max_le
                    (le_trans (Valuation.map_sub _ _ _)
                      (max_le hb01 hb02))
                    hb03))
                  hb04))
                hb05))
              hb06))
            hb07))
          hb08))
        hb09))
      hb10)
  -- hence the defect itself is at most `|q₀|`
  have hεval : valuation k (x - bilateralX ustar q₀) ≤ valuation k q₀ := by
    have h1 := congrArg (valuation k) hεmul
    rw [map_mul, map_pow, hDv] at h1
    have h2 : valuation k (x - bilateralX ustar q₀) *
        valuation k x ^ 2 ≤ C := h1 ▸ hPval
    rw [hCdef, mul_comm (valuation k (x - bilateralX ustar q₀)) _,
      mul_comm (valuation k q₀) _] at h2
    exact (mul_le_mul_iff_right₀
      (zero_lt_iff.mpr (pow_ne_zero 2 hX0))).mp h2
  -- the bilateral point satisfies the Tate equation
  have huq : ustar ≠ q₀ := by
    intro hh
    rw [hh] at hustar_val
    rw [hustar_val] at hq1
    exact absurd hq1 (lt_irrefl _)
  have hlow' : valuation k q₀ * valuation k q₀ < valuation k ustar := by
    rw [hustar_val]
    calc valuation k q₀ * valuation k q₀
        ≤ valuation k q₀ * 1 := mul_le_mul' le_rfl hQ1
      _ = valuation k q₀ := mul_one _
      _ < 1 := hq1
  have hns := nonsingular_bilateral ustar q₀ hu0' hustar_ne1 huq hq0 hq1
    hlow' (le_of_eq hustar_val)
  have hEq2 : (bilateralY ustar q₀) ^ 2 +
      (bilateralX ustar q₀) * (bilateralY ustar q₀) =
      (bilateralX ustar q₀) ^ 3 +
        WeierstrassCurve.tateA₄ q₀ * (bilateralX ustar q₀) +
        WeierstrassCurve.tateA₆ q₀ := by
    have h1 := ((WeierstrassCurve.tateCurve q₀).toAffine.equation_iff
      _ _).mp hns.1
    simpa [WeierstrassCurve.tateCurve] using h1
  -- the division form of the `δ`-relation, and the factored identity
  have hδdiv : y - bilateralY ustar q₀ =
      (y - TY ustar) / (x - TX ustar) * (x - bilateralX ustar q₀) := by
    rw [div_mul_eq_mul_div, eq_div_iff hD0]
    linear_combination hδmul
  have hsub : (y - bilateralY ustar q₀) *
      ((y - bilateralY ustar q₀) + 2 * (bilateralY ustar q₀) +
        (bilateralX ustar q₀) + (x - bilateralX ustar q₀)) =
      (x - bilateralX ustar q₀) *
        (3 * (bilateralX ustar q₀) ^ 2 +
          3 * (bilateralX ustar q₀) * (x - bilateralX ustar q₀) +
          (x - bilateralX ustar q₀) ^ 2 +
          WeierstrassCurve.tateA₄ q₀ - bilateralY ustar q₀) := by
    linear_combination heq - hEq2
  have hfactored : (x - bilateralX ustar q₀) *
      ((y - TY ustar) / (x - TX ustar) *
        ((y - bilateralY ustar q₀) + 2 * (bilateralY ustar q₀) +
          (bilateralX ustar q₀) + (x - bilateralX ustar q₀)) -
       (3 * (bilateralX ustar q₀) ^ 2 +
          3 * (bilateralX ustar q₀) * (x - bilateralX ustar q₀) +
          (x - bilateralX ustar q₀) ^ 2 +
          WeierstrassCurve.tateA₄ q₀ - bilateralY ustar q₀)) = 0 := by
    linear_combination hsub -
      ((y - bilateralY ustar q₀) + 2 * (bilateralY ustar q₀) +
        (bilateralX ustar q₀) + (x - bilateralX ustar q₀)) * hδdiv
  -- the slope fraction in `u`-form
  have ht : (y - TY ustar) / (x - TX ustar) = ustar / (1 - ustar) :=
    (div_eq_div_iff hD0 h1u0).mpr (by
      linear_combination (1 - ustar) * hNS - ustar * hDS)
  -- the exclusion factor equals the dominant `-u²/(1-u)⁴` plus small terms
  have hR : (y - TY ustar) / (x - TX ustar) *
        ((y - bilateralY ustar q₀) + 2 * (bilateralY ustar q₀) +
          (bilateralX ustar q₀) + (x - bilateralX ustar q₀)) -
       (3 * (bilateralX ustar q₀) ^ 2 +
          3 * (bilateralX ustar q₀) * (x - bilateralX ustar q₀) +
          (x - bilateralX ustar q₀) ^ 2 +
          WeierstrassCurve.tateA₄ q₀ - bilateralY ustar q₀) =
      -(ustar ^ 2 / (1 - ustar) ^ 4) +
        (ustar / (1 - ustar) * (y - bilateralY ustar q₀) +
         ustar / (1 - ustar) * (x - bilateralX ustar q₀) -
         6 * (ustar / (1 - ustar) ^ 2) * TX ustar - 3 * TX ustar ^ 2 +
         ustar / (1 - ustar) * TX ustar + 2 * (ustar / (1 - ustar)) *
           TY ustar + TY ustar -
         3 * (ustar / (1 - ustar) ^ 2 + TX ustar) *
           (x - bilateralX ustar q₀) -
         (x - bilateralX ustar q₀) ^ 2 -
         WeierstrassCurve.tateA₄ q₀) := by
    rw [ht, hbX, hbY]
    field_simp
    ring
  -- valuations of the dominant and small parts
  have h1u : 1 - ustar = (x - TX ustar) /
      ((x - TX ustar) + (y - TY ustar)) :=
    (eq_div_iff hS0').mpr hDS.symm
  have hW : valuation k (1 - ustar) = valuation k x / valuation k y := by
    rw [h1u, map_div₀, hDv, hSv]
  have htval : valuation k (ustar / (1 - ustar)) =
      valuation k y / valuation k x := by
    rw [map_div₀, hustar_val, hW, one_div, inv_div]
  have hYX_sq : valuation k y / valuation k x *
      (valuation k y / valuation k x) = valuation k x := by
    rw [div_mul_div_comm, hy2]
    rw [div_eq_iff (mul_ne_zero hX0 hX0), pow_succ, pow_two]
    exact mul_assoc _ _ _
  have hXlval : valuation k (ustar / (1 - ustar) ^ 2) = valuation k x := by
    rw [map_div₀, hustar_val, map_pow, hW, one_div, div_pow, inv_div,
      div_eq_iff (pow_ne_zero 2 hX0), pow_two (valuation k y), hy2,
      pow_succ]
    exact mul_comm _ _
  have hMAINval : valuation k (ustar ^ 2 / (1 - ustar) ^ 4) =
      valuation k x ^ 2 := by
    rw [map_div₀, map_pow, map_pow, hustar_val, one_pow, hW, one_div,
      div_pow, inv_div, div_eq_iff (pow_ne_zero 4 hX0),
      show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two (valuation k y), hy2,
      ← pow_mul, show (3 * 2 : ℕ) = 2 + 2 * 2 from rfl, pow_add]
  have hYXle : valuation k y / valuation k x ≤ valuation k x := by
    rw [div_le_iff₀ (zero_lt_iff.mpr hX0)]
    calc valuation k y ≤ valuation k x ^ 2 := hYX2
      _ = valuation k x * valuation k x := pow_two _
  have hδaval : valuation k (y - bilateralY ustar q₀) ≤
      valuation k y / valuation k x * valuation k q₀ := by
    rw [hδdiv, map_mul, map_div₀, hNv, hDv]
    exact mul_le_mul' le_rfl hεval
  set C₂ := valuation k x * valuation k q₀ with hC₂def
  have hQC₂ : valuation k q₀ ≤ C₂ := by
    calc valuation k q₀ = 1 * valuation k q₀ := (one_mul _).symm
      _ ≤ C₂ := mul_le_mul' hx le_rfl
  have hr1 : valuation k (ustar / (1 - ustar) *
      (y - bilateralY ustar q₀)) ≤ C₂ := by
    rw [map_mul, htval]
    calc valuation k y / valuation k x *
        valuation k (y - bilateralY ustar q₀)
        ≤ valuation k y / valuation k x *
          (valuation k y / valuation k x * valuation k q₀) :=
          mul_le_mul' le_rfl hδaval
      _ = valuation k y / valuation k x *
          (valuation k y / valuation k x) * valuation k q₀ := by
          rw [mul_assoc]
      _ = C₂ := by rw [hYX_sq]
  have hr2 : valuation k (ustar / (1 - ustar) *
      (x - bilateralX ustar q₀)) ≤ C₂ := by
    rw [map_mul, htval]
    exact mul_le_mul' hYXle hεval
  have hr3 : valuation k (6 * (ustar / (1 - ustar) ^ 2) * TX ustar) ≤
      C₂ := by
    rw [map_mul, map_mul, hXlval]
    calc valuation k 6 * valuation k x * valuation k (TX ustar)
        ≤ 1 * valuation k x * valuation k q₀ :=
          mul_le_mul' (mul_le_mul'
            (by simpa using valuation_intCast_le_one (R := k) 6) le_rfl)
            hTXv
      _ = C₂ := by rw [one_mul]
  have hr4 : valuation k (3 * TX ustar ^ 2) ≤ C₂ := by
    rw [map_mul, map_pow]
    refine le_trans ?_ hQC₂
    calc valuation k 3 * valuation k (TX ustar) ^ 2
        ≤ 1 * (valuation k q₀ * 1) := by
          refine mul_le_mul' h3v ?_
          rw [pow_two]
          exact mul_le_mul' hTXv (le_trans hTXv hQ1)
      _ = valuation k q₀ := by rw [one_mul, mul_one]
  have hr5 : valuation k (ustar / (1 - ustar) * TX ustar) ≤ C₂ := by
    rw [map_mul, htval]
    exact mul_le_mul' hYXle hTXv
  have hr6 : valuation k (2 * (ustar / (1 - ustar)) * TY ustar) ≤ C₂ := by
    rw [map_mul, map_mul, htval]
    calc valuation k 2 * (valuation k y / valuation k x) *
        valuation k (TY ustar)
        ≤ 1 * valuation k x * valuation k q₀ :=
          mul_le_mul' (mul_le_mul' h2v hYXle) hTYv
      _ = C₂ := by rw [one_mul]
  have hr7 : valuation k (TY ustar) ≤ C₂ := le_trans hTYv hQC₂
  have hr8 : valuation k (3 * (ustar / (1 - ustar) ^ 2 + TX ustar) *
      (x - bilateralX ustar q₀)) ≤ C₂ := by
    rw [map_mul, map_mul]
    have h1 : valuation k (ustar / (1 - ustar) ^ 2 + TX ustar) ≤
        valuation k x := by
      refine le_trans (Valuation.map_add _ _ _) (max_le (le_of_eq hXlval)
        (le_trans hTXv (le_trans hQ1 hx)))
    calc valuation k 3 *
        valuation k (ustar / (1 - ustar) ^ 2 + TX ustar) *
        valuation k (x - bilateralX ustar q₀)
        ≤ 1 * valuation k x * valuation k q₀ :=
          mul_le_mul' (mul_le_mul' h3v h1) hεval
      _ = C₂ := by rw [one_mul]
  have hr9 : valuation k ((x - bilateralX ustar q₀) ^ 2) ≤ C₂ := by
    rw [map_pow]
    refine le_trans ?_ hQC₂
    calc valuation k (x - bilateralX ustar q₀) ^ 2
        ≤ valuation k q₀ * 1 := by
          rw [pow_two]
          exact mul_le_mul' hεval (le_trans hεval hQ1)
      _ = valuation k q₀ := mul_one _
  have hr10 : valuation k (WeierstrassCurve.tateA₄ q₀) ≤ C₂ :=
    le_trans ha₄ hQC₂
  -- the small part is at most `C₂ = |x||q₀| < |x|²`
  have hRval : valuation k
      (ustar / (1 - ustar) * (y - bilateralY ustar q₀) +
       ustar / (1 - ustar) * (x - bilateralX ustar q₀) -
       6 * (ustar / (1 - ustar) ^ 2) * TX ustar - 3 * TX ustar ^ 2 +
       ustar / (1 - ustar) * TX ustar + 2 * (ustar / (1 - ustar)) *
         TY ustar + TY ustar -
       3 * (ustar / (1 - ustar) ^ 2 + TX ustar) *
         (x - bilateralX ustar q₀) -
       (x - bilateralX ustar q₀) ^ 2 -
       WeierstrassCurve.tateA₄ q₀) ≤ C₂ := by
    refine le_trans (Valuation.map_sub _ _ _) (max_le
      (le_trans (Valuation.map_sub _ _ _) (max_le
        (le_trans (Valuation.map_sub _ _ _) (max_le
          (le_trans (Valuation.map_add _ _ _) (max_le
            (le_trans (Valuation.map_add _ _ _) (max_le
              (le_trans (Valuation.map_add _ _ _) (max_le
                (le_trans (Valuation.map_sub _ _ _) (max_le
                  (le_trans (Valuation.map_sub _ _ _) (max_le
                    (le_trans (Valuation.map_add _ _ _)
                      (max_le hr1 hr2))
                    hr3))
                  hr4))
                hr5))
              hr6))
            hr7))
          hr8))
        hr9))
      hr10)
  have hC₂lt : C₂ < valuation k x ^ 2 := by
    rw [hC₂def, pow_two]
    exact mul_lt_mul_of_pos_left (lt_of_lt_of_le hq1 hx)
      (zero_lt_iff.mpr hX0)
  -- hence the exclusion factor has valuation `|x|²` and is nonzero
  have hBBval : valuation k
      ((y - TY ustar) / (x - TX ustar) *
        ((y - bilateralY ustar q₀) + 2 * (bilateralY ustar q₀) +
          (bilateralX ustar q₀) + (x - bilateralX ustar q₀)) -
       (3 * (bilateralX ustar q₀) ^ 2 +
          3 * (bilateralX ustar q₀) * (x - bilateralX ustar q₀) +
          (x - bilateralX ustar q₀) ^ 2 +
          WeierstrassCurve.tateA₄ q₀ - bilateralY ustar q₀)) =
      valuation k x ^ 2 := by
    rw [hR]
    have h1 : valuation k
        (ustar / (1 - ustar) * (y - bilateralY ustar q₀) +
         ustar / (1 - ustar) * (x - bilateralX ustar q₀) -
         6 * (ustar / (1 - ustar) ^ 2) * TX ustar - 3 * TX ustar ^ 2 +
         ustar / (1 - ustar) * TX ustar + 2 * (ustar / (1 - ustar)) *
           TY ustar + TY ustar -
         3 * (ustar / (1 - ustar) ^ 2 + TX ustar) *
           (x - bilateralX ustar q₀) -
         (x - bilateralX ustar q₀) ^ 2 -
         WeierstrassCurve.tateA₄ q₀) <
        valuation k (-(ustar ^ 2 / (1 - ustar) ^ 4)) := by
      rw [Valuation.map_neg, hMAINval]
      exact lt_of_le_of_lt hRval hC₂lt
    rw [(valuation k).map_add_eq_of_lt_left h1, Valuation.map_neg,
      hMAINval]
  -- conclude: the defect vanishes and `ustar` is the sought parameter
  rcases mul_eq_zero.mp hfactored with hzero | hBBzero
  · exact ⟨ustar, hu0', hustar_ne1,
      by rw [hustar_val]; exact hq1, le_of_eq hustar_val,
      (sub_eq_zero.mp hzero).symm⟩
  · exfalso
    rw [hBBzero, map_zero] at hBBval
    exact pow_ne_zero 2 hX0 hBBval.symm

set_option warn.sorry false in
/-- **`x`-surjectivity, non-identity-component case** (sorry node —
Silverman ATAEC V.4, Lemma 4.1.4 and the coset-counting argument): if
`|x| < 1` then `(x,y)` lies in one of the finitely many non-identity
components `U_n`, `V_n`, `W` of the special fibre of the Néron model;
each component meets the image of the annulus parametrisation (its
points are within `E_{q,0}` of each other by the elementary ultrametric
estimates of Lemma 4.1.4, including the duplication-resultant identity
`f·F - g·G = Δ` for the boundary shell `W`), and since the image of
`φ` already contains a full set of coset representatives for
`E_q(K)/E_{q,0}(K)` (of order `ord_v(q)`, matched by the `q^ℤ`-indexed
shift classes), every component is hit. -/
theorem exists_annulus_bilateralX_eq_of_lt_one (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq1 : valuation k q₀ < 1) (x y : k)
    (hxy : (WeierstrassCurve.tateCurve q₀).toAffine.Equation x y)
    (hx : valuation k x < 1) :
    ∃ u : k, u ≠ 0 ∧ u ≠ 1 ∧ valuation k q₀ < valuation k u ∧
      valuation k u ≤ 1 ∧ bilateralX u q₀ = x := by
  have htsum_pnat : ∀ (f : ℕ+ → k), Summable f →
      ∀ c : ValueGroupWithZero k, (∀ m, valuation k (f m) ≤ c) →
      valuation k (∑' m, f m) ≤ c :=
    fun f hf c hb => valuation_tsum_le hf c hb
  have hqpow_le : ∀ N : ℕ+, valuation k q₀ ^ (N : ℕ) ≤ valuation k q₀ := by
    intro N
    calc valuation k q₀ ^ (N : ℕ) ≤ valuation k q₀ ^ (1 : ℕ) :=
        pow_le_pow_right_of_le_one' (le_of_lt hq1) N.2
      _ = valuation k q₀ := pow_one _
  by_cases hcase : valuation k q₀ < valuation k x ^ 2
  · -- Case A (open shell, `|q| < |x|² < 1`): on the shell `|u| = |x|`
    -- the map `u ↦ bilateralX u - u` is small and contractive, so the
    -- iteration `u ↦ x - (bilateralX u - u)` seeded at `x` converges to
    -- an exact solution — the leading map is the identity, so no branch
    -- selection and no exclusion argument are needed.
    have hX0 : valuation k x ≠ 0 := by
      intro hz
      rw [hz, pow_two, mul_zero] at hcase
      exact absurd hcase (not_lt.mpr zero_le)
    have hx0 : x ≠ 0 := fun hz => hX0 (by rw [hz, map_zero])
    have hXpos : (0 : ValueGroupWithZero k) < valuation k x :=
      zero_lt_iff.mpr hX0
    have hsq : valuation k q₀ < valuation k x * valuation k x := by
      rwa [pow_two] at hcase
    have hqx : valuation k q₀ < valuation k x :=
      lt_of_lt_of_le hsq (by
        calc valuation k x * valuation k x
            ≤ valuation k x * 1 := mul_le_mul' le_rfl (le_of_lt hx)
          _ = valuation k x := mul_one _)
    have hqdivx : valuation k q₀ / valuation k x < valuation k x := by
      rw [div_lt_iff₀ hXpos]
      exact hsq
    set Mx := max (valuation k x * valuation k x)
      (valuation k q₀ / valuation k x) with hMxdef
    have hMxlt : Mx < valuation k x := max_lt
      (mul_lt_of_lt_one_right hXpos hx) hqdivx
    set ρ := max (valuation k x)
      (valuation k q₀ / (valuation k x * valuation k x)) with hρdef
    have hρ1 : ρ < 1 := max_lt hx (by
      rw [div_lt_one₀ (zero_lt_iff.mpr (mul_ne_zero hX0 hX0))]
      exact hsq)
    have hρ0 : ρ ≠ 0 := fun hz =>
      hX0 (le_zero_iff.mp (hz ▸ le_max_left _ _))
    -- shell facts
    have hshell : ∀ u : k, valuation k u = valuation k x →
        u ≠ 0 ∧ u ≠ 1 ∧ valuation k (1 - u) = 1 ∧
          valuation k (q₀ * u) < 1 ∧ valuation k (q₀ * u⁻¹) < 1 := by
      intro u hu
      have hu0 : u ≠ 0 := fun hz => hX0 (by rw [← hu, hz, map_zero])
      have hult : valuation k u < 1 := hu ▸ hx
      refine ⟨hu0, ?_, (valuation k).map_one_sub_of_lt hult, ?_, ?_⟩
      · intro hz
        rw [hz, map_one] at hu
        exact absurd (hu ▸ hx) (lt_irrefl _)
      · rw [map_mul]
        calc valuation k q₀ * valuation k u
            ≤ valuation k q₀ * 1 := mul_le_mul' le_rfl (le_of_lt hult)
          _ = valuation k q₀ := mul_one _
          _ < 1 := hq1
      · rw [map_mul, map_inv₀, hu, ← div_eq_mul_inv]
        exact lt_trans hqdivx hx
    -- termwise bounds for the two Lambert halves on the shell
    have htermA1 : ∀ (u : k), valuation k u = valuation k x → ∀ m : ℕ+,
        valuation k (q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 2) ≤
          valuation k x * valuation k x := by
      intro u hu m
      have hsmall : valuation k (q₀ ^ (m : ℕ) * u) < 1 := by
        rw [map_mul, map_pow]
        calc valuation k q₀ ^ (m : ℕ) * valuation k u
            ≤ valuation k q₀ * 1 :=
              mul_le_mul' (hqpow_le m) (le_of_lt (hu ▸ hx))
          _ = valuation k q₀ := mul_one _
          _ < 1 := hq1
      rw [map_div₀, map_mul, map_pow, hu, map_pow,
        (valuation k).map_one_sub_of_lt hsmall, one_pow, div_one]
      calc valuation k q₀ ^ (m : ℕ) * valuation k x
          ≤ valuation k q₀ * valuation k x := mul_le_mul_left (hqpow_le m) _
        _ ≤ valuation k x * valuation k x :=
            mul_le_mul_left (le_of_lt hqx) _
    have htermA2 : ∀ (u : k), valuation k u = valuation k x → ∀ m : ℕ+,
        valuation k (q₀ ^ (m : ℕ) * u⁻¹ /
          (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 2) ≤
          valuation k q₀ / valuation k x := by
      intro u hu m
      have hsmall : valuation k (q₀ ^ (m : ℕ) * u⁻¹) < 1 := by
        rw [map_mul, map_pow, map_inv₀, hu]
        calc valuation k q₀ ^ (m : ℕ) * (valuation k x)⁻¹
            ≤ valuation k q₀ * (valuation k x)⁻¹ :=
              mul_le_mul_left (hqpow_le m) _
          _ = valuation k q₀ / valuation k x := (div_eq_mul_inv _ _).symm
          _ < 1 := lt_trans hqdivx hx
      rw [map_div₀, map_mul, map_pow, map_inv₀, hu, map_pow,
        (valuation k).map_one_sub_of_lt hsmall, one_pow, div_one,
        ← div_eq_mul_inv]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_left (hqpow_le m) _
    -- the leading-part identity and its shell bound
    have hkeylead : ∀ u : k, (1 : k) - u ≠ 0 →
        u / (1 - u) ^ 2 - u = u ^ 2 * (2 - u) / (1 - u) ^ 2 := by
      intro u h1u
      field_simp
      ring
    have h2sub : ∀ u : k, valuation k u = valuation k x →
        valuation k (2 - u) ≤ 1 := by
      intro u hu
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
      · simpa using valuation_intCast_le_one (R := k) 2
      · rw [hu]
        exact le_of_lt hx
    -- the tail bound: `|bilateralX u - u| ≤ Mx` on the shell
    have hGval : ∀ u : k, valuation k u = valuation k x →
        valuation k (bilateralX u q₀ - u) ≤ Mx := by
      intro u hu
      obtain ⟨hu0, hu1, h1u, hqu, hquinv⟩ := hshell u hu
      have h1u0 : (1 : k) - u ≠ 0 := by
        intro hz
        rw [hz, map_zero] at h1u
        exact zero_ne_one h1u
      have he : bilateralX u q₀ - u =
          (u / (1 - u) ^ 2 - u) +
          ((∑' m : ℕ+, q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 2) +
           (∑' m : ℕ+, q₀ ^ (m : ℕ) * u⁻¹ /
              (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 2) -
           2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
              q₀ ^ (N : ℕ))) := by
        rw [bilateralX]
        ring
      rw [he]
      have hq_le_Mx : valuation k q₀ ≤ Mx := by
        refine le_trans ?_ (le_max_right _ _)
        rw [le_div_iff₀ hXpos]
        calc valuation k q₀ * valuation k x
            ≤ valuation k q₀ * 1 := mul_le_mul' le_rfl (le_of_lt hx)
          _ = valuation k q₀ := mul_one _
      have hlead : valuation k (u / (1 - u) ^ 2 - u) ≤ Mx := by
        rw [hkeylead u h1u0, map_div₀, map_mul, map_pow, map_pow, hu,
          h1u, one_pow, div_one]
        refine le_trans ?_ (le_max_left _ _)
        calc valuation k x ^ 2 * valuation k (2 - u)
            ≤ valuation k x ^ 2 * 1 := mul_le_mul' le_rfl (h2sub u hu)
          _ = valuation k x * valuation k x := by rw [mul_one, pow_two]
      have hS1 : valuation k
          (∑' m : ℕ+, q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 2) ≤
            Mx :=
        le_trans (htsum_pnat _ (summable_lambert_terms u q₀ hq1 hqu) _
          (htermA1 u hu)) (le_max_left _ _)
      have hS2 : valuation k
          (∑' m : ℕ+, q₀ ^ (m : ℕ) * u⁻¹ /
            (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 2) ≤ Mx :=
        le_trans (htsum_pnat _ (summable_lambert_terms u⁻¹ q₀ hq1 hquinv)
          _ (htermA2 u hu)) (le_max_right _ _)
      have hσ : valuation k
          (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
            q₀ ^ (N : ℕ)) ≤ valuation k q₀ := by
        refine htsum_pnat _ (summable_sigma_one_nonarch q₀ hq1) _ ?_
        intro N
        rw [map_mul, map_pow]
        have hd1 : valuation k
            (∑ d ∈ (N : ℕ).divisors, (d : k)) ≤ 1 :=
          Valuation.map_sum_le _ fun d _ => by
            simpa using valuation_intCast_le_one (R := k) d
        calc valuation k (∑ d ∈ (N : ℕ).divisors, (d : k)) *
            valuation k q₀ ^ (N : ℕ)
            ≤ 1 * valuation k q₀ ^ (N : ℕ) := mul_le_mul_left hd1 _
          _ = valuation k q₀ ^ (N : ℕ) := one_mul _
          _ ≤ valuation k q₀ := hqpow_le N
      have hS3 : valuation k
          (2 * ∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
            q₀ ^ (N : ℕ)) ≤ Mx := by
        rw [map_mul]
        refine le_trans ?_ hq_le_Mx
        refine le_trans (mul_le_mul'
          (by simpa using valuation_intCast_le_one (R := k) 2) hσ) ?_
        rw [one_mul]
      exact le_trans (Valuation.map_add _ _ _) (max_le hlead
        (le_trans (Valuation.map_sub _ _ _) (max_le
          (le_trans (Valuation.map_add _ _ _) (max_le hS1 hS2)) hS3)))
    -- the difference identities
    have hkeyLdiff : ∀ u v : k, (1 : k) - u ≠ 0 → (1 : k) - v ≠ 0 →
        (u / (1 - u) ^ 2 - u) - (v / (1 - v) ^ 2 - v) =
          (u - v) * ((1 - u * v) - (1 - u) ^ 2 * (1 - v) ^ 2) /
            ((1 - u) ^ 2 * (1 - v) ^ 2) := by
      intro u v h1 h2
      field_simp
      ring
    have hkeyD : ∀ a w z : k, 1 - a * w ≠ 0 → 1 - a * z ≠ 0 →
        a * w / (1 - a * w) ^ 2 - a * z / (1 - a * z) ^ 2 =
          a * (w - z) * (1 - a ^ 2 * w * z) /
            ((1 - a * w) ^ 2 * (1 - a * z) ^ 2) := by
      intro a w z h1 h2
      field_simp
      ring
    have hone_sub_ne' : ∀ z : k, valuation k z < 1 → 1 - z ≠ 0 := by
      intro z hz hh
      have h1 := (valuation k).map_one_sub_of_lt hz
      rw [hh, map_zero] at h1
      exact zero_ne_one h1
    -- the `Q`-factor of the leading difference is bounded by `|x|`
    have hQb : ∀ u v : k, valuation k u = valuation k x →
        valuation k v = valuation k x →
        valuation k ((1 - u * v) - (1 - u) ^ 2 * (1 - v) ^ 2) ≤
          valuation k x := by
      intro u v hu hv
      have hid : (1 - u * v) - (1 - u) ^ 2 * (1 - v) ^ 2 =
          (u + v - u * v) * (2 - (u + v - u * v)) - u * v := by
        ring
      rw [hid]
      have hw : valuation k (u + v - u * v) ≤ valuation k x := by
        refine le_trans (Valuation.map_sub _ _ _) (max_le
          (le_trans (Valuation.map_add _ _ _) (max_le (le_of_eq hu)
            (le_of_eq hv))) ?_)
        rw [map_mul, hu, hv]
        calc valuation k x * valuation k x
            ≤ valuation k x * 1 := mul_le_mul' le_rfl (le_of_lt hx)
          _ = valuation k x := mul_one _
      have h2w : valuation k (2 - (u + v - u * v)) ≤ 1 := by
        refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
        · simpa using valuation_intCast_le_one (R := k) 2
        · exact le_trans hw (le_of_lt hx)
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
      · rw [map_mul]
        calc valuation k (u + v - u * v) *
            valuation k (2 - (u + v - u * v))
            ≤ valuation k x * 1 := mul_le_mul' hw h2w
          _ = valuation k x := mul_one _
      · rw [map_mul, hu, hv]
        calc valuation k x * valuation k x
            ≤ valuation k x * 1 := mul_le_mul' le_rfl (le_of_lt hx)
          _ = valuation k x := mul_one _
    -- the Lipschitz bound for the tail map on the shell
    have hGlip : ∀ u v : k, valuation k u = valuation k x →
        valuation k v = valuation k x →
        valuation k ((bilateralX u q₀ - u) - (bilateralX v q₀ - v)) ≤
          ρ * valuation k (u - v) := by
      intro u v hu hv
      obtain ⟨hu0, hu1, h1u, hqu, hquinv⟩ := hshell u hu
      obtain ⟨hv0, hv1, h1v, hqv, hqvinv⟩ := hshell v hv
      have h1u0 : (1 : k) - u ≠ 0 := hone_sub_ne' u (hu ▸ hx)
      have h1v0 : (1 : k) - v ≠ 0 := hone_sub_ne' v (hv ▸ hx)
      have hinvdiff : valuation k (u⁻¹ - v⁻¹) =
          valuation k (u - v) / (valuation k x * valuation k x) := by
        have he : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by
          field_simp
        rw [he, map_div₀, map_mul, hu, hv,
          show v - u = -(u - v) from by ring, Valuation.map_neg]
      have hlead : valuation k
          ((u / (1 - u) ^ 2 - u) - (v / (1 - v) ^ 2 - v)) ≤
            ρ * valuation k (u - v) := by
        rw [hkeyLdiff u v h1u0 h1v0, map_div₀, map_mul, map_mul,
          map_pow, map_pow, h1u, h1v, one_pow, one_mul, div_one]
        calc valuation k (u - v) *
            valuation k ((1 - u * v) - (1 - u) ^ 2 * (1 - v) ^ 2)
            ≤ valuation k (u - v) * valuation k x :=
              mul_le_mul' le_rfl (hQb u v hu hv)
          _ = valuation k x * valuation k (u - v) := mul_comm _ _
          _ ≤ ρ * valuation k (u - v) :=
              mul_le_mul_left (le_max_left _ _) _
      have htermD1 : ∀ m : ℕ+, valuation k
          (q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 2 -
           q₀ ^ (m : ℕ) * v / (1 - q₀ ^ (m : ℕ) * v) ^ 2) ≤
            ρ * valuation k (u - v) := by
        intro m
        have hsu : valuation k (q₀ ^ (m : ℕ) * u) < 1 := by
          rw [map_mul, map_pow]
          calc valuation k q₀ ^ (m : ℕ) * valuation k u
              ≤ valuation k q₀ * 1 :=
                mul_le_mul' (hqpow_le m) (le_of_lt (hu ▸ hx))
            _ = valuation k q₀ := mul_one _
            _ < 1 := hq1
        have hsv : valuation k (q₀ ^ (m : ℕ) * v) < 1 := by
          rw [map_mul, map_pow]
          calc valuation k q₀ ^ (m : ℕ) * valuation k v
              ≤ valuation k q₀ * 1 :=
                mul_le_mul' (hqpow_le m) (le_of_lt (hv ▸ hx))
            _ = valuation k q₀ := mul_one _
            _ < 1 := hq1
        have hbr : valuation k (1 - (q₀ ^ (m : ℕ)) ^ 2 * u * v) ≤ 1 := by
          refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
          · rw [map_one]
          · rw [map_mul, map_mul, map_pow, map_pow, hu, hv]
            calc (valuation k q₀ ^ (m : ℕ)) ^ 2 * valuation k x *
                valuation k x
                ≤ 1 ^ 2 * 1 * 1 := mul_le_mul' (mul_le_mul'
                    (pow_le_pow_left' (le_trans (hqpow_le m)
                      (le_of_lt hq1)) 2) (le_of_lt hx)) (le_of_lt hx)
              _ = 1 := by rw [one_pow, one_mul, one_mul]
        rw [hkeyD _ _ _ (hone_sub_ne' _ hsu) (hone_sub_ne' _ hsv),
          map_div₀, map_mul, map_mul, map_mul]
        simp only [map_pow]
        rw [(valuation k).map_one_sub_of_lt hsu,
          (valuation k).map_one_sub_of_lt hsv]
        simp only [one_pow, mul_one, div_one]
        calc valuation k q₀ ^ (m : ℕ) * valuation k (u - v) *
            valuation k (1 - (q₀ ^ (m : ℕ)) ^ 2 * u * v)
            ≤ valuation k q₀ ^ (m : ℕ) * valuation k (u - v) * 1 :=
              mul_le_mul' le_rfl hbr
          _ = valuation k q₀ ^ (m : ℕ) * valuation k (u - v) := mul_one _
          _ ≤ valuation k q₀ * valuation k (u - v) :=
              mul_le_mul_left (hqpow_le m) _
          _ ≤ ρ * valuation k (u - v) := by
              refine mul_le_mul_left ?_ _
              refine le_trans (le_of_lt hqx) (le_max_left _ _)
      have htermD2 : ∀ m : ℕ+, valuation k
          (q₀ ^ (m : ℕ) * u⁻¹ / (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 2 -
           q₀ ^ (m : ℕ) * v⁻¹ / (1 - q₀ ^ (m : ℕ) * v⁻¹) ^ 2) ≤
            ρ * valuation k (u - v) := by
        intro m
        have huinv : valuation k u⁻¹ = (valuation k x)⁻¹ := by
          rw [map_inv₀, hu]
        have hvinv : valuation k v⁻¹ = (valuation k x)⁻¹ := by
          rw [map_inv₀, hv]
        have hsu : valuation k (q₀ ^ (m : ℕ) * u⁻¹) < 1 := by
          rw [map_mul, map_pow, huinv]
          calc valuation k q₀ ^ (m : ℕ) * (valuation k x)⁻¹
              ≤ valuation k q₀ * (valuation k x)⁻¹ :=
                mul_le_mul_left (hqpow_le m) _
            _ = valuation k q₀ / valuation k x := (div_eq_mul_inv _ _).symm
            _ < 1 := lt_trans hqdivx hx
        have hsv : valuation k (q₀ ^ (m : ℕ) * v⁻¹) < 1 := by
          rw [map_mul, map_pow, hvinv]
          calc valuation k q₀ ^ (m : ℕ) * (valuation k x)⁻¹
              ≤ valuation k q₀ * (valuation k x)⁻¹ :=
                mul_le_mul_left (hqpow_le m) _
            _ = valuation k q₀ / valuation k x := (div_eq_mul_inv _ _).symm
            _ < 1 := lt_trans hqdivx hx
        have hbr : valuation k
            (1 - (q₀ ^ (m : ℕ)) ^ 2 * u⁻¹ * v⁻¹) ≤ 1 := by
          refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
          · rw [map_one]
          · rw [map_mul, map_mul]
            calc valuation k ((q₀ ^ (m : ℕ)) ^ 2) * valuation k u⁻¹ *
                valuation k v⁻¹
                = valuation k (q₀ ^ (m : ℕ) * u⁻¹) *
                  valuation k (q₀ ^ (m : ℕ) * v⁻¹) := by
                  rw [map_mul, map_mul,
                    map_pow (valuation k) (q₀ ^ (m : ℕ)) 2, pow_two,
                    mul_assoc (valuation k (q₀ ^ (m : ℕ)) *
                      valuation k (q₀ ^ (m : ℕ)))]
                  exact mul_mul_mul_comm _ _ _ _
              _ ≤ 1 * 1 := mul_le_mul' (le_of_lt hsu) (le_of_lt hsv)
              _ = 1 := one_mul _
        rw [hkeyD _ _ _ (hone_sub_ne' _ hsu) (hone_sub_ne' _ hsv),
          map_div₀, map_mul, map_mul, map_mul]
        simp only [map_pow]
        rw [(valuation k).map_one_sub_of_lt hsu,
          (valuation k).map_one_sub_of_lt hsv]
        simp only [one_pow, mul_one, div_one]
        rw [hinvdiff]
        calc valuation k q₀ ^ (m : ℕ) *
            (valuation k (u - v) / (valuation k x * valuation k x)) *
            valuation k (1 - (q₀ ^ (m : ℕ)) ^ 2 * u⁻¹ * v⁻¹)
            ≤ valuation k q₀ ^ (m : ℕ) *
              (valuation k (u - v) / (valuation k x * valuation k x)) *
              1 := mul_le_mul' le_rfl hbr
          _ = valuation k q₀ ^ (m : ℕ) *
              (valuation k (u - v) / (valuation k x * valuation k x)) :=
              mul_one _
          _ ≤ valuation k q₀ *
              (valuation k (u - v) / (valuation k x * valuation k x)) :=
              mul_le_mul_left (hqpow_le m) _
          _ = valuation k q₀ / (valuation k x * valuation k x) *
              valuation k (u - v) := by
              rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
                mul_comm (valuation k (u - v))]
          _ ≤ ρ * valuation k (u - v) :=
              mul_le_mul_left (le_max_right _ _) _
      -- fold the differences and assemble
      obtain ⟨-, -, -, hqu', hquinv'⟩ := hshell u hu
      have hSu1 := summable_lambert_terms u q₀ hq1 hqu'
      have hSv1 := summable_lambert_terms v q₀ hq1 hqv
      have hSu2 := summable_lambert_terms u⁻¹ q₀ hq1 hquinv'
      have hSv2 := summable_lambert_terms v⁻¹ q₀ hq1 hqvinv
      have he1 : bilateralX u q₀ - u =
          (u / (1 - u) ^ 2 - u) +
          ((∑' m : ℕ+, q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 2) +
           (∑' m : ℕ+, q₀ ^ (m : ℕ) * u⁻¹ /
              (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 2) -
           2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
              q₀ ^ (N : ℕ))) := by
        rw [bilateralX]
        ring
      have he2 : bilateralX v q₀ - v =
          (v / (1 - v) ^ 2 - v) +
          ((∑' m : ℕ+, q₀ ^ (m : ℕ) * v / (1 - q₀ ^ (m : ℕ) * v) ^ 2) +
           (∑' m : ℕ+, q₀ ^ (m : ℕ) * v⁻¹ /
              (1 - q₀ ^ (m : ℕ) * v⁻¹) ^ 2) -
           2 * (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
              q₀ ^ (N : ℕ))) := by
        rw [bilateralX]
        ring
      rw [he1, he2, show ∀ L1 A1 B1 C L2 A2 B2 : k,
          (L1 + (A1 + B1 - 2 * C)) - (L2 + (A2 + B2 - 2 * C)) =
            (L1 - L2) + ((A1 - A2) + (B1 - B2)) from
        fun L1 A1 B1 C L2 A2 B2 => by ring]
      rw [← hSu1.tsum_sub hSv1, ← hSu2.tsum_sub hSv2]
      refine le_trans (Valuation.map_add _ _ _) (max_le hlead ?_)
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
      · exact valuation_tsum_le (hSu1.sub hSv1) _ htermD1
      · exact valuation_tsum_le (hSu2.sub hSv2) _ htermD2
    -- the iteration `H u = x - (bilateralX u - u)` and its orbit
    set H : k → k := fun u => x - (bilateralX u q₀ - u) with hHdef
    have hHshell : ∀ u : k, valuation k u = valuation k x →
        valuation k (H u) = valuation k x := by
      intro u hu
      simp only [hHdef]
      have he : valuation k (x - (bilateralX u q₀ - u)) =
          valuation k (-((bilateralX u q₀ - u) - x)) := by
        congr 1
        ring
      rw [he, Valuation.map_neg,
        (valuation k).map_sub_eq_of_lt_right
          (lt_of_le_of_lt (hGval u hu) hMxlt)]
    have hHdiff : ∀ u v : k, valuation k u = valuation k x →
        valuation k v = valuation k x →
        valuation k (H u - H v) ≤ ρ * valuation k (u - v) := by
      intro u v hu hv
      have he : H u - H v = -((bilateralX u q₀ - u) -
          (bilateralX v q₀ - v)) := by
        simp only [hHdef]
        ring
      rw [he, Valuation.map_neg]
      exact hGlip u v hu hv
    set seq : ℕ → k := fun n => H^[n] x with hseqdef
    have hseq_zero : seq 0 = x := rfl
    have hseq_succ : ∀ n, seq (n + 1) = H (seq n) := fun n =>
      Function.iterate_succ_apply' H n _
    have hseq_shell : ∀ n, valuation k (seq n) = valuation k x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [hseq_succ n]
        exact hHshell _ ih
    have hdiffA : ∀ n, valuation k (seq (n + 1) - seq n) ≤
        Mx * ρ ^ n := by
      intro n
      induction n with
      | zero =>
        rw [hseq_succ 0, hseq_zero, pow_zero, mul_one]
        have he : H x - x = -(bilateralX x q₀ - x) := by
          simp only [hHdef]
          ring
        rw [he, Valuation.map_neg]
        exact hGval x rfl
      | succ n ih =>
        rw [hseq_succ (n + 1), hseq_succ n]
        calc valuation k (H (H (seq n)) - H (seq n)) ≤
            ρ * valuation k (H (seq n) - seq n) :=
              hHdiff _ _ (hHshell _ (hseq_shell n)) (hseq_shell n)
          _ ≤ ρ * (Mx * ρ ^ n) := by
              refine mul_le_mul' le_rfl ?_
              have h5 := ih
              rwa [hseq_succ n] at h5
          _ = Mx * ρ ^ (n + 1) := by
              rw [pow_succ]
              rw [mul_comm ρ, mul_assoc]
    -- realize the constants as field elements and pass to the norm
    obtain ⟨cρ, hcρ⟩ := ValuativeRel.valuation_surjective (K := k) ρ
    have hcρ0 : cρ ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hcρ
      exact hρ0 hcρ.symm
    have hMx0 : Mx ≠ 0 := by
      intro hz
      have h1 : valuation k q₀ / valuation k x = 0 :=
        le_zero_iff.mp (hz ▸ le_max_right _ _)
      rw [div_eq_zero_iff] at h1
      rcases h1 with h1 | h1
      · exact hq0 ((Valuation.zero_iff _).mp h1)
      · exact hX0 h1
    obtain ⟨cM, hcM⟩ := ValuativeRel.valuation_surjective (K := k) Mx
    have hcM0 : cM ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hcM
      exact hMx0 hcM.symm
    -- rank-one analytic structure (the LocalField recipe)
    letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
    haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
    letI : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField _ _
    have hbridge_lt : ∀ z c : k, valuation k z < valuation k c ↔
        ‖z‖ < ‖c‖ :=
      fun z c => (Valued.toNormedField.norm_lt_iff).symm
    have hbridge_le : ∀ z c : k, valuation k z ≤ valuation k c ↔
        ‖z‖ ≤ ‖c‖ :=
      fun z c => (Valued.toNormedField.norm_le_iff).symm
    have hcauchy : CauchySeq seq := by
      refine cauchySeq_of_le_geometric ‖cρ‖ ‖cM‖ ?_ ?_
      · rw [← norm_one (α := k)]
        exact (hbridge_lt _ _).mp (by rw [hcρ, map_one]; exact hρ1)
      · intro n
        rw [dist_eq_norm]
        have h1 : valuation k (seq n - seq (n + 1)) ≤
            valuation k (cM * cρ ^ n) := by
          rw [map_mul, map_pow, hcρ, hcM,
            show seq n - seq (n + 1) = -(seq (n + 1) - seq n) from by
              ring, Valuation.map_neg]
          exact hdiffA n
        calc ‖seq n - seq (n + 1)‖ ≤ ‖cM * cρ ^ n‖ :=
            (hbridge_le _ _).mp h1
          _ = ‖cM‖ * ‖cρ‖ ^ n := by rw [norm_mul, norm_pow]
    obtain ⟨ustar, hus⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hconv : ∀ c : k, c ≠ 0 → ∀ᶠ n in Filter.atTop,
        valuation k (seq n - ustar) < valuation k c := by
      intro c hc
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hus ‖c‖
        (norm_pos_iff.mpr hc)
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have h2 := hN n hn
      rw [dist_eq_norm] at h2
      exact (hbridge_lt _ _).mpr h2
    -- the limit lies on the shell
    have hustar_val : valuation k ustar = valuation k x := by
      obtain ⟨n, hn⟩ := (hconv x hx0).exists
      rw [← hseq_shell n] at hn
      have he : valuation k ustar =
          valuation k (-((seq n - ustar) - seq n)) := by
        congr 1
        ring
      rw [he, Valuation.map_neg,
        (valuation k).map_sub_eq_of_lt_right hn]
      exact hseq_shell n
    -- the limit is a fixed point of `H`
    have hfix : H ustar = ustar := by
      by_contra hne
      have hΔ0 : H ustar - ustar ≠ 0 := sub_ne_zero_of_ne hne
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        (hconv (H ustar - ustar) hΔ0)
      have h1 : valuation k (seq N - ustar) <
          valuation k (H ustar - ustar) := hN N le_rfl
      have h2 : valuation k (seq (N + 1) - ustar) <
          valuation k (H ustar - ustar) := hN (N + 1) (Nat.le_succ N)
      have h3 : valuation k (H ustar - seq (N + 1)) <
          valuation k (H ustar - ustar) := by
        rw [hseq_succ N]
        calc valuation k (H ustar - H (seq N))
            ≤ ρ * valuation k (ustar - seq N) :=
              hHdiff _ _ hustar_val (hseq_shell N)
          _ ≤ 1 * valuation k (ustar - seq N) :=
              mul_le_mul_left (le_of_lt hρ1) _
          _ = valuation k (ustar - seq N) := one_mul _
          _ = valuation k (seq N - ustar) := by
              rw [show ustar - seq N = -(seq N - ustar) from by ring,
                Valuation.map_neg]
          _ < valuation k (H ustar - ustar) := h1
      have h4 : valuation k (H ustar - ustar) <
          valuation k (H ustar - ustar) := by
        calc valuation k (H ustar - ustar)
            = valuation k ((H ustar - seq (N + 1)) +
                (seq (N + 1) - ustar)) := by
              congr 1
              ring
          _ ≤ max (valuation k (H ustar - seq (N + 1)))
              (valuation k (seq (N + 1) - ustar)) :=
              Valuation.map_add _ _ _
          _ < valuation k (H ustar - ustar) := max_lt h3 h2
      exact absurd h4 (lt_irrefl _)
    -- conclusion: `bilateralX ustar = x` and the shell conditions
    have hbXeq : bilateralX ustar q₀ = x := by
      have h1 := hfix
      simp only [hHdef] at h1
      linear_combination -h1
    have hu0' : ustar ≠ 0 := fun hz =>
      hX0 (by rw [← hustar_val, hz, map_zero])
    have hu1' : ustar ≠ 1 := by
      intro hz
      rw [hz, map_one] at hustar_val
      rw [← hustar_val] at hx
      exact absurd hx (lt_irrefl _)
    exact ⟨ustar, hu0', hu1', by rw [hustar_val]; exact hqx,
      le_of_lt (hustar_val ▸ hx), hbXeq⟩
  · -- Case B (the boundary shell `|x|² ≤ |q|`, Silverman's `W`): work
    -- with the sum `S(u) = bilateralX u + bilateralY u`, whose Lambert
    -- kernels combine so that the `q/u`-term cancels exactly; the
    -- iteration `u ↦ (x+y) - (S(u) - u)` contracts on the shell
    -- `|u| = |y|`, and the fixed point matches both coordinates.
    push Not at hcase
    -- `|a₆| = |q|` exactly (leading coefficient `-1`)
    have ha₆exact : valuation k (WeierstrassCurve.tateA₆ q₀) =
        valuation k q₀ := by
      have h2 := valuation_evalInt_sub_sum_le q₀ hq1 a₆Formal 2
      have hsum : ∑ n ∈ Finset.range 2,
          ((PowerSeries.coeff n a₆Formal : ℤ) : k) * q₀ ^ n = -q₀ := by
        rw [Finset.sum_range_succ, Finset.sum_range_one]
        rw [coeff_a₆Formal, coeff_a₆Formal]
        simp
      rw [hsum] at h2
      rw [WeierstrassCurve.tateA₆_eq_evalInt q₀ hq1]
      have hq2lt : valuation k q₀ ^ 2 < valuation k q₀ := by
        rw [pow_two]
        exact mul_lt_of_lt_one_right
          (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hq0)) hq1
      have he : valuation k (evalInt q₀ a₆Formal) =
          valuation k (-q₀ + (evalInt q₀ a₆Formal - -q₀)) := by
        congr 1
        ring
      rw [he, (valuation k).map_add_eq_of_lt_left
        (by
          rw [Valuation.map_neg]
          exact lt_of_le_of_lt h2 hq2lt), Valuation.map_neg]
    -- the explicit equation and the `W`-shell magnitudes of `y`
    have heq : y ^ 2 + x * y = x ^ 3 +
        WeierstrassCurve.tateA₄ q₀ * x + WeierstrassCurve.tateA₆ q₀ := by
      have h1 := ((WeierstrassCurve.tateCurve q₀).toAffine.equation_iff
        x y).mp hxy
      simpa [WeierstrassCurve.tateCurve] using h1
    have ha₄ : valuation k (WeierstrassCurve.tateA₄ q₀) ≤
        valuation k q₀ := by
      rw [WeierstrassCurve.tateA₄_eq_evalInt q₀ hq1]
      calc valuation k (evalInt q₀ a₄Formal)
          ≤ valuation k q₀ ^ 1 := valuation_evalInt_le_pow q₀ hq1
            (fun m hm => by
              interval_cases m
              rw [coeff_a₄Formal]
              simp)
        _ = valuation k q₀ := pow_one _
    have hQ0 : valuation k q₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
    have hxsmall : valuation k x * valuation k x ≤ valuation k q₀ := by
      rwa [← pow_two]
    have hxlt1 : valuation k x < 1 := hx
    have hRHS : valuation k (x ^ 3 +
        WeierstrassCurve.tateA₄ q₀ * x + WeierstrassCurve.tateA₆ q₀) =
        valuation k q₀ := by
      rw [add_assoc]
      have hsm : valuation k (x ^ 3) < valuation k q₀ := by
        rw [map_pow]
        calc valuation k x ^ 3 = valuation k x * valuation k x *
            valuation k x := by rw [pow_succ, pow_two]
          _ ≤ valuation k q₀ * valuation k x :=
              mul_le_mul_left hxsmall _
          _ < valuation k q₀ * 1 :=
              mul_lt_mul_of_pos_left hxlt1 (zero_lt_iff.mpr hQ0)
          _ = valuation k q₀ := mul_one _
      have hsm2 : valuation k (WeierstrassCurve.tateA₄ q₀ * x) <
          valuation k q₀ := by
        rw [map_mul]
        calc valuation k (WeierstrassCurve.tateA₄ q₀) * valuation k x
            ≤ valuation k q₀ * valuation k x := mul_le_mul_left ha₄ _
          _ < valuation k q₀ * 1 :=
              mul_lt_mul_of_pos_left hxlt1 (zero_lt_iff.mpr hQ0)
          _ = valuation k q₀ := mul_one _
      have he2 : valuation k (x ^ 3 + (WeierstrassCurve.tateA₄ q₀ * x +
          WeierstrassCurve.tateA₆ q₀)) =
          valuation k (WeierstrassCurve.tateA₄ q₀ * x +
            WeierstrassCurve.tateA₆ q₀) := by
        refine (valuation k).map_add_eq_of_lt_right ?_
        rw [(valuation k).map_add_eq_of_lt_right
          (by rw [ha₆exact]; exact hsm2)]
        rw [ha₆exact]
        exact hsm
      rw [he2, (valuation k).map_add_eq_of_lt_right
        (by rw [ha₆exact]; exact hsm2), ha₆exact]
    have hfact : valuation k y * valuation k (y + x) = valuation k q₀ := by
      have h1 : y * (y + x) = y ^ 2 + x * y := by ring
      calc valuation k y * valuation k (y + x)
          = valuation k (y * (y + x)) := (map_mul _ _ _).symm
        _ = valuation k (y ^ 2 + x * y) := by rw [h1]
        _ = valuation k q₀ := by rw [heq]; exact hRHS
    have hy0 : y ≠ 0 := by
      intro hh
      rw [hh, map_zero, zero_mul] at hfact
      exact hQ0 hfact.symm
    have hY0 : valuation k y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    have hyx : valuation k (y + x) = valuation k y := by
      rcases lt_trichotomy (valuation k y) (valuation k (y + x)) with
        h | h | h
      · exfalso
        have hXG : valuation k x = valuation k (y + x) := by
          have he : valuation k x = valuation k (-(y - (y + x))) := by
            congr 1
            ring
          rw [he, Valuation.map_neg,
            (valuation k).map_sub_eq_of_lt_right h]
        have hbig : valuation k q₀ <
            valuation k (y + x) * valuation k (y + x) := by
          calc valuation k q₀ = valuation k y * valuation k (y + x) :=
              hfact.symm
            _ < valuation k (y + x) * valuation k (y + x) :=
              mul_lt_mul_of_pos_right h (zero_lt_iff.mpr (by
                intro hz
                rw [hz, mul_zero] at hfact
                exact hQ0 hfact.symm))
        rw [← hXG] at hbig
        exact absurd (lt_of_lt_of_le hbig hxsmall) (lt_irrefl _)
      · exact h.symm
      · exfalso
        have hXY : valuation k x = valuation k y := by
          have he : valuation k x = valuation k ((y + x) - y) := by
            congr 1
            ring
          rw [he, (valuation k).map_sub_eq_of_lt_right h]
        have hbig : valuation k q₀ <
            valuation k y * valuation k y := by
          calc valuation k q₀ = valuation k y * valuation k (y + x) :=
              hfact.symm
            _ < valuation k y * valuation k y :=
              mul_lt_mul_of_pos_left h (zero_lt_iff.mpr hY0)
        rw [← hXY] at hbig
        exact absurd (lt_of_lt_of_le hbig hxsmall) (lt_irrefl _)
    have hy2 : valuation k y * valuation k y = valuation k q₀ := by
      rw [← hfact, hyx]
    have hxy_le : valuation k x ≤ valuation k y := by
      by_contra hcon
      push Not at hcon
      have h1 : valuation k y * valuation k y <
          valuation k x * valuation k x :=
        lt_of_le_of_lt (mul_le_mul' hcon.le le_rfl)
          (mul_lt_mul_of_pos_left hcon (lt_of_le_of_lt zero_le hcon))
      rw [hy2] at h1
      exact absurd (lt_of_lt_of_le h1 hxsmall) (lt_irrefl _)
    have hylt1 : valuation k y < 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : (1 : ValueGroupWithZero k) ≤
          valuation k y * valuation k y := by
        calc (1 : ValueGroupWithZero k) = 1 * 1 := (one_mul _).symm
          _ ≤ valuation k y * valuation k y := mul_le_mul' hcon hcon
      rw [hy2] at h1
      exact absurd (lt_of_le_of_lt h1 hq1) (lt_irrefl _)
    have hone_sub_ne'' : ∀ z : k, valuation k z < 1 → 1 - z ≠ 0 := by
      intro z hz hh
      have h1 := (valuation k).map_one_sub_of_lt hz
      rw [hh, map_zero] at h1
      exact zero_ne_one h1
    have hbin1 : ∀ j : ℕ, valuation k (((j.choose 2 : ℕ) : k)) ≤ 1 := by
      intro j
      simpa using valuation_intCast_le_one (R := k) (j.choose 2)
    have hbin2 : ∀ j : ℕ,
        valuation k ((((j + 1).choose 2 : ℕ) : k)) ≤ 1 := by
      intro j
      simpa using valuation_intCast_le_one (R := k) ((j + 1).choose 2)
    -- shell windows: on `|u| = |y|` both Lambert windows are inside
    -- the disc, since `|q₀|/|y| = |y| < 1`
    have hwin : ∀ u : k, valuation k u = valuation k y →
        u ≠ 0 ∧ valuation k u < 1 ∧ valuation k (q₀ * u) < 1 ∧
          valuation k (q₀ * u⁻¹) = valuation k y := by
      intro u hu
      have hu0 : u ≠ 0 := fun hz => hY0 (by rw [← hu, hz, map_zero])
      have hult : valuation k u < 1 := hu ▸ hylt1
      refine ⟨hu0, hult, ?_, ?_⟩
      · rw [map_mul]
        calc valuation k q₀ * valuation k u
            ≤ valuation k q₀ * 1 := mul_le_mul' le_rfl (le_of_lt hult)
          _ = valuation k q₀ := mul_one _
          _ < 1 := hq1
      · rw [map_mul, map_inv₀, hu, ← hy2, mul_assoc,
          mul_inv_cancel₀ hY0, mul_one]
    -- the combined sum series: the Lambert kernels collapse, so the
    -- dangerous `q/u`-term cancels exactly
    have hSsum : ∀ u : k, valuation k u = valuation k y →
        bilateralX u q₀ + bilateralY u q₀ =
          u / (1 - u) ^ 3 +
          (∑' m : ℕ+, q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 3) -
          (∑' m : ℕ+, (q₀ ^ (m : ℕ) * u⁻¹) ^ 2 /
            (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) -
          (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
            q₀ ^ (N : ℕ)) := by
      intro u hu
      obtain ⟨hu0, hult, hqu, hquinv⟩ := hwin u hu
      have hquinv1 : valuation k (q₀ * u⁻¹) < 1 := by
        rw [hquinv]
        exact hylt1
      have h1u0 : (1 : k) - u ≠ 0 := hone_sub_ne'' u hult
      have hsm1 : ∀ m : ℕ+, valuation k (q₀ ^ (m : ℕ) * u) < 1 := by
        intro m
        rw [map_mul, map_pow]
        calc valuation k q₀ ^ (m : ℕ) * valuation k u
            ≤ valuation k q₀ * 1 :=
              mul_le_mul' (hqpow_le m) (le_of_lt hult)
          _ = valuation k q₀ := mul_one _
          _ < 1 := hq1
      have hsm2 : ∀ m : ℕ+, valuation k (q₀ ^ (m : ℕ) * u⁻¹) < 1 := by
        intro m
        rw [map_mul, map_pow, map_inv₀]
        calc valuation k q₀ ^ (m : ℕ) * (valuation k u)⁻¹
            ≤ valuation k q₀ * (valuation k u)⁻¹ :=
              mul_le_mul_left (hqpow_le m) _
          _ = valuation k (q₀ * u⁻¹) := by rw [map_mul, map_inv₀]
          _ < 1 := hquinv1
      have hA1 : Summable (fun m : ℕ+ ↦
          q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 2) :=
        summable_lambert_terms u q₀ hq1 hqu
      have hA2 : Summable (fun m : ℕ+ ↦
          (q₀ ^ (m : ℕ) * u) ^ 2 / (1 - q₀ ^ (m : ℕ) * u) ^ 3) :=
        summable_lambert_terms_general
          (fun j ↦ ((j.choose 2 : ℕ) : k)) (fun v ↦ v ^ 2 / (1 - v) ^ 3)
          hbin1 u q₀ hq1 hqu
          (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_self v₀ hv₀)
      have hB1 : Summable (fun m : ℕ+ ↦
          q₀ ^ (m : ℕ) * u⁻¹ / (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 2) :=
        summable_lambert_terms u⁻¹ q₀ hq1 hquinv1
      have hB2 : Summable (fun m : ℕ+ ↦
          q₀ ^ (m : ℕ) * u⁻¹ / (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) :=
        summable_lambert_terms_general
          (fun j ↦ (((j + 1).choose 2 : ℕ) : k)) (fun v ↦ v / (1 - v) ^ 3)
          hbin2 u⁻¹ q₀ hq1 hquinv1
          (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_succ v₀ hv₀)
      have hdirect : ∀ m : ℕ+,
          q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 2 +
            (q₀ ^ (m : ℕ) * u) ^ 2 / (1 - q₀ ^ (m : ℕ) * u) ^ 3 =
          q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 3 := by
        intro m
        have h0 := hone_sub_ne'' _ (hsm1 m)
        field_simp
        ring
      have hinverse : ∀ m : ℕ+,
          q₀ ^ (m : ℕ) * u⁻¹ / (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 2 -
            q₀ ^ (m : ℕ) * u⁻¹ / (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3 =
          -((q₀ ^ (m : ℕ) * u⁻¹) ^ 2 /
            (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) := by
        intro m
        have h0 := hone_sub_ne'' _ (hsm2 m)
        field_simp
        ring
      have hlead : u / (1 - u) ^ 2 + u ^ 2 / (1 - u) ^ 3 =
          u / (1 - u) ^ 3 := by
        field_simp
        ring
      have hc1 : (∑' m : ℕ+,
          q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 2) +
          (∑' m : ℕ+, (q₀ ^ (m : ℕ) * u) ^ 2 /
            (1 - q₀ ^ (m : ℕ) * u) ^ 3) =
          ∑' m : ℕ+, q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 3 := by
        rw [← hA1.tsum_add hA2]
        exact tsum_congr fun m => hdirect m
      have hc2 : (∑' m : ℕ+,
          q₀ ^ (m : ℕ) * u⁻¹ / (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 2) -
          (∑' m : ℕ+, q₀ ^ (m : ℕ) * u⁻¹ /
            (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) =
          -(∑' m : ℕ+, (q₀ ^ (m : ℕ) * u⁻¹) ^ 2 /
            (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) := by
        rw [← hB1.tsum_sub hB2, ← tsum_neg]
        exact tsum_congr fun m => hinverse m
      rw [bilateralX, bilateralY]
      linear_combination hc1 + hc2 + hlead
    -- `|q₀| = |y|²` in the useful directions
    have hq_eq : valuation k q₀ = valuation k y * valuation k y := hy2.symm
    have hqlty : valuation k q₀ < valuation k y := by
      rw [hq_eq]
      exact mul_lt_of_lt_one_right (zero_lt_iff.mpr hY0) hylt1
    -- the tail bound: `|S(u) - u| ≤ |q₀| < |y|` on the shell
    have hGBval : ∀ u : k, valuation k u = valuation k y →
        valuation k ((bilateralX u q₀ + bilateralY u q₀) - u) ≤
          valuation k q₀ := by
      intro u hu
      obtain ⟨hu0, hult, hqu, hquinv⟩ := hwin u hu
      have hquinv1 : valuation k (q₀ * u⁻¹) < 1 := by
        rw [hquinv]
        exact hylt1
      have h1u0 : (1 : k) - u ≠ 0 := hone_sub_ne'' u hult
      have h1u : valuation k (1 - u) = 1 :=
        (valuation k).map_one_sub_of_lt hult
      have hsm1 : ∀ m : ℕ+, valuation k (q₀ ^ (m : ℕ) * u) < 1 := by
        intro m
        rw [map_mul, map_pow]
        calc valuation k q₀ ^ (m : ℕ) * valuation k u
            ≤ valuation k q₀ * 1 :=
              mul_le_mul' (hqpow_le m) (le_of_lt hult)
          _ = valuation k q₀ := mul_one _
          _ < 1 := hq1
      have hsm2 : ∀ m : ℕ+, valuation k (q₀ ^ (m : ℕ) * u⁻¹) ≤
          valuation k y := by
        intro m
        rw [map_mul, map_pow, map_inv₀]
        calc valuation k q₀ ^ (m : ℕ) * (valuation k u)⁻¹
            ≤ valuation k q₀ * (valuation k u)⁻¹ :=
              mul_le_mul_left (hqpow_le m) _
          _ = valuation k (q₀ * u⁻¹) := by rw [map_mul, map_inv₀]
          _ = valuation k y := hquinv
      rw [hSsum u hu]
      have hlead3 : valuation k (u / (1 - u) ^ 3 - u) ≤
          valuation k q₀ := by
        have hid : u / (1 - u) ^ 3 - u =
            u ^ 2 * (3 - 3 * u + u ^ 2) / (1 - u) ^ 3 := by
          field_simp
          ring
        rw [hid, map_div₀, map_mul, map_pow, map_pow, hu, h1u, one_pow,
          div_one]
        have hbr : valuation k (3 - 3 * u + u ^ 2) ≤ 1 := by
          refine le_trans (Valuation.map_add _ _ _) (max_le
            (le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)) ?_)
          · simpa using valuation_intCast_le_one (R := k) 3
          · rw [map_mul]
            calc valuation k 3 * valuation k u
                ≤ 1 * 1 := mul_le_mul'
                  (by simpa using valuation_intCast_le_one (R := k) 3)
                  (le_of_lt hult)
              _ = 1 := one_mul _
          · rw [map_pow]
            calc valuation k u ^ 2 ≤ 1 ^ 2 :=
                pow_le_pow_left' (le_of_lt hult) 2
              _ = 1 := one_pow _
        calc valuation k y ^ 2 * valuation k (3 - 3 * u + u ^ 2)
            ≤ valuation k y ^ 2 * 1 := mul_le_mul' le_rfl hbr
          _ = valuation k y * valuation k y := by rw [mul_one, pow_two]
          _ = valuation k q₀ := hy2
      have hS1 : valuation k (∑' m : ℕ+,
          q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 3) ≤
            valuation k q₀ := by
        refine htsum_pnat _ (summable_lambert_terms_general
          (fun j ↦ (((j + 1).choose 2 : ℕ) : k)) (fun v ↦ v / (1 - v) ^ 3)
          hbin2 u q₀ hq1 hqu
          (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_succ v₀ hv₀)) _ ?_
        intro m
        rw [map_div₀, map_mul, map_pow, map_pow,
          (valuation k).map_one_sub_of_lt (hsm1 m), one_pow, div_one]
        calc valuation k q₀ ^ (m : ℕ) * valuation k u
            ≤ valuation k q₀ * 1 :=
              mul_le_mul' (hqpow_le m) (le_of_lt hult)
          _ = valuation k q₀ := mul_one _
      have hS2 : valuation k (∑' m : ℕ+,
          (q₀ ^ (m : ℕ) * u⁻¹) ^ 2 /
            (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) ≤ valuation k q₀ := by
        refine htsum_pnat _ (summable_lambert_terms_general
          (fun j ↦ ((j.choose 2 : ℕ) : k)) (fun v ↦ v ^ 2 / (1 - v) ^ 3)
          hbin1 u⁻¹ q₀ hq1 hquinv1
          (fun v₀ hv₀ ↦ hasSum_pnat_choose_two_self v₀ hv₀)) _ ?_
        intro m
        have hsm2' : valuation k (q₀ ^ (m : ℕ) * u⁻¹) < 1 :=
          lt_of_le_of_lt (hsm2 m) hylt1
        rw [map_div₀, map_pow, map_pow,
          (valuation k).map_one_sub_of_lt hsm2', one_pow, div_one]
        calc valuation k (q₀ ^ (m : ℕ) * u⁻¹) ^ 2
            ≤ valuation k y ^ 2 := pow_le_pow_left' (hsm2 m) 2
          _ = valuation k q₀ := by rw [pow_two, hy2]
      have hσ2 : valuation k (∑' N : ℕ+,
          (∑ d ∈ (N : ℕ).divisors, (d : k)) * q₀ ^ (N : ℕ)) ≤
            valuation k q₀ := by
        refine htsum_pnat _ (summable_sigma_one_nonarch q₀ hq1) _ ?_
        intro N
        rw [map_mul, map_pow]
        have hd1 : valuation k
            (∑ d ∈ (N : ℕ).divisors, (d : k)) ≤ 1 :=
          Valuation.map_sum_le _ fun d _ => by
            simpa using valuation_intCast_le_one (R := k) d
        calc valuation k (∑ d ∈ (N : ℕ).divisors, (d : k)) *
            valuation k q₀ ^ (N : ℕ)
            ≤ 1 * valuation k q₀ ^ (N : ℕ) := mul_le_mul_left hd1 _
          _ = valuation k q₀ ^ (N : ℕ) := one_mul _
          _ ≤ valuation k q₀ := hqpow_le N
      have he : (u / (1 - u) ^ 3 +
          (∑' m : ℕ+, q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 3) -
          (∑' m : ℕ+, (q₀ ^ (m : ℕ) * u⁻¹) ^ 2 /
            (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) -
          (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
            q₀ ^ (N : ℕ))) - u =
          ((u / (1 - u) ^ 3 - u) +
          (∑' m : ℕ+, q₀ ^ (m : ℕ) * u / (1 - q₀ ^ (m : ℕ) * u) ^ 3)) -
          ((∑' m : ℕ+, (q₀ ^ (m : ℕ) * u⁻¹) ^ 2 /
            (1 - q₀ ^ (m : ℕ) * u⁻¹) ^ 3) +
          (∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, (d : k)) *
            q₀ ^ (N : ℕ))) := by
        ring
      rw [he]
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
      · exact le_trans (Valuation.map_add _ _ _) (max_le hlead3 hS1)
      · exact le_trans (Valuation.map_add _ _ _) (max_le hS2 hσ2)
    sorry

/-- **`x`-surjectivity onto the annulus** (DERIVED 2026-07-20 by case
split on `valuation k x` against `1`, dispatching to the two Silverman
cases above — ATAEC V.3.1(d)/V.4). -/
theorem exists_annulus_bilateralX_eq (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq1 : valuation k q₀ < 1) (x y : k)
    (hxy : (WeierstrassCurve.tateCurve q₀).toAffine.Equation x y) :
    ∃ u : k, u ≠ 0 ∧ u ≠ 1 ∧ valuation k q₀ < valuation k u ∧
      valuation k u ≤ 1 ∧ bilateralX u q₀ = x := by
  rcases lt_or_ge (valuation k x) 1 with hx | hx
  · exact exists_annulus_bilateralX_eq_of_lt_one q₀ hq0 hq1 x y hxy hx
  · exact exists_annulus_bilateralX_eq_of_one_le q₀ hq0 hq1 x y hxy hx

/-- **Surjectivity of the uniformisation** (DERIVED 2026-07-18 from the
`x`-onto leaf `exists_annulus_bilateralX_eq` — Silverman V.3.1(d)/V.4):
every point of the Tate curve is a `pointMapQuot`-value. The leaf
produces an annulus parameter over the `x`-coordinate; the quadratic in
`y` has exactly the two roots `bilateralY u` and `negY` of it
(`Y_eq_of_X_eq`), realised by `u` and by its inverse partner (`u⁻¹` on
the valuation-one shell, `q·u⁻¹` in the interior — the PROVEN vertical
case `bilateral_negY_of_mul_trivial`). -/
theorem pointMapQuot_surjective [DecidableEq k] (q : kˣ)
    (hq : valuation k (q : k) < 1) :
    Function.Surjective (pointMapQuot q hq) := by
  have hq0 : (q : k) ≠ 0 := q.ne_zero
  have hqv : valuation k (q : k) ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have hqpos : (0 : ValueGroupWithZero k) < valuation k (q : k) :=
    zero_lt_iff.mpr hqv
  have hsq_lt : valuation k (q : k) * valuation k (q : k) <
      valuation k (q : k) := by
    calc valuation k (q : k) * valuation k (q : k)
        < 1 * valuation k (q : k) :=
          (OrderIso.mulRight₀ _ hqpos).strictMono hq
      _ = valuation k (q : k) := one_mul _
  intro P
  cases P with
  | zero => exact ⟨1, pointMapQuot_one q hq⟩
  | some x y h =>
    obtain ⟨u, hu0, hu1, hulow, huhigh, hbX⟩ :=
      exists_annulus_bilateralX_eq (q : k) hq0 hq x y h.1
    have huq : u ≠ (q : k) := fun heq => absurd hulow (by
      rw [heq]; exact lt_irrefl _)
    have huwin : valuation k (q : k) * valuation k (q : k) <
        valuation k u := lt_trans hsq_lt hulow
    have hpm := pointMap_eq_bilateral u (q : k) hu0 hu1 huq hq0 hq
      huwin huhigh
    have hequ : (WeierstrassCurve.tateCurve (q : k)).toAffine.Equation
        (bilateralX u (q : k)) (bilateralY u (q : k)) :=
      (nonsingular_bilateral u (q : k) hu0 hu1 huq hq0 hq huwin huhigh).1
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h.1 hequ hbX.symm with hy | hy
    · -- `y = bilateralY u`: the point is `pointMap u`
      refine ⟨QuotientGroup.mk (Units.mk0 u hu0), ?_⟩
      have hcoe : pointMapQuot q hq (QuotientGroup.mk (Units.mk0 u hu0)) =
          pointMap (q : k) hq0 hq u hu0 := by
        rw [pointMapQuot_mk]; exact pointMap_congr rfl
      rw [hcoe, hpm]
      exact point_some_congr hbX hy.symm
    · -- `y = negY`: the point is `pointMap` of the inverse partner
      rcases eq_or_lt_of_le huhigh with hshell | hint
      · -- `|u| = 1`: partner `v = u⁻¹`
        set v : k := u⁻¹ with hvdef
        have hv0 : v ≠ 0 := inv_ne_zero hu0
        have hv1 : v ≠ 1 := fun hv => hu1 (by
          rw [← inv_inv u, ← hvdef, hv, inv_one])
        have htriv : u * v = 1 ∨ u * v = (q : k) :=
          Or.inl (mul_inv_cancel₀ hu0)
        obtain ⟨hXv, hYv⟩ := bilateral_negY_of_mul_trivial u v (q : k)
          hu0 hu1 hv0 hq0 hq hulow huhigh htriv
        have hvval : valuation k v = 1 := by
          rw [hvdef, map_inv₀, hshell, inv_one]

        have hvlow : valuation k (q : k) < valuation k v := by
          rw [hvval]; exact hq
        have hvhigh : valuation k v ≤ 1 := le_of_eq hvval
        have hvq : v ≠ (q : k) := fun heq => absurd hvlow (by
          rw [heq]; exact lt_irrefl _)
        have hvwin : valuation k (q : k) * valuation k (q : k) <
            valuation k v := lt_trans hsq_lt hvlow
        refine ⟨QuotientGroup.mk (Units.mk0 v hv0), ?_⟩
        have hcoe : pointMapQuot q hq (QuotientGroup.mk (Units.mk0 v hv0)) =
            pointMap (q : k) hq0 hq v hv0 := by
          rw [pointMapQuot_mk]; exact pointMap_congr rfl
        rw [hcoe,
          pointMap_eq_bilateral v (q : k) hv0 hv1 hvq hq0 hq hvwin hvhigh]
        exact point_some_congr (hXv.trans hbX)
          (by rw [hYv, ← hy])
      · -- `|u| < 1`: partner `v = q·u⁻¹`
        set v : k := (q : k) * u⁻¹ with hvdef
        have hv0 : v ≠ 0 := mul_ne_zero hq0 (inv_ne_zero hu0)
        have hv1 : v ≠ 1 := by
          intro hv
          apply huq
          have h2 : (q : k) * u⁻¹ * u = 1 * u := by rw [← hvdef, hv]
          rw [mul_assoc, inv_mul_cancel₀ hu0, mul_one, one_mul] at h2
          exact h2.symm
        have htriv : u * v = 1 ∨ u * v = (q : k) := Or.inr (by
          rw [hvdef, mul_comm ((q : k)) _, ← mul_assoc,
            mul_inv_cancel₀ hu0, one_mul])
        obtain ⟨hXv, hYv⟩ := bilateral_negY_of_mul_trivial u v (q : k)
          hu0 hu1 hv0 hq0 hq hulow huhigh htriv
        have huv : valuation k u ≠ 0 := (Valuation.ne_zero_iff _).mpr hu0
        have hupos : (0 : ValueGroupWithZero k) < valuation k u :=
          zero_lt_iff.mpr huv
        have huinvpos : (0 : ValueGroupWithZero k) < (valuation k u)⁻¹ :=
          zero_lt_iff.mpr (inv_ne_zero huv)
        have hvval : valuation k v =
            valuation k (q : k) * (valuation k u)⁻¹ := by
          rw [hvdef, map_mul, map_inv₀]
        have hvlow : valuation k (q : k) < valuation k v := by
          rw [hvval]
          calc valuation k (q : k)
              = valuation k (q : k) * 1 := (mul_one _).symm
            _ < valuation k (q : k) * (valuation k u)⁻¹ := by
                have h3 : (1 : ValueGroupWithZero k) < (valuation k u)⁻¹ := by
                  calc (1 : ValueGroupWithZero k)
                      = valuation k u * (valuation k u)⁻¹ :=
                        (mul_inv_cancel₀ huv).symm
                    _ < 1 * (valuation k u)⁻¹ :=
                        (OrderIso.mulRight₀ _ huinvpos).strictMono hint
                    _ = (valuation k u)⁻¹ := one_mul _
                exact (OrderIso.mulLeft₀ _ hqpos).strictMono h3
        have hvhigh : valuation k v ≤ 1 := by
          rw [hvval]
          calc valuation k (q : k) * (valuation k u)⁻¹
              ≤ valuation k u * (valuation k u)⁻¹ :=
                mul_le_mul_left hulow.le _
            _ = 1 := mul_inv_cancel₀ huv
        have hvq : v ≠ (q : k) := fun heq => hu1 (by
          have h2 : (q : k) * u⁻¹ * u = (q : k) * u := by
            rw [← hvdef, heq]
          rw [mul_assoc, inv_mul_cancel₀ hu0, mul_one] at h2
          have h2' : (q : k) * u = (q : k) * 1 := by
            rw [mul_one]; exact h2.symm
          exact mul_left_cancel₀ hq0 h2')
        have hvwin : valuation k (q : k) * valuation k (q : k) <
            valuation k v := lt_trans hsq_lt hvlow
        refine ⟨QuotientGroup.mk (Units.mk0 v hv0), ?_⟩
        have hcoe : pointMapQuot q hq (QuotientGroup.mk (Units.mk0 v hv0)) =
            pointMap (q : k) hq0 hq v hv0 := by
          rw [pointMapQuot_mk]; exact pointMap_congr rfl
        rw [hcoe,
          pointMap_eq_bilateral v (q : k) hv0 hv1 hvq hq0 hq hvwin hvhigh]
        exact point_some_congr (hXv.trans hbX)
          (by rw [hYv, ← hy])

/-- Negation compatibility, derived from the addition law and the
trivial-class image. -/
theorem pointMapQuot_inv [DecidableEq k] (q : kˣ)
    (hq : valuation k (q : k) < 1) (x : kˣ ⧸ Subgroup.zpowers q) :
    pointMapQuot q hq x⁻¹ = -(pointMapQuot q hq x) := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← pointMapQuot_add q hq x⁻¹ x, inv_mul_cancel]
  exact pointMapQuot_one q hq

/-- The kernel is trivial on all classes (quotient induction over
`pointMapQuot_eq_zero_iff`). -/
theorem pointMapQuot_eq_zero_iff' (q : kˣ)
    (hq : valuation k (q : k) < 1) (x : kˣ ⧸ Subgroup.zpowers q) :
    pointMapQuot q hq x = 0 ↔ x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u => exact pointMapQuot_eq_zero_iff q hq u

/-- **Bijectivity of the uniformisation**, derived top-down:
injectivity from the trivial kernel (`pointMapQuot_eq_zero_iff'`) and
the addition law (`pointMapQuot_add`); surjectivity is the remaining
sorried leaf (`pointMapQuot_surjective`). -/
theorem pointMapQuot_bijective [DecidableEq k] (q : kˣ)
    (hq : valuation k (q : k) < 1) :
    Function.Bijective (pointMapQuot q hq) := by
  constructor
  · intro x y hxy
    have h0 : pointMapQuot q hq (x * y⁻¹) = 0 := by
      rw [pointMapQuot_add q hq x y⁻¹, pointMapQuot_inv q hq y, hxy]
      exact add_neg_cancel _
    have h1 : x * y⁻¹ = 1 := (pointMapQuot_eq_zero_iff' q hq _).mp h0
    calc x = x * y⁻¹ * y := by group
      _ = 1 * y := by rw [h1]
      _ = y := one_mul y
  · exact pointMapQuot_surjective q hq

/-- **The finite-level Tate uniformisation** (derived from the two
leaves above): the canonical additive equivalence
`kˣ/q^ℤ ≃+ E_q(k)`, whose underlying function is `pointMapQuot` — in
particular it is canonical (choice-free), hence compatible with field
extensions and Galois actions, which is what the gluing over the
separable closure consumes. -/
noncomputable def tateCurveEquiv [DecidableEq k] (q : kˣ)
    (hq : valuation k (q : k) < 1) :
    Additive (kˣ ⧸ Subgroup.zpowers q) ≃+
      (WeierstrassCurve.tateCurve (q : k)).toAffine.Point where
  toFun x := pointMapQuot q hq x.toMul
  invFun P := Additive.ofMul
    ((Equiv.ofBijective _ (pointMapQuot_bijective q hq)).symm P)
  left_inv x := by
    have h := (Equiv.ofBijective _
      (pointMapQuot_bijective q hq)).symm_apply_apply x.toMul
    exact congrArg Additive.ofMul h
  right_inv P := (Equiv.ofBijective _
    (pointMapQuot_bijective q hq)).apply_symm_apply P
  map_add' x y := pointMapQuot_add q hq x.toMul y.toMul

@[simp]
theorem tateCurveEquiv_apply [DecidableEq k] (q : kˣ)
    (hq : valuation k (q : k) < 1)
    (x : Additive (kˣ ⧸ Subgroup.zpowers q)) :
    tateCurveEquiv q hq x = pointMapQuot q hq x.toMul :=
  rfl

end Annulus

end TateCurve

end
