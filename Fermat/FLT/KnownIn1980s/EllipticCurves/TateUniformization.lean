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

set_option warn.sorry false in
/-- **Extended-annulus bilateral bridge for `X`** (sorry node): the
`evalA`-sum agrees with the bilateral value also on the upper half
`1 < |u₀| < |q₀|⁻¹` of the extended annulus (rearrangement of the
`(u, q)`-graded double series along the other Lambert splitting). -/
theorem evalA_XA_eq_bilateralX_ext (u₀ q₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) (hq1 : valuation k q₀ < 1)
    (hu : 1 < valuation k u₀) (hqu : valuation k (q₀ * u₀) < 1) :
    evalA u₀ q₀ h0 h1 XA = bilateralX u₀ q₀ :=
  sorry

set_option warn.sorry false in
/-- **Extended-annulus bilateral bridge for `Y`** (sorry node). -/
theorem evalA_YA_eq_bilateralY_ext (u₀ q₀ : k) (h0 : u₀ ≠ 0)
    (h1 : u₀ ≠ 1) (hq1 : valuation k q₀ < 1)
    (hu : 1 < valuation k u₀) (hqu : valuation k (q₀ * u₀) < 1) :
    evalA u₀ q₀ h0 h1 YA = bilateralY u₀ q₀ :=
  sorry

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

set_option warn.sorry false in
/-- **Injectivity of the bilateral coordinate pair on the annulus** (sorry
node — Silverman V.4, the injectivity half): two annulus parameters with
the same bilateral `x`- AND `y`-values coincide. Attack: the difference
`X(u) - X(v)` as a series in the annulus (theta-quotient/Newton-polygon
analysis over the complete field `k`), with the `y`-value separating the
two sheets. -/
theorem bilateralXY_inj (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1) (hv0 : v₀ ≠ 0) (hv1 : v₀ ≠ 1)
    (hq0 : q₀ ≠ 0) (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1)
    (hX : bilateralX u₀ q₀ = bilateralX v₀ q₀)
    (hY : bilateralY u₀ q₀ = bilateralY v₀ q₀) :
    u₀ = v₀ :=
  sorry

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

/-- **Non-`2`-torsion of nontrivial-square annulus parameters** (sorry
node): for an annulus parameter whose square is not in the trivial class,
the bilateral point is not `2`-torsion — its `y`-value differs from `negY`
of itself. Series content: `2Y(u) + X(u) = 0` characterises the three
nontrivial `2`-torsion parameters `u ∈ {-1, ±√q}·q^ℤ`. -/
theorem bilateral_ne_negY_of_sq_nontrivial (u₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1) (hq0 : q₀ ≠ 0)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hsq1 : u₀ * u₀ ≠ 1) (hsqq : u₀ * u₀ ≠ q₀) :
    bilateralY u₀ q₀ ≠ (WeierstrassCurve.tateCurve q₀).toAffine.negY
      (bilateralX u₀ q₀) (bilateralY u₀ q₀) := by
  intro heq
  have hqv : valuation k q₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have huv : valuation k u₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hu0
  rcases lt_or_eq_of_le huhigh with hlt | hone
  · -- interior case: the inverse-class representative is `q₀ * u₀⁻¹`
    set v₀ := q₀ * u₀⁻¹ with hv₀
    have hv0 : v₀ ≠ 0 := mul_ne_zero hq0 (inv_ne_zero hu0)
    have hv1 : v₀ ≠ 1 := by
      intro h1
      rw [hv₀] at h1
      have huq : u₀ = q₀ := by
        field_simp at h1
        exact h1.symm
      rw [huq] at hulow
      exact absurd hulow (lt_irrefl _)
    have hvval : valuation k v₀ = valuation k q₀ * (valuation k u₀)⁻¹ := by
      rw [hv₀, map_mul, map_inv₀]
    have hvlow : valuation k q₀ < valuation k v₀ := by
      rw [hvval]
      have hinvgt : (1 : ValueGroupWithZero k) < (valuation k u₀)⁻¹ := by
        have hpos : (0 : ValueGroupWithZero k) < (valuation k u₀)⁻¹ :=
          zero_lt_iff.mpr (inv_ne_zero huv)
        calc (1 : ValueGroupWithZero k)
            = valuation k u₀ * (valuation k u₀)⁻¹ := (mul_inv_cancel₀ huv).symm
          _ < 1 * (valuation k u₀)⁻¹ :=
              (OrderIso.mulRight₀ _ hpos).strictMono hlt
          _ = (valuation k u₀)⁻¹ := one_mul _
      calc valuation k q₀ = valuation k q₀ * 1 := (mul_one _).symm
        _ < valuation k q₀ * (valuation k u₀)⁻¹ :=
            (OrderIso.mulLeft₀ _ (zero_lt_iff.mpr hqv)).strictMono hinvgt
    have hvhigh : valuation k v₀ ≤ 1 := by
      rw [hvval]
      calc valuation k q₀ * (valuation k u₀)⁻¹
          ≤ valuation k u₀ * (valuation k u₀)⁻¹ :=
            mul_le_mul_left (le_of_lt hulow) _
        _ = 1 := mul_inv_cancel₀ huv
    have hmul := bilateral_negY_of_mul_trivial u₀ v₀ q₀ hu0 hu1 hv0 hq0 hq1
      hulow huhigh (Or.inr (by rw [hv₀]; field_simp))
    have hXeq : bilateralX u₀ q₀ = bilateralX v₀ q₀ := hmul.1.symm
    have hYeq : bilateralY u₀ q₀ = bilateralY v₀ q₀ := by
      rw [hmul.2]
      exact heq
    have huv₀ := bilateralXY_inj u₀ v₀ q₀ hu0 hu1 hv0 hv1 hq0 hq1
      hulow huhigh hvlow hvhigh hXeq hYeq
    refine hsqq ?_
    calc u₀ * u₀ = u₀ * v₀ := by nth_rw 2 [huv₀]
      _ = q₀ := by rw [hv₀]; field_simp
  · -- boundary case: the inverse-class representative is `u₀⁻¹`
    set v₀ := u₀⁻¹ with hv₀
    have hv0 : v₀ ≠ 0 := inv_ne_zero hu0
    have hv1 : v₀ ≠ 1 := by
      intro h1
      rw [hv₀] at h1
      exact hu1 (by rw [← inv_inv u₀, h1, inv_one])
    have hvval : valuation k v₀ = 1 := by
      rw [hv₀, map_inv₀, hone, inv_one]
    have hvlow : valuation k q₀ < valuation k v₀ := by
      rw [hvval]
      exact hq1
    have hvhigh : valuation k v₀ ≤ 1 := le_of_eq hvval
    have hmul := bilateral_negY_of_mul_trivial u₀ v₀ q₀ hu0 hu1 hv0 hq0 hq1
      hulow huhigh (Or.inl (mul_inv_cancel₀ hu0))
    have hXeq : bilateralX u₀ q₀ = bilateralX v₀ q₀ := hmul.1.symm
    have hYeq : bilateralY u₀ q₀ = bilateralY v₀ q₀ := by
      rw [hmul.2]
      exact heq
    have huv₀ := bilateralXY_inj u₀ v₀ q₀ hu0 hu1 hv0 hv1 hq0 hq1
      hulow huhigh hvlow hvhigh hXeq hYeq
    refine hsq1 ?_
    calc u₀ * u₀ = u₀ * v₀ := by nth_rw 2 [huv₀]
      _ = 1 := by rw [hv₀]; exact mul_inv_cancel₀ hu0

set_option warn.sorry false in
/-- **The cleared tangent `X`-identity** (sorry node — the
denominator-free form of Silverman V.3.1(c), doubling case, `x`-part):
with `M` the tangent-slope numerator and `E` its denominator
(`y - negY`), the identity `(X(u²) + 2X(u))·E² = M² + M·E`. Same series
content as the cleared chord identities, along the diagonal. -/
theorem bilateral_tangentX_cleared (u₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1) (hq0 : q₀ ≠ 0)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hsq1 : u₀ * u₀ ≠ 1) (hsqq : u₀ * u₀ ≠ q₀) :
    (bilateralX (u₀ * u₀) q₀ + 2 * bilateralX u₀ q₀) *
        (bilateralY u₀ q₀ - (WeierstrassCurve.tateCurve q₀).toAffine.negY
          (bilateralX u₀ q₀) (bilateralY u₀ q₀)) ^ 2 =
      (3 * bilateralX u₀ q₀ ^ 2 +
          2 * (WeierstrassCurve.tateCurve q₀).toAffine.a₂ * bilateralX u₀ q₀ +
          (WeierstrassCurve.tateCurve q₀).toAffine.a₄ -
          (WeierstrassCurve.tateCurve q₀).toAffine.a₁ * bilateralY u₀ q₀) ^ 2 +
        (3 * bilateralX u₀ q₀ ^ 2 +
          2 * (WeierstrassCurve.tateCurve q₀).toAffine.a₂ * bilateralX u₀ q₀ +
          (WeierstrassCurve.tateCurve q₀).toAffine.a₄ -
          (WeierstrassCurve.tateCurve q₀).toAffine.a₁ * bilateralY u₀ q₀) *
        (bilateralY u₀ q₀ - (WeierstrassCurve.tateCurve q₀).toAffine.negY
          (bilateralX u₀ q₀) (bilateralY u₀ q₀)) :=
  sorry

set_option warn.sorry false in
/-- **The cleared tangent `Y`-identity** (sorry node — the
denominator-free form of Silverman V.3.1(c), doubling case, `y`-part),
linear in the `x`-part output. Same series content. -/
theorem bilateral_tangentY_cleared (u₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1) (hq0 : q₀ ≠ 0)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hsq1 : u₀ * u₀ ≠ 1) (hsqq : u₀ * u₀ ≠ q₀) :
    -(bilateralY (u₀ * u₀) q₀ + bilateralX (u₀ * u₀) q₀) *
        (bilateralY u₀ q₀ - (WeierstrassCurve.tateCurve q₀).toAffine.negY
          (bilateralX u₀ q₀) (bilateralY u₀ q₀)) =
      (3 * bilateralX u₀ q₀ ^ 2 +
          2 * (WeierstrassCurve.tateCurve q₀).toAffine.a₂ * bilateralX u₀ q₀ +
          (WeierstrassCurve.tateCurve q₀).toAffine.a₄ -
          (WeierstrassCurve.tateCurve q₀).toAffine.a₁ * bilateralY u₀ q₀) *
          (bilateralX (u₀ * u₀) q₀ - bilateralX u₀ q₀) +
        bilateralY u₀ q₀ *
        (bilateralY u₀ q₀ - (WeierstrassCurve.tateCurve q₀).toAffine.negY
          (bilateralX u₀ q₀) (bilateralY u₀ q₀)) :=
  sorry

/-- **The tangent identity** (DERIVED 2026-07-18 from the cleared tangent
identities and the non-`2`-torsion leaf — Silverman V.3.1(c), doubling
case): the division bookkeeping of the tangent slope is handled here;
the series content is the cleared identities. -/
theorem bilateral_add_self [DecidableEq k] (u₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1) (hq0 : q₀ ≠ 0)
    (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hsq1 : u₀ * u₀ ≠ 1) (hsqq : u₀ * u₀ ≠ q₀) :
    bilateralY u₀ q₀ ≠ (WeierstrassCurve.tateCurve q₀).toAffine.negY
      (bilateralX u₀ q₀) (bilateralY u₀ q₀) ∧
    bilateralX (u₀ * u₀) q₀ =
      (WeierstrassCurve.tateCurve q₀).toAffine.addX (bilateralX u₀ q₀)
        (bilateralX u₀ q₀)
        ((WeierstrassCurve.tateCurve q₀).toAffine.slope (bilateralX u₀ q₀)
          (bilateralX u₀ q₀) (bilateralY u₀ q₀) (bilateralY u₀ q₀)) ∧
    bilateralY (u₀ * u₀) q₀ =
      (WeierstrassCurve.tateCurve q₀).toAffine.addY (bilateralX u₀ q₀)
        (bilateralX u₀ q₀) (bilateralY u₀ q₀)
        ((WeierstrassCurve.tateCurve q₀).toAffine.slope (bilateralX u₀ q₀)
          (bilateralX u₀ q₀) (bilateralY u₀ q₀) (bilateralY u₀ q₀)) := by
  have hYne := bilateral_ne_negY_of_sq_nontrivial u₀ q₀ hu0 hu1 hq0 hq1
    hulow huhigh hsq1 hsqq
  have hE : bilateralY u₀ q₀ -
      (WeierstrassCurve.tateCurve q₀).toAffine.negY
        (bilateralX u₀ q₀) (bilateralY u₀ q₀) ≠ 0 :=
    sub_ne_zero.mpr hYne
  have h1 := bilateral_tangentX_cleared u₀ q₀ hu0 hu1 hq0 hq1
    hulow huhigh hsq1 hsqq
  have h2 := bilateral_tangentY_cleared u₀ q₀ hu0 hu1 hq0 hq1
    hulow huhigh hsq1 hsqq
  rw [show (WeierstrassCurve.tateCurve q₀).toAffine.a₂ = 0 from rfl,
    show (WeierstrassCurve.tateCurve q₀).toAffine.a₁ = 1 from rfl,
    tateCurve_negY q₀, show u₀ * u₀ = u₀ ^ 2 from (pow_two u₀).symm] at h1 h2
  have hE' : bilateralY u₀ q₀ - (-(bilateralY u₀ q₀) - bilateralX u₀ q₀) ≠ 0 := by
    rw [← tateCurve_negY q₀]
    exact hE
  have hXeq : bilateralX (u₀ * u₀) q₀ =
      (WeierstrassCurve.tateCurve q₀).toAffine.addX (bilateralX u₀ q₀)
        (bilateralX u₀ q₀)
        ((WeierstrassCurve.tateCurve q₀).toAffine.slope (bilateralX u₀ q₀)
          (bilateralX u₀ q₀) (bilateralY u₀ q₀) (bilateralY u₀ q₀)) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hYne,
      WeierstrassCurve.Affine.addX,
      show (WeierstrassCurve.tateCurve q₀).toAffine.a₂ = 0 from rfl,
      show (WeierstrassCurve.tateCurve q₀).toAffine.a₁ = 1 from rfl,
      tateCurve_negY q₀]
    field_simp
    linear_combination h1
  refine ⟨hYne, hXeq, ?_⟩
  rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY,
    show (WeierstrassCurve.tateCurve q₀).toAffine.a₁ = 1 from rfl,
    show (WeierstrassCurve.tateCurve q₀).toAffine.a₃ = 0 from rfl,
    ← hXeq, WeierstrassCurve.Affine.slope_of_Y_ne rfl hYne,
    show (WeierstrassCurve.tateCurve q₀).toAffine.a₂ = 0 from rfl,
    show (WeierstrassCurve.tateCurve q₀).toAffine.a₁ = 1 from rfl,
    tateCurve_negY q₀]
  field_simp
  linear_combination -h2



/-- **The fibre of the bilateral `x`-value** (DERIVED 2026-07-18 from the
coordinate-pair injectivity `bilateralXY_inj`, the PROVEN vertical case,
and the `y`-dichotomy `Y_eq_of_X_eq` — Silverman V.4): on the fundamental
annulus, two parameters with the same bilateral `x`-value either coincide
or are inverse to each other modulo `q₀^ℤ` (their product is `1` or
`q₀`). -/
theorem eq_or_mul_eq_of_bilateralX_eq (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1) (hv0 : v₀ ≠ 0) (hv1 : v₀ ≠ 1)
    (hq0 : q₀ ≠ 0) (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1)
    (hX : bilateralX u₀ q₀ = bilateralX v₀ q₀) :
    v₀ = u₀ ∨ u₀ * v₀ = 1 ∨ u₀ * v₀ = q₀ := by
  have hqv : valuation k q₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have hqpos : (0 : ValueGroupWithZero k) < valuation k q₀ :=
    zero_lt_iff.mpr hqv
  have hsq_lt : valuation k q₀ * valuation k q₀ < valuation k q₀ := by
    calc valuation k q₀ * valuation k q₀ < 1 * valuation k q₀ :=
          (OrderIso.mulRight₀ _ hqpos).strictMono hq1
      _ = valuation k q₀ := one_mul _
  have huq : u₀ ≠ q₀ := fun h => absurd hulow (by rw [h]; exact lt_irrefl _)
  have hvq : v₀ ≠ q₀ := fun h => absurd hvlow (by rw [h]; exact lt_irrefl _)
  have huwin : valuation k q₀ * valuation k q₀ < valuation k u₀ :=
    lt_trans hsq_lt hulow
  have hvwin : valuation k q₀ * valuation k q₀ < valuation k v₀ :=
    lt_trans hsq_lt hvlow
  have hequ : (WeierstrassCurve.tateCurve q₀).toAffine.Equation
      (bilateralX u₀ q₀) (bilateralY u₀ q₀) :=
    (nonsingular_bilateral u₀ q₀ hu0 hu1 huq hq0 hq1 huwin huhigh).1
  have heqv : (WeierstrassCurve.tateCurve q₀).toAffine.Equation
      (bilateralX v₀ q₀) (bilateralY v₀ q₀) :=
    (nonsingular_bilateral v₀ q₀ hv0 hv1 hvq hq0 hq1 hvwin hvhigh).1
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq heqv hequ hX.symm with hy | hy
  · -- equal `y`-values: the parameters coincide
    exact Or.inl (bilateralXY_inj v₀ u₀ q₀ hv0 hv1 hu0 hu1 hq0 hq1
      hvlow hvhigh hulow huhigh hX.symm hy)
  · -- `negY`-related `y`-values: `v₀` is the inverse partner of `u₀`
    rcases eq_or_lt_of_le huhigh with hshell | hint
    · -- shell: partner `u₀⁻¹`
      have hinv0 : u₀⁻¹ ≠ 0 := inv_ne_zero hu0
      have hinv1 : u₀⁻¹ ≠ 1 := fun h => hu1 (by
        rw [← inv_inv u₀, h, inv_one])
      obtain ⟨hXw, hYw⟩ := bilateral_negY_of_mul_trivial u₀ u₀⁻¹ q₀
        hu0 hu1 hinv0 hq0 hq1 hulow huhigh (Or.inl (mul_inv_cancel₀ hu0))
      have hinvval : valuation k u₀⁻¹ = 1 := by
        rw [map_inv₀, hshell, inv_one]
      have hveq : v₀ = u₀⁻¹ := bilateralXY_inj v₀ u₀⁻¹ q₀ hv0 hv1
        hinv0 hinv1 hq0 hq1 hvlow hvhigh
        (by rw [hinvval]; exact hq1) (le_of_eq hinvval)
        (hX.symm.trans hXw.symm) (hy.trans hYw.symm)
      exact Or.inr (Or.inl (by rw [hveq, mul_inv_cancel₀ hu0]))
    · -- interior: partner `q₀ * u₀⁻¹`
      have huvne : valuation k u₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hu0
      have hupos : (0 : ValueGroupWithZero k) < valuation k u₀ :=
        zero_lt_iff.mpr huvne
      have huinvpos : (0 : ValueGroupWithZero k) < (valuation k u₀)⁻¹ :=
        zero_lt_iff.mpr (inv_ne_zero huvne)
      have hw0 : q₀ * u₀⁻¹ ≠ 0 := mul_ne_zero hq0 (inv_ne_zero hu0)
      have hw1 : q₀ * u₀⁻¹ ≠ 1 := by
        intro h
        apply huq
        have h2 : q₀ * u₀⁻¹ * u₀ = 1 * u₀ := by rw [h]
        rw [mul_assoc, inv_mul_cancel₀ hu0, mul_one, one_mul] at h2
        exact h2.symm
      obtain ⟨hXw, hYw⟩ := bilateral_negY_of_mul_trivial u₀ (q₀ * u₀⁻¹) q₀
        hu0 hu1 hw0 hq0 hq1 hulow huhigh (Or.inr (by
          rw [mul_comm q₀ _, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul]))
      have hwval : valuation k (q₀ * u₀⁻¹) =
          valuation k q₀ * (valuation k u₀)⁻¹ := by
        rw [map_mul, map_inv₀]
      have hwlow : valuation k q₀ < valuation k (q₀ * u₀⁻¹) := by
        rw [hwval]
        have h3 : (1 : ValueGroupWithZero k) < (valuation k u₀)⁻¹ := by
          calc (1 : ValueGroupWithZero k)
              = valuation k u₀ * (valuation k u₀)⁻¹ :=
                (mul_inv_cancel₀ huvne).symm
            _ < 1 * (valuation k u₀)⁻¹ :=
                (OrderIso.mulRight₀ _ huinvpos).strictMono hint
            _ = (valuation k u₀)⁻¹ := one_mul _
        calc valuation k q₀ = valuation k q₀ * 1 := (mul_one _).symm
          _ < valuation k q₀ * (valuation k u₀)⁻¹ :=
            (OrderIso.mulLeft₀ _ hqpos).strictMono h3
      have hwhigh : valuation k (q₀ * u₀⁻¹) ≤ 1 := by
        rw [hwval]
        calc valuation k q₀ * (valuation k u₀)⁻¹
            ≤ valuation k u₀ * (valuation k u₀)⁻¹ :=
              mul_le_mul_left hulow.le _
          _ = 1 := mul_inv_cancel₀ huvne
      have hveq : v₀ = q₀ * u₀⁻¹ := bilateralXY_inj v₀ (q₀ * u₀⁻¹) q₀
        hv0 hv1 hw0 hw1 hq0 hq1 hvlow hvhigh hwlow hwhigh
        (hX.symm.trans hXw.symm) (hy.trans hYw.symm)
      refine Or.inr (Or.inr ?_)
      rw [hveq, mul_comm q₀ _, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul]

/-- **The addition law on annulus parameters** (derived from the sorried
chord/tangent/fibre leaves, the PROVEN vertical case, and the bilateral
coordinate bridge): the point map turns multiplication of annulus
parameters into addition of Tate-curve points. -/
theorem pointMap_mul [DecidableEq k] (u₀ v₀ q₀ : k)
    (hu0 : u₀ ≠ 0) (hu1 : u₀ ≠ 1) (hv0 : v₀ ≠ 0) (hv1 : v₀ ≠ 1)
    (hq0 : q₀ ≠ 0) (hq1 : valuation k q₀ < 1)
    (hulow : valuation k q₀ < valuation k u₀)
    (huhigh : valuation k u₀ ≤ 1)
    (hvlow : valuation k q₀ < valuation k v₀)
    (hvhigh : valuation k v₀ ≤ 1) :
    pointMap q₀ hq0 hq1 (u₀ * v₀) (mul_ne_zero hu0 hv0) =
      pointMap q₀ hq0 hq1 u₀ hu0 + pointMap q₀ hq0 hq1 v₀ hv0 := by
  have hqv : valuation k q₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have hqpos : (0 : ValueGroupWithZero k) < valuation k q₀ :=
    zero_lt_iff.mpr hqv
  have huv : valuation k u₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hu0
  have hupos : (0 : ValueGroupWithZero k) < valuation k u₀ :=
    zero_lt_iff.mpr huv
  -- the parameters are not `q₀` (their valuation is strictly bigger)
  have huq : u₀ ≠ q₀ := fun h => absurd hulow (by rw [h]; exact lt_irrefl _)
  have hvq : v₀ ≠ q₀ := fun h => absurd hvlow (by rw [h]; exact lt_irrefl _)
  -- window facts for the factors
  have hsq_lt : valuation k q₀ * valuation k q₀ < valuation k q₀ :=
    by
      calc valuation k q₀ * valuation k q₀ < 1 * valuation k q₀ :=
            (OrderIso.mulRight₀ _ hqpos).strictMono hq1
        _ = valuation k q₀ := one_mul _
  have hulow2 : valuation k q₀ * valuation k q₀ < valuation k u₀ :=
    lt_trans hsq_lt hulow
  have hvlow2 : valuation k q₀ * valuation k q₀ < valuation k v₀ :=
    lt_trans hsq_lt hvlow
  -- window facts for the product
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
  -- coordinates of the two summands
  rw [pointMap_eq_bilateral u₀ q₀ hu0 hu1 huq hq0 hq1 hulow2 huhigh,
    pointMap_eq_bilateral v₀ q₀ hv0 hv1 hvq hq0 hq1 hvlow2 hvhigh]
  by_cases htriv : u₀ * v₀ = 1 ∨ u₀ * v₀ = q₀
  · -- the vertical case: the sum is zero
    obtain ⟨hXeq, hYeq⟩ := bilateral_negY_of_mul_trivial u₀ v₀ q₀
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
    · -- equal `x`-values, not the vertical case: the parameters coincide
      rcases eq_or_mul_eq_of_bilateralX_eq u₀ v₀ q₀ hu0 hu1 hv0 hv1 hq0 hq1
        hulow huhigh hvlow hvhigh hX with heq | h1 | hqc
      · -- doubling
        subst heq
        obtain ⟨hYne, hXX, hYY⟩ := bilateral_add_self v₀ q₀ hv0 hv1 hq0 hq1
          hvlow hvhigh hw1 hwq
        rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hYne]
        exact point_some_congr hXX hYY
      · exact absurd h1 hw1
      · exact absurd hqc hwq
    · -- the chord case
      obtain ⟨hXX, hYY⟩ := bilateral_add_of_X_ne u₀ v₀ q₀ hu0 hv0 hq0 hu1 hv1
        hq1 hulow huhigh hvlow hvhigh hX
      rw [WeierstrassCurve.Affine.Point.add_of_X_ne hX]
      exact point_some_congr hXX hYY

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

set_option warn.sorry false in
/-- **The bilateral `x`-value is onto the affine `x`-line** (sorry node —
the analytic heart of Silverman V.4): for every affine solution `(x, y)`
of the Tate curve equation there is a parameter `u` in the fundamental
annulus with `bilateralX u = x`. Attack: the valuation/Newton-polygon
analysis of `X(u) - x` as a function of `u` on the annulus (the theta
quotient), using completeness of `k`. -/
theorem exists_annulus_bilateralX_eq (q₀ : k) (hq0 : q₀ ≠ 0)
    (hq1 : valuation k q₀ < 1) (x y : k)
    (hxy : (WeierstrassCurve.tateCurve q₀).toAffine.Equation x y) :
    ∃ u : k, u ≠ 0 ∧ u ≠ 1 ∧ valuation k q₀ < valuation k u ∧
      valuation k u ≤ 1 ∧ bilateralX u q₀ = x :=
  sorry

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
