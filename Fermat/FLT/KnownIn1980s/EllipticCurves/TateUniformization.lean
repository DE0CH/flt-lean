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

end Evaluation

end TateCurve

end
