/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.Valuation.RamificationGroup
-- `ValuationSubring.inertia_fixes_of_pow_eq_one` (step (b)), used in the
-- local unipotence assembly
import Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.NumberTheory.LocalField.Basic
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateParameter
public import Fermat.FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange
public import Fermat.FLT.KnownIn1980s.EllipticCurves.ReductionBaseChange

/-!

# The Tate curve

Let `k` be a nonarchimedean local field and let `E/k` be an elliptic curve, given by a
minimal Weierstrass equation, with split multiplicative reduction. Tate's theory attaches
to `E` a canonical *Tate parameter*, an element `q = q(E)` of `k` with `0 < |q| < 1`, and
an isomorphism of groups `E(k) ≅ kˣ/qᶻ` (Tate's uniformisation), Galois-equivariantly
after base change to a separable closure.

These results are due to Tate, in a manuscript which
circulated from the early 1960s and was eventually published in 1995 as *A review of
non-Archimedean elliptic curves*. See also Roquette, *Analytic theory of elliptic
functions over local fields* (1970), and Silverman, *Advanced topics in the arithmetic
of elliptic curves*, V.3 and V.5, for textbook accounts.

VENDORING CHANGES (2026-07-16, Fermat project): the upstream FLT file states the
uniformisation as sorry-d *data* (`tateCurveEquiv`, `tateEquiv`,
`tateEquivSepClosure`), which would poison the meaning of every downstream statement
mentioning it (any property "of `tateEquiv`" would be a property of an arbitrary
`sorry`). Following the policy used for the Weil pairing
(`Fermat.FLT.EllipticCurve.WeilPairing.exists_weilPairing`), the data and its
satellite lemmas (`tateEquiv_baseChange`, `tateEquiv_galois`, `tatePoint`,
`tatePoint_baseChange`, `tatePoint_galois`, `tatePoint_mem_torsionBy_*`,
`weilPairing_tatePoint`) are replaced by ONE existential Prop node,
`exists_tateEquivSepClosure`: there exists a Galois-equivariant group isomorphism
`Ωˣ/qᶻ ≅ E(Ω)` over a separable closure `Ω`. This is the exact content consumers
need (the torsion-membership lemmas are formal consequences of any witness, and the
finite-level statements follow by restriction). The fully proven upstream material —
the Tate curve series, the valuation lemmas, the Tate parameter, and base-change
functoriality — is vendored verbatim. The upstream import of
`FLT.KnownIn1980s.EllipticCurves.WeilPairing` (sorry-d data) is dropped; the
Weil-pairing/uniformisation sign-coherence statement `weilPairing_tatePoint` is NOT
vendored (no current consumer; if one appears it must be stated as a *joint*
existential over both packages).
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

-- Can be deleted when mathlib#41391 lands
set_option linter.overlappingInstances false

/-! ### The Tate curve `E_q`

For `q` with `0 < |q| < 1` there is an explicit Weierstrass curve `E_q`, whose coefficients
are power series in `q` with integer coefficients, together with a uniformisation
`kˣ/qᶻ ≅ E_q(k)` given by explicit power series `X(u, q)`, `Y(u, q)` — all of it involving
no choices whatsoever, and commuting on the nose with every valuative morphism of fields.
The uniformisation of a general `E` with split multiplicative reduction is obtained by
transporting this one along an isomorphism `E_{q(E)} ≅ E` of Weierstrass curves
(`exists_variableChange_tateCurve` below), and *that* is the only choice in the theory:
there are exactly two such isomorphisms, differing by negation.
-/

section TateCurve

-- For the defining series we only need a topology on the field: this section makes sense
-- (and the series converge) over any field complete with respect to a rank 1
-- nonarchimedean valuation.
variable {k : Type*} [Field k] [TopologicalSpace k]

/-- The coefficient `a₄(q) = -5s₃(q)` of the Tate curve, where
`sₖ(q) = ∑_{n≥1} nᵏqⁿ/(1-qⁿ)` (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateA₄ (q : k) : k :=
  -5 * ∑' n : ℕ, ((n + 1 : ℕ) : k) ^ 3 * q ^ (n + 1) / (1 - q ^ (n + 1))

/-- The coefficient `a₆(q) = -(5s₃(q) + 7s₅(q))/12` of the Tate curve, where
`sₖ(q) = ∑_{n≥1} nᵏqⁿ/(1-qⁿ)`; the integrality `12 ∣ 5n³ + 7n⁵` makes sense of the
division by `12` in every characteristic (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateA₆ (q : k) : k :=
  ∑' n : ℕ, -(((5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5) / 12 : ℤ) : k) * q ^ (n + 1) /
    (1 - q ^ (n + 1))

/-- The Tate curve `E_q : y² + xy = x³ + a₄(q)x + a₆(q)` (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateCurve (q : k) : WeierstrassCurve k :=
  ⟨1, 0, 0, tateA₄ q, tateA₆ q⟩

end TateCurve

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

-- `tateParameter` — the inverse of `q ↦ j(q)` of Silverman, ATAEC V.5.2, by which the
-- Tate parameter is *defined* below, choice-freely — is constructed in
-- `Fermat.FLT.KnownIn1980s.EllipticCurves.TateParameter` (imported above) as the
-- evaluation at `j⁻¹` of an explicit integral power series. Here we state its
-- interaction with the valuation.

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
lemma WeierstrassCurve.tateParameter_eq {j : k} : WeierstrassCurve.tateParameter j =
    TateCurve.evalInt j⁻¹ TateCurve.jInvReverse := by
  rfl

/-- The Tate parameter of `j` has valuation exactly `|j|⁻¹`: the leading term `j⁻¹` of
the inverse series `q = j⁻¹ + 744j⁻² + ⋯` dominates ultrametrically. -/
theorem WeierstrassCurve.valuation_tateParameter_eq {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) = (valuation k j)⁻¹ := by
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp [map_zero] at hj
  have h := TateCurve.valuation_evalInt_eq j⁻¹ (inv_ne_zero hj0)
    (by simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj) TateCurve.constantCoeff_jInvReverse
    TateCurve.coeff_one_jInvReverse
  rw [WeierstrassCurve.tateParameter_eq, h, map_inv₀]

theorem WeierstrassCurve.tateParameter_ne_zero {j : k} (hj : 1 < valuation k j) :
    tateParameter j ≠ 0 := by
  intro h
  have heq := valuation_tateParameter_eq hj
  rw [h, map_zero] at heq
  exact inv_ne_zero (ne_of_gt (lt_trans zero_lt_one hj)) heq.symm

theorem WeierstrassCurve.valuation_tateParameter_lt_one {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) < 1 := by
  simpa [valuation_tateParameter_eq hj] using inv_lt_one_of_one_lt₀ hj

-- The next few lemmas transfer `mathlib`'s reduction-theoretic facts (stated for the adic
-- valuation of the discrete valuation ring `𝒪[k]`) to the canonical valuation of `k`,
-- through unit and maximal-ideal membership in `𝒪[k]`.

/-- An elliptic curve over `k` with bad (here multiplicative) reduction has discriminant of
valuation less than `1`: the discriminant of the integral model lies in the maximal ideal. -/
theorem WeierstrassCurve.valuation_Δ_lt_one (E : WeierstrassCurve k)
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.Δ < 1 := by
  have hbad := HasMultiplicativeReduction.badReduction (R := 𝒪[k]) (W := E)
  rw [← integralModel_Δ_eq 𝒪[k] E] at hbad ⊢
  exact adicValuation_lt_one_iff.mp hbad

/-- An elliptic curve over `k` with multiplicative reduction has `c₄` of valuation exactly
`1`: `c₄` of the integral model is a unit of `𝒪[k]`. -/
theorem WeierstrassCurve.valuation_c₄_eq_one (E : WeierstrassCurve k)
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.c₄ = 1 := by
  have hmul := HasMultiplicativeReduction.multiplicativeReduction (R := 𝒪[k]) (W := E)
  rw [← integralModel_c₄_eq 𝒪[k] E] at hmul ⊢
  exact adicValuation_eq_one_iff.mp hmul

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The discriminant of an elliptic curve has nonzero valuation. -/
theorem WeierstrassCurve.valuation_Δ_ne_zero (E : WeierstrassCurve k) [E.IsElliptic] :
    valuation k E.Δ ≠ 0 := by
  rw [(valuation k).ne_zero_iff, ← E.coe_Δ']
  exact Units.ne_zero _

/-- An elliptic curve over `k` with multiplicative reduction has `|j| = |c₄|³/|Δ| = |Δ|⁻¹`. -/
theorem WeierstrassCurve.valuation_j_eq (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.j = (valuation k E.Δ)⁻¹ := by
  rw [show E.j = (↑(E.Δ'⁻¹) : k) * E.c₄ ^ 3 from rfl, map_mul, map_pow,
    E.valuation_c₄_eq_one, one_pow, mul_one, Units.val_inv_eq_inv_val, map_inv₀, E.coe_Δ']

/-- An elliptic curve over `k` with split multiplicative reduction has non-integral
`j`-invariant, `|j(E)| > 1`: indeed `v(j) = -v(Δ_min) < 0`, since `c₄` is a unit when the
reduction is multiplicative. -/
theorem WeierstrassCurve.one_lt_valuation_j (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasSplitMultiplicativeReduction 𝒪[k]] :
    1 < valuation k E.j := by
  rw [E.valuation_j_eq]
  exact (one_lt_inv₀ (zero_lt_iff.mpr E.valuation_Δ_ne_zero)).mpr E.valuation_Δ_lt_one

/-- The Tate parameter of an elliptic curve `E`, given by a minimal Weierstrass equation with
split multiplicative reduction over a nonarchimedean local field `k`: the unique element
`q` of `k` with `0 < |q| < 1` such that `j(E) = j(q) = q⁻¹ + 744 + 196884q + ⋯`, defined
directly (with no appeal to choice) as `tateParameter E.j`, the inverse `j`-series
evaluated at `j(E)`. Equivalently, the unique `q` such that `E(k̄)` is Galois-equivariantly
isomorphic to `k̄ˣ/q^ℤ`. (The bare existence of an abstract isomorphism `E(k) ≅ kˣ/q^ℤ`
would not pin down `q`: already over `ℚ_p` the groups `ℚ_pˣ/p^ℤ` and `ℚ_pˣ/(p(1+p))^ℤ`
are isomorphic, even topologically.) -/
noncomputable def WeierstrassCurve.q (E : WeierstrassCurve k) [E.IsElliptic] : k :=
  tateParameter E.j

-- Let E/k be an elliptic curve, given by a minimal Weierstrass equation,
-- with split multiplicative reduction
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[k]]
  [E.IsMinimal 𝒪[k]]

omit [E.IsMinimal 𝒪[k]] in
theorem WeierstrassCurve.q_ne_zero : E.q ≠ 0 :=
  tateParameter_ne_zero E.one_lt_valuation_j

omit [E.IsMinimal 𝒪[k]] in
/-- The Tate parameter has norm less than `1`. -/
theorem WeierstrassCurve.valuation_q_lt_one : valuation k E.q < 1 :=
  valuation_tateParameter_lt_one E.one_lt_valuation_j

/-- The Tate parameter as an element of `kˣ`. -/
noncomputable def WeierstrassCurve.qUnit : kˣ :=
  Units.mk0 E.q E.q_ne_zero

set_option warn.sorry false in
/-- Tate's theorem (Silverman, ATAEC V.5.3) (sorry node): an elliptic curve with split
multiplicative reduction is isomorphic, by a change of Weierstrass coordinates, to the
Tate curve of its Tate parameter. Since `j(E)` is non-integral, `Aut` of the curve is
`{±1}` and there are exactly *two* such `C`, differing by negation. -/
theorem WeierstrassCurve.exists_variableChange_tateCurve :
    ∃ C : VariableChange k, C • tateCurve E.q = E :=
  sorry

open scoped ArithmeticFunction.sigma in
/-- The Lambert series rearrangement `∑_{n≥1} n³qⁿ/(1-qⁿ) = ∑_{n≥1} σ₃(n)qⁿ` for
`|q| < 1`: the defining series of `tateA₄` is the evaluation of the formal series
`a₄(q) = -5s₃(q) ∈ ℤ⟦q⟧`. -/
theorem WeierstrassCurve.tateA₄_eq_evalInt (q : k) (hq : valuation k q < 1) :
    tateA₄ q = TateCurve.evalInt q TateCurve.a₄Formal := by
  have hF : ∀ n, PowerSeries.coeff n TateCurve.a₄Formal
      = ∑ d ∈ n.divisors, -5 * (d : ℤ) ^ 3 := by
    intro n
    rw [TateCurve.coeff_a₄Formal, ArithmeticFunction.sigma_apply]
    push_cast
    rw [Finset.mul_sum]
  rw [← TateCurve.tsum_lambert_eq_evalInt q hq _ hF]
  simp only [tateA₄]
  rw [← tsum_mul_left]
  exact tsum_congr fun m ↦ by push_cast; ring

open scoped ArithmeticFunction.sigma in
/-- The Lambert series rearrangement for `tateA₆`, as for `tateA₄_eq_evalInt`; the
bookkeeping of the exact division by `12` uses `12 ∣ 5d³ + 7d⁵` termwise. -/
theorem WeierstrassCurve.tateA₆_eq_evalInt (q : k) (hq : valuation k q < 1) :
    tateA₆ q = TateCurve.evalInt q TateCurve.a₆Formal := by
  have h12 : ∀ d : ℤ, (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    intro d
    have hz : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 12) = 0 := by
      push_cast
      generalize (d : ZMod 12) = r
      revert r
      decide
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp hz
  set c : ℕ → ℤ := fun d ↦ -((5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12) with hc
  -- the coefficients of `a₆Formal` are the divisor sums of `c`: the divisor sum commutes
  -- with the exact division by `12`
  have hF : ∀ N, PowerSeries.coeff N TateCurve.a₆Formal = ∑ d ∈ N.divisors, c d := by
    intro N
    rw [TateCurve.coeff_a₆Formal]
    symm
    simp only [hc]
    have hσ : ∑ d ∈ N.divisors, (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5)
        = 5 * (σ 3 N : ℤ) + 7 * (σ 5 N : ℤ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
      push_cast
      ring
    have hsum : (12 : ℤ) ∣ 5 * (σ 3 N : ℤ) + 7 * (σ 5 N : ℤ) := by
      rw [← hσ]
      exact Finset.dvd_sum fun d _ ↦ h12 d
    have hterm : ∀ d ∈ N.divisors, -((5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12) * 12
        = -(5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) := fun d _ ↦ by
      rw [neg_mul, Int.ediv_mul_cancel (h12 d)]
    apply mul_right_cancel₀ (b := (12 : ℤ)) (by norm_num)
    rw [Finset.sum_mul, Finset.sum_congr rfl hterm, neg_mul, Int.ediv_mul_cancel hsum,
      ← hσ, Finset.sum_neg_distrib]
  rw [← TateCurve.tsum_lambert_eq_evalInt q hq c hF]
  simp only [tateA₆]
  refine tsum_congr fun m ↦ ?_
  simp only [hc]
  push_cast
  ring

/-! ### Functoriality

Now let `l` be a second nonarchimedean local field and let `k → l` be a morphism of fields
inducing the valuative relation on `k` from the one on `l` (the `ValuativeExtension`
hypothesis). The compatibility hypothesis is what makes the morphism continuous, hence
commute with the power series defining Tate's theory; it is automatic for `k`-embeddings
between algebraic extensions of `k` (by uniqueness of extensions of valuations over the
complete field `k`), but not for arbitrary abstract field morphisms.
-/

variable {l : Type*} [Field l] [ValuativeRel l] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] [Algebra k l] [ValuativeExtension k l]

-- The base change of E is elliptic. (Mathlib has this instance for `E.map f`, but
-- `WeierstrassCurve.baseChange` is a non-reducible `def`, so instance search cannot
-- see through it.)
instance : (E.baseChange l).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k l)).IsElliptic

/-- The construction of the Tate curve commutes on the nose with any valuative morphism:
its coefficients are power series in `q` with *integer* coefficients, and the partial
sums converge at matching rates on both sides (`TateCurve.evalInt_map`).

On the hypothesis `|q| < 1`: the coefficient series `tateA₄`, `tateA₆` are `tsum`s, which
take *junk values* outside the open unit disc, and every consumer feeds this lemma a Tate
parameter, which lies strictly inside the disc (`valuation_q_lt_one`). So the hypothesis
is free in practice, and keeps the statement the honest identity of convergent series
that it is in Silverman. -/
theorem WeierstrassCurve.tateCurve_baseChange (q : k) (hq : valuation k q < 1) :
    (tateCurve q)⁄l = tateCurve (algebraMap k l q) := by
  have hq' : valuation l (algebraMap k l q) < 1 := TateCurve.valuation_algebraMap_lt_one hq
  have h4 : algebraMap k l (tateA₄ q) = tateA₄ (algebraMap k l q) := by
    rw [tateA₄_eq_evalInt q hq, tateA₄_eq_evalInt _ hq', TateCurve.evalInt_map q hq]
  have h6 : algebraMap k l (tateA₆ q) = tateA₆ (algebraMap k l q) := by
    rw [tateA₆_eq_evalInt q hq, tateA₆_eq_evalInt _ hq', TateCurve.evalInt_map q hq]
  ext <;> simp [WeierstrassCurve.baseChange, tateCurve, h4, h6]

-- The base change of `E` to `l` is still given by a minimal Weierstrass equation. This uses the
-- multiplicative reduction hypothesis (which makes `c₄` a unit): minimality by itself is not
-- preserved by ramified base change — `y² = x³ + p` is minimal over `ℚ_p` but not over
-- `ℚ_p(p^{1/6})`. See `WeierstrassCurve.isMinimal_baseChange` in `ReductionBaseChange`.
instance : (E.baseChange l).IsMinimal 𝒪[l] :=
  E.isMinimal_baseChange

-- and it still has split multiplicative reduction, via
-- `WeierstrassCurve.hasSplitMultiplicativeReduction_baseChange` in `ReductionBaseChange`
-- (from which the preceding `IsMinimal` also follows by class-parent projection).
instance : (E.baseChange l).HasSplitMultiplicativeReduction 𝒪[l] :=
  E.hasSplitMultiplicativeReduction_baseChange

/-- The Tate parameter series commutes with valuative extensions: it is the evaluation of
an integral power series at `j⁻¹`, so this is a direct instance of `evalInt_map`. -/
theorem WeierstrassCurve.tateParameter_map {j : k} (hj : 1 < valuation k j) :
    tateParameter (algebraMap k l j) = algebraMap k l (tateParameter j) := by
  have hjinv : valuation k j⁻¹ < 1 := by
    simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj
  simp_rw [WeierstrassCurve.tateParameter_eq, TateCurve.evalInt_map j⁻¹ hjinv, map_inv₀]

omit [E.IsMinimal 𝒪[k]] in
theorem WeierstrassCurve.q_baseChange : (E.baseChange l).q = algebraMap k l E.q := by
  rw [show (E.baseChange l).q = tateParameter (E.baseChange l).j from rfl,
    show E.q = tateParameter E.j from rfl,
    show (E.baseChange l).j = algebraMap k l E.j from E.map_j (algebraMap k l),
    tateParameter_map E.one_lt_valuation_j]

/-! ### Tate's uniformisation over a separable closure

Passing to the limit over the finite subextensions of a separable closure `Ω` of `k`, the
finite-level uniformisations `E(l) ≅ lˣ/qᶻ` glue to a Galois-equivariant uniformisation
`E(Ω) ≅ Ωˣ/qᶻ`. The `N`-torsion of `Ωˣ/qᶻ` is generated by the `N`-th roots of unity and
(the classes of) the `N`-th roots of `q`, so the uniformisation identifies the `N`-torsion
of `E` explicitly: this is how one computes the Galois representations attached to `E`.

The statement below is an existential Prop (see the vendoring note in the module
docstring): the isomorphism is pinned down mathematically only up to a sign (the choice
of one of the two isomorphisms `E_{q(E)} ≅ E`), and no consumer needs a canonical
choice — only existence of an equivariant one.
-/

-- Now let `Ω` be a separable closure of `k`. It is not itself a nonarchimedean local field
-- (it is not complete), so it does not fit the framework above; but `E(Ω)` is the union of
-- the `E(l)` over the finite subextensions `l/k` of `Ω`, and Tate's theory applies to each.
variable (Ω : Type*) [Field Ω] [Algebra k Ω] [IsSepClosed Ω] [Algebra.IsSeparable k Ω]

-- the base change of E to Ω is elliptic (same remark as for `l` above)
instance : (E.baseChange Ω).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k Ω)).IsElliptic

/-- The image of the Tate parameter in a separable closure `Ω` of `k`, as a unit. (`Ω` is
not a nonarchimedean local field, so this is not literally `(E.baseChange Ω).qUnit`.) -/
noncomputable def WeierstrassCurve.qUnitSepClosure : Ωˣ :=
  Units.map (algebraMap k Ω).toMonoidHom E.qUnit

-- `DecidableEq Ω` is needed for the group law on `(E⁄Ω).Point`
variable [DecidableEq Ω]

set_option warn.sorry false in
/-- **Tate's uniformisation theorem over a separable closure** (sorry node): for `E/k`
an elliptic curve, in minimal Weierstrass form, with split multiplicative reduction
over a nonarchimedean local field `k`, and `Ω` a separable closure of `k`, there is a
group isomorphism `Ωˣ/q(E)ᶻ ≅ E(Ω)` that is equivariant for the natural actions of
`Gal(Ω/k)` on both sides (Silverman, ATAEC V.3.1 + V.5.3: glue the finite-level
uniformisations `E(l) ≅ lˣ/qᶻ` over the finite subextensions `l/k` of `Ω`; the
`k`-linearity of every `σ ∈ Gal(Ω/k)` makes the sign choice `σ`-stable, cf.
`tateEquiv_galois` in the upstream FLT file). Stated as an existential Prop because
the isomorphism is canonical only up to negation. -/
theorem WeierstrassCurve.exists_tateEquivSepClosure :
    ∃ e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point,
      ∀ (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ),
        WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom (e (Additive.ofMul ↑u)) =
          e (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)) :=
  sorry

omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω] in
/-- `N`-th roots of unity give `N`-torsion points of `E` under ANY Tate
uniformization (PROVEN — a formal consequence of the group-isomorphism
property, stated for the witnesses of `exists_tateEquivSepClosure`):
`N • [ζ] = [ζ^N] = [1] = 0`, and `e` transports annihilation. -/
theorem WeierstrassCurve.mem_torsionBy_of_mem_rootsOfUnity
    (e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point)
    {N : ℕ} {ζ : Ωˣ} (hζ : ζ ∈ rootsOfUnity N Ω) :
    e (Additive.ofMul ↑ζ) ∈ AddSubgroup.torsionBy ((E⁄Ω)).Point (N : ℤ) := by
  have hζN : ζ ^ N = 1 := hζ
  have hann : ((N : ℤ)) • (Additive.ofMul
      (↑ζ : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) = 0 := by
    rw [← ofMul_zpow, ← QuotientGroup.mk_zpow, zpow_natCast, hζN,
      QuotientGroup.mk_one, ofMul_one]
  refine (Submodule.mem_torsionBy_iff _ _).mpr ?_
  rw [← map_zsmul e, hann, map_zero]

omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω] in
/-- `N`-th roots of the Tate parameter give `N`-torsion points of `E`
under ANY Tate uniformization (PROVEN, as above): `N • [r] = [r^N] = [q]
= 0` since `q` generates the subgroup that is quotiented out. -/
theorem WeierstrassCurve.mem_torsionBy_of_pow_eq
    (e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point)
    {N : ℕ} {r : Ωˣ} (hr : r ^ N = E.qUnitSepClosure Ω) :
    e (Additive.ofMul ↑r) ∈ AddSubgroup.torsionBy ((E⁄Ω)).Point (N : ℤ) := by
  have hann : ((N : ℤ)) • (Additive.ofMul
      (↑r : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) = 0 := by
    rw [← ofMul_zpow, ← QuotientGroup.mk_zpow, zpow_natCast, hr]
    rw [show ((E.qUnitSepClosure Ω : Ωˣ) :
        Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) = 1 from
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _), ofMul_one]
  refine (Submodule.mem_torsionBy_iff _ _).mpr ?_
  rw [← map_zsmul e, hann, map_zero]

/-- **Representatives of torsion in the Tate quotient** (PROVEN — pure
group theory): every `N`-torsion class of `Gˣ/q^ℤ` is represented by an
element whose `N`-th power is an integer power of `q`. This is step (a)
of the derivation of the multiplicative-reduction inertia statements
from `exists_tateEquivSepClosure`. -/
theorem exists_rep_pow_eq_zpow_of_torsion {G : Type*} [CommGroup G]
    (q : G) {N : ℕ} (t : Additive (G ⧸ Subgroup.zpowers q))
    (ht : ((N : ℤ)) • t = 0) :
    ∃ (u : G) (a : ℤ),
      Additive.ofMul ((u : G ⧸ Subgroup.zpowers q)) = t ∧ u ^ N = q ^ a := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul t)
  have h1 : ((u : G ⧸ Subgroup.zpowers q)) ^ N = 1 := by
    have h2 := congrArg Additive.toMul ht
    rw [toMul_zsmul, toMul_zero, zpow_natCast] at h2
    rw [hu]
    exact h2
  have h3 : (u ^ N : G) ∈ Subgroup.zpowers q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h1
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp h3
  exact ⟨u, a, by rw [hu, ofMul_toMul], ha.symm⟩

/-- **The inertia-difference of a Tate-parameter root is a root of
unity** (PROVEN): if `σ` fixes `u^N`, then `σ(u)·u⁻¹` is an `N`-th root
of unity. Step (c) of the multiplicative-reduction derivation: for a
torsion representative `u` with `u^N = q_E^a`, every `σ ∈ Gal(Ω/k)`
fixes `u^N` (the Tate parameter comes from the base field), so `σ`
moves `u` by at most an `N`-th root of unity. -/
theorem map_mul_inv_mem_rootsOfUnity_of_pow_fixed
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ) {N : ℕ}
    (hfix : Units.map σ.toAlgHom.toRingHom.toMonoidHom (u ^ N) = u ^ N) :
    Units.map σ.toAlgHom.toRingHom.toMonoidHom u * u⁻¹ ∈
      rootsOfUnity N Ω := by
  rw [mem_rootsOfUnity]
  calc (Units.map σ.toAlgHom.toRingHom.toMonoidHom u * u⁻¹) ^ N
      = Units.map σ.toAlgHom.toRingHom.toMonoidHom (u ^ N) * (u ^ N)⁻¹ := by
        rw [mul_pow, map_pow, inv_pow]
    _ = 1 := by rw [hfix, mul_inv_cancel]

omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω]
  [DecidableEq Ω] in
/-- Every `k`-automorphism of `Ω` fixes the Tate parameter (PROVEN): it
comes from the base field. -/
theorem WeierstrassCurve.map_qUnitSepClosure_eq (σ : Ω ≃ₐ[k] Ω) :
    Units.map σ.toAlgHom.toRingHom.toMonoidHom (E.qUnitSepClosure Ω) =
      E.qUnitSepClosure Ω := by
  apply Units.ext
  show σ ((algebraMap k Ω) E.q) = (algebraMap k Ω) E.q
  exact σ.commutes E.q

omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω]
  [DecidableEq Ω] in
/-- Every `k`-automorphism of `Ω` fixes all integer powers of the Tate
parameter (PROVEN). -/
theorem WeierstrassCurve.map_zpow_qUnitSepClosure_eq (σ : Ω ≃ₐ[k] Ω)
    (a : ℤ) :
    Units.map σ.toAlgHom.toRingHom.toMonoidHom (E.qUnitSepClosure Ω ^ a) =
      E.qUnitSepClosure Ω ^ a := by
  rw [map_zpow, E.map_qUnitSepClosure_eq]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω] in
/-- **Local unipotence of inertia on Tate torsion** (PROVEN 2026-07-17,
assembling steps (a), (b), (c) over ANY witness of the uniformization):
given a Galois-equivariant Tate uniformization `e` of `E` over `Ω` and
a valuation subring `A` of `Ω` whose residue characteristic does not
divide `p`, every element of the inertia subgroup of `A` acts
unipotently on the `p`-torsion: `σ(σP) − σP − σP + P = 0`. The torsion
class is represented by `u` with `u^p = q_E^a` (step (a)); every
`k`-automorphism fixes `q_E^a`, so `σ(u)/u =: ζ` is a `p`-th root of
unity (step (c)) and `σP − P = e[ζ]`; inertia fixes `ζ` (step (b)), so
a second application of `σ − 1` kills `e[ζ]`. -/
theorem WeierstrassCurve.tate_inertia_unipotent
    (e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point)
    (he : ∀ (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ),
      WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom (e (Additive.ofMul ↑u)) =
        e (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)))
    (A : ValuationSubring Ω) {p : ℕ} (hp : p ≠ 0)
    (hchar : ((p : ℕ) : IsLocalRing.ResidueField A) ≠ 0)
    (σ : A.decompositionSubgroup k) (hσ : σ ∈ A.inertiaSubgroup k)
    (P : ((E⁄Ω)).Point)
    (hP : P ∈ AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ)) :
    WeierstrassCurve.Affine.Point.map (W' := E)
        ((σ : Ω ≃ₐ[k] Ω)).toAlgHom
        (WeierstrassCurve.Affine.Point.map (W' := E)
          ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P) -
      WeierstrassCurve.Affine.Point.map (W' := E)
        ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P -
      WeierstrassCurve.Affine.Point.map (W' := E)
        ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P + P = 0 := by
  classical
  -- pull the torsion class back through `e`
  set t : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) :=
    e.symm P with ht
  have hPt : e t = P := e.apply_symm_apply P
  have httor : ((p : ℕ) : ℤ) • t = 0 := by
    have h1 : ((p : ℕ) : ℤ) • P = 0 := hP
    rw [ht, ← map_zsmul e.symm, h1, map_zero]
  obtain ⟨u, a, hut, hupow⟩ :=
    exists_rep_pow_eq_zpow_of_torsion (E.qUnitSepClosure Ω) t httor
  -- `σ` moves `u` by the root of unity `ζ`
  have hfixpow : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom
      (u ^ p) = u ^ p := by
    rw [hupow]
    exact E.map_zpow_qUnitSepClosure_eq Ω (σ : Ω ≃ₐ[k] Ω) a
  have hζmem : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom u
      * u⁻¹ ∈ rootsOfUnity p Ω :=
    map_mul_inv_mem_rootsOfUnity_of_pow_fixed (σ : Ω ≃ₐ[k] Ω) u hfixpow
  set ζ : Ωˣ := Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom u
    * u⁻¹ with hζ
  -- inertia fixes `ζ`
  have hζpow : (ζ : Ω) ^ p = 1 := by
    have h1 : ζ ^ p = 1 := hζmem
    have h2 := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
  have hσζ : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom ζ =
      ζ := by
    apply Units.ext
    show (σ : Ω ≃ₐ[k] Ω) (ζ : Ω) = (ζ : Ω)
    exact A.inertia_fixes_of_pow_eq_one hp hchar σ hσ hζpow
  -- `σP = P + e[ζ]`
  have hσu : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom u =
      ζ * u := by
    rw [hζ, inv_mul_cancel_right]
  have hstep : ∀ Q : ((E⁄Ω)).Point,
      Q = e (Additive.ofMul (↑u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) →
      WeierstrassCurve.Affine.Point.map (W' := E)
        ((σ : Ω ≃ₐ[k] Ω)).toAlgHom Q =
      e (Additive.ofMul (↑(ζ * u) : Ωˣ ⧸ Subgroup.zpowers
        (E.qUnitSepClosure Ω))) := by
    intro Q hQ
    rw [hQ, he (σ : Ω ≃ₐ[k] Ω) u, hσu]
  have hPu : P = e (Additive.ofMul (↑u : Ωˣ ⧸ Subgroup.zpowers
      (E.qUnitSepClosure Ω))) := by
    rw [hut, hPt]
  have hσP : WeierstrassCurve.Affine.Point.map (W' := E)
      ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P =
      e (Additive.ofMul (↑(ζ * u) : Ωˣ ⧸ Subgroup.zpowers
        (E.qUnitSepClosure Ω))) := hstep P hPu
  -- `σ(σP) = σP + e[σζ] − ... = e[ζ·ζ·u]`? — apply equivariance again
  have hσσP : WeierstrassCurve.Affine.Point.map (W' := E)
      ((σ : Ω ≃ₐ[k] Ω)).toAlgHom
      (WeierstrassCurve.Affine.Point.map (W' := E)
        ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P) =
      e (Additive.ofMul (↑(ζ * (ζ * u)) : Ωˣ ⧸ Subgroup.zpowers
        (E.qUnitSepClosure Ω))) := by
    rw [hσP, he (σ : Ω ≃ₐ[k] Ω) (ζ * u)]
    congr 2
    rw [map_mul, hσζ, hσu]
  -- assemble in the additive quotient
  have h₂ : (Additive.ofMul (↑(ζ * u) : Ωˣ ⧸ Subgroup.zpowers
      (E.qUnitSepClosure Ω))) =
      Additive.ofMul ((ζ : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) +
      Additive.ofMul ((u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) := by
    rw [QuotientGroup.mk_mul, ofMul_mul]
  have h₁ : (Additive.ofMul (↑(ζ * (ζ * u)) : Ωˣ ⧸ Subgroup.zpowers
      (E.qUnitSepClosure Ω))) =
      Additive.ofMul ((ζ : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) +
      (Additive.ofMul ((ζ : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) +
       Additive.ofMul ((u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)))) := by
    rw [QuotientGroup.mk_mul, ofMul_mul, h₂]
  rw [hσσP, hσP, hPu, h₁, h₂, map_add, map_add]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
omit [E.IsMinimal 𝒪[k]] [IsSepClosed Ω] [Algebra.IsSeparable k Ω] in
/-- **Local triviality of inertia on Tate torsion when the parameter is
a `p`-th power up to units** (steps (a)+(b′)+(d) over any witness of
the uniformization): if `q_E · w⁻ᵖ` is a unit of the valuation subring
`A` (with nonzero residue) for some `w ∈ kˣ`, then every inertia
element FIXES the `p`-torsion pointwise. The torsion class is
represented by `u` with `uᵖ = q_Eᵃ`; then `x := u·w⁻ᵃ` satisfies
`xᵖ = (q_E·w⁻ᵖ)ᵃ`, a `σ`-fixed unit constant of `A`, so inertia fixes
`x` (`inertia_fixes_of_pow_eq`), hence `u`, hence the point. -/
theorem WeierstrassCurve.tate_inertia_trivial
    (e : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ ((E⁄Ω)).Point)
    (he : ∀ (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ),
      WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom (e (Additive.ofMul ↑u)) =
        e (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)))
    (A : ValuationSubring Ω) {p : ℕ} (hp : p ≠ 0)
    (hchar : ((p : ℕ) : IsLocalRing.ResidueField A) ≠ 0)
    (σ : A.decompositionSubgroup k) (hσ : σ ∈ A.inertiaSubgroup k)
    (w : kˣ)
    (hcA : algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k)) ∈ A)
    (hcres : IsLocalRing.residue A
      (⟨algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k)), hcA⟩ : A) ≠ 0)
    (P : ((E⁄Ω)).Point)
    (hP : P ∈ AddSubgroup.torsionBy ((E⁄Ω)).Point ((p : ℕ) : ℤ)) :
    WeierstrassCurve.Affine.Point.map (W' := E)
      ((σ : Ω ≃ₐ[k] Ω)).toAlgHom P = P := by
  classical
  set t : Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) :=
    e.symm P with ht
  have hPt : e t = P := e.apply_symm_apply P
  have httor : ((p : ℕ) : ℤ) • t = 0 := by
    have h1 : ((p : ℕ) : ℤ) • P = 0 := hP
    rw [ht, ← map_zsmul e.symm, h1, map_zero]
  obtain ⟨u, a, hut, hupow⟩ :=
    exists_rep_pow_eq_zpow_of_torsion (E.qUnitSepClosure Ω) t httor
  -- the recentred representative `x := u · wΩ⁻ᵃ` and its constant power
  set wΩ : Ωˣ := Units.map (algebraMap k Ω).toMonoidHom w with hwΩ
  have h1 : (u * wΩ⁻¹ ^ a) ^ (p : ℤ) =
      (Units.map (algebraMap k Ω).toMonoidHom (E.qUnit * w⁻¹ ^ p)) ^ a := by
    calc (u * wΩ⁻¹ ^ a) ^ (p : ℤ)
        = u ^ (p : ℤ) * (wΩ⁻¹ ^ a) ^ (p : ℤ) := mul_zpow _ _ _
      _ = u ^ p * (wΩ⁻¹ ^ a) ^ (p : ℤ) := by rw [zpow_natCast]
      _ = E.qUnitSepClosure Ω ^ a * (wΩ⁻¹ ^ a) ^ (p : ℤ) := by rw [hupow]
      _ = E.qUnitSepClosure Ω ^ a * (wΩ⁻¹ ^ (p : ℤ)) ^ a := by
          rw [← zpow_mul, ← zpow_mul, mul_comm a ((p : ℤ))]
      _ = E.qUnitSepClosure Ω ^ a * (wΩ⁻¹ ^ p) ^ a := by rw [zpow_natCast]
      _ = (E.qUnitSepClosure Ω * wΩ⁻¹ ^ p) ^ a := (mul_zpow _ _ _).symm
      _ = (Units.map (algebraMap k Ω).toMonoidHom (E.qUnit * w⁻¹ ^ p)) ^ a := by
          congr 1
          rw [map_mul, map_pow, map_inv, ← hwΩ]
          rfl
  have hxpow : ((u * wΩ⁻¹ ^ a : Ωˣ) : Ω) ^ p =
      (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a := by
    calc ((u * wΩ⁻¹ ^ a : Ωˣ) : Ω) ^ p
        = (((u * wΩ⁻¹ ^ a) ^ p : Ωˣ) : Ω) :=
          (Units.val_pow_eq_pow_val _ _).symm
      _ = (((u * wΩ⁻¹ ^ a) ^ (p : ℤ) : Ωˣ) : Ω) := by rw [zpow_natCast]
      _ = (((Units.map (algebraMap k Ω).toMonoidHom
            (E.qUnit * w⁻¹ ^ p)) ^ a : Ωˣ) : Ω) := by rw [h1]
      _ = ((Units.map (algebraMap k Ω).toMonoidHom
            (E.qUnit * w⁻¹ ^ p) : Ωˣ) : Ω) ^ a :=
          Units.val_zpow_eq_zpow_val _ _
      _ = (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a := rfl
  -- the constant power is `σ`-fixed (it comes from the base field)
  have hσc : (σ : Ω ≃ₐ[k] Ω)
      ((algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a) =
      (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a := by
    rw [map_zpow₀]
    congr 1
    exact (σ : Ω ≃ₐ[k] Ω).commutes _
  -- the constant is a unit of `A`, so its integer powers stay in `A`
  have hcunit : IsUnit (⟨algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k)),
      hcA⟩ : A) := by
    by_contra hnu
    exact hcres (Ideal.Quotient.eq_zero_iff_mem.mpr
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  have hcoe : (((hcunit.unit ^ a : Aˣ) : A) : Ω) =
      (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a := by
    calc (((hcunit.unit ^ a : Aˣ) : A) : Ω)
        = ((Units.map A.subtype.toMonoidHom (hcunit.unit ^ a) : Ωˣ) : Ω) := rfl
      _ = (((Units.map A.subtype.toMonoidHom hcunit.unit) ^ a : Ωˣ) : Ω) := by
          rw [map_zpow]
      _ = ((Units.map A.subtype.toMonoidHom hcunit.unit : Ωˣ) : Ω) ^ a :=
          Units.val_zpow_eq_zpow_val _ _
      _ = (((hcunit.unit : A) : Ω)) ^ a := rfl
      _ = (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a := by
          rw [hcunit.unit_spec]
  have hcApow : (algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a ∈ A :=
    hcoe ▸ SetLike.coe_mem _
  have hcrespow : IsLocalRing.residue A
      (⟨(algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a, hcApow⟩ : A) ≠
      0 := by
    rw [show (⟨(algebraMap k Ω (((E.qUnit * w⁻¹ ^ p : kˣ) : k))) ^ a,
        hcApow⟩ : A) = ((hcunit.unit ^ a : Aˣ) : A) from Subtype.ext hcoe.symm]
    exact ((hcunit.unit ^ a).isUnit.map (IsLocalRing.residue A)).ne_zero
  -- inertia fixes the recentred representative (step (b′))
  have hfix : (σ : Ω ≃ₐ[k] Ω) ((u * wΩ⁻¹ ^ a : Ωˣ) : Ω) =
      ((u * wΩ⁻¹ ^ a : Ωˣ) : Ω) :=
    A.inertia_fixes_of_pow_eq hp hchar σ hσ hcApow hcrespow hσc hxpow
  -- `σ` fixes `wΩ` (it comes from the base field), hence fixes `u`
  have hσw : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom wΩ =
      wΩ := by
    apply Units.ext
    show (σ : Ω ≃ₐ[k] Ω) ((wΩ : Ωˣ) : Ω) = ((wΩ : Ωˣ) : Ω)
    exact (σ : Ω ≃ₐ[k] Ω).commutes w
  have h5 : (u * wΩ⁻¹ ^ a) * wΩ ^ a = u := by
    rw [inv_zpow, inv_mul_cancel_right]
  have hσu : Units.map ((σ : Ω ≃ₐ[k] Ω)).toAlgHom.toRingHom.toMonoidHom u =
      u := by
    rw [← h5, map_mul, map_zpow, hσw]
    congr 1
    apply Units.ext
    exact hfix
  -- conclude: the point itself is fixed
  rw [← hPt, ← hut, he (σ : Ω ≃ₐ[k] Ω) u, hσu]
