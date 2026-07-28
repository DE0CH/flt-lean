/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!

# Automorphisms of an elliptic curve with `j ∉ {0, 1728}`

Proposed new Mathlib file `Mathlib.AlgebraicGeometry.EllipticCurve.Aut`.

Let `E` be an elliptic curve over a field `K`. Over a field, isomorphisms of Weierstrass curves
are exactly the admissible changes of variables `WeierstrassCurve.VariableChange K`, acting via
`•`; the automorphisms of `E` are therefore the `C : VariableChange K` with `C • E = E`. This file
proves the classical fact (Silverman, *The Arithmetic of Elliptic Curves*, III.10) that if
`j(E) ∉ {0, 1728}` then the only automorphisms of `E` are `±1`, uniformly in the characteristic.

## Main definitions and statements

* `WeierstrassCurve.eq_one_or_eq_negVariableChange_of_smul_eq` : if `j(E) ∉ {0, 1728}` then any
  `C : VariableChange K` with `C • E = E` equals `1` or `negVariableChange E`.
* `WeierstrassCurve.autGroup E` : the automorphism group of `E`, as the stabiliser of `E` under
  the action of `VariableChange K`.
* `WeierstrassCurve.autGroupMulEquiv` : for `j(E) ∉ {0, 1728}`, the (computable) isomorphism
  `autGroup E ≃* Multiplicative (ZMod 2)`.

## Implementation notes

The proof is broken into pieces. `j ∉ {0, 1728}` is equivalent to `c₄ ≠ 0` and `c₆ ≠ 0`
(`j_eq_zero_iff` and `c₆_eq_zero_iff_j_eq_1728`). From the transformation laws of `c₄` and `c₆`
one gets `u² = 1` (`u_eq_one_or_eq_neg_one`), which reduces everything to the case `u = 1`. There
`r = 0` follows from the transformation laws of `b₄`, `b₆`, `b₈` (`r_eq_zero_of_u_eq_one`), and
then `s`, `t` are read off from those of `a₁`, `a₂`, `a₃`, `a₄`
(`eq_one_or_eq_negVariableChange_of_u_eq_one`, where the `negVariableChange` value can occur only
in characteristic `2`).

-/

@[expose] public section

namespace WeierstrassCurve

universe u

variable {K : Type u} [Field K] (E : WeierstrassCurve K)

/-! ### `Aut(E) = {±1}` for `j ∉ {0, 1728}`

Throughout, `C • E = E` is an automorphism of `E`; the nonvanishing of `c₄` and `c₆` encodes
`j ∉ {0, 1728}`. -/

-- (module-system note: the two lemmas below are consumed by the proofs of the
-- theorems that follow, but the EXPORTED proof bodies hide those edges from
-- the term-cone detector — do not delete as free-floating.)
/-- An automorphism `C` of `E` with `C.u = 1` has no `x`-translation: `C.r = 0`. This follows
from the transformation laws of `b₄`, `b₆`, `b₈` together with `c₆ ≠ 0`. -/
lemma r_eq_zero_of_u_eq_one (hc6 : E.c₆ ≠ 0) {C : VariableChange K} (hu : C.u = 1)
    (hCE : C • E = E) :
    C.r = 0 := by
  rw [c₆] at hc6
  have eb4 := congrArg b₄ hCE
  have eb6 := congrArg b₆ hCE
  have eb8 := congrArg b₈ hCE
  simp [variableChange_b₄, variableChange_b₆, variableChange_b₈, hu] at eb4 eb6 eb8
  grobner


/-- The `u`-coefficient of an automorphism `C` of `E` (with `c₄, c₆ ≠ 0`) satisfies `u² = 1`:
the `c₄` and `c₆` laws give `u⁴ = u⁶ = 1`. -/
lemma u_eq_one_or_eq_neg_one (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0) {C : VariableChange K}
    (hCE : C • E = E) : C.u = 1 ∨ C.u = -1 := by
  have hu4 : (C.u : K) ^ 4 = 1 := by
    have h := congrArg c₄ hCE
    rwa [variableChange_c₄, Units.val_inv_eq_inv_val, mul_eq_right₀ hc4, inv_pow, inv_eq_one] at h
  have hu6 : (C.u : K) ^ 6 = 1 := by
    have h := congrArg c₆ hCE
    rwa [variableChange_c₆, Units.val_inv_eq_inv_val, mul_eq_right₀ hc6, inv_pow, inv_eq_one] at h
  have hu2 : (C.u : K) * (C.u : K) = 1 := by linear_combination hu6 - (C.u : K) ^ 2 * hu4
  rcases mul_self_eq_one_iff.mp hu2 with h | h
  · exact .inl (Units.val_eq_one.mp h)
  · exact .inr (Units.ext h)


/-- An automorphism `C` of `E` with `C.u = 1` is either the identity or `negVariableChange E`.
After `r_eq_zero_of_u_eq_one`, the `a₁` and `a₃` laws give `2s = 2t = 0`; in characteristic `≠ 2`
this forces `s = t = 0`, and in characteristic `2` the `a₂`, `a₄` laws pin `(s, t)` down to either
`(0, 0)` or `(-a₁, -a₃)`. -/
lemma eq_one_or_eq_negVariableChange_of_u_eq_one (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0)
    {C : VariableChange K} (hu : C.u = 1) (hCE : C • E = E) :
    C = 1 ∨ C = E.negVariableChange := by
  have hr : C.r = 0 := E.r_eq_zero_of_u_eq_one hc6 hu hCE
  obtain ⟨e1, e2, e3, e4, -⟩ := WeierstrassCurve.ext_iff.mp hCE
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, hu,
    inv_one, Units.val_one, one_pow, one_mul] at e1 e2 e3 e4
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · -- characteristic `2`: `a₁ ≠ 0` (else `c₄ = a₁⁴ = 0`); the `a₂`, `a₄` laws force `(s, t)` to be
    -- `(0, 0)` or `(-a₁, -a₃)`, the latter being `negVariableChange` since `-1 = 1`.
    have ha1 : E.a₁ ≠ 0 := by rw [c₄, b₂, b₄] at hc4; grobner
    have hq2 : C.s * (E.a₁ + C.s) = 0 := by linear_combination -e2 + 3 * hr
    have hq4 : C.s * E.a₃ + C.t * E.a₁ = 0 := by
      linear_combination -e4 + (2 * E.a₂ - C.s * E.a₁ + 3 * C.r) * hr - C.s * C.t * h2
    rcases (mul_eq_zero.mp hq2).imp id eq_neg_of_add_eq_zero_right with hs | hs
    · have ht : C.t = 0 := by grobner
      exact .inl (VariableChange.ext hu hr hs ht)
    · have ht : C.t = -E.a₃ := by grobner
      have hu1neg : (1 : Kˣ) = -1 := by ext; push_cast; linear_combination h2
      exact .inr (VariableChange.ext (hu.trans hu1neg) hr hs ht)
  · -- characteristic `≠ 2`: `2s = 2t = 0`, so `s = t = 0` and `C = 1`.
    have hs : C.s = 0 := by grobner
    have ht : C.t = 0 := by grobner
    exact .inl (VariableChange.ext hu hr hs ht)

/-- If `c₄ ≠ 0` and `c₆ ≠ 0` then the only admissible changes of variables fixing `E` are `1` and
`negVariableChange E`. This is the form of `Aut(E) = {±1}` phrased via `c₄, c₆` (equivalent to
`j ∉ {0, 1728}` for an elliptic curve, see `eq_one_or_eq_negVariableChange_of_smul_eq`). -/
theorem eq_one_or_eq_negVariableChange_of_smul_eq_of_c₄_ne_zero (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0)
    {C : VariableChange K} (hC : C • E = E) : C = 1 ∨ C = E.negVariableChange := by
  rcases E.u_eq_one_or_eq_neg_one hc4 hc6 hC with hu | hu
  · exact E.eq_one_or_eq_negVariableChange_of_u_eq_one hc4 hc6 hu hC
  · -- Reduce `u = -1` to `u = 1` by composing with the involution `negVariableChange E`.
    have hDu : (E.negVariableChange * C).u = 1 := by
      rw [show (E.negVariableChange * C).u = E.negVariableChange.u * C.u from rfl,
        negVariableChange_u, hu, neg_one_mul, neg_neg]
    have hDE : (E.negVariableChange * C) • E = E := by
      rw [mul_smul, hC, negVariableChange_smul_self]
    have hCeq : C = E.negVariableChange * (E.negVariableChange * C) := by
      rw [← mul_assoc, negVariableChange_mul_self, one_mul]
    rcases E.eq_one_or_eq_negVariableChange_of_u_eq_one hc4 hc6 hDu hDE with h | h
    · right; rw [hCeq, h, mul_one]
    · left; rw [hCeq, h, negVariableChange_mul_self]

/-- If `j(E) ∉ {0, 1728}` then the only admissible changes of variables fixing `E` are `1` and
`negVariableChange E`; that is, `Aut(E) = {±1}`. -/
theorem eq_one_or_eq_negVariableChange_of_smul_eq [E.IsElliptic] (hj₀ : E.j ≠ 0)
    (hj₁₇₂₈ : E.j ≠ 1728) {C : VariableChange K} (hC : C • E = E) :
    C = 1 ∨ C = E.negVariableChange :=
  E.eq_one_or_eq_negVariableChange_of_smul_eq_of_c₄_ne_zero (E.j_eq_zero_iff.not.mp hj₀)
    (E.c₆_eq_zero_iff_j_eq_1728.not.mpr hj₁₇₂₈) hC

/-! ### The automorphism group at `j ∈ {0, 1728}`

At `j ∈ {0, 1728}` the conclusion `Aut(E) = {±1}` is FALSE — the curves `y² = x³ + ax` and
`y² = x³ + b` carry the extra automorphisms `(x, y) ↦ (u²x, u³y)` for `u⁴ = 1`, resp. `u⁶ = 1`.
What survives, and what this subsection isolates, is the *shape* of the argument above:

* the `c₄` and `c₆` transformation laws give `u⁴ = 1` whenever `c₄ ≠ 0` and `u⁶ = 1` whenever
  `c₆ ≠ 0` (`u_pow_four_eq_one_of_smul_eq`, `u_pow_six_eq_one_of_smul_eq`) — these are the two
  halves of `u_eq_one_or_eq_neg_one` used separately rather than together, and exactly one of the
  two hypotheses survives at each special `j`;
* an elliptic curve never has `c₄ = c₆ = 0` (`c_relation`), so at `j = 1728` (`c₆ = 0`) one gets
  `u⁴ = 1` and at `j = 0` (`c₄ = 0`) one gets `u⁶ = 1`
  (`u_pow_four_eq_one_of_smul_eq_of_j_eq_1728`, `u_pow_six_eq_one_of_smul_eq_of_j_eq_zero`);
* in characteristic `≠ 2, 3`, and with NO hypothesis on `j` at all, `u` determines the
  automorphism: `u = 1` forces `C = 1` (`eq_one_of_u_eq_one_of_smul_eq`) and `u = -1` forces
  `C = negVariableChange E` (`eq_negVariableChange_of_u_eq_neg_one`).  The `r = 0` step of
  `eq_one_or_eq_negVariableChange_of_u_eq_one` needed `c₆ ≠ 0` because it had to work in
  characteristic `2`; away from characteristics `2` and `3` the `a₁`, `a₂`, `a₃` laws alone give
  `s = r = t = 0` and no hypothesis on `j` is needed.

Together these say that `C ↦ C.u` embeds `Aut(E)` into `μ₄` (at `j = 1728`) or `μ₆` (at `j = 0`)
in characteristic `0`, which is the form in which the automorphism group is consumed by the
descent argument of `ModularCurve/X0.lean`
(`exists_stableCyclic_twist_of_autStable_of_j_special`): there one needs to know that an
automorphism which does NOT preserve a cyclic subgroup has `u ≠ ±1`, hence `u² = -1` at
`j = 1728` and `u` of order `3` or `6` at `j = 0`. -/

/-- **An automorphism with `u = 1` is the identity**, in characteristic `≠ 2, 3`.

Unlike `eq_one_or_eq_negVariableChange_of_u_eq_one` this needs NO hypothesis on `j`: that lemma
had to cover characteristic `2`, where `1 = -1` and `negVariableChange` is a genuine second
solution, and paid for it with `c₄, c₆ ≠ 0`.  Here the `a₁` law gives `2s = 0`, hence `s = 0`;
the `a₂` law then gives `3r = 0`, hence `r = 0`; and the `a₃` law gives `2t = 0`. -/
lemma eq_one_of_u_eq_one_of_smul_eq (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {C : VariableChange K} (hu : C.u = 1) (hCE : C • E = E) : C = 1 := by
  obtain ⟨e1, e2, e3, -, -⟩ := WeierstrassCurve.ext_iff.mp hCE
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, hu, inv_one,
    Units.val_one, one_pow, one_mul] at e1 e2 e3
  have hs : C.s = 0 := by
    rcases mul_eq_zero.mp (show (2 : K) * C.s = 0 by linear_combination e1) with h | h
    · exact absurd h h2
    · exact h
  have hr : C.r = 0 := by
    rcases mul_eq_zero.mp
      (show (3 : K) * C.r = 0 by linear_combination e2 + (E.a₁ + C.s) * hs) with h | h
    · exact absurd h h3
    · exact h
  have ht : C.t = 0 := by
    rcases mul_eq_zero.mp (show (2 : K) * C.t = 0 by linear_combination e3 - E.a₁ * hr) with h | h
    · exact absurd h h2
    · exact h
  exact VariableChange.ext hu hr hs ht

/-- **An automorphism with `u = -1` is `negVariableChange E`**, in characteristic `≠ 2, 3` and
with no hypothesis on `j`.  Compose with the involution `negVariableChange E` and apply
`eq_one_of_u_eq_one_of_smul_eq`. -/
theorem eq_negVariableChange_of_u_eq_neg_one (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {C : VariableChange K} (hu : C.u = -1) (hCE : C • E = E) : C = E.negVariableChange := by
  have hmul : (E.negVariableChange * C) • E = E := by
    rw [mul_smul, hCE, negVariableChange_smul_self]
  have hu1 : (E.negVariableChange * C).u = 1 := by
    show E.negVariableChange.u * C.u = 1
    rw [negVariableChange_u, hu, neg_mul_neg, one_mul]
  have h1 := E.eq_one_of_u_eq_one_of_smul_eq h2 h3 hu1 hmul
  calc C = E.negVariableChange * E.negVariableChange * C := by
        rw [negVariableChange_mul_self, one_mul]
    _ = E.negVariableChange * (E.negVariableChange * C) := by rw [mul_assoc]
    _ = E.negVariableChange := by rw [h1, mul_one]

/-- The `c₄` transformation law alone: an automorphism of a curve with `c₄ ≠ 0` has `u⁴ = 1`. -/
lemma u_pow_four_eq_one_of_smul_eq (hc4 : E.c₄ ≠ 0) {C : VariableChange K}
    (hCE : C • E = E) : (C.u : K) ^ 4 = 1 := by
  have h := congrArg c₄ hCE
  rwa [variableChange_c₄, Units.val_inv_eq_inv_val, mul_eq_right₀ hc4, inv_pow, inv_eq_one] at h

/-- The `c₆` transformation law alone: an automorphism of a curve with `c₆ ≠ 0` has `u⁶ = 1`. -/
lemma u_pow_six_eq_one_of_smul_eq (hc6 : E.c₆ ≠ 0) {C : VariableChange K}
    (hCE : C • E = E) : (C.u : K) ^ 6 = 1 := by
  have h := congrArg c₆ hCE
  rwa [variableChange_c₆, Units.val_inv_eq_inv_val, mul_eq_right₀ hc6, inv_pow, inv_eq_one] at h

/-- An elliptic curve with `j = 1728` has `c₄ ≠ 0`: `c₆ = 0` there, and `1728Δ = c₄³ - c₆²`
would force `Δ = 0`. -/
lemma c₄_ne_zero_of_j_eq_1728 [E.IsElliptic] (h1728 : (1728 : K) ≠ 0) (hj : E.j = 1728) :
    E.c₄ ≠ 0 := by
  intro hc4
  have hc6 : E.c₆ = 0 := E.c₆_eq_zero_iff_j_eq_1728.mpr hj
  have hrel := E.c_relation
  rw [hc4, hc6] at hrel
  exact mul_ne_zero h1728 E.isUnit_Δ.ne_zero (by simpa using hrel)

/-- An elliptic curve with `j = 0` has `c₆ ≠ 0`: `c₄ = 0` there, and `1728Δ = c₄³ - c₆²`
would force `Δ = 0`. -/
lemma c₆_ne_zero_of_j_eq_zero [E.IsElliptic] (h1728 : (1728 : K) ≠ 0) (hj : E.j = 0) :
    E.c₆ ≠ 0 := by
  intro hc6
  have hc4 : E.c₄ = 0 := E.j_eq_zero_iff.mp hj
  have hrel := E.c_relation
  rw [hc4, hc6] at hrel
  exact mul_ne_zero h1728 E.isUnit_Δ.ne_zero (by simpa using hrel)

/-- **`Aut(E) ↪ μ₄` at `j = 1728`**: every automorphism of an elliptic curve with `j = 1728`
has `u⁴ = 1`. -/
theorem u_pow_four_eq_one_of_smul_eq_of_j_eq_1728 [E.IsElliptic] (h1728 : (1728 : K) ≠ 0)
    (hj : E.j = 1728) {C : VariableChange K} (hCE : C • E = E) : (C.u : K) ^ 4 = 1 :=
  E.u_pow_four_eq_one_of_smul_eq (E.c₄_ne_zero_of_j_eq_1728 h1728 hj) hCE

/-- **`Aut(E) ↪ μ₆` at `j = 0`**: every automorphism of an elliptic curve with `j = 0`
has `u⁶ = 1`. -/
theorem u_pow_six_eq_one_of_smul_eq_of_j_eq_zero [E.IsElliptic] (h1728 : (1728 : K) ≠ 0)
    (hj : E.j = 0) {C : VariableChange K} (hCE : C • E = E) : (C.u : K) ^ 6 = 1 :=
  E.u_pow_six_eq_one_of_smul_eq (E.c₆_ne_zero_of_j_eq_zero h1728 hj) hCE

end WeierstrassCurve

end
