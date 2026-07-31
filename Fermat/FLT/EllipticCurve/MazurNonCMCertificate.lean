/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.EuclideanDomain

/-!
# A mod-`ℓ` degree obstruction, and the `p = 11` certificate of Mazur's non-CM table

`Fermat/FLT/ModularCurve/X0.lean` needs, for six explicit curves over `ℚ`, that `Ψ_p` has no
monic rational divisor of degree `p − 1`.  The `ℚ`-side of that is
`Polynomial.exists_monic_dvd_map_zmod_of_monic_dvd_map_rat`
(`Fermat/FLT/Mathlib/RingTheory/Polynomial/ReductionModPrime.lean`), which reduces it to a
statement over `ZMod ℓ`.  This file supplies the finite-field side:

* `not_monic_dvd_of_smallDegreePart` — the UNIFORM degree obstruction, over any finite field.
  Given a factorisation `Ψ = C c * (D * H)` in which `H` divides `X ^ (#K ^ m) - X` and has no
  root in `K`, and given that `1` is the only divisor of `m` that is `≤ n`, no monic divisor of
  `Ψ` of degree `n > deg D` exists.  Note it needs neither `Ψ` squarefree nor `H` factored:
  squarefreeness is what makes such a certificate TRUE, not what makes the proof go.
* `not_monic_dvd_preΨ_elevenA_mod` — the instance at the `p = 11`, `j = −121` row of Mazur's
  table: `ℓ = 23`, `m = 11`, `n = 10`, `deg D = 5`, `deg H = 55`.

The explicit `Ψ̄`, `D` and `H` were produced by PARI/GP 2.15.4 and are re-derived here inside
Lean from mathlib's EDS recursion — `Ψ₂Sq, Ψ₃, preΨ₄, preΨ' 5, preΨ' 6, preΨ' 7` and then
`preΨ'_odd 3`, which is exactly the chain `preΨ' 11` needs.  It lives in its own module rather
than in `X0.lean` because elaboration is single-threaded per file and `X0.lean` is already the
slowest file in the tree; nothing here mentions a modular curve.

**THE ONE OPEN LEAF IS `dvd_X_pow_card_pow_sub_X_hPolyElevenA`**, `H ∣ X ^ (23 ^ 11) - X`.
That is a pure statement about two polynomials over `ZMod 23` — no curve, no `ℚ`, no Galois
theory — and its docstring records the route.
-/

@[expose] public section

open Polynomial

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace Fermat.MazurNonCMCertificate

/-- **THE DEGREE OBSTRUCTION** (PROVEN 2026-07-30), uniform over finite fields.

`hmn` says `1` is the only divisor of `m` that is at most `n`; at `m = 11`, `n = 10` that is
the primality of `11`, and at `m = 34`, `n = 16` it FAILS for `d = 2`, which is why the
`p = 17` rows need a second coprimality and the `p = 11` rows do not.

The proof is three steps.  `G` and `H` share no irreducible factor `π`: such a `π` would have
`deg π ∣ m` by `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X` and `deg π ≤ n` by
`natDegree_le_of_dvd`, hence `deg π = 1` by `hmn`, hence a root of `π` — which is a root of
`H`, against `hHroot`.  So `IsCoprime G H`, so `G ∣ C c * D`, so `G ∣ D` since `C c` is a unit;
and then `n = deg G ≤ deg D < n`. -/
theorem not_monic_dvd_of_smallDegreePart {K : Type*} [Field K] [Finite K]
    {Ψ D H : K[X]} {c : K} (hc : c ≠ 0) (hfac : Ψ = C c * (D * H))
    {m n : ℕ} (hmn : ∀ d : ℕ, d ∣ m → d ≤ n → d = 1)
    (hHdvd : H ∣ X ^ (Nat.card K) ^ m - X)
    (hHroot : ∀ a : K, H.eval a ≠ 0)
    (hD0 : D ≠ 0) (hD : D.natDegree < n)
    (G : K[X]) (hG : G.Monic) (hGdeg : G.natDegree = n) : ¬ G ∣ Ψ := by
  classical
  intro hdvd
  have hG0 : G ≠ 0 := hG.ne_zero
  have hcop : IsCoprime G H := by
    rw [← EuclideanDomain.gcd_isUnit_iff]
    by_contra hu
    have hne : EuclideanDomain.gcd G H ≠ 0 := fun h => hG0 (by
      simpa using EuclideanDomain.gcd_eq_zero_iff.mp h |>.1)
    obtain ⟨π, hπ, hπdvd⟩ := WfDvdMonoid.exists_irreducible_factor hu hne
    have hπG : π ∣ G := hπdvd.trans (EuclideanDomain.gcd_dvd_left G H)
    have hπH : π ∣ H := hπdvd.trans (EuclideanDomain.gcd_dvd_right G H)
    have hdeg1 : π.natDegree = 1 :=
      hmn _ (hπ.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (hπH.trans hHdvd))
        (hGdeg ▸ natDegree_le_of_dvd hπG hG0)
    obtain ⟨a, ha⟩ := exists_root_of_degree_eq_one
      (by rw [degree_eq_natDegree hπ.ne_zero, hdeg1]; rfl)
    exact hHroot a (by obtain ⟨t, ht⟩ := hπH; rw [ht, eval_mul, ha, zero_mul])
  have h2 : G ∣ C c * D := by
    rw [hfac, ← mul_assoc] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd
  have h3 : G ∣ D := (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)).dvd_mul_left.mp h2
  have := natDegree_le_of_dvd h3 hD0
  omega

/-! ### The `p = 11`, `j = −121` row over `ZMod 23`

`Δ = −14641 = −11⁴` is prime to `23`, so the reduction is good, and `23 ∤ 11 = leadingCoeff Ψ₁₁`.
-/

/-- The minimal model `[1,1,0,-2,-7]` of the `p = 11`, `j = −121` row, read over `ZMod 23`.
Definitionally `Fermat.nonCMModelElevenAmod`. -/
def elevenAMod : WeierstrassCurve (ZMod 23) := ⟨1, 1, 0, -2, -7⟩

/-- The product of the five LINEAR irreducible factors of `Ψ₁₁ mod 23`. -/
noncomputable def dPolyElevenA : (ZMod 23)[X] :=
  X^5 + 14*X^4 + 7*X^3 + 9*X^2 + 16*X + 1

/-- The product of the five irreducible factors of `Ψ₁₁ mod 23` of degree `11`. -/
noncomputable def hPolyElevenA : (ZMod 23)[X] :=
  X^55 + 11*X^54 + 12*X^53 + 22*X^52 + 10*X^51 + 10*X^50 + 13*X^49 + 20*X^48 + X^47 + 12*X^46 +
    13*X^45 + 10*X^44 + 11*X^43 + 2*X^42 + 7*X^41 + 9*X^40 + 16*X^39 + 2*X^38 + 5*X^37 + 16*X^36 +
    5*X^35 + 17*X^34 + 17*X^33 + 16*X^31 + 19*X^30 + 20*X^29 + 19*X^28 + 21*X^27 + 3*X^26 +
    8*X^25 + X^24 + 6*X^23 + 4*X^22 + 9*X^21 + 4*X^20 + 14*X^19 + 13*X^18 + 22*X^17 + 4*X^16 +
    10*X^14 + 15*X^13 + 10*X^12 + 19*X^11 + 6*X^10 + 7*X^9 + 16*X^8 + 22*X^7 + 2*X^6 + 21*X^5 +
    22*X^4 + 6*X^3 + X^2 + 4*X + 19

theorem Ψ₂Sq_elevenAMod : elevenAMod.Ψ₂Sq =
    4*X^3 + 5*X^2 + 15*X + 18 := by
  rw [WeierstrassCurve.Ψ₂Sq]
  simp only [elevenAMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    map_ofNat, C_neg, C_add, C_mul, C_pow, C_1, C_0]
  reduce_mod_char

theorem Ψ₃_elevenAMod : elevenAMod.Ψ₃ =
    3*X^4 + 5*X^3 + 11*X^2 + 8*X + 7 := by
  rw [WeierstrassCurve.Ψ₃]
  simp only [elevenAMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_ofNat, C_neg, C_add, C_sub, C_mul, C_pow, C_1, C_0]
  reduce_mod_char

theorem preΨ₄_elevenAMod : elevenAMod.preΨ₄ =
    2*X^6 + 5*X^5 + 3*X^4 + 19*X^3 + X^2 + 15*X + 16 := by
  rw [WeierstrassCurve.preΨ₄]
  simp only [elevenAMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_ofNat, C_neg, C_add, C_sub, C_mul, C_pow, C_1, C_0]
  reduce_mod_char

theorem preΨ'_five_elevenAMod : elevenAMod.preΨ' 5 =
    5*X^12 + 2*X^11 + 16*X^10 + 15*X^9 + X^8 + X^7 + 8*X^5 + X^4 + 20*X^3 + 6*X^2 + 19*X + 11 := by
  have h := elevenAMod.preΨ'_odd 0
  norm_num [WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_two] at h
  rw [h, Ψ₃_elevenAMod, preΨ₄_elevenAMod, Ψ₂Sq_elevenAMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_six_elevenAMod : elevenAMod.preΨ' 6 =
    3*X^16 + 20*X^15 + 19*X^14 + 7*X^13 + 20*X^12 + 21*X^11 + 18*X^10 + 16*X^9 + 6*X^8 + 21*X^7 +
    4*X^6 + 20*X^5 + 3*X^4 + 20*X^3 + 2*X^2 + 11*X + 10 := by
  have h := elevenAMod.preΨ'_even 0
  norm_num [WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_two,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_elevenAMod, preΨ₄_elevenAMod, preΨ'_five_elevenAMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_seven_elevenAMod : elevenAMod.preΨ' 7 =
    7*X^24 + X^23 + 19*X^22 + 11*X^21 + 21*X^20 + 8*X^19 + 14*X^18 + 10*X^17 + 22*X^16 + 6*X^15 +
    4*X^14 + X^13 + 11*X^12 + 12*X^11 + 10*X^10 + 22*X^9 + 3*X^8 + 3*X^7 + 19*X^6 + 12*X^5 +
    10*X^4 + 7*X^3 + 9*X^2 + 2*X + 20 := by
  have h := elevenAMod.preΨ'_odd 1
  norm_num [WeierstrassCurve.preΨ'_two, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_elevenAMod, preΨ₄_elevenAMod, preΨ'_five_elevenAMod, Ψ₂Sq_elevenAMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

/-- **`Ψ₁₁ mod 23 = 11 · D · H`** (PROVEN 2026-07-30), the certificate in the form
`not_monic_dvd_of_smallDegreePart` consumes.  `preΨ'_odd 3` needs exactly `preΨ' 7`,
`preΨ' 5`, `preΨ₄`, `preΨ' 6` and `Ψ₂Sq`, which is why the chain above stops where it does. -/
theorem preΨ'_eleven_elevenAMod :
    elevenAMod.preΨ' 11 = C 11 * (dPolyElevenA * hPolyElevenA) := by
  have h := elevenAMod.preΨ'_odd 3
  norm_num [WeierstrassCurve.preΨ'_four, Nat.even_iff] at h
  rw [h, preΨ₄_elevenAMod, preΨ'_five_elevenAMod, preΨ'_six_elevenAMod,
    preΨ'_seven_elevenAMod, Ψ₂Sq_elevenAMod, dPolyElevenA, hPolyElevenA]
  simp only [map_ofNat]
  reduce_mod_char
  ring_nf
  reduce_mod_char

/-- `H` has no root in `ZMod 23`: it is a product of irreducibles of degree `11`.  Twenty-three
evaluations of a degree-`55` polynomial, so `decide` does it directly. -/
theorem eval_hPolyElevenA_ne_zero (a : ZMod 23) : hPolyElevenA.eval a ≠ 0 := by
  revert a
  simp only [hPolyElevenA, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  decide

/-- **THE ONE OPEN LEAF OF THIS FILE** (sorry leaf, cut 2026-07-30): `H` divides
`X ^ (23 ^ 11) - X`, i.e. every irreducible factor of `H` has degree dividing `11`.

TRUE, machine-checked in PARI/GP 2.15.4 (`Mod(x, H) ^ (23 ^ 11) == x`); `H` is in fact a
product of five irreducibles of degree exactly `11`, and `eval_hPolyElevenA_ne_zero` above is
what turns "dividing `11`" into "equal to `11`" where the obstruction needs it.

**THE ROUTE, and it is entirely mechanical.**  Write `r_k := X ^ (23 ^ k) mod H`, so `r_0 = X`
and the claim is `r_11 = X`.  Do NOT compute `r_k ^ 23` by repeated squaring: over `ZMod 23`
the Frobenius is LINEAR, `r ^ 23 = Polynomial.expand 23 r` (`Polynomial.expand_char` together
with `ZMod.pow_card`, which kills the coefficient-wise `c ↦ c ^ 23`).  So precompute the table
`T_i := X ^ (23 * i) mod H` for `i ≤ 54` — each `T_{i+1}` is `T_i * T_1` reduced, one identity
of degree `≤ 108` apiece — and then each of the eleven Frobenius steps is a single `ZMod 23`
linear combination of the `T_i`, which `ring_nf` checks at degree `54`.

Every identity is of the shape `A * B = Q * H + R`, verified by the same
`reduce_mod_char; ring_nf; reduce_mod_char` idiom the chain above uses; `Q` and `R` come from
PARI.  The count is about `65` identities and the arithmetic is `≈ 2·10⁵` `F₂₃` operations,
which is the figure the `X0.lean` cost triage calls "comfortably kernel-checkable".

The same route closes the `p = 11`, `j = −24729001` row (same `ℓ`, same degrees) and, with one
extra coprimality at `d = 2`, the two `p = 17` rows.  It does NOT close the `p = 37` rows:
there `deg H = 666`, `ℓ = 397` and `m = 222`. -/
theorem dvd_X_pow_card_pow_sub_X_hPolyElevenA :
    hPolyElevenA ∣ X ^ (Nat.card (ZMod 23)) ^ 11 - X :=
  sorry

/-- **Row `p = 11`, `j = −121`: `Ψ₁₁ mod 23` has no monic divisor of degree `10`**
(PROVEN 2026-07-30 over `dvd_X_pow_card_pow_sub_X_hPolyElevenA`).

This is what `Fermat.not_monic_dvd_preΨ_mod_nonCMModelElevenA` in `X0.lean` consumes, and
through `Fermat.not_monic_dvd_preΨ_of_mod` it is the whole content of the `ℚ`-statement
`Fermat.not_monic_dvd_preΨ_nonCMModelElevenA`. -/
theorem not_monic_dvd_preΨ_elevenA_mod (G : (ZMod 23)[X]) (hG : G.Monic)
    (hdeg : G.natDegree = 10) : ¬ G ∣ elevenAMod.preΨ' 11 := by
  have hp23 : Nat.Prime 23 := by decide
  have hp11 : Nat.Prime 11 := by decide
  have hc : (11 : ZMod 23) ≠ 0 := by decide
  have hmn : ∀ d : ℕ, d ∣ 11 → d ≤ 10 → d = 1 := by
    intro d hd hle
    rcases hp11.eq_one_or_self_of_dvd d hd with h | h
    · exact h
    · omega
  haveI : Fact (Nat.Prime 23) := ⟨hp23⟩
  have hDdeg : dPolyElevenA.natDegree = 5 := by rw [dPolyElevenA]; compute_degree!
  have hD0 : dPolyElevenA ≠ 0 := fun h => by rw [h, natDegree_zero] at hDdeg; omega
  have hDlt : dPolyElevenA.natDegree < 10 := by omega
  exact not_monic_dvd_of_smallDegreePart hc preΨ'_eleven_elevenAMod hmn
    dvd_X_pow_card_pow_sub_X_hPolyElevenA eval_hPolyElevenA_ne_zero hD0 hDlt G hG hdeg

end Fermat.MazurNonCMCertificate

end
