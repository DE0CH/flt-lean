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
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Finiteness

/-!
# A mod-`ℓ` degree obstruction, and the `p = 11` certificate of Mazur's non-CM table

`Fermat/FLT/ModularCurve/X0.lean` needs, for six explicit curves over `ℚ`, that `Ψ_p` has no
monic rational divisor of degree `p − 1`.  The `ℚ`-side of that is
`Polynomial.exists_monic_dvd_map_zmod_of_monic_dvd_map_rat`
(`Fermat/FLT/Mathlib/RingTheory/Polynomial/ReductionModPrime.lean`), which reduces it to a
statement over `ZMod ℓ`.  This file supplies the finite-field side:

* `not_monic_dvd_of_bigDegreePart` — the UNIFORM degree obstruction, in the form that applies
  at every row.  Given a factorisation `Ψ = C c * (D * H)` in which every irreducible factor of
  `H` has degree `> n`, no monic divisor of `Ψ` of degree `n > deg D` exists.  It needs neither
  `Ψ` squarefree nor `H` factored nor `K` finite: squarefreeness is what makes such a
  certificate TRUE, not what makes the proof go.
* `not_monic_dvd_of_smallDegreePart` — the corollary in which the hypothesis on `H` is the one a
  computation certifies: `H ∣ X ^ (#K ^ m) - X`, `H` has no root in `K`, and `1` is the only
  divisor of `m` that is `≤ n`.
* `not_monic_dvd_of_coprimeSmallDegreeParts` — the corollary for the rows where that last clause
  FAILS.  At `m = 34, n = 16` (`p = 17`) and at `m = 222, n = 36` (`p = 37`) there are divisors
  `d ∣ m` with `1 < d ≤ n`, and the no-root hypothesis is exactly the `d = 1` instance of the
  right one: `IsCoprime H (X ^ (#K ^ d) - X)` for every such `d`.  That is the form in which
  each clause is a single `gcd` computation.
* `dvd_X_pow_card_pow_natDegree_sub_X_of_irreducible` — the converse of mathlib's
  `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`, and the reason the previous item can
  exist at all: an irreducible `π` of degree `d` over a finite field divides `X ^ (#K ^ d) - X`,
  so a `gcd` certificate at `d` really does exclude factors of degree `d`.
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

/-- **THE DEGREE OBSTRUCTION** (PROVEN 2026-07-30; generalised 2026-07-31), in the form that
applies at every row of the table and not only at the `p = 11` ones.

The hypothesis on `H` is exactly what the argument uses: every irreducible factor of `H` has
degree `> n`.  Nothing about `X ^ (#K ^ m) - X`, nothing about roots, and `K` need not even be
finite — the finite-field input enters only when a *certificate* for `hHbig` is produced, which
is what the two corollaries below do.

The proof is three steps.  `G` and `H` share no irreducible factor `π`: such a `π` would divide
`G`, so `deg π ≤ deg G = n` by `natDegree_le_of_dvd`, against `hHbig`.  So `IsCoprime G H`, so
`G ∣ C c * D`, so `G ∣ D` since `C c` is a unit; and then `n = deg G ≤ deg D < n`.

**Why this shape, and not the `hmn` one it replaces** (2026-07-31).  The previous statement
asked that `1` be the only divisor of `m` that is `≤ n`.  That is the primality of `11` at the
`p = 11` rows, and it is FALSE at every other row of Mazur's table: `m = 34, n = 16` has
`d = 2`, and `m = 222, n = 36` has `d = 2, 3, 6`.  So the lemma as originally stated did not
apply to four of the six rows — a defect recorded in
`Fermat.not_monic_dvd_preΨ_mod_nonCMModelThirtySevenB`'s docstring on the day it was measured.
Splitting the certificate off from the obstruction fixes that once for all rows. -/
theorem not_monic_dvd_of_bigDegreePart {K : Type*} [Field K]
    {Ψ D H : K[X]} {c : K} (hc : c ≠ 0) (hfac : Ψ = C c * (D * H))
    {n : ℕ} (hHbig : ∀ π : K[X], Irreducible π → π ∣ H → n < π.natDegree)
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
    exact absurd (hGdeg ▸ natDegree_le_of_dvd hπG hG0) (not_le.mpr (hHbig π hπ hπH))
  have h2 : G ∣ C c * D := by
    rw [hfac, ← mul_assoc] at hdvd
    exact hcop.dvd_of_dvd_mul_right hdvd
  have h3 : G ∣ D := (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)).dvd_mul_left.mp h2
  have := natDegree_le_of_dvd h3 hD0
  omega

/-- **AN IRREDUCIBLE OF DEGREE `d` OVER A FINITE FIELD DIVIDES `X ^ (#K ^ d) - X`**
(2026-07-31), the converse of mathlib's
`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`.

Standard, and the proof is the standard one: `K[X]/(π)` is a field with `#K ^ deg π` elements,
so its generator `x` satisfies `x ^ (#K ^ deg π) = x`, so the minimal polynomial of `x` — which
is `π` up to the unit `C (leadingCoeff π)⁻¹` — divides `X ^ (#K ^ deg π) - X`.

It is what makes `not_monic_dvd_of_coprimeSmallDegreeParts` possible: without it, a `gcd`
computation `gcd(H, X ^ (#K ^ d) - X) = 1` would rule out only those degree-`d` factors that
one already knew how to see, whereas the two directions together say that the degree-`d`
irreducible factors of `H` are EXACTLY the ones this `gcd` sees. -/
theorem dvd_X_pow_card_pow_natDegree_sub_X_of_irreducible {K : Type*} [Field K] [Finite K]
    {π : K[X]} (hπ : Irreducible π) : π ∣ X ^ (Nat.card K) ^ π.natDegree - X := by
  haveI : Fact (Irreducible π) := ⟨hπ⟩
  have hπ0 : π ≠ 0 := hπ.ne_zero
  haveI : Module.Finite K (AdjoinRoot π) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hπ0).basis
  haveI : Finite (AdjoinRoot π) := Module.finite_of_finite (R := K)
  haveI := Fintype.ofFinite (AdjoinRoot π)
  have hcard : Nat.card (AdjoinRoot π) = Nat.card K ^ π.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot π),
      (AdjoinRoot.powerBasis hπ0).finrank, AdjoinRoot.powerBasis_dim]
  have hroot : (AdjoinRoot.root π) ^ (Nat.card K ^ π.natDegree) = AdjoinRoot.root π := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hdvd : minpoly K (AdjoinRoot.root π) ∣ X ^ (Nat.card K) ^ π.natDegree - X :=
    minpoly.dvd _ _ (by simp [hroot])
  rw [AdjoinRoot.minpoly_root hπ0] at hdvd
  exact (dvd_mul_right π (C π.leadingCoeff⁻¹)).trans hdvd

/-- **THE DEGREE OBSTRUCTION, `gcd`-CERTIFICATE FORM** (2026-07-31) — the shape every row of
Mazur's table can use, including the four the `hmn` form below cannot reach.

`hHdvd` says the irreducible factors of `H` have degree dividing `m`; `hHsmall` kills, one
`gcd` at a time, each degree `d ∣ m` that is small enough to matter.  At `m = 11, n = 10` the
only such `d` is `1` and `hHsmall` is the no-root hypothesis; at `m = 34, n = 16` they are
`1, 2`; at `m = 222, n = 36` they are `1, 2, 3, 6`.

The `d = 0` case is vacuous and is discharged inside rather than excluded by hypothesis: an
irreducible has positive degree, so `d = deg π ≠ 0` whenever the clause is invoked. -/
theorem not_monic_dvd_of_coprimeSmallDegreeParts {K : Type*} [Field K] [Finite K]
    {Ψ D H : K[X]} {c : K} (hc : c ≠ 0) (hfac : Ψ = C c * (D * H))
    {m n : ℕ}
    (hHdvd : H ∣ X ^ (Nat.card K) ^ m - X)
    (hHsmall : ∀ d : ℕ, d ∣ m → d ≤ n → IsCoprime H (X ^ (Nat.card K) ^ d - X))
    (hD0 : D ≠ 0) (hD : D.natDegree < n)
    (G : K[X]) (hG : G.Monic) (hGdeg : G.natDegree = n) : ¬ G ∣ Ψ := by
  refine not_monic_dvd_of_bigDegreePart hc hfac (fun π hπ hπH => ?_) hD0 hD G hG hGdeg
  by_contra hle
  rw [not_lt] at hle
  have hdmul : π.natDegree ∣ m :=
    hπ.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (hπH.trans hHdvd)
  exact hπ.not_isUnit
    ((hHsmall _ hdmul hle).isUnit_of_dvd' hπH (dvd_X_pow_card_pow_natDegree_sub_X_of_irreducible hπ))

/-- **THE `d = 1` CERTIFICATE IS EXACTLY THE NO-ROOT HYPOTHESIS** (2026-07-31).

`X ^ (#K ^ 1) - X` is the product of the linear factors, so `IsCoprime H (X ^ #K - X)` says
precisely that `H` has no linear factor, i.e. no root.  Proved in the direction that is used —
no root implies coprime — through the degree argument rather than through the product
decomposition, so no `Splits`/`roots` bookkeeping is needed. -/
theorem isCoprime_X_pow_card_sub_X_of_eval_ne_zero {K : Type*} [Field K] [Finite K]
    {H : K[X]} (hHroot : ∀ a : K, H.eval a ≠ 0) :
    IsCoprime H (X ^ (Nat.card K) ^ 1 - X) := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]
  by_contra hu
  have hH0 : H ≠ 0 := fun h => hHroot 0 (by simp [h])
  have hne : EuclideanDomain.gcd H (X ^ (Nat.card K) ^ 1 - X) ≠ 0 := fun h => hH0 (by
    simpa using EuclideanDomain.gcd_eq_zero_iff.mp h |>.1)
  obtain ⟨π, hπ, hπdvd⟩ := WfDvdMonoid.exists_irreducible_factor hu hne
  have hπH : π ∣ H := hπdvd.trans (EuclideanDomain.gcd_dvd_left _ _)
  have hπX : π ∣ X ^ (Nat.card K) ^ 1 - X := hπdvd.trans (EuclideanDomain.gcd_dvd_right _ _)
  have hdeg1 : π.natDegree = 1 :=
    Nat.dvd_one.mp (hπ.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hπX)
  obtain ⟨a, ha⟩ := exists_root_of_degree_eq_one
    (by rw [degree_eq_natDegree hπ.ne_zero, hdeg1]; rfl)
  exact hHroot a (by obtain ⟨t, ht⟩ := hπH; rw [ht, eval_mul, ha, zero_mul])

/-- **THE DEGREE OBSTRUCTION, PRIME-`m` FORM** (PROVEN 2026-07-30; since 2026-07-31 a corollary
of `not_monic_dvd_of_coprimeSmallDegreeParts`, with its statement unchanged).

`hmn` says `1` is the only divisor of `m` that is at most `n`; at `m = 11`, `n = 10` that is
the primality of `11`, and at `m = 34`, `n = 16` it FAILS for `d = 2`, which is why the
`p = 17` and `p = 37` rows must use `not_monic_dvd_of_coprimeSmallDegreeParts` instead.  Under
`hmn` the only small divisor is `d = 1`, and `hHroot` is that instance — which is the content
of `isCoprime_X_pow_card_sub_X_of_eval_ne_zero`, and the reason the general form is a genuine
generalisation and not a different theorem. -/
theorem not_monic_dvd_of_smallDegreePart {K : Type*} [Field K] [Finite K]
    {Ψ D H : K[X]} {c : K} (hc : c ≠ 0) (hfac : Ψ = C c * (D * H))
    {m n : ℕ} (hmn : ∀ d : ℕ, d ∣ m → d ≤ n → d = 1)
    (hHdvd : H ∣ X ^ (Nat.card K) ^ m - X)
    (hHroot : ∀ a : K, H.eval a ≠ 0)
    (hD0 : D ≠ 0) (hD : D.natDegree < n)
    (G : K[X]) (hG : G.Monic) (hGdeg : G.natDegree = n) : ¬ G ∣ Ψ := by
  refine not_monic_dvd_of_coprimeSmallDegreeParts hc hfac hHdvd (fun d hd hle => ?_)
    hD0 hD G hG hGdeg
  rw [hmn d hd hle]
  exact isCoprime_X_pow_card_sub_X_of_eval_ne_zero hHroot

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
