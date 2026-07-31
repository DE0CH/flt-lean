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
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobeniusB
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.ElevenA
public import Fermat.FLT.EllipticCurve.MazurNonCMFrobenius.ElevenB

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

/-- **THE CONVERSE OF `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`** (PROVEN
2026-07-31), which mathlib has in one direction only.

Over a finite field `K` with `q = Nat.card K` elements, an irreducible `f` whose degree divides
`k` divides `X ^ q ^ k - X`.  The proof is the standard one: `AdjoinRoot f` is a field with
`q ^ f.natDegree` elements, so its generator `x` satisfies `x ^ (q ^ f.natDegree) ^ j = x` for
every `j` by `FiniteField.pow_card_pow`; taking `j` with `f.natDegree * j = k` and pushing
through `AdjoinRoot.mk_eq_zero` gives the divisibility.

This is what upgrades the `p = 11` rows' "`H` has no ROOT" to the `p = 17` rows' "`H` has no
irreducible factor of degree `1` or `2`": without it one can only ever exclude degree `1`,
because `exists_root_of_degree_eq_one` is the only handle on a factor that mathlib supplies.
Mathlib-shaped; a candidate for upstreaming next to its converse in
`Mathlib/FieldTheory/Finite/Extension.lean`. -/
theorem irreducible_dvd_X_pow_card_pow_sub_X {K : Type*} [Field K] [Finite K] {f : K[X]}
    (hf : Irreducible f) {k : ℕ} (hk : f.natDegree ∣ k) :
    f ∣ X ^ (Nat.card K) ^ k - X := by
  classical
  haveI : Fact (Irreducible f) := ⟨hf⟩
  haveI hfin : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
  haveI : Finite (AdjoinRoot f) := @Module.finite_of_finite K (AdjoinRoot f) _ _ _ _ hfin
  haveI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  obtain ⟨j, rfl⟩ := hk
  have hcard : Fintype.card (AdjoinRoot f) = Nat.card K ^ f.natDegree := by
    rw [← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot f),
      PowerBasis.finrank (AdjoinRoot.powerBasis hf.ne_zero), AdjoinRoot.powerBasis_dim]
  have hx : (AdjoinRoot.root f) ^ (Nat.card K ^ (f.natDegree * j)) = AdjoinRoot.root f := by
    rw [pow_mul, ← hcard]
    exact FiniteField.pow_card_pow j _
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, hx, sub_self]

/-- **THE DEGREE OBSTRUCTION, GENERAL FORM** (PROVEN 2026-07-31).

`not_monic_dvd_of_smallDegreePart` above is the `k = 1` case, where `IsCoprime H (X ^ q - X)` is
the same thing as "`H` has no root in `K`".  The general `k` is what the `p = 17` rows need:
there `m = 34` and `n = 16`, so the divisors of `m` that are `≤ n` are `1` AND `2`, and a single
coprimality at `k = 2` excludes both at once — `X ^ q - X ∣ X ^ q ^ 2 - X`, so root-freeness is
subsumed rather than an extra hypothesis.

`hmk` says every divisor of `m` that is at most `n` divides `k`; at `m = 11`, `n = 10`, `k = 1`
that is the primality of `11`, and at `m = 34`, `n = 16`, `k = 2` it is the divisor list
`1, 2, 17, 34`.

The proof is the same three steps, with `irreducible_dvd_X_pow_card_pow_sub_X` replacing the
appeal to a root: a common irreducible factor `π` of `G` and `H` has `deg π ∣ m` by
`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X` and `deg π ≤ n` by `natDegree_le_of_dvd`,
hence `deg π ∣ k` by `hmk`, hence `π ∣ X ^ q ^ k - X`, contradicting `hHcop`.  So `IsCoprime G H`,
so `G ∣ C c * D`, so `G ∣ D` since `C c` is a unit; and then `n = deg G ≤ deg D < n`.

This lemma does NOT subsume the `k = 1` one for free: deriving `IsCoprime H (X ^ q - X)` from
root-freeness is a further (easy) argument, and the `p = 11` rows are already proven through the
other statement, so both are kept. -/
theorem not_monic_dvd_of_smallDegreePart' {K : Type*} [Field K] [Finite K]
    {Ψ D H : K[X]} {c : K} (hc : c ≠ 0) (hfac : Ψ = C c * (D * H))
    {m n k : ℕ} (hmk : ∀ d : ℕ, d ∣ m → d ≤ n → d ∣ k)
    (hHdvd : H ∣ X ^ (Nat.card K) ^ m - X)
    (hHcop : IsCoprime H (X ^ (Nat.card K) ^ k - X))
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
    have hdk : π.natDegree ∣ k :=
      hmk _ (hπ.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (hπH.trans hHdvd))
        (hGdeg ▸ natDegree_le_of_dvd hπG hG0)
    exact hπ.not_isUnit
      (hHcop.isUnit_of_dvd' hπH (irreducible_dvd_X_pow_card_pow_sub_X hπ hdk))
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

/-- **`H ∣ X ^ (23 ^ 11) - X`** (PROVEN 2026-07-31), i.e. every irreducible factor of `H` has
degree dividing `11`.  `eval_hPolyElevenA_ne_zero` above is what turns "dividing `11`" into
"equal to `11`" where the obstruction needs it.

The whole content is `Fermat.MazurNonCMFrobenius.dvd_X_pow_sub_X_hPoly`, in its own module
because it is a few thousand lines of generated `ring` identities and elaboration is
single-threaded per file.  `H` is the product of five irreducible polynomials of degree
exactly `11`; the divisibility is proven for each factor separately, through a precomputed
table of `(X ^ 23) ^ i mod hⱼ`, and the five are recombined by explicit Bézout certificates.

The route the original cut proposed — reduce `X ^ (23 ^ k)` mod `H` itself — was tried and is
about `5×` more `ring` work, because it needs a `55`-entry table of degree-`54` polynomials
rather than five `10`-entry tables of degree-`10` ones.

The same route closes the `p = 11`, `j = −24729001` row (same `ℓ`, same degrees) and, with one
extra coprimality at `d = 2`, the two `p = 17` rows.  It does NOT close the `p = 37` rows:
there `deg H = 666`, `ℓ = 397` and `m = 222`. -/
theorem dvd_X_pow_card_pow_sub_X_hPolyElevenA :
    hPolyElevenA ∣ X ^ (Nat.card (ZMod 23)) ^ 11 - X := by
  rw [Nat.card_zmod, hPolyElevenA]
  exact Fermat.MazurNonCMFrobenius.dvd_X_pow_sub_X_hPoly

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

/-! ### The `j = −24729001` row, the other member of isogeny class `121`

Identical in every structural respect to the `j = −121` chain above — same `ℓ = 23`, same
`m = 11`, same `n = 10`, same degree multiset `1⁵, 11⁵` for `Ψ₁₁ mod 23`, so `deg D = 5` and
`deg H = 55` again.  The two curves are the two members of the isogeny class `121`, which is
why the certificate has the same shape; the polynomials themselves are unrelated.

Every number below was produced by re-running mathlib's own `preΨ'` recursion in an
independent Python implementation of `F₂₃[X]`, VALIDATED by reproducing the six `elevenAMod`
values above exactly — those are Lean-verified, so the validation is against the kernel and
not against PARI.  PARI/GP 2.15.4 supplied only the factorisation, and its factors are
multiplied back out and re-checked before use. -/

/-- The minimal model `[1,1,1,-30,-76]` of the `p = 11`, `j = −24729001` row, read over
`ZMod 23`.  Definitionally `Fermat.nonCMModelElevenBmod`. -/
def elevenBMod : WeierstrassCurve (ZMod 23) := ⟨1, 1, 1, -30, -76⟩

/-- The product of the five LINEAR irreducible factors of `Ψ₁₁ mod 23` for `elevenBMod`. -/
noncomputable def dPolyElevenB : (ZMod 23)[X] :=
  X^5 + 14*X^4 + 17*X^3 + 16*X^2 + 21

/-- The product of the five irreducible factors of degree `11` of `Ψ₁₁ mod 23` for
`elevenBMod`. -/
noncomputable def hPolyElevenB : (ZMod 23)[X] :=
  X^55 + 11*X^54 + 9*X^53 + 20*X^52 + X^51 + 13*X^50 + 2*X^49 + 3*X^48 + 2*X^47 + 8*X^46 + 8*X^45 +
    4*X^44 + 9*X^42 + 4*X^41 + 17*X^40 + 22*X^39 + 7*X^38 + 11*X^37 + 20*X^36 + 8*X^34 + 17*X^33 +
    9*X^32 + 16*X^31 + 16*X^30 + 3*X^29 + 18*X^28 + X^27 + 16*X^26 + 4*X^25 + 13*X^24 + 14*X^23 +
    12*X^22 + 20*X^21 + 10*X^20 + 15*X^19 + 7*X^18 + 16*X^17 + 2*X^16 + 9*X^15 + 20*X^14 + 21*X^13 +
    5*X^12 + X^11 + 15*X^10 + 7*X^9 + 22*X^8 + 9*X^7 + 18*X^6 + 2*X^5 + 20*X^4 + 22*X^3 + 22*X^2 +
    6

theorem Ψ₂Sq_elevenBMod : elevenBMod.Ψ₂Sq =
    4*X^3 + 5*X^2 + 20*X + 19 := by
  rw [WeierstrassCurve.Ψ₂Sq]
  simp only [elevenBMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    map_ofNat, C_neg, C_add, C_mul, C_pow, C_1]
  reduce_mod_char

theorem Ψ₃_elevenBMod : elevenBMod.Ψ₃ =
    3*X^4 + 5*X^3 + 7*X^2 + 11*X + 16 := by
  rw [WeierstrassCurve.Ψ₃]
  simp only [elevenBMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_ofNat, C_neg, C_add, C_sub, C_mul, C_pow, C_1]
  reduce_mod_char

theorem preΨ₄_elevenBMod : elevenBMod.preΨ₄ =
    2*X^6 + 5*X^5 + 4*X^4 + 6*X^3 + 22*X^2 + 5*X + 6 := by
  rw [WeierstrassCurve.preΨ₄]
  simp only [elevenBMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_ofNat, C_neg, C_add, C_sub, C_mul, C_pow, C_1]
  reduce_mod_char

theorem preΨ'_five_elevenBMod : elevenBMod.preΨ' 5 =
    5*X^12 + 2*X^11 + 13*X^10 + 5*X^9 + 21*X^8 + 20*X^7 + 8*X^6 + 20*X^5 + 16*X^4 + 4*X^2 +
      10*X + 2 := by
  have h := elevenBMod.preΨ'_odd 0
  norm_num [WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_two] at h
  rw [h, Ψ₃_elevenBMod, preΨ₄_elevenBMod, Ψ₂Sq_elevenBMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_six_elevenBMod : elevenBMod.preΨ' 6 =
    3*X^16 + 20*X^15 + 17*X^14 + 5*X^13 + 2*X^12 + 2*X^11 + 6*X^10 + 16*X^9 + 19*X^8 + 14*X^7 +
    3*X^6 + 20*X^5 + 14*X^4 + 22*X^3 + 11*X^2 + 22*X + 8 := by
  have h := elevenBMod.preΨ'_even 0
  norm_num [WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_two,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_elevenBMod, preΨ₄_elevenBMod, preΨ'_five_elevenBMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_seven_elevenBMod : elevenBMod.preΨ' 7 =
    7*X^24 + X^23 + 13*X^22 + 11*X^21 + 22*X^20 + 11*X^19 + 19*X^18 + 5*X^17 + 2*X^16 + 8*X^15 +
    12*X^14 + 22*X^13 + 22*X^12 + 22*X^11 + 14*X^10 + 22*X^9 + 10*X^8 + X^7 + 8*X^6 + 9*X^5 +
    19*X^4 + 22*X^3 + 15*X^2 + 10*X + 21 := by
  have h := elevenBMod.preΨ'_odd 1
  norm_num [WeierstrassCurve.preΨ'_two, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_elevenBMod, preΨ₄_elevenBMod, preΨ'_five_elevenBMod, Ψ₂Sq_elevenBMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

/-- **`Ψ₁₁ mod 23 = 11 · D · H`** for `elevenBMod` (PROVEN 2026-07-31).  Same shape as
`preΨ'_eleven_elevenAMod`: `preΨ'_odd 3` needs exactly `preΨ' 7`, `preΨ' 5`, `preΨ₄`,
`preΨ' 6` and `Ψ₂Sq`. -/
theorem preΨ'_eleven_elevenBMod :
    elevenBMod.preΨ' 11 = C 11 * (dPolyElevenB * hPolyElevenB) := by
  have h := elevenBMod.preΨ'_odd 3
  norm_num [WeierstrassCurve.preΨ'_four, Nat.even_iff] at h
  rw [h, preΨ₄_elevenBMod, preΨ'_five_elevenBMod, preΨ'_six_elevenBMod,
    preΨ'_seven_elevenBMod, Ψ₂Sq_elevenBMod, dPolyElevenB, hPolyElevenB]
  simp only [map_ofNat]
  reduce_mod_char
  ring_nf
  reduce_mod_char

/-- `H` has no root in `ZMod 23`: it is a product of irreducibles of degree `11`. -/
theorem eval_hPolyElevenB_ne_zero (a : ZMod 23) : hPolyElevenB.eval a ≠ 0 := by
  revert a
  simp only [hPolyElevenB, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  decide

/-- **`H ∣ X ^ (23 ^ 11) - X`** for the `j = −24729001` row (PROVEN 2026-07-31).

The content is `Fermat.MazurNonCMFrobeniusB.dvd_X_pow_sub_X_hPoly`, generated by
`flt-frobenius-cert.py` into its own module for the same reason as the `A` row: elaboration
is single-threaded per file, so the two certificates elaborate in parallel. -/
theorem dvd_X_pow_card_pow_sub_X_hPolyElevenB :
    hPolyElevenB ∣ X ^ (Nat.card (ZMod 23)) ^ 11 - X := by
  rw [Nat.card_zmod, hPolyElevenB]
  exact Fermat.MazurNonCMFrobeniusB.dvd_X_pow_sub_X_hPoly

/-- **Row `p = 11`, `j = −24729001`: `Ψ₁₁ mod 23` has no monic divisor of degree `10`**
(PROVEN 2026-07-31).

This is what `Fermat.not_monic_dvd_preΨ_mod_nonCMModelElevenB` in `X0.lean` consumes. -/
theorem not_monic_dvd_preΨ_elevenB_mod (G : (ZMod 23)[X]) (hG : G.Monic)
    (hdeg : G.natDegree = 10) : ¬ G ∣ elevenBMod.preΨ' 11 := by
  have hp23 : Nat.Prime 23 := by decide
  have hp11 : Nat.Prime 11 := by decide
  have hc : (11 : ZMod 23) ≠ 0 := by decide
  have hmn : ∀ d : ℕ, d ∣ 11 → d ≤ 10 → d = 1 := by
    intro d hd hle
    rcases hp11.eq_one_or_self_of_dvd d hd with h | h
    · exact h
    · omega
  haveI : Fact (Nat.Prime 23) := ⟨hp23⟩
  have hDdeg : dPolyElevenB.natDegree = 5 := by rw [dPolyElevenB]; compute_degree!
  have hD0 : dPolyElevenB ≠ 0 := fun h => by rw [h, natDegree_zero] at hDdeg; omega
  have hDlt : dPolyElevenB.natDegree < 10 := by omega
  exact not_monic_dvd_of_smallDegreePart hc preΨ'_eleven_elevenBMod hmn
    dvd_X_pow_card_pow_sub_X_hPolyElevenB eval_hPolyElevenB_ne_zero hD0 hDlt G hG hdeg

end Fermat.MazurNonCMCertificate

end

-- SCOPE REPAIR, 2026-07-31: the `@[expose] public section` and `namespace` openers below were
-- dropped by the same release-28 merge that damaged `MazurNonCMFrobenius.lean`.  This file is
-- TWO generated documents concatenated — the `p = 11` rows and the `p = 17` rows — and the
-- merge kept only the first one's header, leaving the second block's two `end`s (at the bottom
-- of the file) unmatched and the whole `p = 17` half declared at ROOT level, where
-- `ModularCurve/X0.lean`'s four `MazurNonCMCertificate.not_monic_dvd_preΨ_*_mod` citations
-- cannot see it.  The two `end`s at the bottom are the surviving evidence of what was here.
@[expose] public section

namespace Fermat.MazurNonCMCertificate

/-- The minimal model `[1, 1, 0, -660, -7600]` of the `p = 17`, `j = −882216989/131072` row, read over
`ZMod 67`.  Definitionally `Fermat.nonCMModelSeventeenAmod`. -/
def seventeenAMod : WeierstrassCurve (ZMod 67) := ⟨1, 1, 0, -660, -7600⟩

/-- The product of the four irreducible QUADRATIC factors of `Ψ₁₇ mod 67` on this row. -/
noncomputable def dPolySeventeenA : (ZMod 67)[X] :=
  X^8 + 29*X^7 + 53*X^6 + 21*X^5 + 31*X^4 + 10*X^3 + 17*X^2 + 23*X + 26

theorem Ψ₂Sq_seventeenAMod : seventeenAMod.Ψ₂Sq =
    4*X^3 + 5*X^2 + 40*X + 18 := by
  rw [WeierstrassCurve.Ψ₂Sq]
  simp only [seventeenAMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    map_ofNat, C_neg, C_add, C_mul, C_pow, C_1, C_0]
  reduce_mod_char

theorem Ψ₃_seventeenAMod : seventeenAMod.Ψ₃ =
    3*X^4 + 5*X^3 + 60*X^2 + 54*X + 23 := by
  rw [WeierstrassCurve.Ψ₃]
  simp only [seventeenAMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_ofNat, C_neg, C_add, C_sub, C_mul, C_pow, C_1, C_0]
  reduce_mod_char

theorem preΨ₄_seventeenAMod : seventeenAMod.preΨ₄ =
    2*X^6 + 5*X^5 + 33*X^4 + 46*X^3 + 29*X^2 + 23*X + 2 := by
  rw [WeierstrassCurve.preΨ₄]
  simp only [seventeenAMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_ofNat, C_neg, C_add, C_sub, C_mul, C_pow, C_1, C_0]
  reduce_mod_char

theorem preΨ'_five_seventeenAMod : seventeenAMod.preΨ' 5 =
    5*X^12 + 25*X^11 + 42*X^10 + 30*X^9 + 33*X^8 + 45*X^7 + 4*X^6 + 48*X^5 + 4*X^4 + 63*X^3 + 31*X^2
      + 9*X + 5 := by
  have h := seventeenAMod.preΨ'_odd 0
  norm_num [WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_two] at h
  rw [h, Ψ₃_seventeenAMod, preΨ₄_seventeenAMod, Ψ₂Sq_seventeenAMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_six_seventeenAMod : seventeenAMod.preΨ' 6 =
    3*X^16 + 20*X^15 + 8*X^14 + 2*X^13 + 13*X^12 + 52*X^11 + 20*X^10 + 35*X^9 + 19*X^8 + 33*X^7 +
      17*X^6 + 46*X^5 + 19*X^4 + 27*X^3 + 15*X^2 + 21*X + 23 := by
  have h := seventeenAMod.preΨ'_even 0
  norm_num [WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_two,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_seventeenAMod, preΨ₄_seventeenAMod, preΨ'_five_seventeenAMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_seven_seventeenAMod : seventeenAMod.preΨ' 7 =
    7*X^24 + 3*X^23 + 39*X^22 + 59*X^21 + 40*X^20 + 47*X^19 + 29*X^18 + 64*X^17 + 32*X^16 + 38*X^15
      + 41*X^14 + 53*X^13 + 19*X^12 + 52*X^11 + 47*X^10 + 4*X^9 + 33*X^8 + 33*X^7 + 5*X^6 +
      15*X^5 + 58*X^4 + 35*X^3 + 9*X^2 + 8*X + 20 := by
  have h := seventeenAMod.preΨ'_odd 1
  norm_num [WeierstrassCurve.preΨ'_two, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_seventeenAMod, preΨ₄_seventeenAMod, preΨ'_five_seventeenAMod, Ψ₂Sq_seventeenAMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_eight_seventeenAMod : seventeenAMod.preΨ' 8 =
    4*X^30 + 50*X^29 + 55*X^28 + 16*X^27 + 6*X^26 + 4*X^25 + 62*X^24 + 66*X^23 + 29*X^22 + 27*X^21 +
      43*X^20 + 15*X^19 + X^18 + 35*X^17 + 46*X^16 + 46*X^15 + 41*X^14 + 61*X^13 + 35*X^12 +
      48*X^11 + 52*X^10 + X^9 + 10*X^8 + 41*X^7 + 41*X^6 + 24*X^5 + 33*X^4 + 23*X^3 + 60*X^2 +
      34*X + 30 := by
  have h := seventeenAMod.preΨ'_even 1
  norm_num [WeierstrassCurve.preΨ'_two, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_seventeenAMod, preΨ₄_seventeenAMod, preΨ'_five_seventeenAMod, preΨ'_six_seventeenAMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_nine_seventeenAMod : seventeenAMod.preΨ' 9 =
    9*X^40 + 16*X^39 + 60*X^38 + 34*X^37 + 57*X^36 + 49*X^35 + 13*X^34 + 16*X^33 + 11*X^32 + 63*X^31
      + 59*X^30 + 11*X^29 + 34*X^28 + 32*X^27 + 51*X^26 + 38*X^25 + 24*X^24 + 40*X^23 + 4*X^22 +
      45*X^21 + 56*X^20 + 66*X^19 + 39*X^18 + 61*X^17 + 31*X^16 + 5*X^15 + 50*X^14 + 10*X^13 +
      58*X^12 + 8*X^11 + 31*X^10 + 10*X^9 + 19*X^8 + 6*X^7 + 36*X^6 + 50*X^5 + 41*X^4 + 50*X^3 +
      51*X^2 + 25*X + 59 := by
  have h := seventeenAMod.preΨ'_odd 2
  norm_num [WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four, Nat.even_iff] at h
  rw [h, Ψ₃_seventeenAMod, preΨ₄_seventeenAMod, preΨ'_five_seventeenAMod, preΨ'_six_seventeenAMod,
    Ψ₂Sq_seventeenAMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_ten_seventeenAMod : seventeenAMod.preΨ' 10 =
    5*X^48 + 33*X^47 + 66*X^46 + 4*X^45 + 42*X^44 + 49*X^43 + 6*X^42 + 8*X^41 + 5*X^40 + 9*X^39 +
      27*X^38 + 22*X^37 + 24*X^36 + 51*X^35 + 31*X^34 + 51*X^33 + 48*X^32 + 37*X^31 + 62*X^30 +
      47*X^29 + 17*X^28 + 36*X^27 + 16*X^26 + 25*X^25 + 43*X^23 + 5*X^22 + 41*X^21 + 14*X^20 +
      22*X^19 + 23*X^18 + 45*X^17 + X^16 + 61*X^15 + 34*X^14 + 57*X^13 + 38*X^12 + 44*X^11 +
      52*X^10 + 60*X^9 + 63*X^8 + 29*X^7 + 53*X^6 + 14*X^5 + 58*X^4 + 39*X^3 + 52*X^2 + 15*X +
      66 := by
  have h := seventeenAMod.preΨ'_even 2
  norm_num [WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_seventeenAMod, preΨ₄_seventeenAMod, preΨ'_five_seventeenAMod, preΨ'_six_seventeenAMod,
    preΨ'_seven_seventeenAMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

/-- `preΨ' 8 ^ 2`, precomputed so that the degree-`144` identity below never has to expand a
cube: `ring_nf` on `(31 terms) ^ 3` is `31³` monomial products, on `(61) * (31)` it is `1891`. -/
theorem sq_preΨ'_eight_seventeenAMod : seventeenAMod.preΨ' 8 ^ 2 =
    16*X^60 + 65*X^59 + 59*X^58 + 50*X^56 + 47*X^55 + 3*X^54 + 57*X^53 + 14*X^52 + 13*X^51 + 61*X^50
      + 25*X^49 + 30*X^48 + 19*X^47 + 10*X^46 + X^45 + 6*X^44 + 14*X^43 + 29*X^42 + 55*X^41 +
      62*X^40 + 13*X^39 + 48*X^38 + X^37 + 19*X^36 + 58*X^35 + 48*X^34 + 45*X^33 + 44*X^32 +
      53*X^31 + 41*X^30 + 46*X^29 + 52*X^28 + 5*X^27 + 48*X^26 + 21*X^25 + 39*X^24 + 56*X^23 +
      8*X^22 + 3*X^21 + 60*X^20 + 52*X^19 + 40*X^18 + 28*X^17 + 28*X^16 + 6*X^15 + 36*X^14 +
      10*X^13 + 13*X^12 + 12*X^11 + 42*X^10 + 18*X^9 + 49*X^8 + 65*X^7 + 5*X^6 + 12*X^5 + 42*X^4
      + 33*X^3 + 66*X^2 + 30*X + 29 := by
  rw [preΨ'_eight_seventeenAMod]
  ring_nf
  reduce_mod_char

theorem cube_preΨ'_eight_seventeenAMod : seventeenAMod.preΨ' 8 ^ 3 =
    64*X^90 + 55*X^89 + 11*X^88 + 14*X^87 + 25*X^86 + 66*X^85 + 18*X^84 + 40*X^83 + 6*X^82 + 42*X^81
      + 53*X^80 + 9*X^79 + 44*X^78 + 23*X^77 + 58*X^76 + 44*X^75 + 29*X^74 + 29*X^73 + 48*X^72 +
      47*X^71 + 20*X^70 + 31*X^69 + 50*X^68 + 26*X^67 + 48*X^66 + 5*X^65 + 53*X^64 + 41*X^63 +
      16*X^62 + 56*X^61 + 44*X^60 + 41*X^59 + 25*X^58 + 58*X^57 + 6*X^56 + 13*X^55 + 28*X^54 +
      28*X^53 + 33*X^52 + 24*X^51 + 8*X^50 + 34*X^49 + 9*X^48 + 34*X^47 + 3*X^46 + 19*X^45 +
      12*X^44 + 17*X^43 + 34*X^42 + 28*X^41 + 38*X^40 + 34*X^39 + 44*X^38 + 61*X^37 + 40*X^36 +
      18*X^35 + 35*X^34 + 7*X^33 + 63*X^32 + 3*X^31 + 36*X^30 + 32*X^29 + 2*X^28 + 47*X^27 +
      6*X^26 + 7*X^25 + 39*X^24 + 30*X^23 + 6*X^22 + 21*X^21 + 57*X^20 + 30*X^19 + 21*X^18 +
      21*X^17 + 21*X^16 + 7*X^15 + 37*X^14 + 59*X^13 + 10*X^12 + 30*X^11 + 40*X^10 + 20*X^9 +
      7*X^8 + 54*X^7 + 18*X^6 + 4*X^5 + 16*X^4 + 6*X^3 + 50*X^2 + 10*X + 66 := by
  rw [pow_succ, sq_preΨ'_eight_seventeenAMod, preΨ'_eight_seventeenAMod]
  ring_nf
  reduce_mod_char

theorem sq_preΨ'_nine_seventeenAMod : seventeenAMod.preΨ' 9 ^ 2 =
    14*X^80 + 20*X^79 + 63*X^78 + 53*X^77 + 19*X^76 + 19*X^75 + 16*X^74 + 8*X^73 + 7*X^72 + 27*X^71
      + 56*X^70 + 25*X^69 + 43*X^68 + 61*X^67 + 45*X^66 + 7*X^65 + 10*X^64 + 23*X^63 + 25*X^62 +
      32*X^61 + 40*X^60 + 15*X^59 + 24*X^58 + 25*X^57 + 66*X^56 + 66*X^55 + 47*X^54 + 6*X^53 +
      19*X^52 + 39*X^51 + 28*X^50 + 13*X^49 + 51*X^48 + 42*X^47 + 38*X^46 + 20*X^45 + 59*X^44 +
      56*X^43 + 11*X^42 + 10*X^41 + 17*X^40 + 61*X^39 + 66*X^38 + 38*X^37 + 32*X^36 + 12*X^35 +
      64*X^34 + 12*X^33 + 62*X^32 + 25*X^31 + 26*X^30 + 38*X^29 + 10*X^28 + 61*X^27 + 50*X^26 +
      13*X^24 + 32*X^23 + 23*X^22 + 25*X^21 + 57*X^20 + 10*X^19 + 55*X^18 + 29*X^17 + 53*X^16 +
      8*X^15 + 39*X^14 + 26*X^13 + 53*X^12 + 59*X^11 + 21*X^10 + 57*X^9 + 31*X^8 + 50*X^7 +
      30*X^6 + 52*X^5 + 23*X^4 + 8*X^3 + 10*X^2 + 2*X + 64 := by
  rw [preΨ'_nine_seventeenAMod]
  ring_nf
  reduce_mod_char

theorem cube_preΨ'_nine_seventeenAMod : seventeenAMod.preΨ' 9 ^ 3 =
    59*X^120 + 2*X^119 + 52*X^118 + 12*X^117 + 46*X^116 + 52*X^115 + 36*X^114 + 63*X^113 + 3*X^112 +
      28*X^111 + 42*X^110 + 3*X^109 + 58*X^108 + 38*X^107 + 38*X^106 + 42*X^105 + 40*X^104 +
      10*X^103 + 46*X^102 + 49*X^101 + 66*X^100 + 60*X^99 + 52*X^98 + 29*X^97 + 49*X^96 +
      39*X^95 + 46*X^94 + 12*X^93 + 65*X^92 + 8*X^91 + 61*X^90 + 37*X^89 + 34*X^88 + 61*X^87 +
      42*X^86 + 58*X^85 + 37*X^84 + 4*X^83 + 20*X^82 + 39*X^81 + 30*X^80 + 33*X^79 + 23*X^78 +
      60*X^77 + 24*X^76 + 65*X^75 + 51*X^74 + 24*X^73 + 29*X^72 + 45*X^71 + 31*X^70 + 49*X^69 +
      20*X^68 + 60*X^67 + 58*X^66 + 45*X^65 + 25*X^64 + 54*X^63 + 43*X^62 + 12*X^61 + 57*X^60 +
      39*X^59 + 6*X^58 + 64*X^57 + 61*X^56 + 23*X^55 + 48*X^54 + 45*X^53 + 59*X^52 + 38*X^51 +
      49*X^50 + 31*X^49 + 63*X^48 + 6*X^47 + 40*X^46 + 63*X^45 + 29*X^44 + 5*X^43 + 16*X^42 +
      50*X^41 + 16*X^40 + 28*X^39 + 33*X^38 + 25*X^37 + 31*X^36 + 63*X^35 + 11*X^34 + 4*X^33 +
      24*X^32 + 18*X^31 + 8*X^30 + 21*X^29 + 34*X^28 + 53*X^27 + 37*X^26 + 43*X^25 + 60*X^24 +
      29*X^23 + 54*X^21 + 17*X^20 + 61*X^19 + 38*X^18 + 28*X^17 + 18*X^16 + 18*X^15 + 35*X^14 +
      12*X^13 + 17*X^12 + 42*X^11 + 44*X^10 + 34*X^9 + 23*X^8 + 9*X^7 + 20*X^6 + 61*X^5 + 34*X^4
      + 4*X^3 + 18*X^2 + 43*X + 24 := by
  rw [pow_succ, sq_preΨ'_nine_seventeenAMod, preΨ'_nine_seventeenAMod]
  ring_nf
  reduce_mod_char

/-- **`Ψ₁₇ mod 67 = 17 · D · H`** on this row, the certificate in the form
`not_monic_dvd_of_smallDegreePart'` consumes.  `preΨ'_odd 6` needs exactly `preΨ' 10`,
`preΨ' 8 ^ 3`, `Ψ₂Sq ^ 2`, `preΨ' 7` and `preΨ' 9 ^ 3`; the two cubes are rewritten by the
precomputed lemmas above, never expanded. -/
theorem preΨ'_seventeen_seventeenAMod :
    seventeenAMod.preΨ' 17 = C 17 * (dPolySeventeenA * hPolySeventeenA) := by
  have h := seventeenAMod.preΨ'_odd 6
  norm_num [Nat.even_iff] at h
  rw [h, cube_preΨ'_eight_seventeenAMod, cube_preΨ'_nine_seventeenAMod, preΨ'_ten_seventeenAMod,
    preΨ'_seven_seventeenAMod, Ψ₂Sq_seventeenAMod, dPolySeventeenA, hPolySeventeenA]
  simp only [map_ofNat]
  reduce_mod_char
  ring_nf
  reduce_mod_char

/-- **OPEN LEAF**: every irreducible factor of `H` has degree dividing `34`.

TRUE, machine-checked twice on 2026-07-31 — PARI/GP 2.15.4 (`Mod(x, H) ^ (67 ^ 34) == x`) and
an independent Python reimplementation.  `H` is a product of four irreducibles of degree
exactly `34`.

**THE ROUTE IS FULLY WORKED OUT AND MECHANICAL, AND THE `p = 11` ROWS ARE THE WORKED EXAMPLE.**
`MazurNonCMFrobenius/ElevenA.lean` and `…/ElevenB.lean` are the same statement at `ℓ = 23`,
`m = 11`, and they are PROVEN.  `gen_modules.py` at the repo root emits this row too, from the
same code path, and its output was checked to be mathematically correct.

**WHAT STOPPED IT WAS FILE SIZE, NOT MATHEMATICS.**  The generated `SeventeenA.lean` is 14 287
lines and about 2 500 theorems; elaboration is single-threaded per FILE, and it was still
running after 60 minutes at 47 GB resident when it was stopped.  The `p = 11` rows, 2 390
lines, take 2 minutes each.  The fix is to SPLIT PER FACTOR: `H` has four degree-`34` factors,
each chain is independent, so emit `MazurNonCMFrobenius/SeventeenA/Factor1.lean` … `Factor4.lean`
(≈3 500 lines apiece, elaborating in parallel) and leave only the four Bézout coprimalities,
the product identity and the `xpow_mul` assembly in `SeventeenA.lean`. -/
theorem dvd_X_pow_card_pow_sub_X_hPolySeventeenA :
    hPolySeventeenA ∣ X ^ (Nat.card (ZMod 67)) ^ 34 - X :=
  sorry

/-- **OPEN LEAF**: `H` has no irreducible factor of degree `1` or `2`.
TRUE, machine-checked 2026-07-31: `gcd(H, lift(Mod(x, H) ^ (67 ^ 2)) - x) = 1`.

This single coprimality is what the `p = 17` rows need in place of the `p = 11` rows'
root-freeness: the divisors of `m = 34` that are at most `n = 16` are `1` and `2`, and both
divide `2`.  The generator emits it from the SAME chain — a second, 13-step square-and-multiply
run at the smaller exponent `67 ^ 2`, then one Bézout pair against `r₂ - X`. -/
theorem isCoprime_hPolySeventeenA :
    IsCoprime hPolySeventeenA (X ^ (Nat.card (ZMod 67)) ^ 2 - X) :=
  sorry

/-- **Row `p = 17`, `j = −882216989/131072`: `Ψ₁₇ mod 67` has no monic divisor of degree `16`**
(PROVEN 2026-07-31 over the two computational leaves above).

This is what `Fermat.not_monic_dvd_preΨ_mod_nonCMModelSeventeenA` in `X0.lean` consumes. -/
theorem not_monic_dvd_preΨ_seventeenA_mod (G : (ZMod 67)[X]) (hG : G.Monic)
    (hdeg : G.natDegree = 16) : ¬ G ∣ seventeenAMod.preΨ' 17 := by
  have hc : (17 : ZMod 67) ≠ 0 := by decide
  have hmk : ∀ d : ℕ, d ∣ 34 → d ≤ 16 → d ∣ 2 := by
    intro d hd hle
    interval_cases d <;> revert hd <;> decide
  have hDdeg : dPolySeventeenA.natDegree = 8 := by rw [dPolySeventeenA]; compute_degree!
  have hD0 : dPolySeventeenA ≠ 0 := fun h => by rw [h, natDegree_zero] at hDdeg; omega
  have hDlt : dPolySeventeenA.natDegree < 16 := by omega
  -- `Field (ZMod 67)` — and hence `K := ZMod 67` in the obstruction — needs this.  It must come
  -- AFTER the `decide`s above: with it in scope the numeral `(17 : ZMod 67)` routes through the
  -- local field instance, and `decide` then refuses the free variable.
  haveI : Fact (Nat.Prime 67) := ⟨by decide⟩
  exact not_monic_dvd_of_smallDegreePart' hc preΨ'_seventeen_seventeenAMod hmk
    dvd_X_pow_card_pow_sub_X_hPolySeventeenA isCoprime_hPolySeventeenA hD0 hDlt G hG hdeg

/-! ### The `p = 17`, `j = −297756989/2` row over `ZMod 67`

`Ψ₁₇ mod 67` is squarefree of degree `144` with irreducible-factor degrees `2⁴, 34⁴`
(PARI/GP 2.15.4, 2026-07-31), so `deg D = 8`, `deg H = 136` and `m = 34`.  The divisors of
`34` that are `≤ 16` are `1` and `2`, both dividing `2`, so the single coprimality
`IsCoprime H (X ^ 67 ^ 2 - X)` discharges BOTH — no separate root-freeness statement is
needed.
-/

/-- The minimal model `[1, 0, 1, -3041, 64278]` of the `p = 17`, `j = −297756989/2` row, read over
`ZMod 67`.  Definitionally `Fermat.nonCMModelSeventeenBmod`. -/
def seventeenBMod : WeierstrassCurve (ZMod 67) := ⟨1, 0, 1, -3041, 64278⟩

/-- The product of the four irreducible QUADRATIC factors of `Ψ₁₇ mod 67` on this row. -/
noncomputable def dPolySeventeenB : (ZMod 67)[X] :=
  X^8 + 42*X^7 + 14*X^6 + 11*X^5 + 12*X^4 + 38*X^3 + 42*X^2 + 58*X + 15

theorem Ψ₂Sq_seventeenBMod : seventeenBMod.Ψ₂Sq =
    4*X^3 + X^2 + 32*X + 34 := by
  rw [WeierstrassCurve.Ψ₂Sq]
  simp only [seventeenBMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    map_ofNat, C_neg, C_add, C_mul, C_pow, C_1, C_0]
  reduce_mod_char

theorem Ψ₃_seventeenBMod : seventeenBMod.Ψ₃ =
    3*X^4 + X^3 + 48*X^2 + 35*X + 45 := by
  rw [WeierstrassCurve.Ψ₃]
  simp only [seventeenBMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_ofNat, C_neg, C_add, C_sub, C_mul, C_pow, C_1, C_0]
  reduce_mod_char

theorem preΨ₄_seventeenBMod : seventeenBMod.preΨ₄ =
    2*X^6 + X^5 + 13*X^4 + 5*X^3 + 48*X^2 + 37*X + 33 := by
  rw [WeierstrassCurve.preΨ₄]
  simp only [seventeenBMod, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_ofNat, C_neg, C_add, C_sub, C_mul, C_pow, C_1, C_0]
  reduce_mod_char

theorem preΨ'_five_seventeenBMod : seventeenBMod.preΨ' 5 =
    5*X^12 + 5*X^11 + 28*X^10 + 40*X^9 + 24*X^8 + 2*X^7 + 28*X^6 + 25*X^5 + 58*X^4 + 66*X^3 + 12*X^2
      + 43*X + 20 := by
  have h := seventeenBMod.preΨ'_odd 0
  norm_num [WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_two] at h
  rw [h, Ψ₃_seventeenBMod, preΨ₄_seventeenBMod, Ψ₂Sq_seventeenBMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_six_seventeenBMod : seventeenBMod.preΨ' 6 =
    3*X^16 + 4*X^15 + 41*X^14 + 40*X^13 + 44*X^12 + 32*X^11 + 64*X^10 + 9*X^9 + 27*X^8 + 23*X^6 +
      25*X^5 + 55*X^4 + 38*X^3 + 51*X^2 + 20*X + 1 := by
  have h := seventeenBMod.preΨ'_even 0
  norm_num [WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_two,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_seventeenBMod, preΨ₄_seventeenBMod, preΨ'_five_seventeenBMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_seven_seventeenBMod : seventeenBMod.preΨ' 7 =
    7*X^24 + 14*X^23 + 59*X^22 + 37*X^21 + 61*X^20 + 23*X^19 + 40*X^18 + 53*X^17 + 52*X^16 + 3*X^15
      + 64*X^14 + 14*X^13 + 3*X^12 + 65*X^11 + 64*X^10 + 62*X^9 + 34*X^8 + 41*X^7 + 36*X^6 +
      30*X^5 + 26*X^4 + 17*X^3 + 57*X^2 + 42*X + 10 := by
  have h := seventeenBMod.preΨ'_odd 1
  norm_num [WeierstrassCurve.preΨ'_two, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_seventeenBMod, preΨ₄_seventeenBMod, preΨ'_five_seventeenBMod, Ψ₂Sq_seventeenBMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_eight_seventeenBMod : seventeenBMod.preΨ' 8 =
    4*X^30 + 10*X^29 + 64*X^28 + 59*X^27 + 25*X^26 + 9*X^25 + 58*X^24 + 14*X^23 + 54*X^22 + 3*X^21 +
      58*X^20 + 2*X^19 + 60*X^18 + 15*X^17 + 17*X^16 + 56*X^15 + 65*X^14 + 35*X^13 + 43*X^12 +
      57*X^11 + 40*X^10 + 13*X^9 + 66*X^8 + 25*X^7 + 45*X^6 + 20*X^5 + 44*X^4 + 6*X^3 + 13*X^2 +
      32*X + 25 := by
  have h := seventeenBMod.preΨ'_even 1
  norm_num [WeierstrassCurve.preΨ'_two, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_seventeenBMod, preΨ₄_seventeenBMod, preΨ'_five_seventeenBMod, preΨ'_six_seventeenBMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_nine_seventeenBMod : seventeenBMod.preΨ' 9 =
    9*X^40 + 30*X^39 + 4*X^38 + 24*X^37 + 47*X^36 + 17*X^35 + 35*X^34 + 60*X^33 + 59*X^32 + 49*X^31
      + 16*X^30 + 8*X^29 + 29*X^28 + 48*X^27 + 17*X^26 + 63*X^25 + 18*X^24 + 31*X^23 + 27*X^22 +
      46*X^21 + 58*X^20 + 60*X^19 + 49*X^18 + 25*X^17 + 25*X^16 + 2*X^15 + 8*X^14 + 48*X^13 +
      49*X^12 + 39*X^11 + 61*X^10 + 12*X^9 + 51*X^8 + 36*X^7 + 56*X^6 + 53*X^5 + 18*X^4 + 51*X^3
      + 20*X^2 + 52*X + 14 := by
  have h := seventeenBMod.preΨ'_odd 2
  norm_num [WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four, Nat.even_iff] at h
  rw [h, Ψ₃_seventeenBMod, preΨ₄_seventeenBMod, preΨ'_five_seventeenBMod, preΨ'_six_seventeenBMod,
    Ψ₂Sq_seventeenBMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem preΨ'_ten_seventeenBMod : seventeenBMod.preΨ' 10 =
    5*X^48 + 20*X^47 + 29*X^46 + 34*X^45 + 42*X^44 + 47*X^43 + 53*X^42 + 8*X^41 + 28*X^40 + 45*X^39
      + 20*X^38 + 61*X^37 + 7*X^36 + 34*X^35 + 9*X^34 + 63*X^33 + 41*X^32 + 9*X^31 + X^30 +
      47*X^29 + 55*X^28 + 3*X^27 + 39*X^26 + 25*X^25 + 3*X^24 + 37*X^23 + 31*X^22 + 65*X^21 +
      64*X^20 + 14*X^19 + 15*X^18 + 44*X^16 + 3*X^15 + 4*X^14 + 30*X^13 + 54*X^12 + 17*X^11 +
      45*X^10 + 21*X^9 + 12*X^8 + 14*X^7 + 21*X^6 + 30*X^5 + 36*X^4 + 54*X^3 + 41*X^2 + 10*X +
      21 := by
  have h := seventeenBMod.preΨ'_even 2
  norm_num [WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four] at h
  rw [h, Ψ₃_seventeenBMod, preΨ₄_seventeenBMod, preΨ'_five_seventeenBMod, preΨ'_six_seventeenBMod,
    preΨ'_seven_seventeenBMod]
  reduce_mod_char
  ring_nf
  reduce_mod_char

/-- `preΨ' 8 ^ 2`, precomputed so that the degree-`144` identity below never has to expand a
cube: `ring_nf` on `(31 terms) ^ 3` is `31³` monomial products, on `(61) * (31)` it is `1891`. -/
theorem sq_preΨ'_eight_seventeenBMod : seventeenBMod.preΨ' 8 ^ 2 =
    16*X^60 + 13*X^59 + 9*X^58 + 10*X^57 + 49*X^56 + 17*X^55 + 22*X^54 + 14*X^53 + 41*X^52 + 6*X^51
      + 9*X^50 + 28*X^49 + 8*X^48 + 44*X^47 + 11*X^46 + 62*X^45 + 59*X^44 + 24*X^43 + 30*X^42 +
      54*X^41 + 63*X^40 + 52*X^39 + 46*X^38 + 11*X^37 + 61*X^36 + 12*X^34 + 3*X^33 + 37*X^32 +
      36*X^31 + 13*X^30 + 6*X^29 + 23*X^28 + 39*X^27 + 48*X^26 + 53*X^25 + 20*X^24 + 25*X^23 +
      60*X^22 + 30*X^21 + 5*X^20 + 64*X^19 + 42*X^18 + 32*X^17 + 42*X^16 + 42*X^15 + 8*X^14 +
      36*X^13 + 15*X^12 + 21*X^11 + 29*X^10 + 52*X^9 + 5*X^8 + 19*X^7 + 20*X^6 + 19*X^5 + 6*X^4
      + 60*X^3 + 66*X^2 + 59*X + 22 := by
  rw [preΨ'_eight_seventeenBMod]
  ring_nf
  reduce_mod_char

theorem cube_preΨ'_eight_seventeenBMod : seventeenBMod.preΨ' 8 ^ 3 =
    64*X^90 + 11*X^89 + 51*X^88 + 30*X^87 + 29*X^86 + 54*X^85 + 28*X^84 + 3*X^83 + 37*X^82 + 59*X^81
      + 41*X^80 + 12*X^79 + 51*X^78 + 23*X^76 + 62*X^75 + 56*X^74 + 29*X^73 + 43*X^72 + 29*X^71
      + 9*X^70 + 14*X^69 + 42*X^68 + 53*X^67 + 66*X^66 + 8*X^65 + 61*X^64 + X^63 + 51*X^62 +
      3*X^61 + 61*X^60 + 18*X^59 + 64*X^58 + 27*X^57 + 28*X^56 + 20*X^55 + 38*X^54 + 3*X^53 +
      14*X^52 + 65*X^51 + 16*X^50 + 20*X^49 + 11*X^48 + 48*X^47 + 16*X^46 + 19*X^45 + 57*X^44 +
      44*X^43 + 30*X^42 + 31*X^41 + 47*X^40 + 64*X^39 + 23*X^38 + 15*X^37 + 8*X^36 + 26*X^35 +
      42*X^34 + 12*X^33 + X^32 + 15*X^31 + 23*X^30 + 48*X^29 + 60*X^28 + 11*X^27 + 15*X^26 +
      22*X^25 + 56*X^24 + 64*X^23 + 42*X^22 + 10*X^21 + 4*X^20 + 57*X^19 + 65*X^18 + 4*X^17 +
      23*X^16 + 48*X^15 + 35*X^14 + 23*X^13 + 44*X^12 + 35*X^11 + 10*X^10 + 57*X^9 + 26*X^8 +
      54*X^7 + 54*X^6 + 55*X^5 + 29*X^4 + 22*X^3 + 5*X^2 + 35*X + 14 := by
  rw [pow_succ, sq_preΨ'_eight_seventeenBMod, preΨ'_eight_seventeenBMod]
  ring_nf
  reduce_mod_char

theorem sq_preΨ'_nine_seventeenBMod : seventeenBMod.preΨ' 9 ^ 2 =
    14*X^80 + 4*X^79 + 34*X^78 + 2*X^77 + 24*X^76 + 35*X^75 + 56*X^74 + 11*X^73 + 61*X^72 + 6*X^71 +
      42*X^70 + 36*X^69 + 32*X^68 + 44*X^67 + 29*X^66 + 58*X^65 + 57*X^64 + 35*X^63 + 10*X^62 +
      49*X^61 + 51*X^60 + 38*X^59 + 66*X^58 + 57*X^57 + 25*X^56 + 45*X^55 + 44*X^54 + 15*X^53 +
      57*X^52 + 48*X^51 + 40*X^50 + 12*X^49 + 6*X^47 + 41*X^46 + 51*X^45 + 39*X^44 + X^43 +
      53*X^42 + 7*X^41 + 59*X^40 + 42*X^39 + 8*X^38 + 13*X^37 + 21*X^36 + 61*X^35 + 63*X^34 +
      33*X^33 + 43*X^32 + 11*X^31 + 18*X^30 + 2*X^29 + 32*X^28 + 65*X^27 + 3*X^26 + 33*X^25 +
      48*X^24 + 27*X^23 + 52*X^22 + 16*X^21 + 23*X^20 + 65*X^19 + 22*X^18 + 64*X^17 + 8*X^16 +
      56*X^15 + 56*X^14 + 39*X^13 + 58*X^12 + 49*X^11 + 26*X^10 + 27*X^9 + 10*X^8 + X^7 + 16*X^6
      + 36*X^5 + 44*X^4 + 24*X^3 + 48*X^2 + 49*X + 62 := by
  rw [preΨ'_nine_seventeenBMod]
  ring_nf
  reduce_mod_char

theorem cube_preΨ'_nine_seventeenBMod : seventeenBMod.preΨ' 9 ^ 3 =
    59*X^120 + 54*X^119 + 13*X^118 + 50*X^117 + 27*X^116 + 7*X^115 + 35*X^114 + 60*X^113 + X^112 +
      49*X^111 + 41*X^110 + 54*X^109 + 34*X^108 + 46*X^107 + 8*X^106 + 54*X^105 + 20*X^104 +
      4*X^103 + 55*X^102 + 14*X^101 + 52*X^100 + 60*X^99 + 39*X^98 + 62*X^97 + 11*X^96 + 28*X^95
      + 14*X^94 + 18*X^93 + 3*X^92 + 15*X^91 + 51*X^90 + 3*X^89 + 33*X^88 + 53*X^87 + 32*X^86 +
      25*X^85 + 27*X^84 + 58*X^83 + 59*X^82 + 33*X^81 + 30*X^80 + 7*X^79 + 7*X^78 + 46*X^77 +
      44*X^76 + 20*X^75 + 34*X^74 + 20*X^73 + 36*X^72 + 14*X^71 + 54*X^70 + 24*X^69 + 33*X^68 +
      8*X^67 + 55*X^66 + 46*X^65 + 63*X^64 + 30*X^63 + 33*X^62 + 42*X^61 + 63*X^60 + 21*X^59 +
      38*X^58 + 54*X^57 + 8*X^56 + 19*X^55 + 47*X^54 + 40*X^53 + 21*X^52 + 33*X^51 + 4*X^50 +
      26*X^49 + 6*X^48 + 66*X^47 + 8*X^46 + 52*X^45 + 50*X^44 + 3*X^43 + 22*X^41 + 5*X^40 +
      42*X^39 + 49*X^38 + 58*X^37 + 51*X^36 + 66*X^35 + 47*X^34 + 17*X^33 + 33*X^32 + 40*X^31 +
      60*X^30 + 64*X^29 + 53*X^28 + 4*X^27 + 24*X^26 + 30*X^25 + 39*X^24 + 6*X^23 + 48*X^22 +
      31*X^21 + 7*X^20 + 23*X^19 + 20*X^18 + 23*X^17 + 9*X^16 + 19*X^15 + 6*X^14 + 34*X^13 +
      X^12 + 21*X^11 + 23*X^10 + 41*X^9 + 33*X^8 + 37*X^7 + 11*X^6 + 39*X^5 + 7*X^4 + 6*X^3 +
      38*X^2 + 24*X + 64 := by
  rw [pow_succ, sq_preΨ'_nine_seventeenBMod, preΨ'_nine_seventeenBMod]
  ring_nf
  reduce_mod_char

/-- **`Ψ₁₇ mod 67 = 17 · D · H`** on this row, the certificate in the form
`not_monic_dvd_of_smallDegreePart'` consumes.  `preΨ'_odd 6` needs exactly `preΨ' 10`,
`preΨ' 8 ^ 3`, `Ψ₂Sq ^ 2`, `preΨ' 7` and `preΨ' 9 ^ 3`; the two cubes are rewritten by the
precomputed lemmas above, never expanded. -/
theorem preΨ'_seventeen_seventeenBMod :
    seventeenBMod.preΨ' 17 = C 17 * (dPolySeventeenB * hPolySeventeenB) := by
  have h := seventeenBMod.preΨ'_odd 6
  norm_num [Nat.even_iff] at h
  rw [h, cube_preΨ'_eight_seventeenBMod, cube_preΨ'_nine_seventeenBMod, preΨ'_ten_seventeenBMod,
    preΨ'_seven_seventeenBMod, Ψ₂Sq_seventeenBMod, dPolySeventeenB, hPolySeventeenB]
  simp only [map_ofNat]
  reduce_mod_char
  ring_nf
  reduce_mod_char

/-- **OPEN LEAF**: every irreducible factor of `H` has degree dividing `34`.
TRUE, machine-checked 2026-07-31 in PARI/GP and in Python.  Word for word
`dvd_X_pow_card_pow_sub_X_hPolySeventeenA` with a different `H`; see that docstring for the
route, the worked `p = 11` example, and why the generated module has to be split per factor. -/
theorem dvd_X_pow_card_pow_sub_X_hPolySeventeenB :
    hPolySeventeenB ∣ X ^ (Nat.card (ZMod 67)) ^ 34 - X :=
  sorry

/-- **OPEN LEAF**: `H` has no irreducible factor of degree `1` or `2`.
TRUE, machine-checked 2026-07-31.  See `isCoprime_hPolySeventeenA`. -/
theorem isCoprime_hPolySeventeenB :
    IsCoprime hPolySeventeenB (X ^ (Nat.card (ZMod 67)) ^ 2 - X) :=
  sorry

/-- **Row `p = 17`, `j = −297756989/2`: `Ψ₁₇ mod 67` has no monic divisor of degree `16`**
(PROVEN 2026-07-31 over the two computational leaves above).

This is what `Fermat.not_monic_dvd_preΨ_mod_nonCMModelSeventeenB` in `X0.lean` consumes. -/
theorem not_monic_dvd_preΨ_seventeenB_mod (G : (ZMod 67)[X]) (hG : G.Monic)
    (hdeg : G.natDegree = 16) : ¬ G ∣ seventeenBMod.preΨ' 17 := by
  have hc : (17 : ZMod 67) ≠ 0 := by decide
  have hmk : ∀ d : ℕ, d ∣ 34 → d ≤ 16 → d ∣ 2 := by
    intro d hd hle
    interval_cases d <;> revert hd <;> decide
  have hDdeg : dPolySeventeenB.natDegree = 8 := by rw [dPolySeventeenB]; compute_degree!
  have hD0 : dPolySeventeenB ≠ 0 := fun h => by rw [h, natDegree_zero] at hDdeg; omega
  have hDlt : dPolySeventeenB.natDegree < 16 := by omega
  -- See `not_monic_dvd_preΨ_seventeenA_mod` for why this `haveI` must come last.
  haveI : Fact (Nat.Prime 67) := ⟨by decide⟩
  exact not_monic_dvd_of_smallDegreePart' hc preΨ'_seventeen_seventeenBMod hmk
    dvd_X_pow_card_pow_sub_X_hPolySeventeenB isCoprime_hPolySeventeenB hD0 hDlt G hG hdeg

end Fermat.MazurNonCMCertificate

end
