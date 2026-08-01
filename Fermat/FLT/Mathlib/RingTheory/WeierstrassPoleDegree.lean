/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.BigOperators.Fin

/-!
# From a genus-one pole filtration to a Weierstrass presentation

This module contains the **purely algebraic half of Silverman *AEC* III.3.1**: the passage
from the Riemann–Roch dimension count `dim_k L(n·[O]) = n` to an actual Weierstrass
equation together with the statement that its two coordinates generate the ring.

Nothing here is Riemann–Roch, nothing here is geometry, and nothing here mentions a
scheme.  The input is one function `d : R → ℕ` — the order of the pole at the single
point at infinity — subject to four axioms, plus the dimension count.  The output is a
`WeierstrassCurve k`, two elements `x y : R` satisfying its affine equation, and the
generation clause `Subring.closure (Set.range (algebraMap k R) ∪ {x, y}) = ⊤`.

## Why the cut is here

`Fermat/FLT/ModularCurve/X1.lean`'s `exists_weierstrassGenerators_of_abelianSchemeChart`
was a single opaque leaf carrying the whole of III.3.1.  Its docstring named the argument
correctly and the argument has two completely separate halves:

* the **analytic/geometric** half — a group scheme has trivial relative tangent bundle,
  hence arithmetic genus one, hence `dim_k L(n·[O]) = n` for `n ≥ 1`.  That is the real
  Riemann–Roch content and it stays a leaf;
* the **linear-algebra** half — everything after the dimension count.  That is this file,
  and it is PROVEN here with no `sorry`.

Splitting them means the Riemann–Roch prover never has to look at a Weierstrass equation,
and nobody ever has to redo the (fiddly, and entirely elementary) coefficient chase.

## The axioms, and why they are the right ones

`IsPoleDegree k R d` asks exactly for what the pole order at a rational point of a curve
satisfies, with the junk convention `d 0 = 0`:

* `map_mul` — `ord_O` is a valuation, so pole orders ADD on products.  This is what makes
  monomials in `x` and `y` have the pole orders the argument needs, and it is the clause
  that a mere filtration `L(0) ⊆ L(1) ⊆ ⋯` does not supply;
* `add_le` — the ultrametric inequality;
* `eq_zero_iff` — `L(0) = H⁰(A, 𝒪_A) = k`, i.e. a function regular everywhere is
  constant.  This is where PROPERNESS and geometric connectedness of the curve are spent.

`IsDomain R` is deliberately NOT assumed: it is a CONSEQUENCE of the axioms together with
`Nontrivial R` (see `IsPoleDegree.smul_eq_of_ne` and the `x ^ j ≠ 0` induction inside the
main proof), and asking for it would make the leaf above harder for no gain.

## THE COUNTEREXAMPLE THAT FIXES THE SCOPE OF THIS FILE — why `Δ ≠ 0` is NOT here

The axioms below do **not** imply that the Weierstrass curve produced is nonsingular, and
this is not a defect of the packaging: the coordinate ring of the CUSPIDAL cubic
`y² = x³`, namely `k[t², t³] ⊆ k[t]`, satisfies every clause of `IsPoleDegree` (with
`d(t^m) = m`) and has `dim_k L(n) = #{m ≤ n : m ≠ 1} = n` for every `n ≥ 1`.  So a
singular Weierstrass curve has exactly the same pole filtration as a smooth one — the
arithmetic genus of a nodal or cuspidal plane cubic is also one — and no argument from
`d` alone can separate them.

What separates them is NORMALITY: `k[t², t³]` is not integrally closed, whereas the ring
of functions on a SMOOTH affine curve is.  That is geometry rather than linear algebra, so
`W.IsElliptic` is left to its own leaf next to the Riemann–Roch one; see
`Fermat.isElliptic_of_weierstrassGenerators_of_abelianSchemeChart` in `X1.lean`.

## Contents

* `Fermat.IsPoleDegree` — the four axioms;
* `Fermat.poleSubmodule` — `L(n) = {r | d r ≤ n}` as a `k`-submodule of `R`;
* `Fermat.exists_weierstrassGenerators_of_isPoleDegree` — the main theorem, PROVEN.

## References

Silverman, *The Arithmetic of Elliptic Curves*, Proposition III.3.1.
-/

@[expose] public section

universe u v

namespace Fermat

variable {k : Type u} [Field k] {R : Type v} [CommRing R] [Algebra k R] {d : R → ℕ}

/-- **The order of the pole at one rational point**, axiomatised.

`d r` is the order of the pole of the regular function `r` at the single point `O` that
was removed from a proper curve to obtain `Spec R`.  The junk value at `0` is `0`.

See the module docstring for why these four clauses and no others, and in particular for
the cuspidal-cubic witness showing that they do NOT pin the curve up to isomorphism. -/
structure IsPoleDegree (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]
    (d : R → ℕ) : Prop where
  /-- The junk convention at `0`. -/
  map_zero : d 0 = 0
  /-- Pole orders add on products: `ord_O` is a valuation. -/
  map_mul : ∀ r s : R, r ≠ 0 → s ≠ 0 → d (r * s) = d r + d s
  /-- The ultrametric inequality. -/
  add_le : ∀ r s : R, d (r + s) ≤ max (d r) (d s)
  /-- `L(0) = k`: a function with no pole anywhere is constant.  This is where properness
  and geometric connectedness of the ambient curve are spent. -/
  eq_zero_iff : ∀ r : R, r ≠ 0 → (d r = 0 ↔ ∃ c : k, algebraMap k R c = r)

namespace IsPoleDegree

/-- Scaling by a nonzero constant does not change the pole order. -/
lemma smul_eq_of_ne (h : IsPoleDegree k R d) {c : k} (hc : c ≠ 0) (r : R) :
    d (c • r) = d r := by
  -- one inequality, applied twice: to `c` and to `c⁻¹`.
  have key : ∀ (a : k), a ≠ 0 → ∀ s : R, d (a • s) ≤ d s := by
    intro a ha s
    rcases eq_or_ne s 0 with rfl | hs
    · simp [h.map_zero]
    · haveI : Nontrivial R := ⟨⟨s, 0, hs⟩⟩
      have hane : algebraMap k R a ≠ 0 := by
        simpa using fun hh => ha ((algebraMap k R).injective (by simpa using hh))
      have h0 : d (algebraMap k R a) = 0 :=
        (h.eq_zero_iff _ hane).2 ⟨a, rfl⟩
      rw [Algebra.smul_def, h.map_mul _ _ hane hs, h0, zero_add]
  refine le_antisymm (key c hc r) ?_
  calc d r = d (c⁻¹ • c • r) := by rw [inv_smul_smul₀ hc]
    _ ≤ d (c • r) := key c⁻¹ (inv_ne_zero hc) _

/-- Scaling by any constant does not increase the pole order. -/
lemma smul_le (h : IsPoleDegree k R d) (c : k) (r : R) : d (c • r) ≤ d r := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [h.map_zero]
  · exact (h.smul_eq_of_ne hc r).le

/-- Multiplying by a constant does not increase the pole order. -/
lemma algebraMap_mul_le (h : IsPoleDegree k R d) (c : k) (r : R) :
    d (algebraMap k R c * r) ≤ d r := by
  rw [← Algebra.smul_def]; exact h.smul_le c r

/-- Multiplying by a NONZERO constant does not change the pole order. -/
lemma algebraMap_mul_eq (h : IsPoleDegree k R d) {c : k} (hc : c ≠ 0) (r : R) :
    d (algebraMap k R c * r) = d r := by
  rw [← Algebra.smul_def]; exact h.smul_eq_of_ne hc r

/-- Negation does not change the pole order. -/
lemma neg (h : IsPoleDegree k R d) (r : R) : d (-r) = d r := by
  have : (-1 : k) • r = -r := by simp
  rw [← this, h.smul_eq_of_ne (by simp) r]

/-- The ultrametric inequality against a common bound. -/
lemma add_le' (h : IsPoleDegree k R d) {r s : R} {n : ℕ} (hr : d r ≤ n) (hs : d s ≤ n) :
    d (r + s) ≤ n :=
  (h.add_le r s).trans (max_le hr hs)

/-- `d 1 = 0`. -/
lemma map_one (h : IsPoleDegree k R d) [Nontrivial R] : d (1 : R) = 0 :=
  (h.eq_zero_iff 1 one_ne_zero).2 ⟨1, _root_.map_one _⟩

/-- **THE LEADING-TERM PRINCIPLE.**  If `c • u` is cancelled by something of strictly
smaller pole order then `c = 0`.  This single lemma is what proves every linear
independence in this file. -/
lemma eq_zero_of_algebraMap_mul_add (h : IsPoleDegree k R d) {c : k} {u w : R} {m n : ℕ}
    (hu : d u = n) (hw : d w ≤ m) (hmn : m < n)
    (heq : algebraMap k R c * u + w = 0) : c = 0 := by
  by_contra hc
  have h1 : algebraMap k R c * u = -w := by linear_combination heq
  have h2 : d (algebraMap k R c * u) = n := by rw [h.algebraMap_mul_eq hc u, hu]
  rw [h1, h.neg w] at h2
  omega

end IsPoleDegree

/-- **`L(n) = {r ∈ R | d r ≤ n}`**, the space of functions with a pole of order at most
`n` at the point at infinity, as a `k`-submodule of `R`. -/
def poleSubmodule (h : IsPoleDegree k R d) (n : ℕ) : Submodule k R where
  carrier := {r : R | d r ≤ n}
  add_mem' := fun hr hs => h.add_le' hr hs
  zero_mem' := by simp [h.map_zero]
  smul_mem' := fun c _ hr => (h.smul_le c _).trans hr

@[simp] lemma mem_poleSubmodule {h : IsPoleDegree k R d} {n : ℕ} {r : R} :
    r ∈ poleSubmodule h n ↔ d r ≤ n := Iff.rfl

lemma poleSubmodule_mono (h : IsPoleDegree k R d) {m n : ℕ} (hmn : m ≤ n) :
    poleSubmodule h m ≤ poleSubmodule h n := fun _ hr => le_trans hr hmn

/-! ## The dimension count, and the two consequences everything below is built from -/

section Rank

variable (h : IsPoleDegree k R d)
  (hfd : ∀ n : ℕ, Module.Finite k (poleSubmodule h n))
  (hrank : ∀ n : ℕ, 1 ≤ n → Module.finrank k (poleSubmodule h n) = n)

include h hrank in
/-- **There is a function with a pole of order exactly `n`, for every `n ≥ 2`.**

If there were none then `L(n) = L(n−1)`, and the two have different dimensions.  Note the
bound `2 ≤ n` is sharp and not a technicality: there is NO function of pole order exactly
`1` — that is the Weierstrass gap, and it is why the curve is a plane CUBIC. -/
lemma exists_poleDegree_eq {n : ℕ} (hn : 2 ≤ n) : ∃ r : R, d r = n := by
  by_contra hc
  push Not at hc
  have hEq : poleSubmodule h n = poleSubmodule h (n - 1) := by
    refine le_antisymm (fun r hr => ?_) (poleSubmodule_mono h (by omega))
    have hne := hc r
    simp only [mem_poleSubmodule] at hr ⊢
    omega
  have h1 := hrank n (by omega)
  rw [hEq, hrank (n - 1) (by omega)] at h1
  omega

include h hfd hrank in
/-- **`L(1) = k`**: there is no function of pole order exactly one.

`L(0)` is the line spanned by `1` (a function with no pole at all is constant, by
`eq_zero_iff`), and `dim L(1) = 1` forces `L(1)` to be that same line. -/
lemma poleSubmodule_one_eq_span_one [Nontrivial R] :
    poleSubmodule h 1 = Submodule.span k {(1 : R)} := by
  have hspan : poleSubmodule h 0 = Submodule.span k {(1 : R)} := by
    refine le_antisymm (fun r hr => ?_) ?_
    · simp only [mem_poleSubmodule, Nat.le_zero] at hr
      rcases eq_or_ne r 0 with rfl | hr0
      · exact Submodule.zero_mem _
      · obtain ⟨c, hc⟩ := (h.eq_zero_iff r hr0).1 hr
        rw [← hc, Submodule.mem_span_singleton]
        exact ⟨c, by rw [Algebra.smul_def, mul_one]⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      simp [h.map_one]
  haveI := hfd 1
  have hEq : poleSubmodule h 0 = poleSubmodule h 1 :=
    Submodule.eq_of_le_of_finrank_le (poleSubmodule_mono h (Nat.zero_le 1))
      (by rw [hrank 1 le_rfl, hspan, finrank_span_singleton (one_ne_zero : (1 : R) ≠ 0)])
  rw [← hEq, hspan]

include h hfd hrank in
/-- **THE ONE-DIMENSIONAL JUMP.**  `L(n+1) = L(n) ⊕ k·m` for ANY `m` of pole order exactly
`n+1`.

This single lemma does all the work below: iterating it downwards writes every element of
`L(5)` in the monomial basis `1, x, y, x², xy`, and one further step at `n+1 = 6` produces
the Weierstrass relation.  It replaces the linear-independence argument of the classical
account — the dimensions already know that the monomials are independent. -/
lemma poleSubmodule_succ_eq {n : ℕ} (hn : 1 ≤ n) {m : R} (hmd : d m = n + 1) :
    poleSubmodule h (n + 1) = poleSubmodule h n ⊔ Submodule.span k {m} := by
  haveI := hfd (n + 1)
  have hle : poleSubmodule h n ⊔ Submodule.span k {m} ≤ poleSubmodule h (n + 1) := by
    refine sup_le (poleSubmodule_mono h (by omega)) ?_
    rw [Submodule.span_le, Set.singleton_subset_iff]
    simp [hmd]
  haveI : Module.Finite k (poleSubmodule h n ⊔ Submodule.span k {m} : Submodule k R) :=
    Submodule.finiteDimensional_of_le hle
  have hlt : poleSubmodule h n < poleSubmodule h n ⊔ Submodule.span k {m} := by
    refine lt_of_le_of_ne le_sup_left fun hcon => ?_
    have hmem : m ∈ poleSubmodule h n :=
      hcon ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self m)
    simp only [mem_poleSubmodule, hmd] at hmem
    omega
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hrank n hn] at h1
  exact (Submodule.eq_of_le_of_finrank_le hle
    (by rw [hrank (n + 1) (by omega)]; omega)).symm

include h hfd hrank in
/-- **`x` AND `y` GENERATE.**  Any subring containing the constants and two elements of
pole orders `2` and `3` is all of `R`.

Induction on the pole order.  The monomials `x^j` and `x^j·y` realise every pole order
except `1`, and `poleSubmodule_succ_eq` says that adjoining any one element of pole order
`n+1` to `L(n)` gives `L(n+1)` — so a function of pole order `n` differs from a constant
multiple of the standard monomial by something of strictly smaller pole order. -/
lemma mem_of_isPoleDegree [Nontrivial R] {x y : R} (hx : d x = 2) (hy : d y = 3)
    {S : Subring R} (hA : ∀ c : k, algebraMap k R c ∈ S) (hxS : x ∈ S) (hyS : y ∈ S)
    (r : R) : r ∈ S := by
  have hxne : x ≠ 0 := fun hh => by rw [hh, h.map_zero] at hx; omega
  have hyne : y ≠ 0 := fun hh => by rw [hh, h.map_zero] at hy; omega
  have hxp : ∀ j : ℕ, x ^ j ≠ 0 ∧ d (x ^ j) = 2 * j := by
    intro j
    induction j with
    | zero => exact ⟨by simp, by simpa using h.map_one⟩
    | succ j ih =>
      have hd : d (x ^ (j + 1)) = 2 * (j + 1) := by
        rw [pow_succ, h.map_mul _ _ ih.1 hxne, ih.2, hx]; ring
      exact ⟨fun hh => by rw [hh, h.map_zero] at hd; omega, hd⟩
  have hxy : ∀ j : ℕ, d (x ^ j * y) = 2 * j + 3 := fun j => by
    rw [h.map_mul _ _ (hxp j).1 hyne, (hxp j).2, hy]
  -- a monomial of every pole order `≥ 2`, lying in `S`
  have hmono : ∀ n : ℕ, 2 ≤ n → ∃ m : R, d m = n ∧ m ∈ S := by
    intro n hn
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨x ^ j, by rw [(hxp j).2]; omega, Subring.pow_mem _ hxS j⟩
    · exact ⟨x ^ (j - 1) * y, by rw [hxy]; omega,
        Subring.mul_mem _ (Subring.pow_mem _ hxS _) hyS⟩
  suffices hkey : ∀ n : ℕ, ∀ s : R, d s ≤ n → s ∈ S from hkey (d r) r le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro s hs
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have h1 : s ∈ poleSubmodule h 1 := by simp only [mem_poleSubmodule]; omega
      rw [poleSubmodule_one_eq_span_one h hfd hrank, Submodule.mem_span_singleton] at h1
      obtain ⟨c, rfl⟩ := h1
      rw [Algebra.smul_def, mul_one]
      exact hA c
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m, hmd, hmS⟩ := hmono (p + 1) (by omega)
      have hmem : s ∈ poleSubmodule h (p + 1) := hs
      rw [poleSubmodule_succ_eq h hfd hrank (by omega) hmd] at hmem
      obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 hmem
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      refine Subring.add_mem _ (IH p (by omega) w hw) ?_
      rw [Algebra.smul_def]
      exact Subring.mul_mem _ (hA c) hmS

include h hfd hrank in
/-- **SILVERMAN *AEC* III.3.1, THE ALGEBRAIC HALF: a genus-one pole filtration produces a
Weierstrass presentation.**  PROVEN, no `sorry`.

`x` has pole order `2` and `y` pole order `3` (they exist because `dim L(2) > dim L(1)`
and `dim L(3) > dim L(2)`).  Then `1, x, y, x², xy` exhaust `L(5)` and `x³` completes them
to `L(6)`, so `y² ∈ L(6)` is a `k`-combination of the six — with the coefficient of `x³`
nonzero, since `y² ∉ L(5)`.  Rescaling `x, y` by that coefficient turns the combination
into a Weierstrass equation, and the generation clause is `mem_of_isPoleDegree`.

The curve produced need NOT be nonsingular; see the module docstring for the cuspidal
witness, and note that no hypothesis here could rule it out. -/
theorem exists_weierstrassGenerators_of_isPoleDegree :
    ∃ (W : WeierstrassCurve k) (x y : R),
      y ^ 2 + (algebraMap k R W.a₁ * x + algebraMap k R W.a₃) * y
          = x ^ 3 + algebraMap k R W.a₂ * x ^ 2 + algebraMap k R W.a₄ * x
            + algebraMap k R W.a₆ ∧
        Subring.closure (Set.range (algebraMap k R) ∪ {x, y}) = ⊤ := by
  haveI : Nontrivial R := by
    by_contra hcon
    haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hcon
    have hbot : poleSubmodule h 1 = ⊥ := by
      refine le_antisymm (fun r _ => ?_) bot_le
      simpa using Subsingleton.elim r 0
    have h1 := hrank 1 le_rfl
    rw [hbot, finrank_bot] at h1
    omega
  obtain ⟨x, hx⟩ := exists_poleDegree_eq h hrank (n := 2) le_rfl
  obtain ⟨y, hy⟩ := exists_poleDegree_eq h hrank (n := 3) (by omega)
  have hxne : x ≠ 0 := fun hh => by rw [hh, h.map_zero] at hx; omega
  have hyne : y ≠ 0 := fun hh => by rw [hh, h.map_zero] at hy; omega
  have hdx2 : d (x ^ 2) = 4 := by rw [pow_two, h.map_mul _ _ hxne hxne, hx]
  have hx2ne : x ^ 2 ≠ 0 := fun hh => by rw [hh, h.map_zero] at hdx2; omega
  have hdx3 : d (x ^ 3) = 6 := by
    rw [show x ^ 3 = x ^ 2 * x by ring, h.map_mul _ _ hx2ne hxne, hdx2, hx]
  have hdxy : d (x * y) = 5 := by rw [h.map_mul _ _ hxne hyne, hx, hy]
  have hdy2 : d (y ^ 2) = 6 := by rw [pow_two, h.map_mul _ _ hyne hyne, hy]
  -- the tower of one-dimensional jumps, `L(1) ⊂ L(2) ⊂ ⋯ ⊂ L(6)`
  have e1 : poleSubmodule h 1 = Submodule.span k {(1 : R)} :=
    poleSubmodule_one_eq_span_one h hfd hrank
  have e2 : poleSubmodule h 2 = poleSubmodule h 1 ⊔ Submodule.span k {x} :=
    poleSubmodule_succ_eq h hfd hrank (n := 1) le_rfl hx
  have e3 : poleSubmodule h 3 = poleSubmodule h 2 ⊔ Submodule.span k {y} :=
    poleSubmodule_succ_eq h hfd hrank (n := 2) (by omega) hy
  have e4 : poleSubmodule h 4 = poleSubmodule h 3 ⊔ Submodule.span k {x ^ 2} :=
    poleSubmodule_succ_eq h hfd hrank (n := 3) (by omega) hdx2
  have e5 : poleSubmodule h 5 = poleSubmodule h 4 ⊔ Submodule.span k {x * y} :=
    poleSubmodule_succ_eq h hfd hrank (n := 4) (by omega) hdxy
  have e6 : poleSubmodule h 6 = poleSubmodule h 5 ⊔ Submodule.span k {x ^ 3} :=
    poleSubmodule_succ_eq h hfd hrank (n := 5) (by omega) hdx3
  -- every element of `L(5)` in the monomial basis `1, x, y, x², xy`
  have hL5 : ∀ r : R, r ∈ poleSubmodule h 5 → ∃ c0 c1 c2 c3 c4 : k,
      r = algebraMap k R c0 + algebraMap k R c1 * x + algebraMap k R c2 * y
        + algebraMap k R c3 * x ^ 2 + algebraMap k R c4 * (x * y) := by
    intro r hr
    rw [e5] at hr
    obtain ⟨r4, hr4, z4, hz4, rfl⟩ := Submodule.mem_sup.1 hr
    obtain ⟨c4, rfl⟩ := Submodule.mem_span_singleton.1 hz4
    rw [e4] at hr4
    obtain ⟨r3, hr3, z3, hz3, rfl⟩ := Submodule.mem_sup.1 hr4
    obtain ⟨c3, rfl⟩ := Submodule.mem_span_singleton.1 hz3
    rw [e3] at hr3
    obtain ⟨r2, hr2, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hr3
    obtain ⟨c2, rfl⟩ := Submodule.mem_span_singleton.1 hz2
    rw [e2] at hr2
    obtain ⟨r1, hr1, z1, hz1, rfl⟩ := Submodule.mem_sup.1 hr2
    obtain ⟨c1, rfl⟩ := Submodule.mem_span_singleton.1 hz1
    rw [e1, Submodule.mem_span_singleton] at hr1
    obtain ⟨c0, rfl⟩ := hr1
    exact ⟨c0, c1, c2, c3, c4, by simp only [Algebra.smul_def, mul_one]; try ring⟩
  -- `y²` against the basis of `L(6)`; the `x³` coefficient is nonzero because `y² ∉ L(5)`
  have hy2 : y ^ 2 ∈ poleSubmodule h 6 := by simp [mem_poleSubmodule, hdy2]
  rw [e6] at hy2
  obtain ⟨w, hw, z, hz, hsum⟩ := Submodule.mem_sup.1 hy2
  obtain ⟨c5, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hc5 : c5 ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hsum
    have hw5 : d w ≤ 5 := hw
    rw [hsum] at hw5
    omega
  obtain ⟨c0, c1, c2, c3, c4, hwe⟩ := hL5 w hw
  have hrel : y ^ 2 = algebraMap k R c0 + algebraMap k R c1 * x + algebraMap k R c2 * y
      + algebraMap k R c3 * x ^ 2 + algebraMap k R c4 * (x * y)
      + algebraMap k R c5 * x ^ 3 := by
    rw [Algebra.smul_def] at hsum
    rw [← hsum, hwe]; try ring
  -- `X = c₅·x`, `Y = c₅·y` normalises the leading coefficients to one
  refine ⟨⟨-c4, c3, -(c2 * c5), c1 * c5, c0 * c5 ^ 2⟩,
    algebraMap k R c5 * x, algebraMap k R c5 * y, ?_, ?_⟩
  · simp only [map_neg, map_mul, map_pow]
    linear_combination (algebraMap k R c5) ^ 2 * hrel
  · set S : Subring R := Subring.closure (Set.range (algebraMap k R) ∪
      {algebraMap k R c5 * x, algebraMap k R c5 * y}) with hS
    have hA : ∀ c : k, algebraMap k R c ∈ S := fun c =>
      Subring.subset_closure (Or.inl ⟨c, rfl⟩)
    have hinv : algebraMap k R c5⁻¹ * algebraMap k R c5 = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc5, map_one]
    have hxS : x ∈ S := by
      have hm : algebraMap k R c5⁻¹ * (algebraMap k R c5 * x) ∈ S :=
        Subring.mul_mem _ (hA c5⁻¹) (Subring.subset_closure (Or.inr (Set.mem_insert _ _)))
      rwa [← mul_assoc, hinv, one_mul] at hm
    have hyS : y ∈ S := by
      have hm : algebraMap k R c5⁻¹ * (algebraMap k R c5 * y) ∈ S :=
        Subring.mul_mem _ (hA c5⁻¹)
          (Subring.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl)))
      rwa [← mul_assoc, hinv, one_mul] at hm
    exact eq_top_iff.2 fun r _ => mem_of_isPoleDegree h hfd hrank hx hy hA hxS hyS r

end Rank

end Fermat
