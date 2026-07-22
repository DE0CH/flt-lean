/-
FrobeniusFixedField.lean — the finite-subfield degree toolkit over
`𝔽̄_q = AlgebraicClosure (ZMod q)`.

For each `n`, `frobFixed q n` is the subfield of `frobⁿ`-fixed points
`{x | x ^ q ^ n = x}` (a copy of `𝔽_{qⁿ}` inside `𝔽̄_q`).  The module
provides the degree dictionary — membership in `frobFixed q n` is
divisibility of the Frobenius period `frobPeriod q x` (the minimal
period of `x ↦ x ^ q` at `x`) — the exact cardinality `qⁿ`, the
lattice/divisibility order facts, fresh-element existence by counting,
and a curve-point version: a nonsingular point with abscissa in
`frobFixed q ℓ ∖ frobFixed q 1` avoiding a finite set, whose ordinate
lies in `frobFixed q (2ℓ)` (the ordinate solves a quadratic with
coefficients fixed by `frobℓ`).

This is the toolkit for discharging the `G''`-existence sorry in the
σ-mirror step of `exists_weilPairing_mu` (WeilPairing.lean): the mirror
field is `frobFixed q (2ℓf₀)`-shaped, the promised avoided elements
stay out by the arithmetic helper `d ∣ 2ℓf ∧ ¬ℓ ∣ d → d ∣ 2f`.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Data.Nat.Prime.Infinite

@[expose] public section

namespace WeilPairing

open Polynomial

variable (q : ℕ) [Fact q.Prime]

/-- The subfield of `frobⁿ`-fixed points of `𝔽̄_q`: elements with
`x ^ q ^ n = x`.  For `n ≠ 0` this is the copy of `𝔽_{qⁿ}` inside the
algebraic closure. -/
def frobFixed (n : ℕ) : Subfield (AlgebraicClosure (ZMod q)) where
  carrier := {x | x ^ q ^ n = x}
  zero_mem' := zero_pow (pow_ne_zero n (Fact.out (p := q.Prime)).ne_zero)
  one_mem' := one_pow _
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have hmap := map_add (iterateFrobenius (AlgebraicClosure (ZMod q)) q n) a b
    simpa [iterateFrobenius_def, ha, hb] using hmap
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hmap := map_neg (iterateFrobenius (AlgebraicClosure (ZMod q)) q n) a
    simpa [iterateFrobenius_def, ha] using hmap
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [inv_pow, ha]

theorem mem_frobFixed_iff {n : ℕ} {x : AlgebraicClosure (ZMod q)} :
    x ∈ frobFixed q n ↔ x ^ q ^ n = x := Iff.rfl

/-- The Frobenius period of `x`: the minimal period of the Frobenius
`x ↦ x ^ q` at `x`.  Positive for every element of `𝔽̄_q`
(`frobPeriod_pos`), and equal to the degree `[𝔽_q(x) : 𝔽_q]`. -/
noncomputable def frobPeriod (x : AlgebraicClosure (ZMod q)) : ℕ :=
  Function.minimalPeriod (frobenius (AlgebraicClosure (ZMod q)) q) x

theorem mem_frobFixed_iff_isPeriodicPt {n : ℕ} {x : AlgebraicClosure (ZMod q)} :
    x ∈ frobFixed q n ↔
      Function.IsPeriodicPt (frobenius (AlgebraicClosure (ZMod q)) q) n x := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  rw [mem_frobFixed_iff, iterate_frobenius]

/-- The degree dictionary (load-bearing): membership in the `frobⁿ`-fixed
subfield is divisibility of the Frobenius period. -/
theorem mem_frobFixed_iff_frobPeriod_dvd {n : ℕ} {x : AlgebraicClosure (ZMod q)} :
    x ∈ frobFixed q n ↔ frobPeriod q x ∣ n := by
  unfold frobPeriod
  rw [mem_frobFixed_iff_isPeriodicPt q, Function.isPeriodicPt_iff_minimalPeriod_dvd]

/-- Monotonicity of the fixed-subfield lattice along divisibility. -/
theorem frobFixed_le_frobFixed {a b : ℕ} (h : a ∣ b) :
    frobFixed q a ≤ frobFixed q b := fun _x hx =>
  (mem_frobFixed_iff_frobPeriod_dvd q).mpr
    (((mem_frobFixed_iff_frobPeriod_dvd q).mp hx).trans h)

/-- Every element of `𝔽̄_q` lies in some `frobFixed q m`, `m ≠ 0`
(everything is algebraic, so lies in a finite subfield). -/
theorem exists_ne_zero_mem_frobFixed (x : AlgebraicClosure (ZMod q)) :
    ∃ m : ℕ, m ≠ 0 ∧ x ∈ frobFixed q m := by
  classical
  have hint : IsIntegral (ZMod q) x :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ZMod q) x).isIntegral
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod q) {x}) :=
    Module.finite_of_finite (ZMod q)
  letI : Fintype (IntermediateField.adjoin (ZMod q) {x}) := Fintype.ofFinite _
  refine ⟨Module.finrank (ZMod q) (IntermediateField.adjoin (ZMod q) {x}),
    Module.finrank_pos.ne', ?_⟩
  rw [mem_frobFixed_iff]
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod q) {x}) =
      q ^ Module.finrank (ZMod q) (IntermediateField.adjoin (ZMod q) {x}) := by
    rw [Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]
  have hx := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self (ZMod q) x⟩ :
      IntermediateField.adjoin (ZMod q) {x})
  rw [hcard] at hx
  simpa using congrArg Subtype.val hx

/-- The Frobenius period is positive. -/
theorem frobPeriod_pos (x : AlgebraicClosure (ZMod q)) : 0 < frobPeriod q x := by
  obtain ⟨m, hm, hx⟩ := exists_ne_zero_mem_frobFixed q x
  have hd := (mem_frobFixed_iff_frobPeriod_dvd q).mp hx
  rcases Nat.eq_zero_or_pos (frobPeriod q x) with h0 | hpos
  · rw [h0] at hd
    exact absurd (zero_dvd_iff.mp hd) hm
  · exact hpos

theorem frobPeriod_le_of_mem {n : ℕ} (hn : n ≠ 0) {x : AlgebraicClosure (ZMod q)}
    (h : x ∈ frobFixed q n) : frobPeriod q x ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((mem_frobFixed_iff_frobPeriod_dvd q).mp h)

/-- An element of `frobFixed q ℓ ∖ frobFixed q 1` for `ℓ` prime has
Frobenius period exactly `ℓ`. -/
theorem frobPeriod_eq_prime {ℓ : ℕ} (hℓ : ℓ.Prime) {x : AlgebraicClosure (ZMod q)}
    (hmem : x ∈ frobFixed q ℓ) (hnot : x ∉ frobFixed q 1) : frobPeriod q x = ℓ := by
  rcases (Nat.dvd_prime hℓ).mp ((mem_frobFixed_iff_frobPeriod_dvd q).mp hmem) with h | h
  · exact absurd ((mem_frobFixed_iff_frobPeriod_dvd q).mpr (by rw [h])) hnot
  · exact h

/-! ### Cardinality: `frobFixed q n` has exactly `q ^ n` elements -/

/-- A classical decidable-equality instance on the algebraic closure
(for `Multiset.toFinset` and finset unions below). -/
noncomputable local instance : DecidableEq (AlgebraicClosure (ZMod q)) :=
  Classical.typeDecidableEq _

/-- The `frobⁿ`-fixed points as the finset of roots of `X ^ qⁿ - X`. -/
noncomputable def frobFixedFinset (n : ℕ) : Finset (AlgebraicClosure (ZMod q)) :=
  (X ^ q ^ n - X : (AlgebraicClosure (ZMod q))[X]).roots.toFinset

theorem mem_frobFixedFinset_iff {n : ℕ} (hn : n ≠ 0) {x : AlgebraicClosure (ZMod q)} :
    x ∈ frobFixedFinset q n ↔ x ∈ frobFixed q n := by
  have hne : (X ^ q ^ n - X : (AlgebraicClosure (ZMod q))[X]) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn (Fact.out (p := q.Prime)).one_lt
  rw [frobFixedFinset, Multiset.mem_toFinset, mem_roots hne, mem_frobFixed_iff]
  simp [Polynomial.IsRoot, sub_eq_zero]

/-- `frobFixed q n` is a finite set (roots of the nonzero polynomial
`X ^ qⁿ - X`). -/
theorem frobFixed_finite {n : ℕ} (hn : n ≠ 0) :
    ((frobFixed q n : Subfield (AlgebraicClosure (ZMod q))) :
      Set (AlgebraicClosure (ZMod q))).Finite := by
  have hcoe : ((frobFixed q n : Subfield (AlgebraicClosure (ZMod q))) :
      Set (AlgebraicClosure (ZMod q))) = ↑(frobFixedFinset q n) := by
    ext x
    rw [Finset.mem_coe, mem_frobFixedFinset_iff q hn, SetLike.mem_coe]
  rw [hcoe]
  exact Finset.finite_toSet _

/-- `frobFixed q n` has exactly `q ^ n` elements: `X ^ qⁿ - X` is
separable of degree `qⁿ` and splits over the algebraic closure. -/
theorem card_frobFixedFinset {n : ℕ} (hn : n ≠ 0) :
    (frobFixedFinset q n).card = q ^ n := by
  have hsep : (X ^ q ^ n - X : (AlgebraicClosure (ZMod q))[X]).Separable :=
    galois_poly_separable q (q ^ n) (dvd_pow_self q hn)
  rw [frobFixedFinset, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ hn (Fact.out (p := q.Prime)).one_lt]

/-! ### The lattice order is divisibility -/

theorem frobFixed_inf (a b : ℕ) :
    frobFixed q a ⊓ frobFixed q b = frobFixed q (Nat.gcd a b) := by
  ext x
  simp only [Subfield.mem_inf, mem_frobFixed_iff_frobPeriod_dvd q, Nat.dvd_gcd_iff]

theorem frobFixed_le_frobFixed_iff {a b : ℕ} (ha : a ≠ 0) :
    frobFixed q a ≤ frobFixed q b ↔ a ∣ b := by
  refine ⟨fun hle => ?_, frobFixed_le_frobFixed q⟩
  have hsub : frobFixed q a ≤ frobFixed q (Nat.gcd a b) := by
    rw [← frobFixed_inf]
    exact le_inf le_rfl hle
  have hg0 : Nat.gcd a b ≠ 0 := fun h => ha (Nat.eq_zero_of_gcd_eq_zero_left h)
  have hcard : q ^ a ≤ q ^ Nat.gcd a b := by
    rw [← card_frobFixedFinset q ha, ← card_frobFixedFinset q hg0]
    refine Finset.card_le_card fun x hx => ?_
    rw [mem_frobFixedFinset_iff q hg0]
    exact hsub ((mem_frobFixedFinset_iff q ha).mp hx)
  have hle' : a ≤ Nat.gcd a b :=
    (Nat.pow_le_pow_iff_right (Fact.out (p := q.Prime)).one_lt).mp hcard
  have hga : Nat.gcd a b = a :=
    le_antisymm (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha)) hle'
  exact hga ▸ Nat.gcd_dvd_right a b

/-! ### Fresh elements by counting -/

/-- Fresh-element existence: if `q ^ m + |A| < q ^ n` then `frobFixed q n`
contains an element outside `frobFixed q m` and outside `A`. -/
theorem exists_mem_notMem_avoid {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (A : Finset (AlgebraicClosure (ZMod q))) (hcard : q ^ m + A.card < q ^ n) :
    ∃ x : AlgebraicClosure (ZMod q),
      x ∈ frobFixed q n ∧ x ∉ frobFixed q m ∧ x ∉ A := by
  classical
  have hlt : (frobFixedFinset q m ∪ A).card < (frobFixedFinset q n).card := by
    calc (frobFixedFinset q m ∪ A).card
        ≤ (frobFixedFinset q m).card + A.card := Finset.card_union_le _ _
      _ = q ^ m + A.card := by rw [card_frobFixedFinset q hm]
      _ < q ^ n := hcard
      _ = (frobFixedFinset q n).card := (card_frobFixedFinset q hn).symm
  obtain ⟨x, hxn, hxout⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨x, (mem_frobFixedFinset_iff q hn).mp hxn,
    fun h => hxout (Finset.mem_union_left _ ((mem_frobFixedFinset_iff q hm).mpr h)),
    fun h => hxout (Finset.mem_union_right _ h)⟩

/-- Fresh-element existence at a prime: if `q + |A| < q ^ ℓ` then there
is `x ∈ frobFixed q ℓ` outside `frobFixed q 1` (hence of Frobenius
period exactly `ℓ`) avoiding `A`. -/
theorem exists_mem_prime_notMem_avoid {ℓ : ℕ} (hℓ : ℓ.Prime)
    (A : Finset (AlgebraicClosure (ZMod q))) (hcard : q + A.card < q ^ ℓ) :
    ∃ x : AlgebraicClosure (ZMod q),
      x ∈ frobFixed q ℓ ∧ x ∉ frobFixed q 1 ∧ x ∉ A := by
  refine exists_mem_notMem_avoid q hℓ.ne_zero one_ne_zero A ?_
  simpa [pow_one] using hcard

/-- There are primes `ℓ` beyond any bound with `q ^ ℓ` beyond any bound. -/
theorem exists_prime_lt_pow (N : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ N < ℓ ∧ N < q ^ ℓ := by
  obtain ⟨ℓ, hle, hp⟩ := Nat.exists_infinite_primes (N + 1)
  have hNℓ : N < ℓ := hle
  exact ⟨ℓ, hp, hNℓ,
    hNℓ.trans (Nat.lt_pow_self (Fact.out (p := q.Prime)).one_lt)⟩

/-! ### The arithmetic helper -/

/-- The degree-arithmetic helper: `d ∣ 2ℓf` and `d` coprime to `ℓ`
force `d ∣ 2f`. -/
theorem dvd_two_mul_of_coprime {d ℓ f : ℕ} (hcop : Nat.Coprime d ℓ)
    (hdvd : d ∣ 2 * ℓ * f) : d ∣ 2 * f := by
  refine hcop.dvd_of_dvd_mul_right ?_
  rwa [show 2 * f * ℓ = 2 * ℓ * f by ring]

/-- The degree-arithmetic helper, prime form: `d ∣ 2ℓf`, `ℓ` prime not
dividing `d`, force `d ∣ 2f`. -/
theorem dvd_two_mul_of_prime_not_dvd {d ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hdvd : d ∣ 2 * ℓ * f) (hnd : ¬ℓ ∣ d) : d ∣ 2 * f :=
  dvd_two_mul_of_coprime ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hnd).symm hdvd

/-- Mem-transport for the σ-mirror avoid-sets: an element outside
`frobFixed q (2f)` whose period is not divisible by the prime `ℓ` stays
outside `frobFixed q (2ℓf)`. -/
theorem notMem_frobFixed_two_mul_prime {x : AlgebraicClosure (ZMod q)} {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hnot : x ∉ frobFixed q (2 * f)) (hnd : ¬ℓ ∣ frobPeriod q x) :
    x ∉ frobFixed q (2 * ℓ * f) := fun hmem =>
  hnot <| (mem_frobFixed_iff_frobPeriod_dvd q).mpr <|
    dvd_two_mul_of_prime_not_dvd hℓ ((mem_frobFixed_iff_frobPeriod_dvd q).mp hmem) hnd

/-- A prime `ℓ` beyond the degree of a containing fixed field cannot
divide the Frobenius period (`ℓ > all fixed degrees` step of the
σ-mirror plan). -/
theorem not_dvd_frobPeriod_of_mem {x : AlgebraicClosure (ZMod q)} {N ℓ : ℕ}
    (hN : N ≠ 0) (hmem : x ∈ frobFixed q N) (hℓ : N < ℓ) :
    ¬ℓ ∣ frobPeriod q x := fun hdvd =>
  absurd ((Nat.le_of_dvd (frobPeriod_pos q x) hdvd).trans
    (frobPeriod_le_of_mem q hN hmem)) (Nat.not_le.mpr hℓ)

/-! ### Quadratic extensions and curve points -/

/-- If `y` solves a monic quadratic with coefficients fixed by `frobⁿ`,
then `y` is fixed by `frob²ⁿ`: `y ^ qⁿ` is again a root of the
quadratic, hence `y` itself or the conjugate `-y - b`, and applying
`frobⁿ` once more returns to `y`. -/
theorem mem_frobFixed_two_mul_of_quadratic {n : ℕ} {b c y : AlgebraicClosure (ZMod q)}
    (hb : b ∈ frobFixed q n) (hc : c ∈ frobFixed q n)
    (hy : y ^ 2 + b * y + c = 0) : y ∈ frobFixed q (2 * n) := by
  have hb' : b ^ q ^ n = b := (mem_frobFixed_iff q).mp hb
  have hc' : c ^ q ^ n = c := (mem_frobFixed_iff q).mp hc
  have h0 : (iterateFrobenius (AlgebraicClosure (ZMod q)) q n) (y ^ 2 + b * y + c) = 0 := by
    rw [hy, map_zero]
  rw [map_add, map_add, map_mul, map_pow] at h0
  simp only [iterateFrobenius_def] at h0
  rw [hb', hc'] at h0
  have hfac : (y ^ q ^ n - y) * (y ^ q ^ n + y + b) = 0 := by
    linear_combination h0 - hy
  rcases mul_eq_zero.mp hfac with h | h
  · exact frobFixed_le_frobFixed q (dvd_mul_left n 2)
      ((mem_frobFixed_iff q).mpr (sub_eq_zero.mp h))
  · have hz : y ^ q ^ n = -y - b := by linear_combination h
    have hneg : (-y - b : AlgebraicClosure (ZMod q)) ^ q ^ n = -(y ^ q ^ n) - b := by
      have hmap := map_sub (iterateFrobenius (AlgebraicClosure (ZMod q)) q n) (-y) b
      rw [map_neg] at hmap
      simpa [iterateFrobenius_def, hb'] using hmap
    rw [mem_frobFixed_iff, two_mul, pow_add, pow_mul, hz, hneg, hz]
    ring

/-- Curve-point version: for `ℓ` prime with `q + |A| < q ^ ℓ`, the curve
has a nonsingular point whose abscissa lies in
`frobFixed q ℓ ∖ frobFixed q 1` and avoids `A`, and whose ordinate lies
in `frobFixed q (2ℓ)`.  Nonsingularity-from-the-equation and the
`frobFixed q 1`-rationality of the coefficients are hypotheses
(instantiate with `Wb.toAffine` for a base-changed elliptic curve). -/
theorem exists_nonsingular_frobFixed (W : WeierstrassCurve.Affine (AlgebraicClosure (ZMod q)))
    (hns : ∀ x y : AlgebraicClosure (ZMod q), W.Equation x y → W.Nonsingular x y)
    (ha₁ : W.a₁ ∈ frobFixed q 1) (ha₂ : W.a₂ ∈ frobFixed q 1)
    (ha₃ : W.a₃ ∈ frobFixed q 1) (ha₄ : W.a₄ ∈ frobFixed q 1)
    (ha₆ : W.a₆ ∈ frobFixed q 1) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (A : Finset (AlgebraicClosure (ZMod q))) (hcard : q + A.card < q ^ ℓ) :
    ∃ x y : AlgebraicClosure (ZMod q), W.Nonsingular x y ∧
      x ∈ frobFixed q ℓ ∧ x ∉ frobFixed q 1 ∧ x ∉ A ∧
      y ∈ frobFixed q (2 * ℓ) := by
  obtain ⟨x, hxℓ, hx1, hxA⟩ := exists_mem_prime_notMem_avoid q hℓ A hcard
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    (W.polynomial.map (Polynomial.evalRingHom x)) (by
      rw [Polynomial.degree_map_eq_of_leadingCoeff_ne_zero]
      · rw [WeierstrassCurve.Affine.degree_polynomial]
        norm_num
      · rw [show W.polynomial.leadingCoeff = 1 from
          WeierstrassCurve.Affine.monic_polynomial]
        simp)
  have hEq : W.Equation x y := by
    rw [WeierstrassCurve.Affine.Equation]
    rw [Polynomial.IsRoot, Polynomial.eval_map] at hy
    rw [show W.polynomial.evalEval x y =
      W.polynomial.eval₂ (Polynomial.evalRingHom x) y from
      (Polynomial.eval₂_evalRingHom x ▸ rfl)]
    exact hy
  have h1ℓ : frobFixed q 1 ≤ frobFixed q ℓ := frobFixed_le_frobFixed q (one_dvd ℓ)
  have hquad : y ^ 2 + (W.a₁ * x + W.a₃) * y +
      -(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    have heq := (W.equation_iff x y).mp hEq
    linear_combination heq
  exact ⟨x, y, hns x y hEq, hxℓ, hx1, hxA,
    mem_frobFixed_two_mul_of_quadratic q
      (add_mem (mul_mem (h1ℓ ha₁) hxℓ) (h1ℓ ha₃))
      (neg_mem (add_mem (add_mem (add_mem (pow_mem hxℓ 3)
        (mul_mem (h1ℓ ha₂) (pow_mem hxℓ 2))) (mul_mem (h1ℓ ha₄) hxℓ)) (h1ℓ ha₆)))
      hquad⟩

/-- Convenience: images of the prime field are `frob`-fixed. -/
theorem algebraMap_mem_frobFixed_one (r : ZMod q) :
    algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) r ∈ frobFixed q 1 := by
  rw [mem_frobFixed_iff, pow_one, ← map_pow, ZMod.pow_card]

end WeilPairing
