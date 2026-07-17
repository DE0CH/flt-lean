/-
EDSRank.lean — own work for the Fermat project.

The rank-of-apparition machinery for normalised elliptic divisibility
sequences over a field: if `r ≥ 2` is minimal with `W r = 0`, then
either the neighbour `W (r+1)` is nonzero — in which case the zero set
of `W` on positive indices is exactly the multiples of `r` (the
`T(k−r, r)`-descent) — or the seeds degenerate: `(b, c) = (0, 0)`
(with `r = 2`) or `(c, d) = (0, 0)` with `b ≠ 0` (with `r = 3`). The
degenerate cases are impossible for the division-polynomial values at
a point of an elliptic curve (the small Bézout certificates), which
yields the coprimality of `Φₙ` and `ΨSqₙ` over a field — replacing
the resultant-formula node.
-/
module

public import Fermat.FLT.Mathlib.NumberTheory.EDSStange

@[expose] public section

namespace EDSRank

open EllipticDivisibilitySequence

variable {F : Type*} [Field F] (b c d : F)

/-- `r` is the rank of apparition: the minimal index `≥ 2` with
`W r = 0` (there is none at `1` since `W 1 = 1`). -/
def IsRank (r : ℕ) : Prop :=
  2 ≤ r ∧ normEDS b c d r = 0 ∧
    ∀ k : ℕ, 1 ≤ k → k < r → normEDS b c d k ≠ 0

variable {b c d}

lemma IsRank.sub_one_ne_zero {r : ℕ} (h : IsRank b c d r) :
    normEDS b c d ((r : ℤ) - 1) ≠ 0 := by
  have h2 := h.1
  have hmin := h.2.2 (r - 1) (by omega) (by omega)
  rwa [show (((r - 1 : ℕ)) : ℤ) = (r : ℤ) - 1 by omega] at hmin

/-- **Adjacent zeros force `c = 0`**: the `T(·, 2)` quadratic
recursion at `n = r − 1`. -/
lemma IsRank.c_eq_zero_of_adjacent {r : ℕ} (h : IsRank b c d r)
    (hadj : normEDS b c d ((r : ℤ) + 1) = 0) : c = 0 := by
  have hq := normEDS_quadratic b c d ((r : ℤ) - 1)
  rw [show ((r : ℤ) - 1 + 2) = (r : ℤ) + 1 by ring,
    show ((r : ℤ) - 1 + 1) = (r : ℤ) by ring] at hq
  rw [hadj, h.2.1] at hq
  simp only [zero_mul, mul_zero, zero_sub] at hq
  have hc2 : c * normEDS b c d ((r : ℤ) - 1) ^ 2 = 0 :=
    neg_eq_zero.mp hq.symm
  rcases mul_eq_zero.mp hc2 with hc | hsq
  · exact hc
  · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp hsq)
      h.sub_one_ne_zero

/-- **Adjacent zeros bound the rank by `3`**: `c = W 3 = 0` and
minimality. -/
lemma IsRank.le_three_of_adjacent {r : ℕ} (h : IsRank b c d r)
    (hadj : normEDS b c d ((r : ℤ) + 1) = 0) : r ≤ 3 := by
  by_contra hgt
  have hc := h.c_eq_zero_of_adjacent hadj
  have h3 := h.2.2 3 (by omega) (by omega)
  rw [show ((3 : ℕ) : ℤ) = 3 from rfl, normEDS_three] at h3
  exact h3 hc

/-- **The degenerate seeds from adjacent zeros**: either
`(b, c) = (0, 0)` (rank `2`) or `(c, d) = (0, 0)` with `b ≠ 0`
(rank `3`). -/
lemma IsRank.degenerate_of_adjacent {r : ℕ} (h : IsRank b c d r)
    (hadj : normEDS b c d ((r : ℤ) + 1) = 0) :
    (b = 0 ∧ c = 0) ∨ (c = 0 ∧ d = 0 ∧ b ≠ 0) := by
  have hc := h.c_eq_zero_of_adjacent hadj
  have hr3 := h.le_three_of_adjacent hadj
  have hr2 := h.1
  interval_cases r
  · -- rank 2 : `b = W 2 = 0`
    left
    refine ⟨?_, hc⟩
    have := h.2.1
    rwa [show ((2 : ℕ) : ℤ) = 2 from rfl, normEDS_two] at this
  · -- rank 3 : `d ⬝ b = W 4 = 0` and `b = W 2 ≠ 0`
    right
    have hb : b ≠ 0 := by
      have := h.2.2 2 (by omega) (by omega)
      rwa [show ((2 : ℕ) : ℤ) = 2 from rfl, normEDS_two] at this
    have hd : d * b = 0 := by
      have := hadj
      rwa [show ((3 : ℕ) : ℤ) + 1 = 4 from rfl, normEDS_four] at this
    rcases mul_eq_zero.mp hd with hd' | hb'
    · exact ⟨hc, hd', hb⟩
    · exact absurd hb' hb

/-- **Rank divisibility**: when the rank has a nonzero upper
neighbour, every positive zero index is a multiple of the rank — the
`T(k − r, r)`-descent. -/
theorem IsRank.dvd_of_eq_zero {r : ℕ} (h : IsRank b c d r)
    (hne : normEDS b c d ((r : ℤ) + 1) ≠ 0) :
    ∀ k : ℕ, 1 ≤ k → normEDS b c d k = 0 → r ∣ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro hk h0
  rcases lt_trichotomy k r with hlt | heq | hgt
  · exact absurd h0 (h.2.2 k hk hlt)
  · exact heq ▸ dvd_refl k
  · -- the descent step
    have hT := normEDS_ellSequence b c d
      ((k : ℤ) - r) (r : ℤ)
    rw [show ((k : ℤ) - r + r) = (k : ℤ) by ring] at hT
    have hzero : normEDS b c d ((k : ℤ) - r) = 0 := by
      have hprod : normEDS b c d ((r : ℤ) + 1) *
          normEDS b c d ((r : ℤ) - 1) *
          normEDS b c d ((k : ℤ) - r) ^ 2 = 0 := by
        linear_combination hT -
          normEDS b c d ((k : ℤ) - r - r) * h0 +
          (normEDS b c d ((k : ℤ) - r + 1) *
            normEDS b c d ((k : ℤ) - r - 1) *
            normEDS b c d (r : ℤ)) * h.2.1
      rcases mul_eq_zero.mp hprod with hp | hsq
      · rcases mul_eq_zero.mp hp with hp1 | hp2
        · exact absurd hp1 hne
        · exact absurd hp2 h.sub_one_ne_zero
      · exact pow_eq_zero_iff two_ne_zero |>.mp hsq
    have h2r := h.1
    have hkr : normEDS b c d ((k - r : ℕ)) = 0 := by
      rw [Nat.cast_sub (le_of_lt hgt)]
      exact hzero
    have hIH := IH (k - r) (by omega) (by omega) hkr
    obtain ⟨m, hm⟩ := hIH
    have hk : k = r * m + r := (Nat.sub_eq_iff_eq_add (le_of_lt hgt)).mp hm
    exact ⟨m + 1, by rw [Nat.mul_succ]; exact hk⟩

end EDSRank
