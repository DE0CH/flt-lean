import Fermat.PrimeFive

/-!
# Fermat's Last Theorem — top layer

`fermat_last_theorem` reduces `FermatLastTheorem` to
* exponent `4` — `fermatLastTheoremFour` (mathlib),
* exponent `3` — `fermatLastTheoremThree` (mathlib),
* prime exponents `p ≥ 5` — `fermatLastTheoremFor_of_five_le`
  (`Fermat/PrimeFive.lean`, the remaining open subtree),

via mathlib's reduction `FermatLastTheorem.of_odd_primes`.
-/

/-- **Fermat's Last Theorem**: for `n ≥ 3`, the equation `a ^ n + b ^ n = c ^ n`
has no solutions in nonzero natural numbers. -/
theorem fermat_last_theorem : FermatLastTheorem := by
  apply FermatLastTheorem.of_odd_primes
  intro p hp hodd
  by_cases hlt : p < 5
  · -- `p` is an odd prime `< 5`, so `p = 3`.
    have h2 : 2 ≤ p := hp.two_le
    interval_cases p
    · exact absurd hodd (by decide)
    · exact fermatLastTheoremThree
    · exact absurd hp (by decide)
  · exact fermatLastTheoremFor_of_five_le p hp (le_of_not_gt hlt)

/-- Fermat's Last Theorem, unfolded to its explicit `∀`-statement. -/
theorem fermat_last_theorem_explicit :
    ∀ n : ℕ, 2 < n →
      ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n :=
  fun n hn => fermat_last_theorem n hn
