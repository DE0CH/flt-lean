import Mathlib

/-!
# Fermat's Last Theorem for prime exponents `p ≥ 5`

This is the hard case of Fermat's Last Theorem, proved by Wiles and
Taylor–Wiles (1995) via the Frey–Serre–Ribet reduction to modularity of
semistable elliptic curves over `ℚ`.

The statement is recorded here as the root of the remaining dependency
tree; its proof is decomposed in the files this one will come to import
(Frey curve, Mazur irreducibility, modularity, Ribet level lowering,
absence of weight-2 level-2 cusp forms). See `PROGRESS.md`.
-/

/-- **Fermat's Last Theorem for prime exponents `p ≥ 5`** (Wiles, Taylor–Wiles).
If `p ≥ 5` is prime, then `a ^ p + b ^ p = c ^ p` has no solutions in nonzero
natural numbers. -/
theorem fermatLastTheoremFor_of_five_le (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    FermatLastTheoremFor p := by
  sorry
