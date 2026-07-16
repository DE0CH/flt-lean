# FLT formalization — progress and dependency tree

Goal: `theorem fermat_last_theorem : FermatLastTheorem` in `Fermat/Basic.lean`,
with the proof tree walked top-down; every gap is an explicit `sorry`-d theorem
(never an `axiom`), and every layer is compiled and axiom-checked
(`#print axioms` must show at most `propext`, `Classical.choice`, `Quot.sound`,
`sorryAx`).

Strategy: treat the proof as a dependency tree. State the theorem, prove it
from the strongest available mathlib facts plus explicitly stated gaps, then
recurse into the gaps. Follow the Wiles/Taylor–Wiles route as organized by the
Frey–Serre–Ribet reduction; use Buzzard's FLT project (Imperial) blueprint as a
map where helpful.

## Tree (✓ = proven here or in mathlib, ✗ = sorry, ○ = in progress)

- `fermat_last_theorem : FermatLastTheorem`
  - ✓ `FermatLastTheorem.of_odd_primes` (mathlib, NumberTheory/FLT/Four.lean)
  - ✓ `fermatLastTheoremFour` (mathlib)
  - ✓ `fermatLastTheoremThree` (mathlib)
  - ✗ `fermatLastTheoremFor_of_five_le : ∀ p, p.Prime → 5 ≤ p → FermatLastTheoremFor p`
    — the Wiles–Taylor route; to be decomposed next into:
    - Frey curve `y² = x(x − a^p)(x + b^p)` as an elliptic curve over ℚ
    - Mazur: irreducibility of the mod-p representation of the Frey curve
    - Wiles–Taylor–Wiles: modularity of semistable elliptic curves over ℚ
    - Ribet: level lowering to level 2
    - No nonzero cusp forms of weight 2, level Γ₀(2)

## Log

- 2026-07-16: project scaffolded in `fermat/`; branch `flt-formalization`,
  worktree `/tmp/flt-worktree`. Layer 1 (reduction to odd primes ≥ 5) built.
