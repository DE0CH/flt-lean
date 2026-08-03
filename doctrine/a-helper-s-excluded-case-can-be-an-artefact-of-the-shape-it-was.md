## A HELPER'S EXCLUDED CASE CAN BE AN ARTEFACT OF THE SHAPE IT WAS STATED IN — GENERALISE THE HELPER BEFORE BELIEVING THE OBSTRUCTION
(2026-08-02, `flt-lean-75`, closing `exists_wronskianPoly_scalar_charTwo_supersingular`,
the last leaf of `EllipticCurve/DifferentialCharacter.lean`.)
That leaf's docstring ended with **"SO EXACTLY TWO PLACES ARE LEFT, and a prover should be
sent at those and nothing else"**, and the first of the two was wrong — not stale, not
mis-measured, but a misreading of a helper lemma's hypothesis as a fact about the
mathematics. The docstring said, of the root `b₀` of `S = a₁X + a₃`:
> `charTwo_AS_rootMultiplicity` does not apply (`S(b₀) = 0` is exactly its excluded
> hypothesis) … the missing input is a lower bound on `ord_{b₀} D` — the analogue of the
> Artin–Schreier step at a ramified place. Geometrically `b₀` is the `2`-torsion point of
> `W` … so this is a real configuration and not a case to be excluded.
Every clause about the HELPER is true, and the helper's own docstring says the same thing
in the same words. But the helper is stated in the exact syntactic shape of its first
consumer's expression — `N = Cx²·f + D² + Cx·D·S` — so its additive coefficient is `Cx·S`,
and `S(b) ≠ 0` is what buys `ord_b(Cx·S) = ord_b Cx`. The exclusion is a property of THAT
SPELLING, not of the Artin–Schreier step. In the leaf's own setting `hone` cancelled by `B`
reads `Cx·S = a₃′·E`, so the SAME `N` has additive coefficient `a₃′·E`, whose order is
`ord_b E` at every place, root of `S` or not.
**Restating the helper over an arbitrary additive coefficient is the same twenty-line
proof.** `AS_rootMultiplicity_gen`: `N = Q + (D² + c·D)` with `ord_b N < ord_b Q` and
`ord_b N < 2·ord_b c` gives `ord_b N = 2·ord_b D`. The old lemma is its `Q = Cx²f`,
`c = Cx·S` instance, the excluded place disappears, and the leaf's finite-place count runs
uniformly with no case split on `S(b)` anywhere.
**The check, and it is one read of the helper's PROOF rather than its statement: is the
hypothesis used for the mathematics, or only to establish an inequality that your setting
supplies another way?** In this development helpers are routinely stated in the shape of
the first consumer's expression — that is what makes them cheap to apply there and what
encodes that consumer's algebra into their hypotheses. A docstring that blames such a
hypothesis for a hard case is quoting the helper, not the problem.
**COROLLARY, AND IT IS THE PART THAT PAYS: A HYPOTHESIS HANDED TO A LEAF "SO THAT WHAT IS
LEFT IS THE COUNT AND NOTHING ELSE" CAN BE DEAD IN ONE BRANCH OF THE SPLIT.** `hparB` — the
parity of `ord_b B`, itself the whole output of the sibling theorem
`charTwo_rootMultiplicity_B_even` — is **not used** by the supersingular proof. With the
generalised step the parity is a CONCLUSION (`3m = 2(ε − d)` forces `m` even), not an
input. It is genuinely needed in the ordinary branch, where the coefficient really is
`Cx·S`; so the two branches are asymmetric for a structural reason, and nobody had
noticed because the parent forwards `hparB` to both. **Lean's unused-variable linter names
this for free the moment the proof closes — read the warning rather than suppressing it.**
Keep the binder (underscored) when the call site would otherwise have to move: an unused
hypothesis costs the consumer nothing, and a signature change plus its call site is the
class-7 interface split this file spends pages on.
### The half of that docstring that WAS right, and what it cost
The other named place, `∞`, was real: the degree bound `deg P + deg S ≤ 2·deg B` needed the
whole computation again in `natDegree`. Two things about doing it:
* **the crude-bound cases must be taken FIRST**, before any Artin–Schreier step —
  `deg A ≤ deg B`, and `deg A = deg B + 1` with `deg S = 0`. They are exactly where the
  leading term of `g(u)` need not dominate, so the step is unavailable; and they are not
  pathologies, since `deg A = deg B + 1` is the shape of an ordinary separable isogeny.
  Taking them first turns "the argument has a gap" into "two lines of `omega`";
* **`natDegree_add_eq_left_of_natDegree_lt` / `natDegree_sub_eq_left_of_natDegree_lt` are
  the `∞`-analogues of `rootMultiplicity_add_of_lt`**, and `natDegree_derivative_le` is the
  analogue of `pow_sub_one_dvd_derivative_of_pow_dvd`. Writing the two counts side by side
  with that dictionary in hand is what makes the second one a transcription.
### Three mechanical notes, each of which cost a round
* **Do the `ord`-side bookkeeping with DIVISIBILITY, not with `rootMultiplicity`.** A
  summand that is identically zero (here `Cx·D·C a₁` when `a₁ = 0`) has
  `rootMultiplicity = 0`, which destroys a min-bound; but `(X − b)^j ∣ 0` is free. Prove
  `(X − b)^j ∣ N₁` term by term and convert once with `le_rootMultiplicity_iff`. On the
  `natDegree` side the same asymmetry forces the opposite move — there `natDegree 0 = 0` is
  what you WANT, and the `by_cases` is on whether the polynomial being differentiated is
  constant.
* **`set x := e with h` does not fold terms produced LATER by a lemma.** A `have` obtained
  from an auxiliary theorem comes back in the raw spelling, and `omega` then treats it as a
  different atom from the goal's `x` — the failure prints two constraint sets over
  near-identical names. One `rw [← h] at that_have` fixes it; budget for it whenever a
  proof `set`s an abbreviation and then calls out to a lemma about the same object.
* **`rw [two_mul, pow_add]` to turn `(X − b)^(2k) ∣ Cx^2` into a product of two divisibilities
  rewrites inside `Cx ^ 2` as well**, and the error mentions `npowRec 1 Cx`, which reads as
  an instance problem and is not one. The idiom already in this file is right and should be
  copied: `have : (X − C b)^(2*k) = ((X − C b)^k)^2 := by ring` then `pow_dvd_pow_of_dvd`.
