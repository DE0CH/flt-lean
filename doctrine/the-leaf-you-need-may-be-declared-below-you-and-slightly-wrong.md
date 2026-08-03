## THE LEAF YOU NEED MAY BE DECLARED BELOW YOU AND SLIGHTLY WRONG — CUT THE COMMON GENERALISATION ABOVE, DO NOT HOIST
(2026-08-02, `flt-lean-252`, on `norm_coeff_le_sqrt_of_dvd_level` in
`ModularCurve/X0.lean`; frontier `101 → 100` with no code moved.)
The declaration-order sections above give two repairs for "my leaf's input is
declared below me": HOIST the input, or move the CONSUMERS down. There is a
third, and where it applies it is far cheaper than either, because it moves
nothing at all.
That leaf's route needed the Atkin–Lehner local value at a newform. The tree
already had it — `norm_coeff_le_one_of_sq_not_dvd_of_isNewEigenformAt`, a
`sorry` leaf **2337 lines BELOW**, and carrying one hypothesis too many
(`¬ p² ∣ M`, i.e. only the `p ∥ M` half). So the two obvious moves were both
bad: cutting a rival leaf above manufactures a duplicate of a leaf that already
has consumers, and hoisting a declaration 2300 lines up in the most-edited file
in the tree is the merge-hostile shape class 7 is about.
**What works: cut ONE new leaf ABOVE, obtained from the below-leaf by DELETING
the hypothesis that does not survive your generality, then prove BOTH over it.**
Here `‖a_p‖ ≤ 1` for *every* `p ∣ M` at a newform subsumes the `p ∥ M` version
(`a_p = 0` outright when `p² ∣ M`, so the dropped case is the EASIER half of the
same citation), and the below-leaf becomes a one-line delegation. Net `2 → 1`,
no relocation, and **no call site moves** — keep the delegating theorem's
signature, underscore the now-unused binder, and leave its docstring in place.
Three checks before taking it, and all three are cheap:
* **Deleting a hypothesis is a STRENGTHENING**, so the below-leaf's audit does
  NOT transfer. Re-run it on the added case. If the added case is *harder* than
  the original, this move is a trap — you have made the frontier worse while the
  count says `−1`.
* **Grep for the below-leaf before cutting anything.** A conclusion grep, not a
  name grep: the two statements here shared no identifier with my target's
  vocabulary, and a route note naming the missing input in PROSE ("the missing
  arithmetic is `‖a_p‖ = 1` for `p ∥ M` at a newform") is what actually matched.
* **Check the new leaf's own load-bearing hypotheses with a witness**, because
  the generalisation is where one gets dropped. Here `hnew` is load-bearing and
  the witness is one PARI line: `a₂` of the level-11 newform is `−2`, so its
  `2`-stabilizations are eigenforms of level `22` with `‖a₂‖ = √2 > 1` — which
  simultaneously proves the parent's `√p` cannot be improved to `1`.
### RIDER: TWO RECURSIONS AT ONE PRIME KILL A CASE FOR FREE
Same proof, and it corrects a sentence this file repeats in three audits:
*"`hecke`/`atkin` constrain only the RELATIONS among the `a_n`, never their
size."* True of ONE eigenform. Across a stabilization it is false in a useful
direction: if `a` satisfies `atkin` at `p` (because `p ∣ M`) and its parent `b`
satisfies `hecke` at `p` (because `p ∤ M₀`), then `a_{p²} = a_p²` against
`b_{p²} = b_p² − p` forces `(p : ℂ) = 0` whenever the stabilization prime is not
`p`. That is a whole sub-case of the induction discharged with no bound at all,
and the same computation at the stabilization prime itself produces `a_p·β = p`
— the quadratic `X² − b_p X + p` — which is what turns Deligne at the SMALLER
level into the bound at the larger one. **When two of a structure's recursion
fields can both apply to the same coefficient, compare them before assuming a
case needs analysis.**
