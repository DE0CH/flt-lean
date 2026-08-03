## A LEAF'S OWN PRESCRIBED ROUTE CAN SILENTLY USE THE HYPOTHESIS THE LEAF IS MISSING
(2026-08-02, `flt-lean-124`, `exists_tameLocalLift_of_isSmallExtension` — item (5)(d)
of the obstruction audit in `HardlyRamified/Deformation.lean`.)  A mature leaf here
carries a ROUTE: "the three data lift one at a time and only one of them is
obstructed", bullet by bullet.  The route is written to reassure a successor that the
leaf is attackable, and it is read that way.  **Read it instead as a list of CLAIMS,
and check each one's hypotheses against the leaf's binder list.  A step the route
states as obvious is exactly where a missing hypothesis hides**, because the author
was thinking about the intended application, where it holds for free.
Here the route's first bullet said the character `δ` "is unramified and satisfies
`δ² = 1`, so it factors through the unramified quotient and **is determined by
`δ(Frob) ∈ {±1}`**; both values lift canonically".  Every clause is true in the
application and the bolded one is FALSE in the stated generality: `δ(Frob)` is merely
SOME square root of `1`, and `3² = 1` in `ZMod 8`.  So the leaf was refuted by its own
sketch — and the refutation is the whole falsity audit, obtained by reading four lines
of prose rather than by hunting for a witness.
**The witness the sketch points at is then immediate, and it is the smallest one.**
`ZMod 16 ↠ ZMod 8` is a small extension (`𝔪 · ker = (2)·(8) = 0`); the square roots of
`1` are `{1,3,5,7}` below and `{1,7,9,15}` above, and the latter reduce to `{1,7}`
only.  So `3` squares to `1` and lifts to nothing.  Three `decide`s check it in ten
seconds.  **When a leaf's conclusion asserts a lift of an object satisfying a
POLYNOMIAL equation (`x² = 1`, `x² = x`, `xⁿ = 1`), the refutation is almost always a
`ZMod p^k ↠ ZMod p^(k-1)` with `p` the bad prime; try that before anything clever.**
**AND THE CHEAPEST ORACLE FOR WHICH HYPOTHESIS IS MISSING: DIFF THE BINDER LISTS OF
THE SIBLING CLAUSES CUT FROM THE SAME AUDIT ITEM.**  Item (5) was cut into four
clauses on one day by one author.  Clause (5a) carries `(h2 : IsUnit (2 : S))` with a
docstring saying "where `hℓOdd` enters, and it is the only place it does"; clause (5d)
is the same kind of statement — lift a `±1`-valued datum along a small extension — and
did not carry it.  One `grep` for `IsUnit (2` over the file found both the missing
hypothesis and the proof that it is dischargeable at the call site.  This is the
standing "when two halves of a development mirror each other, DIFF THEIR BINDER LISTS"
rule at its sharpest scope: not two files, not a `ℚ`/`F` twin pair, but **clauses of
one audit item**, which are as close to each other as statements in this tree ever get
and are still written independently.
* **The repair can make the route's hardest-looking bullet FREE, and by a shorter
  argument than the route's.**  With `2` a unit, `δ g * δ g = 1` in a LOCAL ring forces
  `δ g 1 = ±1` POINTWISE (`eq_one_or_eq_neg_one_of_mul_self_eq_one`, already in the
  file) — no unramified quotient, no Frobenius, no class field theory.  So the bullet
  that read as "cite local CFT" is six lines.  Recut the leaf to RECEIVE the datum in
  the pinned form and the character bookkeeping leaves the frontier for good.
* **Do NOT hand a lifted `p̃`/`δ̃` into the residual leaf as a hypothesis.**  It looks
  like the same move and it is not a reduction: the content is that they can be chosen
  COMPATIBLY with the lift `τ`, so a `p̃` supplied independently of `τ` is worth
  nothing.  The `±1` pinning is a statement about the INPUT `ρ2`'s own structure, which
  is exactly why it reduces and the other two bullets do not.  **The test for whether
  peeling a bullet is a real cut: is the peeled statement about the leaf's INPUT, or
  about its OUTPUT?**  Only the first kind reduces.
**And record a second axis you checked and could not settle, rather than shipping a
hypothesis you cannot justify.**  Constructing the lifted character also needs
`{g : δ g = 1}` OPEN, which follows from continuity of `δ` as soon as `1` and `-1` are
topologically separated in `R` — free in the application (`D.R` is `𝔪`-adically
complete, hence Hausdorff) and NOT implied by the stated hypotheses.  No witness was
produced that the module topology on `Module.End R R` is coarse enough for the
pathology, so no hypothesis was added; the gap is written on the declaration with the
note that it is free at the call site.  A leaf that is FALSE is worse than one that is
open — and a leaf carrying an unjustified hypothesis nobody can discharge is worse
than one carrying a written-down question.
