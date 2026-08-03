## FOLLOW THE HYPOTHESIS: a "base" argument is usually spent in ONE place

(2026-07-31, closing the general-base half of a `ℚ`-only theorem in `X0.lean`.)
When a leaf is the base-free twin of a proven theorem that carries a base
argument — `g : Z ⟶ SpecQ`, `[CharZero k]`, `(hp : p ∤ N)` — do **not** start
from the mathematics. **Grep the proven proof for that argument and find every
use.** In this development the answer is repeatedly *one*, and it is used to
derive one small consequence.

`g : Z ⟶ SpecQ` ran through six declarations of `X0.lean` and was spent exactly
once, in step 1 of `isReduced_geomFibre_nTorsion_of_specQBase`, to get
`(n : K) ≠ 0`. Restating all six with that consequence as the hypothesis —
every proof copied *verbatim*, only the first line of one of them changed —
turned a leaf whose docstring called for "finiteness and flatness of `E[n]`, the
sections of a constant finite group scheme, and the comparison torsor" into a
single crisp arithmetic leaf about one curve over one field. Cost: an afternoon
of copy-and-elaborate at ~6 s per iteration. **The decomposition was mechanical;
finding it was one `grep`.**

Two corollaries.

* **A leaf's own "MISSING INFRASTRUCTURE" list is a hypothesis, not a fact**,
  and it goes stale silently: the list on this node had been retired three days
  earlier when its `ℚ`-side twin was reproven a different way, and the twin's
  docstring recorded the retirement while the leaf's did not. Check the sibling
  before believing the list.
* **The sibling's falsity audit may prove the wrong thing.** This one said the
  `ℚ`-base "is load-bearing and cannot be dropped: over a base of residue
  characteristic `p ∣ n` the statement is FALSE". The geometry was right and the
  conclusion was wrong — at such a base the *data* the statement quantifies over
  is empty. "The hypothesis is load-bearing for the PROOF" and "for the TRUTH"
  are different claims and audits conflate them.

