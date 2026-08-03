## SEVENTH class: an OPEN leaf that is also DEAD — and "it was deleted" is a claim, not a fact

(2026-07-31, `flt-lean-190`.) Every counting rule above asks *is this leaf open?*
None asks *does anything consume it?* A leaf can be open, compile, emit its
`declaration uses 'sorry'` warning, pass the three-part ownership test, survive
`leafstat.py` — and still be **worth nothing to close**, because its only
consumer is itself consumerless. Closing it moves the frontier number and moves
the project not at all.

`X0.lean` carried exactly this. `exists_galoisConj_cmEndomorphism_eq_sub` was a
live sorry leaf whose sole consumer, `not_stable_of_cmEndomorphism`, had **zero**
uses anywhere in the tree — the CM route it served had been replaced days earlier
by a CM-blind certificate table.

**What made it invisible is the interesting part, and it is a new medium for an
old trap.** FOUR docstrings in that file stated that `not_stable_of_cmEndomorphism`
"became consumerless and was DELETED the same day" (2026-07-28). The write-up
landed; the deletion did not. Those four copies **cross-corroborate**: reading any
two looks like independent confirmation, when they are one author's single claim
written in four places. This is the commit-message trap one section up, in
docstring form — and worse, because docstrings are what the next agent reads to
orient.

So add to every bookkeeping cycle, and to every prover agent's first ten minutes:

- **Before working a leaf, establish REACHABILITY, not just openness.** Grep
  comment-stripped source for uses of the leaf's name *and* of each declaration
  that consumes it, transitively, until you hit something in the root cone. One
  `python3` pass over `Fermat/` costs seconds.
- **A docstring saying something WAS deleted is a hypothesis.** So is "PROVEN",
  "consumerless", "now obsolete", and "this leaf is no longer needed". Grep for
  the name. The compiler and a comment-stripped scan are the only witnesses.
- **Deleting the dead pair is a FULL result**, not a consolation prize: it removes
  a leaf that would otherwise keep drawing dispatches forever.

**And a dead consumer can be hiding a NARROWING.** Once the dead theorem was gone,
the surviving leaf `not_forall_galoisScalar_of_cmEndomorphism` had exactly one
call site, which instantiated it at `q = p`. It had been stated for an arbitrary
prime `q`, needing three regimes; narrowed to `q = p` only the ramified one
survives, dropping the Weil-pairing determinant argument — the hardest ingredient
— entirely. **A leaf stated wider than any live call site needs is common, and the
usual cause is a call site that has since died.** Check the width whenever you
delete a consumer.

