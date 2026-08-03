## A ONE-HOP CONSUMER SCAN CALLS A DEAD LEAF LIVE — THE SCAN MUST BE A FIXPOINT
(2026-08-01, `flt-lean-385`, the `geomPic_descent` cluster in
`ModularCurve/HyperellipticJacobian.lean`.)  The standing check before proving a leaf is
"grep the comment-stripped tree for consumers of your target".  Run one hop, it is wrong in
the direction that costs an agent-run: it reports LIVE for a leaf whose consumer is itself
consumerless.
Here a rival cut had orphaned FOUR leaves at once.  Three of them —
`geomPic_exists_bcDiv_of_divAct_fixed`, `geomPic_exists_finiteLevel_divisor`,
`geomPic_hilbert90` — return exactly one code hit each, their own declaration line, and the
one-hop scan gets those right.  The fourth, `geomPic_exists_const_of_ord_nonneg`, has an
honest consumer (`geomPic_degOf_eq_one`), which has an honest consumer
(`geomPic_degHom_divAct`), **which has none**.  So a chain of three declarations, two of them
PROVEN, was dead, and one hop says otherwise.
    for each name: consumers := code hits outside its own declaration
    dead := fixpoint of  { X : every consumer of X is dead }   -- not  { X : no consumer }
**A rival cut orphans a SUBTREE, not a leaf**, because the losing cut's assembly lemmas were
written to serve it and nothing else.  Expect PROVEN declarations in the dead set — they are
invisible to every sorry-scan, cost nothing to keep, and are the thing that makes the one-hop
answer wrong.
**And when the WINNER is itself a leaf there is no inline block to harvest.**  CLAUDE.md's
existing repair — *the winner's INLINE block is almost always your proof* — worked for exactly
one of the four here, because cut B's `geomPic_descent` happened to carry 3b's argument
inline; abstracting it made 3b proven AND live in one edit.  For the other three the winner
(`geomPic_descent_divisor`) is a `sorry`, so nothing can be harvested and the choice is
DELETE or RESTORE THE CONSUMPTION.
**Restore, when the loser is the better decomposition — and the test for that is which side
has NAMES.**  `geomPic_descent_divisor` bundles a degree count, a normalisation, a cocycle
construction, an inflation and Hilbert 90; the loser's residue is *`κ(w) = ℚ̄`*, *a divisor is
defined at a finite Galois level* and *Hilbert 90 for `F̄/F`* — three statements a prover can
look up.  So the task is **prove the WINNER over the loser's leaves**: one leaf out, three
citable ones in, and the dead subtree revives with them.  Deleting instead scores better on
the count and throws the decomposition away.
Two riders, both about not making it worse:
* **Do NOT prove a dead leaf "while you are here".**  A proven declaration with no consumer is
  free-floating code, which this project forbids, so the next sweep deletes it — the work is
  lost and the frontier moved by one for nothing.  Say so ON the leaf, in capitals: three
  dispatches had already been drawn to this block.
* **When you cut the residue of such a leaf, cut it as a STRENGTHENING of something LIVE.**
  `geomPic_hilbert90`'s route needs the fixed field of an OPEN SUBGROUP, and the file has only
  the absolute statement, as its own separate leaf — which is live.  Strengthening that live
  leaf keeps the new obligation consumed; opening a fifth sibling here would reproduce the
  dead-leaf problem one level down.
