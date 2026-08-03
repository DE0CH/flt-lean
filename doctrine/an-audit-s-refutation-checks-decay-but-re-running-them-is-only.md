## AN AUDIT'S REFUTATION CHECKS DECAY — BUT RE-RUNNING THEM IS ONLY HALF THE JOB

(2026-07-31, `flt-lean-246`, on two atomicity-audited leaves of `KhareWintenberger.lean`.)

A mature leaf here carries an ATOMICITY or CUT audit that names each axis it searched
*and the one-line check that would refute the verdict*. Those checks are the most
valuable thing in the docstring and they are cheap — three greps closed three axes in
under a minute. **Run them; they decay.** Two of the three had moved since the audit was
written: `exists_const_natCard_zeroLocus_sub_le` had gone from an open leaf to **PROVEN**
(111 body lines, zero `sorry`), which turns "blocker 1 is a piece of mathematics" into
"blocker 1 is a relocation job" — a completely different price on the same cut.

**But an audit's checks only cover the axes it thought of, and the gap is systematic
rather than accidental.** A CUT AUDIT that refutes *"derive the node's conclusion FROM
the weaker shape"* says nothing about *"replace the node's conclusion BY the weaker
shape and rewire the consumers"*. Those are different moves with different failure
modes, and the second is the one an attacker actually tries first. Here the audit had
carefully refuted direction one (purity cannot rebuild the point-count package —
`Npt : ℕ → ℕ` effectivity) and was silent on direction two, which is where the whole
decision lived.

**And before weakening any leaf to "what its consumer needs", READ EVERY CONSUMER.**
This is where the trap sprang. Every docstring in that block presented the node as
feeding one lemma to produce `‖φ(a_w)‖ ≤ 2√(Nw)` — true of consumer 1. Consumer 2, 1400
lines away, calls a *sharper* lemma twice and needs `‖γ i‖ = ‖γ j‖ = √q` **exactly**, an
equality rather than a bound. Weakening the node to consumer 1's conclusion — the obvious
move, and the one the prose invites — compiles nowhere. No docstring recorded this; only
reading the second proof did. Generalise: **prose describes the consumer the author was
thinking about**, so the consumer set is something to enumerate mechanically, never to
inherit.

**Finally, "strictly weaker" is not automatically better.** The purity shape here *is*
strictly weaker (the audit's own effectivity argument separates them) and it was still
declined, because it orphans ~190 lines of proven complex analysis into free-floating
code while closing zero leaves and opening zero. Under this file's own tie-breaker —
count OPEN leaves after, not leaves created — a reshaping that is leaf-neutral and
destroys verified material is a loss. **Record the declined option with the condition
that would reverse it** (here: a second consumer appearing for the orphaned lemmas), so
the next owner inherits a decision rather than an open question.

