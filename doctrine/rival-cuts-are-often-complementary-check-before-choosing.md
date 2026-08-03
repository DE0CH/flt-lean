## RIVAL CUTS ARE OFTEN COMPLEMENTARY — check before choosing

(2026-07-30.) Nine of 57 branches in one batch were declined because another agent had cut the
same node differently. In one case that verdict would have been wrong. `flt-lean-134` proved
sub-leaf (γ) of `exists_relNormDivisorHom_ray_class` OUTRIGHT and left (α) over a fresh sorry;
`flt-lean-343` proved (α) OUTRIGHT and left (γ) over a fresh sorry. **Taking either branch whole
keeps an avoidable open node; taking one proof from each closes both.** It cost one careful read
of four hunks and netted zero new sorries where either alone netted one.

So when two branches cut one node, the question is not "which cut is better" but "did they close
different halves". Ask it first. The tie-breakers, in the order that has actually decided cases:

- **fewer OPEN leaves after**, not fewer leaves created — `flt-lean-44`'s divisor-set cut left ONE
  leaf and closed 23 of 32 cases outright, against a bound-cut that left TWO and closed none;
- **named beats anonymous** — a cut leaving 8 NAMED leaves beats one leaving 4 declarations with 4
  anonymous inner sorries inside them, even though the headline count is worse, because an inner
  sorry is ownerless by construction;
- **already integrated and consumed by neighbours**, which is the merge worker's only defensible
  ground when the mathematics is genuinely equivalent (two complete proofs of one theorem cannot
  both be carried — the name collides — so that is a CHOICE, not a merge, and it belongs to an
  author; record the rejected branch's sha in the merge commit).

**And a branch that was right when dispatched can be wrong when it lands.** `flt-lean-91` and
`flt-lean-195` independently generalised `EllipticScheme.lean`'s reverse Riemann-Roch chain from
`ℚ` to an arbitrary field, both truthfully reporting "NO LEAF WAS ADDED" — true at their base,
where the three leaves were open. They were PROVEN at `ℚ` by the time the branches merged, so the
same edit would have traded one closed leaf for three re-opened ones. Re-derive a branch's own
accounting against the release, never against its base; and when you decline for this reason, queue
the follow-up, because the work usually got CHEAPER (here: generalise the PROOFS, and both targets
close with no new sorry).

