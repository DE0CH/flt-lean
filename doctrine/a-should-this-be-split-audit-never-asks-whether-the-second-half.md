## A "SHOULD THIS BE SPLIT?" AUDIT NEVER ASKS WHETHER THE SECOND HALF HAS A CONSUMER
(2026-08-01, `flt-lean-27`, on `X18.two_divisible_pic` / `X13.two_divisible_pic` in
`ModularCurve/HyperellipticJacobian.lean`.) A mature leaf of the shape `A ∧ B` — usually
not written as a conjunction, but as one statement that *is* one, like `Pic = 2·Pic` for a
finitely generated group, which is `rank = 0` **and** `#tors` odd — attracts a standing
question: *should this be split into two leaves?* This development answers it well: two
careful passes on the same day priced the split, found the second half a fresh development
for no gain, and wrote "not a cut worth making" both times. Both were right.
**Neither asked who READS the second half.** Nothing did. The sole consumer was one
`finite_pic`, which reads `rank = 0` and never the parity, so the honest move was never a
split but a **DELETION**: weaken the leaf to `A`, rename it, rewire the one call site. What
had been costed at length as "a second leaf nobody wants to prove" was an obligation nobody
wanted at all.
**The check is one question and it is not the one the audit asks.** "Should `A ∧ B` be
split?" is about the PROVER's convenience. Ask instead: **grep the consumers and see which
conjunct each reads.** A conjunct with no reader is deleted, not split, and no amount of
deliberation about the split will surface that — the split framing presupposes both halves
are wanted.
Three riders, all of which decided this case:
* **The leaf's own justification for the stronger form was about the ROUTE, and routes are
  not consumers.** Here: "`2`-divisibility is the literal output of a `2`-descent". True,
  and it argues for a *convenient* statement, not a *necessary* one. Check whether the
  route still works over the weaker statement — it did, one extra step, via a lemma the
  file already had.
* **The lemma that made the stronger form cheap becomes FREE-FLOATING**, so the weakening
  costs you a deletion. Do it, and record the statement plus the `git show <sha>:<path>`
  recovery on its replacement, saying what would justify restoring it. Here that was
  `finite_of_fg_of_two_divisible` (fg + `2`-divisible ⇒ finite, by the determinant trick),
  worth restoring as a step to the new lemma the moment anything proves a `2`-divisibility
  statement.
* **Weakening a CONCLUSION is the one restatement whose falsity audits transfer** — a
  weakened conclusion cannot become false — but say WHY, and re-check the other two kinds:
  the NON-VACUITY witness usually narrows (here "even torsion" stopped refuting anything,
  that being exactly the strength given up), and an ATOMICITY verdict must be re-derived,
  since a weaker statement can admit a cut the stronger one did not.
**The receipt for a count-neutral recut is two lines and belongs in the commit**, because a
`−1 +1` warning-set delta is indistinguishable from "nothing happened":
    git diff -U0 -- <file> | grep -E '^[+-].*sorry'   # must be paired ±, one pair per leaf
    <comment-stripped sorry-token count and declaration count, before and after>
