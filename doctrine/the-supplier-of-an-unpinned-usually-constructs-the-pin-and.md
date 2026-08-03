## THE SUPPLIER OF AN UNPINNED `∀` USUALLY *CONSTRUCTS* THE PIN AND THROWS IT AWAY — READ ITS PROOF, NOT ITS CONCLUSION
(2026-07-31, `flt-lean-162`, `ModularCurve/X0.lean`.) This file records at length that a
leaf quantified over an UNPINNED bundled pair is the shape in which a false sub-leaf hides,
and it records the repair — pin the pair — as something to reach for only *after* a
refutation, because pinning is assumed to cost an interface change through every consumer.
**That cost is usually not paid at the leaf's own supplier, and the check is one read of the
supplier's PROOF.** `exists_cuspidalAbelianSievePrime_oneSixtyNine` was universal over a
rank-`0` abelian image `(A, c)` constrained only by `hfin` and `hcinj` — flagged in its own
docstring as "UNVERIFIED rather than established", and by the audit above it as "the only
place in this chain where a false sub-leaf could hide". The single theorem that supplies
the pair, `exists_x0AbelianNeronDatum_oneSixtyNine`, does not merely *satisfy* a much
stronger condition: it **builds the pair out of it**, by
`exists_albaneseQuotientAbelianImage`, and then defines
`c := fun T g x => RelPoint.post π hπ (jac.aj g x)` on the nose. So exporting `c = π ∘ aj`
with `π` SURJECTIVE cost one conjunct in the conclusion, `fun _ _ _ => rfl` in the proof,
and one `hsurj` that was already in hand and being discarded. Nothing above the sieve moved.
**The generalisable procedure, and it is cheap:**
1. find the leaf's supplier — the theorem that produces the object the `∀` ranges over;
2. **read its proof body, not its statement.** A supplier that `obtain`s its object from a
   richer `∃` and then re-packages it into a thin `def` is throwing away exactly the pin you
   want. The tell is an `obtain ⟨…, hextra, …⟩` whose `hextra` never appears again;
3. export what it already has as one extra conjunct, and add it to the leaf as a hypothesis.
   If the supplier *defines* the object rather than choosing it, the new clause is `rfl`.
**Say in the commit that the count did not move, and say what got smaller.** This is `1 → 1`
and looks like nothing happened. What changed is that the recorded *reduction* of the search
space — three careful prose paragraphs headed "the `∀` search is BOUNDED" — became a
hypothesis of the statement instead of a comment beside it, and one of its three steps
(the ambient-torsion bookkeeping) became unnecessary outright.
**And pin only as far as it is FREE; name the rest and queue it.** The strictly stronger pin
here (the Atkin–Lehner Prym) needs the shared `def` the supplier consumes to grow three
fields, and that `def` is used at two other levels and by an unrelated theorem — a real
interface change in the most contended file in the tree. Taking the free half and writing
down precisely why the other half is not free is a better outcome than either doing all of it
badly or doing none of it: the next owner inherits a decision, not a question.
**A rider on faithfulness, because a pin is not a proof of faithfulness.** Re-run the leaf's
recorded refutation mechanism *under* the new hypothesis and report what survives. Here the
pin kills the cheapest version of the mechanism (the `w`-quotient family of quadratic points
produces a `w`-ANTI-invariant class, which the surjection cannot kill) and does not kill all
of it (a projection onto one simple factor still admits a codimension-`2` coincidence). Both
halves belong in the docstring; a pin advertised as settling the question when it merely
narrows it is the same failure as an audit labelled "inherited" with no argument.
