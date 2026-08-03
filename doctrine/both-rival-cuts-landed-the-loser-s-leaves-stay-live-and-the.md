## BOTH RIVAL CUTS LANDED: THE LOSER'S LEAVES STAY LIVE AND THE WINNER'S *ASSEMBLY* GOES FREE-FLOATING

(2026-08-01, `flt-lean-315`, `RelativePicard.lean`.)  The duplicate-cut sections
below tell you how to DETECT two cuts of one node.  This is the shape they take
when the two cuts are each **two leaves plus an assembly**, and it costs twice as
much as the one-leaf case because the damage is symmetric:

* a 2026-07-30 branch cut the node into `exists_relPicZeroGroupScheme` +
  `isProper_of_relPicZeroGroupScheme`, glued by a bespoke structure;
* a 2026-07-31 branch cut the SAME node into `exists_relPicIdentityComponent` +
  `isProper_relPicIdentityComponent`, assembled by `exists_relPicZeroSubfunctor`;
* the two landed in regions far enough apart not to conflict, so the merge kept
  **both**, and resolved the ONE line they share — the parent's proof body — to
  the 07-30 side.

Result: **four open leaves where two suffice**, and — the half nothing else
reports — the winning cut's assembly `exists_relPicZeroSubfunctor` PROVEN with
**zero consumers anywhere in the tree**, i.e. free-floating.  Every instrument
agreed the tree was healthy: green build, four honest `declaration uses 'sorry'`
warnings, `own.py`/`leafstat.py` correctly reporting all four unowned and open.

**TWO detectors, and run both — either alone is weak.**  The docstring/body
mismatch (below) found it here; the second is cheaper and keyed on the winner
rather than the loser: **a PROVEN theorem whose only comment-stripped occurrence
is its own declaration.**  A proven assembly with no consumer is not merely dead
code — it is the receipt that its cut lost a merge it should have won.

    python3 - # strip /- -/ and -- , then count \bNAME\b per file
    # 1 occurrence for a PROVEN theorem  =>  free-floating  =>  look for its rival

**CHOOSING BETWEEN TWO CUTS OF EQUAL LEAF COUNT.**  The standing tie-breakers
(fewer OPEN leaves; already integrated and consumed) do not separate a 2-vs-2
tie, and "already consumed" actively points at the LOSER, since the merge wired
the parent to it.  What separated them here, in order of weight:

1. **What each leaf asks of its OWNER.**  The 07-31 leaves do not demand the nine
   group axioms — those are transported at the assembly, and none of them is
   geometry.  The 07-30 leaf handed its owner a whole `RelGroupSchemeStruct` to
   build.  Same count, strictly less owed.
2. **Whether the junk witness dies ON THE LEAF or by appeal to construction.**
   `isProper_relPicIdentityComponent` receives its sibling's full conclusion
   including `GeometricallyConnected jstr`, so `J = P` is refuted by a
   hypothesis.  `isProper_of_relPicZeroGroupScheme`'s own docstring admitted it
   "may NOT be proven from `_hincl` alone; a prover must use how `J` was
   constructed" — an admission that the leaf is stated in a form its owner
   cannot discharge.
3. **Which audit carries a proof plan.**  One had five numbered steps; the other
   had a paragraph.

**And check a docstring's junk witness against the WHOLE hypothesis list before
believing it refutes anything.**  That same docstring claimed non-vacuity because
"`J = P`, `incl = id`, `G` the group data of `Pic` itself satisfies
`IsRelPicZeroIncl` in full" — which reads as a self-refutation and nearly got the
leaf reported FALSE.  It is not: the existential also demands
`G : RelGroupSchemeStruct jstr`, whose `connected` field `Pic` fails (one
component per degree).  The witness satisfies the named PREDICATE and not the
STATEMENT.  Same family as the standing rule that a counterexample is only as
strong as the hypothesis list it was tested against — here the untested
hypothesis was in a *different conjunct of the same existential*.

**The repair is cheap and the count is the wrong measure of it.**  Writing the
transport the winning cut always intended — `ab.add p q` is the unique preimage
of `hP.addPoint (incl p) (incl q)`, existing by the closure clause and unique by
`hinj`, every axiom `hinj` applied to a `simp only [hA, hZ, hN]` chain ending in
the corresponding proven law on `Pic` — was ~25 lines and compiled first try in a
scratch.  Frontier 4 → 2, **no mathematics done and none newly owed**.  Say that
in the commit: a `−2` from a merge repair reads exactly like a `−2` from proving
something, and only one of them means the project moved.

