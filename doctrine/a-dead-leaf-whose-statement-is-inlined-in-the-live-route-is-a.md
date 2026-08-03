## A DEAD LEAF WHOSE STATEMENT IS INLINED IN THE LIVE ROUTE IS A PROVE-AND-REROUTE, NOT A DELETE
(2026-08-02, `flt-lean-91`, `geomPic_exists_bcDiv_of_divAct_fixed` in
`ModularCurve/HyperellipticJacobian.lean`.)  The SEVENTH-class rule above — an OPEN leaf
that is also DEAD — prescribes deletion, and says so in bold: *"Deleting the dead pair is a
FULL result, not a consolation prize."*  That is right when the dead leaf's content is dead
too.  It is the WRONG move, and a lossy one, in the commonest way a leaf goes dead here:
**a re-cut re-proved the parent by another route and INLINED the dead leaf's statement into
the parent's body.**  Then the content is not dead at all — it is live, duplicated, and
sitting in a proof body where nothing can cite it.  Deleting the leaf drops the frontier by
one and leaves the duplication; proving it and rerouting the parent through it drops the
frontier by one AND removes the duplication, for the same effort.
Measured here: the leaf had **one** comment-stripped occurrence in all of `Fermat/` (its own
declaration), and its statement — "an invariant divisor is constant on the fibres of `below`,
hence a `bcDiv`" — was 28 lines inside `geomPic_descent`, which had been re-proved through
`geomPic_descent_divisor`.  Proving the leaf and calling it was `52 insertions, 35 deletions`
in one file, `22 → 21` sorries, and the parent's proof went from 33 lines to 6.
**The check, and it is the same grep you were going to run anyway:** when the consumer scan
comes back with only the declaration's own line, do NOT stop and delete.  Read the parent
that USED to consume it — named in the leaf's own docstring, or found by grepping the
conclusion — and ask whether the parent's body now contains the leaf's statement.  Three
outcomes, and only the first is a deletion:
* the parent no longer needs the statement at all ⇒ dead content, delete;
* the parent inlines it ⇒ **prove and reroute** (this section);
* the parent proves it under another name ⇒ the duplicate-cut case, delegate one to the
  other (the `merger`-side rule above).
**And check whether the leaf's stated input has since been PROVEN, because that is usually
why the re-cut happened.**  This leaf's docstring said transitivity "is the only thing
`GeomPic` does not already carry" — true when written, false since 2026-07-31, when
`placeAct_transitive` was proven and declared 265 lines ABOVE it.  So the leaf was provable
where it stood, and the whole task was a 45-line transcription of the parent's own inlined
block.  That is the standing rule about absence claims (*an audit's "the tree does not have
X" is a hypothesis*) arriving through a leaf's INPUT rather than through its route.
Two riders, both cheap:
* **The added hypothesis is free at a dead leaf.**  `hsep` had to be threaded in because
  `placeAct_transitive` needs it; a leaf with no consumers cannot have a call site broken,
  and the one consumer you are about to create already carried it.  Check that last clause —
  it is what makes the signature change cost nothing above the leaf.
* **Verify with BOTH counts, not one.**  The build's `declaration uses 'sorry'` warning set
  went `22 → 21` and the comment-stripped source `sorry` TOKEN count went `22 → 21`.  Equal
  deltas is what rules out an anonymous inner `sorry` having been swapped in for the named
  one — a `have … := sorry` inside the new proof would move the second count and not the
  first.
