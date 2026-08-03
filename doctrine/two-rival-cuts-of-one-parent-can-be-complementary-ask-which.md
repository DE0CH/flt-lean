## TWO RIVAL CUTS OF ONE PARENT CAN BE COMPLEMENTARY — ASK WHICH HALF EACH PEELED

(2026-07-31, release 33, `exists_obstructionCocycle_smallExtension_deformation`.)
CLAUDE.md already records how to CHOOSE between rival cuts (fewer open leaves
after; named beats anonymous; already-integrated wins ties).  Every one of those
tie-breaks presumes the two cuts are alternatives.  Often they are not.

Here merger had peeled the DEGENERATE branch of the leaf (`K = ker φ`, where the
small extension is an isomorphism), leaving `..._ne_zero`; `flt-lean-316` had
peeled the CONTINUOUS SET-THEORETIC SECTION, proving four lemmas and leaving
`..._of_section`.  Taking either side wholesale orphans the other's leaf and
strands its proven machinery — the class-7 interface split in rival-cut form,
and the outcome a textual merge produces by default.

**The check is to diff the two RESIDUAL STATEMENTS, not the two diffs.**  They
were identical except for the two extra hypotheses, so `..._of_section` plus the
PROVEN `hasUniformSections` implies `..._ne_zero` by dropping an unused
argument.  Keeping merger's parent proof, transplanting 316's block verbatim
above `..._ne_zero`, and proving `..._ne_zero` in eight lines banked BOTH peels
with nothing orphaned and the count unchanged.

**The tell that two cuts are complementary rather than rival: their residual
statements differ from each other in DISJOINT hypotheses.**  Rival cuts differ
in the CONCLUSION or in the same hypothesis; complementary ones each add a
different one, and then each implies the other's residue once its own added
hypothesis is discharged.  Diff the binder lists before deciding anything.
