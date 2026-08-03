## TWO LEAVES CITING ONE CLASSICAL THEOREM NEED NOT BE MERGEABLE — DIFF THE BINDER LISTS
(2026-08-02, `flt-lean-120`, `Modularity/MoretBailly.lean`.) The standing rule *"AN
'IRREDUCIBLE' VERDICT SEARCHES FOR A PROOF. CHECK FIRST WHETHER A SIBLING LEAF ALREADY IS
ONE"* prescribes the right search — grep the file's DOCSTRINGS for the name of the classical
theorem, not for identifiers — and then states a conclusion that is too strong: *"either one
implies the other or the two should be merged; either way the second `sorry` is not a second
obligation."* There is a third outcome and it is common.
`MoretBailly.lean` carries **two** Bertini-irreducibility leaves, 19 000 lines apart, both
citing *Jouanolou, Théorèmes de Bertini et applications, Thm 6.3*:
`exists_bertiniIrreducibleLocus_isAlgClosed` (scheme-theoretic, a good LOCUS of hyperplanes
for an integral affine algebra) and `exists_plane_irreducible_planeSection` (polynomial, ONE
good `2`-plane for an irreducible hypersurface). They share no identifier, no type and no
statement shape, so no duplicate scan can pair them and neither docstring mentions the other.
Only the bibliography matches — which is exactly what the standing rule predicts.
**And neither implies the other.** The check is one read of the two binder lists:
* the scheme leaf carries `[CharZero K]` and `[Algebra.Smooth K A]`; the polynomial leaf has
  neither, its only call site is in characteristic `p`, and `V(h)` for an arbitrary
  irreducible `h` is singular. So it cannot discharge the polynomial leaf;
* the polynomial leaf produces ONE plane for a HYPERSURFACE; the scheme leaf needs a good
  LOCUS for an ARBITRARY integral affine algebra. So it cannot discharge that one either.
So the duplication is in the WORK, not in the statements, and the finding is still worth as
much as a merge would have been: whoever is dispatched at either must be told about the
other, and what should actually be proven is the common statement (an integral affine variety
of dimension `≥ 2` over `K = K̄` has an irreducible general hyperplane section, in every
characteristic), once. **Record the relationship in BOTH docstrings; do not force a merge and
do not delete either leaf.**
Corollary, and it is what makes the finding cheap: **the CITATION is the join key.** Grep
`Fermat/` for the author and theorem number — `Jouanolou`, `Schmidt Chapter V`, `EGA IV
9.7.7`, `Stacks 0`… — rather than for vocabulary. Two independently-cut leaves share their
bibliography and nothing else, and a bibliography grep costs one command.
Second corollary, from the same pair: **one leaf's docstring can name an obstruction the
OTHER leaf does not have.** The scheme leaf lists two missing inputs — geometric
irreducibility of the generic fibre, and the generic-to-special passage (EGA IV 9.7.7,
absent from the pin). The polynomial leaf owes only the FIRST, because it asks for one plane
rather than a locus and this module's own PROVEN Noether forms carry generic to special. So
reading the sibling's obstruction list told the smaller leaf which half of it applied, which
is the sort of thing neither docstring could say while they were invisible to each other.
