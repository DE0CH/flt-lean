## A REFUTATION POISONS PROOFS, NOT STATEMENTS — compute the poisoned subgraph before deleting a tower
(2026-07-31, `flt-lean-124`, on `Threeadic.lean`.) `dc6836b9` did the right thing in
the right direction: `eq_one_of_smul_eq_mul_localInertia_connected_threeTorsion` was
refuted, so the cut walked UP its call graph to the lowest declaration whose own
statement is TRUE, sorried that, and deleted the `35` declarations below. The
deletion was verified carefully — exact sorry ledger, zero dangling references,
green builds of the module and all three importers — and every one of those checks
was correct.
**It deleted twice as much as the refutation touched.** Building the citation graph
of the pre-cut file restricted to the `35` deleted names and taking the transitive
closure of the false leaf's consumers gives **18 poisoned and 17 clean**. The clean
17 are ordinary proven theorems that were deleted only because they became
consumerless once the tower above them went — which is a consequence of the
deletion, not evidence for it.
**What you want is not the poisoned SET but its MINIMAL elements — where the poison
ENTERS.** The transitive closure necessarily swallows everything above an entry point,
including the theorem the cut was aiming at, so reading it as "all of this is unusable"
is exactly the mistake. Along the chain to the target the poison entered at just two
declarations; the four above them cite the false leaf only THROUGH those two, so
re-sorrying the two entry points restores all four with their original, previously
verified proofs. That moved the frontier from one bundled leaf to two crisp
coefficient-free ones, put ~840 lines of proof back in the tree, and left strictly less
open mathematics — at the cost of `+1` on the sorry count, which is the disclosure
trade this file already describes.
So the procedure when a leaf is refuted, before deleting anything:
    for each declaration D in the cone:
        poisoned(D)  iff  D cites the false leaf, or D cites a poisoned declaration
computed on the COMMENT-STRIPPED source of the pre-cut file, attributing each
citation to its enclosing declaration by walking backwards to the nearest header.
Delete the poisoned set; keep the clean set if anything still consumes it; and cut
at the *lowest poisoned* statements rather than at the lowest true one, because a
poisoned statement is usually still true and is a better leaf than the theorem three
levels above it.
Two corollaries that are easy to get backwards:
* **"Its proof used the false leaf" is not a falsity audit of its statement.** Both
  statements re-cut here are untouched by the recorded counterexample — one is about
  scalar-stability of a connected locus and the witness is about how wild inertia
  acts on a large socle. Check what the witness actually instantiates before
  concluding a statement went down with its proof.
* **A clean-but-consumerless proven theorem is worth listing by name in the cut's
  docstring**, with the fact that it is clean. Four of the 17 here were exactly what
  the restoration needed, and one — `le_span_singleton_sup_smul_pow_of_displacement_surjective`
  — carries a counterexample (`N = A·(1,0) + A·(0,3)` over `ℤ/9`) showing why the
  naive Nakayama step everyone reaches for is FALSE. That kind of content is
  unrecoverable in practice once it is only in a deleted range nobody remembers.

