## TWO RIVAL CUTS OF ONE CLUSTER, BOTH MERGED, IS A CYCLE THAT LOOKS LIKE TWO INDEPENDENT SORRIES

(2026-07-31, `flt-lean-334`, `HopfAlgebra/ShortExact.lean`.) The task said "`flat_finrank_cartierDual`
is the ONLY sorry in that file". On `merger` the file had **two**, and the second was not a new leaf
— it was the *old* root of the same cluster, re-introduced by merging a branch that predated the
re-cut. Both routes were mathematically fine. Together they were a **cycle**:

    route A:  exists_lift_span_sup_jacobson  ->  exists_lift_ker_le_span  ->  exists_spanning
                                             ->  exists_basis_cartierDual
    route B:  flat_finrank  ->  nonempty_basis_chooseBasisIndex  ->  exists_lift_ker_le_span  -> ...

Each route derives the other's root from its own. Lean cannot see the cycle, because declaration
order breaks it: whichever root is textually first is a `sorry` and the other is "open" too, so the
file simply carries **two** obligations where it should carry one. Nothing is red. No frontier scan
flags it. Every `declaration uses 'sorry'` warning is honest. It reads as ordinary decomposition
progress, and it is the exact opposite — the merge DOUBLED what the file owes.

**The tell is that the two sorries are visibly about the same mathematics**, and that one of them
has a docstring deriving the other. Whenever a file has two open leaves whose docstrings each cite
the other as the thing they replace, suspect this and check the merge-base: one of them almost
certainly arrived from a branch that forked before the re-cut.

**The resolution rule, and it is decidable rather than a matter of taste: keep the arrangement whose
root leaf is IMPLIED by the rival's root.** That leaves the file owing strictly less. Demote the
rival's declarations to PROVEN corollaries placed below the shared cut, and say in their docstring
that they are corollaries and why moving them back up is a cycle. Here `flat_finrank_cartierDual`
(flat + constant fibre rank) implies the Jacobson generation leaf, so the Jacobson leaf was kept as
the root and `flat_finrank_cartierDual` was closed in ~10 lines from `exists_basis_cartierDual`.
Net: one file, two sorries -> one sorry, and the survivor is the weaker obligation.

Corollary for dispatch: **"the only sorry in that file" in a task prompt is a claim about the commit
the prompt was written against, not about your tree.** Regenerate it — strip comments, grep `sorry`
tokens, compare against the build's warning set — before believing the file has the shape you were
told.

