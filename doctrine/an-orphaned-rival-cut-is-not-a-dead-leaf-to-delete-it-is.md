## AN ORPHANED RIVAL CUT IS NOT A DEAD LEAF TO DELETE — IT IS USUALLY THE BETTER LEAF, AND YOUR TARGET IS THE ONE TO PROVE OVER IT

(2026-07-31, `flt-lean-183`, `ModularCurve/X0.lean`'s Weil-extension cluster, and it took
the cluster from two open leaves to one without proving any mathematics.)

The rival-cut sections above tell you how to DETECT an orphan (grep your target for code
consumers; read the parent's `by` block rather than its docstring) and how to DISPOSE of
one (delegate, do not re-prove; delete a consumerless duplicate). Both readings assume the
orphan is the loser. **Very often it is the WINNER, and the right move is to prove your own
assigned target over it.**

The instance. `exists_weilExtension_of_abelianScheme` was cut twice in one day: on
2026-07-30 into a LOCAL one-point step (`exists_localExtension_of_abelianScheme`) plus a
noetherian induction and a gluing lemma, and on 2026-07-31 into a PURITY statement
(`exists_weilExtension_purity`, EGA IV₄ 20.4.12). The two cuts touch disjoint regions, so
the merge took both; the parent kept the purity proof; and the 2026-07-30 leaf was left
with **zero code consumers**, dragging `exists_hom_of_forall_enlargeOpen`,
`exists_hom_sup_of_agree`, `openCoverOfSup` and `noetherianSpace_of_isProper` — about 250
lines of PROVEN machinery — into free-floating code with it. Every instrument reported two
ordinary open leaves for one theorem, and the dispatcher (correctly) sent an agent at the
live one.

**The tie-break is not "which cut is live" but "which residual statement is more
attackable", and the two are usually equivalent so you are free to choose.** Here purity ⟹
local (via the parent, taking `V = ⊤`, which the local leaf's own docstring already
recorded) and local ⟹ purity (the proof written that day), so nothing is gained or lost
mathematically; what decides it is that the local statement asks for a morphism on ONE
neighbourhood of ONE point and can therefore be met inside a single local ring, which is
the shape every textbook proof of BLR 4.4/1 has. Proving the live target over the orphan
therefore closes a leaf, revives the machinery, and leaves the better statement open.

**The proof of the live target over the orphan is usually SHORT, because the orphan came
with its assembly.** A cut that was made and then stranded still has its glue sitting
beside it. Here the whole of it was: split on whether the complement already carries a
codimension-`≤ 1` point (if so, take `V = U` and the purity clause is discharged by that
point, with nothing extended at all); otherwise the codimension bound holds at every
enlargement, so the orphaned leaf feeds the orphaned induction and returns a global
morphism, and `V = ⊤` makes the purity clause vacuous. Twenty lines, first compile.

**Three things to do while you are there, all cheap and none of them optional.**

* **Check the ORDER before planning the proof.** An orphaned cut is routinely declared
  BELOW the rival that displaced it — mine was 250 lines below — so proving the rival over
  it needs a RELOCATION. Move the block you are editing anyway (here the purity theorem,
  whose docstring you are going to rewrite in any case) rather than the untouched one, and
  say in `to_merger` exactly which lines moved where.
* **Correct the parent's docstring, which is the thing that hid this.** It said "PROVEN by
  noetherian induction and gluing over `exists_localExtension_of_abelianScheme`" while its
  `by` block called the purity leaf. Once the two are chained rather than rival, every
  clause of that paragraph is true again one link further down — say so in place, instead
  of deleting a correct account of a cut.
* **Report the delta as merge repair, not as mathematics.** `2 → 1` open leaves and nothing
  proven. A reader who sees only the count will otherwise believe a theory gap closed.

**AND THE ROUTE NOTE ON THE LEAF YOU CLOSE MAY BE RETIRED BY YOUR OWN PROOF — check, and
say so.** The purity docstring spent sixty lines on `IsReduced XZ`, because its recorded
route went through mathlib's `Scheme.RationalMap.domain` / `RationalMap.toPartialMap`,
which carry `[IsReduced X]` and `[Y.IsSeparated]` as instance hypotheses — and then on the
fact that this pin has no `Smooth ⟹ GeometricallyReduced` (re-verified: still absent; the
only `Group/Smooth.lean` statement points the other way). Every word was true and **none of
it was needed**: the maximal domain of definition is never constructed, so no reducedness,
no separatedness and no `PartialMap` API enters. A missing-machinery paragraph is scoped to
the route its author had in mind, and a different route can retire it outright — but check
whether the SIBLING it was also blaming still needs it (here
`exists_neronExtension_atSpecialGenericPoint` genuinely does, for a different reason), and
retire only what you actually retired.

**A hypothesis your proof stops using is not automatically to be dropped.** `hdense` became
unused, and dropping it would have orphaned `dense_of_codimTwo_compl`, the 30-line topology
lemma the consumer calls to produce it. Underscore the binder so the emptiness is
mechanically visible, keep the signature so no call site moves, and write down what would
justify removing it later.

**AND EXPECT A SECOND AGENT TO BE DIAGNOSING THE SAME ORPHAN, WITH THE OPPOSITE REMEDY.**
An orphan is conspicuous once anyone looks, so it draws more than one diagnosis at a time —
`flt-lean-22` found this one the same day and resolved it by DELETING the orphaned leaf and
leaving the four helpers consumerless, which is the other defensible move. **A union merge
of the two is RED**, because one branch's proof calls the declaration the other deletes. So
whichever side you take, (a) grep the other worktrees' UNCOMMITTED diffs for your cluster
before you commit — `git -C ~/flt-lean-N diff -U0 -- <file> | grep '^@@'` over the pool
costs seconds and is the only thing that sees this — and (b) say in `to_merger` that the two
are mutually exclusive and must be resolved WHOLESALE, never hunk by hunk. The tie-break to
quote is the project's own: same leaf count either way, so prefer the side that leaves less
in the leaf and leaves nothing free-floating.

