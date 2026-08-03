## THE `merger` CHECK GIVES A FALSE GREEN LIGHT — THE RIVAL CUT IS UNCOMMITTED IN ANOTHER WORKTREE

(2026-08-02, `flt-lean-394` and `flt-lean-384`, on
`exists_toAffineLine_of_iso_sectionIdeal`.  Two agents produced the same recut,
independently, on the same day, down to the new NAME and the proof body.)

Everything the release-window sections prescribe was run and every answer was
GREEN: `git rev-list --count HEAD..main` reached `0`; `git show merger:<file>`
showed the target still `sorry`; `X0.lean` was byte-identical between `main` and
`merger`; a comment-stripped tree scan showed the target had zero consumers, so
it really was a dead leaf worth re-pointing.  All correct, and all irrelevant —
**the rival cut was uncommitted in a sibling worktree, so no branch, no `merger`
copy and no scan of the object store could contain it.**

What the two runs produced, independently: the same rename
(`exists_toAffineLine_of_iso_sectionIdeal` →
`exists_toAffineLine_of_constSmul_sectionIdeal`), the same restated hypotheses
(`f`, `e`, `_hf` in place of the bare `Nonempty` iso, plus the `IsIntegral`
instance), and the same eight-line assembly closing the sibling leaf over
`isFinite_toAffineLine_of_isValuativelyFull` — matching to the `haveI` lines and
the final `exact ⟨U, ι, φ, hopen, hdom, …⟩`.

**So run the WORKTREE scan beside the `merger` scan, as a first action.**  The
fifth-invisibility-class section already gives the command; it is written as
advice to a dispatcher, and it is the PROVER who needs it, because the prover is
the one about to write the duplicate.  Restrict it to the paths you will touch
or it takes minutes:

    cd ~; for d in flt-lean-*; do
      u=$(git -C "$d" status --porcelain -- <the files you will edit> 2>/dev/null)
      [ -n "$u" ] && echo "WIP $d"; done
    # then, per hit: git -C "$d" diff | grep -n '<your target name>'

**And the risk is HIGHEST exactly where the task looks cleanest.**  The intuition
is backwards: a vaguely-specified leaf gets attacked twelve different ways, while
a leaf whose docstring names the seam, the machinery and the residue admits
essentially ONE repair — so two competent agents dispatched near it converge on
the same characters.  Convergence is reassuring about the mathematics and is
still one worker-cycle thrown away.  Here the leaf's own docstring named the
sibling, the sorry-free finiteness theorem and the exact three obligations; there
was nothing else to do.

**When you find you are second, decline your OWN payload — even when yours is
verified and theirs is not yet committed.**  The tie-break is not who compiled
first: two proofs of one theorem cannot both be carried, the names collide, and a
merge worker resolving that has no author to ask.  Landing mine would have traded
a clean single-region diff for a conflict in the most-edited file in the repo over
identical content.  Say in `to_merger` which worktree holds the incumbent, that
you verified the incumbent's own assembly compiles, and what your independent
derivation confirms — a second, independent arrival at the same cut is real
evidence and is worth recording even though the code is not.

Corollary, and it is what made the run pay for itself anyway: **a declined cut
frees you to take the neighbouring work the incumbent explicitly is NOT doing.**
The incumbent's own docstring listed the residue ("what is left is TWO items");
one of them was the divisor-degree layer, in two different modules, one of which
turned out to be unreachable from `Fermat.lean` and deletable.  Read the
incumbent's diff for the residue it names and take that, rather than looking for
a fresh target.

