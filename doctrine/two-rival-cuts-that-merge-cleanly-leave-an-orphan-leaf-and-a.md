## TWO RIVAL CUTS THAT MERGE CLEANLY LEAVE AN ORPHAN LEAF *AND* A DUPLICATE LEAF — and both look like ordinary open work

(2026-07-31, `flt-lean-96`, `HyperellipticJacobian.lean`.) The class-7 section warns that a
merge can split ONE edit across the conflict boundary. This is the other half: when two
branches decompose the SAME node in two different ways, and their leaves land in regions far
enough apart not to collide, the merge takes **both cuts in full**. Nothing conflicts,
nothing is dropped, the build is green — and the tree now permanently carries the loser's
leaves as work nobody will ever consume.

Measured here. `geomPic_bc_injective` was cut twice:

* cut **A** → `GeomPic.below_surjective` + `GeomPic.exists_emb_of_divisor_invariant`
  (packaged Hilbert 90), plus a proven `GeomPic.bcDiv_injective` over the first;
* cut **B** → `geomPic_below_surjective` + `_exists_const_of_divisor_eq_zero` +
  `_exists_finiteLevel` + `_exists_emb_of_fieldAct_fixed`, with the Hilbert-90 argument
  written out INLINE in `geomPic_bc_injective`.

What landed is a chimera: `geomPic_bc_injective` consumes cut **B**'s three analytic leaves
*and* cut **A**'s `bcDiv_injective`. So the survivors are `GeomPic.below_surjective`
(consumed) and three of B (consumed) — while `GeomPic.exists_emb_of_divisor_invariant` has
**no consumer at all**, and `geomPic_below_surjective` is `GeomPic.below_surjective`
**verbatim, declared ~500 lines away**. Two of the file's 25 sorried declarations were
phantom work, and every frontier scan counted them as ordinary leaves.

**Why nothing catches it.** The duplicate is not a duplicate NAME, so `check-dup` and
`xdup.py` are silent; the orphan compiles, emits its `declaration uses 'sorry'` warning, and
passes `own.py` and `leafstat.py`. The module's own dependency-tree docstring listed cut B's
four leaves and did not mention cut A's two at all — while the CODE used one of them. Only
grepping for CONSUMERS finds either.

**So, before proving any leaf: grep the file for uses of its own name.** One command, and it
distinguishes "open" from "open and worth closing":

    grep -n '<leafName>' <file>     # hits that are docstrings only ⇒ nobody consumes it

**The repairs are not symmetric, and the cheap one is not deletion.**

* *The orphan*: do NOT delete a true, audited statement. The winner's INLINE block is almost
  always your proof — cut B's STEPs 2–7 were `exists_emb_of_divisor_invariant`'s proof with
  one particular `ḡ` in place of the statement's `u`. Abstracting it closed the leaf over
  three leaves the consumer ALREADY depends on, so no `sorryAx` edge was added and the count
  strictly dropped. Deleting would have scored the same on the count and thrown away a
  reusable theorem.
* *The duplicate*: delegate, and **the direction is forced by which copy is CONSUMED.** Make
  the unconsumed name a one-line proof of the consumed one (`… := gp.below_surjective`), so
  the sole remaining leaf is the one the tree actually rests on. Backwards, a prover who
  closes the delegated name leaves the consumed copy open and moves nothing.

**The orphan usually cannot be proven where it stands.** Cut A's leaf was declared ~500 lines
ABOVE all three of cut B's, so its proof was not expressible at that point — Lean's linear
order, the declaration-order leaf class again. Relocating it is part of the repair; restate
it with explicit binders in the section-`variable` order (`{c₀ … c₅} {D} (gp) {u} (hu)
(hinv)`) and the signature is preserved to the character, so no call site can break.

**And the task prompt will describe the LOSING cut as current.** Mine said, in good faith,
"the consumer `geomPic_bc_injective` was proven over this leaf" — true on the branch that cut
it, false of what merged. A queue entry is written against the tree its author was looking at;
that a prompt names a real leaf with a real audit is no evidence its consumer story survived
the merge. Re-derive the consumer from the file, never from the prompt.

Bookkeeping note, since it is the shape that hides this work: the module went 25 → 23 sorried
declarations with **no new leaf and no mathematics done**. Neither closure was a proof of
anything; both were merge damage. Report it that way.

