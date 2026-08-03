## A "MERGE THESE TWO LEAVES" TASK DIES THE MOMENT EITHER LEAF CLOSES — AND A STALE HEADER IS WHAT WRITES IT

(2026-08-01, `flt-lean-290`, on the two `Γ₁(N)` cusp leaves in `ModularCurve/X1.lean`.)

The fusion move this file endorses in several places — two leaves citing ONE sentence of
one reference become one leaf — has a precondition nobody states, because it is too
obvious to write down: **both leaves must still be open.** A fusion proposal is therefore
the most perishable kind of queue entry there is, since it is invalidated by the ordinary
success of either half, and its author cannot see that coming.

Here the task named `exists_rationalCuspSectionsX1_field` and
`exists_cuspSymbolEmbedding_x1_finiteField`, with a fully worked structure design and the
correct warning *"DO NOT LAND THE STRUCTURE WITHOUT BOTH DERIVATIONS — with only one, the
leaf count is unchanged and the change is a rename"*. The second leaf had been **PROVEN
the previous day**, re-cut into `exists_geometricCuspEquiv_x1_finiteField`. So the
prescribed work was exactly the rename its own prompt forbade, and landing it would also
have re-cut a leaf that was hours old — the rival-cut hazard, in the file with the most
concurrent editors in the tree.

**THE HEADER IS WHAT GENERATED THE TASK, AND THE HEADER IS ONE LINE.** The 2026-07-31 cut
proved the declaration, moved its content to a new leaf, and appended an accurate account
of the change *lower down the docstring* — while leaving the FIRST LINE reading
`(sorry leaf — the hard direction of Ogg's description …)`, and leaving an
`AXES SEARCHED` paragraph written for a leaf that no longer existed. Queue entries and
task prompts are written from opening paragraphs. So:

* **when a cut CLOSES a declaration, edit the first line of its docstring in the same
  commit.** Appending "PROVEN, see below" three paragraphs down is invisible to everything
  that reads this tree at scale;
* **an `AXES SEARCHED` block on a now-proven declaration must be relabelled**, not left to
  read as live open-work analysis. If the axes migrated to the new leaf, say so and name it.

This is the standing stale-`(sorry leaf)` hazard already recorded above, with the cost
measured one step further along: it does not merely mislead a reader, it **manufactures a
dispatched task whose premise is dead**, and the agent that receives it cannot tell from
the prompt.

**The check, for whoever RECEIVES a fusion task, and it is two commands:**

    python3 flt-frontier.py | sed -n '/<your file>/,/^$/p'   # both names must appear
    git show merger:<the file> | grep -n '<each name>'       # and on merger too

If either name is absent from the frontier, **stop and re-derive the accounting before
editing anything**. The honest deliverable is then the audit plus the header repair, not
the merge — and say in the leaf's own docstring which merge was declined and why, because
the next queue generator will otherwise write the same task again.

**And when you decline a fusion, price the REVISED fusion explicitly rather than leaving
it implied.** With one half closed, the natural fallback is to fuse the surviving leaf
with whatever the closed one was re-cut into. That is a genuine question and it usually
has a genuine answer: here the two survivors are the same Deligne–Rapoport sentence at
DIFFERENT GENERALITIES (a general base field, and `𝔽_ℓ` with Frobenius), and merging them
needs Galois descent — "a `Gal`-fixed geometric point is rational" — which is a second
obligation, so the trade is `2 → 2` with both survivors larger. **A fusion across a
generality gap is not a fusion; it is a fusion plus a descent leaf.** Check for that gap
before costing one: the tell is that the two leaves' hypotheses differ by more than the
base object — one mentions a Frobenius, a finite field, or a specific automorphism, and
the other does not.

