## unreachable modules dark islands

(Cut verbatim out of CLAUDE.md's `THE GOAL: fully formalize Fermat's Last Theorem, no sorry, n` section at the 2026-08-03 doctrine split; nothing reworded.)

**Fourth category, invisible to ALL THREE: a module UNREACHABLE from
`Fermat.lean` is never compiled at all** (2026-07-27). `lake build` builds the
root's import closure. A module no module in that closure imports is simply not
built — so it is invisible to `lake build`, invisible to the
`declaration uses 'sorry'` warning set, and invisible to the transitive census.
It can contain anything, including code that does not compile, and nothing will
say so.

At `a18c5c4d` there were **99** such modules — the whole vendored
automorphic-form / adele / Haar closure, 1690 floating declarations. It is also
a hard blocker for the census, which imports *every* module under `Fermat/`:
one unreachable module that fails to build takes the census down with it. A
release has since wired almost all of them in.

**Root cause, found 2026-07-27 and deeper than a forgotten import: the island was
exactly the set of project files NOT on Lean's module system.** 277 of 286 files
declare `module`; the only non-`module` files were `Fermat.lean`, `Basic`,
`PrimeFive`, `SorryGate` — and the five unreachable ones. **A `module` file cannot
import a non-`module` one** (`cannot import non-module ... from module`), so the
island was *structurally unimportable by any consumer that could plausibly want
it*. Nobody forgot an import; the import was **not expressible**.

The fix is the header treatment its already-wired siblings use: `module`,
`public import`, `@[expose] public section`. So when a module looks orphaned,
check its HEADER before hunting for a missing consumer — and note that wiring an
island in correctly RAISES the reported frontier, because its sorries become
visible for the first time. That is disclosure, not regression.

**Do NOT over-read that into "every name you use needs a `public import`" — that
is false, and the false version has been sitting in a leaf docstring telling
agents to edit a 71 000-line header** (measured and corrected 2026-07-31). A
plain `import M` makes `M`'s names available for elaboration in the importing
module; `public` only controls whether they are RE-EXPORTED to that module's own
importers. Since **theorem proof bodies are elided by the module system**, a
`public theorem` may use privately-imported constants freely. What needs a
`public` edge is a name occurring in a **statement**, or in the body of a
`def`/`abbrev`/`instance` that `@[expose]` publishes.
`ModThree.lean`'s `exists_local_hopf_tensor_etale_algEquiv_of_finite_hopf`
carried the note "whoever takes this leaf must add
`public import Fermat.FLT.GroupScheme.ConnectedEtale` — a transitively-reached or
private import does not make the names available even in proof bodies". The file
had imported that module privately since before the note was written, and 300
lines of new public theorems calling into it elaborate green against exactly that
configuration. The one edge that did have to be `public` was
`Mathlib.RingTheory.HopfAlgebra.Quotient`, because `Ideal.IsHopfIdeal` appears in
two of the new STATEMENTS. Check WHERE the name occurs before touching a header:
the test is one `lake env lean` on a scratch module mirroring the target's import
lines, about ten seconds.

**So a fourth standing check belongs in every bookkeeping cycle: enumerate
modules under `Fermat/` and subtract the root's import closure.** A newly
vendored subtree is the usual way modules land here — vendoring a directory
does not wire it to anything, and the tree looks green precisely because the
new code is not being compiled.

**THE SECOND WAY A MODULE GOES DARK, and it is the commoner one now: BREAKING A
DUPLICATE-DECLARATION COLLISION BY DROPPING AN IMPORT.**  (2026-08-02,
`flt-lean-394`.)  When two branches land rival developments of one layer, the
symptom is `environment already contains …` at the single module that imports
both, and the cheapest repair is to drop one import.  That removes the collision
**from the build and not from the tree**: the dropped module becomes unreachable,
hence never compiled, hence free to hold `sorry`s that no build can see — and it
keeps the collision loaded for anyone who ever imports both again, including the
census, whose import block is regenerated from a scan of the whole tree.
`CurveDivisorDegree.lean` sat that way from release 31 to release 33, carrying
three invisible `sorry`s, and it is exactly the 380-vs-377 gap between
`tools/merge/frontier.py` and the compiler's warning set that release 33 recorded.

**So the fourth check has a companion reading: an unreachable module is not merely
un-wired, it may be a HALF-PERFORMED de-duplication, and the other half is a
decision somebody already made and did not carry out.**  Look for the note that
records it — here `X0.lean`'s own import block said in as many words which module
was kept and why, and ended "Reconciling the two modules is queued."  A queued
reconciliation that has been queued repeatedly is a decision nobody will ever be
dispatched to perform; per the FALSITY-AUDIT rule above, perform it.

**AND THE OBVIOUS REPAIR — DELETE THE DARK MODULE — IS THE ONE TO CHECK HARDEST,
BECAUSE ITS PREMISE IS A TREE SCAN AND THE TREE IS NOT WHERE THE ANSWER IS.**  All
three checks pass easily and all three are about THIS commit: nothing imports it
(so its declarations are unreferenceable by construction); every name unique to it
has zero code uses in a comment-stripped scan; and `lake env lean` on the file says
whether the content is even real (an unreachable module has never been compiled, so
"it has proofs in it" is a hypothesis — here it was true, 3 sorries and 0 errors).
I ran all three, they all said DELETE, and deleting would have been wrong: the
reconciliation had already been done **the other way** and was sitting committed and
unmerged on two branches, which strip the duplicated names, make the dark module
import the keeper, restore the dropped import, and — decisively — CONSUME the one
piece of content the keeper lacks, to close a leaf.

So the fourth check needs a fifth step, and it is the same command the section above
gives for a rival cut, pointed at branches instead of worktrees:

    for b in $(git branch --format='%(refname:short)'); do
      git show "$b:<the dark module>" 2>/dev/null | grep -q '<the marker of the repair>' && echo "$b"
    done

**"Zero consumers" is a claim about the tree you can see, and a dark module is
precisely the kind of thing somebody is repairing on a branch** — because it is
listed in the queue, and it has been listed there for several releases.  Grep the
QUEUE too: a queue entry describing the module's reconciliation *as already landed*
(mine said "X0 now imports it … this is the +3 that release 34's frontier will
show") is written from a branch, and is the loudest possible signal that the work
exists somewhere you have not looked.

When the answer really is delete, record in the note the sha to `git show` it back
from and the one piece of content the keeper lacks, with the condition that would
justify resurrecting it.  A deletion that collides with such a branch is a
modify/delete conflict against work that proves a theorem, and `semmerge.py`
propagates additions and never deletions — so the outcome is not decidable from
the diff, which is the worst thing to hand a merge worker.

**AND WHEN IT IS NOT, DO NOT WRITE THE WARNING WHERE THE REPAIR WILL LAND.**  The
obvious place to record "this module is dark, do not delete it" is the import block
that dropped the import — which is EXACTLY the region the repairing branch rewrites,
so the note is a guaranteed textual conflict with the work it endorses, and is stale
the moment that work merges.  I wrote one there and had to take it out; `merge-tree`
found it in seconds:

    git merge-tree --write-tree --name-only HEAD <the repairing branch>   # exit 1 = conflict

**Run that against every branch your edit's subject matter names, not just against
`merger`.**  Mine was clean against `merger` and conflicted with both repair
branches, which is the combination that looks safest and is worst.  A warning about
a transient state belongs in `to_merger` (read exactly when the decision is made)
and in CLAUDE.md (durable, and it merges cleanly because nobody else edits your
paragraph); a docstring is for what stays true.  What survived from that edit was
the one clause that is true either way — an inventory bullet elsewhere had listed
`finite_divSupport` as PROVEN when it is a `sorry`, and no branch touched it.

Two things worth measuring rather than assuming while you are there.  **An import
scan must not anchor at end-of-line** — `import Fermat.X -- why` is a real line in
this tree and an `$`-anchored regex silently drops the edge, which manufactures a
phantom unreachable module.  And **the inventory bullets that name such a module
go stale in both directions**: the one in `Interface.lean` listed
`finite_divSupport` as PROVEN when it is a `sorry`, so a prover would have built on
it.  Re-measure a proof-status claim by attributing `sorry` tokens to enclosing
declarations, never by reading the bullet.

