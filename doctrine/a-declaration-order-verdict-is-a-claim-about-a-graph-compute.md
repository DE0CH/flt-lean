## A DECLARATION-ORDER VERDICT IS A CLAIM ABOUT A GRAPH — COMPUTE THE GRAPH, IT IS ONE SCAN
(2026-08-02, `flt-lean-246`, closing `exists_weilPair_of_heckeOp_smul` in
`ModularCurve/X0.lean`.)  This file already records that a leaf can be blocked by
declaration order rather than by mathematics, and that the repair is a relocation.
What it does not say is how to tell a relocation that is BLOCKED from one that is
merely LARGE — and the difference decides whether the honest shape of the remaining
work is "split an 119 000-line module" or "move one contiguous block".
That leaf's own docstring, and the section docstring above it, both said:
> All four ingredients live 10 000 lines BELOW this line, and **neither block can
> move past the other**, so a prover must first SPLIT this module.
The first clause was true.  The second was false, and it is exactly the clause that
is checkable.  Build the in-file citation graph — comment-strip, attribute each token
to its enclosing declaration, resolve by name and by dotted suffix — and compute two
closures:
* **UP** from the leaf: everything that transitively CONSUMES it (here 68
  declarations, 28 of them sitting between the leaf and the ingredient block);
* **DOWN** from the ingredient block: everything it transitively DEPENDS on (337).
**If those two sets intersect, the ordering is a genuine cycle and no relocation can
fix it.  If they do not, one of the two blocks may move past the other, and the graph
also tells you WHERE**: the deepest member of the DOWN closure is the earliest legal
insertion point.  Here the intersection was EMPTY and the deepest dependency was
5 000 lines above the leaf, so a single contiguous 2 124-line block moved up and the
leaf became a fifteen-line assembly over one clean citation.
Expect exactly the false positive this file already names: the only apparent
dependency in the way was the token `zero`, an `induction … with | zero` CASE LABEL.
Strip comments first or the scan is worthless — this project's docstrings quote Lean
constantly.
### A HOIST NEEDS FOUR CHECKS, AND THE THIRD IS THE ONE NOBODY RUNS
Moving code UP is the direction that can break the moved code, so the dependency scan
is necessary and it is NOT sufficient.  All four are seconds of scripting:
1. **Dependencies** — the DOWN closure's deepest member must be above the insertion
   point (above).
2. **Scope stack** — the enclosing `namespace`/`section` chain must be IDENTICAL at
   the source and the destination.  Here the obvious insertion point (immediately
   before the leaf) sat inside a `section CuspPeriodReduction` that the block was not
   in; the correct one was 550 lines earlier, where the stack matched.
3. **The active `open` / `attribute` environment**, which is what a naive scope check
   misses.  Three top-level-looking `open`s sat between the two positions
   (`open _root_.MeasureTheory`, `open _root_.CategoryTheory.Limits`,
   `open Limits MvPolynomial Algebra HomogeneousLocalization`) — every one of them
   inside a `section` that closed before the block, so the environments were in fact
   identical.  **That had to be computed, not assumed**: had any been at namespace
   level, the moved block would have lost names it resolves unqualified, and the only
   symptom would have been an `unknown identifier` after a 40-minute build.  Simulate
   the scope stack with a frame per `namespace`/`section`, collect `open`/`attribute`
   lines that do NOT end in `in` into the current frame, and compare the two snapshots.
4. **Name collisions** — no name declared in the block may collide with one declared
   between the destination and the source, or the intervening code's name resolution
   changes.
Also grep the block itself for `instance`, `attribute`, `@[simp]`, `notation` and
top-level `open`/`section`: any of those would change the environment for everything
between the two positions even if the four checks pass.  Here there were none — only
two `open _root_.Polynomial in` lines, which travel with their own declarations.
**Commit the move on its own, with the receipt**: `sort` of the file before and after
must be byte-identical and the line count unchanged.  That is a complete proof that
the commit is a pure permutation, which is the one thing a 2 000-line relocation diff
cannot be read for by eye.
### "X LIVES DOWNSTREAM IN MODULE M" IS A CLAIM ABOUT ONE MODULE
Same leaf, second stale obstacle, and it is the cheaper of the two to check.  The
docstring said `cuspForm_finiteDimensional` "lives downstream in
`Modularity/Interface.lean`", so a prover would have to hoist it.  It does live there
— and it ALSO lives in `ModularCurve/WeightTwoEigenform.lean`, which the file
`public import`s, and the file was already CALLING it 7 000 lines further down.
So the check is `grep -rn '<name>' Fermat/` — the whole tree, not the module the
docstring names — followed by `grep -n '<name>' <your own file>`.  A name that your
own file already uses is not missing from it, whatever a docstring says about where
it lives.  Same family as the standing rule that inventory audits understate what
exists, with the twist that here the audit named a real location and simply was not
the only one.
### THE SCRATCH SETTLES THE MATHEMATICS BEFORE THE RELOCATION IS ATTEMPTED
The order that made this cheap: a scratch module `public import`ing the UNEDITED
`X0.olean` sees BOTH the leaf and the ingredients regardless of their relative
position, so the whole assembly — and the exact statement of the residual leaf — was
written and verified at **9 seconds per round** before a single line of the file
moved.  The relocation then had nothing mathematical left in it, and its only risk
was the four mechanical checks above.  Do it in that order: a hoist debugged at the
same time as a proof is a hoist debugged at 40 minutes per iteration.
