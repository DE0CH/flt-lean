## A TARGET THAT EXISTS ONLY ON `merger` IS WORKABLE — AND A RED IMPORT CONE IS NOT A REASON TO STOP
(2026-07-31, `flt-lean-35`, on `exists_stepanovIrrationalLinearFormsField`.) The
release-window section above is written for one direction — *your target is already
PROVEN on `merger`*. The **mirror case** arrives just as often and nothing above covers
it: **the target does not exist on `main` at all**, because it was CUT on `merger` by a
decomposition that has not been released. `main` was 868 commits behind `merger` here,
and the leaf had been created by a decomposition the day before.
Task prompts built from a decomposition note routinely name such a leaf, and they tend to
carry an escape hatch — *"if the declaration is not in your tree, say so in the sentinel
and stop; do not re-derive it."* **Taking that hatch throws the whole run away for a leaf
that is perfectly workable.** The hatch is there to stop you re-deriving a released leaf;
it is not a verdict that the work cannot be done.
The move is one command: **`git merge merger` into your worktree branch and work there.**
Your diff then applies to the tree the merge worker actually holds, so merging back is
trivial, and the declaration you were sent at is right there. Basing on `main` instead is
strictly worse — you would have to re-create the declaration and its neighbours, which is
a guaranteed conflict against a tree that already has them, plus a rival cut on top. Say
in `to_merger` that the branch is merger-based and why, so the 800-commit ancestry is not
read as an accident. Stop only if the name is on neither `main` nor `merger` nor any batch
branch.
**SECOND, INDEPENDENT, AND THE ONE THAT LOOKS LIKE A BLOCKER: a red module anywhere in
your target's import cone makes your target unbuildable, and that is not your problem to
fix.** Release 27 was HELD because `ModularCurve/X0.lean` is red (see
`tools/merge/RELEASE-27-HANDOVER.md`), and `Modularity/Interface.lean` `public import`s
it — so `lake build Fermat.FLT.Modularity.Interface` cannot succeed for anybody, whatever
you write. Do not repair X0 (a multi-hour job with a named owner), and do not report the
tree as broken.
What you do instead: **find the largest GREEN module that carries every definition your
STATEMENT mentions, and verify the entire payload in a scratch module importing that
one.** Here every `stepanov*` definition the leaf names — `stepanovAnsatz`,
`stepanovUnknownCount`, `stepanovEquationCount`, `stepanov_equationCount_lt_unknownCount`,
`pow_X_sub_C_dvd_iff_hasseDeriv` — lives in `Modularity/MoretBailly.lean`, which the
release worker had already verified green. So six new lemmas and the reproof were
elaborated without `Interface.lean` ever being touched by the compiler.
Three riders, all of which cost something here:
* **Check the target's own context by READING, since you cannot build it**: the enclosing
  `namespace`, the `open`s in force at that line, and that every name you cite is declared
  ABOVE your insertion point. Strip comments before doing the namespace scan — this
  project's docstrings contain the words `namespace`, `section` and `end` in prose, and a
  naive stack machine reported a nesting depth of ten where the truth was two.
* **Say in `to_merger` that the payload is scratch-verified, not in-file verified**, and
  name the module it was verified against. That is a materially weaker claim than a green
  build and the merge worker must know which it is holding.
* The scratch must repeat the target file's `local notation` and non-`public` imports, and
  must NOT inherit `open`s the target does not have — mirror the target, do not minimise.
