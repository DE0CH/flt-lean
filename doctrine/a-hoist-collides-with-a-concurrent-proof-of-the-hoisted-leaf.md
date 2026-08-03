## A HOIST COLLIDES WITH A CONCURRENT *PROOF* OF THE HOISTED LEAF — MOVE THE PROOF, NOT THE STATEMENT

(2026-07-31, `flt-lean-86`.) Closing `cuspForm_coe_eq_zero_of_ellipticSturm`
(`ModularCurve/X0.lean`) required HOISTING two leaves out of
`FreyCurve/MazurTorsion.lean`, which is downstream — an `X0.lean` theorem cannot cite
`MazurTorsion.lean`, and both files' docstrings had already prescribed the move. At
that same moment `flt-lean-104` held **369 uncommitted lines in `MazurTorsion.lean`
proving one of the two** (`numCusps_le_order_qExpansion_norm`). Neither agent could see
the other from any branch: the hoist was uncommitted here, the proof was uncommitted
there.

This is not the ordinary same-file collision the fleet is designed for and git handles.
A hoist changes WHERE a declaration lives; a proof changes what its body is. Textual
merge succeeds and produces the declaration in **both** files — a `has already been
declared` hard error that neither diff predicts when read on its own.

**The resolution is asymmetric, and should be applied without deliberation: keep the
hoisted LOCATION and move the PROOF to it.** A statement is what conflicts; a proof
transplants, because a hoist copies the statement verbatim. Restoring the declaration
downstream to keep the proof where it was re-breaks the upstream theorem the hoist
existed to enable, and re-sorrying it upstream manufactures a duplicate leaf — strictly
worse than either branch alone.

If a helper the proof depends on genuinely cannot move upstream, move it FURTHER up
rather than giving up the hoist: `Modularity/HeckeOperator.lean` sits above `X0.lean`
and its own docstring says it exists to host the "norms/traces to level 1" theory.

**The general form, which is the part worth keeping:** before hoisting a declaration out
of a file, grep the *uncommitted diffs* of every claimed worktree for its NAME, not for
the file. `own.py`'s fourth check does exactly this, and this is the case it was written
for — a leaf you are about to relocate is precisely the kind of thing somebody else is
about to prove.

**RESOLVED 2026-07-31 (same worktree, next agent), and the resolution is cheaper than the
rule above suggests — because a hoist's payload is a STATEMENT, so the rival PROOF is
never wasted.** By the time the hoist was picked back up, `flt-lean-104`'s work had landed
on `merger` (`Fermat.relIndex_gamma0GL` *and* `Fermat.numCusps_le_order_qExpansion_norm`,
both PROVEN in `MazurTorsion.lean` over ~1470 lines of new development). So the collision
was no longer symmetric — one side was committed and one was not — and the merge
worker's tie-break rules would have picked the committed side, i.e. would have DISCARDED
the hoist and re-opened `cuspForm_coe_eq_zero_of_ellipticSturm`.

What was done instead: the whole 1478-line development was moved verbatim into `X0.lean`
at the hoisted location, its `Fermat.`-qualified declarations re-namespaced to sit inside
that file's `namespace Fermat`, and `MazurTorsion.lean` keeps only the one-line
`ν₂ = ν₃ = 0` corollary.

**COUNT THE FRONTIER, DO NOT ASSERT IT — this section first claimed `−2` and the true
figure is `0`** (corrected 2026-07-31, same worktree, by counting the two modules'
`declaration uses 'sorry'` sets against release `7080929d`: `X0.lean` `101 → 103`,
`MazurTorsion.lean` `39 → 37`). The `−2` was measured against a base that does not
exist — one where `flt-lean-104`'s proofs had landed *and* the hoist was free. Split by
author the honest numbers are `+2` for the hoist alone, which must carry the statements
up as fresh `sorry`s, and `−2` for the rival proofs alone; landing them together cancels.
This is the same trap CLAUDE.md already warns about two sections up, arrived at from the
other direction: a *decomposition*'s net is as easy to overstate as a release's, and the
temptation is worse because the author knows the work was real. **The argument for a
merge like this one is never the count** — it is that ONE opaque leaf naming four
ingredients in prose became THREE concrete leaves each with a route and a refutation
test. Say that, and give the count separately and correctly.

The move cost one splice and one build because a proof of `X` in file `F` depends
only on things upstream of `X`, and a hoist by construction moves `X` upstream — **so
the proof's own import cone always moves with it.** The only things that can block the
transplant are (a) helpers defined *downstream* of the destination, and (b) `import`s the
destination lacks; (b) was ten mathlib modules and is mechanical.

**Two checks make the transplant safe, and both are cheap.** Before splicing, list every
declaration the moved block introduces and grep the destination for a collision — the
destination here has 74 000 lines and its own `Fermat.*` namespace, so this is a real
risk and not a formality (zero collisions, as it happened). And stage the block in a
throwaway module that `import`s the destination: an `already declared` error there IS the
collision check, and it runs at scratch-module speed rather than at 25-minute
destination-build speed.

