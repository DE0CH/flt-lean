## A RIVAL CUT CAN SURVIVE A MERGE AS A CHAIN THAT DEAD-ENDS IN AN UNDERSCORED HYPOTHESIS
(2026-07-31, `flt-lean-110`, the `Γ₀` Eichler–Shimura cluster in `X0.lean`.) The
seventh-invisibility-class sections above say to grep a leaf for CONSUMERS before proving it,
and that a leaf with none is dead. There is a shape they do not cover, and it defeats that
check exactly: **the leaf HAS a consumer, the consumer has a consumer, and three hops later
the chain is passed as an argument the receiving theorem IGNORES.**
`exists_isotypicHom_of_isWeightTwoEigenform` (the target) → `exists_isotypicQuotient_of_isIntegral`
→ `exists_isotypicQuotient_of_isWeightTwoEigenform` → the `_hquot` parameter of
`exists_heckeIsotypicDecomposition_of_isotypicQuotients`, whose body never mentions it and takes
its quotients from a DIFFERENT leaf (`exists_universalIsotypicQuotient`) instead.
Every instrument passes. The argument is applied, so the whole chain is in the used-constant
cone and the free-floating check is silent; every declaration compiles; `own.py` and
`leafstat.py` correctly report the leaf open and unowned; the frontier scan counts it. And it
is worth nothing: the theorem it ultimately feeds discards it.
**The tell is one underscore.** This project marks a hypothesis a proof does not consume by
prefixing it `_`, so `_hquot` at the call site is the whole diagnosis. So extend the consumer
grep: do not stop at "something references my leaf" — follow the references until you reach a
declaration whose PROOF BODY mentions the name, and check that no link is an `_`-prefixed
binder. Three greps, and it is the difference between a proof and a wasted run.
**How it gets built, and it is nobody's mistake:** two branches cut the same node the same day
and the merge kept both. The loser's chain survives because its top declaration is still
*applied* somewhere — at a hypothesis the winner's proof no longer needs but whose signature
still carries it. So expect this wherever a "given P, build Q" theorem has been re-proven from
a stronger input: the old `P` hypothesis stays in the signature and keeps a dead chain alive.
**And the parent's DOCSTRING named the surviving route while its BODY took the losing one.**
CLAUDE.md already says to grep a route claimed in a docstring against the proof body; note the
direction here is the useful one — the docstring was RIGHT and the body was wrong, so the
mismatch is not always the docstring rotting. Either way the mismatch itself is the signal that
two cuts of one node are in the file.
### The resolution, and the receipt that makes it safe
Per the standing rule, keep the arrangement whose root leaf is IMPLIED by the rival's root:
`exists_universalIsotypicQuotient` gives `IsIsotypicQuotient` field-for-field with
`integral := hint`, the converse cannot hold (an `IsIsotypicHom` carries no `universal` clause),
and the root cone was already carrying it for the decomposition. So the parent was re-routed
through it and the loser's modular half deleted: `X0.lean` 101 → 100 sorried declarations,
**no new leaf, and no new mathematics owed**.
Two things made that safe and both are cheap:
* **Verify the transport in a scratch BEFORE deleting anything.** A module that
  `public import`s the target's built olean and restates the parent under a primed name
  compiles the whole field-by-field transport in well under a minute, against ~40 for the real
  file. A `EXIT=0` with no `sorry` warning there is proof that the surviving leaf really does
  imply the parent — which is the claim the deletion rests on, and the only one worth checking
  by machine rather than by eye.
* **`git diff -U0 | grep -E '^[+-] *sorry *$'` is the receipt for a closure.** One `-  sorry`
  and no `+  sorry` says exactly "one leaf closed, none opened", and it is checkable by anyone
  in a second — unlike a warning-set delta, which cannot distinguish a closure from a closure
  plus an unrelated disclosure.
**Do not delete the twin on the other side.** `exists_isotypicQuotient_of_isIsotypicHom` and
`IsIsotypicHom` are kept: `X1.lean` calls both over its own still-open `Γ₁` leaf, and the `Γ₁`
side has no universal-quotient leaf to route through. A rival cut being redundant on one side
says nothing about the other, and the shape-free half of a cut is usually the half that is
shared.
**What the deletion cost, stated because it is the only real loss:** the deleted docstring
carried the `B := J`, `v := π` route (the projector of `End(J₀(N)) ⊗ ℚ` onto the `a`-isotypic
part), which needs no quotient of an abelian scheme. That observation is real and now sits on
the surviving leaf's `nontriv` field, where it is the cheap route to the NON-VANISHING half.
When you delete a leaf, move its route notes onto whatever now owes the same mathematics —
deleting them is how the next agent re-derives them.
