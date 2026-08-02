---
name: flt-hoist-may-have-already-landed
description: "A leaf whose docstring says \"WHAT IS MISSING is a HOIST\" names the file the block USED TO live in; grep the declaration, not that file."
metadata: 
  node_type: memory
  type: project
  originSessionId: ed82de9e-32c5-4ba0-8951-bd6048f6e405
  modified: 2026-08-02T09:25:07.389Z
---

A leaf in this tree is routinely cut with the docstring *"**WHAT IS MISSING is a
HOIST, not a theory** — `X` lives in `<downstream module>`"*. That paragraph is
the most actionable thing in the file and the one that rots fastest, because the
agent who performs the hoist cannot edit every leaf that was waiting on it.

**The tell that defeats the ordinary "re-grep an absence claim" reflex: the
docstring names the file the block USED TO live in.** A hoist creates a NEW
module, so grepping the named file — or re-checking that it is still downstream,
which it is — CONFIRMS the docstring and tells you nothing.

Check the DECLARATION and your own import block instead:

    grep -rn "def <movedName>\|theorem <movedName>" Fermat/ --include=*.lean
    grep -n '^public import' <your file> | grep -i <the concept>

Measured 2026-08-02, `flt-lean-240`: `heckeOp_smul_of_isWeightTwoEigenform`
(`ModularCurve/X0.lean`) said its `q`-expansion dictionary was stuck in
`Modularity/Interface.lean`. The block had moved to the new
`Modularity/HeckeQExpansion.lean` on 2026-07-31 — the day after the leaf was cut
— and `X0.lean` already `public import`ed it. The leaf was a forty-line assembly;
six minutes of it was the proof. The same file's `finite_setOf_isWeightTwoEigenform`
had been unblocked the same way by a second hoist into `WeightTwoEigenform.lean`.

**Why:** a docstring records a LAYOUT obstruction, and layout is exactly what
another agent changes without touching your leaf. Applies equally to "needs a
module split", "blocked by declaration order", "the machinery is in a file that
imports this one".

**How to apply:** for any leaf whose stated obstruction is a RELOCATION, run the
two greps above before reading another line of the docstring. If you PERFORM a
hoist, `grep -rn 'is a HOIST\|hoist out of' Fermat/` and add one sentence to each
waiting leaf. See [[flt-inventory-audits-understate-what-exists]] and
[[flt-leaf-cost-estimates-are-hypotheses]].
