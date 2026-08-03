## A "WHAT IS MISSING IS A HOIST" PARAGRAPH IS DATED EVIDENCE ABOUT AN IMPORT BLOCK — GREP THE IMPORT BLOCK, NOT THE FILE IT NAMES
(2026-08-02, `heckeOp_smul_of_isWeightTwoEigenform` in `ModularCurve/X0.lean`,
closed in four rewrites after a day as a leaf.)
This file already records that an "absent from the pin" verdict is a search
result rather than a fact.  The commonest LOCAL form of that failure is
narrower and cheaper to check: a leaf cut with a docstring headed **"WHAT IS
MISSING is a HOIST, not a theory"**, naming a block of declarations and the
DOWNSTREAM module they live in.  Such a paragraph is a measurement of the
import graph on the day it was written, and in this fleet the import graph
moves every release.
Here the named block — `qCoeff`, `qExpansion_heckeTransform_coeff` and the six
`heckeRep`/`qParam` helpers, said to live in `Modularity/Interface.lean`
(downstream) — had been hoisted into `Modularity/HeckeQExpansion.lean`, and
`X0.lean` had `public import`ed that module **since the same day the leaf was
cut**: the edge is in its own import block at line 681, added for an unrelated
consumer and justified there in a comment.  So every input was in scope while
the leaf sat there advertising that they were not, and a second, older
paragraph 18 000 lines away (the `exists_basis_charpoly_heckeOp` section
docstring) was prescribing the same already-completed move.
**The check is one command and it is not the one the paragraph suggests:**
    grep -n '^public import' <the file the leaf lives in>     # not the file the paragraph names
    grep -rn 'theorem <one named declaration>' Fermat/        # where does it live NOW
A "hoist needed" paragraph sends you to read the DOWNSTREAM module and confirm
the block is there — which it still is if the hoist was a copy, and which tells
you nothing about your own scope either way.  Read your own import block first.
Two riders from the same close.
* **A hoist ANNOUNCES itself in the importing file's comments, and that is the
  cheapest evidence there is.**  `X0.lean`'s import block carries a comment
  saying exactly which declarations the new edge is for.  When a leaf's
  docstring and an import comment disagree about where something lives, the
  import comment wins: it is checked by the compiler, and the docstring is not.
* **Correct BOTH copies when you find one stale.**  The prescription existed in
  two places written a day apart; fixing only the leaf's would have left the
  other to send the next prover at the same non-task.  Grep the file for the
  distinctive name in the stale claim (`exists_cuspForm_heckeTransform` here)
  before you stop.
### The Lean trap that decides where such a bridging helper is stated
`Fermat.Gamma0GL` is an `abbrev` and `GaloisRepresentation.Modularity.Gamma0GL`
is a `def`, with the same body.  They unify at DEFAULT transparency — which is
why a statement mixing `CuspForm (Gamma0GL M) 2` from one side with `heckeOp`
from the other typechecks at all — and NOT at `instances`, which is the level
`rw` works at.  So a lemma proven on the `Modularity` side is unusable as a
rewrite on the `Fermat` side even though both goals print identically.  The
measured symptom is the standing "printed pattern equals printed target" trap in
a new suit:
    simpa using (qCoeffL M m).map_smul c g
    -- Type mismatch: After simplification, term ... has type True
    --   but is expected to have type qCoeff M (c • g) m = c * qCoeff M g m
`simp` closed the *hypothesis* (it is `map_smul` at the other carrier) and left
the goal untouched, so the two were never related.  **Restate the one-line fact
on the side your objects live on** — six lines here — rather than fighting the
crossing; `exact`/`refine` cross it for free, `rw`/`simpa` never will.
Corollary for the frontier count: this close was `−1` with no mathematics done,
and the receipt that says so is the pair *(build's `declaration uses 'sorry'`
warning set has no entry in the declaration's line range)* and *(the file's
comment-stripped `sorry` TOKEN count fell by exactly one)*.  Quote both — the
first alone cannot see an anonymous inner `sorry` swapped in for a named one.
