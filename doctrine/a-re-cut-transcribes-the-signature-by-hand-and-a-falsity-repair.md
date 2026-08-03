## A RE-CUT TRANSCRIBES THE SIGNATURE BY HAND — AND A FALSITY REPAIR IS EXACTLY THE BINDER IT DROPS

(2026-08-01, `flt-lean-313`, `ModThree.lean`.  One day live, invisible to every
instrument, and the diagnosis is one binder-list diff.)

Re-cutting a node — split it in two, prove one half, re-point the parent — is the
commonest move in this development.  The new leaf's signature is written out BY
HAND from the old one, and the hand-transcription is where a hypothesis added by
an *earlier falsity repair* gets dropped: to whoever is concentrating on the
decomposition it reads as decoration, because it is not what either half is
*about*.

Measured here.  `287edc70` (07-30) refuted the Fontaine presentation leaves and
repaired them by adding `hū3` (the residue point is `𝔽₃`-rational) to three
declarations.  `5904e20a` (07-31) re-cut the node into
`exists_idempotentLocalQuotient` + `exists_minimalPresentation_of_idempotentLocalQuotient`,
transcribed the step-2 signature, and **dropped `hū3` from the new leaf and from
the parent** — restoring, verbatim, a statement that had been refuted the day
before with an explicit witness sitting twenty lines above it in the same file.

**WHY NOTHING SAW IT — all four standing checks are silent BY CONSTRUCTION:**

* the false thing is a `sorry` LEAF, so no build breaks and no error appears;
* the old and new leaf have DIFFERENT NAMES, so `xdup.py`/`check-dup` cannot pair
  them, and `dupstmt.py` will not either while the binder lists differ — which is
  precisely the defect;
* the parent is PROVEN, so no frontier scan flags the chain;
* the `sorry` COUNT went UP by one (the orphan plus the new leaf), which reads as
  ordinary decomposition progress.

**THE TWO DETECTORS, both cheap, and the second is the one that generalises.**

1. **A DEAD BINDER at the top of the chain.**  `exists_fontainePresentation` kept
   its `hū3` binder — the 07-30 repair survived there — and simply stopped passing
   it, because the callee no longer took it.  So the file contained a hypothesis
   that no call in its own proof body consumes.  That is a two-second grep and it
   points straight at the break:

       grep -n '(<binder> :' <file>          # signatures that declare it
       grep -n '<binder>[ )]' <file>         # and every place a body USES it

   A binder declared and never consumed, in a file that is otherwise disciplined
   about `_`-prefixing unused hypotheses, is a re-cut that lost its other half.
   (Lean's `unusedVariables` linter says so too, on every green build.)
2. **DIFF THE ORPHAN'S BINDER LIST AGAINST THE LIVE LEAF'S.**  A re-cut that does
   not delete the leaf it replaces leaves the CORRECT signature sitting in the
   file as the only surviving record of the repair.  Here the orphan
   (`exists_minimalPresentation_of_isLocalRing_quotient`, consumerless since
   07-31) and the live leaf were the same statement up to binder names — *except*
   for `hū3`.  So the orphan is not merely dead weight: **it is the witness.**

**So the rule for whoever re-cuts: the deletion of the old leaf is PART of the
re-cut, and before you delete it, diff its binder list against the new one and
justify every difference in writing.**  If you cannot bring yourself to delete it,
that is the signal that the two are not the same statement and you have changed
something you did not mean to.  And for whoever inherits: a consumerless leaf
beside a live one of the same shape is a diff to run, not merely garbage to
collect.

**The repair cost nothing, which is the usual shape** (this file's standing
observation that the missing hypothesis is already in the caller's hand): `hū3`
is discharged at the top by a `by_cases` in `exists_fontaineCoordinates`, whose
negative branch is the named leaf `exists_fontaineCoordinates_of_not_primeFieldValued`.
So restoring it was one binder on two declarations and one argument at two call
sites, exporting no obligation to anybody — and deleting the orphan took the
cluster from two open leaves to one, with the survivor TRUE instead of FALSE.

**Accounting note, because it is unflattering and must be said: no mathematics was
done.**  The frontier moved `−1` and the project did not.  What changed is that
the one remaining leaf is true, the dead one will stop drawing dispatches (it drew
mine), and the audit that was silently reverted is recorded where the next reader
of either declaration will hit it.

