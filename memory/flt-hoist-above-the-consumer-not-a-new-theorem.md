---
name: flt-hoist-above-the-consumer-not-a-new-theorem
description: A "MISSING MACHINERY" note can be false because the theorem exists downstream — check whether ONE unrelated import is what put it there
metadata:
  type: project
---

`X0.lean`'s Néron–Ogg–Shafarevich leaf needed inertia ⟹ `q ∤ discr`. The
theorem existed — `isUnramifiedAt_of_inertia_le_fixingSubgroup` and
`not_dvd_discr_of_inertiaTrivialAt` — but in two files DOWNSTREAM of `X0.lean`,
so a plain grep for "does the tree have this" answers yes and a plain grep for
"can I use it" answers no.

The decisive question is **WHY** the source file is downstream, and the answer
is often ONE import needed by ONE unrelated declaration. Here
`MinkowskiUnramified.lean` imports `GaloisRepresentation/Chebotarev.lean`
(13 479 lines) solely for `discreteTopology_moduleTopology`, used by the LAST
declaration in the file. The dictionary needs none of it. Splitting the block
into `GaloisRepresentation/InertiaUnramified.lean` cost `X0.lean`'s cone one
module of 1752 lines instead of four totalling 16 160.

Procedure that made it cheap and safe:

1. Compute the cone delta before deciding — `imports` closure of the candidate
   minus the consumer's, with line counts. That number IS the decision.
2. Extract the block **verbatim** by line range (`sed -n 'lo,hip'`), so the hoist
   is byte-identical and no statement can drift.
3. Replicate the source file's `@[expose] public section` and `namespace`, or the
   declarations are not exported and every downstream use site breaks.
4. DELETE from the sources and have them `public import` the new module — never
   leave a copy, that is a duplicate-declaration merge hazard.

This is the third instance of the same repair (`DiscrExponent.lean` 2026-07-28,
`MinkowskiUnramified.lean` itself out of `MazurTorsion.lean` 2026-07-27). **A
node stranded below its consumer is a missing module boundary, not a missing
theorem.** See [[flt-missing-machinery-may-be-downstream]], of which this is the
sharper, actionable form.
