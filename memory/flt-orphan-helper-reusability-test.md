---
name: flt-orphan-helper-reusability-test
description: "Before deleting an orphaned cluster, test its PROVEN helpers for reuse in the live route by reading which OBJECT their hypothesis is stated about — and check the leaf's own docstring, which names its parent and can be the liar"
metadata: 
  node_type: memory
  type: project
  originSessionId: 50fb14d4-938c-4f8b-97f9-d9a7cf02824b
  modified: 2026-08-01T21:32:09.628Z
---

When a rival cut is orphaned, the cluster usually contains PROVEN helpers as well
as the dead leaf. "Keep them, they are proven" and "delete on sight" are both
reflexes, not decisions. The test is one line: **read which OBJECT the orphan's
hypothesis is stated about, and ask whether the live proof ever puts a test
element there.**

Measured 2026-08-01, `ArtinConductor.lean`. The orphan
`le_relIndex_gp_one_of_smul_unif_eq_mul` is proven and demands
`σ • D.unif = ζ · D.unif` — an eigenvector equation on `D.unif`, i.e. on an
element of valuation exactly `1`. That is exactly what the dead arithmetic leaf
existed to supply, and exactly what the live proof of
`exists_lowerRamificationData_phi_one_le` deliberately avoids needing: it takes an
`n`-th root `Z` of a BASE uniformizer, chooses the level to FIX `Z` rather than to
make `Z` a uniformizer, and injects `μ_n` into `G₀ ⧸ G₁` through
`eq_one_of_smul_eq_mul_of_mem_gp_one` without ever mentioning `v(Z)`. So the
helper is unusable in the live route by construction — superseded, not merely
unconsumed. Where the answer comes out the other way, repurposing beats deleting
and the same one line tells you so.

**Why:** this is the half of the orphan story that
[[flt-consumerless-leaf-is-dead-or-duplicate]] does not cover. That entry tells
you the leaf is dead; it does not tell you what to do with the proven material
beside it, and getting that wrong either strands free-floating code (forbidden
here) or destroys reusable work.

The companion tell is a direction nothing else records: **the LEAF'S OWN docstring
names its parent and asserts the parent is proven over it, and that sentence rots
exactly like a parent's docstring naming the wrong leaf.** Here it said "everything
downstream of it is PROVEN in `exists_lowerRamificationData_phi_one_le` below" and
"this is the ONLY arithmetic still owed" — true when written, false when read,
because the parent had since been proven outright by an independent route. The
parent's PROOF BODY is the only witness, in either direction.

**How to apply:** grep both ways before reading the mathematics — does anything
reach my target, and does the parent my docstring names actually CALL me. If the
answer is no twice, the task is a deletion. Then pick between routes by counting
the leaves each leaves OPEN (live route zero, dead route one, so the live one
supersedes), run the one-line reusability test on each proven helper, and leave a
note at the deletion site carrying the recovery sha plus any refutation the dead
docstring recorded that nothing else does. Write comment delimiters in PROSE
inside that note. Do NOT sweep up the other unreachable declarations you find on
the way: several will be `instance`s reached by typeclass search, which a token
scan structurally cannot see.
