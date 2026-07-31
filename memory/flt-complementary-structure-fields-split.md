---
name: flt-complementary-structure-fields-split
description: Two branches adding DIFFERENT fields to one structure merge to one field kept, and the constructor literal taken from the other side — "X is not a field" plus "fields missing: Y" in one module is the tell
metadata:
  type: project
---

Release 32 (2026-07-31), `ModularCurve/X1.lean`. Two branches each repaired a
different refuted `∀ P` theorem by hoisting its citation onto
`Gamma1GITPresentation` as a new field — `smoothM` (Katz–Mazur 8.2.1, `64651d82`)
and `transitiveM` (Deligne–Rapoport IV.5.5, `420bd322`). The second forked before
the first, so the merge took the STRUCTURE from one side and a CONSTRUCTOR LITERAL
from the other, losing `smoothM` from two structures, a hypothesis and a call site.

**Why:** the merge boundary can run through a structure and its constructors in
opposite directions. A single dropped edit cannot produce that; only two rival
copies of one declaration can.

**How to apply:** when one module reports both `X is not a field of structure S`
and `Fields missing: Y`, do not weaken either statement — `git log -S` both field
names, and if the adding commits are incomparable the repair is the UNION. Check
the union is right by three tests: different citations, different discharging
leaves, disjoint consumers. If instead one docstring says it SUPERSEDES the other,
the union is the duplicated-hypothesis failure of release 24 and you must choose.

It survived six releases because `X1` sits behind the red `X0` — see
[[flt-red-upstream-hides-downstream-damage]]. Related: [[flt-two-leaves-may-be-one]],
[[flt-delete-times-refactor-orphans-a-leaf]].
