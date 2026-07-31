---
name: flt-deletion-claims-are-not-deletions
description: A docstring saying a declaration "was DELETED as consumerless" is a claim about the past, not a fact about the tree; four corroborating copies of a false one kept a dead sorry leaf on the frontier for three days
metadata:
  type: project
---

On 2026-07-31, `X0.lean` carried **four** docstrings asserting that
`not_stable_of_cmEndomorphism` "became consumerless and was DELETED the same
day" (2026-07-28). The write-up landed; the deletion did not. The theorem was
still in the tree, and it was the sole consumer of the sorry leaf
`exists_galoisConj_cmEndomorphism_eq_sub` — which therefore stayed on the
frontier and kept attracting dispatches at a leaf nothing could ever consume.

**Why:** the four copies cross-corroborate. Reading any two of them looks like
independent confirmation, and they were written by the same author in the same
session, so they are one claim in four places. This is the docstring-medium
sibling of the commit-message trap already recorded in [[CLAUDE.md]]: prose
about what the tree contains ages badly, and the more carefully it is
cross-referenced the more convincing the stale version becomes.

**How to apply:** before working a leaf, establish it is REACHABLE, not just
open. Comment-stripped scan for uses of the leaf's declaration name AND of every
declaration that consumes it — a leaf whose only consumer is itself
consumerless is dead, and closing it is worth nothing. `declaration uses 'sorry'`
counts open leaves; it says nothing about whether anything consumes them. When a
docstring says something WAS deleted, grep for it: that sentence is a hypothesis.

Deleting the dead pair was a full result — it also NARROWED the surviving leaf,
because the deleted theorem had been the only call site needing the general
prime `q`, so `not_forall_galoisScalar_of_cmEndomorphism` could be restated at
`q = p` (dropping two of its three proof regimes, including the Weil-pairing
determinant argument). See [[audit-searched-production-not-invariant]] — the
same "is the leaf stated wider than any call site needs" check.
