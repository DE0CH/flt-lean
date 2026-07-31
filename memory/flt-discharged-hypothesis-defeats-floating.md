---
name: flt-discharged-hypothesis-defeats-floating
description: Support material proven under a still-sorried leaf is free-floating unless the leaf is split into an `_of_X` version taking X as a hypothesis, discharged by the real proof
metadata:
  type: project
---

A sorried body contributes NO dependency edges, so anything you prove "for" an open
leaf is free-floating and cannot be committed. This is why
`flt-lean-272`'s four `InfinitePlace`-indexed trace lemmas sat uncommitted in a git
blob tag for six days across two owners, and why the task prompt's instruction — "commit
it TOGETHER with the assembly that consumes them" — is unsatisfiable as literally
written when the assembly is exactly the leaf you cannot close.

**The mechanism that works** (used 2026-07-31 to land sub-leaf (B) of
`heckeIdealTheta_functionalEquation`):

1. Package the proven fact as a `Prop`-valued `def` — `TraceFormBridge K` — in the new
   module. A `def` keeps the consumer's statement short and lets you STRENGTHEN the
   package later (add a conjunct) without touching the consumer's text at all.
2. Rename the open leaf to `foo_of_X` and give it that `Prop` as an extra hypothesis.
   Body still `sorry`. Its statement is otherwise unchanged.
3. Re-state `foo` with the ORIGINAL signature, proven by `foo_of_X … (theProof)`.
   That proof term is real, so it puts the package — and everything the package's
   proof uses — into the root cone. Consumers of `foo` are untouched.

Net effect: the leaf count is unchanged, the frontier statement is unchanged, and a
genuine sub-leaf is closed and *visible*. The successor gets the fact as a named
hypothesis already in its hands.

The `Prop`-def indirection paid for itself within the hour: sub-leaf (B) landed first as
just the metric identity, then as a conjunction with the dual-lattice theorem, and the
26 000-line consumer file needed no second edit.

Trap met on the way, worth its own line: adding `open Module` / `open scoped Classical`
at FILE level to accommodate new material turned an already-working `simpa` 100 lines
above into a `(deterministic) timeout at tactic execution`. Put extra opens in a
`section` around the new material, not in the file header. See
[[flt-glue-first-no-floating-haves]].
