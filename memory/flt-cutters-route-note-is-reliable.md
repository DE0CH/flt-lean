---
name: flt-cutters-route-note-is-reliable
description: "A leaf's route note is reliable exactly when its author cut the leaf out of a proof they had just finished; a note by someone declining the leaf is not."
metadata: 
  node_type: memory
  type: project
  originSessionId: cddbffbe-c3d6-47ec-9c87-e1757b205a6c
  modified: 2026-08-02T13:12:23.880Z
---

CLAUDE.md is full of warnings that a leaf's recorded ROUTE is a hypothesis written before
anyone tried ([[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-inventory-audits-understate-what-exists]]). There is a recognisable exception, and it
identifies the cheapest leaves on the board.

**Believe a route note when its author had just BUILT the surrounding machinery and cut the
leaf OUT of a proof they finished** — the tell is that it names two or three specific mathlib
declarations and says the leaf is "left open for want of time, not for want of a route".
That author knows which mathlib lemma the neighbouring steps ran on. **Distrust a route note
attached by someone DECLINING a leaf** ("this needs a theory we do not have"): they never
opened it.

**Why:** the two kinds of note look identical in the file and are written in the same voice,
but one is a record of working knowledge and the other is a guess made from outside.

**How to apply:** read the commit that CUT the leaf (`git log -S '<leafName>'`) before pricing
it. If the cut commit also closed a parent, the route is near-certain. Measured 2026-08-02 on
`ModularCurve/PoleOrderValuation.lean`'s `exists_sub_smul_poleOrd_lt`: the docstring named
`Scheme.Hom.stalkClosedPointTo` plus the section `zeroSection ab ≫ f = 𝟙`, and both were exact
— the leaf closed in one run with no residual leaf. The sibling leaf in that same module
carries the same sentence and is still open.

Corollary for what to queue: a module whose docstring says a leaf is "reachable with tooling
this tree already owns" and names it is a better dispatch than any leaf whose docstring
describes missing theory.
