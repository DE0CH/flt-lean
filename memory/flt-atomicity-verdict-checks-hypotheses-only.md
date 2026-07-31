---
name: flt-atomicity-verdict-checks-hypotheses-only
description: "\"No further clause-shaped cut is available\" audits hypotheses, not the conclusion's quantifier over a finite set; the descent is in-tree even when the step is a citation"
metadata:
  type: project
---

A leaf's atomicity verdict ("every remaining hypothesis is consumed by the
classical argument; the conclusion is the input datum with ONE clause added") is
a claim about the INPUT side only. When the conclusion quantifies over a finite
set — `𝒮.S ⊆ badF`, `supp 𝔫 ⊆ bad`, `∀ i ∈ s, P i` — the classical proof is
almost always a one-at-a-time descent, and the descent is Lean work this tree can
do even though the step is a citation.

`exists_eigenform_minimalLevel_of_isUnramifiedOutside` (KhareWintenberger.lean)
was cut this way on 2026-07-31: it is now an induction on `𝒮.S.card` over the
one-place leaf `exists_eigenform_eraseS_of_isUnramifiedAt`. Leaf count unchanged
(1 → 1); what shrank is the citation — from "conductor–level dictionary over a
set + the finiteness that terminates it" to "local–global compatibility and the
newvector statement at ONE unramified place" — and the ramification hypothesis
sharpened from `∀ w ∉ badF, ρ unramified at w` to `ρ unramified at w₀`.

**Why:** an atomicity audit is written by reading the binder list, so it sees
hypotheses and misses that the goal is a bounded loop.

**How to apply:** before inheriting an "ATOMIC" verdict, ask whether the
conclusion mentions a finite set and whether the ambient structure lets you build
the smaller object cheaply (`U₁Data`'s only constraint on `S` was inherited by
subsets, so the erase was six lines). Pick a measure needing no `DecidableEq` in
the STATEMENT — `𝒮.S.card`, not `(𝒮.S \ bad).card`, since `\` drags an `SDiff`
instance into the `suffices`. See [[flt-inventory-audits-understate-what-exists]]
and [[audit-searched-production-not-invariant]].
