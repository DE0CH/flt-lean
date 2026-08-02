---
name: flt-devissage-verdict-names-a-quantity
description: "A recorded \"that dévissage does not work\" note is about ONE quantity — check which way YOUR quantity is monotone under the same combination"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 7e6ea76e-7052-425e-a259-4631f2a36535
  modified: 2026-08-02T19:42:52.154Z
---

(2026-08-01, `flt-lean-382`.) `ArtinSymbol.lean` records, correctly and in bold, that the
cyclic dévissage fails: *"each step gives `[Fᵢ₊₁ : Fᵢ] ≤ h_{Fᵢ}`, and multiplying them bounds
`[L : K]` by `∏ h_{Fᵢ}`, not by `h_K`"*. That is about the naked DEGREE inequality. The NORM
INDEX chains the other way, so the same dévissage is sound for the second fundamental
inequality — which the same cluster says elsewhere (*"norm groups shrink under composita;
nothing analogous holds on the Galois side"*).

**Why:** a dévissage verdict is a statement about the monotonicity of the quantity it was
measuring under the combination being used. Two notes in one cluster can be individually
correct and jointly misleading, because the reader carries the verdict across quantities.

**How to apply:** before inheriting any "this reduction does not work" note, name the quantity
it measures, name the quantity YOU are chaining, and check the monotonicity of yours under the
combination. Same family as [[flt-route-inductive-step-is-often-formal]] and
[[flt-audit-scoped-to-declaration-it-read]].
