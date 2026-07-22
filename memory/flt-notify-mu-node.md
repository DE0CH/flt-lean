---
name: flt-notify-mu-node
description: "Deyao 2026-07-21: send a PushNotification when exists_weilPairing_mu is proven OR when work pivots away from it"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: a9c0eb39-e62e-4ff6-bd25-8f304bca8b98
---

Standing instruction (Deyao, 2026-07-21): send a phone notification (the
`PushNotification` tool, status `proactive`) at the moment either of these
happens in the FLT loop:

1. `exists_weilPairing_mu` (WeilPairing.lean, the μ-node) is fully proven —
   its trailing `sorry` discharged and `lake build` green; or
2. work on `exists_weilPairing_mu` stops for any other reason (pivot to a
   different node, discovered blocker, restructure) — say which reason.

**Why:** the μ-node is a long multi-window arc; Deyao wants to be pulled back
in exactly when it resolves or stalls, not poll the tree.

**How to apply:** the `PushNotification` tool is deferred — load it via
ToolSearch (`select:PushNotification`) if its schema is not in context, then
send one message under 200 chars leading with the outcome (e.g.
"exists_weilPairing_mu PROVEN — 11 sorries left" or
"paused mu-node: <reason>"). This fires once per event, not per iteration.
Related: [[flt-continuous-loop-directives]].
