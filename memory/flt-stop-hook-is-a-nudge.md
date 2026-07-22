---
name: flt-stop-hook-is-a-nudge
description: "Deyao 2026-07-22 — the Stop hook is an automatic back-to-work nudge, NOT a safety net; best-effort is fine, failure is acceptable (especially while he watches)"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: e68e4f89-102e-4f9f-8119-8fd03437ed31
  modified: 2026-07-22T16:57:48.742Z
---

Deyao (2026-07-22): "stop hook is not a safety net, it's ok if it stops. i don't need a safety, i just need something automatic to prompt it go back to work when not done. it's ok if automation fails, especially when i'm actively watching."

**Why:** The earlier framing (mechanically un-exitable loop, invariant enforcement) fit the single-agent era; in orchestrator mode the hook's only job is to automatically re-prompt when there is genuinely unowned work. Over-engineering robustness (elaborate liveness proofs, guaranteed blocking) costs more than an occasional missed or spurious stop.

**How to apply:** Keep hook logic simple and best-effort: allow stops while the fleet looks alive (fleet-registry mtime check is plenty); block with a short nudge when it looks idle and sorries remain; any ambiguous/error path may just allow the stop rather than fail-closed. Do not add machinery to make the loop "impossible to exit." Related: [[flt-orchestrator-role]], [[flt-stop-hook-session-guard]].
