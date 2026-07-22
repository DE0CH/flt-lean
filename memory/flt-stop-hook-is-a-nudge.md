---
name: flt-stop-hook-is-a-nudge
description: "Deyao 2026-07-22 — the Stop hook is an automatic back-to-work nudge, NOT a safety net; low-stakes, simple. NOTE: 'fail-open' was Claude's design choice, NOT Deyao's — under the crash-don't-fallback rule the hook crashes loudly on unexpected states"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: e68e4f89-102e-4f9f-8119-8fd03437ed31
  modified: 2026-07-22T19:37:40.849Z
---

Deyao (2026-07-22): "stop hook is not a safety net, it's ok if it stops. i don't need a safety, i just need something automatic to prompt it go back to work when not done. it's ok if automation fails, especially when i'm actively watching."

**Why:** In orchestrator mode the hook's only job is to automatically re-prompt when there is genuinely nothing else (subagents, background tasks) whose state change would re-prompt the session. Low stakes: a missed nudge or a spurious stop is fine; do not over-engineer robustness.

**CORRECTION (Deyao, same day, after Claude misattributed):** Deyao never chose "fail-open" — that was Claude's inference, wrongly recorded as his choice ("i did not in fact choose fail-open, you choose it"). Under [[scripts-crash-dont-fallback]] the consistent semantics are: exit 0 (allow) ONLY on the affirmatively verified live-background-work case; exit 2 (block+nudge) on verified idle-with-sorries; any UNEXPECTED state → raise and crash loudly (a crashed Stop hook is harmless to the loop and visible to the caller — that is the desired signal, not a silent allow).

**How to apply:** Keep hook logic simple: liveness check first (session task/subagent/workflow dirs, mtime freshness); nudge only on idle-with-sorries; crash on anything unexpected. Do not add machinery to make the loop "impossible to exit". Related: [[flt-orchestrator-role]], [[flt-stop-hook-session-guard]], [[scripts-crash-dont-fallback]].
