---
name: subagent-dispatch-suspended-until-told
description: "Deyao 2026-07-23 — subagent dispatch was blanket-paused, then explicitly RE-ENABLED, standing (carries forward, not per-occasion). Current state: dispatch IS allowed."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 8e948ad7-2925-4f81-a46b-38fef37021d4
---

**Current state: subagent dispatch is allowed.** Timeline, same session,
2026-07-23:

1. Deyao stopped 6 subagents dispatched for a keep-list audit task:
   "do not launch subagents. did you forget." Corrected my first read
   ("math-loop dispatch is fine, other tasks need checking") to: "no
   that's not the reason, i stopped you from using subagents and said
   until i tell you to use subagents again" — a full blanket pause, not
   scoped by task type. Also: "no i don't want to use fleet, fleet is
   buggy from experience" — active distrust of
   [[flt-fleet-13-worktree-protocol]] specifically (that session's own
   incident: killed agents left worktrees dirty, needing manual cleanup).
2. Later the same session: "you are approved to use subagents now, use
   subagents for this task." I initially recorded this as a one-off,
   per-occasion approval that wouldn't carry forward. Deyao corrected
   that too: "it is a reversal of the blanket pause" / "approval does
   carry forward."

**Why:** Pauses and re-authorizations from Deyao are each their own
explicit statement — don't assume scope (task-type-limited, one-off vs.
standing) in either direction; read the literal words, and when
corrected, take the correction as replacing my inference, not
narrowing it further on my own.

**How to apply:** Subagent dispatch is currently allowed (standing,
not per-task) — the fleet-buggy distrust from item 1 hasn't been
explicitly retracted, so favor caution with the specific
[[flt-fleet-13-worktree-protocol]] worktree-pool mechanism (verify
worktrees are left clean after each dispatch), but dispatching itself
is not gated. If Deyao pauses dispatch again, treat it as blanket
unless he says otherwise, and don't assume a later re-approval is
scoped to one task unless he says so.
