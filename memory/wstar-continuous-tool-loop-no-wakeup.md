---
name: wstar-continuous-tool-loop-no-wakeup
description: "Deyao's directive (2026-07-16) — no ScheduleWakeup; continuous tool-call loop with exactly one exit condition (lake build green, zero sorries); inability surfaces as an unexitable loop, never surrender text"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 74165b05-2b0c-49ee-af63-0a6d7cb838f6
---

For the W* Lean formalization (and long autonomous grinds generally),
Deyao's loop contract, documented in the project CLAUDE.md:

- **No ScheduleWakeup** — banned. Continuation is the tool-call loop
  itself (every tool result prompts further generation, as in a long
  coding session), plus a **30-minute catch-all cron job** (CronCreate,
  re-arm each fresh session; session-bound, 7-day expiry) for dropped
  turns.
- **Exactly one exit condition**: `lake build` green. The lakefile sets
  `warningAsError = true`, so any warning — above all `declaration uses
  sorry` — fails the build. All lint/deprecation warnings must be fixed on
  sight; the only tolerated failures are sorry nodes.
- **If continuation seems impossible, continue regardless**: attempt the
  most plausible next concrete action each iteration, forever. Inability
  must surface as a loop that cannot exit (repeatedly failed attempts on
  record) — never as a generated give-up paragraph; failed attempts are
  the clearer, mechanically checkable signal.
- Replies to Deyao's mid-work messages answer and resume tool calls in
  the same turn. Check `git status` before committing (his staged changes
  must not be swept into work commits).

Supersedes the wakeup-based pattern in [[wstar-top-down-dependency-tree]].
