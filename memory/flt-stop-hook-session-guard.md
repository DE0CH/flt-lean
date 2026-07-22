---
name: flt-stop-hook-session-guard
description: The FLT Stop hook only drives the session whose id is in .claude/stop-hook-session-id; a successor loop session must update that file first
metadata: 
  node_type: memory
  type: project
  originSessionId: a9c0eb39-e62e-4ff6-bd25-8f304bca8b98
---

Since 2026-07-21 the FLT Stop hook (`.claude/check-sorries.py` in
`~/cs/flt-worktree`) refuses any session whose `session_id` (hook stdin)
differs from the id recorded in `.claude/stop-hook-session-id` (committed to
the repo). Foreign sessions are blocked with a standing refusal telling them
to only warn the user ("the STOP HOOK ran, this is probably not intended.").

**Why:** an accidentally launched second chat ("Lean FLT: second chat",
2026-07-21 09:03) was driven into the work loop by the hook and committed to
the repo; Deyao wants exactly one designated loop session.

**How to apply:** if a NEW session is meant to take over the continuous FLT
loop (e.g. after this session ends), it must first write its own session id
(the transcript-file UUID) into `.claude/stop-hook-session-id` and commit
that change — otherwise the hook will wedge it in the refusal branch.
Related: [[flt-notify-mu-node]], [[flt-continuous-loop-directives]].
