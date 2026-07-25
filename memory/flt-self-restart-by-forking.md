---
name: flt-self-restart-by-forking
description: "Deyao 2026-07-24 — how the orchestrator restarts itself by forking into a new tmux window; drive it AUTONOMOUSLY whenever a restart is needed, don't wait to be told"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: bc388a7e-3d6c-4f64-9f93-3ae0c1bfe511
  modified: 2026-07-25T11:50:41.989Z
---

Deyao (2026-07-24): "remember how to restart yourself, and if you need to
restart, drive it autonomously." Restart = fork this session into a fresh
Claude process and kill the old one. Use it when a restart is warranted
(context nearing exhaustion, session-limit degradation, harness/MCP state
corruption) — no permission needed, it is pre-approved.

**Procedure (executed successfully twice, 2026-07-24; session chain
f8fcb103 → 1e467fbd → bc388a7e, windows fork → fork2):**

1. New tmux window in session `agent-2`, fresh name (fork2 → fork3 → …),
   cwd `/home/chend/flt-lean`:
   `tmux new-window -d -t agent-2 -n <new> -c /home/chend/flt-lean`
   then send-keys:
   `set -a; source /home/chend/flt-lean/.env; set +a; claude --dangerously-skip-permissions --resume <CURRENT-session-id> --fork-session`
   (own session id = the uuid in the scratchpad path in the system prompt).
2. Repoint the refill health-capture: in
   `~/.config/systemd/user/claude-refill.service` set
   `Environment=REFILL_TMUX=agent-2:<new>`; `systemctl --user daemon-reload`.
3. Detached handoff script (`setsid nohup … &`, the sanctioned
   kill→continue pattern of [[stop-hook-tmux-restart]]): sleep 30; `tmux
   kill-window -t agent-2:<old>`; sleep 10; `tmux send-keys -t
   agent-2:<new> 'continue' Enter`.
4. **Write NOTHING for the fork — no handover note, not even a role-
   disambiguation line** (Deyao, 2026-07-25, correcting earlier practice twice
   over). Claude Code is a pure function of (transcript + tool-call output) →
   next token. The fork inherits this session's EXACT transcript, so anything
   the parent could write down, the child can derive itself — including WHICH
   SIDE IT IS: `tmux list-windows -t agent-2` shows the old window gone and the
   new one active, and its own session id is in its scratchpad path. A note adds
   zero information and costs the context it was meant to preserve.

   The child therefore just resumes and re-derives state from the world: write
   its own session id into `.claude/stop-hook-session-id`
   ([[flt-stop-hook-session-guard]]), copy the old session's
   `subagents/agent-*.jsonl` across, resume live agents by id
   ([[kill-recovery-just-resume]]) — all of which is already in the inherited
   context and in CLAUDE.md, which is why it need not be restated.

**Why:** subagents and MCP servers are children of the session process —
they die at the kill and the fork resumes them from copied transcripts;
background watchers/census runs inside agents die too (tell those agents to
restart them). In-flight MCP builds die with the session: re-run the gate
in the fork before pushing anything that awaited it.
