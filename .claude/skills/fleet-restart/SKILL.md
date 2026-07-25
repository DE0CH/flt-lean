---
name: fleet-restart
description: Restart the orchestrator session by forking it into a fresh tmux window and killing the old one. Use when context is nearing exhaustion, the session is degrading under limits, or harness state is corrupted. Pre-approved — drive it autonomously, no permission needed.
---

# Restart the orchestrator (fork-and-kill)

A restart forks THIS session into a fresh Claude process and kills the old one.
The fork inherits the exact transcript, so nothing needs to be handed over.

Deyao (2026-07-24): *"remember how to restart yourself, and if you need to
restart, drive it autonomously."* It is pre-approved — do not ask.

## When

- Context nearing exhaustion.
- Session-limit degradation.
- Harness state corruption.

## Procedure

Executed successfully multiple times; session chain f8fcb103 → 1e467fbd →
bc388a7e, windows fork → fork2 → … (current window is discoverable with
`tmux list-windows -t agent-2`).

**1. Open the new window.** Fresh name, next in the fork sequence, cwd at the
repo root:

```bash
tmux new-window -d -t agent-2 -n <new> -c /home/chend/flt-lean
tmux send-keys -t agent-2:<new> \
  'set -a; source /home/chend/flt-lean/.env; set +a; claude --dangerously-skip-permissions --resume <CURRENT-session-id> --fork-session' Enter
```

Your own session id is the uuid in the scratchpad path in your system prompt.

**2. Repoint the refill health-capture.** In
`~/.config/systemd/user/claude-refill.service` set
`Environment=REFILL_TMUX=agent-2:<new>`, then `systemctl --user daemon-reload`.

**3. Hand off from a DETACHED script.** Never kill your own window from inside
the turn that must still finish. Use the sanctioned kill→continue pattern
(`setsid nohup … &`, survives the tmux kill):

```
sleep 30
tmux kill-window -t agent-2:<old>
sleep 10
tmux send-keys -t agent-2:<new> 'continue' Enter
```

## Write NOTHING for the fork

**No handover note. No summary. Not even a role-disambiguation line.** (Deyao,
2026-07-25, correcting earlier practice twice over.)

Claude Code is a pure function of (transcript + tool-call output) → next token.
The fork inherits this session's EXACT transcript, so anything the parent could
write down, the child can derive itself — **including which side it is**:
`tmux list-windows -t agent-2` shows the old window gone and the new one active,
and its own session id is in its scratchpad path. A note adds zero information
and costs the context it was meant to preserve.

## What the child does on waking (it derives this itself — do not instruct it)

- Write its own session id into `.claude/stop-hook-session-id` (the Stop hook
  only drives the session recorded there).
- Copy the old session's `subagents/agent-*.jsonl` into its own `subagents/`
  directory, then resume live agents by id — see the `fleet-resume` skill.
- Re-run any verification gate that was in flight, before pushing anything that
  awaited it.

## Why the kill costs what it costs

Subagents and MCP servers are children of the session process: they die at the
kill, and the fork resumes them from the copied transcripts. Background watchers
and census runs living inside agents die too — tell those agents to restart
them. In-flight builds die with the session.

## Never re-enable a Stop hook from inside the session that is about to stop

A session that re-enables the hook while still running can trap ITSELF in the
blocked-stop loop. If the hook was disabled (renamed to `_DISABLED_Stop` in
`.claude/settings.json`), re-enable it only from the same detached script, in
this order: kill the old session's window → rename `_DISABLED_Stop` back to
`Stop` → `tmux send-keys 'continue'` into the new window so it picks the config
up.

## Related

- `.claude/skills/fleet-resume/SKILL.md` — resuming the agents afterwards,
  including the cross-session transcript copy this restart makes necessary.
