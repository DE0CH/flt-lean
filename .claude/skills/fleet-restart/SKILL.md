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

**0. STOP THE AGENTS FIRST — before forking anything** (Deyao, 2026-07-25,
after I got this wrong). `TaskStop` every running subagent and let them come to
rest, *then* fork.

Skipping this does not merely lose their in-process state — it leaves them
RUNNING while the fork starts, so two orchestrators briefly share one fleet, the
old process's exit is not clean, and the child inherits agents whose actual state
no longer matches any transcript. When I skipped it, 60 agents were reported as
"no completion record … their in-process state was lost", their remote builds
died with the foreground `ssh` sessions that the terminated turns were holding
open, and ten worktrees ended up `claimed` with uncommitted work but no
resolvable owner — which then took a recovery pass of its own.

Stopping first makes the fork's job mechanical: every agent is at rest, every
transcript is final, and the child resumes them from a consistent snapshot.

**NO TIMERS. THE TWO SIDES IDENTIFY THEMSELVES** (Deyao, 2026-07-25). Earlier
versions of this procedure handed off with a detached `sleep 30; kill-window;
sleep 10; send-keys` script. That is a race, not a synchronisation: the sleeps
are guesses about how long a fork takes to become ready, and nothing verifies
either side is where it should be. Replace it with an explicit
parent/child test that each side runs on itself.

**1. Record who the parent is, then fork.**

```bash
# parent, before forking: stamp its own identity where both sides can read it
echo <CURRENT-session-id> > /home/chend/flt-lean/.claude/restart-parent-session-id

tmux new-window -d -t agent-2 -n <new> -c /home/chend/flt-lean
tmux send-keys -t agent-2:<new> \
  'set -a; source /home/chend/flt-lean/.env; set +a; claude --dangerously-skip-permissions --resume <CURRENT-session-id> --fork-session' Enter
```

Your own session id is the uuid in the scratchpad path in your system prompt.
Set any env change the restart exists for (e.g.
`export CLAUDE_CODE_MAX_CONCURRENT_SUBAGENTS=200`) in that same `send-keys` line
— it is the only moment it can be applied.

**2. Each side detects which it is.** Both processes share the transcript, so
both will read this skill and reach this step. The test is one comparison:

```
my id  == contents of .claude/restart-parent-session-id  →  I am the PARENT
my id  != contents                                       →  I am the CHILD
```

The fork gets a fresh session id, so the comparison is decisive and needs no
timing. (`tmux list-windows -t agent-2` corroborates it, but the id is the
authority.)

**3a. If you are the PARENT: clean up after yourself and stop.** You have
already stopped the agents in step 0. Do not resume anything, do not merge, do
not dispatch — the child owns the fleet from here. Your only remaining job is to
remove yourself:

```bash
tmux kill-window -t agent-2:<your-own-window>
```

Killing your own window ends your process, which is the point: it is the last
thing you do, so there is nothing left to interrupt. Never leave the parent
alive "just in case" — two orchestrators on one fleet is the failure this whole
procedure exists to avoid.

**3b. If you are the CHILD: take ownership.** In this order:

1. `echo <your-session-id> > .claude/stop-hook-session-id` — the Stop hook only
   drives the session recorded there.
2. Repoint the refill health-capture: set
   `Environment=REFILL_TMUX=agent-2:<your window>` in
   `~/.config/systemd/user/claude-refill.service`, then
   `systemctl --user daemon-reload`.
3. Copy the parent's subagent transcripts into your own session directory:
   `cp -n ~/.claude/projects/<slug>/<parent-id>/subagents/agent-*.jsonl \
        ~/.claude/projects/<slug>/<your-id>/subagents/`
4. Resume every agent — see the `fleet-resume` skill.
5. Recreate any cron jobs. They are in-memory and died with the parent.
6. `rm .claude/restart-parent-session-id` — the marker has done its job, and
   leaving it makes the next restart's test read a stale answer.

## Write NOTHING for the fork

**No handover note. No summary. Not even a role-disambiguation line.** (Deyao,
2026-07-25, correcting earlier practice twice over.)

Claude Code is a pure function of (transcript + tool-call output) → next token.
The fork inherits this session's EXACT transcript, so anything the parent could
write down, the child can derive itself — **including which side it is**, from
the one-line marker in step 2 plus its own session id. A note adds zero
information and costs the context it was meant to preserve.

The marker file is the *only* legitimate exception, and it is not a note: it is
one uuid, written by the parent about itself, so that a comparison can replace a
guess. Do not put anything else in it.

**Do not identify the sides by tmux state.** An earlier version of this skill
said the child could tell it was the child because "the old window is gone." That
is now false by construction — under this procedure the parent is still alive
when the child wakes, and only removes itself afterwards. Comparing session ids
is the test; tmux is at most corroboration.

Everything the child then does is listed in step 3b — it does not need to be
told, because it is reading this same file.

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
