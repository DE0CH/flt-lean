---
name: fleet-resume
description: Resume fleet agents that were killed mid-task (usage/session limit, crash, orchestrator restart). Use whenever agents report "Agent terminated early due to an API error", "You've hit your session limit", or after the orchestrator itself restarts. JUST RESUME — never salvage.
---

# Resume killed fleet agents

**The whole procedure is: SendMessage every dead agent the word `continue`.
Nothing else. Do not salvage.**

## The rule (Deyao, 2026-07-23, after I got it wrong three times)

> "why do you do salvage-and-resume. you literally just have to resume. all the
> state is the transcript, and nothing is to be salvaged before you can resume
> where you left off."

A kill interrupts **only the in-flight API call**. The agent's transcript holds
its entire working context; its worktree holds its files exactly as it left
them, uncommitted edits included. `SendMessage` puts it back exactly where it
was.

## FORBIDDEN before resuming

These are not merely unnecessary — the first is actively destructive:

- **Do NOT revert or clean uncommitted worktree state.** The transcript still
  references those edits. Reverting forces every resumed agent to re-derive work
  it had already done. This happened across three consecutive kills.
- **Do NOT pre-merge the agents' committed branches.** Merging happens at an
  agent's NORMAL completion, never as kill recovery.
- **Do NOT inventory dirty worktrees, scan branches ahead of main, or "assess
  what landed."** That reconnaissance is the salvage instinct wearing a hat. It
  is also how the orchestrator ends up merging a branch out from under an agent
  that is still working on it.
- **Do NOT touch the pool file.** A killed agent still owns its worktree.

## Do NOT narrate the resume

Send the bare word `continue`. No per-agent state summary, no "your worktree is
intact", no reminder about `.lake`. The agent's transcript already has
everything; a resume message that narrates state is redundant at best and
misleading at worst (Deyao, 2026-07-23). A narrated resume also risks
contradicting what the agent actually knows, since the orchestrator is
reconstructing that from memory.

## Procedure

1. **Collect the dead agent ids.** They are in the task-notification blocks —
   `<task-id>` of every entry whose status is `failed`. Also check `TaskList`
   for `failed` tasks if notifications have scrolled away.

2. **Check whether the limit has actually reset**, if the failure was a session
   limit. The error names a reset time in a stated timezone:

   ```bash
   TZ=Europe/London date
   ```

   Resuming before the reset just re-fails, which is cheap but noisy. Resuming
   after it works. If the reset is hours away, resume one agent as a probe
   rather than all of them.

3. **SendMessage each id with `continue`.** Batch them — many `SendMessage`
   calls in a single message run concurrently. `to` takes the raw agent id.

   A successful resume reports either `was stopped (failed); resumed it in the
   background` or `had no active task; resumed from transcript`. Both are fine.

4. **Then stop.** Integration (merge, mark pool `free`, drop the
   `~/.flt-inflight.jsonl` record, pop the queue) happens only when an agent
   reports NORMAL completion — not now.

## If the orchestrator itself restarted since the agents were spawned

`SendMessage` reports **"No transcript found"**, because the session id changed.
The transcripts still exist under the OLD session's directory. Copy them across:

```bash
cp ~/.claude/projects/<slug>/<OLD-session-id>/subagents/agent-*.jsonl \
   ~/.claude/projects/<slug>/<CURRENT-session-id>/subagents/
```

Then `SendMessage` resumes them normally (verified 2026-07-23, 13/13 resumed).
The slug for this project is `-home-chend-flt-lean`; the current session id is
the uuid in the scratchpad path in the system prompt.

## The other reason an agent needs resuming: it stranded itself

Distinct from a kill. The agent ends a turn saying some version of *"I'll stop
polling and let the poller / `Monitor` / `EXIT=` marker wake me"* — and nothing
is tracking that work, so nothing ever does. It reports as **completed** with a
result that reads like a progress note rather than a final report. The
task-notification is the tell: it fires *because* the agent has no live
background children.

Resume it the same transparent way, then — as a **separate** message, not as
narration wrapped around the resume — state the correct mechanism:

> Only a Bash call issued with `run_in_background: true` wakes you when it
> finishes. A remote `nohup`/`setsid` detach, a completed `Monitor`, and a plain
> foreground `ssh` that died at your turn boundary are indistinguishable from
> your side — none of them notify you.
>
> Two correct shapes, no third: (1) run outlasts your turn → plain foreground
> `ssh` with `run_in_background: true`, then end the turn; (2) you want to watch
> it → poll in-turn until you hold the exit status.

**Fix it once in `/home/chend/.flt-agent-doctrine.md`, not per-agent.** A
recurring behavioural defect is a doctrine bug. Per-resume commentary reaches one
agent, costs context, and risks contradicting what that agent already knows.

## Related

- `.claude/skills/fleet-restart/SKILL.md` — restarting the orchestrator itself,
  which is the situation that creates the cross-session case above.
