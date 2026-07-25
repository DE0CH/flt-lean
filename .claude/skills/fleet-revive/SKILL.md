---
name: fleet-revive
description: Sweep the fleet for dead agents — ones that stopped without finishing — and resume them. Covers agents stranded waiting on an untracked build, agents that reported "completed" with a progress note instead of a final report, and any stopped agent whose worktree is still claimed. Distinct from /fleet-resume, which is specifically kill recovery.
---

# Revive dead agents

A **dead** agent is one that is stopped but not finished. Its worktree is still
`claimed`, its work is unmerged, and nothing is going to restart it. It is not
an error state anyone gets notified about — the fleet just quietly loses a
worker, and the loop invariant ("every sorry has an owner at all times") is
silently false.

The most common cause by far: the agent ended a turn expecting to be woken by
something the harness was never tracking.

## Two kinds, and how to tell them apart

Read the agent's last result text. The distinction is not the status field.

**Dead — stopped mid-task.** Status is often `completed`. The result reads like
a progress note, not a report: *"I'll pause here and resume when the watcher
fires"*, *"blocked on compute"*, *"nothing further to do until Lean answers"*,
*"I'll stop polling and let Monitor `xyz` wake me"*. It usually contains no
commit hash and no verification verdict. **Revive it.**

**Genuinely finished.** The result is a report: outcome, new sorried leaves with
names and line numbers, commit hash, and how it verified. **Integrate it** —
merge, mark the slot `free`, drop its `~/.flt-inflight.jsonl` record. Do not
resume it.

The task-notification carries the decisive hint either way: it fires *because*
the agent has no live background children. So an agent that says it is waiting
on a background job is, by the fact that you received the notification at all,
waiting on nothing.

## Finding them

**The notification stream is the ground truth.** The harness sends a
task-notification whenever an agent stops. An agent you have received no
notification about is still live — possibly sitting inside a two-hour
`lake build`, which looks identical to death from outside. So the candidate set
is exactly: agents that notified you, minus the ones you integrated.

`TaskList` does NOT list agents — it is the unrelated TODO list, and returns
"No tasks found" on this project. Do not reach for it here.

**Do not sweep by output-file mtime.** Tried 2026-07-25: it reported 70 of 82
agents "stale" and 12 live, because an agent inside any long tool call appends
nothing for as long as that call runs. Acting on it would have injected messages
into ~60 healthy agents mid-build. Staleness cannot distinguish working from
dead, and no disk-side signal can.

To reconcile which stopped agents were never integrated, map worktrees to their
current agent and check them against the notifications you have handled:

```bash
grep ' claimed$' ~/.flt-worktree-pool
python3 flt-owner.py --all      # worktree -> current agent id, from transcripts
```

`flt-owner.py` reads the subagent transcripts and takes only the LATEST dispatch
per worktree. Use it, not `~/.flt-inflight.jsonl`, and never dispatch order.

## Reviving

Two messages, in this order. Do not merge them into one.

**1. The resume — transparent.** Send the bare word `continue`. The agent
resumes from its transcript and should not experience an interruption. No state
summary; its transcript already holds everything (Deyao, 2026-07-25: *"resume
from their transcript so the resume is transparent to the agents"*).

**2. The mechanism — only if it stranded itself**, as a separate message:

> Only a Bash call issued with `run_in_background: true` wakes you when it
> finishes. A remote `nohup`/`setsid` detach, a completed `Monitor`, and a plain
> foreground `ssh` that died at your turn boundary are indistinguishable from
> your side — none of them notify you.
>
> Two correct shapes, no third: (1) run outlasts your turn → plain foreground
> `ssh` with `run_in_background: true`, then end the turn; (2) you want to watch
> it → poll in-turn until you hold the exit status.

## Do not salvage

Same prohibition as `/fleet-resume`: touch nothing in the worktree, revert
nothing, merge nothing before resuming. The uncommitted state is what the
agent's transcript refers to.

## Fix the cause once, not per agent

If several agents strand themselves the same way, that is a doctrine bug. Edit
`/home/chend/.flt-agent-doctrine.md` so every future dispatch gets it, instead of
messaging the ones you happened to notice. Per-agent commentary reaches one
agent, costs context, and risks contradicting what that agent already knows.

## Related

- `.claude/skills/fleet-resume/SKILL.md` — kill recovery (usage limit, crash).
- `.claude/skills/fleet-restart/SKILL.md` — restarting the orchestrator itself.
