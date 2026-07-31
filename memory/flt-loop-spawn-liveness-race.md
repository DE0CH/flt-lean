---
name: flt-loop-spawn-liveness-race
description: "flt-loop can spawn a duplicate job in one worktree (ALIVE_CACHE 20s > TICK 10s); step 0 for any loop-started agent is to check its token against jobs/<name>.json, and a discarded incarnation must yield WITHOUT writing its sentinel"
metadata: 
  node_type: memory
  type: project
  originSessionId: 28ddcca7-defb-4e73-9023-ccae28fdc638
  modified: 2026-07-30T02:34:08.375Z
---

`flt-loop.py` can have two live agents in one worktree with the same payload.
`TICK=10` but `ALIVE_CACHE=20`, and `do_spawn` does not invalidate
`_alive_cache` — so `live_tokens()` may serve a sweep taken *before* the spawn,
making a healthy new job observably `¬alive`. `died()` is
`started ∧ ¬alive ∧ ¬sentinel` and row 9 needs one tick, so a job can be
condemned ~11 s after starting. Observed 2026-07-30 03:29 on the merger
(`15a2888d` killed, `03cc960a` spawned 34 s later; both alive in
`~/flt-staging`). Not merger-specific — any kind can lose its first tick.

**Why:** the loop's `alive` is an ssh sweep for `flt-job-<token>` in argv[0],
cached for throughput; the cache has no lower bound relative to spawn time, and
row 9's *contract* logic (the medic's repair) is correct and not implicated.

**How to apply:** as a loop-started agent, before ANY destructive or shared
write, check your prompt's token against
`~/.flt-loop/jobs/<name>.json` + `.started`. Mismatch ⇒ you are a discarded
incarnation:

- **Yield.** Do not merge, do not build into `~/.flt-release-lake/build` (a torn
  snapshot poisons every agent dispatched after the release), do not rewrite
  `queue1`. Write nothing into the worktree — the twin's `git add -A` sweeps it up.
- **Do NOT write your sentinel.** The loop ignores it (token check) *and*
  overwriting the live twin's sentinel gets its finished release read as a death.
- Leave the report as a file at `~/.flt-loop/` root — inert to `load()`/`save()`,
  survives the `jobs/` pruning, and gets committed into the state repo where a
  medic reads it. Never name it `STOP`.
- `git status` clean + no `lean`/`lake` process does NOT mean idle; the twin may
  be between steps. Re-check after a minute. Same trap as
  [[flt-fleet-13-worktree-protocol]] and the promotion rule in CLAUDE.md.

Fix if authorized (medic's authority, not a worker's): in `do_spawn`,
`_alive_cache["tokens"].add(j["token"])` after the ssh returns.
