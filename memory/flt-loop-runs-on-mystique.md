---
name: flt-loop-runs-on-mystique
description: "The flt-loop state machine runs on mystique (= MEDIC_HOST), not on the medic's own host; it now re-execs onto edited source by itself, and a live Claude session there respawns it if killed"
metadata: 
  node_type: memory
  type: project
  originSessionId: 76ca355f-ad55-4e1f-9a4d-95adeda8d2e4
  modified: 2026-07-30T04:26:11.848Z
---

The loop process lives on **mystique** — `flt_loop_rows.MEDIC_HOST` — while a medic
spawned by it typically runs on **nightcrawler** (its worktree is `~/flt-lean`, and
`r5_action` places a job on its worktree's host, so the medic does *not* run where the
loop does). So `ps -p $(cat ~/.flt-loop/loop.lock)` from the medic's own host reports
"not alive" for a perfectly healthy loop, and `flt-loop-status.py` prints the alarm
"the loop process is not running" for the same reason. Sweep the hosts, or just go to
mystique.

**DO NOT hand-restart it to pick up a source edit — as of 2026-07-30 the loop adopts
its own repairs.** `adopt_source()` hashes `flt-loop.py` + `flt_loop_rows.py` every
tick, and on the first tick with **no medic record** it runs `--dry-run` against the
changed source and `os.execv`s onto it (same pid, so `loop.lock` stays valid; same
fds, so `loop.out` carries on). Edit, commit, and just leave it — your LAST edit is
what gets adopted.

**Why:** hand-restarting is what produced fault 5. A medic restarted the loop, then
found a further fault *from its own commit* and fixed it into the source of a
five-minute-old process; the old table applied its GO and panicked on the next tick
for the reason the new table could not. The transition trace then lies — `git log` in
the state dir shows rows firing out of a table that no longer exists on disk, so the
next medic dry-runs a repaired guard, watches it match, and cannot explain the panic.

**How to apply:** after editing, check `loop.out` for `source changed and dry-runs
clean -> re-exec onto it`. If the dry-run fails the loop keeps the old table and
emails "edited source refused" — that is the one case where the process really is
running code you did not write.

If you must start one anyway: **the `cd` is not optional** — ssh lands in `$HOME`, and
`python3 -u flt-loop.py` there fails with `can't open file '/home/chend/flt-loop.py'`.

    ssh mystique 'cd ~/flt-lean && setsid --fork nohup python3 -u flt-loop.py \
                    >> ~/.flt-loop/loop.out 2>&1 </dev/null'

`take_lock()` makes a takeover safe without cleanup — it reads the stale pid, finds no
`flt-loop.py` in `/proc/<pid>/cmdline`, and proceeds. Never hand-clear `loop.lock`. A
"refusing to start" line beside a "flt-loop running" line is the lock working.

**There IS an undocumented respawner, contrary to what this note used to say.** No cron
(chend is denied `crontab` on mystique) and no systemd unit — but a Claude session has
been alive on mystique in tmux `agent-2` since 2026-07-26 (`claude --resume 852090c5…
--fork-session`), and when the loop was killed at 05:22 on 2026-07-30 a replacement
appeared ~25 s later with `ppid 1`, `cwd=~/flt-lean`, and that session's `CLAUDE_PID`
in its environment. So a kill does not reliably stop the loop, and a replacement may
not be yours. Check `flt-loop running, pid …, source <digest>` in `loop.out` against
`source_digest()` to see whose source actually won.

Related: [[flt-loop-spawn-liveness-race]], [[claude-is-a-pure-function]],
[[flt-machine-migration]].
