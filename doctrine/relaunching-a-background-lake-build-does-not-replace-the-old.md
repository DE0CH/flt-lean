## RELAUNCHING A BACKGROUND `lake build` DOES NOT REPLACE THE OLD ONE — you get N of them in one worktree

(2026-07-31, `flt-lean-367`, self-inflicted.) A `lake build` launched with
`run_in_background: true` keeps running **after it prints errors**: `lake` reports the failed
module and carries on building every other target in the cone, for another twenty minutes. So
the natural loop — see errors → fix the file → launch the build again → see errors → fix →
launch again — ends with **three concurrent `lake` processes in the same worktree**, all
writing the same `.lake/build` and, because the command line was copied, **the same log file**.

It is invisible by construction, and every check you would naturally run agrees with the
mistake:

* the log looks like ONE build, because the newest writer truncated it and the others append
  into it — job counters from different builds interleave and read as monotone progress;
* `grep EXIT=` finds nothing, since none of them has exited;
* the harness's own completion notification for the older call never arrived, which reads as
  "that call is over" and means the opposite.

It was found only by `ps -eo pid,ppid,etimes,args | grep '[l]ake build'` returning three rows
with three different `etimes`. This is the two-agents-one-worktree collision of the
`flt-lean-86` incident with no second agent — the same shared `.lake`, the same interleaved
`lean` workers writing one `.olean` — so treat it with the same seriousness.

**Rules.** Before launching a build, list your own `lake`/`lean` processes and kill the stale
ones BY PID after confirming `/proc/<pid>/cwd` is your worktree (never by pattern — see the
doctrine). Give each launch its own log file. And do not read "errors appeared" as "the build
stopped": only the `EXIT=` line you appended yourself says that.

