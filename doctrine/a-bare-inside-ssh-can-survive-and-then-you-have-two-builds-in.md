## A BARE `&` INSIDE `ssh` CAN SURVIVE — AND THEN YOU HAVE TWO BUILDS IN ONE WORKTREE
(2026-07-31, observed directly.) A launch written as
`ssh $H '... && (lake build ... > /tmp/log 2>&1; echo EXIT=$? >> /tmp/log) & echo LAUNCHED'`
returned instantly and was assumed dead, so it was re-issued in the endorsed shape (plain
foreground `ssh`, `run_in_background: true`). **Both survived.** Forty minutes later the worktree
had TWO `lake build` processes and FOUR `lean` workers — two on `X0.lean`, two on
`MoretBailly.lean` — writing the same `.olean` paths, and both were redirecting to the same log
with `>`.
The tell is not the log (which looks like one slightly erratic build) but the process table:
    ssh $H 'for p in $(pgrep -x lake); do c=$(readlink /proc/$p/cwd); \
      case "$c" in $HOME/flt-lean-N*) ps -o pid=,ppid=,etimes= -p $p;; esac; done'
Two entries means two builds. Kill the ORPHAN — the one whose `ppid` chain reaches a `bash -c`
with `ppid 1` rather than a live `ssh` — by PID, then sweep `lean` processes in your own worktree
whose `ppid` is `1`. Keep the harness-tracked one; it is the only one that can wake you.
And do not conclude a backgrounded-inside-`ssh` command died just because the call returned: the
doctrine's "a bare `&` over ssh may SURVIVE — the failure mode is duplication, not death" is
literally true, and the duplicate races your real build for the same output files.
