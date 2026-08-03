## AN ORPHANED `lean` BLOCKS FOREVER AND LOOKS EXACTLY LIKE A SLOW ELABORATION

(2026-07-31, same worktree.) A backgrounded `lake build` had its `ssh` torn down at a turn
boundary. `lake` died; its `lean` child survived with `ppid = 1` and **hung forever writing its
`--json` diagnostics into the now-closed pipe.** After 2.4 hours of wall clock it showed
`etimes = 8727`, `VmRSS = 12 GB`, and a plausible `cmdline` elaborating a 48k-line module.

That is *precisely* the signature the standing doctrine tells you to leave alone — "rising
`etimes` and multi-GB RSS = elaborating". **It is wrong for an orphan, and `etimes`/RSS cannot
tell the two apart**, because a blocked process keeps its memory and keeps ageing.

The discriminator is CPU time, and only a DELTA of it (the total is large and looks healthy —
this one had burned 1636 s of real work before it stalled):

    ssh $H 'p=<pid>; a=$(awk "{print \$14+\$15}" /proc/$p/stat); sleep 20; \
            b=$(awk "{print \$14+\$15}" /proc/$p/stat); echo "ticks/20s: $((b-a))"'

`0` means dead-but-not-exited: kill it by PID after confirming `/proc/<pid>/cwd` is yours. A
healthy worker returns ~100 ticks per second of wall clock (one core), since elaboration is
single-threaded.

**And the prevention is free: never let `lake`'s output go to a pipe you might drop.** Redirect
to a FILE inside the remote command — `bash -c "lake build > /tmp/log 2>&1; echo EXIT=\$? >> /tmp/log"`
under `setsid --fork` — and the orphan finishes normally even if every parent dies. The
truncated-log hazard the doctrine warns about is the same bug seen from the other end.

