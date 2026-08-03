## `cmd | tail -N; echo EXIT=$?` REPORTS `tail`'s STATUS — the pipe falsifies the marker you trust
(2026-07-31, `flt-lean-129`, cost one 15-minute build.) The doctrine already says
never to pipe a long build through `tail`, because nothing lands until the process
exits. There is a sharper reason, and it defeats the positive-terminator rule that
exists to catch exactly this:
    ssh $H 'timeout 900 lake build $MOD 2>&1 | tail -20; echo EXIT=$?'
`$?` after a PIPELINE is the LAST component's status — `tail`'s — which is `0`
whatever `lake` did. So that run printed **`EXIT=0` on a build `timeout` had KILLED
at 900 s**: a positive terminator, written by me, and wrong. The visible tail was a
run of green `✔ … Built` lines, which reads as success unless you notice the job
counter `[5649/5671]` never reached its total.
**Redirect, never pipe, and put the marker in the same shell as the build:**
    lake build $MOD > /tmp/b.log 2>&1; echo EXIT=$? >> /tmp/b.log
then read the log. Two further points from the same incident. A `timeout` on a build
whose length you have not measured is a way to manufacture this exact false positive
— leave it off and poll instead. And `Build completed successfully (NNNN jobs)` with
`NNNN` equal to the announced total is the only line that says a `lake build`
finished; `EXIT=0` alone does not, if a pipe stands between it and `lake`.
