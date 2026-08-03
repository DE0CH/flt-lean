## `| head -N` ON A BUILD KILLS THE BUILD — AND THE TRUNCATED LOG LOOKS LIKE A CLEAN ONE
(2026-07-31, cost one full module build, ~25 min.) The doctrine warns never to pipe a
backgrounded build through `tail`. `head -N` is worse and reads as more innocent: it *exits*
after N lines, so the writers upstream get `SIGPIPE` and the whole pipeline — including
`lake` — dies. Here
    lake build <Module> 2>&1 | tee /tmp/b.log | grep -E "error|declaration uses" | head -40
was killed the instant the 40th matching line was printed. `/tmp/b.log` then held 905 lines
ending mid-stream, with **no error lines and no `Build completed`** — indistinguishable at a
glance from a green build in progress, and `grep -c error` on it returns 0.
**Redirect, never pipe:** `lake build <Module> > /tmp/b.log 2>&1; echo "EXIT=$?" >> /tmp/b.log`
and grep the file afterwards. Judge a build by the presence of `Build completed successfully`
plus an explicit `EXIT=`, never by the absence of the word `error` — absence of errors is also
what a killed build looks like.
