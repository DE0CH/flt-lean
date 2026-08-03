## A DETACHED BUILD WITH `ppid = 1` STILL DIES — the missing `EXIT=` is the only tell

(Same run, twice.)  `setsid --fork bash -c '… ; echo EXIT=$? >> log'` gives `ppid = 1` and
survives session teardown, which is what the doctrine asks for.  It does not survive the
host's memory pressure: both runs ended with the log stopping mid-stream at
`[5262/5272]`, no `EXIT=` line, no error text, and no process left.  `grep -i error` on
that log is empty and `grep -c "declaration uses 'sorry'"` is a plausible number — i.e. by
every check other than the positive terminator it reads as a finished, clean build.

So the standing rule earns its keep in a third distinct way (after truncated `ssh` and
`lake: command not found`): **require the literal `EXIT=` line you wrote yourself, and
`Build completed successfully (NNNN jobs)`, before believing anything.**  When it is
absent, check `free -g` before re-diagnosing the Lean: at 32 GB free out of 2015 with a
load average of 117, the build was killed, not broken.

