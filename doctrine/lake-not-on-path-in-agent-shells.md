## lake not on path in agent shells

(Cut verbatim out of CLAUDE.md's `Verification is the COMMAND LINE. No MCP, no LSP, no servers` section at the 2026-08-03 doctrine split; nothing reworded.)

**`lake` IS NOT ON PATH IN AN AGENT'S SHELL, AND THE FAILURE LOOKS LIKE A CLEAN
BUILD** (2026-07-31, cost one round). The harness's `Bash` runs a non-login
shell that never sources the profile, so `~/.elan/bin` is absent — *even when
you are already on the owning host and no `ssh` is involved.* The existing note
about this is filed under ssh, which is why it reads as not applying locally.
It does apply. Export it yourself, every call:

    export PATH="$HOME/.elan/bin:$PATH"

The reason it costs a round rather than a second is the SHAPE of the failure.
`lake: command not found` exits **127**, and the log contains no `error`, no
`warning`, no traceback — so `grep -i error` is EMPTY and `grep -c "declaration
uses 'sorry'"` is `0`. Read as "no errors, no sorries", that is indistinguishable
from a perfect build, and it is the same trap the doctrine's truncated-log
section describes arriving by a different route. **Require the positive
terminators — a literal `EXIT=0` *and* a `Build completed successfully (NNNN
jobs)` line with a plausible job count.** An `EXIT=` that is not `0` is a
failure however empty the log looks; zero sorry warnings from a build that never
ran is the most confident wrong answer available.

**`lake` IS NOT ON THE AGENT'S PATH, EVEN LOCALLY, AND THE FAILURE LOOKS
LIKE A FINISHED BUILD** (2026-07-31, flt-lean-106). Since the loop took
over, a prover agent runs *on* its worktree's host and calls `lake`
directly — no `ssh`, so the `cd`-plus-elan-PATH wrapper the ssh recipe
above carries is skipped, and the agent's shell has only
`~/node/bin:/usr/local/bin:/usr/bin:…`. The result is

    /bin/bash: line 1: lake: command not found
    EXIT=127

which, launched in the background with output redirected, is a **6-line
log that returns in one second and contains no `error:`** — i.e. it
passes the "no errors in the log" eyeball test and the harness reports
exit 0 for the wrapper. Export the PATH in every `lake` call:

    export PATH="$HOME/.elan/bin:$PATH"

and require `EXIT=0` *plus* `Build completed successfully` before
believing a build, per the doctrine's positive-terminator rule. A
127 is a missing binary, not a missing proof.

