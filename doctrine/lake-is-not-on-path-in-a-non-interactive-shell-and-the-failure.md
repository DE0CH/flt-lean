## `lake` IS NOT ON `PATH` IN A NON-INTERACTIVE SHELL — AND THE FAILURE LOOKS LIKE A BUILD

Same run, same day. A backgrounded `lake build … > log; echo EXIT=$? >> log` produced

    timeout: failed to run command 'lake': No such file or directory
    EXIT=127

The harness's Bash tool initialises from the user profile for *interactive* use, but a
backgrounded compound command got a `PATH` of `/home/chend/node/bin:/usr/local/sbin:…`
with no `~/.elan/bin`. `git` worked, so the shell was clearly functional; only `lake` was
missing. Combined with the doctrine above — *never conclude a build succeeded from the
absence of errors* — note the mirror-image hazard: a 4-line log with no `error` in it and
`EXIT=127` is not a fast clean build, it is a build that never started.

    export PATH=$HOME/.elan/bin:$PATH        # first thing in every lake invocation

The existing memory `flt-ssh-build-needs-cd-and-elan-path.md` records this for `ssh`
invocations. It bites identically for a plain local background Bash call on the owning
host, which is the shape the post-2026-07-30 loop makes agents use most.

