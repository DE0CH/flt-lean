## `lake` IS NOT ON PATH in a fresh agent shell, even on the owning host

Same day, one wasted build round. `lake build …` returns `lake: command not found`, `EXIT=127` —
the harness's Bash shell does not pick up elan's shim directory. Prefix every build with

    export PATH="$HOME/.elan/bin:$PATH"

`EXIT=127` with an otherwise empty log is this, not a broken worktree. Note it looks nothing like
the memory-filed ssh trap (`flt-ssh-build-needs-cd-and-elan-path`), where a missing `cd` makes
`elan` DOWNLOAD a toolchain and the build merely appears slow; this one fails instantly.

