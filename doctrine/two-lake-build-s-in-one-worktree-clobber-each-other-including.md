## TWO `lake build`s IN ONE WORKTREE CLOBBER EACH OTHER — including your own two
(2026-07-31, same agent, cost one 20-minute build.) The doctrine's warnings about concurrent
builds are all about TWO AGENTS sharing a worktree. One agent is enough. A downstream build
(`Fermat.FLT.FreyCurve.MazurTorsion`) died with
    error: failed to open file '.../HyperellipticJacobian.olean': No such file or directory
not because anything was wrong, but because I started a rebuild of `HyperellipticJacobian` in
the same worktree while the consumer build was still running, and lake unlinks the olean before
rewriting it. The failure is indistinguishable from a torn `.lake` and reads as a much more
serious problem than it is.
Worse, it is silent until the end: `grep -c error` on the log was **0** while the build was
still running, so an early check says "clean" and the real answer arrives minutes later. Only
the `EXIT=` marker you wrote yourself is a verdict.
So: **one `lake build` per worktree at a time.** If you want a downstream check, run it AFTER
the module it depends on has settled, not alongside an edit-rebuild loop. Scratch-module
`lake env lean` runs are safe to overlap with nothing — they read oleans too.
