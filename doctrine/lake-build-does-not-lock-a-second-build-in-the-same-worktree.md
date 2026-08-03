## `lake build` DOES NOT LOCK — a second build in the same worktree runs RIVAL elaborations

(2026-07-31, measured.) Launching `lake build <Mod>` while an earlier `lake build` is still
running in the SAME worktree does **not** block or queue. Both proceed, and `ps` shows the two
`lake` processes each with their own `lean` children **elaborating the same files**, writing the
same `.olean` paths in `/scratch/chend-flt/flt-lean-N/.lake/build`:

    3307744 lake  lake build Fermat.FLT.FreyCurve.MazurTorsion
    3315601 lean    …/Fermat/FLT/FreyCurve/Semistable.lean      <- child of 3307744
    3330028 lake  lake build Fermat.FLT.FreyCurve.MazurTorsion   <- second invocation
    3330679 lean    …/Fermat/FLT/FreyCurve/Semistable.lean      <- child of 3330028, SAME file

The natural sequence that produces it is innocent: start a baseline build in the background, edit
the file while it runs, then start the verification build. The doctrine's "two rival elaborations
writing one `.olean`" warning was written about a self-detached `ssh`; it applies just as much to
two ordinary foreground builds, and nothing in `lake` prevents it.

**Before launching a build, check for one already running, by cwd:**

    ssh $H 'for p in $(pgrep "^lake$"); do
              case "$(readlink /proc/$p/cwd)" in $HOME/flt-lean-N) echo "$p BUSY";; esac
            done'

**If you find yourself with two, the cheapest safe move is usually to let BOTH finish.** They are
building the same sources, so they write byte-identical content; the torn-olean risk comes from
*killing* one mid-write, not from the overlap. Then run one more `lake build` of the target and
require the `Build completed successfully` line — a replay is cheap and it is what certifies the
artifacts are consistent. Kill only if you must, by PID after a cwd check, never by pattern.

