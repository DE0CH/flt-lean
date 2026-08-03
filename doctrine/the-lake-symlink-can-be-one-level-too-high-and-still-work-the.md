## THE `.lake` SYMLINK CAN BE ONE LEVEL TOO HIGH AND STILL WORK — the documented tell does not fire
(Same task, and it corrects the detection half of the section above on this trap.)  That
section says to check `ls ~/flt-lean-N/.lake/packages` and expect it to be missing when the
symlink points at the PARENT.  **On a worktree where a previous runaway already ran, that
check SUCCEEDS**, because the runaway cloned mathlib and built it at the wrong level.  Here
both trees were complete and 7.0 G each:
    ~/flt-lean-91/.lake -> /scratch/chend-flt/flt-lean-91          <- WRONG, and working
    /scratch/chend-flt/flt-lean-91/{build,config,packages}          <- the runaway's junk
    /scratch/chend-flt/flt-lean-91/.lake/{build,packages}           <- the real one
So `lake build` is green, nothing clones, no log line is unusual, and ~10 G is wasted
silently.  **The tell that always works is the symlink TARGET, not what is under it:**
    ls -ld ~/flt-lean-N/.lake    # the target path MUST end in `/.lake`
Repair is `rm .lake && ln -s /scratch/chend-flt/flt-lean-N/.lake .lake`, then re-seed the
PROJECT build (`rsync -a --delete ~/.flt-release-lake/build/ .lake/build/`) — the mathlib
package builds live under `.lake/packages/*/.lake/build` and are not touched by that rsync.
Check the worktree is quiet by PID first.  Do not delete the junk siblings in the same
commit as Lean work: they are 10 G of somebody else's machine-local state, `.lake` is not
tracked, and no commit carries the repair either way.
