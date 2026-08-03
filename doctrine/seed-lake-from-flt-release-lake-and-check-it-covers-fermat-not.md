## SEED `.lake` FROM `~/.flt-release-lake` — AND CHECK IT COVERS `Fermat/`, NOT JUST MATHLIB
(2026-07-31, measured: >1 h of cone rebuild replaced by 55 s of rsync.) A freshly repointed
worktree's `.lake` is stale for the whole PROJECT cone, not merely for mathlib. Building
`HilbertModularity` from it spent 30 minutes inside `FreyCurve/Semistable.lean` alone and had not
reached the target file. The release snapshot is not just a mathlib cache — it holds the project
oleans too, and it is usually EXACTLY right:
    git diff --stat $(cat ~/.flt-release-lake/sha) main -- Fermat/     # empty => snapshot is current
Empty means every `Fermat/` olean in the snapshot is valid for `main`, because releases move `main`
by tooling-only commits afterwards. Then, on the owning host:
    kill the worktree's own lean/lake by PID first   # rsync into a live build dir corrupts it
    rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/
After that only your edited file elaborates. Two traps met while doing it: `pgrep -f` matched the
remote `bash -c` of the ssh command itself and killed the shell mid-loop, so match `pgrep -x lean`
/ `pgrep -x lake` and filter on `/proc/<pid>/cwd`; and `--delete` is wanted, since the point is to
remove the stale oleans, while `.lake/packages` sits outside `build/` and is untouched.
