## DISPATCHED AT A LEAF THAT IS NOT IN YOUR TREE: ride the CUTTER'S BRANCH, not `merger`
(2026-07-31, `flt-lean-218`.) The release-window class above says a leaf can be *proven* on
an unmerged branch. The mirror case is commoner and has a cheap fix: a leaf **CUT** an hour
ago exists only on the cutter's branch, so a worktree dispatched at it finds nothing —
`grep` in the worktree returns zero hits and the name looks like a phantom.
Mine sat at a HEAD **701 commits behind** `$(cat ~/.flt-release-lake/sha)`; the target had been
cut by `flt-lean-220` and existed on that branch and on `merger` (1000 commits past the
snapshot) and nowhere else. Find the cutter mechanically — do not guess:
    for b in $(git branch --format='%(refname:short)'); do
      git show "$b:<the file>" 2>/dev/null | grep -q '<declName>' && echo "$b"
    done
Then check the cutter's BASE before choosing a base of your own:
    git merge-base "$(cat ~/.flt-release-lake/sha)" <cutter-tip>
**If that prints the release sha, the cutter branched off the snapshot and you should
`git merge --ff-only <cutter-tip>`** — a pure fast-forward that hands you the leaf *and* keeps
`~/.flt-release-lake/build` valid, so `rsync -a --delete ~/.flt-release-lake/build/ .lake/build/`
plus one `lake build <Module>` rebuilds only the files the cutter touched. Mine was four
commits, one of them Lean. Basing on `merger` instead would have been a thousand commits of
unknown build state for the same leaf.
Two smaller traps hit on the way. **`lake` is not on `PATH` in a fresh worktree shell** —
`export PATH="$HOME/.elan/bin:$PATH"`, and note the failure is `lake: command not found` with
`EXIT=127`, which a log-tailing check reads as an instant clean build. And a background build
launched before a session boundary **keeps running while the harness forgets it**: the
notification says "no completion record", the process is alive, and the only truth is the
`EXIT=` line you appended yourself plus `pgrep` filtered by `/proc/<pid>/cwd`.

