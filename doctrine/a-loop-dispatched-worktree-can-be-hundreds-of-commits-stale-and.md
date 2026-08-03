## A loop-dispatched worktree can be HUNDREDS of commits stale, and `lake` is not on `PATH`

(2026-07-31, `flt-lean-235`, cost ~10 minutes but would have cost a whole run had it gone
unnoticed.) Two facts about the state a prover agent actually wakes up in, neither of which is
stated in the task prompt:

- **`lake`/`lean`/`elan` are NOT on the default `PATH`** of a fleet worker's shell. The first
  command run was `lake build …`, which returned `lake: command not found` and **exit 127** — a
  build log that looks like a build failure. Every shell needs
  `export PATH="$HOME/.elan/bin:$PATH"` prepended; it does not persist between Bash calls.
- **The worktree may not be at `main`.** `flt-lean-235` was dispatched sitting on an old `merger`
  commit, **704 commits behind `main`**, with a `.lake/build` to match. The task prompt's line
  numbers were `main`'s, so every one of them pointed at unrelated code, and a repo-wide grep for
  the three target declarations returned **nothing at all** — which reads exactly like "these
  leaves were deleted/renamed since the queue was written", the diagnosis that ends a run in a
  `to_merger` note instead of a proof.

So the first two commands of any prover run, before reading the target file:

    export PATH="$HOME/.elan/bin:$PATH"
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

Then seed artifacts rather than building mathlib: `~/.flt-release-lake/sha` names the commit the
snapshot was built at; if `git log --name-only <sha>..main` touches no `.lean` file the snapshot is
**exactly current** for Lean, and

    rsync -a --delete ~/.flt-release-lake/build/ .lake/build/

turns a 704-commit-stale tree into a green one. `lake build <Module>` then confirmed
`Build completed successfully (5590 jobs)` in a couple of minutes with nothing to elaborate.

Corollary for triage: **"the declaration does not exist anywhere in the tree" is a
wrong-checkout symptom before it is a rename symptom.** Check `git log --oneline -1 main` against
`git log --oneline -1` before believing a grep that returns zero.

