## A TASK'S OWN "IS THE FILE QUIET" GUARD — and why rebasing onto `merger` is NOT the dodge
(2026-07-31, `flt-lean-291`.) A well-written task that makes an INTERFACE change sometimes ships
with its own precondition: *skip me if `merger` is still carrying an unmerged restructuring of this
region*. That guard is class 7 above stated in advance, and it is one command:
    diff <(git show main:<path>) <(git show merger:<path>) | grep -E '^[0-9]'
The hunk LINE RANGES are the whole answer — you do not have to read the prose. If a hunk boundary
abuts the declaration you were told to edit, the merge will split your signature change from your
call sites exactly as class 7 describes. In the instance that produced this note the guard hunk was
`1365c1374,1483`, ending on the line immediately above the `theorem` line to be changed: an
adjacent-line edit on both sides, i.e. a guaranteed conflict at the one place where a wrong
resolution silently compiles on one side only.
**The tempting workaround is to base the branch on `merger` instead, so there is no boundary. Do
not.** Two reasons, and the second is fatal on its own:
- `merger` is a LIVE branch — it moved between two consecutive `git rev-parse` calls in this very
  session — so "based on merger" names nothing stable.
- The seeded artifacts (`~/.flt-release-lake/build`, rsynced at each release) track **main**. At the
  time of writing `merger` was **867 commits and 164 000 changed lines** ahead of main across 118
  files, so a worktree rebased onto it has no usable `.lake` and must rebuild an unreleased tree
  that nobody has certified green. You would be paying a full mathlib-adjacent rebuild to verify a
  three-line change, against a base whose redness would not be yours.
So the correct response to a fired guard is the one the task asks for: **skip, and re-queue with the
full edit spelled out**, including the current line numbers and the guard restated. That is a full
success, not a wasted cycle — the queued task is strictly cheaper to run after the release than the
conflict repair would have been before it.
