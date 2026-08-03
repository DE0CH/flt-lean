## THE TASK PROMPT'S LINE NUMBERS ARE A CHECKSUM ON THE WORKTREE
(2026-07-31, flt-lean-359; the dispatch template already cited this section by name
before it existed.) A task prompt is written against `main` at dispatch time and
quotes declaration names, and often line numbers, from it. **The loop does sometimes
hand out a worktree that is hundreds of commits stale**: `flt-lean-359` was dispatched
720 commits behind `main` and `flt-lean-350` was 724 behind at the same moment, while
their neighbours were 4 behind (i.e. current). So the first command of every task is
    git rev-list --count HEAD..main      # MUST be 0
and, if it is not, `git status --short` (must be empty) plus
`git merge-base --is-ancestor HEAD main` (must hold) — those two are exactly the
dispatch hook's own preconditions — and then `git merge --ff-only main`. That is a
repair the agent may do itself; it is not a reason to panic the loop.
Why it matters more than it sounds: on a stale tree the target declaration may not
exist at all, or may exist with a DIFFERENT statement, and every ownership and
"is it already proven" check silently answers about a tree nobody else is looking at.
`flt-lean-359`'s two targets grepped as absent-and-present respectively, which read
as "the leaf was renamed" and was in fact "your worktree predates it".
**And the fast-forward is not the end of the check** — `main` is only the frontier as
of the last release (fifth invisibility class above). After fast-forwarding, run
    git show merger:<the file> | grep -n '<your target>'
before writing any Lean. `flt-lean-359` found its target ALREADY DECOMPOSED on
`merger`, under the same name and the same statement, by a branch that landed the
same day the task was written.
