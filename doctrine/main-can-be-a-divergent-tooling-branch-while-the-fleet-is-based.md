## `main` CAN BE A DIVERGENT TOOLING BRANCH WHILE THE FLEET IS BASED ON A RELEASE COMMIT ON `merger`

(2026-07-31, measured.)  Every rule in this file about staleness assumes `main` is the
last green RELEASE and that being behind means being an ancestor.  On this day neither
held: `main` was `5162faa1`, a run of `flt-loop:` tooling commits, and

    git merge-base --is-ancestor <release 27 tip> main   ->  FALSE
    git merge-base --is-ancestor main merger             ->  TRUE

i.e. `main` sits on a side branch that `merger` has since merged, and releases 27 and 28
exist **only on `merger`**.  A worktree advanced to `main` therefore does not contain a
target that was cut two releases ago, and the usual diagnosis — "my worktree is behind,
`git merge --ff-only main`" — silently does nothing about it.

The cheap way to find the base the rest of the fleet is actually on, without trusting any
branch name:

    git merge-base flt-lean-<some other live worktree> flt-lean-<another>

That returned the release-27 tip directly.  Then pick the **last COMPLETED release** on
`merger`, not `merger` itself: the loop log said `row 21  merger HELD the release (red
build)`, so `merger`'s head was mid-release-29 and red, while release 28's tip
(`e110bcba`, one commit before the first `release 29:` subject) is the newest point that
was built green.  `git merge <that sha>` put the worktree where the fleet is.

Corollary for `~/.flt-release-lake`: its `sha` can be OLDER than the base you need
(`7080929d` here, which predates release 27), so a green scratch elaborated against that
snapshot proves nothing about declarations added since.  Check
`git merge-base --is-ancestor $(cat ~/.flt-release-lake/sha) <your base>` before using the
snapshot as an olean source, and rebuild rather than shim when it comes back stale.

