## IF YOUR TARGET IS NOT IN YOUR WORKTREE AT ALL, YOU ARE ON `main` AND `main` IS BEHIND `merger`

(Same task, same day.) The worktree was dispatched onto `main`, and `flat_finrank_cartierDual` did
not exist anywhere in the file. Not renamed, not moved — absent. `main` was **867 commits behind
`merger`**: release 27 had been built on `merger` and not yet promoted, so `main` was two releases
stale while every task prompt was being written against `merger`'s frontier.

This is the "release window" trap in its sharpest form: the usual symptom is a leaf that is already
proven, and this is the mirror — a leaf that does not exist yet. Both come from the same cause and
both are resolved by the same one-line check *before* reading anything:

    git log --oneline -1 main merger
    git merge-base --is-ancestor main merger && echo "main is BEHIND merger"

If `main` is behind, `git merge --ff-only merger` first and work there. The merge worker merges into
`merger`, so basing on `merger` costs nothing and a branch based on a stale `main` silently
re-litigates hundreds of commits at merge time.

