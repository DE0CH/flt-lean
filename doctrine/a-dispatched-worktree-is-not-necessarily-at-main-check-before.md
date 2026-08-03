## A DISPATCHED WORKTREE IS NOT NECESSARILY AT `main` — check before calling a target a phantom

(2026-07-31, `flt-lean-109`.) The dispatch hook is supposed to fast-forward the worktree to
`main`. Mine arrived **575 commits behind** it, clean and on its own branch, so `HEAD` was a
perfectly ordinary ancestor of `main` and nothing looked wrong. One of the two named targets,
`exists_levelOneGeneratingSeq_space_of_charpoly`, **did not exist anywhere in the tree** — and a
`git log -S`/`git log -m -S` sweep across `--all` found only merge commits, which reads exactly
like the "cut, merged, and deliberately declined" case documented below.

It was none of those. The task prompt's line numbers (`:3800`, `:4093`) matched `main` **exactly**,
which is the cheap tell: prompts are stamped against `main` at queue time, so *line numbers that do
not match your file are a statement about your checkout, not about the leaf.* One
`git merge --ff-only main` and both targets were there at the quoted lines.

So the first three commands of any task, before any archaeology:

    git rev-list --count HEAD..main      # MUST be 0; if not, you are not looking at the frontier
    git merge --ff-only main
    sed -n '<quoted line>p' <the file>   # the declaration should be right there

Corollary for the `.lake` seeding, and it is worth 20 seconds against a multi-hour build:
`~/.flt-release-lake/sha` names the commit the snapshot was built at. If

    git diff --stat $(cat ~/.flt-release-lake/sha) main -- Fermat/

is EMPTY, the snapshot is bit-for-bit `main`'s Lean state (only tooling commits landed since), so
`rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/` gives a
fully warm tree. Mine was, and it did.

And `lake` is **not on `PATH`** in a fresh agent shell even when running locally on the owning
host — `export PATH="$HOME/.elan/bin:$PATH"` first, or the build dies instantly with
`lake: command not found` and an `EXIT=127` that is easy to misread as a build failure.

