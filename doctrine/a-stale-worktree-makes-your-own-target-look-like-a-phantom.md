## A STALE WORKTREE MAKES YOUR OWN TARGET LOOK LIKE A PHANTOM — check the base BEFORE the target

(2026-07-31, `flt-lean-390`.) A task named three leaves with file-and-line references. Two of
the three names did not exist anywhere in the tree, and the third sat ~3600 lines away from the
line the prompt gave. Every naive reading of that is wrong in an expensive direction: "the queue
is stale", "these were renamed", "already proven and the entry survived", "the line numbers were
guessed". The correct reading was none of those — **the worktree was 704 commits behind `main`**,
and the prompt had been written against `main`. After one `git merge --ff-only main` all three
names resolved at exactly the lines the prompt gave, to the character.

The dispatch hook is documented to fast-forward a worktree to `main` at allocation. It did not
here, and nothing in the worktree announces that: `git status` was clean, the branch was a proper
ancestor of `main`, and `git log -1` showed a perfectly ordinary recent-looking commit — a merge
into `merger` from two days earlier, which reads like current work rather than like a stale base.

**So the first command of any task, before reading the target file, is:**

    git rev-list --count HEAD..main     # 0, or you are working against the past
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

This is the same class as the RELEASE WINDOW entry above and its exact mirror image. There, the
leaf is closed on a branch and `main` has not caught up; here, the leaf is *open on `main`* and
your checkout has not caught up. Both make a real target look like a phantom, and both are
invisible to every ownership check in this file, because those checks all reason about records
and branches rather than about **which commit you are standing on**.

Corollary, and it is what makes this cheap to get right: **a file-and-line reference in a task
prompt is a checksum on your base.** If the declaration is not at the named line, do not start
hunting for a rename — check `HEAD..main` first. It costs one command and it is right more often
than any of the interesting explanations.

