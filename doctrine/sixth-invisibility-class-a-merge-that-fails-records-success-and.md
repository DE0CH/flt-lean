## SIXTH invisibility class: a merge that fails, records success, and drops the payload

(2026-07-29.) `git merge flt-lean-243` printed `error: Unable to write index` and **still
produced a merge commit whose tree was byte-identical to the pre-merge tree** — none of the
branch's changes, while recording that branch as an ancestor. `git status` then reported "All
conflicts fixed but you are still merging", and `git commit --no-edit` sealed it without
complaint. Suspected trigger: the background `git gc` git itself starts ("Auto packing the
repository in the background") during a preceding merge, so the risk concentrates exactly where
branches are merged back to back.

This is worse than every failure class above it, because **the result compiles.** A green build
is not evidence; a dropped payload builds perfectly. The merged branch is then marked merged and
dropped from the batch, so the work is not merely missing — it is unrecoverable through the
normal flow, and the frontier looks like it regressed with no cause anyone can name.

It was caught only because a declaration the merge was supposed to prove was still `sorry`
afterwards. The check is one command per merge:

    git diff --stat HEAD^1 HEAD     # MUST be non-empty if that branch changed files

Empty for a branch that should have changed something → `git reset --hard HEAD^` and re-merge.
`git config --local gc.auto 0` in the staging worktree prevents background packing from firing
mid-merge; it is local and affects nothing else. This matters most for the merge worker, which
merges a hundred-odd branches in one run.

**Corollary, and the reason this belongs beside the other five: "the branch is an ancestor" is
NOT evidence that its content is present.** Every ownership and integration check in this file
that reasons from ancestry — subsumption claims, "X carries Y's commit", the merge-base test in
the three-part ownership rule — inherits this hole. Ancestry is a claim about the commit graph;
content is a claim about trees. Verify the tree when it matters.

**And the honest, non-buggy version of this bites just as hard (2026-07-29).** A merge that
resolves *against* a branch — `-s ours`, or "taking merger's side wholesale" — is CORRECT
behaviour and still leaves the branch a full ancestor while its declarations are gone.
`git merge-base --is-ancestor <branch> merger` returns SAFE; the leaf does not exist. An agent
was dispatched at `projective_localizedModule_quotient_range_of_lTensor_injective`, whose
defining commit `ace07c06` **is** an ancestor of `main`, and found the declaration nowhere in the
tree: merge `8ce9528e` had declined that whole route in favour of a rival cut that ends at two
leaves instead of three.

**The detection trick, because the obvious command hides it: `git log -S <name>` shows only the
commit that ADDED the name and nothing else, so the history reads as "added, never removed".
Removal inside a merge is only visible with `-m`:**

    git log -m -S '<declName>' --oneline -- <path>     # -m is what shows merge-side removals

So a leaf can be absent for three different reasons that all look alike from `main`: never cut;
cut on an unmerged branch (the release window); or **cut, merged, and deliberately declined**.
Only the third is permanent, and only `-m` distinguishes it. Before reporting a phantom name,
run that command — the merge's own subject line usually says which rival cut won and why.

