## A TASK PROMPT THAT CITES A REPAIR COMMIT IS CITING `merger`, NOT `main`
(2026-07-31, `flt-lean-65`.) A prompt opened with "two repairs landed that day (commits
`f1ca4452` and `b1225666`) and you must read the leaf's docstring before anything else — it
now contains a FALSITY AUDIT and a step-by-step route". Neither commit was an ancestor of the
worktree's HEAD: the dispatch hook fast-forwards to `main`, and both were still sitting on
`merger`. So the docstring in the file was the OLD one, the statement was missing the `htors`
binder the prompt described, and `IsTraceDualFunctional`'s third clause was the weak version
the prompt said had been replaced. **Everything the prompt asserted was true, and none of it
was true in the worktree.** This is the release window (class five) seen from the receiving
end, and it is the normal case for any prompt written by an agent that just finished: the
repair it is telling you about is *its own*, and it has not landed.
The check is two commands and costs nothing:
    git merge-base --is-ancestor <sha> HEAD || echo "NOT PRESENT — go get it"
    git log --oneline main..<sha>          # usually a handful of commits
Then **merge that sha directly, not `merger`.** Here `main..b1225666` was three commits over
two files; merging `merger` wholesale would have dragged an entire release's payload onto a
single-leaf branch for no reason, and made the merge worker's job harder rather than easier.
Say in the report that your branch carries those commits, so the merger knows the duplication
is deliberate.
Corollary for whoever WRITES such a prompt: a sha is not a location. Write
"`b1225666`, on `merger`, not yet on `main` — merge it first", because the reader's tree is
`main` by construction.
