## AN AGENT WHOSE TARGETS ARE ALREADY PROVEN SHOULD STILL BUILD — that build IS the release build, run a day early

(2026-07-31, `flt-lean-105`.) All three assigned TARGETs were already proven on `merger`
— the release window, class five above — so the honest report was "nothing to do" and the
worktree could have been freed in ten minutes. Building the merged tree anyway found a
**duplicate-declaration blocker sitting on `merger` itself**: `Fermat.modPullbackSheafifyIso`
declared in BOTH `ModularCurve/RelativePicard.lean` (general, at a presheaf) and
`Modularity/AmpleSheaf.lean` (specialised, at a tensor of two sheaves), with the second file
`public import`ing the first. Both files were byte-identical to `merger`, so this was not
merge fallout in one worktree — it was the next release build, failing, found before the
release started.

It is the cross-FILE form of class 7 that the interface-split section already names, and it
is worth restating because of how it hides: the two declarations are 60 000 lines and one
file apart, neither branch conflicted with the other, `git diff` is clean, and the ONLY
symptom is `` `X` has already been declared `` followed by application-type mismatches at
the call sites — where the imported version silently wins and the arity is wrong. A per-file
duplicate scan cannot see it. The repair is a rename plus its call sites: the general
version keeps the short name, the specialisation takes the longer one.

**So the rule: an agent that finds its targets already closed has not finished. Run
`lake build` on its module anyway before writing the sentinel.** The cost is one build in a
worktree that is otherwise idle; the payoff is that release-blocking breakage is found by a
worker with time to fix it rather than by the merge worker with a hundred branches queued
behind it. `to_merger` is then the channel, since the fix lives in files the agent was never
assigned.

Corollary for the same situation: the useful work is one level DOWN. The three targets'
residues — the leaves their proofs opened — are named in their own docstrings, are unowned by
construction (they did not exist when the queue was written), and are exactly what the next
dispatch would have to find anyway.

