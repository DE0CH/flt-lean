## YOUR TASK MAY BE DONE ON `merger` AND ITS **RESIDUE** STILL UNOWNED — TAKE THE RESIDUE
(Same run.) The release-window rule says to run `git show merger:<file> | grep -n <name>`
before your first edit, and it says what to do when the answer is "already proven":
decline and report. That is right for a leaf. It is **too weak for a CUT-LEVEL task**,
because a cut-level task names a repair with several steps, and the agent that landed it
on `merger` may deliberately have taken only some of them.
Here the assigned task was the ten-signature `IsTraceGenerated` transport to
`HilbertAuxDeformationDatum`. Steps 1–3 (define the predicate, add the hypothesis to the
two leaves, thread it down the one-call-site-per-step chain) were all on `merger`. Step 4
— the TERMINUS, which the task itself called "the only mathematics in the task" — had been
opened as a named leaf exactly as the task's own fallback instructed, and **nobody was
dispatched at it**, because it did not exist on `main` when the queue was written. That is
the class-5 invisibility of a decomposition performed on an unmerged branch, and the agent
whose task created the leaf is the one best placed to see it.
So the procedure when your target is already closed on `merger`:
1. read the landed version and **enumerate which of your task's steps it took**;
2. if a step was converted into a NEW leaf, that leaf is unowned by construction — grep
   `~/.flt-loop/jobs/*.prompt` to confirm, then take it;
3. **fast-forward your branch to `merger`** (`main` is an ancestor of it, so the FF is
   clean) rather than re-deriving anything against `main`. Your branch then merges as a
   fast-forward, and you cannot land a rival cut of work that is already in.
The cost of (3) is the section above: `merger` may not build. Weigh that before FF-ing —
but note the alternative is worse, since the declaration you need to edit only exists
there.
