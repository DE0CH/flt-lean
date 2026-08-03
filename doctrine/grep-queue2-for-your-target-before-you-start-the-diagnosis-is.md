## GREP `queue2` FOR YOUR TARGET BEFORE YOU START — the diagnosis is often already written
(2026-08-01, `flt-lean-26`, on `geomPic_finite_torsion` in
`ModularCurve/HyperellipticJacobian.lean`.)  Every freshness check in this file
looks at the TREE — your worktree, `main`, `merger`, the other worktrees' diffs.
None of them looks at the QUEUE.  But `~/.flt-loop/queue2` is written by prover
agents who have just been inside your file, and it routinely contains a task
whose text *is* the answer to yours.
Mine did.  Dispatched at `geomPic_finite_torsion`, I re-derived — from the git
history and a consumer scan — that it was a dead orphan of a superseded recut and
a verbatim duplicate of `finite_torsion_pic_geom` two hundred lines above it.  A
`queue2` entry written the same morning said exactly that, named all four
orphans, gave their line numbers, and prescribed the deletion.  One
`grep -n '<target>' ~/.flt-loop/queue1 ~/.flt-loop/queue2` would have started me
twenty minutes further along, and it is the same command that tells you whether
your leaf is queued twice.
**And read the queue for your target's NEIGHBOURS too, because that is where the
race lives.**  The `TARGET:` line of another entry is a claim about work in
flight that no branch shows yet.
