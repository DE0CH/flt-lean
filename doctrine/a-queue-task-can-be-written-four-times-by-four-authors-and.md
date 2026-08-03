## A QUEUE TASK CAN BE WRITTEN FOUR TIMES BY FOUR AUTHORS, AND NOTHING CHECKS FOR IT

(2026-07-31, release 32.)  The release invariant is a COVERAGE condition — every open
leaf is queued or held — and it is one-sided: it detects a leaf with no task and is blind
to a task with three rivals.  The divisor-degree reconciliation
(`CurveDivisorDegree.lean` versus `PrincipalDivisorDegree.lean`) was queued **four
times**: three entries in `queue1` and one in `queue2`, written by three prover agents and
one merge worker on three different days, each careful, each ~2–5 kB, none aware of the
others.  Dispatch is FIFO and blind, so that is four agents making four rival edits to two
modules plus `X0.lean` — the most conflict-hostile shape there is.

It is invisible to every instrument for a specific reason: the four texts share almost no
identifiers with each other (they name the modules, not one declaration), so a
name-keyed scan cannot pair them, and each is INDIVIDUALLY correct, so nothing about any
one of them looks wrong.  What pairs them is the SENTENCE — "reconcile the two rival
divisor-degree modules" — in four wordings.

**So the release check has a second half, and it is cheap: cluster the queue by TARGET
LINE.**  Take each task's first `TARGET:` line, strip the decoration, and look for
entries naming the same file pair, the same module, or the same declaration.  Anything
appearing more than once is a collision waiting to be dispatched.  Then keep exactly ONE
— the most recent, which is the one whose account of the tree is current — and FOLD the
others' unique facts into it under a `SUPERSEDES` heading rather than deleting them: the
three losers here carried, between them, the concrete leaf names, the fact that
`ProgressCensus.lean` imports every module (so the release-31 workaround removed the
collision from the build target and not from the tree), and the lesson that `xdup.py` must
be differenced against the last GREEN release.  None of that is in the survivor.

**Corollary for the merge worker's own bookkeeping, learned by nearly getting it wrong:
after deleting duplicates, RE-RUN the coverage check.**  Dropping three of four copies
deleted the only queue entries naming two of the three leaves of the dead module — the
survivor happened to name all three, so coverage held, but that was luck and not design.
A de-duplication is a queue DELETION and has to be re-verified exactly like one.

