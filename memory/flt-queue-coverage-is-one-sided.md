---
name: flt-queue-coverage-is-one-sided
description: The release invariant finds a leaf with no task and is blind to a task with three rivals; cluster the queue by TARGET line, keep the newest, fold the losers' facts in
metadata:
  type: feedback
---

Release 32: the divisor-degree reconciliation was queued FOUR times — three in
`queue1`, one in `queue2` — by three prover agents and one merge worker on three
days. Dispatch is FIFO and blind, so that is four agents making rival edits to two
modules plus `X0.lean`.

**Why:** coverage is one-sided by construction. The four texts share almost no
identifiers (they name modules, not one declaration), so nothing name-keyed pairs
them, and each is individually correct so nothing looks wrong.

**How to apply:** as the second half of the release queue check, cluster tasks by
their first `TARGET:` line and look for entries naming the same file pair, module or
declaration. Keep exactly ONE — the most recent, whose account of the tree is current
— and FOLD the losers' unique facts in under a `SUPERSEDES` heading rather than
deleting them; the three losers here carried the concrete leaf names, the fact that
`ProgressCensus.lean` imports every module, and the rule that `xdup.py` must be
differenced against the last GREEN release. Then RE-RUN coverage: de-duplication is a
queue deletion and can strand a leaf. Related: [[flt-frozen-main-rots-the-queue]].
