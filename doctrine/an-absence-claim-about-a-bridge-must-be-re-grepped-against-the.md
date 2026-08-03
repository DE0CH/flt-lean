## AN ABSENCE CLAIM ABOUT A BRIDGE MUST BE RE-GREPPED AGAINST THE FILE THAT OWNS THE BRIDGE LAYER

(Same task.)  The same leaf's Route 2 ended: "Every ingredient exists in
`WeilPairingDescent.lean` (...); what is missing is the bridge from the generic-point
evaluations that file works with to the honest point evaluations `AdjoinRoot.evalEval`."
The first clause was true and checkable, and it is what made the second one convincing —
the author had clearly opened the file they named.  The bridge is
`exists_pointEval_specialization`, PROVEN 2026-07-25, in `WeilPairingStageB.lean`, a
DIFFERENT module, already `public import`ed, stated uniformly in `(Q, m)` precisely so
that it serves both translation and `[p]`-pullback — with a 500-line `EvalsTo`/`SpecPoint`
calculus under it.

**The generalisable point: a development's "bridge layer" is usually its own module, and
it is never the module whose vocabulary the audit is written in.**  An audit written in
the generic-point vocabulary greps the generic-point file; the honest-point layer is
somewhere else by construction, because that is what a layer is.  So before writing (or
believing) "the bridge is missing", grep for the TARGET vocabulary — here
`AdjoinRoot.evalEval` — across the whole import cone and read the file with the most hits:

    grep -rc '<the target vocabulary>' --include=*.lean Fermat/ | grep -v ':0' | sort -t: -k2 -n

`WeilPairingStageB.lean` had 375 hits and was named nowhere in the audit.  Same family as
[[flt-inventory-audits-understate-what-exists]], with the scope error being a MODULE
rather than a repository.

