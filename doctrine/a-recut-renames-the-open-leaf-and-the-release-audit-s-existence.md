## A RECUT RENAMES THE OPEN LEAF — and the release audit's existence test does NOT catch it

(2026-07-31, `flt-lean-360`.) A blocked leaf is often best handled by a RECUT: prove the
named target over a smaller, restated leaf. `exists_ratCube_jInvariant_heegnerPoint` ("`j(τ₀)`
is a cube in `ℚ`") became PROVEN over the new `exists_intCube_jInvariant_heegnerPoint`
("`j(τ₀) = n ∈ ℤ` is a cube in `ℤ`"), count unchanged 1 → 1. That is a legitimate and often
correct outcome — but it creates a phantom-dispatch shape none of the sections above covers.

**The old name survives, as a PROVEN theorem.** So every stale queue entry naming it passes
the release audit's "does this name still exist as a Lean declaration" filter (the check the
`flt-release-deletes-nonleaf-tasks` note describes), gets dispatched, and lands an agent on a
declaration with nothing to prove. The other phantom classes are all *absences* — a deleted
name, a declined merge, a stale worktree — and absence is what every existing check looks for.
A recut leaves a PRESENCE that is merely no longer open, which reads as healthy at every gate.

The filter that works is the compiler's, not the tree's: a queued leaf name is live only if it
is in the module's `declaration uses 'sorry'` warning set. Cross-check queue entries against
that set, not against `grep`. And an agent that recuts owes the new name to `queue` and to
`to_merger` explicitly — the loop cannot infer a rename from a warning-set delta, which shows
only that one name left the set and another entered it, with nothing linking the two.

Corollary for the recutting agent: **say "RECUT, count unchanged" in the commit subject and
body.** A warning-set delta of `−1 +1` is indistinguishable from one closure plus one unrelated
disclosure, and the honest reading is the one that has to be written down.

