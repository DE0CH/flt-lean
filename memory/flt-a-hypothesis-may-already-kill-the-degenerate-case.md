---
name: flt-a-hypothesis-may-already-kill-the-degenerate-case
description: "A carried arithmetic hypothesis can already exclude the degenerate level; a hand-written branch for it is not just dead code — it hides the route that needs the excluded case gone"
metadata:
  type: project
---

`universal_classifyPullback_special` (X0.lean) carried `hℓN : ¬ ℓ ∣ N`, and its
docstring spent a paragraph proving the `N = 0` case separately ("`YZ` is empty
by `isEmpty_of_isCoarseModuliY0_zero_base`, hence the fibre product is initial,
so no `0 < N` is needed"). **`ℓ ∣ 0` for every `ℓ`, so `hℓN` had already ruled
`N = 0` out.** The whole branch was unreachable:

    have hN : 0 < N := Nat.pos_of_ne_zero fun h => hℓN (h ▸ dvd_zero ℓ)

**Why: the cost is not the dead lines, it is the route the phantom branch
hides.** The obvious attack on that leaf ran through
`nonempty_gamma0AtlasOver_specLoc`, which needs `0 < N`. Reading the docstring
top-down, that looks like a genuine mismatch — the statement is advertised as
holding at `N = 0`, the atlas is not available there, so the atlas route appears
to owe a separate degenerate argument before it can even start. In fact `0 < N`
was one line from a hypothesis the statement had carried since it was written,
and the route was unobstructed. The same paragraph appears on
`exists_isCoarseModuliY0_loc`, where it is real (`hℓN` is present but the case
split is genuinely taken) — which is exactly why it reads as credible on the
neighbour.

**How to apply:** before accepting "route X needs `0 < N` / `n ≠ 0` /
`char ≠ p` which this leaf does not have", check the hypotheses it *does* carry
for one that implies it — `¬ a ∣ b` kills `b = 0`, `IsUnit`/`Invertible` kills
the zero characteristic case, a nonempty-fibre or `Nonempty` field kills the
empty one. And treat a docstring paragraph discharging a degenerate case as a
*claim to check*, not a fact: it is written when the statement is opened, and
nobody re-derives it when a hypothesis is later added. Cheapest possible check —
ask Lean for the one-liner and see whether it compiles.

Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-inventory-audits-understate-what-exists]],
[[audit-searched-production-not-invariant]].
