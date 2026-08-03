## A "THIS HYPOTHESIS IS LOAD-BEARING" AUDIT IS SCOPED TO THE DECLARATION ITS AUTHOR READ — follow the hypothesis to the line that SPENDS it
(2026-08-01, `flt-lean-265`, closing `exists_aut_of_isTorsionReduction_two` in
`FreyCurve/IsogenySignature.lean` — the whole residue-characteristic-`2` gap of the `B₀`
cluster, open since 2026-07-29.)
That leaf existed because a dated, careful, twice-quoted audit on its odd sibling concluded
**"`hq2 : q ≠ 2` IS LOAD-BEARING FOR THE ROUTE ABOVE, AND ONLY FOR IT"**, and — its own words
— *"the audit was begun in order to DELETE this hypothesis and concluded the opposite"*. Its
two factual bullets were true: the statement is true at `q = 2`, and the route does invert `2`,
at exactly one step, to read `s` off `2s = u a₁' - a₁` and `t` off `2t = u³a₃' - a₃ - r a₁`.
Its conclusion — *"so the honest split is: this leaf keeps `hq2`, and `q = 2` is a SEPARATE
leaf"* — was false, and the reason is one an audit of this shape will make every time.
**The division by `2` is not a step of the leaf. It is a step of a MATHLIB-FACING LEMMA two
levels up** (`variableChange_valuation_of_valuation_Δ_eq_one`, about a valuation subring of an
arbitrary field, with no `q` anywhere in it). The leaf spends `hq2` at exactly ONE line — the
appeal to `exists_inertiaVariableChange` — and everything else in its 130-line body is already
uniform in `q`. So the repair was never "a second leaf with a different geometric argument";
it was **a second proof of the upstream lemma**, and it is invisible from the leaf, because
from there `hq2` genuinely is consumed.
**The check, and it is one `grep` per hypothesis: find the line that SPENDS `H`, and ask which
declaration owns that line.** If the answer is not the declaration you are auditing, your
verdict is about somebody else's proof and the repair belongs to them. An audit that traces a
hypothesis to a real obstruction and stops at the module boundary produces exactly this: a
correct diagnosis attached to the wrong node, which then becomes a leaf nobody can close,
because the thing to fix is not in it.
### The mathematics, because it is short and reusable
**`max (v 2) (v 3) = 1` in EVERY valuation subring of every field** — `3 - 2 = 1`, so
`1 = v 1 ≤ max (v 3) (v 2)`, and both are `≤ 1` because `𝒪` is a subring. Three lines. So a
theorem needing "`2` is a unit" and a theorem needing "`3` is a unit" together cover
everything, with NO hypothesis on the residue characteristic. `valuation_two_or_three_eq_one`.
At `v 3 = 1`, Silverman *AEC* VII.1.3(b) needs no division at all:
* **`v r ≤ 1` from the `b₈`-relation**, `u⁸b₈' = b₈ + 3r b₆ + 3r² b₄ + r³ b₂ + 3r⁴`
  (mathlib's `variableChange_b₈`). `r` is the ONLY change-of-variables entry occurring in it,
  so it does not interleave with `s` and `t` at all, and `3r⁴` strictly dominates once
  `v r > 1`. This is cheaper than the `a₆`-relation argument the `2`-inverting proof uses for
  the same step, which has to carry `v t` along with it.
* **`s` and `t` are then roots of MONIC quadratics** over `𝒪` — `s² + s a₁ = a₂ + 3r - u²a₂'`
  and `t² + t(a₃ + r a₁) = a₆ + r a₄ + r²a₂ + r³ - u⁶a₆'` — and `X² ≤ max(X, 1)` forces
  `X ≤ 1`. No integral-closure lemma needed; the ultrametric inequality does it directly.
**Generalisable beyond elliptic curves: when a `2` blocks you, check whether `3` is a unit and
look for the relation in which your unknown appears ALONE.** The `b`-invariants exist precisely
to isolate `r`, and the price of using `b₈` is that all five `aᵢ'` must be integral rather than
three — which at any real call site (here the model and its Galois conjugate) is free.
### Accounting, stated the way this file asks for
Frontier **−1**, verified by name and not by count: the pre-edit file has 6
`declaration uses 'sorry'` warnings and the post-edit file has 5, the difference is exactly
`exists_aut_of_isTorsionReduction_two`, and no new warning appeared. `exists_inertiaVariableChange`
and `exists_aut_of_isTorsionReduction` both LOST their `hq2`, so the `by_cases q = 2` at the
Serre–Tate step of `exists_frobeniusAut_of_potentiallyGoodReduction_two` is gone and the `_two`
variant is deleted rather than kept as a corollary — keeping it would have made it
consumerless, i.e. free-floating.
**Where the generalisation was deliberately STOPPED, and why it is a queued task and not an
omission:** `exists_torsionFrame` and the six theorems above it still carry `hq2 : q ≠ 2`
binders that are now unused (the first is renamed `_hq2`). Propagating the removal is a
seven-signature interface change with call sites in three modules — the class-7 split hazard —
and it buys nothing until a consumer at `q = 2` actually appears. Removing it in the same
commit as the mathematics would have made the mathematics unreviewable.
