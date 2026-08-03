# A RECUT'S ROUTE NOTE MUST NAME WHICH CONTAINMENT THE CITED APPARATUS PROVES — CHECK THE BOOK'S PAGES, NOT THE THEOREM NAMES

(2026-08-03, `flt-lean-170`, on `NormIndex.lean`'s
`exists_artinSymbol_span_eq_one_narrowRay_ray_class`.) The 2026-07-31 recut
replaced the norm-index inequality `n ≤ h` with "the `ray ⊆ ker` half of Artin
reciprocity", on the strength of a route note: the cyclotomic base case is
PROVEN, the auxiliary-field descent apparatus is PROVEN, so "the residual is
one assembly" (Childress pp. 121–123). Every fact in that note is true. The
route is impossible anyway, because **the cited pages prove the OTHER
containment**: Childress pp. 115–123 is Proposition 2.2, `ker ⊆ P⁺·N` — the
containment the tree had ALREADY built (`artinDivisorKernel_le_sup_*`). The
`ray ⊆ ker` direction is obtained on p. 114 by *index counting over Prop 2.2*,
consuming `[I : P⁺N] ≥ [K:F]` — which is verbatim the inequality the recut had
just made DOWNSTREAM of the new leaf. So the recut manufactured a circle and
advertised it as a decomposition, and three months of queue audits passed it
because they graded the inventory's facts, not its direction.

Two mechanical checks, both cheap, either of which catches this class:

1. **Read the cited pages for the QUANTIFIER SHAPE of what they prove**, not
   for whether they exist. A descent that starts "let `a ∈ ker A`" cannot
   prove a statement that starts "let `a ∈ P⁺`" — run the mechanics on the
   wanted input and see what comes out (here: a tautology, since `σ^D` is
   *defined* as the symbol of `a`).
2. **Ask what the classical proof of the RECUT LEAF consumes, and grep the
   tree for where that ingredient's proof now lives.** Here the answer was
   "the parent, one declaration below" — the circle was visible in one grep,
   `hidx₂` discharged via the package via the inequality via the leaf.

Corollary, learned the expensive way by three earlier audits being right and
then overridden: when multiple prior audits say "X is strictly harder than Y,
trading Y for X is a regression", a recut that overrides them must exhibit the
proof-shape that beats the price — a named theorem list is not that; the
containment DIRECTIONS of the named theorems are. The corrected route options
are recorded in the leaf's ROUTE CORRECTION docstring section: reverse the
recut and prove `n ≤ h` cohomologically (Herbrand / ambiguous class number
formula), or pay for BOTH inequalities plus surjectivity to keep the leaf —
strictly more for the same unlock.
