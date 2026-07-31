---
name: flt-cut-the-derived-half-out-of-a-leaf
description: A leaf stated with a DERIVED quantity (a dimension count, an index, a rank) usually splits into elementary geometric clauses plus a pure-algebra derivation you can prove today
metadata:
  type: project
---

When a `sorry` leaf's conclusion mentions a derived numerical invariant —
`Module.finrank`, a degree, an index, a cardinality — ask first whether that
number is *derivable in pure algebra* from clauses the intended geometric proof
would produce anyway. It usually is, and cutting it out removes the entire
linear-algebra half of the leaf without touching the geometry.

Worked instance (2026-07-31, `Fermat/FLT/ModularCurve/EllipticScheme.lean`).
`exists_poleOrder_of_affineComplement` asked for a pole order `deg` on
`R = Γ(A ∖ {O})` **and** `finrank K {r | deg r ≤ n} = n` for `n ≥ 1` — nominally
"Riemann–Roch on a genus-one curve", with no genus, no divisors and no
Riemann–Roch anywhere in the pin. The dimension count turned out to follow from
three ELEMENTARY clauses:

* `∀ r ≠ 0, deg r ≠ 1` (no simple pole — genus `≥ 1`);
* `∃ x, deg x = 2` and `∃ y, deg y = 3` (genus `≤ 1`);
* two elements of equal pole order differ by a `K`-multiple of smaller pole
  order (the residue field at `O` is `K` — true because `O` is a SECTION).

`PoleOrderFiltration.finrank_poleFiltration` proves the count from those in
~120 lines: `hdesc` gives `dim L n / L (n-1) ≤ 1`, the semigroup `⟨2,3⟩ = ℕ ∖ {1}`
gives `= 1` for `n ≥ 2`, and no-simple-pole gives `L 1 = L 0 = K·1`. The leaf
that remains mentions no `Module.finrank` at all.

**Why:** [[flt-cleaner-statement-harder-proof]] says cut on whether the halves
would be proved the SAME WAY. A dimension count and a curve-theoretic pole order
are proved by completely different means, so they were never one leaf.

**How to apply:** before attacking a leaf whose conclusion carries a number,
write down the elementary clauses a textbook proof produces on its way to that
number, and try to derive the number from them alone. If you succeed you have
converted a research-scale leaf into an elementary one and banked verified code
either way.

**One trap when you do this**: the axioms you extract may not PIN the object.
Here `deg' = 2·deg` satisfies every valuation clause, so `∃ x, deg x = 2` cannot
be split off into its own top-level leaf about "any such `deg`" — it would be
false. Sub-clauses about an existentially-quantified object have to stay bundled
with the existential unless something in the bundle makes it canonical. See also
[[flt-two-leaves-may-be-one]].
