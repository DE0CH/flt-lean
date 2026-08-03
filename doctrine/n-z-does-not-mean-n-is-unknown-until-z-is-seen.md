## `∃ n, ∀ z` DOES NOT MEAN `n` IS UNKNOWN UNTIL `z` IS SEEN

(2026-07-31, flt-lean-290.) A leaf's own docstring argued at length that it needed a SECOND,
independent Hermite–Minkowski input, and named the sibling leaf it could not use:

> *"It is NOT supplied by `finite_hilbertInertiaOutsideSubgroups`. That leaf bounds the NUMBER of
> subgroups of index `≤ n` for a GIVEN `n`; here `n` is what is being produced, and no amount of
> counting at a fixed level yields it. … neither implies the other."*

Every clause is wrong, and the whole leaf then fell to one page. **`n` was not what was being
produced.** The thing that must not depend on `z` is the BOUND; the LEVEL at which the counting leaf
gets invoked is free to be any quantity computable from the ambient data. Here `d = N₁.index` and
`p = ringChar k` are fixed by `ρbar` and `k` alone, so `(d·p)!` is such a level — and at that level
the sibling leaf is exactly strong enough, because `⨅ {C : C in that finite set}` is one subgroup,
independent of `z`, that every admissible cocycle dies on.

The general shape, worth checking whenever a `∃ n, ∀ x` leaf is called ATOMIC: **list what is fixed
before `x` is quantified.** In this development that is almost always more than it looks — the
representation, the base field, the finite set of places, the residue characteristic, and every
invariant of them. A "uniform in `x`" obligation is discharged by ANY construction from that list,
not only by one that visibly ignores `x`.

Two corollaries the same day. First, and this is the same family as
[[flt-leaf-cost-estimates-are-hypotheses]] and [[flt-inventory-audits-understate-what-exists]]: a
docstring paragraph saying "leaf A does not imply leaf B" is written by whoever CUT them, before
either was attempted, and is a hypothesis. Try the implication before believing the prose — even
when the prose is careful, cites the right objects, and was written by someone who had just read
both statements. Second: a leaf whose docstring says "the section has TWO Hermite–Minkowski leaves,
best given to one owner" is a dispatch instruction built on that hypothesis, and it survives into
task prompts long after the hypothesis is refuted.

