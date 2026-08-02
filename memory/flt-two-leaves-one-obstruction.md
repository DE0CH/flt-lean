---
name: flt-two-leaves-one-obstruction
description: "Two leaves can duplicate an OBSTRUCTION rather than a statement — grep the docstring prose, since no identifier or statement scan can see it"
metadata: 
  node_type: memory
  type: project
  originSessionId: 9c698dbd-97e6-4e96-abc3-a1681ba5c197
  modified: 2026-08-02T19:40:41.331Z
---

Two leaves can be genuinely different theorems and still carry ONE piece of
missing mathematics, one being provable from the other. `dupstmt.py`, `xdup.py`,
`own.py` and every statement-level scan are silent: the two share no name, no
type and no conclusion. What matches is the DOCSTRING PROSE naming the
obstruction.

Measured 2026-08-02, `Modularity/TateModule.lean`:
`exists_ne_zero_mem_torsion_isMaximal_finiteBase` said its whole content was
"the `ℓ`-INDEPENDENCE of the local ranks, i.e. genuine Tate-module theory";
`finrank_mulByElt_of_relativeDimension`, a `sorry` leaf 20 000 lines above in
the same file, says "the exponents `dᵢ` are the local ranks, and their equality
is precisely what the Galois argument supplies". `grep -n "local ranks" <file>`
finds both. The first is now PROVEN over the second — frontier −1, no new leaf.

**Why:** an audit names the obstruction in words on purpose, so the words are the
only shared handle. Before costing any leaf whose docstring names a classical
obstruction ("`ℓ`-independence", "freeness of a Tate module", "Riemann–Roch in
degree 1", "positivity of the Rosati involution"), grep the file's other leaf
docstrings for that phrase.

**How to apply:** one `grep` on the PHRASE, over the file you are already in,
before reading the mathematics. If a sibling leaf claims the same obstruction,
try to prove yours over it — the residue is usually elementary glue.

Related: [[flt-a-leaf-can-contain-a-leaf]], [[flt-two-leaves-may-be-one]],
[[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-inventory-audits-understate-what-exists]].
