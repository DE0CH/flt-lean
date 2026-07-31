---
name: flt-declaration-order-leaves
description: A leaf whose docstring blames declaration order is usually cheap — run flt-hoistcheck.py before believing any cost estimate, and hoist the machinery, not the consumers
metadata:
  type: project
---

Some leaves in `X0.lean` are open for **no mathematical reason**: their proof is
already written elsewhere in the same file, thousands of lines *below* them. A
leaf needs no producer; a theorem does. `exists_jSection_algClosModel` sat like
that for four days after an audit had correctly identified it.

**Why:** the cost of the repair is a block relocation, and nobody measures it —
the docstrings price these moves by how big they look. Measured on 2026-07-31,
both estimates in `exists_jSection_algClosModel`'s audit were wrong: the
2966-line in-file hoist used **zero** of the 178 declarations it jumped over,
while the "just split it into a module" alternative would have required a
THREE-way split of `X0.lean`, because the block consumes `Gamma0Datum` /
`RelPoint` / `AbelianSchemeStruct` from the same file's first fifteen thousand
lines.

**How to apply:** run `./flt-hoistcheck.py <file> --block A B --to L` (added in
the same commit; both directions, two seconds). Zero hits and balanced
`namespace`/`section` means the move is dependency-free — but eyeball the
anonymous `instance :` declarations it prints, which no name scan can see.
Then prefer moving the MACHINERY over moving the CONSUMERS (consumer clusters
fan out; machinery usually has one straggler), and strengthen the CONCLUSION of
the producers rather than adding a field to a structure, so no consumer of a
field is disturbed. See [[flt-cut-leftovers-close-sibling-leaves]] for the
sibling habit of reading what a proof already has and merely discards — that is
the same failure that kept this leaf open.
