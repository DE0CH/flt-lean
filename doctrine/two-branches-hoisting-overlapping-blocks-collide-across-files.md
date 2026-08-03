## TWO BRANCHES HOISTING OVERLAPPING BLOCKS COLLIDE ACROSS FILES, NOT WITHIN ONE
(2026-07-31.) `flt-lean-77` hoisted 19 `q`-expansion declarations out of `Interface.lean` into a
new `Modularity/HeckeQExpansion.lean`; `flt-lean-147` hoisted 196 into a new
`Modularity/HeckeAtkinLehner.lean`, and the 19 are a strict SUBSET of the 196. Both branches
delete their own copies from `Interface.lean`, so neither introduces a duplicate on its own — the
duplicate appears only when both are ancestors of the same `main`, in two files git never saw in
conflict.
This is the cross-file half of the class-7 interface split, with an extra twist: the two branches
were dispatched at DIFFERENT leaves (an `X0.lean` Hecke charpoly leaf and the Atkin–Lehner
multiplicity-one leaves), so no ownership check on declaration names could have flagged it. What
would have flagged it: **before hoisting, `git ls-tree` every branch for NEW FILES in the target
directory**, not just for edits to the file you are cutting from.
    for b in $(git branch --list --format='%(refname:short)'); do
      git ls-tree --name-only $b Fermat/FLT/<dir>/ ; done | sort -u
Resolution when it happens: keep both modules and make the larger one `public import` the smaller,
deleting its copies of the overlap. That preserves both agents' work and keeps the small module's
cone small for the consumer that only needs it — importing the 8000-line one into `X0.lean` to get
19 declarations is exactly the cone growth that turns unedited modules red.
