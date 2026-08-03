## A PROFINITE CITATION CAN BE A FINITE CONSTRUCTION THAT GOES *UP* FIRST
(2026-08-02, `flt-lean-53`, building the local input for
`WeierstrassCurve.nonempty_fullTranslationDatum_wild`.)  The classical statement
was: `G = Gal(ℚ̄_q/ℚ_q)`, `I` inertia, `N ⊴ G` open in `I`; find a closed `H` with
`H ∩ I = N` and `H·I = G`.  Every account of it — including this tree's own
docstrings, for five days — cites **projectivity of `Ẑ` in profinite groups**.
`Ẑ` is not in the pin, and its projectivity needs the structure theory of
procyclic profinite groups, so the node reads as a theory build.
**It is two short finite-group lemmas with no topology and no finiteness in
them.**  What blocks the naive finite-level attempt is an ORDER obstruction —
inertia genuinely need not be complemented in `Gal(M/K)` (`Z/4 ⊇ Z/2` is
realisable as Galois ⊇ inertia over `ℚ_p`) — and the escape is not to reach for
the infinite object but to **ENLARGE in the direction the problem is free in**:
compose with the unramified extension of degree `d = orderOf φ`, and in
`Gal(M·K_d/K) = Gal(M/K) ×_{Gal(M₀/K)} Gal(K_d/K)` the element `(φ, Frob_d)` has
order exactly `d`, which is all a complement needs
(`Fermat.isComplement'_ker_zpowers`, `Fermat.isComplement'_fiberProduct` in
`Fermat/FLT/Mathlib/GroupTheory/CyclicComplement.lean`).
**The generalisable check, and it is one question: when a splitting or lifting is
blocked at finite level by an obstruction that a bigger level would kill, ask
what the profinite hypothesis is FOR.**  Here `G/I ≅ Ẑ` is used for exactly one
thing — that unramified layers of every degree exist — so it is consumed by
*choosing a level*, not by any structure theorem.  A profinite hypothesis that
enters only as "there are arbitrarily large finite quotients" is a supply of
enlargements, and the argument that uses it can be written one level at a time.
Two tells that you have found the real content rather than a special case:
**every finiteness and topological hypothesis disappears from the statement**
(both lemmas above are about arbitrary groups), and **the counterexample that
motivated the profinite citation survives** — `Z/2` is still not complemented in
`Z/4`, and the lemma does not claim it is; it claims something about a different,
larger group.
Rider on wiring a mathlib-facing module into the closure: **`Fermat.lean` is the
cheapest place, because nothing is downstream of it.** Adding the import there
rebuilds the root alone (~10 s), where adding it to an interior module rebuilds
that module's whole cone.  Say in a comment beside the import that it is there
for compilation and where it should move once a real consumer exists — a module
with no consumer is legitimate while its intended consumer is an open leaf (an
open leaf's body creates no dependency edge), but nothing else records why.
