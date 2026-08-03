## A LEAF'S OWN "NOT PROVABLE FROM WHAT IS HERE" AUDIT CANNOT SEE DOWNSTREAM
(2026-07-31, `natCast_ne_zero_of_geomBasis` in `X0.lean`.) The leaf shipped with a
careful, correct audit naming two routes and pricing each: a rank (`deg [n] = n²`,
Mumford §6) or invariant differentials of an abelian scheme. Both were genuinely
absent, both were correctly priced as new subtrees, and the dispatch that followed
told its agent not to re-measure them. **Neither was needed.** The arithmetic
already existed, PROVEN the previous day, in `X1.lean` — a file that IMPORTS
`X0.lean` and therefore cannot be seen from inside it. The leaf closed in five
lines over a bridge (`exists_weierstrassModel_geomFibreAddEquiv_of_geomPoint`) that
`X0.lean` itself already proved.
This is the `Missing machinery may be DOWNSTREAM` memory, but with a sharper edge:
there, an agent's *inventory* missed a downstream proof. Here, the leaf's own
authored audit did — and an audit reads as settled fact in a way an inventory does
not, so it propagates into dispatch prompts as "this was measured, do not
re-measure". **An audit's ABSENCE claims are scoped to the import cone it was
written in. Before believing one, grep the whole tree for the mathematical content,
not the file's dependencies.** Hoisting the proof out to a small shared module
(here `Fermat/FLT/EllipticCurve/GeomTorsionBasis.lean`) costs nothing: the
downstream file inherits its own declarations back through the upstream file's
`public import`, under unchanged names, so no call site anywhere changes.
**Corollary, same leaf: a docstring conjecture backed by a BOUNDED search is a
hypothesis, and the bound is usually where the counterexample is.** `X1.lean`
recorded "the bare basis property probably implies `n • y = 0`" on the strength of
a sweep over `n ∈ {3, 4, 5}`. It is false, and the smallest counterexample is
`n = 6`: `G = ℤ/20`, `y = z = 1`, where `∃!` holds exactly on the `n`-torsion
`{0, 10}` while `6 • y = 6 ≠ 0`. Re-run such a search past its recorded bound
before relying on the conjecture — it took seconds and it decided the signature.
