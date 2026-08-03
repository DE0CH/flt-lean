## A BRAUER OBSTRUCTION WITH A RATIONAL POINT IS ONE UNIQUENESS LEMMA, NOT AN `H²`
(2026-07-31, `geomPic_descent_divisor` in `HyperellipticJacobian.lean`.)  The leaf's own
plan described the argument the way the literature does: `σ ↦ g_σ` is a `1`-cocycle for
`F̄^×/ℚ̄^×`, so the obstruction to correcting a representative sits between
`H¹(Γ, F̄^×) = 0` and `H²(Γ, ℚ̄^×) = Br(ℚ)`, and the rational point splits the Brauer class.
Read as a specification that says: build a `2`-cocycle with values in `ℚ̄ˣ`, build the
evaluation map at the point, prove it splits.
None of that was written.  In Lean the whole of it is **one lemma with no cohomology in
it**: two nonzero functions with the same divisor *and the same value `1` at the rational
point* are EQUAL.  (Their ratio has trivial divisor, hence is a constant; the shared value
pins that constant to `1`.)  It is used exactly twice — for the cocycle identity, and for
"a `ρ` fixing the finite level has `A ρ = 1`" — and those are the only two places the
obstruction could have appeared.
**The generalisable move: a cohomological obstruction that a normalisation kills should be
formalised as the UNIQUENESS of the normalised representative, never as the obstruction
class.**  The class is an object you must construct, name, and then prove trivial; the
uniqueness lemma is a fact about objects you already have.  Same input, a tenth of the code,
and — the part that matters here — it needs no `H²`, no profinite topology, and no group
cohomology library, in a development that deliberately keeps `QbarGal` a bare type.
The tell that the collapse is available: the normalisation is a **VALUE**, and the value is
`Γ`-equivariant.  Here `A σ := g_σ / g_σ(∞̄₊)` needs `g_σ` to be a unit at `∞̄₊`, which is
exactly what the representative's normalisation `δ(∞̄₊) = 0` delivers; and "value `1` at
`∞̄₊`" is `Γ`-stable because `∞̄₊` is a rational point (`ord_infPlus_fieldAct` plus
`fieldAct_algebraMap`).  Rational point ⇒ equivariant value ⇒ uniqueness ⇒ no `H²`.
**Second lesson, from the same leaf: a sub-leaf named in a PLAN is not a consumer edge, and
the plan outlives the proof.**  `geomPic_descent`'s docstring listed four sub-leaves and
assigned 3b (`geomPic_exists_bcDiv_of_divAct_fixed`) to its step 7.  When step 7 was
actually written it went through `placeAct_transitive` instead — fifteen inline lines — so
3b was orphaned at that moment.  Nothing noticed: the plan still said "the leaves are 3a,
3b, 3c, 3d", the frontier scan still saw an open leaf, and a task naming it was queued and
would have burned a whole worker.
So **when you close a decomposed node, re-derive which sub-leaves the assembly actually
consumed and correct the plan on each of them.**  `grep` the comment-stripped module for
each named sub-leaf; one that appears only inside `/- -/` is dead, whatever the plan says.
The plan is a hypothesis about the proof, written before the proof existed.
