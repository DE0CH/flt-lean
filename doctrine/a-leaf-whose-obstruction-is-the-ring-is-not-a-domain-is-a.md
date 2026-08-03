## A LEAF WHOSE OBSTRUCTION IS "THE RING IS NOT A DOMAIN" IS A STATEMENT ABOUT THE ACTION

(2026-07-31, `isDomain_of_gamma0AtlasOver_zmod`.) Over `ℚ` the rigidified moduli scheme
`𝔐([Γ₀(N)], [Γ(n)])` is integral, so the coarse ring `B = A^G ⊆ A` is a domain because `A`
is. Over `𝔽_p` that is FALSE — at `n = 3`, `p = 7` both primitive cube roots of unity are
`𝔽₇`-rational, Frobenius fixes them, and `A` is a product of two rings — and the file had
recorded, correctly, that what saves the conclusion is that `det : GL₂(ℤ/n) → (ℤ/n)ˣ` is
surjective and `e_n(gP, gQ) = e_n(P, Q)^{det g}`, so `G` permutes the components
TRANSITIVELY even where Frobenius does not.

That sentence is the whole cut, and the algebra under it is thirty lines:

    S reduced + G transitive on `minimalPrimes S`  ⟹  S^G is a domain

*Proof.* `x ≠ 0` in a reduced ring avoids SOME minimal prime (it is not nilpotent, so it
avoids some prime, and `Ideal.exists_minimalPrimes_le` drops to a minimal one below it).
The image of `S^G` is `G`-fixed (`SMulCommClass G R S`: `g • (r • 1) = r • (g • 1)`), so
for such an element "lies in `q`" is a `G`-INVARIANT condition on `q`. Hence if `x, y` are
both nonzero, transitivity carries a minimal prime missing `x` onto one missing `y`, and
that prime misses both while containing `xy = 0`. ∎

Two things worth copying beyond the instance.

**Use MINIMAL PRIMES, not connected components.** The geometric sentence is about
components, and the temptation is to formalise idempotents or a product decomposition.
Minimal primes are what reducedness controls (`⋂ minimalPrimes = nilradical = 0`), they
are all the argument consumes, and they need no topology. For a smooth scheme the two
notions agree anyway, so nothing is lost.

**A leaf whose stated obstruction is a property the object does NOT have is usually
asking you to move the hypothesis onto a different object.** Here "`A` is not a domain" is
true and final; the repair is not to weaken the conclusion but to notice that the
conclusion is about `A^G` and that transitivity of the ACTION is a hypothesis nobody had
tried to state. The leaf count is unchanged, `1 → 1`, and what the residue lost is every
mention of the coarse ring, the invariants, an atlas and a scheme.

**When you cannot merge two overlapping leaves, say WHY in the docstring.** The new leaf
asserts `IsReduced P.A`, which its sibling
`exists_gamma0GITPresentationOver_normalModuli_zmod` also asserts, and a reviewer will ask
why they are not one leaf. They cannot be: the sibling is PROVEN by threading a
`motive : (A : Type) → [CommRing A] → (Spec A ⟶ S) → Prop` through two structure
transports, and a motive of that type cannot mention the deck group `G`. Adding the
transitivity conjunct there would destroy a proof rather than extend one. That is a
mechanical reason, it is invisible from the statements, and it is exactly what the next
agent would otherwise spend an afternoon rediscovering.

