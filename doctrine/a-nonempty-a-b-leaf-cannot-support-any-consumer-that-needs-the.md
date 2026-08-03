## A `Nonempty (A ≃+ B)` LEAF CANNOT SUPPORT ANY CONSUMER THAT NEEDS THE MAP

(2026-07-31, `exists_weierstrassQ_autStable_of_weierstrassAlgClos` in `X0.lean`.) A
leaf whose conclusion is a bare `Nonempty` of an isomorphism type says only that the
two objects are abstractly isomorphic. **Any two witnesses are interchangeable, so a
consumer may use only what is true of EVERY witness** — and for a group isomorphism
that is almost nothing, because composing a witness with any automorphism of the
target yields another witness.

Concretely: `exists_addEquiv_of_weierstrassModel_field` concludes
`Nonempty (RelPoint f (𝟙 (Spec k)) ≃+ (W⁄k).Point)`. At `k = ℚ̄` it looks like exactly
the "points dictionary over `ℚ̄`" that three docstrings in `X0.lean` say is the missing
half — it is not, and no amount of work makes it one. `E(ℚ̄)` is abstractly
`(ℚ/ℤ)² ⊕ ⊕ℚ`, whose automorphisms surject onto `GL₂(ℤ/N)` on `N`-torsion, so the image
of the level structure can be ANY order-`N` cyclic subgroup. Its Galois-stability is
therefore not a property of the datum at all.

**Test before consuming, and it costs one line: is the conclusion invariant under
post-composing the witness with an automorphism of the target?** If not, the leaf is
insufficient however close its statement reads, and the fix is to strengthen the
PRODUCER (add the equivariance/naturality clause), never to try harder downstream.

**And the same test kills the natural CUT**, which is why this belongs beside the
rival-cuts section. Hypothesising the dictionary — `(e : A ≃+ B)` plus "e carries this
sub-object to that one" — and leaving the geometry as the residual leaf produces a
residual that is **FALSE AS STATED**, refuted by the same automorphism. An abstract
`e` in a hypothesis is not a dictionary, it is a relabelling: it has thrown away
exactly the information the residual needs. A cut of a descent statement must either
construct the dictionary inside, or hypothesise it *together with* its semilinearity.

