---
name: flt-overdetermined-degree-conjunct
description: When a leaf gives a generator AND an exact degree, the degree is over-determined — ask for ≤ and derive =, which deletes a whole half of the cited theorem
metadata:
  type: project
---

A leaf whose conclusion pins an object (a primitive `n`-th root of unity in
`κ(x)`, a generator, an embedding) **and** asserts an exact numerical invariant
(`residueQDegree = φ(n)`) is asking for the same thing twice. The generator
already gives the lower bound. Weaken the numeric conjunct to `≤` plus a
non-degeneracy clause and prove `=` in a separate, cheap lemma.

Done 2026-07-31 on `exists_cuspAboveDivisor_root` (`X0.lean`): the re-cut leaf
asks `residueQDegree ≤ φ(g)` and `≠ 0`, and
`residueQDegree_eq_totient_of_le` recovers the equality.

**Why it is worth doing:** the deleted half is not bookkeeping. Here `≥ φ(g)`
was exactly Deligne–Rapoport §V.5's *single-Galois-orbit* statement — that the
`φ(g)` geometric cusps above a fixed number of sides are permuted transitively
by `Γ_ℚ`. After the re-cut a prover only has to exhibit a cusp DEFINED OVER
`ℚ(ζ_g)` and never has to prove it is defined over nothing smaller.

**How to apply:**
- the non-degeneracy clause is mandatory, not decoration: `Module.finrank` is
  `0` on an infinite-dimensional extension, so `≤ φ(n)` alone is satisfied
  vacuously and the conclusion would come out `0 = φ(n)`. `≠ 0` is what
  supplies `FiniteDimensional`.
- prove the lower bound through `minpoly.natDegree_le` +
  `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible` +
  `Polynomial.natDegree_cyclotomic`. Do **not** route through
  `IntermediateField.adjoin` — see [[flt-rat-algebra-diamond-use-minpoly]].

See [[flt-field-of-moduli-not-definition]] for the trap in the other conjunct of
the same re-cut.
