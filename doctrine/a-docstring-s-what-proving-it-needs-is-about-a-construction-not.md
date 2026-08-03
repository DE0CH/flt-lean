## A DOCSTRING'S "WHAT PROVING IT NEEDS" IS ABOUT A CONSTRUCTION, NOT ABOUT THE STATEMENT

(2026-07-31, `flt-lean-214`.) `exists_involutionSignSplitting` in `X0.lean` had stood
open since 2026-07-28 behind this estimate, written by its author and never re-derived:

> **What proving it needs**: abelian varieties over a field — absent from mathlib
> entirely — together with the quotient of an abelian scheme by an abelian subscheme
> as a faithfully flat map, and fppf descent to see that such a quotient is an
> epimorphism of schemes.

Every clause is a true statement about `P^± := A / B^∓`, the CLASSICAL construction.
None of it was needed. `IsInvolutionSignSplitting` never asks for a quotient: it asks
for a surjective flat epimorphism `p b` on which `ι` acts by `±1`, with finite joint
kernel and a descent for commuting endomorphisms. **`Im(1 ± ι)` is one**, it is
isogenous to the quotient, and nothing in the structure distinguishes them. The leaf
closed over machinery that was already in the file — the image theorem, `flat_`/
`epi_of_surjective_of_isAdditiveOn`, `finite_torsion_geomPt_of_abelianScheme`,
rigidity, and the `EffectiveEpi` that `epi_of_surjective_of_isAdditiveOn` discards.

This is the SECOND time the same substitution has paid in this one file — the first
is recorded on `exists_abelianImage_of_isAdditiveOn` as "the CHEAP replacement for
Poincaré reducibility that the image-not-kernel cut buys". So it is a pattern, not a
coincidence: **over a field, an IMAGE is cheap (scheme-theoretic image + Cartier gives
smoothness) and a QUOTIENT is expensive (fppf descent, the subscheme's own geometry),
and the two are isogenous.** Whenever a leaf's stated obstruction is a quotient, ask
first whether an image satisfies the conclusion.

The general rule, and it applies to every leaf in this development:

- **An absence table is evidence about the ROUTE its author searched.** It is not a
  theorem about the statement, and it does not expire loudly — it just sits there
  looking authoritative while the file grows the machinery that makes it false.
- Before accepting "this needs a theory we do not have", **read the CONCLUSION alone,
  field by field, and ask what each field actually demands.** Here the answer was
  visible in the structure's own docstring: it already said `ker_finite` "is the
  `2`-torsion argument", which is true of the image construction and says nothing
  about quotients.
- The cost of the check is one careful read. The cost of not making it was three days
  of a node the fleet believed was blocked on a missing subtree.

Corollary for anyone WRITING a leaf: say "the construction I have in mind needs X",
not "proving it needs X". The two read identically to the next agent and only one of
them is true.

