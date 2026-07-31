---
name: flt-multiplicity-lives-in-the-factor
description: "\"the index set must be finer than X\" is usually a claim about objects the structure never constrains — check the fields before believing it"
metadata:
  type: project
---

`X0.lean` and `X1.lean` each said, in a docstring repeated across two files, that
the index set of a Hecke-isotypic decomposition **cannot** be the set of
eigen-systems, because level `N = p³M` needs `σ₀(N/M)` copies of `A_g` while
`U_p` supplies only `2` systems — so the copies must be carried by `σ₀(N/M)`
distinct degeneracy-twisted surjections. `X0.lean`'s twin used exactly that
argument to reject an otherwise-obvious cut, on the ground that a prover taking
it would be left writing `idx := sorry`.

**It is a claim about a decomposition into copies of `A_g`, and the structure
never asks for one.** `IsHeckeIsotypicDecomposition{,Gamma1}.isotypic` says only
that `minpoly ℤ (coeff i n)` annihilates `S i n` at arities coprime to `N`, and
`A i := A_g^{σ₀(N/M)}` — the whole `g`-old quotient — satisfies that as
comfortably as one copy. So `idx` **is** the set of eigen-systems and the
multiplicity lives inside `A i`. Taking the MAXIMAL isotypic quotient at each
system discharges the multiplicities without indexing them, and is also the only
way `equivariant` can hold at the junk arities: an individual degeneracy-twisted
`J_1(N) ↠ A_g` does not commute with `U_p`, so it admits no `S i p` at all,
while a maximal kernel is stable under every endomorphism.

**Why:** an audit that costs a cut is usually reasoning about the intended
mathematical object (`A_f`, the newform's own abelian variety) rather than about
the Lean fields, which are strictly weaker. The gap between the two is where the
cheap cut hides.

**How to apply:** when a docstring rejects a decomposition because "the index set
would have to be finer", read the structure's fields and ask what is actually
constrained about the indexed objects. If the fields pin only a *property* of
`A i` and not its isomorphism class, the extra multiplicity can be absorbed into
`A i`. Corollary in the other direction: the joint-kernel statement is then TRUE
only for a *chosen* family, and FALSE for an arbitrary one — the existential
quantifier over the family is load-bearing, and a "for every family" restatement
is a falsity trap. See [[flt-cut-leftovers-close-sibling-leaves]] and
[[flt-leaf-names-wrong-half-as-hard]].
