---
name: flt-route-residue-is-the-cheap-route
description: "A leaf docstring's \"what that route does NOT deliver is X\" paragraph is an ORDERING instruction — prove X first and most of the route evaporates"
metadata: 
  node_type: memory
  type: project
  originSessionId: c721205d-ec56-41c7-9bdc-015e4570494b
  modified: 2026-08-01T07:01:38.348Z
---

(2026-07-31, `flt-lean-135`, closing `A₀-3b-i-a`
`exists_fundamentalCharacter_of_relIndex_localInertiaGroup` in
`FreyCurve/MazurTorsion.lean`.)

A mature leaf carries a worked route and then a closing paragraph: *"what that
route does NOT deliver is `<clause>`; the extra ingredient is exactly
`<structural fact>`, worth cutting out as its own lemma."*

**Read that as an ordering instruction, not an afterthought.** Here the route
was "build one finite quotient `(χ, θ_{e(N−1)}, I_N/J)`, take a cyclic
generator, define `ψ σ := χ(g₀)^{k/e}`" and the residue was torsion-freeness of
`T = I_N/P_N`. Proving the structural facts FIRST made three quarters of the
route unnecessary: the level-`e(N−1)` tame character was never built and
`exists_localInertia_tameCharacter_orbit` was never used.

**Why, generally:** a route through ONE finite quotient cannot see a statement
about the infinite group, so the residue it leaves is always the hard half;
whereas the structural facts, once proven, make the finite quotient nearly free.

**And when a group is DEFINED as an intersection of kernels, every property of
the common target transfers for free.** `P_v = ⋂_z ker θ_z` with `θ_z` valued in
`rootsOfUnity` gives *T is abelian* in three lines. Torsion-freeness is forty:
take an `n`-th root `z'` of the tame generator `z` in the ALGEBRAIC CLOSURE — it
is again a tame generator — and `θ_z(t) = θ_{z'}(t)^n = θ_{z'}(t^n) = 1`.

Corollary on shape: state the result over an ABSTRACT character (any
`CommGroup`-valued `chi : I_v →* A` killing `P_v` and surjective) at an arbitrary
number field; the concrete instantiation is then fifty lines. See
[[flt-leaf-cost-estimates-are-hypotheses]].
