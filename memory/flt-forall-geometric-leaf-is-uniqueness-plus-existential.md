---
name: flt-forall-geometric-leaf-is-uniqueness-plus-existential
description: "A leaf stated over EVERY object with a geometric property (every smooth compactification, every model) decomposes as UNIQUENESS of that object plus an existential citation — the count stays 1 to 1 and all the geometry leaves the leaf"
metadata: 
  node_type: memory
  type: project
  originSessionId: 5c927d46-112d-479d-bea8-bf1f3dd81b99
  modified: 2026-08-02T19:41:20.337Z
---

(2026-08-02, `flt-lean-49`, `exists_isX0Compactification_sexticThirtySeven` in
`FreyCurve/MazurTorsion.lean`.)  A citation leaf in this tree is routinely stated
over an ARBITRARY object carrying a geometric property — *"given ANY smooth
compactification `X` of the affine sextic, `X` is `X_0(37)`"* — because that is the
shape the consumer wants (it has manufactured its own `X` and must not be forced to
name one).  The `∀` then drags every scheme-theoretic obligation into the leaf,
where the modular content is, and a successor cannot tell them apart.

**How to apply.**  Split it as

1. **uniqueness** of the arbitrary object — general algebraic geometry, provable,
   reusable, and it belongs upstream;
2. the leaf restated **existentially over ONE such object**, which is what a
   citation actually supplies;
3. a **transport** of the conclusion along the resulting isomorphism.

Here that was `exists_inverse_of_isSmoothCompactification` (two smooth
compactifications of one integral scheme over a field are isomorphic over it,
compatibly with the immersions), `exists_openImmersion_x0ThirtySeven` (the affine
sextic is an open subscheme of *some* `X_0(37)`), and `IsX0Compactification.ofInverse`
— which was **already PROVEN** in `X0.lean`, written for the `𝔽_ℓ` uniqueness
argument, and is the sort of thing to grep for before re-deriving it.

**Why:** the direct-sorry count does not move, `1 → 1`, so this must be reported as
a RECUT (see [[flt-recut-leaves-stale-docstring]]).  What changes is that the
residue asks for ONE MORPHISM and mentions no properness, no smoothness, no
density, no finiteness of a complement and no `∀`.  Judge it by what is LEFT in the
leaf.

**Two riders, both measured here.**  Prefer the `∃` form and say so — the `∀` form
is equivalent (via the same uniqueness theorem plus initiality of the coarse moduli
space) and is strictly more to prove, so it is the wrong thing to hand a successor.
And the four bookkeeping clauses of the packaged property (`isDominant`,
`finite_compl`, `isProper`, `smooth`) are all derivable from the existential's own
output, so ask the leaf for the bare open immersion and prove the package as its own
lemma; otherwise every future prover re-derives them.

Related: [[flt-cut-so-each-half-is-a-consequence]],
[[flt-every-vs-some-representing-object]], [[flt-price-the-consumers-input]].
