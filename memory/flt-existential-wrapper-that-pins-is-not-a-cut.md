---
name: flt-existential-wrapper-that-pins-is-not-a-cut
description: "Restating a leaf as \"∃ A, Q A ∧ P A\" reduces nothing when Q determines A — the uniqueness lemma for Q is usually already in the file, proven by whoever consumed the recut"
metadata: 
  node_type: memory
  type: project
  originSessionId: cfd8924c-c7a3-4996-a342-9e159300ce51
  modified: 2026-08-02T11:46:34.827Z
---

(2026-08-02, `flt-lean-284`, `exists_heckeMatrix_qCoeff_of_x0HeckeCharpolyTable`
in `ModularCurve/X0.lean`.)

A standard good move here is to restate a leaf so it ASKS FOR LESS: replace
`P someComplicatedTerm` by `∃ A, Q A ∧ P A` with `Q` a concrete, low-vocabulary
condition a prover can supply directly. The 2026-07-31 recut of that leaf did
this — `charpoly (toMatrix b b (heckeOp N ℓ)) = c` became `∃ A, (A reproduces
the q-expansion recursion) ∧ A.charpoly = c` — advertising that "nothing about
modular forms survives except `qCoeff`, which is a number".

**It reduced nothing, and the tell needs no mathematics: `Q` PINS `A`.** The
file's own `toMatrix_heckeOp_of_qCoeff`, PROVEN thirty lines above, says
`Q A → A = toMatrix b b (heckeOp N ℓ)`. One witness, so `P A` is the old
statement verbatim and the leaf is logically equivalent to its own consumer
(`charpoly_toMatrix_heckeOp_of_x0HeckeCharpolyTable`, derived FROM it).

**The check: for each conjunct you add, grep for a uniqueness lemma
`Q A → A = <the term you are removing>`.** In a tree that decomposes this
aggressively it is usually already there, because somebody proved it to consume
the recut — its presence is the signal, not a convenience.

The dual is what makes the recut look attractive: the added conjunct is usually
FREE (here `Q (toMatrix b b (heckeOp N ℓ))` is `qCoeff_heckeOp` plus a basis
expansion). Free AND pinning = pure packaging: cannot make the leaf easier
(a prover discharges it) and cannot make it harder (it forces nothing new).

**Do not revert on this finding alone** — both forms are equivalent, so a revert
is churn in the repo's most contended file against a one-day-old deliberate
edit. Write the equivalence into the docstring with both witnessing lemma names
so nobody cuts it a third time, and spend the run elsewhere.

**Where the reducing cut lives is one consumer FURTHER DOWN.** A banked constant
cannot appear in a statement quantifying over the object it depends on (here `A`
depends on the universally quantified basis `b` — that leaf's "WHY THE
EXISTENTIAL AND NOT A NAMED MATRIX" paragraph is correct). It can appear at the
first consumer that CHOOSES that object: `exists_basis_charpoly_heckeOp`, which
builds its basis from `finrank = d`. So a correct "why not a named constant"
block does not close the axis — ask which declaration downstream fixes the
parameter, and cut there.

Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-recut-leaves-stale-docstring]], [[flt-equivalence-prose-is-a-free-leaf]].
