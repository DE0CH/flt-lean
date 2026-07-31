---
name: flt-forall-over-structure-needs-pinned-field
description: A leaf quantified over ALL inhabitants of a structure is safe iff it constrains a field the structure PINS up to unique isomorphism — check which field, not whether the ∀ "feels" strong
metadata:
  type: project
---

`X1.lean` has one refuted `∀ A : Gamma1Atlas …` leaf
(`nonempty_relPoint_atlas_of_relPoint`, with a full FALSITY AUDIT) and one that
is fine (`exists_gamma1UniversalFamily_of_atlas`, 2026-07-31). The difference
is not the strength of the quantifier — it is **which field of the structure the
conclusion mentions**.

* `Gamma1Atlas.M` is the RIGIDIFIED scheme `𝔐([Γ₁(N)], [Γ(n)])`. Nothing pins
  it: every admissible auxiliary level `n` gives a different `M`, with different
  rational points and different components. A `∀ A` constraining `M` has to hold
  for all of them at once, and the refuted leaf did not (Hasse forbids
  `M(𝔽₁₁)` for `N = 5`).
* `Gamma1Atlas.Y` together with `Gamma1Atlas.classify` IS pinned:
  `Gamma1Atlas.toIsCoarseModuliY1` makes the pair initial among classifying
  cocones, so any two atlases over one base have uniquely isomorphic ones,
  compatibly with `classify`. A statement about `Y`/`classify` has the SAME
  truth value at every atlas — the `∀` is free, not a strengthening.

So the check before writing or auditing a `∀ <structure>` leaf is one question:
**does the structure's own universal property determine the field I am talking
about?** If yes, quantify freely. If no, the leaf must either fix an inhabitant
(`∃ A`) or carry the hypotheses that pin the one it means.

The same lens is worth applying to hypotheses that come from a *pinned* field:
because `(Y, classify)` is initial, the atlas's `quotient` field is strong
enough to prove things that look like they need geometry. That is how the
uniqueness half of `IsFineGamma1Moduli` was closed with no rigidity argument at
all — `𝟙` and the classifying map of the descended family are two solutions of
one `∃!`. See [[flt-uniqueness-clause-needs-subsingleton-base]].
