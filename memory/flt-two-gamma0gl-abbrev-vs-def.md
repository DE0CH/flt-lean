---
name: flt-two-gamma0gl-abbrev-vs-def
description: "Fermat.Gamma0GL is an abbrev and Modularity.Gamma0GL a def; rw across them fails with \"not type-correct under the instances transparency level\"."
metadata: 
  node_type: memory
  type: project
  originSessionId: ed82de9e-32c5-4ba0-8951-bd6048f6e405
  modified: 2026-08-02T09:25:18.882Z
---

`Fermat.Gamma0GL` (`ModularCurve/WeightTwoEigenform.lean`, an **`abbrev`**) and
`GaloisRepresentation.Modularity.Gamma0GL` (`Modularity/HeckeOperator.lean`, a
**`def`**) have the same body and are the same term. `WeightTwoEigenform.lean`'s
RIVAL CARRIERS survey machine-checked this, says the equation is `rfl`, and says
**"do not unify them and do not write a bridge lemma"** — while mentioning "one
(harmless) reducibility asymmetry". That asymmetry is exactly where a proof
mixing the two sides breaks, and the error names neither `Gamma0GL`:

    Tactic `rewrite` failed: Did not find an occurrence of the pattern
      GaloisRepresentation.Modularity.qCoeff ?N 0 ?m
    in the target expression
      GaloisRepresentation.Modularity.qCoeff M 0 1 = a 1
    Note: The target expression is not type-correct under the `instances`
    transparency level …

**Why:** an `abbrev` is reducible and a `def` is not. Lean HAPPILY ELABORATES a
`Modularity`-side function applied to a `Fermat`-side `CuspForm`, but `rw`
inserts its replacement typed at the `Fermat` side, so the rewritten term is not
type-correct at `instances` transparency.

**How to apply:** do NOT chase it with `show` / `simp only` / `erw`. Use a
defeq-checking step, which crosses the gap for free — e.g.
`congrArg (qCoeffL M 1) h` then `map_zero`, in place of
`rw [h, qCoeff_zero_cuspForm]`. The phrase *"not type-correct under the
`instances` transparency level"* means a REDUCIBILITY mismatch, never a wrong
lemma. Same family as [[lean-same-morphism-two-points-blocks-rw]].
