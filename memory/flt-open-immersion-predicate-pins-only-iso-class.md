---
name: flt-open-immersion-predicate-pins-only-iso-class
description: "A predicate \"∃ open immersion Spec B ⟶ A with this range\" is invariant under Aut(B), so it pins B only up to isomorphism — over a non-reduced base that is too coarse"
metadata: 
  node_type: memory
  type: project
  originSessionId: fd2a942f-f07a-46c8-ad31-6f4fba906c1e
  modified: 2026-08-01T21:29:25.571Z
---

`Fermat/FLT/ModularCurve/X0.lean`'s `IsWeierstrassModel ab W` says
`∃ ι : Spec R[W] ⟶ A, IsOpenImmersion ι ∧ ι ≫ f = str ∧ Set.range ι.base = (range of zero section)ᶜ`.
Replacing `ι` by `ι ∘ Spec e` for any `R`-algebra automorphism `e` of `R[W]`
preserves all three clauses, so the predicate depends only on the `R`-algebra
ISOMORPHISM CLASS of `R[W]`. Strengthening the range clause scheme-theoretically
does not help: `ι` and `ι ∘ Spec e` have the same image.

**Why:** over a reduced base every automorphism of `R[W]` is a `VariableChange`
(`WeierstrassPoleOrder.linearShape_of_surjective_of_isReduced`, PROVEN), so the
coordinates are pinned; over `R = ℚ[ε]/(ε²)` the automorphism `id + ε∂`
(`x ↦ x + 2εy`, `y ↦ y + ε(3x²+a₄)`, `∂` the invariant derivation) is not
linear, and it is the translation by an infinitesimal point — it moves the zero
SECTION while fixing the topological point under it.

**How to apply:** this makes `exists_linearShape_of_surjective_of_isWeierstrassModel`
FALSE, and with it `exists_linearShape_of_isWeierstrassModel`,
`exists_linearAlgHom_of_isWeierstrassModel`,
`exists_variableChange_of_isWeierstrassModel` and `weierstrassModel_j_unique`
over non-reduced bases. The transport lemma
`isWeierstrassModel_of_algEquiv` (machine-checked 2026-08-01, quoted in full in
the FALSITY AUDIT on `IsWeierstrassModel`) is the engine; it also shows the
`ℚ[ε]/(ε²)` pair already recorded in that file IS a pair of models of one `ab`,
contradicting the audit sentence that said it "has no `A` at all". The repair is
to strengthen the DEFINITION to pin the compactification (pole orders along the
zero section, via `Fermat.sectionIdeal`) — a cut-level task with ~10 consumers,
queued rather than performed. See [[flt-audit-scoped-to-declaration-it-read]] and
[[leaf-falsity-can-live-in-a-definition]].
