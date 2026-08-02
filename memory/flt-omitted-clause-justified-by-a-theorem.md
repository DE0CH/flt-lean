---
name: flt-omitted-clause-justified-by-a-theorem
description: "When a structure justifies a weaker clause by citing a theorem, check that theorem's hypotheses against the structure's own fields — the citation is often circular"
metadata: 
  node_type: memory
  type: project
  originSessionId: 271e5ad2-3a2f-4ad6-98d8-72362e879101
  modified: 2026-08-01T23:43:45.789Z
---

A bundled structure here often carries a paragraph *"the literature asks for
`X`; we ask for the weaker `Y`, and `Y ⟹ X` by <named theorem>, so nothing is
lost and `Y` is cheaper to state."* That paragraph is a proof sketch with
hypotheses, and it is the least re-read part of a structure's docstring because
it reads as a design note.

`CyclicSubgroupOfOrder` (`ModularCurve/X0.lean`) pinned the GEOMETRIC-FIBRE
cardinality where Katz–Mazur pin the RANK, justified by Cartier's theorem
("finite flat ⟹ étale ⟹ rank = #points"). Cartier needs the RANK invertible on
the base — the very thing not being pinned. Circular. Counterexample: over
`𝔽̄_p`, `p ∤ N`, `E` ordinary, `C = (ℤ/N) ⊕ μ_{p^k}` satisfies every clause for
every `k` (`μ_{p^k}` contributes no geometric points; over a field everything is
flat).

**The check:** write down the cited theorem's hypotheses and verify each against
the structure's OWN fields — not against the hypotheses its consumers carry. The
tell is that the theorem's hypothesis mentions the quantity you are declining to
assert.

**Corollary on sibling structures.** `Gamma0Datum` carries two level structures:
`FullLevelStructure` (clause `geom_basis`, plus `nsmul_P`/`nsmul_Q` added after a
refutation) and `CyclicSubgroupOfOrder` (clause `geom_cyclic`, no torsion clause).
Same file, 1300 lines apart, same gap, one repaired and one not. Sharper than
[[flt-faithfulness-repair-not-inherited-by-twin]], which is about `ℚ`/`F` twins in
two files: sibling structures share no identifier and only the SHAPE of their
clauses matches, so grep a repaired structure's file for other `geom_`-prefixed
fields.

**Costing the repair: count STRUCTURE LITERALS, not references.**
`grep -rn "geom_cyclic :=\|neg_liesIn :="` finds the four construction sites; the
~40 mentions of the type name price it as a multi-file interface change and are
mostly `∀`-over-the-structure (which a new field only weakens) or docstrings.
But check the direction: a `∀`-over-the-structure in HYPOTHESIS position makes
its theorem STRONGER when the class shrinks.
