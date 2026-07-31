---
name: flt-absence-audit-greps-consumer-vocabulary
description: A leaf's "stated nowhere, not reachable by wiring" can miss the same theorem under the AUTHOR's names; the missed declaration's own docstring may state the equality verbatim
metadata:
  type: project
---

`exists_relPoint_inj_x0Model_of_abelianSchemeStruct`'s verification pass
(2026-07-30) priced its residue as bullet 4: *"the identification of
`RelPoint f (𝟙 SpecQ)` with the Galois-fixed part of `GeomFibrePt f (𝟙 SpecQ)`
is stated nowhere … it is not reachable by wiring"*, and marked it CONFIRMED
absent "by grep, not inferred". It was wrong in both clauses. `X0.lean` proves
all three halves — `injective_ratToGeom`, `galSMul_ratToGeom`,
`exists_ratPoint_of_galoisInvariant` — and the third's **own docstring** ends
"together with `injective_ratToGeom` and the free half `galSMul_ratToGeom`
this says `A(ℚ) = A(ℚ̄)^{Γ_ℚ}`". The wiring was four lines.

**Why:** the audit grepped the CONSUMER's vocabulary (`RelPoint`,
`GeomFibrePt`, "Galois-fixed"). The author had named the same fact after its
*construction* (`ratToGeom`) and stated the equality only in prose. A grep for
a statement shape cannot see a statement named after its proof.

**How to apply:** before believing any "stated nowhere" verdict, grep for the
CONSTRUCTIONS the statement would be about (here `ratToGeom`), not only for
the statement's own words, and read the neighbours' docstrings — a proven
theorem's prose often names the very equality being hunted. Same task: the
"Riemann–Roch as a scheme" item priced as absent was
`exists_weierstrassCurve_of_abelianSchemeStruct`, available as a **citation**:
it is *transitively* sorried but carries no DIRECT `sorry`, so using it costs
no leaf and opens none — refusing to cite a transitively-sorried theorem only
duplicates work under a second name. Cf. [[flt-absence-audit-names-one-module]],
[[flt-inventory-audits-understate-what-exists]],
[[flt-missing-machinery-may-be-downstream]].
