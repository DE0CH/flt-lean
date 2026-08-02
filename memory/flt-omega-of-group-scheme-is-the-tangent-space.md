---
name: flt-omega-of-group-scheme-is-the-tangent-space
description: "A leaf priced at \"Ω of a group scheme + additivity on invariant differentials\" is the tangent-space theorem, which this tree already proves under a name sharing no keyword"
metadata: 
  node_type: memory
  type: project
  originSessionId: 364d16d0-8a36-4e4b-af0c-b33f7a0a2b39
  modified: 2026-08-01T19:23:32.666Z
---

`kaehler_stalkMap_mulByNat_prime_eq_zero` (`Modularity/TateModule.lean`) was
priced by its own docstring at the classical route — `Ω_{A/k}` free on invariant
differentials, `f ↦ f^*` additive on them, hence `[p]^* = p = 0`. Its crux was
already PROVEN in `Modularity/AbelianSchemeIsogeny.lean` as
`nonempty_module_infKernel_of_squareZero`: *`ker (A(R) ⟶ A(R₀))` is a `k`-vector
space for a square-zero thickening*. Same theorem, no shared identifier, and the
module was already `public import`ed. Closed 2026-08-01 in ~200 lines,
axiom-clean.

**Why:** `Ω` of a group scheme and its tangent space at the identity are one
datum; a development formalises whichever its first consumer needed, so a grep
in the leaf's vocabulary returns nothing.

**How to apply:** when a route asks for differentials of a GROUP object, also
grep `infKernel`, `squareZero`, `tangent`, `Lie`, `Der`, `dual number` — and
conversely. Instantiate at the UNIVERSAL square-zero extension
`R ⊕ Ω[R⁄k] ↠ R` with sections `r ↦ (r, d r)` and `r ↦ (r, 0)`: their
difference lies in the kernel, `p` kills it, and `X.fromSpecStalk` being a mono
([[flt-fromspecstalk-is-a-mono]]) turns the resulting equality of morphisms back
into an equality of ring maps. Related: [[flt-inventory-audits-understate-what-exists]],
[[flt-leaf-cost-estimates-are-hypotheses]].
