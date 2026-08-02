---
name: flt-predicate-is-a-finiteness-condition
description: "A deformation-condition predicate can silently force the coefficient ring to be pro-finite (and be vacuous on a coarse topology) — audit it as a condition on the RING, not just the object."
metadata: 
  node_type: memory
  type: project
  originSessionId: ed1ff382-eed4-4e19-a731-4494b8265d4d
  modified: 2026-08-02T18:33:22.723Z
---

(2026-08-02, `flt-lean-123`, refuting `exists_flatLocalLift_of_isSmallExtension`.)
`GaloisRep.IsFlatAt`/`IsFlatAtLocal` demands an equivariant bijection onto the geometric
points of a FINITE flat Hopf algebra's generic fibre — so it forces `A ⧸ I` finite at
every open ideal, and it is VACUOUS when `⊤` is the ring's only open ideal (indiscrete
topology; also the usual topology on any non-discrete FIELD).

**Why:** a smoothness leaf `P over R → ∃ lift over S with P` then (i) CONCLUDES that `S`
is pro-finite, which no hypothesis supplied, and (ii) ASSUMES nothing when `R`'s topology
is coarse. Either alone refutes it. Witness needing no arithmetic: `S = R = ℚ_p`,
`ψ = id`, discrete topology on the source.

**How to apply:** for any leaf whose hypothesis/conclusion is a predicate defined by
quantifying over the OPEN IDEALS of a coefficient ring, ask both "what does it force
about the ring" and "when is it vacuous" before auditing the mathematics. The repair is
topology binders (`[CompactSpace S]`, `IsAdic (𝔪 ·)`), and each must be checked
dischargeable at the call site. `Finite.algHom` makes the finiteness half `inferInstance`
— no separability or étaleness needed. See [[flt-leaf-cost-estimates-are-hypotheses]] and
[[audit-searched-production-not-invariant]].
