---
name: flt-special-base-assembly-transfers
description: A leaf priced as atomic often has its ASSEMBLY already proven at a special base — transcribe the skeleton, and only the leaves change
metadata:
  type: project
---

`exists_weierstrassModel_of_isLocalRing` (X0.lean) carried a reproduced
"IRREDUCIBILITY VERDICT" for four days — *no machinery attaches `ω`, `c₄`, `c₆`
or `Δ` to an `AbelianSchemeStruct` at this pin* — and two successive amendments
priced it as a differentials theory, then as `f_*𝒪(nO)` plus
cohomology-and-base-change. Both were pricing the WHOLE node.

The node was not atomic. `EllipticScheme.lean`'s
`exists_weierstrassModel_of_ellipticScheme` is the SAME theorem at a base FIELD,
and it is an **assembly over three leaves** — chart, coordinates, ellipticity.
Transcribing its twenty-line glue with `K` replaced by a local ring `R` compiles
unchanged: not one step used that the base was a field. Only the three leaves
change, and two of them (affineness of the complement; `IsUnit Δ`) carry no
Riemann–Roch at all, so the verdict applied to ONE of the three.

**Why:** an irreducibility verdict is written against a NODE, and a node's proof
skeleton is usually cheaper and more portable than any of its inputs. The
skeleton is the part that is formal — associativity, `Spec` of a ring iso,
transport of a range along an isomorphism — and formal steps do not notice which
base you are over. The verdict is about the INPUTS and silently inherits to the
assembly, which is where it is wrong.

**How to apply:** before pricing a leaf whose docstring says a theory is missing,
grep for the same conclusion already proven at a SPECIAL base (a field, `ℚ`,
`ℚ̄`, a DVR, char 0). If it is an assembly, transcribe the assembly first and
find out which of its leaves actually used the specialisation — that is the real
cost, and it is usually a strict subset. Note the DIRECTION: the special case's
*leaves* may be genuinely inapplicable (over a local ring
`PoleOrderFiltration`'s multiplicative `deg` is false, `B` need not be a domain)
while its *skeleton* transfers verbatim. This is the converse of
[[lean-special-parameter-may-already-cover-general]], which is about a special
parameter's STATEMENT already covering the general case.

Related: [[flt-inventory-audits-understate-what-exists]],
[[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-reduce-to-an-open-leaf-not-a-proof]].
