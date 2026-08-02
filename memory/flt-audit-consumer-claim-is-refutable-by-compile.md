---
name: flt-audit-consumer-claim-is-refutable-by-compile
description: "An \"axis not available because the consumer needs X\" verdict is a claim about a proof in the same file — restate the consumer over the weakened hypothesis and compile it."
metadata: 
  node_type: memory
  type: project
  originSessionId: 24422c2d-a2ea-4f18-ac34-e3753aff7ccc
  modified: 2026-08-01T17:56:21.256Z
---

(2026-08-01, `flt-lean-330`.) An `AXES SEARCHED` paragraph that rules an axis out on the
strength of **what a consumer needs** is not a mathematical claim: it is a claim about a
proof sitting in the same file, and it is settled by a compile rather than by argument.

`exists_geometricCuspEquiv_x1_finiteField` read: *"the BIJECTION-vs-INJECTION axis is NOT
available … the consumer needs only an injection, but an injection of GEOMETRIC points
would not let the degree-one points be separated, since two distinct cusps of the same
degree are distinguished only by the fibre structure a bijection records."* Specific,
plausible, FALSE — the consumer separates two cusps with
`Subtype.ext (congrArg Sigma.fst (Φ.injective (Subtype.ext hab)))`, i.e. by
`Function.Injective Φ` and nothing else.

**The check**: restate the CONSUMER in a scratch with the WEAKENED form of the leaf as an
explicit hypothesis, and elaborate. Compiles ⟹ the axis is available. Do NOT read the
proof and reason about it — a step that "uses the `Equiv`" is usually one an injection
also supplies, which is the confusion these verdicts are built on.

**Then decide and record the decision, not the option.** I declined the axis (surjectivity
falls out of the same Deligne–Rapoport construction as injectivity, so weakening buys
little and gives up the form an exact count would need) and wrote into the docstring what
would reverse it. An axis paragraph recording a checked-and-declined option beats one
recording a wrong reason for never checking.

Same family as [[flt-audit-refuting-check-unrun]] and
[[flt-leaf-cost-estimates-are-hypotheses]]; companion to
[[flt-group-action-is-a-fixed-cost]].
