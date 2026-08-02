---
name: flt-dead-hypothesis-blocks-a-route
description: "A dead binder on a PROVEN theorem can make it inapplicable at the one value a consumer needs; follow the binder by name through the wrapper chain, not with the linter."
metadata: 
  node_type: memory
  type: project
  originSessionId: ee11f2ce-9920-435e-b5d8-fb18e0f75d21
  modified: 2026-08-02T04:07:33.059Z
---

CLAUDE.md records that an "unused" hypothesis is free strength and costs a prover
nothing. That is true when the hypothesis is HARMLESS. The third case is expensive:
**a dead hypothesis can make a proven theorem unusable at exactly the value its next
consumer needs.**

2026-08-02, `flt-lean-267`, `EllipticCurve/WeilPairing.lean`:
`translationChar_setup_value` proves `B = c^e·A` (`e ∈ {1, p−1}`) where `A`, `B` are
character-for-character the products in the open leaf `weilValue_self_config_eq_one` —
i.e. `z = c^e`, so the leaf is just `c = 1`. It carried `(hc1 : c ≠ 1)`, locking out the
only value alternation cares about. `hc1` was DEAD: one occurrence, the binder list of
`exists_millerRatio_eval_translationChar_of_avoid`, forwarded unused through two
wrappers. Deleting it (6 sites) rebuilt green and turned a leaf priced at a chapter of
Silverman into one equation.

**Lean's `unusedVariables` linter does NOT find this** — it fires on the declaration
owning the binder, never on the wrappers that forward it, and the wrappers are where a
consumer meets it. Follow the binder by NAME:

    grep -n '\bhc1\b' <every file in the chain>   # binder + forwarding call sites

Appears only in signatures and forwarding argument lists ⇒ dead everywhere. Then ask the
question the linter cannot: **is there a value the hypothesis excludes that some consumer
needs?**

Riders: removing it changes ARITY, so it is an interface edit (class-7) — own commit,
enumerate call sites, and keep it where genuinely used (here
`weilValueProp_translationChar_witness`, whose nondegeneracy branch really needs
`c ≠ 1`). And the dead binder is normally a fossil of the FIRST consumer, so when a
proven theorem is "almost" what your leaf needs, diff its binder list against what you
can supply before deciding it is the wrong tool.

Related: [[flt-inventory-audits-understate-what-exists]],
[[flt-leaf-cost-estimates-are-hypotheses]], [[flt-bridge-layer-is-its-own-module]].
