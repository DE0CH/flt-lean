---
name: flt-bridge-layer-is-its-own-module
description: "An audit saying \"the bridge from X-vocabulary to Y-vocabulary is missing\" greps the X file; the bridge layer is a different module by construction — grep for the TARGET vocabulary."
metadata: 
  node_type: memory
  type: project
  originSessionId: ee11f2ce-9920-435e-b5d8-fb18e0f75d21
  modified: 2026-08-02T04:07:42.444Z
---

2026-08-02, `flt-lean-267`. `weilValue_self_config_eq_one`'s Route 2 ended: *"Every
ingredient exists in `WeilPairingDescent.lean` (…); what is missing is the bridge from
the generic-point evaluations that file works with to the honest point evaluations
`AdjoinRoot.evalEval`."* The first clause was true and checkable, which is what made the
second convincing — the author had clearly opened the file they named.

The bridge is `exists_pointEval_specialization`, **PROVEN 2026-07-25**, in
`WeilPairingStageB.lean` — a different module, already `public import`ed, stated
uniformly in `(Q, m)` so that it covers both `z ↦ z∘τ_{Q₀}` and `z ↦ z∘[p]`, with a
~500-line `EvalsTo`/`SpecPoint` calculus under it (`specPoint_zsmul` is Silverman AEC
VII.2.1 for the local ring at a point).

**A development's bridge layer is its own module, and it is never the module whose
vocabulary the audit is written in** — an audit written in the source vocabulary greps
the source file, and the bridge lives elsewhere because that is what a layer is. So
grep for the TARGET vocabulary across the cone and read the file with the most hits:

    grep -rc '<target vocabulary>' --include=*.lean Fermat/ | grep -v ':0' | sort -t: -k2 -n

`WeilPairingStageB.lean` had 375 `evalEval` hits and was named nowhere in the audit.

Same family as [[flt-inventory-audits-understate-what-exists]], with the scope error
being a MODULE rather than a repository. See also
[[flt-dead-hypothesis-blocks-a-route]], the other half of the same task.
