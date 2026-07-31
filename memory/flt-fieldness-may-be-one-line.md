---
name: flt-fieldness-may-be-one-line
description: Before costing a "generalise this from fields to rings" job, grep the PROOF for where fieldness is actually spent — it is often a single instance line
metadata:
  type: project
---

A leaf stated over a field is not thereby a theorem *about* fields. On
2026-07-31 `Gamma0GITPresentationOver.bcQuot_universal_of_field`
(X0.lean) was generalised to an arbitrary flat ring map by deleting ONE
line — `haveI : Module.Flat k K := Module.Flat.of_free` — and taking
`hf : f.Flat` as a hypothesis instead. Nothing else in the 40-line proof
changed but the signature. The mathlib-facing engine it delegates to,
`InvariantBaseChange.exists_unique_of_isPullback`, had been written for
arbitrary `CommRing` with `[Module.Flat k K]` from the start, and the
surrounding structure `Gamma0GITPresentationOver N S` was already over an
arbitrary base scheme. The generality was there; only the wrapper was narrow.

**Why:** whoever writes a leaf writes it at the generality the *consumer of
the day* needs, and the docstring then records that generality as if it were
the mathematics. A successor reads "over a field", believes a field is
needed, and prices the generalisation as new theory. Here the true price was
one line, and the "hard" remaining content (Zariski gluing over `Spec ℤ`) was
in a completely different place from where the docstring's field hypotheses
suggested.

**How to apply:** before dispatching or costing a generalisation, run the
cheap check — grep the proof body for every use of the restrictive
hypothesis (`Field`, `IsDomain`, `Finite`, `NumberField`, …). Instances are
where it hides: `Module.Flat.of_free`, `Field.toIsField`, a `by infer_instance`
that only succeeds over a field. If the count is one or two, generalise in
place and make the old statement disappear rather than survive as a corollary
(a corollary nothing consumes is free-floating). Then re-audit where the real
obstruction sits — it moves. See [[flt-inventory-audits-understate-what-exists]]
and [[flt-leaf-names-wrong-half-as-hard]].
