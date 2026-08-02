---
name: flt-local-conclusion-rescues-a-failed-hypothesis
description: "When a leaf's blocking hypothesis is FALSE globally, check whether the conclusion is defined prime-locally — the local version of the hypothesis is often true and free."
metadata: 
  node_type: memory
  type: project
  originSessionId: 0634e510-0b55-4d8c-be57-e8ffad7c0d69
  modified: 2026-08-02T03:47:57.691Z
---

`isRegularRing_of_isInvariant_of_smooth` (`Fermat/FLT/Mathlib/RingTheory/InvariantTensorRegular.lean`)
sat open because every lemma its classical route needed carried `[IsDomain R]`, and `IsDomain R`
is genuinely FALSE there (`R = S^G` with `S` a smooth curve algebra that splits into components).
Its docstring priced the repair as a `G`-equivariant PRODUCT DECOMPOSITION of `S` — a structure
theory of reduced normal noetherian rings absent from the pin.

**`IsRegularRing` is DEFINED prime-locally** (`IsNoetherianRing` + `∀ p, IsRegularLocalRing
(Localization.AtPrime p)`), so the hypothesis that must hold is `IsDomain (Localization.AtPrime p)`
— and a product of domains has every localization a domain. Localizing bought exactly what the
decomposition was for, for free. Closed 2026-08-02; the residue is normality only.

**Why:** the audit reasoned from the LEMMA LIST ("every lemma I would use carries `[IsDomain R]`")
rather than from the GOAL. Unfolding the goal's definition once is the whole insight, and it is
cheaper than any inventory search.

**How to apply:** before pricing the repair of a failed hypothesis, ask whether the conclusion is
one of the "for every prime/maximal ideal" notions — `IsRegularRing`, `IsReduced`, flatness,
`IsIntegrallyClosed` for a domain. If it is, only the localized hypothesis is needed, and the
usual reason a global hypothesis fails (several components, several minimal primes, a product) is
precisely why its local versions hold. Companion technique: `Localization.AtPrime p` is a domain
**iff `ker (R → R_p)` is prime**, which turns "is this localization a domain" into an ideal
computation upstairs with no minimal-prime correspondence — see
[[flt-inventory-audits-understate-what-exists]] and [[flt-leaf-cost-estimates-are-hypotheses]] for
the two audit failures this one composes with.
