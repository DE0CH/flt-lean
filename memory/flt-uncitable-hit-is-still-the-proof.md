---
name: flt-uncitable-hit-is-still-the-proof
description: An absence audit asks "can I call this?"; ask "does a proof of this shape exist anywhere in the tree?" — a hit in an unimportable layer still hands you the whole route.
metadata:
  type: project
---

`exists_residueField_ringHom_of_valuationSubring` (`Modularity/TateModule.lean`) sat open
behind a dated, entirely TRUE paragraph: *"`grep` over `Mathlib/` for
`IsAlgClosed.*ResidueField` is empty … both halves have to be written."* Four hits exist in
`Fermat/`, and one — `GaloisRepresentation.exists_resIso_of_comap_toSubring_eq_range` in
`FreyCurve/IsogenySignature.lean` — is the same theorem over `ℚ`, PROVEN, both halves
written out. The leaf closed by transcription (`AlgebraicClosure ℚ ↝ AlgebraicClosure F`),
first try, 15 s of elaboration (2026-08-02, flt-lean-332).

**Why the standing "grep `Fermat/` too" rule did not fire:** the hit is in a layer
`Modularity` cannot import (`FreyCurve`/`EllipticCurve` are downstream). So *"is there
something I can CALL?"* correctly answers no — and that is the wrong question.

**Why:** an uncitable proof still gives the route, the mathlib lemma names and the tactic
script, which is nearly all of the work. Only "no proof of this shape exists anywhere" is
expensive news, and it is much rarer than audits claim.

**How to apply:** before costing any leaf off an absence claim, run
`grep -rn '<the CONCLUSION, 2-3 spellings>' --include=*.lean Fermat/` with **no import-cone
filter**, then decide separately whether the hit is a call or a copy. When writing such a
paragraph, quote the command and name the trees searched — "grep over `Mathlib/` is empty"
is read downstream as a claim about the project. See [[flt-inventory-audits-understate-what-exists]],
[[audit-lacks-x-is-about-x]], [[flt-absence-audit-greps-consumer-vocabulary]],
[[flt-port-may-exist-in-unimported-sibling]].
