---
name: flt-true-and-standard-is-the-ungrepped-leaf
description: "A leaf whose docstring says \"TRUE and standard, nothing missing from the pin\" is the one nobody grepped — read its step list as a search query, not a plan."
metadata: 
  node_type: memory
  type: project
  originSessionId: 7e708486-ec28-49f0-8af7-5e0f94a8ecc7
  modified: 2026-08-02T11:46:02.045Z
---

Every "absence claim" rule in this project addresses a docstring that says
something is MISSING. The opposite shape is commoner and cheaper to miss,
because the leaf looks *finished*: a docstring that says **"TRUE and standard,
in three steps, none of which needs anything not at this pin"**, lists the
steps, and stops.

Measured 2026-08-02 on `isIntegral_curveBaseChange_specQ`
(`Fermat/FLT/ModularCurve/X0.lean`, cut 2026-07-31). Its three steps —
smooth over a field ⟹ regular stalks ⟹ reduced; connected + locally
irreducible ⟹ irreducible; irreducible + reduced = `IsIntegral` — were all
correct, and `Modularity/AbelianSchemeIsogeny.lean`'s
`isIntegral_of_smooth_geometricallyConnected` had been PROVEN along exactly
those steps since **2026-07-27, four days before the leaf was cut**, in a
module `X0.lean` `public import`s. The leaf closed in five lines.

**Why:** a leaf claiming something is missing attracts a re-grep (the doctrine
says to re-grep absence claims). A leaf claiming nothing is missing attracts
neither an attack (it is not blocked) nor a grep (it asserts no absence).

**How to apply:** treat the docstring's step list as a SEARCH QUERY. Before
writing step one, grep the WHOLE tree for the CONCLUSION of the last step —
never for the leaf's own name, which is chosen for the OBJECT while the proven
theorem is named for the HYPOTHESES it consumes (the two shared no component
here, and the theorem was 89 000 lines away in another module):

    grep -rn 'IsIntegral' --include=*.lean Fermat/ | grep -i 'connected\|smooth'

If you are the one CUTTING such a leaf, run that grep and put the result in the
docstring ("grepped `<query>` on `<date>`, nothing"), so the next reader
inherits a search rather than a plan.

Related: [[flt-inventory-audits-understate-what-exists]],
[[flt-leaf-names-the-module-holding-its-answer]],
[[flt-leaf-cost-estimates-are-hypotheses]].

Two pin facts banked with it: `Smooth` and `GeometricallyConnected` each carry
a DIRECT `instance … : P (pullback.snd f g)`, so base-changing them is
`inferInstance` (unlike `SmoothOfRelativeDimension`, whose stability is a
`lemma`); and `GeometricallyConnected` DOES forbid the empty scheme
(`geometrically (ConnectedSpace ·)`, and `ConnectedSpace` extends `Nonempty`),
so a leaf pairing it with an `IsIntegral` conclusion needs no nonemptiness
clause.
