---
name: flt-substitute-leaf-cannot-consume-its-hypothesis
description: "When a leaf's hypotheses are a known substitute for some hypothesis h, no theorem carrying h can be an input to it — a docstring citing one has the logical direction backwards"
metadata: 
  node_type: memory
  type: project
  originSessionId: 4d6e6639-110d-4830-bb14-d6203ebc8480
  modified: 2026-08-02T09:25:13.727Z
---

(2026-08-02, `flt-lean-115`, `exists_genRelPic` in `Modularity/GeneralisedPicard.lean`.)

That leaf's recorded route named its right-hand term as "`Fermat.exists_relPicFull`
(BLR 8.2/1), already in this module's import closure". It IS in the closure and it is
**inapplicable**: it takes `(o : RelPoint strX (𝟙 S))`, a SECTION of `X ⟶ S`, and the
whole reason Moret–Bailly introduces the rigidificator `Z` (finite flat surjective over
`S`) is that no section exists.

Witness: over `ℚ` the conic `x²+y²+z²=0` is smooth proper geometrically integral with no
rational point and only degree-`2` closed points, so `Z` exists and `o` does not. The
consumer was in exactly that position — it is trying to PRODUCE rational points.

**The check, one read of the cited theorem's binder list: when a leaf's hypotheses are a
known SUBSTITUTE for some hypothesis `h` — a multisection for a section, a rigidificator
for a base point, a finite étale cover for a rational point, a Chebotarev prime for a
splitting condition — no theorem carrying `h` can be an input to that leaf.**

**Why:** a substitute exists precisely because `h` is unavailable, so citing a theorem
that needs `h` inverts the dependency. In the literature the implication usually runs the
other way — BLR 8.2/3 and FGA make the RIGIDIFIED functor primary, because its objects
have no automorphisms, and recover `Pic` as a quotient — so the leaf typically SUBSUMES
the theorem its docstring cites as its input (here: take `Z = S`, `ι = o`).

**How to apply:** before costing a route off a cited theorem, read that theorem's binders
and instantiate them against the leaf's hypotheses. Record the finding on the leaf, or the
next prover spends the run trying to apply it. Related:
[[flt-faithfulness-prose-vs-binder]], [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-inventory-audits-understate-what-exists]].
