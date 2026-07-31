---
name: flt-pin-classifying-function-at-tautological-point
description: "A leaf blaming a Nonempty hypothesis for handing out unrelated classifying functions is repaired in ~15 lines by evaluating the structure's naturality field at the tautological point"
metadata: 
  node_type: memory
  type: project
  originSessionId: bb252123-2f15-43e6-8073-059154b16c02
  modified: 2026-07-31T13:27:16.217Z
---

(2026-07-31, `flt-lean-266`, `ModularCurve/RelativePicard.lean`.) Representability
structures here are an arbitrary classifying FUNCTION on points plus a naturality
field (`IsRelPicOf`: `sheaf` + `sheaf_pre`). A leaf whose hypothesis is
`∀ V, Nonempty (IsRelPicOf … (pstr ∣_ V))` really does hand out one unrelated
function per `V` — the docstring's argument for that is correct and was repeated in
the task prompt as the reason the cut sits where it does.

**It does not matter, and the repair is one formal step.** The object has a
TAUTOLOGICAL point (`𝟙 P` as a `P`-point of `P` over its own structure morphism);
`RelPoint.pre p.1 p.2 (tautological) = p` is `Subtype.ext (Category.comp_id _)`, so
the naturality field evaluated there says `sheaf p ~ p^* (sheaf tautological)` for
EVERY `p`. So any one classifying function is pullback of a single universal object,
and `inj`/`surj` transfer to that pullback by transitivity/symmetry of the relation.
Unrelated functions become pinned objects — step 1 of every gluing argument — for
~15 lines (`exists_relPicUniversal_of_isRelPicOf`).

**Why:** "the functions differ by an automorphism of the functor" and "there is
nothing to glue" are different claims; a gluing argument needs OBJECTS, and Yoneda
is exactly the statement that a naturality field pins them.

**How to apply:** when a docstring blames a `Nonempty` hypothesis for incomparable
data, look for a naturality field and an identity/tautological point before
believing it. Then cash in whatever the route note calls "immediate" — here
`invertible` and `sheaf_pre` for `sheaf := p ↦ p^* poin` really were four lines
(`isInvertibleSheaf_modPullback`; `curveBaseChangeMap_comp` + `modPullbackCompIso` +
`relPicEquiv_of_iso`), and three of five structure fields became theorems while the
direct-sorry count stayed 1 → 1. Report that as a RECUT and say what got smaller.
See also [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-inventory-audits-understate-what-exists]].
