---
name: flt-faithfulness-prose-vs-binder
description: "A leaf's faithfulness bullet names the property it wants in English; the Lean binder may be strictly weaker, and then the leaf is usually FALSE"
metadata: 
  node_type: memory
  type: project
  originSessionId: 4d6e6639-110d-4830-bb14-d6203ebc8480
  modified: 2026-08-02T09:24:53.260Z
---

(2026-08-02, `flt-lean-115`, `exists_genRelPic` in `Modularity/GeneralisedPicard.lean`.)

Mature leaves in flt-lean carry a FAITHFULNESS section, one bullet per hypothesis,
shaped *"`hfoo` — `X → S` is P, **which is what gives** Q"*. The prose is English, the
binder is Lean, **and they can name different classes. When they do the leaf is usually
FALSE**, because the docstring's argument is correct and the signature does not supply
its input.

Here the bullet said "geometrically **integral** fibres, which is what gives
`f_*𝒪_X = 𝒪_S` universally"; the binder was `GeometricallyIrreducible`, which is
`geometrically (IrreducibleSpace ·)` — purely topological. Mathlib records the gap
itself: `GeometricallyIntegral = GeometricallyReduced ⊓ GeometricallyIrreducible`.
Refuted by `X = Spec k[ε]` over `Spec k`, `Z` the reduced point, tested at any `T` with
`H¹(T,𝒪_T) ≠ 0`.

**Two greps, on every faithfulness bullet:**

1. Is the noun in the prose the same class as the binder? The pairs that recur are
   integral/irreducible, reduced/normal, finite/quasi-finite, proper/separated,
   flat/faithfully flat — and mathlib usually has a lemma decomposing the stronger one.
2. Find the in-tree PRODUCER of the property the bullet promises and read ITS hypothesis
   list; that list is the true one. A bullet promising a property the leaf cannot derive
   is the tell.

**If the argument has TWO steps, check the bullet checks both.** This one verified
`Γ(T,𝒪^×) ↪ Γ(Z_T,𝒪^×)` and silently assumed `Aut(ℒ) = Γ(T,𝒪^×)` — the other
injectivity, and the one that failed.

**Why:** a faithfulness section reads as the check that the leaf is not false, so nobody
re-runs it; and it is written in the register where a class name and its informal gloss
look interchangeable.

**How to apply:** repair by ADDING a binder naming the consumed property (here
`HasUniversallyTrivialPushforward`), not by restating the geometry — adding cannot make a
true leaf false, so sibling bullets are inherited, and say why. Related:
[[flt-leaf-cost-estimates-are-hypotheses]], [[leaf-falsity-can-live-in-a-definition]],
[[flt-decomposition-drops-a-hypothesis]], [[flt-substitute-leaf-cannot-consume-its-hypothesis]].
