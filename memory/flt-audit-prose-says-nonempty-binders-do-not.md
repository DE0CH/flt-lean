---
name: flt-audit-prose-says-nonempty-binders-do-not
description: A "why every conjunct is TRUE" audit can quietly restate the hypothesis list in prose; the extra adjective ("a NONEMPTY open subscheme") is the missing binder, and the degenerate object refutes the leaf.
metadata:
  type: project
---

(2026-08-02, `exists_boundarySubscheme_of_projectiveCompactification`,
`Fermat/FLT/Modularity/MoretBailly.lean`.) The leaf carried the strongest possible
clean bill of health — a conjunct-by-conjunct faithfulness audit ending

> **None of the four can fail, so this leaf is not one that will turn out to be
> FALSE AS STATED.**

It was FALSE as stated, and the refutation is one word long. The audit's own second
paragraph opens

> `X̄` is a smooth proper geometrically irreducible curve over `ℚ` and `C` is a
> **nonempty** open subscheme …

and "nonempty" appears **in the prose and in no binder**. `C` was an arbitrary
`Scheme`. Take `C = ∅` (`Scheme.emptyTo X̄` is an `IsOpenImmersion` INSTANCE in the
pin), so `(range j.base)ᶜ = univ`, which satisfies the `hZ : …ᶜ.Nonempty` binder
*trivially* — the one hypothesis that looks like it is about nonemptiness is the one
the degenerate witness satisfies most easily. The conclusion then hands back a
closed immersion with full image that is finite over `Spec ℚ`, which forces
`Finite ↥X̄`; `ℙ¹_ℚ` is infinite.

**The check, and it is mechanical: diff the audit's PROSE restatement of the
hypotheses against the BINDER LIST, adjective by adjective.** An audit is written by
someone holding the intended instance in their head, so the prose is a description
of that instance, not of the quantifier. Every adjective the prose adds and the
binders do not is a candidate missing hypothesis, and the degenerate object
(`∅`, the zero ring, the trivial group, the zero morphism) is the witness.

Two riders.

* **A nonemptiness binder elsewhere in the list is not the one you need, and its
  presence is what makes the gap invisible.** `hZ` reads as "the boundary is
  nonempty", which sounds like it rules out degeneracy; it rules out the opposite
  degeneracy. When a statement has two objects, check nonemptiness of *each*.
* **The repair is almost always already in the caller's hand — check before
  reporting a refutation as a blocker.** Here the sole call site carries
  `hreal : HasRationalPoint fC (ULift ℝ)`, i.e. a morphism `Spec (ULift ℝ) ⟶ C`,
  so `Nonempty ↥C` costs four lines there and no statement above it moved. A leaf
  refuted-and-repaired-in-place is a better outcome than a leaf refuted and
  escalated. See [[flt-leaf-hypotheses-are-a-superset]].

Related: [[flt-degenerate-case-does-not-transfer-between-twins]] and
[[flt-decomposition-drops-a-hypothesis]] are the same gap arriving through a
TRANSCRIPTION and through a CUT; this one arrives through an AUDIT, which is worse,
because an audit is what a later reader consults *instead of* re-deriving.
