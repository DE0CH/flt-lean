---
name: lean-apply-not-refine-when-goal-pins-metavariable
description: Use `apply` rather than `refine f _ x y` when a later argument's TYPE mentions an implicit the goal would determine
metadata:
  type: reference
---

When a theorem's later argument has a type mentioning an earlier implicit —
`(cm) … (hι : ι.hom ≫ IsFibreIdent.openSection cm.genIdent cm.model.comm = hX.j)` —
`refine f _ hX ι hι ?_ …` elaborates the arguments BEFORE unifying the result with
the goal, so `hι` is checked against a type still containing `?cm`:

    Application type mismatch: the argument hι has type
      ι.hom ≫ eGen.openSection ⋯ = hX.j
    but is expected to have type
      ι.hom ≫ (IsX0CurveModel.genIdent ?m.386).openSection ⋯ = hX.j

**Why:** the two print as almost the same thing, so it reads as a wrong lemma or a
coercion problem rather than as elaboration order.

**How to apply:** `apply f (namedImplicit := …)` unifies the CONCLUSION with the
goal first, which pins the implicit and lets every argument land; the remaining
side conditions come back as goals. Supplying the implicit explicitly also works
and is the expensive option when it is a large structure literal.

Measured 2026-07-31, `flt-lean-56`, on `IsX0CurveModel.classify_genericOpen`.
Sibling of [[lean-same-morphism-two-points-blocks-rw]] and the standing
"printed pattern equals printed target ⟹ switch to a defeq-checking tactic" rule:
same symptom class, different cause (unresolved metavariable, not a coercion).
