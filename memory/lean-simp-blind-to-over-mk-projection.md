---
name: lean-simp-blind-to-over-mk-projection
description: An Equiv whose type mentions `(Over.mk g).hom` instead of `g` silently kills every Equiv simp lemma; and `simp [myDef]` may not unfold a def declared under `variable (f) in`
metadata:
  type: reference
---

Two `simp` traps, both measured 2026-07-31 while writing
`Fermat/FLT/Modularity/AbelianSchemeGrpObj.lean`.

**1. `(Over.mk g).hom` is not `g` to `simp`.**  An equivalence stated as
`(Y ⟶ Over.mk f) ≃ RelPoint f Y.hom` for a general `Y : Over S` is *defeq* to the
`g`-indexed one, and the elaborator accepts terms built from it — but once a
hypothesis has type `RelPoint f g` and the equivalence expects
`RelPoint f (Over.mk g).hom`, **`Equiv.apply_symm_apply` and
`Equiv.symm_apply_apply` stop firing**, and `simp` reports zero progress on a goal
that is a one-lemma rewrite.  There is no error, only an unsolved goal that looks
like the lemma is missing.  The fix is to state the equivalence with the base
point as a bare morphism: `(Over.mk g ⟶ Over.mk f) ≃ RelPoint f g`.

**How to apply:** when a `simp` that should be trivial makes NO progress, compare
the *type* of the hypothesis with the *expected* type argument of the lemma's
implicit — a projection like `.hom`, `.left`, `.carrier` standing where a bare
variable should be is the usual culprit.

**2. `simp [myDef]` does not always unfold `myDef`.**  A `noncomputable def`
declared under `variable (f) in` failed to unfold from its equation lemma
(`simp [grpZero]` left `⇑E 1 = grpZero f g` untouched) while its siblings
unfolded fine.  Writing an explicit `theorem myDef_def : myDef … = … := rfl` and
passing that instead fixed every occurrence.  Cheap and worth reaching for
immediately rather than diagnosing.
