---
name: lean-same-morphism-two-points-blocks-rw
description: "Two descriptions of ONE morphism give two syntactically different points, hence two different X.presheaf.stalk types, and `rw` cannot bridge them — take the equation as a hypothesis and `subst` it in a primed lemma"
metadata:
  node_type: memory
  type: project
---

In scheme-theoretic Lean, a hypothesis like
`hl₁ : Spec.map α ≫ l = i₁ ≫ Scheme.Opens.ι U` names ONE morphism `Spec L ⟶ X` twice. Any
construction indexed by its image point — `X.presheaf.stalk (f.base (closedPoint L))`,
`Scheme.stalkClosedPointTo f`, `X.presheaf.germ U _ h` — then exists in two syntactically
different **types**, and `rw [hl₁]` cannot move between them: the motive mentions the membership
proof `h`, whose type also changes, so `rw` reports either "motive is not type correct" or the
much more confusing *"did not find an occurrence of the pattern"* on a goal that visibly contains
it. (The give-away is the trailing note *"the target expression is not type-correct under the
`instances` transparency level"*.)

**The fix is a primed lemma that takes the equation and `subst`s it**, e.g.

```lean
theorem foo' (α : R ⟶ S) (l : Spec R ⟶ X) (m : Spec S ⟶ X) (hm : Spec.map α ≫ l = m) … := by
  subst hm; exact foo α l …
```

`m` is a variable, so `subst` really eliminates it, and the consumer then works entirely in
whichever of the two descriptions its own hypotheses give it. Cost: three lines. This closed the
assembly of `notMem_range_of_valuativeLift_toAffineLine_compl_singleton` after `rw`, `simp` and
`conv` had all failed on it.

Three smaller traps met on the same proof, all worth knowing before the next one:

* **`(f ≫ g).base x` and `g.base (f.base x)` are defeq but not interchangeable for `rw`.** Pick
  whichever form the mathlib lemma you are about to use writes, and STATE your `have`s in that
  form from the start. `Scheme.germ_stalkClosedPointTo` wants the composite form;
  `Scheme.Hom.stalkSpecializes_stalkMap` wants the applied form. Passing a hypothesis of the
  other shape *as an argument* is fine (defeq at application), only `rw` is fussy.
* **`set` shadows a variable whose TYPE it rewrites.** `set U : X.Opens := ⟨{z}ᶜ, _⟩` re-introduced
  `i₁ : Spec L ⟶ ↑U` while leaving `hl₁` referring to the old `i₁✝` — silently splitting the
  context in two. Write the literal out, or generalise properly; do not `set` an opens that
  appears in another hypothesis's type.
* **Factor the element-level endgame into an abstract lemma** whose arguments are bare morphisms
  (`ψ : X.presheaf.stalk z ⟶ CommRingCat.of R`, `θ`, `v`, `r`, `w`) with no `Spec.map … ≫ …`
  anywhere. Then unification fixes the dependent indices from the arguments you pass, and none of
  the above can bite. That is what `false_of_pole` in `CurveAffineComplement.lean` is for.

Related: [[flt-glue-first-no-floating-haves]].
