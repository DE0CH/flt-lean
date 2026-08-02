---
name: lean-rw-rfl-lemma-picks-wrong-redex
description: "`rw` fails and `erw` matches the WRONG subterm on `rfl`-lemmas stated with `dsimp%` (`tensorHom_app`, `tensorHom_tmul`) — write `rw [show <exact LHS> = <exact RHS> from rfl]` to pin the redex"
metadata: 
  node_type: memory
  type: reference
  originSessionId: e2ca5e28-541b-49fb-b30b-ce28aa6348bd
  modified: 2026-08-01T21:29:31.316Z
---

(2026-08-01, `flt-lean-150`; cost four of eight iteration rounds.)
`PresheafOfModules.Monoidal.tensorHom_app` and `ModuleCat.MonoidalCategory.tensorHom_tmul` are
both proved `rfl` and both are STATED with `dsimp%`. Consequences on a goal that displays the
pattern:

* `rw [Monoidal.tensorHom_app]` reports *"Did not find an occurrence of the pattern
  `(Monoidal.tensorHom ?f ?g).app ?X`"* — the goal's `⊗ₘ` is `MonoidalCategory.tensorHom` through
  the instance, not the raw constant;
* `erw [ModuleCat.MonoidalCategory.tensorHom_tmul]` SUCCEEDS and matches something else: here it
  unfolded `μ (pushforward φ)` into `extendRestrictScalars` machinery and produced a half-page
  goal with `TensorProduct.mk` and adjunction counits in it.

**How to apply:** write the step as

    rw [show <the exact LHS, spelled out> = <the exact RHS> from rfl]

The `rfl` proof forces the redex you wrote and nothing else can fire. This is the standing
"printed pattern equals printed target ⟹ use a defeq-checking tactic" rule
([[lean-same-morphism-two-points-blocks-rw]]) with the extra twist that you must ALSO pin WHICH
subterm is rewritten — `exact`/`Eq.trans` alone will not, because the surrounding term has to
survive.

Same session, same file, two more of the standing traps confirmed: `have e : M₁ ≅ M₂ := isoMk …`
then `f = e.hom` fails by `rfl` (use `letI`; a `have` on DATA forgets the value), and
`naturality_apply` output carries a `(𝟭 _).obj` wrapper that blocks the next `rw` until
`simp only [Functor.id_obj]` strips it.
