---
name: flt-recut-nonempty-iso-as-isiso-named-map
description: A `Nonempty (A ≅ B)` leaf names no morphism, so no route can start; build the canonical map (usually pure adjunction bookkeeping) and leave `IsIso` of it as the leaf
metadata:
  type: project
---

A leaf whose conclusion is `Nonempty (A ≅ B)` is almost always mis-shaped: it
names no morphism, so a prover must invent one before any mathematics starts —
and every route invents the SAME one. Construct it, prove the construction, and
leave `IsIso <that named map>` as the leaf. One leaf for one leaf; what changes
is that the residual is about a named term rather than an existential a prover
could satisfy with an unrelated isomorphism.

**Why:** in this development the map is nearly always FORMAL. Done 2026-07-31 on
`nonempty_modPullback_sectionIdeal_of_isPullback` (`ModularCurve/RelativePicard.lean`,
`φ^*𝒪(−σ) ≅ 𝒪(−σ')`): the construction is `φ^*(kernel.ι) ≫ unitIso` lifted through
`kernel.lift`, and its side condition is three adjunction steps. It cost ~60 lines
and spent exactly ONE of the leaf's seven hypotheses.

**How to apply:**
* `F.map (kernel.ι (adj.unit.app X)) = 0` for free: `F.map (adj.unit.app X)` is a
  SPLIT MONO whose retraction is `adj.counit.app (F.obj X)`
  (`Adjunction.left_triangle_components` IS the retraction equation), so
  `Limits.zero_of_comp_mono` cancels it. Uses nothing about the morphism.
* transport a vanishing across a commuting square with
  `Scheme.Modules.pullbackComp` / `pullbackCongr` plus a three-line
  `F ≅ G → G.map u = 0 → F.map u = 0`.
* get `u ≫ adj.unit.app N = 0` from `F.map u = 0` by UNIT NATURALITY
  (`u ≫ unit.app N = unit.app M ≫ (F ⋙ G).map u`), not by a `homEquiv` calculation.
* `Scheme.Modules.pullback f` and `pushforward f` are registered `Additive` at pin
  `a3364fa`, so `Functor.map_zero` is free.

Related trap, worth knowing before it costs three round trips: `adj.unit.app X`
has type `(𝟭 C).obj X ⟶ (F ⋙ G).obj X`, so `(𝟭 _).obj` wrappers propagate and
`rw [Category.comp_id]` / `rw [comp_zero]` / `simpa` fail with two
character-identical printed types. See [[flt-two-leaves-may-be-one]]'s sibling
rule in CLAUDE.md: when the printed pattern equals the printed target, switch to a
defeq-checking tactic (`exact comp_zero`, `refine h.trans ?_`), or restructure so
the `≫ 𝟙` is never created.

Say in the commit that the direct-sorry count did NOT move, and say what got
smaller instead — a `−1 +1` warning-set delta is indistinguishable from "nothing
happened" to every frontier scan.
