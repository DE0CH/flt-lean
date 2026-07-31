---
name: flt-limit-machinery-vs-greedy-recursion
description: An audit prescribing "inverse limit of nonempty FINITE sets" is usually a greedy recursion in disguise — check whether the level-wise EXTENSION step always succeeds, and the finiteness hypothesis dies with the limit
metadata:
  type: feedback
---

A route note that says "build it level-wise, then take the limit, using
`nonempty_sections_of_finite_cofiltered_system`" is a hypothesis about the proof,
not the proof. Before importing the category-theoretic limit machinery, ask the
sharper question: **given a solution at level `n`, can you always EXTEND it to
level `n + 1`?** If yes, the whole tower is built by plain `Nat.rec` and neither
the limit nor the finiteness of the levels is used at all.

This happened on the continuous set-theoretic section of a small extension
`S ⧸ K ↠ D.R` (brick (ii) of `exists_obstructionCocycle_smallExtension_deformation`,
`HardlyRamified/Deformation.lean`, 2026-07-31). The leaf's audit prescribed
sections of the finite quotients `A/𝔪ⁿ ↠ B/𝔫ⁿ` assembled by
`nonempty_sections_of_finite_cofiltered_system`. But sections do **not** form an
inverse system — a level-`(n+1)` section has no restriction to level `n`, since
there is no map `B/𝔫ⁿ → B/𝔫ⁿ⁺¹` — so the naive system does not even typecheck,
and repairing it needs the auxiliary "compatible partial towers `Z n`" system.

Meanwhile the extension step is a two-line calculation: `π(𝔪ⁿ) = 𝔫ⁿ` because `π`
is surjective, so the required correction always exists. Greedy recursion then
gives the tower, and `IsPrecomplete`/`IsHausdorff` finish it. Zero category
theory, zero finiteness, zero point-set topology.

**Why:** the limit formulation is what you reach for when extension can FAIL and
you need a compactness argument to rule out a dead end. When extension never
fails, the limit is pure overhead — and it drags in hypotheses (finite levels,
cofiltered index category) that the theorem does not need, which then have to be
verified at every call site.

**How to apply:** when a docstring or task prompt names an inverse-limit lemma,
first write down the extension step as an explicit `∃`. If you can prove it
unconditionally, drop the limit and recurse. Two further corollaries seen on the
same leaf:

* State the regularity ALGEBRAICALLY (`a - b ∈ 𝔫ⁿ → s a - s b ∈ 𝔪ⁿ`) rather than
  as `Continuous s`. It is strictly stronger, and it keeps `TopologicalSpace` out
  of the statement — which matters when the consumer transports its topology
  through a `RingEquiv` and is known to hit `unknown free variable`.
* **Completeness of a small extension comes from its TARGET, not its source.**
  `isPrecomplete_of_isSmallExtension`: `𝔪_A · ker π = ⊥` plus Artin–Rees
  (`Ideal.exists_pow_inf_eq_pow_smul`) gives `𝔪^(c+1) ⊓ ker π = ⊥`, after which a
  Cauchy sequence's kernel component is eventually constant. So no completeness
  input about the presenting power-series ring is needed — see
  [[flt-grep-project-not-just-mathlib]], which is how
  `isPrecomplete_mvPowerSeries` (already proven in
  `Fermat/FLT/Mathlib/RingTheory/PowerSeries/AdicComplete.lean`) was found and
  then turned out not to be needed either.
