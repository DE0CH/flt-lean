---
name: ext-of-isdominant-beats-valuative-criterion
description: Two morphisms out of Spec R agreeing on Spec (Frac R) are equal by ext_of_isDominant — the valuative criterion is for EXISTENCE and costs a hypothesis the argument never uses.
metadata: 
  node_type: memory
  type: reference
  originSessionId: 908932e2-67d0-420f-b567-1b1b37260cac
  modified: 2026-08-02T20:38:05.378Z
---

`AlgebraicGeometry.ext_of_isDominant [IsReduced Y] {f g : Y ⟶ Z} [Z.IsSeparated]
(ι : W ⟶ Y) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g` is the tool for
"two morphisms `Spec R ⟶ X` agreeing on `Spec (Frac R)` are equal", with
`ι := Spec.map (algebraMap R (Frac R))`. It needs reducedness, dominance and a
separated target — **no valuation ring**.

`IsSeparated.valuativeCriterion` / `ValuativeCommSq` is the same fact specialised
to a valuation ring; the valuative criterion's content is EXISTENCE. Reaching for
it here buys a `ValuationRing R` hypothesis the argument never looks at, and the
`Subsingleton.elim` on `CommSq.LiftStruct` only typechecks if both lift structures
are built INLINE (a `have` on them destroys the defeq).

Companions, none of them instances, all needed every time:

* `IsDominant (Spec.map (algebraMap R (Frac R)))` — 8 lines: image of the unique
  point is `⊥` (`Ideal.comap_bot_of_injective` + `IsFractionRing.injective`), then
  `PrimeSpectrum.closure_singleton`.
* `X.IsSeparated` from `IsSeparated (strX : X ⟶ Spec (CommRingCat.of K))` —
  `rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from strX]; infer_instance`.
* `Spec.map (algebraMap (X.presheaf.stalk z) X.functionField) ≫ X.fromSpecStalk z
  = X.fromSpecStalk (genericPoint X)` — `Scheme.SpecMap_stalkSpecializes_fromSpecStalk`
  plus one `congr 1`; the algebra instance IS `stalkSpecializes` along `η ⤳ z`, defeq
  but not syntactically equal.

**Pass the dominance as an EXPLICIT argument.** A `haveI` for
`IsDominant (Spec.map (CommRingCat.ofHom (algebraMap …)))` is not found by instance
search even though it prints identically to the goal — the two elaborations reach the
`Algebra` instance by different routes. Wrap `ext_of_isDominant` in a three-line lemma
with the dominance explicit. Same family as [[flt-see-the-merge-before-the-merger]]'s
sibling trap "failed to synthesize `C X` where `X` prints identically to what you hold".

Consequence for cutting: with these, "how many points lie outside this affine chart"
splits into a BOOKKEEPING half (the chart's coordinates in the function field; the chart
is where they are regular) and an ARITHMETIC half (how many valuation subrings of the
function field omit a given element) — the second mentioning no scheme at all. Prefer
that to building a second chart as a scheme and gluing.
