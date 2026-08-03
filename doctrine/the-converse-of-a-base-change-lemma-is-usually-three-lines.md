## THE CONVERSE OF A BASE-CHANGE LEMMA IS USUALLY THREE LINES INSIDE ITS OWN PROOF

(2026-08-01, `flt-lean-202`, `ProperPushforward.lean`.)  A file that needs flat base change
almost always states it in ONE direction, because that is the direction its first consumer
wanted.  `isIso_appTop_of_isIso_appTop_baseChange` is the DESCENT — `Γ(Z_L) = L` implies
`Γ(Z) = K` — and a later route needs the ASCENT.  The ascent reads as a second theorem to
prove and is not one: **both directions come out of the same `IsPushout` square, which the
existing proof already builds.**  Only the last step differs, and the converse's last step is
the cheap one:

* descent needs `isIso_of_isPushout_of_isField` — a dimension count over two fields;
* ascent is `CategoryTheory.IsPushout.isIso_inr_of_isIso`, i.e. *the opposite leg of a pushout
  along an isomorphism is an isomorphism*, one lemma, no hypothesis on `L` at all.

So before costing the converse of any base-change/descent lemma, **read its PROOF and find the
square**.  Everything up to `rw [isIso_pushoutSection_iff] at hpo` transcribed verbatim here
and the ascent went green first try; and it is strictly MORE general than the descent, since
the field hypothesis on the target disappears.

Two riders from the same run.

* **Restate it in `IsPullback` form, not for `Limits.pullback`.**  The consumer was a square
  handed over by `isPullback_fiberToSpecResidueField_of_isPullback` (mathlib: *the fibre of a
  base change is the base change of the fibre*, and it is what makes the whole "`h` is stable
  under arbitrary base change" statement a five-line proof).  A version stated for the CHOSEN
  pullback needs a transport at every use; `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`
  already takes an abstract `IsPullback`, so the generalisation costs nothing.
* **`MorphismProperty.pullback_snd _ _ inferInstance` needs `(P := @Foo)` when the target is a
  `def`.**  `Scheme.Hom.fiberToSpecResidueField` is a plain `def` for `pullback.snd`, so
  instance search does not unfold it — and then a `[QuasiSeparated g]` binder **fails to
  synthesize against a `haveI` that is literally in context and prints identically**.  Making
  the two hypotheses ORDINARY EXPLICIT ARGUMENTS fixes it (an explicit argument is checked up
  to defeq; instance search is not), which is the standing rule about type synonyms met
  through a `def` instead.  Note `QuasiCompact` happened to succeed where `QuasiSeparated`
  failed, so "one of them resolves" is no evidence about the other.

