## A HYPOTHESIS AN AUDIT CALLS UNUSED IS FREE STRENGTH — SPEND IT, AND THE MISSING THEORY MAY GO AWAY

(2026-07-31, `flt-lean-254`, `ModularCurve/RelativePicard.lean`.) A mature leaf's
hypothesis audit often ends with a line of the form *"`_hproper` and `_hsmooth` are
**not used by the argument above at all** … a prover may ignore both"*, kept only because
the call site holds them for free. That sentence is a claim about ONE route, and it is
the most under-read line in the docstring, because it reads as permission rather than as
information.

`isIso_modPullbackSectionIdealMap` — the base-change comparison `φ^*𝒪(−σ) ⟶ 𝒪(−σ')` — had
exactly that line, and its route was priced at **flat base change for `Scheme.Modules`,
which the pin does not have and which the audit had correctly surveyed as absent**. Spending
the two "unused" hypotheses deletes that input:

* `IsProper` and `SmoothOfRelativeDimension 1` are both stable under base change, so `strY'`
  is again a proper smooth relative curve and the file's own
  `isInvertibleSheaf_sectionIdeal_of_isSection` applies to `(strY', σ')` and not only to
  `(strY, σ)`;
* so BOTH sides of the comparison are invertible sheaves — the source by
  `isInvertibleSheaf_modPullback`, the target by that;
* and **a map between invertible sheaves is an isomorphism as soon as it is an
  epimorphism** (locally it is multiplication by a section, and a surjective one is by a
  unit). The injectivity half — which IS the `Tor`-vanishing the flat-base-change
  development was for — comes for free.

**The generalisable check, and it costs one read of the binder list: for each hypothesis an
audit calls unused, ask what it would GIVE you, not whether the recorded route needs it.**
In this development the answer is usually a base-change-stable property, hence a second
instance of a theorem the file already proves — and a second instance of an existing theorem
is the cheapest input there is. An audit lists what its author's argument consumed; it is
silent about what a different argument could consume, and the hypotheses it calls decoration
are exactly the ones no route has tried.

Two riders from the same run:

* **The old witness is the sanity check on the new cut, and it should be re-read rather than
  copied.** That leaf carried a refutation of the tempting weaker hypothesis (ask only that
  the SECTION square be cartesian): `Y = 𝔸¹_k`, `σ` the origin, `Y' = Spec k[t]/(t)`,
  `σ' = 𝟙`. Under the new decomposition that witness has the map `φ^*I_σ ⟶ I_{σ'} = 0`
  being an EPI and failing invertibility of `I_{σ'}` — so the two halves of the cut fail on
  exactly the two sides the witness distinguishes. **When you re-cut a node, run its recorded
  counterexample against each new half**; agreement of that kind is the strongest evidence a
  cut is along the right seam, and disagreement means one half is false.
* **`IsPullback.of_right` plus `IsPullback.of_id_fst` proves "the section square is
  cartesian" in three lines, in an arbitrary category.** Given `IsPullback φ strY' strY h`
  and sections with `σ ≫ strY = 𝟙`, `σ' ≫ strY' = 𝟙`, `σ' ≫ φ = h ≫ σ`, the outer rectangle
  of the horizontal pasting has identities top and bottom, so it is cartesian for free and
  the left square follows. Reach for the pasting lemmas before writing a
  `PullbackCone.isLimitAux'` by hand — the hand-written version needs three explicit
  verifications and hits the `(PullbackCone.mk …).pt`-is-not-syntactically-`T'` trap on every
  one of them.

