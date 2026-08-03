## "THE EASY CASE OF X" IS AN APPLICATION OF X, NOT A LEAF — READ X'S SIGNATURE

(2026-07-31, `exists_isRelPicZeroOf_baseChange` in `ModularCurve/X0.lean`, closed the
same day it was opened.)

That leaf carried a FIELD-BY-FIELD PRICING TABLE — ten rows, one per field of
`IsRelPicZeroOf`, each naming what the transport costs and whether the ingredient is
proven. Nine rows came out exactly as priced. The tenth, `aj_spec`, was labelled in
bold **"THE ONE NEW GEOMETRIC INPUT"** and instructed a successor to state

    modPullback ψ.hom (sectionIdeal (relSection y)) ≅ sectionIdeal (relSection x)

as a new leaf in `RelativePicard.lean`, *"beside its harder sibling
`nonempty_modPullback_sectionIdeal`"*, describing it as **the easy case** of that
sibling. On that basis the whole route was priced `1 → 1`.

**No leaf had to be stated, and the route is `1 → 0`.** The sibling had been recut
one day earlier as `nonempty_modPullback_sectionIdeal_of_isPullback`, over an
**abstract cartesian square** `IsPullback φ strY' strY h` instead of over
`curveBaseChangeMap` — a generalisation its own docstring records and justifies. An
ISOMORPHISM square with `h = 𝟙 T` *is* a cartesian square
(`CategoryTheory.IsPullback.of_horiz_isIso`, both `ψ` and `𝟙 T` being isos), so the
"new" statement is that leaf applied, and the frontier went DOWN by one.

**The rule: when a docstring calls a step "the easy/special case of `X`", open `X`
and read its SIGNATURE before writing anything.** If `X` quantifies over an abstract
square, an abstract morphism, or an abstract hypothesis of which your case is a
concrete instance, you do not have a leaf to cut — you have an application, and the
`grep -n 'theorem X' -A12` that establishes it takes ten seconds.

Why this is not caught by the checks already in this file: the over-pricing is not a
stale claim about MATHLIB, and not a stale ownership record. It is a docstring that
was accurate about a leaf **in a file it imports**, written before that leaf was
generalised. Nothing re-reads a pricing table when a neighbour is restated. Same
family as *leaf cost estimates are hypotheses* and *inventory audits understate what
exists*, with the stale reference one file away instead of in the pin.

**Corollary for whoever GENERALISES a leaf:** the generalisation is only worth what
its consumers know about it. Say in the new docstring which sibling docstrings now
over-price their routes — here, one sentence on
`nonempty_modPullback_sectionIdeal_of_isPullback` saying "this abstract form also
covers transport along an ISOMORPHISM of curves, `h = 𝟙`" would have saved the leaf
being priced wrong for a day.

Two mechanical notes from the same task, both worth knowing in advance:

* **A helper whose natural home is upstream may be worth stating downstream anyway,
  for BUILD ECONOMICS.** `relPicEquiv_transport` (the `relPicEquiv_modPullback`
  generalisation this route needs) belongs in `RelativePicard.lean`. Putting it there
  invalidates `RelativePicard → AmpleSheaf → AbelianSchemeIsogeny → X0` — four
  modules, ~25 000 lines of re-elaboration — for five lines. It is stated in `X0.lean`
  with a docstring saying where it belongs and why it is not there. Say so explicitly,
  or the next reader "fixes" it into a duplicate.
* **A scratch module can verify an X0-sized edit COMPLETELY when the edit's only
  upstream dependencies are two small structures.** `IsFibreIdent` and
  `IsSmoothProperCurve` are eight lines between them; re-declaring both in a scratch
  that imports `RelativePicard` + `AbelianSchemeIsogeny`, and taking
  `exists_fibreIdentIso`'s conclusion as a hypothesis, verified all 430 lines —
  helpers, the ten-field structure literal, and the target — in **20 seconds** per
  round, against ~35 minutes for one `lake env lean` of `X0.lean`. Mock the STRUCTURES,
  and take the upstream `∃`-theorem as a hypothesis in exactly its published form, so
  that the transplant is `obtain ⟨…⟩ := <the real theorem>` and nothing else.

