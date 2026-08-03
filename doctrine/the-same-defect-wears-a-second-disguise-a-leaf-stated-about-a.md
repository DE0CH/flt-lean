## THE SAME DEFECT WEARS A SECOND DISGUISE: A LEAF STATED ABOUT A *BASE CHANGE* OF THE OBJECT ITS CITATION IS ABOUT

(2026-07-31, `RelativePicard.lean`, the day after the "every representing object" section
above, in the same file, from the same root cause.)

The section above says a leaf must be stated in the shape its citation is stated in. The
"every object" shape is one way to violate that. Here is the other, and it is much easier to
miss because the statement looks perfectly ordinary:

    theorem exists_relPicOf_isAffineOpen (strX : X ⟶ S)
        (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX) …
        (V : S.Opens) (hV : IsAffineOpen V) :
        ∃ P pstr, Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) pstr) ∧ …

**The hypotheses are about `strX`; the conclusion is about `X ×_S V ⟶ V`.** BLR 8.2/1 is a
theorem about a relative curve over an affine base. It is not a theorem about the base change
of a relative curve over an open of some other scheme. So a prover arriving at this leaf must
first prove step (i) — the hypotheses survive base change — before a single line of the
citation applies, and step (i) is invisible: it is not in the statement, it is not a leaf, it
is a sentence in the docstring.

The docstring in this case said so explicitly, and priced it as a feature:

> the base-change stability of `IsProper`, `SmoothOfRelativeDimension 1`,
> `GeometricallyConnected`, `HasUniversallyTrivialPushforward` and of the section is routine
> and belongs to whoever proves this, not to the assembly

**That pricing is the bug.** It is 20 lines, it is entirely mechanical, and bundling it into
a research-scale leaf hides it inside the one node nobody can finish. Discharged, the leaf
becomes `exists_relPicOf_of_isAffineBase` — an arbitrary proper smooth geometrically connected
relative curve with a section over an arbitrary affine base — which is *literally* BLR 8.2/1's
hypothesis list, and the assembly is six lines.

**The test, and it is purely syntactic, so run it on every leaf you are dispatched at:** read
the hypotheses and the conclusion and ask whether they are about the SAME morphism. If the
hypotheses name `f` and the conclusion names `pullback.snd f g`, `f ∣_ V`, `f.baseChange g` or
any other derived morphism, the transport between them is a separate obligation. It is almost
always cheap, it belongs OUTSIDE the leaf, and leaving it inside makes the leaf unciteable.

Three mechanical notes that cost time on the way:

* **mathlib's base-change stability is sometimes a `lemma`, not an `instance`.**
  `smoothOfRelativeDimension_isStableUnderBaseChange` is a lemma, so
  `MorphismProperty.pullback_snd` fails with
  `failed to synthesize MorphismProperty.IsStableUnderBaseChangeAlong (@SmoothOfRelativeDimension 1) g`
  — which reads like the fact is missing when it is merely not an instance. `haveI := …` first.
  `IsProper` and `GeometricallyConnected` do have instances.
* **a property defined as `P.universally` needs no stability theorem at all.**
  `HasUniversallyTrivialPushforward f` is `hasTrivialPushforwardProperty.universally f`, and
  `.universally` is stable under base change by construction, so `MorphismProperty.pullback_snd
  (P := …universally)` closes it outright.
* **a section transports by `pullback.lift_snd` and nothing else.** `relSection` of the constant
  section is already the map; the proof obligation is `pullback.lift _ (𝟙 T) _ ≫ pullback.snd = 𝟙 T`.

Corollary for reviewers of a cut: 1 → 1 on the leaf count is a *good* trade when what changes
is that the leaf now matches its citation. Judge a decomposition by whether the remaining leaf
can be handed to someone with the book open, not by the count alone.

**AND THE DEFECT CLUSTERS — WHEN YOU FIND ONE, RUN THE TEST ON EVERY LEAF IN THE FILE.**

(2026-07-31, same file, same day, two more instances found by doing exactly that.)

The syntactic test above costs ten seconds per leaf: *are the hypotheses and the conclusion
about the SAME morphism?* Having applied it once to `exists_relPicOf_isAffineOpen`, applying
it to the file's other seven leaves immediately caught two more —
`isInvertibleSheaf_sectionIdeal` and `nonempty_modPullback_sectionIdeal`, both with hypotheses
on `strX : X ⟶ S` and conclusions about a section of `X ×_S T ⟶ T`. Stacks 0C4S is about a
section of a smooth relative curve; neither leaf was stated about one.

This is not a coincidence, and the reason tells you where else to look: **the mis-shaping is
inherited from the file's central definition.** Everything here is stated relative to a fixed
`strX` because that is what `IsRelPicOf`, `RelPoint` and `RelPicEquiv` are parameterised by, so
a leaf about the base-changed curve gets written with `strX`'s hypotheses out of sheer local
consistency. Any file with one pervasive ambient object will do the same. **So the unit of the
audit is the FILE, not the leaf** — and the transport lemmas you prove for the first instance
are exactly the ones the rest need, which is why instances two and three cost 3 lemmas and 30
lines between them once the first was done.

Three notes from the two extra instances:

* **The hidden hypothesis surfaces as an explicit one, and that is the audit's job to catch.**
  `relSection x` is a section *by construction*, so the old statement never had to say so.
  The citation-shaped statement quantifies over an arbitrary `σ : T ⟶ Y` and therefore MUST
  carry `σ ≫ strY = 𝟙 T` — without it the leaf is false for a silly reason (`σ = 𝟙 Y` makes
  the kernel `0`). Restating always risks dropping such a constructional hypothesis on the
  floor; enumerate what the old form got for free before writing the new one.
* **Cartesianness is the commonest thing a base-change leaf assumes without saying.** The old
  `nonempty_modPullback_sectionIdeal` had "the square is cartesian and the sections match" as a
  docstring *remark* — the prover was expected to re-derive it. Both are now hypotheses of the
  leaf and PROVEN lemmas at the call site (`IsPullback.of_right` for the pasting;
  `pullback.hom_ext` for the section compatibility). A remark that a prover must re-derive is
  an unowned obligation wearing prose.
* **The transport lemmas pay for themselves elsewhere.** `isPullback_curveBaseChangeMap` — that
  `X ×_S T'` really is the pullback of `X ×_S T` along `T' ⟶ T` — was needed here and is also
  precisely the input step 2 of a *different* open leaf's route was asking for. Prove these as
  named lemmas, never inline in a `have`.

