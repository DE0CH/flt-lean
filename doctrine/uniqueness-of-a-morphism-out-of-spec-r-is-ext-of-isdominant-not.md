## UNIQUENESS OF A MORPHISM OUT OF `Spec R` IS `ext_of_isDominant`, NOT THE VALUATIVE CRITERION
(2026-08-02, `flt-lean-48`, cutting `exists_compl_pair_sexticThirtySeven` in
`FreyCurve/MazurTorsion.lean`.)  Half the geometry in this development is of the shape
*"two morphisms `Spec R ⟶ X` that agree on `Spec (Frac R)` are equal"* — it is what
identifies a point of `X` with its local ring, and it is the step every "which points
are in this chart" argument runs on.  The reflex is to reach for
`AlgebraicGeometry.IsSeparated.valuativeCriterion` and build a `ValuativeCommSq`, because
the statement *sounds* like the uniqueness half of the valuative criterion and mathlib
files it under that name.
**Do not.  The fact needs no valuation ring at all**, and mathlib already has it in the
form that costs three lines:
    AlgebraicGeometry.ext_of_isDominant [IsReduced Y] {f g : Y ⟶ Z} [Z.IsSeparated]
      (ι : W ⟶ Y) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g
with `Y := Spec R`, `ι := Spec.map (algebraMap R (Frac R))`.  What it consumes is
REDUCEDNESS of the source, DOMINANCE of `ι`, and separatedness of the target — and `R`
being a domain gives the first two for free.  `ValuativeCriterion.Uniqueness` is the same
fact specialised to a valuation ring; the valuative criterion's content is EXISTENCE, and
paying for the `ValuativeCommSq` buys a hypothesis (`ValuationRing R`) the argument never
looks at.  Measured here: the `ValuativeCommSq` version was ~15 lines plus a
`Subsingleton.elim` on `LiftStruct` that only typechecks if the two lift structures are
built INLINE (a `have` on them destroys the defeq — the standing `have`-on-data trap), and
`ext_of_isDominant` replaced it with one `refine`.
Three companion facts, all cheap and all needed every time:
* **`IsDominant (Spec.map (algebraMap R (Frac R)))`** is not an instance and is eight
  lines: the image of the unique point is `⊥` (`Ideal.comap_bot_of_injective` plus
  `IsFractionRing.injective`), and `PrimeSpectrum.closure_singleton` makes `closure {⊥}`
  the whole space.
* **`X.IsSeparated` from `IsSeparated strX` for `strX : X ⟶ Spec (CommRingCat.of K)`** is
  `rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from strX]; infer_instance` — the
  affine base is separated over the terminal object, and `IsSeparated` is multiplicative.
* **`Spec.map (algebraMap (X.presheaf.stalk z) X.functionField) ≫ X.fromSpecStalk z =
  X.fromSpecStalk (genericPoint X)`** is `Scheme.SpecMap_stalkSpecializes_fromSpecStalk`
  plus one `congr 1`: the algebra instance `stalkFunctionFieldAlgebra` IS
  `stalkSpecializes` along `η ⤳ z`, so the two morphisms are defeq but not syntactically
  equal and `rw` will not close the last step on its own.
**AND PASS THE DOMINANCE AS AN EXPLICIT ARGUMENT.**  A `haveI` supplying
`IsDominant (Spec.map (CommRingCat.ofHom (algebraMap …)))` at the use site is NOT found by
instance search, although it prints identically to the goal — the two elaborations pick the
`Algebra` instance up by different routes and are defeq but not syntactically equal.  Wrap
`ext_of_isDominant` in a three-line lemma taking the dominance explicitly; an explicit
argument is checked up to defeq and goes through.  Same family as the standing
"failed to synthesize `C X`, where `X` prints identically to something you are holding".
Corollary about how to CUT such a leaf: with those two general lemmas proven, a
"how many points are outside this affine chart" leaf splits into a BOOKKEEPING half (the
chart's coordinates as elements of the function field, and that the chart is exactly where
they are regular) and an ARITHMETIC half (how many valuation subrings of the function field
omit a given element).  Neither half mentions the other's vocabulary, and the arithmetic
half mentions no scheme at all.  Prefer that seam to building the second chart of a
hyperelliptic gluing as a scheme: the gluing route needs the second chart's integrality and
smoothness as two further leaves, the overlap isomorphism, and the extension theorem — and
it still needs the valuative argument at the end to show the two charts COVER.
