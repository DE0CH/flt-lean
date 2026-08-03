## "TWO MORPHISMS AGREEING ON GEOMETRIC POINTS ARE EQUAL" IS TWO MATHLIB LEMMAS — AND NEITHER IS FINDABLE BY GREPPING FOR RIGIDITY
(2026-08-02, `flt-lean-79`, closing `Fermat.Gamma0Datum.hom_ext_of_geomFibrePt` in
`FreyCurve/MazurTorsion.lean` — a leaf whose docstring correctly called it "the standard
reduced-source, dense-closed-points argument" and which nobody had tried.)
That shape recurs all over this development: a point-level identity has to become an
identity of MORPHISMS, because the structure fields (`IsNIsogenyPair`'s `[N]` conditions,
`IsAdditiveOn`, the `dual_map`/`map_dual` clauses) are stated as equations of morphisms.
The pin proves it, in a file nobody greps:
    Mathlib/AlgebraicGeometry/Morphisms/Separated.lean
      ext_of_isDominant_of_isSeparated   -- [IsReduced X], separated `s`, dominant `ι`
      ext_of_fromSpecResidueField_eq     -- ... agreeing after `X.fromSpecResidueField x`
                                         --     for `x` in a DENSE set
    Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean
      residueFieldIsoBase, pointOfClosedPoint, pointEquivClosedPoint, ext_of_apply_eq
                                         -- closed points <-> K-points, K alg closed
**Why no ordinary search finds them.** The mathematician's words for this — "rigidity",
"geometric points", "dense", "Jacobson", "separating family" — appear in NONE of those
declaration names. `grep -rn 'geometric points' Fermat/` returns forty docstrings and no
lemma. What found them was grepping `Morphisms/Separated.lean` itself for `IsDominant`,
i.e. **guessing the FILE from the hypothesis (`separated`) rather than the conclusion.**
Same failure family as [Mathlib states point facts as morphism properties]: the library
indexes by the `MorphismProperty` being consumed, not by the theorem's informal name.
**And the docstring's prescribed route was the expensive one, in a way worth recognising.**
It said: base-change everything to `ℚ̄`, run the argument there, descend by faithful
flatness of `ℚ → ℚ̄`. That is correct mathematics and costs the pullback `d.E ×_ℚ ℚ̄`, its
GEOMETRIC reducedness (strictly more than reducedness), and an epi to descend along.
`ext_of_fromSpecResidueField_eq` is stated with `X.fromSpecResidueField x`, so it runs
**directly over `ℚ`** and none of that is built. Generalisable: **when a route says "base
change to the algebraic closure, then descend", check first whether the residue-field form
of the same theorem lets you stay downstairs.** Passing to `ℚ̄` is what a human does to
make the points visible; the residue field is what a formal statement already has.
The four side conditions were all one-liners already in the tree, which is the real
measure of how close this leaf was: `isReduced_of_smooth_over_field d.f` (from
`d.ab.smooth`), `IsSeparated d'.f` by `inferInstance` from `d'.ab.proper`,
`LocallyOfFiniteType.jacobsonSpace d.f` plus `closure_closedPoints` for density, and
`hu.trans hv.symm` for agreement over the base.
**The one step with content is CLOSED POINT ⟶ GEOMETRIC POINT, and the recipe is
reusable verbatim.** At a closed `x`, `X.fromSpecResidueField x ≫ f` is FINITE — by
`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace` over
`isClosed_singleton_iff_isClosedImmersion`, which is mathlib's own proof of
`residueFieldIsoBase` — so `κ(x)` is a finite `ℚ`-algebra and embeds in `ℚ̄`. Then
`Spec.map φ ≫ X.fromSpecResidueField x` is the geometric point, its base compatibility is
FREE by `subsingleton_hom_specQ`, and `epi_specMap_of_fieldHom φ` (`X0.lean`: `Spec` of a
map of FIELDS is an epi, being faithfully flat) cancels `Spec.map φ` back off. Total: ~20
lines over names that were all already upstream.
**The `Rat`-algebra diamond bites here and the dodge is one binder.** The embedding step
wants `Module.Finite ℚ κ(x)` for the algebra structure coming from `d.f` — but
`DivisionRing.toRatAlgebra` is a global instance and wins, so at the literal `ℚ` the
finiteness refers to the wrong `Algebra ℚ κ(x)`. State the helper over a VARIABLE base
field (`Fermat.exists_ringHom_algebraicClosure_of_finite`, added beside the leaf), where
the `letI : Algebra F L := ψ.toAlgebra` is the only instance in scope and no diamond can
form. Its STATEMENT mentions only bare `RingHom`s, so instantiating at `ℚ` is safe. This
is the same device, for the same reason, as `X0.lean`'s already-present
`exists_ringHom_algebraicClosure` — which is the OTHER direction and does not apply.
**Cost, for calibration**: 6–10 s per scratch round against `MazurTorsion.olean`, the
whole proof green on the first full attempt, one `lake build` of the module at the end
(5307 jobs, all but one replayed from `~/.flt-release-lake`). The audit that matters is
`#print axioms` FROM THE SCRATCH with a known-sorried CONTROL from the same file — 10 s,
and it separates "proven" from "the traversal found nothing".
