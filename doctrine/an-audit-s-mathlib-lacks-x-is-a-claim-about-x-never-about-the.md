## AN AUDIT'S "MATHLIB LACKS X" IS A CLAIM ABOUT X, NEVER ABOUT THE OBLIGATION
(2026-07-31, `hasDoubleCoverOfAffineLine_of_iso_sectionIdeal`, the `g¹₂`.) Three
successive audits — the consumer's and two on the declaration itself — costed that
leaf's `IsFinite φ` clause at Riemann–Roch, recording that "mathlib at this pin has no
coherent cohomology of sheaves on schemes, no `LinearSystem`, no `gonality`, no genus,
no degree of a divisor". **Every one of those absences is real, and none of them is
needed.** Finiteness of `φ : U ⟶ 𝔸¹` from a dense open of a proper curve is
    IsFinite = IsProper ⊓ LocallyQuasiFinite
which is `IsFinite.of_isProper_of_locallyQuasiFinite` in
`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` — **this pin HAS Zariski's Main
Theorem** — plus four cancellation lemmas and `UniversallyClosed.of_valuativeCriterion`.
Proven sorry-free in `Fermat/FLT/Mathlib/AlgebraicGeometry/AffineLineExtension.lean`;
the leaf went from open to proven over one strictly weaker successor, net zero sorries.
The audits searched the axis a `ℙ¹`/pencil route needs (`h⁰`, linear systems, degree)
and reported truthfully on it. An obligation phrased AFFINELY runs on a different axis.
**Three agreeing audits are not three confirmations when all three searched the same
axis** — the same shape as the "three agents confirmed it independently" trap recorded
above for stale oleans.
So: when a docstring prices a clause at a missing theory, do not price the theory.
Restate the clause as a property of the MORPHISM or OBJECT and grep mathlib for that
property's characterisation lemmas — `*_iff_*`, `.of_*`, `eq_*_inf_*`.
`MorphismProperty` inf-decompositions (`IsFinite.eq_proper_inf_locallyQuasiFinite`,
`IsIntegralHom.iff_universallyClosed_and_isAffineHom`, `IsProper.eq_valuativeCriterion`,
`IsSeparated.eq_valuativeCriterion`) are where the cheap routes live, and a search for
the mathematical NOUN cannot see them.
Tactical corollary, because it blocked the proof for three iterations: `ValuativeCommSq`
is a bundled structure, and a lift obtained from
`(ValuativeCriterion f ⟨R, K, i₁, i₂, ⟨w⟩⟩).some.default` carries
`{R := sq.R, commRing := …, …}.R` in its type. That is DEFEQ to `sq.R` but not
syntactically equal, so every subsequent `rw` fails with a pattern that prints as a
half-page structure literal. **Unbundle once** — state the two halves with `R`, `K` as
ordinary binders (`exists_lift_of_isProper`, `eq_of_isSeparated_of_lift`) and discharge
them by `exact`, which sees through proj-reduction — and everything downstream goes
through with plain rewrites.
