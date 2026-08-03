## AN "ABSENT CHAPTER" IN A COST LIST MUST BE CHECKED AGAINST THE **CONCLUSION**, NOT AGAINST THE AUTHOR'S PROOF
(2026-08-02, `flt-lean-29`, on `exists_skolemBallDatum_of_genRelPic` in
`Modularity/MoretBailly.lean`.) A mature leaf here carries a numbered list of the
chapters a prover still owes. Three survey rounds had produced this one and every
clause of it was TRUE when written. Two of the five items were nevertheless the
wrong price, in two DIFFERENT ways, and only one of the two is the familiar
stale-absence failure:
* **Stale-absence, the known shape.** The §3.6 item said *"`𝒪(D)`, `deg` and
  `genus` are not [writable], and `genus` matches zero lines in all of
  `Mathlib/`"*. Both clauses were true — **of `Mathlib/`, which is what the audit
  grepped**. `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveGenus.lean` landed two days
  later with `divisorDegree`, `IsDivisorOn`, `rrSet` (`L(D)`), `ell` (`ℓ(D)`),
  `IsCurveGenus`, `IsCurveGenus.unique` (PROVEN) and the leaf `exists_isCurveGenus`
  — i.e. Riemann's theorem was already an OPEN LEAF WITH CONSUMERS. So §3.6 was not
  a chapter to build; it was a hypothesis to thread, at zero cost in owed theory.
* **THE NEW ONE, and it is not detectable by any grep.** The §3.2 item said the
  symmetric power `X̄^{(d)}` is absent from all three trees. **That is still true and
  it does not matter**, because the leaf's CONCLUSION never mentions a scheme of
  divisors: the parametrisation it hands downstream is by `Fin d → ℚ`, a bare affine
  space. Moret–Bailly needs `X̄^{(d)}` as a SCHEME to say that `φ_d` is a morphism;
  a prover working in DIVISOR/function-field language needs only the coset
  `{f ∈ rrSet D : ord_z f = 0 on Z, f|_Z = α}` inside `X̄.functionField`, and both
  `rrSet` and `Scheme.ord` exist. A chapter of the author's PROOF had been recorded
  as a chapter of the leaf's STATEMENT.
**So the check is two questions per item, and the second is the one nobody asks:**
(i) *re-grep the absence, in `Fermat/` as well as in the pin* — the standing rule;
(ii) **does the leaf's CONCLUSION mention the missing object at all?** If not, ask
what the conclusion actually quantifies over, and price THAT. Here the answer took
a re-pricing from "five missing chapters" to two, and neither of the two is the one
the list opened with.
Corollary for whoever writes such a list: say, per item, whether it is needed to
STATE the residue or only to prove it the way you had in mind. Those decay at
completely different rates.
### `SmoothOfRelativeDimension 1` IS THE PIN'S CURRENCY FOR CURVE THEORY, AND NOTHING PRODUCES IT
Measured the same day and worth knowing before costing any curve leaf:
`CurveGenus.lean`, `CurveDivisorDegree.lean`, `CurveExtension.lean` and
`CurveDimension.lean` all demand `AlgebraicGeometry.SmoothOfRelativeDimension 1`,
and **no theorem in the tree has it as a CONCLUSION from a bare `Smooth f`** —
`grep -rn 'SmoothOfRelativeDimension' Fermat/` returns only producers that already
hold it as a hypothesis or as a structure field. So a development carrying
`Smooth f` plus `topologicalKrullDim ↥X ≤ 1` (which is how `MoretBailly.lean`'s
whole §3.1 chain is stated) is separated from ALL of that machinery by one missing
bridge. It is now the leaf
`smoothOfRelativeDimension_one_of_smooth_of_not_subsingleton`; the non-degeneracy
must be there, since `Spec ℚ` is smooth, integral, of dimension `0 ≤ 1` and of
relative dimension `0`.
### The four-line recipe for `IsIntegral X` / `IsLocallyNoetherian X` over a field
`IsCurveGenus`, `ell` and `rrSet` take both as INSTANCE arguments, so they cannot be
STATED without them, and every consumer hits this first. For `strX : X ⟶ Spec
(CommRingCat.of k)` with `[Smooth strX]` and `[GeometricallyIrreducible strX]`:
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian strX
    haveI : IsReduced X          := isReduced_of_smooth_over_field strX
    haveI : IrreducibleSpace ↥X  := GeometricallyIrreducible.irreducibleSpace_of_subsingleton strX
    haveI : IsIntegral X         := isIntegral_of_irreducibleSpace_of_isReduced X
(`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean` for the second;
the other three are mathlib. `irreducibleSpace_of_subsingleton` is the one to reach
for over a field, because `Spec k` is a one-point space and the general version wants
`IsOpenMap`.) Verified in a 7-second scratch against `MoretBailly.lean`'s own olean.
