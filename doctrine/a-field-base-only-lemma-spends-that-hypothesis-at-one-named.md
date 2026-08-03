## A "FIELD BASE ONLY" LEMMA SPENDS THAT HYPOTHESIS AT ONE NAMED POINT — FIND IT, AND YOU HAVE LOCATED THE ARITHMETIC
(2026-08-02, `flt-lean-324`, on `geometricallyConnected_of_isX0NormalProperModel` in
A leaf over a mixed-characteristic base — `Spec ℤ_(ℓ)` here — routinely carries a
docstring saying, correctly, that the `ℚ`-side toolkit "does not apply". That sentence
is true and it is not the end of the analysis. **Open the `ℚ`-side lemma and find where
its proof actually consumes "the base is a field".** In this development it was one
line:
    -- AlgebraicGeometry.denseRange_of_isPullback, CurveCompactification.lean:4080
    haveI : UniversallyOpen y := universallyOpen_of_specField y
Everything else in that proof — the pasting, `range_base_of_isPullback`, the density
chase — is base-agnostic, and `geometricallyConnected_of_isSmoothCompactification` is
three lines over it. So the whole of "compactifying preserves geometric connectedness"
needs only that **the projection of the base-changed curve is an OPEN MAP**.
That single fact then SORTS THE FIBRES for you, and the sorting is the cut:
* over the GENERIC point, `SpecLoc.generic R` is an OPEN IMMERSION
  (`IsReductionBase.isOpenImmersion_generic`) and `Spec L ⟶ Spec ℚ` is universally open,
  so the composite is universally open and the `ℚ`-side argument transfers VERBATIM;
* over the SPECIAL point, `SpecLoc.special toF` is a CLOSED immersion, the step fails,
  and it fails for a reason — a whole component of the special fibre could a priori be
  cuspidal, which is exactly part of what the citation (Igusa) asserts.
**So the docstring's warning was right about the leaf and silent about which HALF of it
is the content.** Locating the one line turns "this is a citation over a DVR" into "the
characteristic-zero half is free bookkeeping and the characteristic-`ℓ` half is the
theorem", which is a cut a successor can act on.
**The mechanical companion: `geometrically P` over a two-point base splits with no
mathematics at all.** Two PROVEN lemmas do it, and both are reusable:
* `SpecLoc.exists_factor_generic_or_special` — every field point of `Spec ℤ_(ℓ)` factors
  through `SpecLoc.generic R` or through `SpecLoc.special toF`. This is the formal
  content of "the base has two points" and it needs **only `IsReductionBase`'s two
  axioms** plus `ker_eq_span_natCast`: a ring map either inverts `ℓ`, and then extends
  along `R ⊆ ℚ` because `ℚ` is the fraction field of every subring of `ℚ`
  (`IsFractionRing.of_field`, `IsLocalization.lift`), or kills `ℓ`, and then factors
  through `R ⧸ ker toF ≅ 𝔽_ℓ` (`Ideal.Quotient.lift` +
  `RingHom.quotientKerEquivOfSurjective`). Injectivity in the first branch is a descent
  on `(ker toF) ^ k` closed by the file's own `eq_zero_of_mem_pow_ker`;
* `geometricallyConnected_of_factor_two` — if every field point factors through one of
  two morphisms and both base changes are geometrically connected, so is the original.
  Pure category theory over an ARBITRARY base: `pullbackLeftPullbackSndIso` plus
  `GeometricallyConnected.connectedSpace_of_subsingleton`.
**AND THE REASON THE DICHOTOMY WAS WRITTEN FROM THE TWO AXIOMS RATHER THAN FROM THE
STANDARD API: DECLARATION ORDER.** `IsReductionBase.isLocalRing`,
`.isLocalization_away` and `.isOpenImmersion_generic` are all declared roughly **9500
lines BELOW** the target, so none of them is usable there — and a scratch module that
`public import`s `X0.lean` CANNOT SEE THIS, because it sees the whole file. Before
writing a proof against a lemma in the same giant module, `grep -n` its line number and
compare with your own. Here that check is what decided the shape of every proof above,
and it is why the generic-fibre half could not simply be closed in place: closing it
needs a hoist of that block, which is a relocation task and was queued as one.
Accounting, in the shape CLAUDE.md asks for: the direct-sorry count went **1 → 2** and
that is DISCLOSURE. The old leaf bundled two independent theorems in two characteristics
behind one `GeometricallyConnected` over a two-point base; what is left is two statements
over a FIELD base, where the whole `ℚ`-side toolkit provably applies and provably did not
before. Judge it by what is LEFT in each leaf.
