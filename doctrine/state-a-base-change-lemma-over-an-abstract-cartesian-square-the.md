## STATE A BASE-CHANGE LEMMA OVER AN **ABSTRACT CARTESIAN SQUARE** — the "transport along an iso" twin is then the `𝟙` instance, free

(2026-07-31, `flt-lean-260`, `ModularCurve/RelativePicard.lean`.)  A leaf's route
named TWO sublemmas as owed — *`IsRelPicOf` is stable under base change of the base*
and *`IsRelPicOf` transports along an isomorphism of representing objects over the
base* — and priced them as "both routine".  They are **one lemma**, and seeing that
before writing either saved the second.

The move is to state the base-change lemma with `IsPullback` hypotheses instead of
with mathlib's chosen `pullback`:

    theorem IsRelPicOf.ofIsPullback (hP : IsRelPicOf strX pstr)
        (hX  : IsPullback φ strX' strX h)      -- the CURVE is base-changed
        (hPb : IsPullback ψ pstr' pstr h) :    -- the REPRESENTING OBJECT is too
        IsRelPicOf strX' pstr'

Then `h := 𝟙 S`, `φ := 𝟙 X`, `ψ := e.hom` gives transport along an isomorphism, because
an iso IS a pullback along the identity — `IsPullback.of_id_fst` and
`IsPullback.of_horiz_isIso` supply the two squares, and the corollary is three lines.
Three payoffs, and the second is the one that is easy to miss:

* **the consumer's square is usually a PASTING, not a chosen pullback.**  Here the
  curve side is `X ×_S U = (X ×_S V) ×_V U`, which the tree already had as an
  `IsPullback` (`isPullback_curveBaseChangeMap`); in `pullback` form every use would
  have paid a transport;
* **the internal isomorphism comes out canonical and pinned.**  `IsPullback.isoPullback`
  of the pasted square is THE map into a pullback, so `isoPullback_hom_fst`/`_hom_snd`
  determine it, and every later identity about it — naturality in the test object,
  and the cocycle a gluing needs — is one `pullback.hom_ext`;
* **no `pullback.map`/`pullbackLeftPullbackSndIso` juggling appears anywhere.**

For a structure whose fields quantify over relative points, the recipe that made all
five fields go through first try: a point bijection `RelPoint pstr' k ≃ RelPoint pstr (k ≫ h)`
(compose with `ψ` one way, `hPb.lift` the other), a curve comparison
`curveBaseChange strX' k ≅ curveBaseChange strX (k ≫ h)` (paste, then `isoPullback`),
and ONE generalised transport lemma for the file's equivalence relation, stated for an
arbitrary morphism of base-changed curves lying over an arbitrary morphism of bases.
That last generalisation is worth taking even when you only need the `u = 𝟙` case:
`relPicEquiv_modPullback` already existed for `curveBaseChangeMap`, and its proof never
used anything about `curveBaseChangeMap` except one commuting square, so generalising it
cost a copy-paste and made the iso case an instance rather than a rival development.

**And the cost that remains after all this is BOOKKEEPING, not mathematics — say so.**
The residual leaf here is the functoriality of `U ↦ P_U`, and every identity in it is a
`pullback.hom_ext`; what makes it large is that `curveBaseChange strX g` for
propositionally-equal `g` are propositionally and not definitionally equal SCHEMES, so a
cocycle across three opens is a pile of `eqToIso`.  A route note that says "functoriality
is FORCED rather than checked" is right about the mathematics and silent about that, which
is how the leaf came to be priced as small.

