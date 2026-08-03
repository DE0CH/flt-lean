## A "∀ T, RelPoint ≃ RelPoint" FIELD **IS** A MORPHISM OF SCHEMES — and the abstraction for it is usually already in the file
(2026-08-01, `flt-lean-59`, the counting half of `MazurTorsion.lean`'s fifth cut.)
Three separate docstrings in that file recorded, correctly, that `IsX0JNeronDatum`
"relates `X'` to the model `XZ` ONLY through the `RelPoint` equivalences
`spX`/`genX`", and one of them added — also correctly — that reading this as *"so
there is no map of underlying spaces to transport a count along"* is a FALSE
obstruction. The escape is Yoneda and it is two lines: `spX` quantifies over ALL
`T : Scheme.{0}`, so instantiate at `T = X'` and feed it the identity.
**What none of the three noticed is that the whole construction was already
written, 6000 lines upstream, as a named abstraction.** `X0.lean` carries
`IsFibreIdent s f f'` — exactly "a natural equivalence of `RelPoint` functors" —
together with `universalPoint`, `apply_eq_comp` (the Yoneda step), `compareIso`
(`A' ≅ A ×_S S'`), `openSection` (the reconstructed open immersion),
`fibreBaseChangeMap`, and `finite_compl_range_fibreBaseChangeMap_special`, which
is the same closed-immersion-plus-`Scheme.Pullback.range_map` argument the
counting half needs. Building `spX` into an `IsFibreIdent` is four lines
(`toEquiv := d.spX; nat := d.spX_nat`) and everything else follows.
**So the standing check, before writing any Yoneda plumbing: grep for a structure
whose FIELDS have the shape of the ones you are about to quantify over.** Here
`grep -n 'RelPoint .* ≃ RelPoint'` over `X0.lean` finds `IsFibreIdent`,
`IsX0CurveModel.spIdent` and `IsX0JOpenModel` in one call. The reason this is
easy to miss is that the abstraction was introduced for a DIFFERENT consumer (the
special fibre of `IsX0CurveModel`) and its docstring never mentions the datum you
are holding — the standing "[missing machinery may be under another heading]"
failure, arriving through a structure rather than a theorem.
**THE ONE STEP THAT REALLY WAS MISSING, and it is worth naming because it is the
shape of every "the given object is the constructed one" obligation.** `X'` and
`Y'` are pinned only as functors, so the GIVEN open immersion `jY' : Y' ⟶ X'` and
the RECONSTRUCTED `IsFibreIdent.openSection` cannot be compared directly. What
compares them is that BOTH are relative points of `strX'` over `strY'`, and the
identification is an `Equiv`, hence INJECTIVE on those. Their images are computed
by `apply_eq_comp` as composition with the universal point, and the datum's own
`spX_j`, read at the tautological point `⟨𝟙 Y', _⟩`, says exactly that those two
composites agree. **Whenever two morphisms into a functorially-pinned object must
be shown equal, do not chase the construction — exhibit both as relative points at
a common base and use injectivity of the pinning equivalence.**
