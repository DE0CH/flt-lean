## AN OPEN/CLOSED SET DECOMPOSITION IS NOT A CUT — EXTEND THE UNIVERSAL PROPERTY, NOT THE SPACE
(2026-08-02, `flt-lean-99`, closing `exists_extend_atkinLehnerCusps_of_jNeronDatum` in
`FreyCurve/MazurTorsion.lean`.) A leaf asking to EXTEND a morphism `v : U ⟶ U` from a dense
open `U ⊆ X` to `X` is one of the commonest shapes here — a modular curve completed by its
cusps, a Néron model completed by its special fibre, a smooth locus completed by its
boundary. When the tree already carries a description of the COMPLEMENT as a scheme, the cut
that suggests itself is: *act on the complement, then glue*. **Every cut of that shape is
FALSE, and the refutation is one line that needs no geometry at all.**
`X = U ⊔ Z` holds as a decomposition of the underlying SET — which is exactly what a `cover`
field of the form `Set.range ι.base = (Set.range j.base)ᶜ` says — and NOT as one of schemes.
A morphism out of `X` is therefore neither determined by, nor assemblable from, its
restrictions to the two pieces. So a "gluing" leaf taking `(v, action on Z)` and returning
`w` would accept an **arbitrary** `v`, i.e. it is the unpinned form that the extension leaf's
own warning already records as false. Here the tempting cut was along `IsX0JNeronCuspModel`
— `𝒞 = 𝒳 ∖ 𝒴` as a finite étale `ℤ_(q)`-scheme with exactly such a `cover` field, built by
the previous cut one day earlier and sitting 300 lines above the target.
**The tell, and it is checkable before any Lean is written: instantiate your proposed
gluing leaf at a `v` the extension leaf's own ⚠ heading forbids.** If the leaf still
typechecks against its hypotheses, the cut has thrown the pin away. A leaf whose statement
does not mention what pins `v` cannot be a step towards a statement whose truth depends on it.
**THE CUT THAT WORKS EXTENDS THE UNIVERSAL PROPERTY.** The classical construction almost
never compactifies and then checks that the map extends; it builds `X` itself as a moduli
space for a LARGER problem, on which the map is defined for free. Deligne–Rapoport do not
compactify `Y_0(N)`, they construct `X_0(N)` as the coarse space of the `Γ₀(N)`-problem on
GENERALIZED elliptic curves. So state that — the same `structure` shape as the open part's
universal property, with the enlarged problem carried as an abstract functor field plus one
PINNING field tying its classifying map to the open part's along `j` — and the extension
becomes the same three-line descent the open part already runs, plus one use of the OPEN
universal property's UNIQUENESS half to identify `v ≫ j` with `j ≫ w`. Measured here: the
assembly is ~35 lines, entirely formal, and compiled in four scratch iterations.
**AND THE ABSTRACT FUNCTOR FIELD IS NOT JUNK — but you must run the computation that shows
it.** The witness to beat is always the trivial extension (`Deg := the old problem`,
`classify := j ∘ (old classify)`), which satisfies every field except `universal`. It fails
`universal`, and the argument is generic: feed `universal` the OPEN piece with its own
classifying map; the open part's uniqueness half then forces `j ≫ u = 𝟙`, so `j` is a
SECTION of `u`, hence a closed immersion; it is also an open immersion, so its range is
CLOPEN; and connectedness of `X` makes the range `∅` or everything — i.e. `Z = ∅`, where the
leaf is trivial anyway. **Write that paragraph into the structure's docstring**: it is the
whole of what stops the enlarged problem from being decoration, it costs one read, and
without it the next agent has an unpinnable structure and no way to tell.
Two riders from the same run:
* **`Nonempty`-shaped citation leaves in this shape should carry the pinning field, not the
  ⊔-decomposition.** The two descriptions of the same complement are NOT rivals and should
  not be merged: the cuspidal locus as a SCHEME is what a separation/counting argument
  consumes, the cuspidal locus as MODULI is what an extension argument consumes. Say so in
  both docstrings, or a later reader will delete one as a duplicate of the other.
* **Prototype the assembly against the UPSTREAM module, mocking only what is local.** The
  glue here needed `RelPoint`, `relSectionAlong`, `IsCoarseModuliY0` and `Gamma0Datum`, all
  in `ModularCurve/X0.lean`; the only thing from the 70 000-line target file was
  `AtkinLehnerMorphismOver`, four fields, copied verbatim into the scratch. **25 s per
  iteration against ~9 min for `lake env lean` on the real file**, and the text transplanted
  with two changes (the primed names, and the underscores coming off the now-consumed
  hypotheses).
This repository was split out of Deyao's dissertation repo on
2026-07-22 (`git subtree split --prefix=fermat`); the full commit
history of the formalization is preserved. The project root IS the
Lean package (formerly the `fermat/` subfolder).

