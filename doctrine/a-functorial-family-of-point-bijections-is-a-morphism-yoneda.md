## A FUNCTORIAL FAMILY OF POINT-BIJECTIONS **IS** A MORPHISM — Yoneda, and it deletes a model

(2026-07-31, `flt-lean-307`, `exists_isCusp_ne_neronGenAut_of_atkinLehnerPin` in
`MazurTorsion.lean`.)  This development carries several structures whose fields are
*identifications of relative points* rather than morphisms of schemes —
`IsX0JNeronDatum.genX/genY/spX/spY`, `IsX0ReductionAt.redX`, and the `Equiv`-valued
fields of their siblings — always with a docstring explaining that the object "does not
exist at this pin", so the identification is presented on points.  Those docstrings are
right about the FIELD and are routinely over-read into a claim about the CONTENT, and
the over-reading is expensive: it makes every consumer look like it has to keep the whole
model in its statement.

**Check whether NATURALITY is also a field.**  `genX` comes with `genX_nat`, so the
family `T ↦ (X(T) ≃ 𝒳(T))` is an isomorphism of FUNCTORS on schemes over `ℚ`, and Yoneda
turns it into a morphism with two lines of tactic:

    obtain ⟨vR, hvR⟩ : ∃ vR : RelPoint strX strX,
        d.genX strX (strX ≫ SpecLoc.generic R) rfl vR
          = RelPoint.post w hw (d.genX strX (strX ≫ SpecLoc.generic R) rfl ⟨𝟙 X, _⟩) :=
      ⟨(d.genX strX (strX ≫ SpecLoc.generic R) rfl).symm _, Equiv.apply_symm_apply _ _⟩

— evaluate at the object itself, on the tautological point `𝟙 X`.  `genX_nat` then gives
`neronGenAut d w hw = RelPoint.post vR.1 vR.2` at *every* base point, and `genX_j` plus
`post_relSectionAlong_of_comm` give the compatibility with the open immersion.  No
properness, no density, no valuative criterion: it is naturality and
`Equiv.apply_symm_apply` throughout, ~60 lines.

What that bought here: the leaf's own docstring had (correctly) refuted the tempting cut
to "an abstract involution `σ` of `X(ℚ)`" — `hX.IsCusp` is *by definition* "not in the
image of `Y(ℚ)`", so `σ :=` the moduli action on the image together with the IDENTITY on
the cusps satisfies every hypothesis while fixing every cusp — and concluded *"so the
model may not be dropped"*.  The conclusion does not follow.  The counterexample is
killed by `σ` being a MORPHISM (`Y` dense, `X` separated ⟹ unique extension), not by the
model; and the morphism is available.  So the residue is now
`exists_isCusp_ne_post_of_atkinLehnerPin`, Atkin–Lehner (1970) §2 over `hc`, `hX`, `al`
and a bare `v : X ⟶ X` — **`q`, `R`, `toF`, `X'`, `Y'`, `hX'`, `hj`, `d`, `YZ`, `XZ`,
`ystr`, `xstr`, `jZ`, `w`, `w_𝒴`, `hcomm`, `hinv` and `hgen` all gone**, leaf count 1 → 1.

The generalisable question, and it is cheap: **when a docstring says "this is only a map
of points, so the ambient apparatus is load-bearing", ask what makes the junk witness junk
— then ask whether that property, rather than the apparatus, can be a hypothesis.**  Here
the answer was one binder (`hvj : hX.j ≫ v = wYQ ≫ hX.j`) replacing eighteen.

