## A "KERNEL OF A MORPHISM" LEAF IS AN EQUALISER, AND OVER A SEPARATED TARGET THAT IS A CLOSED SUBSCHEME FOR FREE
(2026-08-02, `flt-lean-297`, proving `Fermat.Gamma0Datum.ker_of_geomFibrePt` in
`MazurTorsion.lean`.)  That leaf's docstring prescribed building `ker u` as *"the fibre
product of `u` with the zero section of `d'`"*, which makes the zero section's being a
CLOSED IMMERSION an obligation — a section of a separated morphism, so true, and a real
piece of work at this pin.  It is not needed.  The condition `u(x) = 0` on a relative
point is `x.1 ≫ u = x.1 ≫ (f ≫ ζ)`, i.e. **`x.1` EQUALISES `u` and `f ≫ ζ`**, and
    Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:356
      instance (f g : X ⟶ Y) [Y.IsSeparated] : IsClosedImmersion (Limits.equalizer.ι f g)
hands over the closed immersion with no zero-section theory at all.  `Y.IsSeparated` for
the total space of an abelian scheme over `Spec ℚ` is four lines: `IsProper` extends
`IsSeparated`, `Spec ℚ` is affine hence separated, separatedness composes, and
`terminal.hom_ext` identifies `terminal.from E` with the composite.
**Then BOTH halves of a "these two closed subschemes agree" statement become
FACTORISATIONS THROUGH CLOSED IMMERSIONS**, which is the one shape that descends.  That is
what makes the next section usable, and it is why the equaliser presentation is worth
reaching for even when a fibre product is available: `∃ b, b ≫ κ = a` is a hypothesis of
`IsClosedImmersion.lift`, whereas an EQUALITY of morphisms out of the subscheme is not.
