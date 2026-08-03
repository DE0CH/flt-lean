## A GROUP SCHEME IS BUILT BY YONEDA, NOT BY THE PULLBACK CALCULUS
(2026-07-31, `flt-lean-146`, closing `smooth_schemeTheoreticImage_of_isAdditiveOn`.)
Mathlib's Cartier theorem `AlgebraicGeometry.smooth_of_grpObj` wants `GrpObj (Over.mk f)`,
and the recon for that leaf priced the `GrpObj` as "no mathematics, a lot of plumbing, and
by volume the bulk of the work" — because the obvious construction gives `mul : X ⊗ X ⟶ X`,
`one : 𝟙_ ⟶ X`, `inv : X ⟶ X` and checks five diagrams, each an equation of morphisms out
of an iterated fibre product, in `CartesianMonoidalCategory`'s associator/unitor vocabulary
against this project's `Limits.pullback` one. The recon also prescribed a refactor of the
neighbouring proof to export its three `IsClosedImmersion.lift`s as named declarations.
**None of that was needed.** `CategoryTheory.GrpObj.ofRepresentableBy` builds a group object
in ANY cartesian monoidal category out of a REPRESENTABLE PRESHEAF OF GROUPS. Supply a
functor to `GrpCat` and a `Functor.RepresentableBy`, and every axiom becomes an equation
between ELEMENTS of a type — here `RelPoint bstr g` — with the pullbacks never appearing.
The three morphisms were never written down. Total cost: one general lemma
(`nonempty_grpObj_of_relPointGroup` in `X0.lean`, ~25 lines of proof) plus five two-line
bullets instantiating it.
Three facts that make it work here, all worth knowing before starting:
* **`Over S`'s monoidal structure IS `Limits.pullback`, on the nose.** `tensorObj_left`,
  `lift_left`, `fst_left`, `snd_left`, `toUnit_left` are all `rfl`
  (`Mathlib/CategoryTheory/Monoidal/Cartesian/Over.lean`), and
  `AlgebraicGeometry/Pullbacks.lean:705` registers the instance globally for `Over S` with
  `S : Scheme`. So the "matching two vocabularies" cost the recon feared is zero — but you
  only find that out by reading the file, and the `RepresentableBy` route means you never
  need to.
* **The naturality obligations are exactly two**, `pre_mul` and `pre_one`, because a group
  homomorphism is a `MonoidHom`: nothing has to be said about inversion.
* **`GrpObj` is DATA, so the result is `Nonempty (GrpObj …)`**, discharged by `obtain` at
  the one consumer, whose conclusion is a `Prop`. Do not fight to make it an instance.
**The precedent was already in this repo and was not connected to the leaf.**
`Fermat.nonempty_grpObj_of_yoneda` (`Fermat/FLT/GroupScheme/AffineGroupHopf.lean`) is the
same trick on the affine/Hopf side, and `CyclicSubgroupOfOrder.exists_hopfAlgebra_geomFibre`'s
docstring records it being chosen there on 2026-07-28 over "transport a `GrpObj` along an
equivalence", with the reason spelled out: *"it is enough to give a functorial group
structure on the points, with no monoidal functor anywhere."* The generalisation to
`Over SpecQ` is mechanical, and three days passed without anybody making it.
So: **when a leaf asks for a group/monoid/ring object in a cartesian monoidal category,
look for `ofRepresentableBy` before writing a single morphism.** `MonObj`, `IsCommMonObj`,
`GrpObj` and `CommGrpObj` all have one, in `Mathlib/CategoryTheory/Monoidal/Cartesian/`.
The general form of the lesson: *a functor-of-points presentation and a
morphisms-and-diagrams presentation are Yoneda-equivalent, and mathlib carries the bridge —
so pick whichever side the data is already on, and never pay to cross.* This development's
group laws are primitively functor-of-points data (`AbelianSchemeStruct`), so the crossing
was never necessary in the first place.
