## A ROUTE NOTE THAT NAMES A CLASSICAL THEORY IS A MATHLIB QUERY, NOT A WORK ORDER
(2026-07-31, closing `exists_isIso_of_liesIn_specPt_iff` in `X0.lean`.)  The leaf's
own route said its content was "Cartier / Galois theory of étale algebras", and the
three docstrings that owed it all repeated some form of that phrase.  It reads as a
theory to build.  It is **one mathlib declaration**:
`Algebra.FormallyEtale.equivPiOfIsSepClosed`, giving `A ≃ₐ[K] (PrimeSpectrum A → K)`
from `[EssFiniteType K A] [FormallyEtale K A] [IsSepClosed K]`, in
`Mathlib/RingTheory/Etale/Field.lean`.  The whole leaf came to ~60 lines, of which
the only mathematics is that citation; the rest is translation between the scheme
statement and the algebra statement.
**Why no ordinary search finds it: mathlib does not use the theory's name.**
`grep -ri cartier Mathlib/` does not reach that file.  Neither does "Galois category",
"étale algebra", or any other name a textbook would use for the result.  What finds it
in seconds is the **conclusion's SHAPE** — `ls Mathlib/RingTheory/Etale/`, then the
declaration list of `Field.lean`.  So when an audit names a theory, grep for the
STATEMENT you want (`≃ₐ`, `Π i, `, `IsSepClosed`, `PrimeSpectrum`), and grep the
DIRECTORY the theory would live in, before costing any work off the audit's verdict.
Companion translations, all one-liners, all easy to think are missing: `IsFinite`
extends `IsAffineHom`, so `isAffine_of_isAffineHom` makes the source affine;
`Spec` is fully faithful, so `Spec.preimage`/`Spec.map_preimage` turn any morphism
into a ring map with no `Γ`/`appTop` naturality bookkeeping; and a
`HasRingHomProperty` class transfers between the two worlds by
`HasRingHomProperty.Spec_iff` (`Etale`) or the property's own `SpecMap_iff`
(`IsFinite`).  Those four are the standard scheme-to-algebra bridge in this pin.
