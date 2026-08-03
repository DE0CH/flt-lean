## A LOCALIZATION IN THE GOAL AND ITS BASE RING IN THE PROOF CANNOT COEXIST — KEEP THE LOCALIZATION ABSTRACT
(2026-08-01, `flt-lean-190`, closing `exists_isLocalization_tensorProduct_localizationAtPrime`
in `Modularity/AbelianSchemeIsogeny.lean`.)  This development states its localization leaves
over `Localization.AtPrime p` with a hand-built `Algebra A (Localization.AtPrime p) :=
((algebraMap C (Localization.AtPrime p)).comp a).toAlgebra`, and the leaf's own proof must
introduce `Algebra A C := a.toAlgebra` in order to write `A' ⊗[A] C` at all.  **Those two
cannot be in scope together**, and the reason is a mathlib instance nobody thinks about:
> `Localization.AtPrime p` is an `OreLocalization`, and `OreLocalization` carries
> `instSMulOfIsScalarTower : SMul R (X[S⁻¹])` derived from `SMul R X`.  So the moment
> `Algebra A C` exists, `SMul A (Localization.AtPrime p)` resolves to THAT — not to the
> `Algebra A (Localization.AtPrime p)` your goal names.
Measured, in **both** `letI` orders: with `Algebra A C` in scope
`(inferInstance : SMul A (Localization.AtPrime p)) = algALp.toSMul` is not `rfl`; without it,
it is.  A local `letI` does NOT win here, which is the surprising half — so the standing
advice "introduce the instances in the goal's own spelling and they will match" silently
fails.  The symptom is a type mismatch on `IsScalarTower.of_algebraMap_eq` printing
`@IsScalarTower A A' (Localization.AtPrime p') algAA'.toSMul
OreLocalization.instSMulOfIsScalarTower OreLocalization.instSMulOfIsScalarTower` — i.e. the
EXPECTED type, built from your own ascription, already has the wrong instances in it.
**THE ESCAPE, AND IT IS CHEAP: DO THE WORK OVER AN ABSTRACT `D`.**  Move every step that
needs `Algebra A C` into a helper lemma in which the localization is a VARIABLE
`{D : Type u} [CommRing D] [Algebra C D] (M : Submonoid C) [IsLocalization M D]`.  There is
no `OreLocalization` structure on a variable, so `Algebra A D` can only be the instance you
pass, and the helper may introduce `Algebra A C` freely.  Then instantiate `D :=
Localization.AtPrime p` at the call site, where `Algebra A C` is absent.  The helper's
conclusion is then syntactically the consumer's own `A' ⊗[A] Localization.AtPrime p`.
Three riders that make the split work rather than merely relocate the problem:
* **State the helper's `Algebra A D` and `Algebra A A'` as `letI`s in its STATEMENT, in the
  consumer's exact spelling** (`((algebraMap C D).comp a).toAlgebra`), not as instance
  binders.  An instance binder is a variable, and then the tensor product in the helper's
  conclusion is over a different term from the one in the consumer's goal.
* **A hypothesis whose type carries its own `Algebra` instances as `let`s can be passed
  through freely.**  `hpush` here is `letI : Algebra A C := a.toAlgebra; … Function.Bijective
  …`; applying a helper to it triggers NO instance search in the caller, so the caller never
  acquires `Algebra A C`.  That is what makes the whole arrangement possible, and it is worth
  designing leaf statements this way for exactly that reason.
* **Export computation rules, not the object.**  The helper hands back a bare
  `φ : C' →+* (A' ⊗[A] D)` plus `φ (a' u) = u ⊗ₜ 1` and `φ (m c) = 1 ⊗ₜ algebraMap C D c`.
  Those two equations plus a separate `ringHom_ext_of_isPushout` (two ring maps out of a
  pushout agreeing on both legs are equal) are enough for the consumer to build the scalar
  tower `C' → Y → C'_{p'}` that `IsLocalization.isLocalization_of_submonoid_le` demands —
  with no tensor-product induction in the consumer at all.
**The general form, and it is not about localizations:** whenever a proof needs an instance
`Algebra R X` that some FUNCTOR OF `X` in the goal would use to derive a competing instance,
abstract that functor's value.  `OreLocalization`, `Polynomial`, `MvPolynomial`, `Quotient`
and `TensorProduct` all carry such derived-`SMul` instances, and all of them beat a local
`letI` in the same way.
