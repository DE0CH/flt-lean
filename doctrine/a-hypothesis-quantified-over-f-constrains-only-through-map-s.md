## A HYPOTHESIS QUANTIFIED OVER `Γ F` CONSTRAINS `Γ ℚ` ONLY THROUGH `map`'s IMAGE — the surjectivity is a SILENT DEBT, and it forces `F = ULift.{u} ℚ`
(2026-08-02, `flt-lean-31`, `det_eq_cycCharModN_of_isStandardLevelModule` in
`Modularity/MoretBailly.lean`.) A recurring shape in this development: a predicate
carries a clause quantified over a base field and its Galois group,
    ∀ (F : Type u) (_ : Field F) (_ : Algebra ℚ F) (σ : Γ F) (v w),
      Λ F (ρ (Field.absoluteGaloisGroup.map (algebraMap ℚ F) σ) v) … = galRoot σ (Λ F v w)
and a leaf reads it as a statement about an ARBITRARY `τ : Γ ℚ`. **It is not one.**
`Field.absoluteGaloisGroup.map f` is built from an arbitrarily chosen embedding of
algebraic closures and carries no functoriality — this file already records that, and
`exists_conj_absoluteGaloisGroup_map_comp` is the up-to-conjugacy substitute — so the
clause constrains `ρ` only on the IMAGE of that map. Getting from there to "for every
`τ`" is a genuine proof obligation that the leaf's own three-step route did not mention
and that no reading of the statement surfaces, because the map is silently applied
inside the clause.
**And the `Type u` indexing decides which `F` you may use.** `Λ` quantifies over
`F : Type u` where `u` is the leaf's own universe variable, so `ℚ : Type 0` does NOT
typecheck as an instantiation; the only admissible copy is `ULift.{u} ℚ`, and then
`algebraMap ℚ (ULift.{u} ℚ)` is a ring ISOMORPHISM. So the debt is exactly:
> `Field.absoluteGaloisGroup.map f` is SURJECTIVE when `f` is bijective.
which is now `surjective_absoluteGaloisGroup_map_of_bijective` in that file, ~45 lines:
`ι := AlgebraicClosure.map f` and `ι' := AlgebraicClosure.map f⁻¹` compose to algebra
endomorphisms of an algebraic closure over its own base (two applications of
`AlgebraicClosure.map_algebraMap`), those are bijective by
`Algebra.IsAlgebraic.algHom_bijective`, hence `ι` is; then `σ := ι ∘ τ ∘ ι⁻¹` is an
`L`-automorphism and `Field.absoluteGaloisGroup.lift_map` plus injectivity of `ι`
identify `map f σ` with `τ`.
**The standing check, and it costs one read of the clause:** when a leaf's conclusion
names an object at `τ : Γ K` and its hypothesis names it at `map g σ`, ask what
`range (map g)` is. If the leaf does not say, the leaf owes it. Same family as the
already-recorded "a datum handed across a seam can only be constrained by what already
saw it", with the seam being a Galois-group comparison rather than a structure field.
Three riders, each of which cost time here:
* **The needed range computation is ALREADY PROVEN in that file, inside a body that
  exports only a corollary.** `normal_range_absoluteGaloisGroup_map` establishes
  `range (map (algebraMap K L)) = Z.fixingSubgroup` as an internal `have` and exports
  only NORMALITY of the range. At `L ≅ K` that internal fact IS the surjectivity, with
  `Z = ⊥`. It was cheaper here to prove the bijective case directly (no `Normal K L`
  instance, no `IntermediateField.fixingSubgroup`), but the general lemma is worth
  hoisting the day a third consumer appears — and the episode is one more instance of
  the standing rule to grep the BODIES of theorems that would have had to know a fact,
  not their statements.
* **`Algebra.IsAlgebraic K (AlgebraicClosure K)` is NOT an instance at this pin** —
  supply `AlgebraicClosure.isAlgebraic K` by hand, or the `algHom_bijective` application
  fails with a bare synthesis error. The torsion-free hypothesis it also wants is
  `Module.IsTorsionFree`, not `IsTorsionFree`; the latter is an unknown identifier and
  `autoImplicit` turns the failure into `Function expected at IsTorsionFree`, which
  reads as a missing import.
* **`algebraMap ℚ (ULift.{u} ℚ)` is bijective by SUBSINGLETONNESS, not by unfolding.**
  `Subsingleton (ℚ →+* A)` for a division ring `A` makes it equal to
  `ULift.ringEquiv.symm` in one `Subsingleton.elim`; trying to compute the instance's
  `algebraMap` directly is a diamond hunt. Note `(ULift.ringEquiv (α := ℚ))` does not
  elaborate — the implicit is named `R`, and the error blames `DFunLike.coe`; a type
  ascription `(ULift.ringEquiv.symm : ℚ ≃+* ULift.{u} ℚ)` is the way to pin it.
### The algebra half: a BALANCED alternating biadditive form factors through `det2`, and `[Finite kI]` is spent exactly once
Same leaf, and the part that generalises to every "the pairing pins the determinant"
node. Biadditive + alternating + `kI`-balanced forces `L v w = φ (det2 v w)` for the
additive character `φ x := L e₀ (x • e₁)`: expand `v = v₀•e₀ + v₁•e₁` biadditively and
the four terms are two diagonal ones (killed), `φ (v₀w₁)`, and `φ (v₁w₀)⁻¹` by
antisymmetry — where antisymmetry `L u z * L z u = 1` is itself just `L (u+z) (u+z) = 1`
expanded.
**The one place finiteness enters is `L u (c • u) = 1`, and it needs a characteristic
split that is easy to miss.** Balancedness plus antisymmetry give `L u (x • u)² = 1`,
which kills every `c` that is twice something — fine in characteristic `≠ 2`. In
characteristic `2` that is vacuous and the alternating law is used instead, via
`L u (a² • u) = L (a•u) (a•u) = 1`, so one needs every element to be a SQUARE, i.e.
finiteness. Over an infinite field of characteristic two the factorisation can fail.
Mathlib's `isSquare_of_charTwo'` wants a `CharP kI 2` instance, which is more work from
a bare `(2 : kI) = 0` than proving surjectivity of `x ↦ x*x` directly: injectivity is
`(a-b)² = a² - 2ab + b² = a² + b²`, i.e. one `linear_combination`, and
`Finite.injective_iff_surjective` finishes.
Accounting note: the leaf closed `−1` with no new leaf (`MoretBailly.lean` 20 → 19
sorried declarations), and the three helpers are consumed by it, so nothing floats.
