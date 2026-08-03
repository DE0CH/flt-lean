## AN ALGEBRAICITY STEP THAT ONLY HAS TO MAKE A SUBFIELD BIG ENOUGH IS FREE — ℤ-INTEGRALITY DOES IT
(2026-08-02, `flt-lean-33`, `exists_residueHom_placeAbove` in `Modularity/TateModule.lean`,
closed together with its consumer.) That leaf's docstring listed a four-step classical route.
Steps 1, 3 and 4 are what the proof does. **Step 2 — "the residue field of `placeAbove w` is
ALGEBRAIC over `κ(w)`" — is the only expensive one on the list, and it is not needed.** It is
the step that has to see the finite subextensions of `F̄`, i.e. the valuation theory of every
number field inside `F̄`; nothing else in the leaf is remotely that size.
**What it was there for was SURJECTIVITY of `κ(placeAbove w) ⟶ κ(E)`.** And surjectivity does
not need `κ(E)` algebraic over `κ(w)` — it needs `κ(E)` algebraic over the IMAGE. The image is
a subfield, so it contains ℤ automatically, and `κ(E)` is integral over **ℤ** for free:
`κ(𝒪ᵥ)` is FINITE, hence a finite ℤ-module, and `E := integralClosure 𝒪ᵥ (F_w)ᵃˡᵍ` is integral
over `𝒪ᵥ` by construction. With `κ(placeAbove w)` algebraically closed — step 1 applied to
`placeAbove w` rather than to `E` — mathlib's `IsAlgClosed.ringHom_bijective_of_isIntegral`
closes it. Step 2's own conclusion then comes back for FREE at the end, from integrality of
`E` over `𝒪ᵥ` alone, never from a statement about `placeAbove w`.
**The generalisable rule, and it is worth trying on any leaf whose route contains an
algebraicity or finiteness step: ask what the step is CONSUMED BY.** If the consumer is
"this subfield is large enough to see the whole extension", the base can be dropped all the
way to ℤ, because *a ring homomorphism's image contains ℤ whatever else it contains*. A route
written by a mathematician names the smallest FIELD that works; the smallest RING that works
is usually ℤ and is usually already in hand. Same family as *the crude bound plus a patch*
and *a quantitative statement blocking a leaf is often needed only qualitatively* — the
common shape is that the route's step is stated at the strength its author could see, not at
the strength the consumer asks for.
Three mechanical things from the same proof, each of which cost a round:
* **Prefer the RAW-`RingHom` form of a mathlib lemma when a quotient is involved.**
  `IsAlgClosed.ringHom_bijective_of_isIntegral (f : k →+* K) (hf : f.IsIntegral)` needs no
  algebra instances at all, and that is what made this proof possible: **`Algebra ℤ (R ⧸ I)`
  is a genuine diamond** (`algebraInt` against `Ideal.Quotient.algebra` coming down from
  `Algebra ℤ R`), so the `Algebra.IsIntegral ℤ _` spelling makes `Algebra.IsIntegral.trans`
  fail with `failed to synthesize IsScalarTower ℤ …` **on an instance that is literally in
  context**. `RingHom.IsIntegral.trans` has the same content and no instances — note its `f`
  and `g` are EXPLICIT, so `hf.trans hg` does not elaborate and you must write
  `RingHom.IsIntegral.trans f g hf hg`. `Subsingleton (ℤ →+* R)` then identifies the
  composite with `Int.castRingHom`.
* **A contraction of a maximal ideal is computed from INTEGRALITY, not from locality of the
  map.** `(𝔪_E).under 𝒪ᵥ = 𝔪_{𝒪ᵥ}` is
  `IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)` — two
  lemmas — where proving `algebraMap 𝒪ᵥ E` local by hand is ~30 lines through
  `IsIntegrallyClosed` and `isIntegral_algebraMap_iff`. Look for the integral-extension lemma
  before writing the local-hom one.
* **`IntegralClosure R A` (the project's type synonym, `Deformations/RepresentationTheory/`
  `IntegralClosure.lean`) is DEFEQ to `↥(localValuationSubring v)`**, and the `IsLocalRing`
  instance, the `maximalIdeal` and the `IsAlgClosed` of the residue field all transfer across
  by `rfl`/`exact`. That is what let ONE ring hom serve both the `IsArithFrobAt` side (stated
  about `IntegralClosure`) and the valuation-subring side (stated about `ValuationSubring`),
  with no transport anywhere. **Check for such a defeq before building a comparison map** —
  the two spellings look like different objects and the `rfl` test costs ten seconds. Note
  the `Algebra R _` instances exist only on the `IntegralClosure` spelling, so that is the
  one to state things in.
