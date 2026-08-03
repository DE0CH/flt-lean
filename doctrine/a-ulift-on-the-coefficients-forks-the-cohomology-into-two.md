## A `ULift` ON THE COEFFICIENTS FORKS THE COHOMOLOGY INTO TWO WORLDS WITH NO MAP BETWEEN THEM
(2026-08-02, `flt-lean-248`, closing `card_sha1Twist_le_card_dualNumberDeformationClasses`
in `HardlyRamified/Deformation.lean`.) The standing note
[[flt-cup-product-universe-collapse]] says the categorical cup product forces its three
coefficient modules into one universe, and that the repair is to `ULift` all three. That
is right and it is only half the story. **The `ULift` does not stay local to the pairing.**
`TopRep k G` has morphisms only between objects of ONE module universe, and
`ContinuousCohomology.map` inherits that — its signature is `{X : TopRep k G}`,
`{Y : TopRep k H}` with `f : res φ X ⟶ Y`, so the two representations are in the same
universe by construction. Consequence: once the local objects are `ULift`ed into
`Type (max u v)`, **every global object that is to be localised into them must be
`ULift`ed too**, and any object already stated in `Type v` — here `Sha1Twist`, with 30-odd
consumers and a standing instruction not to rebuild it — is in a cohomology theory that
NOTHING can map into or out of. `max u v = v` is not derivable, so there is no escape by
specialising.
So the shape of the repair is forced, and it is worth knowing before designing a cut:
* build the whole new development in the `ULift`ed world, where the localisation maps are
  constructible by the ordinary `ContinuousCohomology.map` recipe;
* state the crossing ONCE, as a named leaf, as a **cardinality** comparison — an inclusion
  or an isomorphism is not even stateable, the two submodules living in different ambient
  groups;
* and check whether some sibling leaf already owes the same crossing. Here the section
  header on the local Tate pairing already listed "the `ULift` transport" among the
  obligations of `poitouTateExactness_of_localTateDuality`, so naming it turned a
  duplicated hidden obligation into one shared leaf.
**The `N_S`-invariants half is FREE if you take the invariants of the lifted module rather
than lifting the invariants.** `unramTopRep (adZeroTopRepU ρbar) S` and
`unramTopRep (adZeroTopRep ρbar) S` are the two orders; the first keeps everything in one
universe and makes the bridge to the local objects the plain inclusion of invariants, whose
equivariance is **`rfl`** (`unramRep` is a `QuotientGroup.lift` of a `LinearMap.restrict`,
so it computes on `QuotientGroup.mk'`). All four bridge morphisms in this development
compiled first try with `fun _ => ContinuousLinearMap.ext fun _ => rfl`.
### AN ANNIHILATOR DEFINED THROUGH AN EXISTENTIALLY-SUPPLIED ISOMORPHISM SHOULD DROP IT
Same run, and it is the cheapest lesson in it. The local Tate pairing lands in
`H²(ℚ_v, k(1))`, and `IsLocalTateDual` asserts *there exists* a linear equivalence
`inv : H²(ℚ_v, k(1)) ≃ₗ[k] k` making the composite nondegenerate. The obvious definition of
`L^⊥` is `{y | ∀ x ∈ L, inv (pairing x y) = 0}` — and the task prompt for this leaf
prescribed exactly that. **Do not.** It makes the definition depend on a choice extracted
from an existential, hence junk-valued precisely where the existential is an unproven leaf.
It is also unnecessary: `inv` is an EQUIVALENCE, so `inv z = 0 ↔ z = 0`, and the annihilator
of the raw `H²`-valued pairing is the same submodule for every admissible `inv`. Dropping
`inv` made `orthComplU` canonical, removed its dependency on `isLocalTateDual` entirely, and
reduced the submodule proof to `map_zero`/`map_add`/`map_smul`.
**Generalisable: whenever a definition would consume a choice from an existential, ask what
that choice is used for. If it is used only in a slot where it is injective — an
equivalence, a mono, an embedding — the definition does not need it and is better without
it.** The tell is a definition whose docstring has to say "which `inv` is chosen does not
matter": that sentence is a proof that the choice can be deleted, not a reassurance that it
is harmless.
### DERIVE EACH CORRECTION TERM OF A NUMERICAL SIDE CONDITION AND NAME ITS HYPOTHESIS
The Greenberg–Wiles formula turns into the inequality `#H¹_{L^⊥} ≤ #H¹_L` only under a
numerical condition, and getting that condition wrong in a leaf makes the leaf FALSE rather
than merely hard. Three corrections had to be accounted for, and only one of them is
visible in the naive reading:
* the two GLOBAL `H⁰` terms vanish — from absolute irreducibility;
* the finite places outside `S` contribute `1` each — because `#H¹_ur = #H⁰` there, which
  needs `ℓ ∈ S` so that no place outside `S` divides the order of the module;
* **the archimedean place contributes a `−1`, and it is there because `ρbar` is ODD.**
  `H¹(ℝ, ad⁰) = 0` (odd module, group of order two) so the numerator is `1`; but
  `H⁰(ℝ, ad⁰)` is the `+1`-eigenline of the adjoint action of `ρbar(c)`, which is
  one-dimensional exactly when `det ρbar(c) = −1`.
The last is the one to check, and here it came from a STRUCTURE FIELD rather than from a
hypothesis anybody had written: `IsHardlyRamified.det` says `det ρbar` is the cyclotomic
character, and `χ(c) = −1`. **When a side condition has a constant in it, write down which
hypothesis produces that constant** — if the answer is "none", the constant is wrong. And
note the asymmetry that makes this safe to get slightly wrong in one direction only: a
condition STRONGER than necessary leaves the leaf true and merely makes its consumer work
harder, while a WEAKER one makes it false. Err strong, and say in the docstring that you
did and why.
