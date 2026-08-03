## AN "INERT HYPOTHESIS" CLAIM IS A CLAIM ABOUT A GENERAL THEOREM — CHECK THAT THEOREM'S ARCHIMEDEAN SIDE CONDITIONS
(2026-08-01, `flt-lean-165`, `exists_artinIdealMap_of_unramifiedAbelian_normal` in
`Modularity/Interface.lean`.)  A leaf carrying an unused-looking hypothesis often gets a
docstring paragraph declaring it INERT, with a reason of the form *"the theorem holds over
an arbitrary <base>, so a prover may prove the general statement and specialise"*.  That
paragraph is doing two jobs — telling you the hypothesis is free, and telling you the
general statement is TRUE — and the second is the one to check.
Here the paragraph read *"`IsCyclotomicExtension {p} ℚ CF` is INERT here and may be
ignored: Artin reciprocity holds over an arbitrary number field"*.  **The general statement
is FALSE.**  Artin reciprocity AT MODULUS `1` needs the extension unramified at the INFINITE
places too; without that the Artin map kills only the TOTALLY POSITIVE principal ideals and
factors through the NARROW class group.  Witness: `K` real quadratic with `Cl ≅ ℤ/2`,
`Cl⁺ ≅ (ℤ/2)²`, `Cl⁺ = ⟨s,t⟩`, `⟨t⟩ = ker(Cl⁺ ↠ Cl)`, and `M` the class field of `⟨s⟩` —
abelian, unramified at every FINITE prime, `#Gal(M/K) = 2 = h_K`, so every stated hypothesis
holds, while primes of narrow classes `1` and `s` share a Frobenius and differ in `Cl`.
What rescued the leaf is exactly the "inert" hypothesis: `ℚ(ζ_p)` is TOTALLY COMPLEX for odd
`p`, so no infinite place can ramify, and at `p = 2` it is `ℚ`, where `h = 1` is odd and
`IsUnramifiedAtInfinitePlaces_of_odd_card_aut` applies.
**The generalisable check, and it is one question: does the general theorem you are being
told to prove have a side condition at the places/primes/degenerate objects your special
case makes vacuous?**  Archimedean conditions are the commonest instance in number theory
precisely because they are invisible in the finite-prime vocabulary a leaf is written in —
`hunr` here quantifies over `Ideal (𝓞 M)` and cannot mention an infinite place at all.  Ray
class groups, narrow class numbers, signs of units, real vs complex embeddings: if the leaf
is about class groups and says nothing about `∞`, ask which class group its conclusion is
really about.
Two riders from the same run.
* **A "mathlib survey" that is correct about the PIN can be badly stale about the TREE.**
  That leaf's survey said "the Artin map, the Artin symbol, ray class groups and reciprocity
  are ALL absent from the pin and from `~/cs/FLT`" — still true, and irrelevant: this project
  had grown `Fermat/FLT/NumberField/{ArtinSymbol,UnramifiedClassFieldBound,`
  `UnramifiedClassFieldExistence,HilbertClassFieldNormal}.lean`, with
  `exists_hilbertClassField_artinIso` PROVEN, and `Interface.lean` already `public import`s
  three of the four.  **Grep your own module's import block before believing an absence
  claim** — the machinery may be not merely in the tree but already in your cone.
* **The whole node then cost ~330 lines and no new mathematics.**  It is now PROVEN over
  `ArtinSymbol.lean`'s two existing leaves (RECIPROCITY, CHEBOTAREV) and nothing else.  The
  three things that were actually missing were plumbing: the `jj : CF →ₐ[ℚ] M` model against
  the honest `Algebra CF M` in which `frobAt` is stated, the inertia-to-`IsUnramifiedAt`
  converse at an abstract base, and `inertiaDeg_eq_one_of_forall_pow_natCard` read in
  residue-CARDINALITY form (which is what `IsArithFrobAt` consumes — it mentions the base
  only through the exponent `Nat.card (𝓞 k ⧸ q.under (𝓞 k))`).
### `IsGalois F E` IS NOT SYNTHESISED FROM `Normal F E` PLUS `Algebra.IsSeparable F E`
Measured, and it costs a cycle: with `[FiniteDimensional ℚ M] [Normal ℚ M]` in scope,
`Algebra.IsSeparable ℚ M` synthesises (char zero) and `IsGalois ℚ M` does **not** — mathlib
has no instance assembling the two.  `haveI : IsGalois ℚ M := ⟨⟩` is the fix and it is
needed surprisingly often, because `IsArithFrobAt (𝓞 K) σ Q` for `σ : Gal(L/K)` needs
`SMulCommClass Gal(L/K) (𝓞 K) (𝓞 L)`, which is found only under `[IsGalois K L]`.
### A SCRATCH THAT IMPORTS THE TARGET MODULE IS THE FASTEST *AND* MOST FAITHFUL LOOP HERE
`Interface.lean` needs ~40 minutes to build and its `.olean` loads in **6 seconds**.  So a
scratch that `public import`s `Fermat.FLT.Modularity.Interface` plus your new module, and
restates the target under a primed name, tests the real instance environment — which a
minimal-import scratch does not.  Two concrete instances differed here: `NumberField ↥M` for
`M : IntermediateField ℚ ℚ̄` with `[FiniteDimensional ℚ M]` is NOT synthesisable from
mathlib alone but IS in `Interface.lean`'s cone, and so is the `SMulCommClass` above.  The
right response is to supply them at the CALL SITE with `haveI` rather than to widen the new
module's import block — a new upstream module should stay small.
Best of all, EXTRACT the finished text from the real file (`sed` the line range, rename the
declaration) rather than keeping a hand-typed parallel copy: what you verify is then the
same characters you commit.
