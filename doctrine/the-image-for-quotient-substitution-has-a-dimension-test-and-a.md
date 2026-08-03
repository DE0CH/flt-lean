## THE IMAGE-FOR-QUOTIENT SUBSTITUTION HAS A DIMENSION TEST AND A DIRECTION TEST
(2026-07-31, from a sweep of every `X0.lean` leaf carrying a "what proving it needs"
paragraph.) Two leaves in that file closed because a docstring's expensive QUOTIENT was
satisfied by a cheap IMAGE that was already in the file — `exists_involutionSignSplitting`
(`Im(1 ± ι)` in place of `A / B^∓` and fppf descent) and `exists_abelianImage_of_isAdditiveOn`
(the image-not-kernel cut in place of Poincaré reducibility). Sweeping the **13 remaining**
such leaves for the same move found **no further instance**, and the two tests that decide it
are worth writing down, because each is checkable in a minute against the conclusion alone —
before any reading of the prose above it.
* **DIMENSION.** The subobject being divided out must be POSITIVE-DIMENSIONAL. `A / B` for an
  abelian subscheme `B ⊆ A` is isogenous to a complementary abelian SUBscheme of `A`
  (Poincaré reducibility), which is the image of a morphism out of `A` — so an image can stand
  in for it. `E / C` for a FINITE subgroup `C` cannot: it has the SAME dimension as `E`, is
  isogenous to no proper subobject, and the isogeny `E ⟶ E/C` is split by nothing, so there is
  no ambient object in which to take an image. That is why `exists_isNIsogenyPair`'s "quotients
  of an elliptic scheme by a finite flat subgroup scheme" is a claim about the STATEMENT and
  should be believed, while the involution leaf's was not.
* **DIRECTION.** The conclusion must want maps only FROM the ambient object. An image receives
  maps from `J` and never into it — which is the known-negative already recorded on
  `exists_finiteKernelComplement_of_surjective_isAdditiveOn`.
* **AND THERE MUST BE AN AMBIENT AT ALL.** `exists_x0IntegralCompactifiedModel` fails a third,
  cruder way: the object it is missing is the scheme `XZ` itself, so there is nothing to take
  an image inside of. A leaf whose conclusion is "this scheme exists" is never a substitution
  candidate; one whose conclusion is "this map out of a scheme I have exists" often is.
A leaf failing any of the three is genuinely blocked and its "what proving it needs" line is
honest. Record the audit ON THE LEAF when you run it — all 13 now carry an
`IMAGE-SUBSTITUTION AUDIT, 2026-07-31` block naming which test it fails — because the cost
of this sweep is entirely in the re-reading, and nothing else stops the next agent repeating it.
**Corollary, and it generalises past this substitution: a docstring's prescribed refuting
`grep` is usually scoped too NARROWLY, and re-running it WIDER is the cheapest audit there is.**
`exists_ramificationSet_geomPtField` told a successor to check
`Fermat/FLT/Modularity/{AbelianSchemeIsogeny,AbelianScheme}.lean` for its missing
Néron–Ogg–Shafarevich input. Run there it confirms the absence — and it is looking in the wrong
place: `AbelianSchemeIsogeny.lean`'s `Unramified` hits are all `FormallyUnramified` of a
MORPHISM and `AbelianScheme.lean`'s `Néron` hits are Néron–SEVERI, while the actual home,
`Fermat/FLT/Mathlib/AlgebraicGeometry/NeronModel.lean` (`IsGoodReductionModel`,
`exists_goodReductionModel_of_surjective`, `exists_neronExtension`, all PROVEN), is named
nowhere in that docstring. The verdict survived; the ROUTE did not.
