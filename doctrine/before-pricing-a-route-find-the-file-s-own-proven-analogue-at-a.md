## BEFORE PRICING A ROUTE, FIND THE FILE'S OWN **PROVEN ANALOGUE AT A DIFFERENT PARAMETER** — ITS DOCSTRING LISTS THE INGREDIENTS
(2026-08-02, `flt-lean-231`, scoping the dim-`1` degeneration of
`isTorsion_factor_of_heckeIsotypic` in `ModularCurve/X0.lean`.)  I wrote a price into
that leaf's docstring — "the genus-one route still needs
`SmoothOfRelativeDimension 1 jstr`, which `AbelianSchemeStruct` does not carry and
which `x0Genus N = 1` does not supply; tying it to `dim J` is Abel–Jacobi in degree
`1`" — and had to correct it **in the same session**.  Every clause about
`AbelianSchemeStruct` was true.  The conclusion was false, because
`smoothOfRelativeDimension_one_of_x0Genus_eq_one` and `isIso_ajHom_of_x0Genus_eq_one`
are PROVEN, sorry-free, **53 000 lines further down the same file**, stated
level-generically over an arbitrary base.
**The detector is one grep and it is not a grep for the machinery.**  The leaf under
attack was `isTorsion_jacobian_of_kenkuLevel` (`N ∈ kenkuLevels`, open).  The same file
carries `isTorsion_jacobian` (`N ∈ levels = {11,17,19,32}`, **PROVEN**) — *the same
theorem at a different parameter set* — and its docstring names all five ingredients of
the route, in order, with their status.  Reading it turned an invented cost estimate
into a bounded, calibrated one (three rows of an existing table).
So, before pricing any route on a leaf of the form `P N` for `N` in some index set:
    grep -n "^theorem <yourLeafStem>" <the file>        # the SAME stem, other parameter
A development that has closed the easy parameters first — and this one does, everywhere
— has already built and NAMED the level-generic half.  The proven sibling is the
cheapest inventory there is: it is written in your vocabulary, it is in your file, and
unlike a "MISSING MACHINERY" list it cannot be stale, because it compiles.
Two riders, both of which cost time here:
* **Grep for the STEM, not for the machinery.**  `smoothOfRelativeDimension_one_of_…`
  and `isIso_ajHom_of_…` share no keyword with `isTorsion_factor_of_heckeIsotypic`, so
  no search phrased in the leaf's own vocabulary reaches them.  What reaches them is the
  proven sibling's docstring, which cites them by name.
* **Correct such a price IN PLACE and keep the wrong reasoning**, labelled.  The false
  step here was inferring "the tree cannot supply `dim J = 1`" from the true premise
  "the structure does not carry a dimension"; a reader who sees only the corrected
  sentence learns the fact and not the trap, and the trap is the transferable half.
### The instance's own mathematics, since it recurs wherever a Hecke decomposition does
**AN ISOTYPIC DECOMPOSITION IS NOT A DECOMPOSITION INTO SIMPLE FACTORS — THE OLDFORM
MULTIPLICITY IS INSIDE THE FACTOR.**  `IsHeckeIsotypicDecomposition.isotypic` is
quantified over `n` COPRIME TO `N`, so its `A i` is isotypic for the ANEMIC system, and
the anemic-isotypic part attached to a level-`M` newform `g` is `A_g^{σ₀(N/M)}`, of
dimension `[K_g : ℚ]·σ₀(N/M)`.  A task prompt priced a cut off "eleven of the fourteen
Kenku Jacobians are products of elliptic curves"; that is true of the SIMPLE factors and
false of these — only `{20, 24, 26, 36, 50}` have every isotypic factor one-dimensional.
The sharpest witness is `N = 28`, where `J₀(28) ∼ E × E` with `E = 14a` and yet the sole
isotypic factor is TWO-dimensional, because there is one anemic system.  **When a
decomposition's isotypy is quantified away from the level, multiply by `σ₀(N/M)` before
believing any dimension claim about its pieces.**
**AND A STRUCTURE WITH NO `nontriv` FIELD ADMITS A TRIVIAL DUPLICATE FACTOR**, so no
dimension clause is derivable from it at all.  `IsHeckeIsotypicDecomposition` has
`idx : Type` with `coeff` not required injective and — unlike its siblings
`IsUniversalIsotypicQuotient` and `IsIsotypicQuotient` — no nontriviality field.  Given
any inhabitant, `idx ⊕ Unit` with the new index carrying a DUPLICATE eigen-system and
`A := SpecQ`, `u := jstr`, `S _ := 𝟙` satisfies every field (`u_surj` because `SpecQ` is
a point; `u_add`/`isotypic` because `RelPoint (𝟙 SpecQ) g` is a singleton; `equivariant`
IS `T_comp`; `cover` is met by the original index; `finite_ker` is untouched).  So
`dim A i = 1` is FALSE for admissible data — and stating it as a HYPOTHESIS is
undischargeable at a call site that obtains the datum internally.  **Check for a
nontriviality field before quantifying over a structure's components.**
