## A LEAF THAT ASKS FOR AN UNBUILT SCHEME CUTS ALONG THE FIELD-CASE ASSEMBLY — read that proof, not the leaf
(2026-08-02, `flt-lean-304`, on `exists_isX0NormalProperModel_specLoc` in
`ModularCurve/X0.lean` — the normal proper integral model of `X_0(N)` over
`ℤ_(ℓ)`.)  A leaf whose conclusion is *"there exists a scheme with these seven
properties"* reads as atomic to every axis audit, and this one carried a four-axis
IRREDUCIBLE verdict, all four of whose axes really are dead.  It is nevertheless
cut mechanically, and the cut is not found by thinking about the leaf at all:
**Open the file that proves the SAME THEOREM OVER A FIELD, read its assembly line
by line, and label each input base-generic or base-specific.**  Here that was
`AlgebraicGeometry.exists_isSmoothCompactification_of_properModel` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveCompactification.lean`.  Of its six
inputs, FOUR transplanted verbatim to a Dedekind base and are now Lean rather than
prose — `IsOpenImmersion i.toNormalization` (Zariski's Main Theorem),
`IsIntegral i.normalization` (a `Mathlib` instance given `IsIntegral Y`),
`IsProper (i.fromNormalization ≫ strP)` (finite over proper), and the stalk
normality (`isIntegrallyClosed_stalk_normalization`, which carries NO hypothesis on
the base) — and only two were base-specific.  The residues are then whatever the
labelling left over, and each is a statement in ONE subject.
Two things this makes cheap that reading the leaf does not:
* **The residues come out already separated by subject.**  Here: one purely modular
  input on the coarse space (affine, integral, finite type, normal), one purely
  algebraic-geometric compactification statement that mentions neither `N` nor `ℓ`,
  and one purely modular cusp-finiteness statement.  Nobody has to be an expert in
  two of the three, and the second is a PORT of two named theorems rather than new
  mathematics.
* **The assembly is verified before any of the residues exist.**  Restate the target
  in a scratch that `public import`s the module, put the residues in as local
  `sorry` stand-ins, and compile: **7 seconds per round** against ~30 minutes for
  the real file.  Both drafts here compiled first try, and the second draft was
  written only because the first exposed the Lean trap below.
**Report the count honestly and separately: this was `1 -> 3`.**  A cut that
decomposes an unbuildable object always raises the count, and the tie-breaker
"fewer OPEN leaves after" is for choosing between RIVAL cuts, not a reason to leave
a leaf nobody can start.  What to say instead is what left the leaf for good — here
the construction itself, i.e. which of the seven fields is supplied by what and in
which order.
### THE LEAN TRAP THAT DECIDED THE SHAPE: a conjunct of an `∃` is not an instance for the next conjunct
The natural way to bundle two general-AG steps into ONE residue is
    ∃ P strP i, IsOpenImmersion i ∧ QuasiCompact i ∧ IsProper strP ∧ i ≫ strP = ystr
      ∧ IsFinite i.fromNormalization                    -- FAILS TO ELABORATE
with `failed to synthesize QuasiCompact i`, because `Scheme.Hom.fromNormalization`
takes `[QuasiCompact i]` and the `QuasiCompact i` CONJUNCT is an ordinary `Prop`,
not a local instance.  The error names a class that is visibly sitting three
conjuncts to the left, which is what makes it read as an instance-priority problem
rather than a scoping one.
**Do not fight it with `∃ (_ : QuasiCompact i)` binders — restate the leaf so its
conclusion mentions only the OUTPUT object.**  Here that meant asking for the
compactification `XZ` directly (open immersion, proper, integral, normal stalks,
commuting) instead of for an auxiliary `P` whose normalisation is finite.  That is
strictly better on its own terms: the residue stops mentioning the intermediate
scheme and the relative-normalisation API entirely, so it can be discharged by ANY
construction rather than only by the one the docstring had in mind.  **A statement
that needs instance arguments to elaborate is a statement about a construction; a
statement about an object does not.**
### AND THE `ℓ ∤ N` CORRECTION, which is the standing route-versus-truth rule
The old docstring closed with *"`ℓ ∤ N` is NOT needed for the construction (the
model exists over `ℤ[1/N]` and one may base change) … a prover may ignore it."*
The first clause is right and is now visible in a SIGNATURE — the compactification
residue carries neither `ℓ` nor `N`.  The second is wrong, and the cut is what shows
why: normality of the coarse space is reached through Igusa's SMOOTHNESS theorem,
which is false at `ℓ ∣ N`, so the hypothesis is load-bearing for the ROUTE.
Whether it is load-bearing for the TRUTH is a different and open question, and the
evidence points the other way — Deligne–Rapoport's model at `ℓ ∣ N` is normal
though not smooth — so what changes at `ℓ ∣ N` is the CITATION, not the truth
value.  **Say which of the two you are claiming.**  A docstring that says
"load-bearing" without saying for which is how a hypothesis gets dropped by the
next agent, and a docstring that says "a prover may ignore it" without checking the
route is how a leaf becomes unprovable.
