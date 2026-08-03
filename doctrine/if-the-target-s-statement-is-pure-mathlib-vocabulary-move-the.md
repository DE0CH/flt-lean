## IF THE TARGET'S STATEMENT IS PURE MATHLIB VOCABULARY, MOVE THE WHOLE LEAF TO A MATHLIB-ONLY MODULE
(2026-07-31, `flt-lean-236`, on `Interface.lean`'s
`exists_planeModel_ringEquiv_functionField_of_isProperSmoothCurve`.) Before planning any
iteration loop inside a giant module, read the target's STATEMENT and ask which of its
symbols come from the project. Here the answer was **none**: `Scheme`, `IsProper`,
`SmoothOfRelativeDimension`, `GeometricallyConnected`, `Scheme.functionField`,
`MvPolynomial`, `AlgebraicClosure`, `FractionRing` are all mathlib, and the one
project-looking symbol — `Fermat.SpecF q` — is an `abbrev` for
`Spec (CommRingCat.of (ZMod q))`. So the entire leaf was restated and PROVEN in a new
module importing mathlib alone, and `Interface.lean` keeps a one-line `exact`.
What that buys, measured on this run:
* **90 s per iteration against ~25 min**, and `lake build` on the new module is 2903 jobs
  instead of 5600;
* **immunity to whatever is wrong upstream.** `merger` at release 28 does not build at
  all (import cycle, below), so `Interface.lean` could not have been verified in ANY
  number of hours. The new module built green regardless, and the only thing left
  unverified is the one-line delegation — which was itself checked in a scratch that
  declares its own `abbrev SpecF` and reproduces the delegation character for character;
* the two residual leaves are stated in mathlib vocabulary too, so a successor needs no
  orientation in an 89 000-line file.
**The check is one pass over the statement, not over the proof.** A leaf whose *proof*
needs project machinery can still have a mathlib-only *statement* — and the statement is
what decides where it can live. Conversely, do not do this when a hypothesis or the
conclusion names a project `structure`: then the module has to import that file and the
whole point is lost.
Two riders. **`Fermat.SpecF` is an `abbrev`, so the delegation is an `exact` and nothing
has to be rewritten** — check for that before duplicating a base. And a statement whose
conclusion is a BARE `RingEquiv` does not care which `𝔽_q`-algebra structure the
function field carries, so the geometry leaf can hand the structure over
EXISTENTIALLY (`∃ alg : Algebra (ZMod q) ↥X.functionField, …`) rather than construct it
through `Scheme.ΓSpecIso`/`appTop`/`germToFunctionField`. That is not the junk-witness
trap here, and the reason is worth reusing: **`ZMod q` is a quotient of `ℤ`, so
`RingHom.ext_zmod` makes `ZMod q →+* A` a subsingleton and the `∃` pins the structure
exactly.** (Same observation as `Interface.lean`'s `hom_specF_eq_of_affine`.)
### A ROUTE NAMING "CLEAR DENOMINATORS FROM THE MINIMAL POLYNOMIAL" IS THE EXPENSIVE ONE
Same leaf. Its docstring prescribed: separating transcendence basis, then
`Field.exists_primitive_element`, then *"clearing denominators from the minimal
polynomial of `y` over `𝔽_q(x)`"*. The last step is not needed at all, and it is the one
that drags in `MvPolynomial (Fin 2) k ≃ k[X][Y]`, Gauss's lemma and primitivity.
**Take a nonzero relation of `![x, y]` of MINIMAL TOTAL DEGREE instead.**
`MvPolynomial.irreducible_of_forall_totalDegree_le`
(`Mathlib/FieldTheory/SeparablyGenerated.lean`) says such an `F` is irreducible
outright. The same file's `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`
(`@[stacks 030W]`, 2025) hands over the separating transcendence basis — the single
hardest classical input, and off the shelf; a docstring older than that file will not
know it exists.
And `ker (aeval ![x,y]) = span {F}` is a **Krull-dimension count**, not elimination
theory: `MvPolynomial.ringKrullDim_of_isNoetherianRing` gives `dim 𝔽_q[X,Y] = 2`, two
applications of `ringKrullDim_succ_le_of_surjective` force `dim (𝔽_q[X,Y]/ker) ≤ 0` if
the inclusion were strict, a zero-dimensional domain is a field, and Zariski's lemma
(`finite_of_finite_type_of_isJacobsonRing`, `@[stacks 0CY7]`) then makes `x` algebraic —
contradiction. Then `IsFractionRing.of_field` plus `IntermediateField.mem_adjoin_iff_div`
identify `K` with `Frac(𝔽_q[X,Y]/(F))` with no `Subalgebra`/`Subring` transport at all.
**The one place to budget time is `WithBot ℕ∞` arithmetic.** `ringKrullDim` is valued
there, `ℕ∞` is NOT cancellative (`⊤ + 1 = ⊤`), so `d + 1 + 1 ≤ 2 → d ≤ 0` needs an
explicit two-level case split — and note `ℕ∞` is `ENat`, a `def` over `WithTop ℕ`, so
`WithTop.top_add` fails to `rw` with *"⊤ has type WithTop ℕ but is expected to have type
ℕ∞"*. Reach the contradiction by `le_self_add` instead of by rewriting: `⊤ ≤ ⊤+1+1 ≤ 2`,
then `simp`.
### AN IMPORT CYCLE IS A RELEASE BLOCKER THAT NO SORRY SCAN AND NO SINGLE-FILE CHECK SEES
Found on `merger` at release 28 (2026-07-31), by an agent whose target was three modules
downstream of it:
    ModularCurve.X0 (public import, :985)  ──▶ FreyCurve.IsogenySignature
    FreyCurve.IsogenySignature (import, :283) ──▶ ModularCurve.HyperellipticJacobian
    ModularCurve.HyperellipticJacobian (import, :325) ──▶ ModularCurve.X0
Each edge is individually justified in its own import comment, each was added by a
different branch, and **no two of them conflict textually** — so the union merges
cleanly and the cycle exists only in the graph. `lake` reports it as
`error: build cycle detected` followed by a list of `bad import` lines for a dozen
modules that are perfectly fine, which reads like fifteen separate defects.
It is the eighth invisibility class and the cheapest to check: **after any merge that
touched an import block, compute the import closure and look for a back edge.** Ten lines
of Python, seconds to run, and it is the only instrument that sees this before a
5600-job build spends an hour reaching it.
`HyperellipticJacobian.lean`'s own import comment already names the resolution — hoist
`nonempty_cubeModel_of_isAmpleSheaf_cube` and `exists_cubeModel_of_abelianScheme` out of
`X0.lean` into `Modularity/AbelianSchemeIsogeny.lean` and drop the `X0` edge — so the
repair is written down and belongs to whoever owns the merge, not to a passer-by.
