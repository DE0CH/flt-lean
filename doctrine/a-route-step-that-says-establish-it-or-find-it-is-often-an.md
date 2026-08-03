## A ROUTE STEP THAT SAYS "ESTABLISH IT OR FIND IT" IS OFTEN AN IMPORT PROBLEM — and a PLAIN import reaches the proof body
(2026-08-02, `one_le_isCurveGenus_curveBaseChange_of_nontrivial_cuspForm` in
`ModularCurve/X0.lean`.)  That leaf's route opened with a step its own docstring
flagged in bold as the one that "surprises people halfway through":
> `_hS` gives `finrank_ℂ S₂(Γ₀(N)) ≥ 1`.  Note this needs
> `FiniteDimensional ℂ (CuspForm (Gamma0GL N) 2)`: `Module.finrank` of an
> infinite-dimensional space is `0`, so `Nontrivial` alone does NOT give
> `1 ≤ finrank`.  Establishing (or citing) finite-dimensionality is a real step.
The mathematics of that step is real and the warning is correct.  **The step was
not a mathematical obligation at all**: `cuspForm_finiteDimensional` had been
PROVEN since 2026-07-24 (over the Sturm bound, no modular-curve geometry), in
`Modularity/HeckeAtkinLehner.lean` — a module `X0.lean` **did not import**.  The
whole of the step was one import line, and with it the leaf's first two route
items became a six-line theorem.
This is the standing "missing machinery may be one import away" failure with a
sharper tell than usual: **the docstring said "establishing OR CITING", i.e. its
author already suspected the thing existed, and did not run the grep.**  So:
* **A route step phrased as a disjunction between doing the work and finding the
  work is an unrun search.**  Run it first — it is one `grep -rn` over `Fermat/`
  — before budgeting anything for the step.
* **Then check the import DIRECTION and price the edge**, because that is what
  decides whether the find is usable.  Ten lines of Python: compute the
  candidate's transitive `Fermat`-import closure, assert every visited file
  EXISTS (a swallowed `FileNotFoundError` truncates the walk and manufactures the
  "no cycle" answer you wanted), and intersect with your own.  Here
  `HeckeAtkinLehner`'s whole closure is `{HeckeOperator, HeckeQExpansion}`, both
  already imported by `X0.lean`, and it does not import `X0.lean` — so the edge
  costs **exactly one module** and creates no cycle.
* **Prefer a PLAIN import to a `public` one, and check where the name occurs.**
  Proof bodies are elided by the module system, so a non-public import reaches
  them.  `cuspForm_finiteDimensional` occurs only inside one `by` block, so the
  plain edge suffices and none of that module's ~196 declarations is re-exported
  through `X0.lean`'s very large downstream cone.  This was verified in a scratch
  before the real edit — `public import` the target, plain `import` the
  candidate, and elaborate the intended proof.
**And check the candidate declares no notation before adding the edge**, since a
plain import still brings notations into the importing module even though it does
not re-export them.  `grep -n '^\s*\(scoped \)\?\(notation\|infix\|prefix\|postfix\|syntax\|macro\|reserve\)'` — here, none.
