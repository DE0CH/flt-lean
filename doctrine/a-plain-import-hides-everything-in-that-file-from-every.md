## A PLAIN `import` HIDES EVERYTHING IN THAT FILE FROM EVERY DOWNSTREAM MODULE
(2026-07-31, flt-lean-393.) `Fermat/FLT/ModularCurve/X0.lean` reaches
`Fermat/FLT/ModularCurve/EllipticScheme.lean` through a **plain `import`, not a
`public import`** (line 369, and it is the only such line in that header). Under
Lean's module system that means nothing downstream of `X0.lean` — `MazurTorsion.lean`
included, 40 000 lines of it — can name a single declaration of `EllipticScheme.lean`.
`relPointPost`, `relPointPost_add` (rigidity), `hom_specRat_eq_of_range_eq`,
`exists_isIso_of_affineChart`, `isIso_of_isDominant_of_inverse`,
`isDominant_of_range_eq_compl`: all PROVEN, all invisible.
This defeats the standing "grep the tree before proving anything from scratch" rule
in a way the rule does not warn about. A `grep` finds the theorem, `git log` shows it
green, its docstring says PROVEN — and `#check` says unknown identifier. **So the
availability test is `lake env lean` on a one-line `#check`, not a grep.** A scratch
module importing the target file costs seven seconds; run it before planning around
a reuse.
Two consequences that both bit in one task:
* **The wrapper is invisible, the theorem it wraps often is not.** The valuative
  criterion `AlgebraicGeometry.exists_unique_extension_of_isSmoothProperCurve` lives
  in `Fermat/FLT/Mathlib/`, is reachable, and is stated over an ARBITRARY FIELD;
  only `EllipticScheme.lean`'s ℚ-specialisation of it is hidden. Reproving the
  ~40 lines of wrapper over a general field was the whole cost.
* **Look for a second copy at the RIGHT generality before duplicating.** X0.lean's
  own `isAdditiveOn_of_post_zero` is relative rigidity over an ARBITRARY base — the
  general form of `EllipticScheme.relPointPost_add`, visible, and better. The first
  plan copied 120 lines of the hidden one; the reachable one made that unnecessary.
