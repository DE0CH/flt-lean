## A LEAF WHOSE CONCLUSION IS RING THEORY ABOUT A CITED SCHEME IS A CITATION PLUS A FIXED BRIDGE — AND THE TWIN HAS USUALLY BUILT THE BRIDGE ALREADY
(2026-08-02, `flt-lean-212`, `exists_dedekind_rigidifiedModuli` in `ModularCurve/X0.lean`.)
A recurring shape here: a citation produces a SCHEME, and the leaf that carries the
citation states its content as properties of the scheme's COORDINATE RING —
`IsDedekindDomain A ∧ Algebra.FiniteType ℚ A ∧ ringKrullDim A = 1`. That statement is
not what any book proves. Katz–Mazur (4.7.1) says *"representable by a **smooth affine
curve**"*; Dedekind-ness is a downstream commutative-algebra consequence that the leaf
has silently bundled in, so the leaf cannot be dispatched at anybody who knows only the
citation.
**Split it: the geometry stays in the leaf, the ring theory becomes a general lemma.**
Here the residue is `IsDomain R.A ∧ SmoothOfRelativeDimension 1 R.strM` — two clauses,
both verbatim citation — and all three original conjuncts come off the smoothness:
* `Algebra.FiniteType` is not an obligation at all: `Algebra.Smooth` **carries**
  `FinitePresentation`, and `algebraSmooth_of_smoothOfRelativeDimension`
  (`SmoothConnectedCriteria.lean`, PROVEN) reads `Algebra.Smooth K A` back off the
  morphism. A clause that a sibling clause implies should never be in a leaf;
* `IsDedekindDomain` is mathlib's **`IsDedekindDomainDvr`** — "noetherian domain whose
  localisations at nonzero primes are DVRs" — which is exactly the shape a scheme
  supplies: `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one`
  (`CurveExtension.lean`, PROVEN) transported along `AlgebraicGeometry.Spec.stalkIso`,
  with `IsLocalization.AtPrime.not_isField` discharging the not-the-generic-point
  exclusion from `P ≠ ⊥`. **Reach for `IsDedekindDomainDvr`, not the four-part
  definition** — noetherian + integrally closed + dimension ≤ 1 would each need its own
  argument, and `IsIntegrallyClosed` in particular would want Serre's criterion, which
  CLAUDE.md correctly records as absent from the pin;
* `ringKrullDim = 1` is `ringKrullDim_eq_of_smoothOfRelativeDimension`, an EXISTING leaf
  of `SmoothConnectedCriteria.lean` that already had a consumer in `X1.lean` — so
  routing through it creates no new obligation.
Total: ~25 lines, first try, in a scratch that iterates in **8 seconds**.
**PROVE THE CONVERSE BEFORE YOU CUT — that is what lets the audit be INHERITED.** A recut
normally VOIDS the earlier faithfulness audit, and re-deriving one for a Katz–Mazur leaf
is expensive. It is inherited for free when the two statements are provably EQUIVALENT,
and over a PERFECT base field they are: `smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing`
(PROVEN, needs `PerfectField`) plus mathlib's `instance [IsDedekindDomain R] : IsRegularRing R`
runs the implication backwards in two lines. `ℚ` is perfect. Compile both directions in the
scratch, say so in the docstring, and **do not commit the converse** — nothing consumes it,
so it would be free-floating; record the two lines that prove it instead.
**AND THE TWIN HAD ALREADY DONE HALF OF THIS.** `X1.lean` made the same move for `Γ₁` on
2026-07-30 — `smoothM` as a structure field, `smoothOfRelativeDimension_of_gamma1RigidifiedModuli`
as the residual citation leaf, both converses added to `SmoothConnectedCriteria.lean`
*for that repair* — and the `Γ₀` side never inherited it. The two converses I needed were
sitting there, written for the twin, three days old. So the standing rule ("a faithfulness
repair is not inherited by the twin") has a positive form worth using: **when your leaf has a
`ℚ`/`F` or `Γ₀`/`Γ₁` twin, grep the twin for your conclusion's vocabulary before pricing
anything** — the machinery is often already built and merely unconsumed on your side.
Accounting, stated the way CLAUDE.md asks: **the count does not move, `1 → 1`**, and the
receipt is `git diff | grep -E '^[+-] *sorry *$'` showing exactly one of each. Judge it by
what is LEFT in the leaf.
### Three smaller things from the same run
* **A task prompt's "this file is RED for reasons that are not yours" is DATED.** Mine said
  X0 carried 39 pre-existing errors and prescribed a differential error-set comparison. That
  was release 31; release 33 published, and `lake env lean` on X0 returned `EXIT=0` with
  **zero** errors. The one-second check is `ls .lake/build/lib/lean/<path>/X0.olean` after
  seeding from `~/.flt-release-lake/build` — **a red module has no olean in the snapshot**, so
  the snapshot answers the question before any build does.
* **`RingEquivClass.isDiscreteValuationRing` does not exist under that name.** It is declared
  inside `namespace IsDiscreteValuationRing`, so it is
  `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`. The error is a bare
  `Unknown constant` naming the path you wrote, which reads as a missing import; the cure is
  `grep -n '^namespace\|^end ' <the mathlib file>` and reading off the enclosing scope, not
  adding imports. (I added two imports chasing it; neither was needed — everything was already
  transitively reachable through X0, which one scratch settles by deleting them and recompiling.)
* **A scratch must reproduce the target's `open` lines or it will reject text that is
  correct.** Pasting my inserted block into a scratch without X0's `open CategoryTheory
  AlgebraicGeometry` produced six `Unknown identifier` errors for `Spec` and
  `SmoothOfRelativeDimension` and an autoImplicit cascade. Get the opens from a
  **comment-masked** scan — this project's docstrings contain the words `open`, `namespace`
  and `end` in prose, so a plain `grep '^open '` over the source is not reliable.
