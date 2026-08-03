## AN "ABSENT FROM THE PIN" TABLE IS ABOUT MATHLIB — AND THE MODULE THAT HAS IT MAY BE NAMED AFTER THE MISSING CONCEPT
(2026-07-31, `flt-lean-108`, closing `exists_forall_isInteger_notIsIntegralElem_functionField`
in `CurveAffineComplement.lean` — the Riemann–Roch leaf — in one run, over machinery that was
already in the tree.)
That leaf carried the best kind of inventory: dated, headed *"WHAT THE PIN ACTUALLY HAS, read
rather than grepped"*, correct in every clause, and explicit that it had been verified by
READING `Mathlib/AlgebraicGeometry/` rather than by name-grep. It ended:
> ABSENT … no `principalDivisor`, no degree map on cycles, no divisor class group, no `genus`,
> no coherent-sheaf cohomology … So the VALUATION-THEORETIC half of divisor theory is done and
> the GLOBAL half — `deg`, finiteness of `L(D)`, and the Riemann inequality — is what has to be
> built.
Every ABSENT clause is true **of mathlib**. The conclusion is about **the tree**, and it was
false: `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveGenus.lean` — a SIBLING FILE IN THE SAME
DIRECTORY, created the same day — defines `rrSet` (`L(D)`), `ell` (`ℓ(D)`), `divisorDegree`,
`pointDivisor` and `IsCurveGenus`, and states Riemann's theorem as its single leaf
`exists_isCurveGenus`. The task prompt reproduced the table verbatim, priced the run as a
theory build, and told me to expect to decompose. The leaf instead closed as a ~90-line
assembly, `2 → 1` sorries in the file, with NO new leaf.
**The specific failure, and it is cheaper to defend against than the general one this file
already records:** the audit searched for the CONCEPT and the module is NAMED for the concept.
`ls` of the leaf's own directory shows `CurveGenus.lean` and `CurveDivisorDegree.lean` next to
`CurveAffineComplement.lean`. A grep for the leaf's vocabulary (`functionField`, `IsInteger`,
`ord`) finds neither. So:
    ls Fermat/FLT/Mathlib/<the same subtree>/     # BEFORE believing any "must be built"
and read the `## Main definitions` block of anything whose FILENAME contains the missing noun.
Two seconds, and it is the one search an audit written from inside a file never runs.
Three riders, each of which cost something:
* **`grep -c "declaration uses 'sorry'"` RETURNS 0 ON A FILE FULL OF SORRIES.** Lean prints
  ``declaration uses `sorry` `` with BACKTICKS. I read a `0` from that grep as "the module is
  clean" and it was not — the same one-character trap as the truncated-log rule, and with the
  same shape of wrong answer (a confident clean). Grep for `declaration uses` and nothing more.
* **"THIS IS THE ONLY `sorry` IN THE FILE" in a task prompt is a claim about a commit.** There
  were two: the Riemann–Roch leaf and `existence_valuativeCriterion_toAffineLine_compl_singleton`
  at the end of the file, which shares nothing with it. Regenerate the set from the build's
  warning LINE NUMBERS before believing any count, including the one you were handed.
* **A leaf's own docstring can hold TWO obsolete bridges at once.** This one said a rational
  function of non-negative order comes from a section "is not in the pin either" — it had been
  proven in the same file that morning as `exists_germToFunctionField_eq_of_forall_isInteger`.
  When a docstring lists prerequisites, check each against the CURRENT file, not against the
  file the paragraph was written for.
### The cut that made it cheap: compare `ℓ` at TWO divisors, never `ℓ(D)` against `K`
Worth copying, because the obvious route needs a theorem nobody has. To get a NONCONSTANT
function out of Riemann's theorem the natural move is `ℓ(n[z]) ≥ 2 > 1 = dim_K K`, which needs
*`K` is algebraically closed in `K(X)`* — a real theorem, and the reason geometric connectedness
is a hypothesis. **Do not prove it.** Use `ℓ(n[z]) ≠ ℓ((n+1)[z])` instead: `L(n[z]) ⊆ L((n+1)[z])`
and the two spans would coincide if the sets did, so some `f ∈ L((n+1)[z])` is outside `L(n[z])`
— and every constant lies in `L(0) ⊆ L(n[z])` for `n ≥ 0`, so that `f` is nonconstant for free.
The extraction step never mentions the span, and "nonconstant" is never compared with
"transcendental". Generally: **when a dimension count is used to produce an object outside a
subspace, compare two members of the FILTRATION rather than one member against a distinguished
subobject** — the distinguished subobject is where the extra theorem hides.
Two facts about `Scheme.ord` this needed, both now in `CurveAffineComplement.lean` and both
mathlib-shaped: `0 ≤ ord f x` is EQUIVALENT to `f` lying in the local ring at `x`
(`exists_stalk_eq_of_zero_le_ord` / `zero_le_ord_of_exists_stalk_eq`, over
`Ring.ordFrac_ge_one_of_ne_zero` and the `ValuationRing` dichotomy); and an element integral
over `K` lies in EVERY local ring (`exists_stalk_eq_of_isIntegralElem`, because a DVR is
integrally closed and `functionFieldHom` factors through every germ). And the step that would
silently make the whole argument vacuous is `0 < strX.residueDegree z` — `Module.finrank`'s junk
value at an infinite extension — which is Zariski's lemma in scheme form and is now
`zero_lt_residueDegree_of_isClosed`, PROVEN and axiom-clean, over
`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace` plus one `Module.Finite.of_restrictScalars_finite`
tower. **Any leaf whose statement weighs points by `residueDegree` needs that positivity, and
nothing in the pin supplies it.**
