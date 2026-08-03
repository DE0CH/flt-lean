## "NOT IN MATHLIB" IS NOT "NOT IN THE PROJECT" — check DOWNSTREAM before believing a leaf is expensive

(2026-07-31, `flt-lean-136`.) `finite_setOf_isWeightTwoEigenform` (`X0.lean`) carried a careful
`WHAT REMAINS GENUINELY MISSING` paragraph: mathlib at this pin has no finite-dimensionality of
`CuspForm`, `~/cs/FLT` has none, so a prover must build the valence formula, or a degree bound on
the Hecke field plus a Sturm bound. Every factual clause was TRUE. The verdict was wrong by a
week: **`cuspForm_finiteDimensional` had been proven on 2026-07-24**, in
`Modularity/Interface.lean` — which carries `public import Fermat.FLT.ModularCurve.X0` and is
therefore DOWNSTREAM, so nothing in it is nameable from `X0.lean`.

That is the whole trap, and it is invisible to the natural check. An audit run *in the file that
needs the theorem* asks "can I name it here", and gets the SAME answer — no — for two situations
that could not be more different:

  * nobody has proven it (weeks of work), and
  * it is proven, one import away, **in the wrong direction** (a hoist, sometimes minutes).

The second is common here precisely because this tree grows downward: the big consumers
(`Interface.lean`, 85k lines) accumulate general-purpose machinery that upstream files then turn
out to need. So:

**Grep the WHOLE tree for the missing statement, not the import cone, and when you find it
downstream, check whether its PROOF is upstream-clean.** If the proof mentions only mathlib — no
project predicate, no leaf, no structure defined below — the hoist is mechanical and the leaf was
never expensive. Here the Sturm-bound proof was 100 lines of `ModularForm.norm`,
`sturm_bound_levelOne` and the `q`-expansion API; moving it to `WeightTwoEigenform.lean` cost four
compile errors (`open scoped Manifold`, `open ModularForm` for the `∣[k]` notation, `_root_.one_zpow`
against the file's `open Matrix`, and a stray `qCoeffL` reference), and the leaf then closed.

**Leave the old paragraph's REASONING in place and mark the verdict.** The archimedean route that
docstring proposed is still a correct route; it is simply not the cheapest one, and the record of
what was searched is what lets the next reader see that the search was of mathlib and not of the
project.

Corollary for the hoist itself: **make the downstream copy a one-line delegation, do not delete it.**
Every consumer keeps its name and its carrier (`Interface.lean`'s version is stated in `qCoeff`,
which is `(qExpansion 1 ⇑f).coeff` by definition, so the delegation is `rfl` on the statement), the
diff in the contended file is a few lines instead of a hundred, and there is exactly one proof.

Same day, same worktree, the mirror-image win: two SORRIED copies of one theorem in two files with
two eigenform predicates (`isIntegral_coeff_prime_of_isWeightTwoEigenform` in `X0.lean` and
`isIntegral_qCoeff_prime_of_isWeightTwoEigenform` in `Interface.lean`). Their common refinement —
stated about mathlib's `qExpansion` coefficients and about no project predicate — goes UPSTREAM of
both, and both become assemblies over it. **A carrier move is a real result when it makes two
leaves into one; it is a wash when it makes one leaf into one.** Say which in the commit message,
because the sorry counts alone cannot tell them apart.

