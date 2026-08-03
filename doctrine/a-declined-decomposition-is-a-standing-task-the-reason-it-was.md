## A DECLINED DECOMPOSITION IS A STANDING TASK — the reason it was declined goes stale

(2026-07-30, `flt-lean-203`.) `nonempty_fullTranslationDatum_two`'s docstring contained a
paragraph headed **"THE DECOMPOSITION THAT WOULD PAY FOR ITSELF, and it is uniform in `q`"**,
naming the exact cut that merges it with `nonempty_preTranslationDatum_three_of_intCoeff_pos`,
and ending: *"That cut is NOT made here only because
`exists_potentiallyGoodModel_of_jIntegral_three` has a live owner and restructuring it under
them would cost a merge conflict for no mathematical gain."*

The mathematics in that paragraph was right and the coordination reason was **two days stale**.
Making the cut took one 60-line proven bridge
(`nonempty_translationDatum_of_full_of_ne_two`: in residue characteristic `q ≠ 2`, `2` is a
unit of `A`, so `ha₁`/`ha₃` give `u⁻¹s, u⁻³t ∈ A` and the three `s`/`t`-corrections
`u⁻²s²`, `u⁻⁴(2st)`, `u⁻⁶t²` are products of those) and turned **two open leaves into one**,
with no signature change anywhere.

So: **when a docstring names a decomposition and declines it for a COORDINATION reason —
"has a live owner", "would conflict with", "is owned elsewhere" — that is a queued task, not
a closed axis.** Re-check the reason; ownership in this fleet turns over in hours. Distinguish
it from a decline for a MATHEMATICAL reason, which does not go stale: the same file's
**"AXIS SEARCHED AND CLOSED: `(ψ, r)` MUST STAY IN ONE EXISTENTIAL"** on
`exists_fundamentalCharacter_of_semistabilityDefect` comes with an explicit counterexample
(`N = 29`, `e = 4`, `ψ' = ψ_L^15`) and should be believed.

Corollary for anyone tempted by the same merge elsewhere: **two per-prime leaves whose
docstrings state the SAME residual obstruction are one leaf.** Both of these ended with "THE
ONE REMAINING GAP IS ... residue degree `1`", written out twice over two different datum
structures. Grep for repeated obstruction sentences across sibling leaves before proving
anything.

