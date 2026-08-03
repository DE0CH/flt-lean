## A HYPOTHESIS YOU CANNOT SUPPLY MAY BE PURCHASABLE BY BASE CHANGE

(2026-07-31, `flt-lean-202`.) `exists_smoothProperCompactification_affineLine` had a
careful audit that named the right obstruction and then priced only the two most
expensive ways past it. The tool it wanted,
`exists_isSmoothCompactification_of_isAffine`, requires `[PerfectField K]`; the leaf
has a bare `[Field K]`. The audit concluded: either build `ℙ¹_K` by hand via `Proj`,
or descend along `K ⊆ K^perf`. Both are large.

The leaf was three lines away. **`𝔸¹_K` is the base change of `𝔸¹` over the PRIME
field, and the prime field is perfect in both characteristics** (`ℚ` by
`PerfectField.ofCharZero`, `𝔽_p` by `PerfectField.ofFinite`). Build the object where
the hypothesis holds, pull it back, and the imperfect case costs one `rcases` on
`CharP.char_is_prime_or_zero`.

So add this before writing "needs new theory" about a missing hypothesis: **ask
whether the statement is stable under a base change that CAN supply the hypothesis.**
A hypothesis on the BASE is often purchasable by moving the construction to a smaller
base — and the smaller base is usually the prime field, `ℤ`, or `Spec ℤ`, where
finiteness/perfectness/normality hold for free. This is a different question from
"how do I prove it", which is the only question the audit asked, and it is much
cheaper to answer.

Corollary worth its own line: **check which properties you must TRANSPORT and which
you can REDERIVE downstream.** Here properness, smoothness and openness are base-change
stable; FINITENESS OF THE COMPLEMENT is not — transporting it means proving the preimage
of a finite set under `C_K ⟶ C_{𝔽_p}` is finite, a genuine argument about the fibres
`Spec (κ(x) ⊗_{𝔽_p} K)`. It was avoided entirely by not transporting it: the base-changed
curve is still a smooth curve over `K`, so its Krull dimension is `≤ 1` and the existing
`finite_compl_range_of_topologicalKrullDim_le_one` regives the conclusion from density
alone. Rederiving downstream was cheaper than transporting, and that is the common case.

Second audit failure in the same leaf, the same shape as the `Isogeny`-row error
recorded above: the audit reported `SmoothOfRelativeDimension 1 (𝔸¹_R ↘ Spec R)` missing
because **it searched for an INSTANCE and there was none — while the CONSTRUCTOR was
right there.** `Algebra.PreSubmersivePresentation.naive` with the relation family indexed
by `PEmpty` presents the polynomial algebra itself; the Jacobian is the determinant of the
empty matrix, i.e. `1`. "No instance fires" is evidence about the instance database, never
about the library.

