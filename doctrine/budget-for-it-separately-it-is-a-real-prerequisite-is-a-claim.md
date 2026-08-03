## "BUDGET FOR IT SEPARATELY — IT IS A REAL PREREQUISITE" IS A CLAIM ABOUT THE PIN, AND THE PIN IS BIGGER THAN THE ONE LEMMA YOU KNOW
(Same task, and it is the reason level `19` sat behind a re-route for two days.)
`MordellWeil19.lean` carried a careful, correct, bolded WARNING: level `11` gets `h(K) = 1`
from `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`, which needs
`|disc| < (2·(π/4)^{r₂}·nⁿ/n!)² ≈ 49.96`; level `11` squeaks in at `44` and **level `19`
is `76`, so that lemma does not apply at all** — and no change of model helps, the cubic
field being the `2`-division field of the whole isogeny class. Every word true. The note
then concluded that the ideal-norm route "needs the ideal-norm side of
`Mathlib/NumberTheory/ClassNumber/*`, which nothing in this tree currently drives. **Budget
for it separately: it is a real prerequisite, not plumbing.**"
It is sixty lines, because the pin already carries the general criterion:
    RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
— "if every prime `P` above every `p ∈ Finset.Icc 1 ⌊M K⌋₊` with `p^{f(P)} ≤ ⌊M K⌋₊` is
principal, `𝓞_K` is a PID". Compute `⌊M K⌋₊ = 2` (here `8√76/(9π) ≈ 2.4666`, so only
`π > 3` and `√76 ≤ 9` are needed), and the single prime above `2` is principal because
`θ³ = −2(θ+1)²` with `θ + 1` a unit, so `(2) = (θ)³`. The Lean shape, worth copying:
* `θ ∈ P` from `θ³ = −2ε² ∈ P` by `IsPrime.mem_of_pow_mem`;
* `span {θ}` is MAXIMAL because `Ideal.absNorm (span {θ}) = |Algebra.norm ℤ θ| = 2` is
  prime — `Ideal.isPrime_of_irreducible_absNorm` then `Ideal.IsPrime.isMaximal`;
* a prime ideal containing a maximal ideal equals it (`IsMaximal.eq_of_le`).
**The generalisable rule: when a docstring says a named mathlib lemma does not apply, it
has told you about ONE lemma. Read the file that lemma lives in.** The three theorems
above `isPrincipalIdealRing_of_abs_discr_lt` in `NumberField/ClassNumber.lean` are exactly
the weaker-hypothesis versions of it, in increasing generality, and the file's own module
docstring says how to use them ("first compute `⌊M K⌋₊`, then `fin_cases`"). This is the
[[flt-inventory-audits-understate-what-exists]] failure in its cheapest form: the audit was
right about absence at the point it looked and never looked one screen up.
### The mechanical trick for a goal you cannot write down: `trace_state`, once
`M K` in that file is a `local notation`, so a consumer cannot state a bound on it and
`rw` it into place. Do not guess the elaborated form. Write the proof with the two
inequality goals as `?_`, put `trace_state; sorry` in each, and read them out of the build
log — one `lake build` of the module in development, and the exact term comes back
(`(4 / Real.pi) ^ nrComplexPlaces KK * (↑(finrank ℚ KK).factorial / ↑(finrank ℚ KK) ^
finrank ℚ KK * √|↑(NumberField.discr KK)|)`). Then discharge them with a standalone lemma
taking the awkward subterm as a VARIABLE (`minkowski_aux (S : ℝ) (hS9 : S ≤ 9)`), so
`exact` does the matching up to defeq and nothing depends on how the casts print.
