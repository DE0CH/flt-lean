---
name: flt-minkowski-above-the-pid-threshold
description: isPrincipalIdealRing_of_abs_discr_lt failing is not the end — the pin's general primesOver criterion gives h=1 in ~60 lines when the Minkowski bound exceeds 2
metadata:
  type: reference
---

`RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` needs
`|disc K| < (2·(π/4)^{r₂}·nⁿ/n!)²` — for a complex cubic, `≈ 49.96`. When it
fails (level `19`'s `ℤ[θ]`, `θ³+2θ²+4θ+2 = 0`, `disc = −76`) the class number can
still be `1` and the pin already carries the general criterion, three theorems
above it in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`:

    RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc

Recipe (used in `Fermat/FLT/EllipticCurve/CubicRing19.lean`, ~60 lines):
1. show `⌊M K⌋₊ ≤ 2` — only `π > 3` and `√|disc| ≤ 9` were needed;
2. so `p = 2` is the only prime; get `θ ∈ P` from a relation like `θ³ = −2ε²`
   (`ε` a unit) by `Ideal.IsPrime.mem_of_pow_mem`;
3. `span {θ}` is maximal because `Ideal.absNorm (span {θ}) = |Algebra.norm ℤ θ|`
   is prime: `Ideal.isPrime_of_irreducible_absNorm` then `Ideal.IsPrime.isMaximal`;
4. `Ideal.IsMaximal.eq_of_le` finishes.

`M K` is a `local notation` in that mathlib file, so you cannot state a bound on
it. Do not guess the elaborated term: leave the goals as `?_` with
`trace_state; sorry`, read them from one build log, then discharge with a lemma
that takes the awkward subterm as a plain variable so `exact` matches up to defeq.

Also: `Algebra.norm_eq_of_algEquiv` transports a norm along `𝓞 K ≃ₐ[ℤ] ZS`, and
the criterion lives at ROOT level (`_root_.RingOfIntegers.…`), not under
`NumberField`.
