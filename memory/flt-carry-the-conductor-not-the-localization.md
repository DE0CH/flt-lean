---
name: flt-carry-the-conductor-not-the-localization
description: An argument of the form "z lies in R_p for every p in some family" formalises far cheaper as a statement about the DENOMINATOR IDEAL in the base ring than as a statement about the localizations
metadata:
  type: feedback
---

When a classical commutative-algebra proof says *"`z` lies in `R_p` for every prime `p`
in this family, and those intersect down to `R`"*, do **not** formalise it by building
`R[1/x]`, `R_p`, and an intersection of `Subalgebra`s inside the fraction field. Carry the
**conductor** (denominator) ideal instead:

    J := {r : R | r • z ∈ R}      -- an ideal of R, nonzero for every z ∈ Frac R

`z ∈ R` is `1 ∈ J`. A localization hypothesis is used ONLY to manufacture one element of
`J` outside one prime, and the rest of the argument happens in `R`:

* *`z ∈ R_p` for every `p` avoiding `x`* becomes *`J ⊄ p` for every such `p`*, hence every
  prime over `J` contains `x`, hence `x ∈ √J` (`Ideal.radical_eq_sInf`) — i.e.
  `x ^ k ∈ J` for some `k`, which `Nat.find` then minimises;
* the classical `R = R[1/x] ∩ R_{(x)}` collapses to: if `k` is least with `a = x ^ k z ∈ R`
  and `k ≥ 1`, minimality gives `x ∤ a`, while `s z ∈ R` with `s ∉ (x)` gives
  `s a = x ^ k c`, so primeness of `(x)` gives `x ∣ a`. Contradiction.

**Why:** the localization objects are where all the Lean friction lives — `IsScalarTower`
instances, `IsFractionRing` of a localization, `Localization.subalgebra` iInf bookkeeping,
and localization-of-localization identifications. The conductor form needs exactly one
plumbing lemma (*an integrally closed `R_p` yields a denominator outside `p`*), used twice,
and it is the ONLY place a localization appears. The resulting statement also drops
hypotheses the classical one seems to need: `IsIntegrallyClosed.of_span_singleton_isPrime`
in `Fermat/FLT/Mathlib/RingTheory/RegularLocalNormal.lean` needs **no** noetherian
hypothesis, **no** locality and **no** dimension theory — about 30 lines total.

**How to apply:** before writing any `Localization.AtPrime`, ask what the localization
hypothesis is actually *producing*. If the answer is "one denominator", define the ideal of
denominators and finish in the base ring. Related: [[flt-reduce-to-an-open-leaf-not-a-proof]],
[[flt-crude-bound-plus-patch]].
