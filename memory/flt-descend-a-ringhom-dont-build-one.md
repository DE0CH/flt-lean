---
name: flt-descend-a-ringhom-dont-build-one
description: When a leaf is priced as "the classical coefficientwise computation", look for a factorisation through RingHoms mathlib already has — descending one along a surjection is free, building one is not
metadata:
  type: feedback
---

`existsUnique_ringHom_wittVector_of_isNilpotent` (Patching.lean) sat open for four
days with a docstring pricing its existence half as *"set `f x = Σ_i ω(x_i^{p^{-i}}) p^i`
… that the sum is a ring map is the classical computation"* — i.e. a large
Witt-polynomial identity, plus a square-zero induction. It was proved on 2026-07-31
in ~200 lines **without proving any Witt-polynomial identity at all**, by factoring

    𝕎 k --𝕎(s')--> 𝕎 (S/p) --θ--> S

where **both arrows come from ring maps that already exist**:

* `𝕎(s')` is `WittVector.map` of a ring map `s' : k →+* S/p` — functoriality, free.
* `θ` is mathlib's `WittVector.ghostComponent M` **descended** along the surjection
  `𝕎 S ↠ 𝕎 (S/p)`. `ghostComponent` is already a `RingHom`; descending a `RingHom`
  along a surjection needs only a kernel inclusion (`RingHom.liftOfSurjective`), and
  the inclusion is one more mathlib lemma (`pow_dvd_ghostComponent_of_dvd_coeff`).

**Why:** a "construct a ring map by a formula on coordinates" obligation is expensive
exactly because the ring-map axioms have to be re-proved. A "descend / compose /
restrict an existing ring map" obligation is cheap because they are inherited. Before
writing a coordinatewise formula, ask which existing `RingHom` has the right values
and what quotient or subobject would make it land where you need.

**How to apply:** when a docstring says "the classical computation", treat that as an
unchecked estimate, not a measurement — the docstring's author was sketching, not
formalising. Grep the relevant mathlib directory for `→+*`-valued definitions first.
Two further transferable pieces from the same proof:

* **A Frobenius twist is free over a perfect ring.** The composite above computes
  `σ (f x) = (x.coeff 0)^{p^M}`, not `x.coeff 0`. That is not a bug in the route —
  precompose the section with `(iterateFrobeniusEquiv k p M).symm`. Any "off by
  Frobenius" mismatch over a perfect base is bookkeeping.
* **In characteristic `p`, the Teichmüller section is a ring map for nothing**, because
  Frobenius is a ring map: `s a := (any lift of a^{p^{-m}})^{p^m}` is well defined and
  additive as soon as ONE exponent `p^m` kills `ker σ`. All the difficulty in the
  classical proof lives in mixed characteristic, and the factorisation above is what
  moves the section into the characteristic-`p` quotient where it is easy.

See also [[audit-searched-production-not-invariant]] (same shape: the audit searched
for how to PRODUCE the object and missed the cheap characterisation) and
[[flt-cleaner-statement-harder-proof]].
