---
name: flt-dropped-instance-binder-hides-a-route
description: A cut can silently drop an INSTANCE binder; nothing breaks, but a whole proof route becomes unavailable inside the leaf and the docstring records it as a missing theorem.
metadata:
  type: project
---

(2026-08-02, `flt-lean-347`, `exists_hilbertAuxDiamondGeneratorsPinned` in
`HardlyRamified/HilbertModularity.lean`.)

Its docstring flagged, in bold, **THE STEP TO CHECK**: the wild-inertia clause is
derivable only if `1 + 𝔪_{R_Q}` is pro-`ℓ`, which needs `(ℓ : R_Q) ∈ 𝔪`, i.e.
residue characteristic `ℓ` — and `HilbertAuxDeformationDatum` "posits only
`Algebra ℤ_[ℓ] R` and `π : R →+* k` surjective; it does NOT state `CharP k ℓ`".
It concluded that if this is not derivable "the honest repair is a field or a
hypothesis".

**It is derivable, and `natCast_eq_zero_of_hilbertAuxDeformationDatum` had proven
it in the SAME FILE ~1700 lines above, for two days.** The reason nobody saw it:
that lemma takes `[Finite k]`, and the six-declaration diamond chain
(`…GeneratorsPinned → …Generators → …Quotient_of_exponents → …Quotient →
…Control → …RingPresentation`) does not carry `[Finite k]` — while
`exists_hilbertTaylorWilesAuxLevelData`, the declaration at the TOP of the chain,
does. A cut copies binders by hand, and this one dropped the instance on the way
down.

**The general shape, and it is why this is worse than dropping an explicit
hypothesis.** An explicit hypothesis that goes missing usually breaks something:
a call site fails, a proof stops elaborating. **A dropped INSTANCE binder breaks
nothing.** The leaf is still true, still sorried, still consumed; every call site
still elaborates, because the caller had the instance and nothing asked for it.
What it does is make an entire ROUTE unavailable *inside* the leaf — and the next
author writing the docstring correctly reports the route as blocked, and blames
the STRUCTURE ("the datum does not state `CharP k ℓ`") rather than the binder
list.

**Two checks, both one command:**

* when a docstring says a fact is "not stated by the structure", grep the file for
  the fact itself — `grep -n 'natCast_eq_zero\|CharP k' <file>` — before believing
  the structure has to change;
* when a leaf is cut out of a parent, **diff the two binder lists including
  INSTANCE binders**. This project's standing rule already says *the missing
  hypothesis is usually already in the caller's hand*; instance binders are the
  half of it nothing enforces.

Adding `[Finite k]` back to all six changed **no call site** (instance search
finds it) and cost one edit each. See also
[[flt-decomposition-drops-a-hypothesis]] and
[[flt-inventory-audits-understate-what-exists]].
