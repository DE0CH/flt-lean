## A FALSITY AUDIT THAT SEARCHES ONE SUB-FAMILY PROVES NOTHING — and "hypothesis ⟺ conclusion" is the tell

(2026-07-31.) `IsShortExact.exists_lift_ker_le_span_cartierDual` in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/ShortExact.lean` carried **two** dated FALSITY AUDITS,
both careful, both correct, both concluding "searched, not refuted". They had also both noticed
the same odd thing and written it down as *weak evidence for* the leaf:

> "the hypothesis keeps turning out to be equivalent to the conclusion rather than merely
> implying it, which is why no counterexample has been produced."

**That coincidence was the refutation, not evidence against one.** When a hypothesis you did not
choose keeps coming out *exactly* equivalent to the conclusion across independent-looking
examples, the examples are not independent — you have picked a sub-family in which some identity
forces them together. Find the identity, then vary whatever it constrains.

Here the audits had searched `G' = μ_p`, `G'' = ℤ/p` — **the two groups always of the same
order**. In that shape the one non-trivial fibre of `G → G''` occurs exactly once, so
`Module.Free R O(G)` and the conclusion are literally the same condition on `[L] ∈ Pic(R)`.
Widening the quotient by one factor of `p` (`G'' = ℤ/p²`) makes the bad fibre occur `p` times,
and `p·[L] = 0` makes the hypothesis VACUOUS while the conclusion is untouched. With `p = 2`,
`R = ℤ[√-5]`, `Pic = ℤ/2`, the counterexample is three lines — **over a Dedekind base, which one
of the two audits had explicitly ruled out** ("a counterexample must have Krull dimension ≥ 2").
That ruling-out was a true statement about the sub-family read as a statement about the leaf.

Three transferable rules:

- **An audit's scope is part of its verdict.** Record which family was searched *in the verdict
  sentence*, not just in the working. "No counterexample" is not a result; "no counterexample
  with `ord G'' = ord G'`" is.
- **Vary the parameter you did not think of as a parameter.** Both audits varied the base ring
  (dimension, `Pic`, `K₀`, characteristic) and neither varied the *relative size* of the two
  ends. The unvaried parameter is where the counterexample lives, essentially by construction.
- **Multiplicity kills K-theoretic obstructions.** If a hypothesis says "`m` copies of `P` are
  free" and the conclusion says "`P` is free", they are the same statement only when `m` is prime
  to the order of `[P]` in `K̃₀`. Check that arithmetic before believing a hypothesis is
  load-bearing.

And the repair worth copying: when a leaf is refuted, look for the hypothesis the *real* consumer
already has. Here the whole chain (five declarations) gained `[IsLocalRing R]`, which is true at
the only intended base (`𝒪ᵖᵥ`), makes `CartierDual R A'` semilocal, and turns the remaining
mathematics from "global triviality of a torsor" into mathlib's
`Module.free_of_flat_of_finrank_eq`. Cost: zero, because a grep showed every mention of the
chain outside its own file was a docstring. **Grep for term-level consumers before assuming a
hypothesis cannot be added; in this development most of the tree is not consumed yet.**

**And the refutation paid for itself immediately, which is the general pattern.** Once the false
GLOBAL statement was replaced by the true LOCAL one, the leaf stopped being atomic: it fell in one
sitting to `flat + constant fibre rank` (a new, strictly smaller, Zariski-local sorry) plus two
proven steps — `finite_maximalSpectrum_of_isLocalRing_of_module_finite` (new, ~35 lines, pure
commutative algebra) and mathlib's `Module.nonempty_basis_of_flat_of_finrank_eq`. A leaf that has
resisted every cut for days is worth suspecting of being false *precisely because* falsity is what
makes it uncuttable: no cut can be found, because there is nothing true underneath to cut into.
"Atomic on every axis tried" is evidence about the statement, not only about the prover.

