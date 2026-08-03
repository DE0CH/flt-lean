## A ROUTE THAT NAMES `𝔽̄_p`-CONSTITUENTS IS USUALLY REPLACEABLE BY A `p`-GROUP FIXED-POINT ARGUMENT
(2026-08-01, `flt-lean-131`, `exists_inertiaEigenvector_space_of_charpoly` in
`HardlyRamified/Family.lean`.) That leaf's docstring prescribed, in its own words, *"any simple
`𝔽_p[I_p]`-submodule `W ≤ T` has all its `𝔽̄_p`-constituents among those of `M ⧸ pM` … a simple
`𝔽_p`-module all of whose `𝔽̄_p`-constituents are `𝔽_p`-rational characters is one-dimensional"*,
and the task prompt repeated it as the natural cut (Brauer–Nesbitt, plus a Jordan–Hölder
statement over the algebraic closure). Formalised, that is Wedderburn plus the decomposition of
`W ⊗_{𝔽_p} 𝔽̄_p` into distinct Galois conjugates — a real development.
**None of it is needed.** The two facts the argument actually consumes are
* the COMMUTATOR SUBGROUP acts unipotently (the characters are multiplicative into an ABELIAN
  group, so they kill commutators, and Cayley–Hamilton turns `(X−1)²` into nilpotence), and
* each element satisfies a SPLIT QUADRATIC with roots in the prime field,
and from those the common eigenvector comes out of pure group theory in ~350 lines with no
`𝔽̄_p` anywhere: a unipotent endomorphism of a `p`-torsion group has `p`-power order (because
`(f − 1)^{p^k} = f^{p^k} − 1` in characteristic `p`), so the commutator subgroup acts through a
`p`-GROUP and its fixed subgroup `Fix` is nonzero by `IsPGroup.exists_fixed_point_of_prime_dvd_
card_of_fixed_point`; `Fix` is stable (the commutator subgroup is normal) and inside it every
pair of operators COMMUTES; so in a MINIMAL nonzero stable subgroup `W ≤ Fix` each eigenspace
`ker (g − a) ⊓ W` is stable, and the split quadratic makes one of the two nonzero, hence all of
`W` by minimality.
**The generalisable question, and it is one line: does the argument need the constituents, or
only a NORMAL SUBGROUP that acts unipotently?** Whenever a route reaches for semisimplification
over `k̄` in order to produce a common eigenvector, check whether the subgroup on which the
characters are trivial acts unipotently. If it does, its fixed subspace is nonzero for free, the
quotient acting on it is abelian, and minimality finishes — no coefficient extension, no
Jordan–Hölder, no Schur. The same substitution should be tried on any leaf whose docstring says
"one-dimensional constituents" or "the semisimplification is `χ̄₁ ⊕ χ̄₂`".
Two riders from the same run.
* **The residue is then stated with NO coefficient field in it.** What is left
  (`exists_inertiaCharpolyScalars_space_of_charpoly`) is two clauses about the operator
  `residualInertiaEnd ρ I σ` — commutators are unipotent, everybody satisfies a split quadratic
  — so the arithmetic prover never has to mention `𝔽̄_p`, a constituent or a simple module. A
  recut whose count is `1 → 1` is worth taking when it deletes a vocabulary that way; say so in
  the commit, because a `−1 +1` warning-set delta reads as nothing having happened.
* **Prove the algebra in a MATHLIB-ONLY scratch, not against the target's cone.** The whole
  `p`-group/minimality development is about `AddMonoid.End` of a finite abelian group and
  imports nothing from the project, so it iterated at **5 SECONDS** per round against a
  ~15-minute rebuild of `Family.lean`; the glue, in a second scratch that `public import`s
  `Family` and restates the target under a primed name, iterated at **12 seconds**. Both
  transplanted into the real file unchanged. `AddSubgroup` throughout rather than
  `Module (ZMod p)` avoids the `ZMod p`-module structure entirely: on a `p`-torsion group every
  subgroup is already a subspace.
