---
name: flt-coarse-moduli-reduction-nets-zero
description: A fixed-point leaf on X_0(N) reduces to a statement about Γ₀(N)-data over ℚ̄ in ~25 lines, because BOTH halves of the coarse-moduli geometric bijection are already proven in X0.lean
metadata:
  type: project
---

`X0.lean` proves both halves of the geometric bijection for a coarse moduli
space, and they are the lever that turns a scheme-theoretic leaf into a purely
arithmetic one:

* `IsCoarseModuliY0.exists_gamma0Datum_of_algClosPoint` — every `ℚ̄`-point of
  `Y` is `classify (specAlgClos ℚ) d` for some `d : Gamma0Datum N (Spec ℚ̄)`;
* `IsCoarseModuliY0.nonempty_isBaseChangeOf_of_classify_eq` — two `ℚ̄`-data
  with the same moduli point are isomorphic (`IsBaseChangeOf (𝟙 _)`).

`IsCoarseModuliY0` itself has NO surjectivity field — `classify` is data plus
naturality plus initiality — so these two are theorems about a presentation
(`Gamma0GITPresentation`), not clauses you can project out. Look for them by
name; the structure will not tell you they exist.

With them, `noFixedModuliPoint_atkinLehner_x0OneSixtyNine` went from an atomic
leaf to a 20-line proof over one residue leaf, **net zero on the frontier**:
precompose the fixed-point equation with `specAlgClos ℚ`, lift the point to a
datum, apply the `IsAtkinLehner` pin, cancel `jY` (an open immersion, hence
`Mono`, so `cancel_mono` applies), and read off `d ≅ d'`. What is left is
`h(−676) = 6` and nothing else.

Two traps met on the way:

* `IsAtkinLehner` says **nothing** about `w` at a moduli point until you hand
  it an `N`-isogenous partner, so any such reduction is forced to consume
  `exists_isNIsogenyPair`. That is not an extra gate when the consumer already
  runs through `exists_atkinLehner_x0`, but it does mean the reduction cannot
  be made independent of it.
* `sectionAlong jY h y` and `RelPoint.post jY h y` are the same term; drop to
  `.1` with `congrArg Subtype.val` and the whole argument becomes associativity.

See also [[flt-two-leaves-may-be-one]] and [[audit-searched-production-not-invariant]].
