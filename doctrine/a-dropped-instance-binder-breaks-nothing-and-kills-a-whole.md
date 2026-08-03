## A DROPPED **INSTANCE** BINDER BREAKS NOTHING AND KILLS A WHOLE ROUTE INSIDE THE LEAF
(2026-08-02, `flt-lean-347`, `exists_hilbertAuxDiamondGeneratorsPinned` in
`HardlyRamified/HilbertModularity.lean`.)
That leaf's docstring flagged, in bold, **THE STEP TO CHECK**: its wild-inertia
clause is derivable only if `1 + 𝔪_{R_Q}` is pro-`ℓ`, which needs
`(ℓ : R_Q) ∈ 𝔪`, i.e. residue characteristic `ℓ` — and it observed, correctly,
that `HilbertAuxDeformationDatum` "posits only `Algebra ℤ_[ℓ] R` and
`π : R →+* k` surjective; it does NOT state `CharP k ℓ`". It concluded that if
the fact is not derivable then **"the honest repair is a field or a hypothesis"**
on the structure.
**The fact was PROVEN in the same file, ~1700 lines above, and had been for two
days**: `natCast_eq_zero_of_hilbertAuxDeformationDatum`. What hid it is that the
lemma takes `[Finite k]`, and the six-declaration diamond chain
(`…GeneratorsPinned → …Generators → …Quotient_of_exponents → …Quotient →
…Control → …RingPresentation`) does not carry it — while
`exists_hilbertTaylorWilesAuxLevelData`, the declaration at the TOP of that
chain, does. A cut copies binders by hand; this one dropped the instance on the
way down. Adding it back to all six changed **no call site**, because instance
search finds it at every one.
**This is a sharper failure than dropping an explicit hypothesis, and the
sharpness is the point.** A missing explicit hypothesis usually breaks
something — a call site, a proof, a build. **A missing INSTANCE binder breaks
nothing.** The leaf stays true, stays sorried, stays consumed, and every consumer
still elaborates, because the caller had the instance and nobody asked for it.
Its only effect is that a route becomes unavailable *inside* the leaf — and the
next author, finding the route blocked, writes the blockage down as a defect of
the STRUCTURE rather than of the binder list. That verdict then propagates: this
one had reached a task prompt as a standing warning.
**Two checks, one command each:**
* before believing "the structure does not state `P`", grep the FILE for `P`
  itself — `grep -n 'natCast_eq_zero\|CharP k' <file>` settled this in seconds.
  The standing rule that an absence claim is scoped to the import cone applies
  here at the smallest possible scope: the same module;
* when a leaf is cut out of a parent, **diff the binder lists INCLUDING instance
  binders.** CLAUDE.md already says the missing hypothesis is usually already in
  the caller's hand; instance binders are the half of that nothing enforces,
  because their absence is silent in both directions.
**The repair shape, once the fact is available: WEAKEN the leaf's clause and
recover the strong one in the glue.** The leaf was asking a prover to hand back
`χ i x = 1` for `x` wild — a statement about the pro-`ℓ` structure of `1 + 𝔪`
that a prover would have had to rebuild. It now hands back only RESIDUAL
triviality (`χ i x - 1 ∈ 𝔪`), which is what `ρbar` unramified at `Q` gives
directly, and `exists_hilbertAuxDiamondGenerators` recovers the strong clause in
four lines over four new PROVEN lemmas. Count `1 → 1`; what left the leaf is
~150 lines of local-ring and wild-inertia argument. Judge it by what is LEFT.
The four lemmas are worth knowing separately, since every `1 + 𝔪` argument in
this development needs them: `ℓ ∈ 𝔪` from `[Finite k]`; one filtration step
`y ≡ 1 mod 𝔪^{n+1} ⟹ y^ℓ ≡ 1 mod 𝔪^{n+2}` via the EXACT identity
`y^ℓ − 1 = ℓ·(y−1) + (y−1)²·c` (no binomial coefficients — `c` comes from
`∑_{i<ℓ} y^i − ℓ = ∑_{i<ℓ}(y^i − 1)` being divisible by `y − 1`, then
`geom_sum_mul`); its iterate; and the pro-`ℓ` statement, whose separatedness is
`IsHausdorff.haus`. Note the divisibility in the last one must be **by elements
of `1 + 𝔪`** — an arbitrary unit `ℓ^e`-th root does not advance the filtration —
and in the application that is free, because the roots are values of the same
character at wild-inertia elements.
