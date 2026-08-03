## false leaves and underdetermined structures

(Cut verbatim out of CLAUDE.md's `THE GOAL: fully formalize Fermat's Last Theorem, no sorry, n` section at the 2026-08-03 doctrine split; nothing reworded.)

**FAITHFULNESS: a leaf can be FALSE AS STATED, and that is worse than open.**
Three were found and corrected on 2026-07-25 alone. A false leaf can never be
proven, and anything derived from it is worthless — so when a leaf resists,
seriously consider that it may be false rather than merely hard. Refuting one
with an explicit counterexample and restating it correctly is a FULLY successful
outcome; say so in task prompts.

**THERE IS A THIRD OUTCOME, and this development's axiomatized structures produce
it regularly (2026-07-31).** When a leaf is stated over a `structure` that
AXIOMATIZES an object rather than over a construction, it can be neither provable
nor refutable: **the axioms simply do not determine the object where the leaf
looks.** `le_fixedSubmodule_gp_of_mem_Ioo` in `ArtinConductor.lean` was exactly
this — `RamificationFiltration.gp_herbrand` pinned the upper-numbering filtration
only AT the Herbrand values, and inside the gaps the axioms left a sandwich whose
BOTH ends are admissible. Probing with other levels is circular, because the axiom
relates every level to `F` and no two levels to each other. No counterexample can
be exhibited in-tree either, since refuting a `∀ F` needs a filtration built over
an arbitrary `Kᵥ`. So the leaf sits there forever, looking merely hard.

The repair is to the STRUCTURE, and there are exactly two checks that turn it from
a dodge into a decision:

1. **Does the CONSTRUCTION that inhabits the structure satisfy the stronger axiom
   for free?** If it needs new input, the strengthening is a disguised `sorry` and
   the answer is no. (Here it was `iInf_le` one way and the ALREADY-OPEN leaf at
   the interval's right endpoint composed with antitonicity the other — zero new
   leaves.)
2. **Which direction do consumers use the structure in?** Strengthening SHRINKS
   the admissible class, so `∀ F` theorems get weaker and `Nonempty` gets harder.
   Get this backwards and you have quietly weakened a theorem instead of
   sharpening a model. (Here `IsSwanExponentAt = Nonempty ∧ ∀ F, …` and every `F`
   reaching a proof comes from the construction, so both halves were safe — and
   faithfulness improved, the genuine object being a singleton.)

Record it as a numbered FALSITY AUDIT in the structure's own docstring, KEEP the
analysis that showed the old axioms insufficient (it is the evidence for the
repair, and without it the next reader sees only a convenient axiom), and correct
in place any route the leaf's docstring proposed that you found does not work.
Often the structure's own audit has already named the repair — this one had.

The discriminating rule for the commonest trap in this development, from a sweep
of every `𝒪ᵥ`-rational group-scheme leaf (2026-07-25): **over `𝒪ᵥ`, identities
and VALUES descend from `𝒪^nr` (flatness/torsion-freeness, and inertia fixes
`𝒪^nr` pointwise); the EXISTENCE of a coordinate or a normal form does not.** A
leaf is faithful exactly when it asks for a value or an inertia-only
equivariance, and false exactly when it asks for an element of `G` or for
`Γ`-wide rationality. Two corollaries: unramified twists are invisible to
inertia, so inertia-only conclusions are twist-blind; and étale-by-étale is
étale, so the dual/Selmer arguments are twist-blind too. `exists_muType_closure`
died on precisely this — it demanded the μ_p-coordinate over `ℤ_p`, but the
connected order-`p` schemes there are the `p−1` unramified twists `μ_p ⊗ ψ`,
each satisfying every hypothesis with no such coordinate when `ψ ≠ 1`.

Corollary for REVIEWERS: watch for a quantifier over `localInertiaGroup` being
"generalized" to all of `Γ`. `exists_localTorsionQuotient_of_good_ordinary` is
true only because `σ` ranges over inertia — the étale quotient at good ordinary
reduction carries the *unramified* character `α`, trivial on inertia but not on
Frobenius — and widening it makes the leaf false for every curve with `α ≠ 1`.

