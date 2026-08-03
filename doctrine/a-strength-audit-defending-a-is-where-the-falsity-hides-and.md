## A "STRENGTH AUDIT" DEFENDING A `∀` IS WHERE THE FALSITY HIDES — AND WEAKENING THE QUANTIFIER COSTS THE CONSUMER NOTHING
(2026-07-31, `flt-lean-17`, on `exists_hilbertAdZeroTrivializing_notMem_range_sub`
in `HardlyRamified/HilbertModularity.lean`.)
This file already says a FALSITY AUDIT is binding and a ROUTE is a hypothesis.
There is a third kind of paragraph, and it is the one to distrust most: a
**STRENGTH AUDIT**, which explains why the leaf may quantify universally over an
object the consumer only ever supplies ONE of. The one here read
> The leaf quantifies over EVERY `σ` in the Taylor–Wiles locus, where the
> consumer needs only the one `σ` it happens to produce. That is deliberate and
> classically free: the argument above is uniform in `σ`, using only that `σ` is
> regular semisimple …
Both halves are wrong, and the leaf was FALSE. A strength audit is a claim that
the CLASSICAL argument is uniform in the quantified variable; it is written by
whoever cut the leaf, before anyone tried, and it is never checked, because it
reads as a note about generality rather than about truth.
**THE CHECK IS TO INSTANTIATE THE QUANTIFIER AT THE EXTREME THE HYPOTHESES
ALLOW AND COMPUTE THE CONCLUSION.** Here the conclusion asks for
`z τ ∉ (ρ σ − 1)·M`, so it is UNSATISFIABLE the moment `ρ σ − 1` is surjective —
and one eigenvalue computation settles when that is: with
`charpoly(ρbar σ) = (X − α)(X − β)`, `α ≠ β`, the twisted adjoint `ρ σ : m ↦
det(ρbar σ)·(ρbar σ) m (ρbar σ)⁻¹` acts on the three-dimensional `ad⁰ρbar(1)`
with eigenvalues `αβ`, `α²`, `β²`. So the leaf needs `αβ = 1` (i.e.
`det ρbar σ = 1`) or `α² = 1` or `β² = 1`, and membership in the locus does not
give any of them. **A conclusion of the form `x ∉ range f` is a properness claim
about `f`; price it before believing any uniformity.**
**AND CHECK THE LEVEL-INDEXED HYPOTHESIS AT ITS DEGENERATE LEVEL.** The clause
that classically supplies `det ρbar σ = 1` is "σ fixes the `ℓⁿ`-th roots of
unity". At `n = 0` that reads `∀ ζ, ζ ^ 1 = 1 → σ ζ = ζ` and is **VACUOUS** —
`ℓ ^ 0 = 1`. Every `μ_{ℓⁿ}`-, `mod ℓⁿ`- or `Iⁿ`-indexed hypothesis in this
development has an `n = 0` instance that asserts nothing; a leaf quantified over
all `n` must be true there too. This is the cheapest single instantiation there
is and it refuted the leaf on its own.
**THE REPAIR THAT CANNOT BE WRONG: WEAKEN `∀ σ` TO `∃ σ`.** Both defects (the
properness above, and the separate fact that Wiles Ch. 3 / DDT §2 *choose* `σ`
after the cocycle — necessary, since `ad⁰ρbar` is REDUCIBLE for a dihedral
`ρbar`, which is absolutely irreducible) are defects of the QUANTIFIER. `∃ σ` is
implied by `∀ σ` plus nonemptiness of the range, so the restatement is a strict
WEAKENING: every earlier audit transfers, no consumer can be broken, and you owe
no arithmetic counterexample — which matters, because exhibiting one here would
have needed a nonzero class in a Selmer group that nothing in this tree
constructs. **Weakening a quantifier is available whenever the consumer picks the
witness itself**, and the consumer's edit is one `obtain`.
**WHEN YOU DO IT, HAND THE OLD SUPPLIER'S OUTPUT INTO THE NEW LEAF.** The
consumer used to call `exists_hilbertFixing_rootsOfUnity_charpoly_split` for its
`σ`; after the restatement it does not, so that call had to move INTO the new
theorem's proof, where it supplies a `σ₀ ∈ locus` that the residual leaf takes as
a HYPOTHESIS. Otherwise the supplier is orphaned — the hazard already recorded
under `[[flt-hoisted-leaf-orphaned-by-reproof]]` — and the residual leaf is made
to re-prove nonemptiness it has no business owning.
### The glue this buys, and why the decomposition is worth the extra leaf
Restating let the node be CUT along the seam the classical proof actually has,
with the join proven rather than described: the values of `z` on the subgroup
`N = {x | ρbar x = 1 ∧ x fixes μ_{ℓⁿ}}` — the formal stand-in for `Γ L`, built as
a `Subgroup` so no field `L` and no fixed-field dictionary is needed — span a
`Γ F`-stable subspace, because `N` is NORMAL and `ContinuousCohomology.eval₁_conj`'s
correction term `z g − ρ(gτg⁻¹)(z g)` then vanishes. The residue is two leaves
with nothing in common: the cohomological half (`H¹(Gal(L/F), ad⁰(1)) = 0`, where
`hc0`/`hcunr`/`hirrF`/`ℓ ≥ 5` are spent and total realness is NOT) and the
adapted choice of `σ` (where both defects above live). Count for the module:
`301 → 301`, unchanged — one false leaf became a proven theorem, one false DEAD
leaf was deleted, two true leaves opened. **Say the count did not move**; a recut
is judged by what is LEFT in each leaf.
### Rider: a repaired statement can leave its PRE-REPAIR copy behind, as a dead FALSE leaf
`nonempty_inter_hilbertSurvivingLocus_hilbertTaylorWilesLocus` was the same
statement as `exists_mem_hilbertSurvivingLocus_inter_hilbertTaylorWilesLocus`
**minus `[NumberField.IsTotallyReal F]`** — i.e. exactly the form the latter's own
2026-07-30 FALSITY AUDIT refutes with the `54b1` witness. It survived the repair,
had ZERO consumers, and every instrument called it ordinary open work.
Two tells, both free. `dupstmt.py` cannot see it (the two statements differ by an
instance binder, so they are not duplicates); what CAN is that **the parent's
docstring named it while the parent's BODY called something else** — the
`[[flt-parent-docstring-vs-proof-body]]` signature, here marking a superseded cut
rather than a duplicated one. And the comment-stripped consumer grep: a leaf whose
only occurrence in code is its own declaration line is dead. **When a leaf is
repaired by ADDING a hypothesis, grep for the old statement**: the repair usually
lands as a new declaration beside the old one, and the old one is then false, dead
and permanently dispatchable.
