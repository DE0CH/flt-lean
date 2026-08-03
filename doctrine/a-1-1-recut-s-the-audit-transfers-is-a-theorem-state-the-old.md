## A `1 → 1` RECUT'S "THE AUDIT TRANSFERS" IS A THEOREM — STATE THE OLD LEAF AS A HYPOTHESIS AND PROVE THE CONVERSE
(2026-08-02, `flt-lean-397`, `Mathlib/AlgebraicGeometry/SmoothLocusDescent.lean`.) This file
already says a recut that leaves the count at `1 → 1` must say WHY the earlier faithfulness
audit transfers, and that an audit labelled "inherited" with no argument is a failure mode.
There is a device that turns that sentence into a machine-checked receipt, it costs one extra
declaration, and it has no circularity problem:
    theorem <new leaf> [hyps] : NEW := sorry                      -- the residue
    theorem <old name>  [hyps] : OLD := by … <new leaf> …          -- forward, PROVEN
    theorem <new>_of_<old> [hyps] (h : OLD) : NEW := by …          -- CONVERSE, PROVEN
The converse takes the OLD statement as an **explicit hypothesis**, not as an instance and
not by citing the now-proven theorem, so nothing is circular — it is an ordinary implication
between two propositions, and Lean checks it. Together the two directions say the recut
neither strengthened nor weakened anything, and the next reader can re-run that check instead
of re-deriving the audit. Here it also settled a real question the prose could only assert:
that `ker(T ⊗ I/I² → J/J²)` is *exactly* the kernel of the `H¹` map, so the naive-complex
residue is not a stronger obligation than the `H¹` leaf it replaced.
**Write the converse even when you expect it to be easy — it is where the hypotheses get
audited.** Proving it is what showed `[Module.Flat S T]` is load-bearing for the EQUIVALENCE
(it identifies `ker(T ⊗ cotangentComplex)` with `T ⊗ H¹`) while not being known to be needed
for the truth of either side; that distinction belongs in the leaf's docstring and nobody
would have found it by reading.
**And record the refuted routes ON THE NEW LEAF, not in the commit message.** Three plausible
attacks were checked and killed here (a projectivity-splitting that says nothing about the
kernel; a descent-of-split-injectivity that is circular; and — the sharp one — adding the
consumer's own `[Algebra.FormallySmooth R T]`, which makes the leaf *equivalent to the
consumer's conclusion* and therefore buys nothing). A leaf whose docstring names its dead
axes is the difference between a successor spending a run and spending ten minutes.
### `Algebra.Extension.H1Cotangent.map_eq` IS WHY `H¹` COMPUTATIONS ARE PRESENTATION-FREE
Same run, and it is the one mathlib fact that makes this kind of glue cheap. `H1Cotangent.map_eq
(f g : Hom P P') : map f = map g` — **ANY two homs between the same two extensions induce the
same map on `H¹`**. So a statement about `Algebra.H1Cotangent.map R R S T` (which is defined
through `Generators.defaultHom` between the tautological presentations) may be moved to ANY
convenient presentation in three lines:
    rw [← Extension.H1Cotangent.map_comp]; exact Extension.H1Cotangent.map_eq _ _
and the comparison at the far end is the iso `Generators.H1Cotangent.equiv`. Reach for that
before believing a leaf must be attacked at `Generators.self`. Companion facts, all in
`Mathlib/RingTheory/Extension/Cotangent/Basic.lean`: `Cotangent.map_comp_h1Cotangentι` (the
naturality of `h1Cotangentι`, and it is `rfl`), `h1Cotangentι_injective`,
`exact_hCotangentι_cotangentComplex`; plus `Generators.CotangentSpace.map_toComp_injective`
and `H1Cotangent.map_comp_cotangentComplex_baseChange` in `Kaehler/JacobiZariski.lean`.
**Lean trap that cost one round: `Function.Injective f` unfolds to `∀ a b, f a = f b → a = b`,
so `intro z hz` on such a goal gives you `hz : T ⊗ M` (a second point) and not `f z = 0`.** For
a linear map use `rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]; intro z hz;
rw [LinearMap.mem_ker] at hz` — the error otherwise is a `rewrite` failure quoting a pattern
`?f 0` against a TYPE, which reads as a unification problem and is not one.
