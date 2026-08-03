## A FAITHFULNESS REPAIR IS NOT INHERITED BY THE TWIN — GREP FOR THE OTHER LEVEL

(2026-07-31.) This development is full of statements that exist at TWO levels — `ℚ` and `F`,
bottom and raised, `Deformation.lean` and `HilbertModularity.lean`, `Patching.lean` and its
Hilbert twin. When a falsity audit repairs one, **the twin is repaired only if somebody goes and
does it**, and nobody is assigned to. The gap is invisible to every mechanical check: both
statements compile, both are sorried, both look audited, and the repaired one's docstring reads
like it covers the family.

Concretely: `HilbertModularity.lean`'s own 2026-07-26 audit established that
`IsWeaklyUniversal` does **not** pin a deformation ring — `R⟦X⟧` with the pushed-forward
representation is another weakly universal datum — and repaired the bottom level by adding
`HilbertDeformationDatum.IsTraceGenerated`. That audit even records that `Deformation.lean` had
made the same repair a day earlier and *this module did not inherit it*. Five days later the
raised-level structure `HilbertAuxDeformationDatum` still had no trace-generation notion at all,
so four raised-level leaves bounding the number of generators of `R_Q` were FALSE by the same
witness — refuted by `𝒟Q.R⟦y_1, …, y_N⟧` for `N > q`, every hypothesis satisfied.

So: **when you read a FALSITY AUDIT, immediately grep for the twin statement and check whether the
repair reached it.** Two greps, and it is the cheapest false leaf you will ever find — the audit
has already done the mathematics for you, and the only question is whether the hypothesis is
present on the other side. In the instance above the audit's own text named the witness, named the
repair, and named the module that had missed it; nothing was left to discover except that it had
happened a second time one level down.

Corollary for the shape of the repair, and it is why these gaps persist: transporting an audit is
usually a **cut-level change** — one new predicate, a hypothesis added to every affected leaf, the
hypothesis threaded down a chain of consumers, and one PRODUCER at the terminus that stops being
provable. That is many signatures across one large file, i.e. exactly the interface-split hazard of
the class-7 section above, so it must go to ONE owner doing nothing else. An agent that finds the
gap mid-task should write the audit into the docstrings, name the terminus, and queue the repair —
not start threading it alongside other work.

