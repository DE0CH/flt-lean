## A "FALSE AS STATED, REPAIR QUEUED" AUDIT MAY BE DESCRIBING A REPAIR THAT ALREADY LANDED — the leaf is DISCARDING it, not missing it
(2026-07-31, `HilbertModularity.lean`, `exists_hilbertAuxDiamondGenerators`.) The
section below is about a decomposition putting a hypothesis on the wrong half. This
is the commoner and cheaper variant: a decomposition **drops a hypothesis entirely**,
and the FALSITY AUDIT copied onto the child then reads as an open cut-level task.
That leaf was cut out of `exists_hilbertAuxDiamondQuotient_of_exponents` on
2026-07-31 and carried, verbatim, an audit saying its control clause is FALSE —
refuted by the power-series inflation `𝒟Q.R⟦y_1, …, y_N⟧`, which weak universality
does not exclude — and that "the repair is to transport the 2026-07-26
`IsTraceGenerated` repair to `HilbertAuxDeformationDatum`; **it is queued as one
owned cut-level task**". The audit's mathematics is right. The task does not exist:
`HilbertAuxDeformationDatum.IsTraceGenerated` had been defined on 2026-07-30, and
**the sole call site was already holding `h𝒟Qt` and passing it nowhere.** The whole
repair was one binder on two declarations and one argument at one call site.
So, before queueing (or accepting) a repair a docstring names:
* **grep for the repair, not for the leaf.** One `grep -n 'IsTraceGenerated'` over
  the file answered it. An audit is written at the moment the defect is seen and is
  never revisited when the fix lands somewhere else in the same file.
* **diff the leaf's binder list against its CALLER's.** This project's own standing
  observation — *the missing hypothesis is usually already in the caller's hand* —
  has a sharper form for freshly-cut leaves: a cut copies the parent's binders BY
  HAND, so a binder the parent had and the child lacks is a transcription loss, not
  a design decision. Here `h𝒟Qt` was the only difference between the two lists.
* **a task prompt saying "the second clause is FALSE, do not attempt it" is
  evidence about the version the queue was written against.** Mine did, and by the
  time it arrived the clause was one binder from true. Losing that would have cost
  the whole run, because the leaf cannot be cut at all while half of it is false.
Corollary for whoever writes such an audit: name the repair as a DECLARATION
(`add h𝒟Qt : 𝒟Q.IsTraceGenerated`), not as a project ("transport the repair"). The
first is refuted by the next reader in ten seconds; the second survives for days.
### The release-snapshot olean verifies a NEW block in seconds even when the file has moved on
Same run, measured: `HilbertModularity.lean` was ~4 000 lines and one release ahead
of `~/.flt-release-lake/build`, and the full cone rebuild ran for hours. The new
cluster — one leaf, three proven lemmas, a restated leaf over the file's own
`HilbertAuxDeformationDatum`, and the whole glue proof — was verified in **7
seconds** by a scratch that `public import`s the module and restates everything
under primed names, compiled against the SNAPSHOT's olean.
That works, and is sound, exactly when **every name the block references predates
the snapshot** — check each with `git show <snapshot-sha>:<file> | grep -c '<name>'`
rather than assuming. Here one name (`HilbertAuxDeformationDatum.IsTraceGenerated`)
did not, so it was dropped from the scratch's copy and everything else was checked;
the residual risk was one binder of an existing `def`. Mirror the target's
`namespace`, its `open` lines and its `local notation3` block verbatim — those are
what the scratch is really testing, and they are what a hand-written minimal import
list gets wrong.
