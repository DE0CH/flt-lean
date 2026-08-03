## A "MISSING THEOREM" MAY BE A MISSING *IMPORT OF YOUR OWN PACKAGING* — check the TYPE, not the structure

(2026-07-31, `X1.lean`.) `integral_Ioi_one_sub_frickePartner_ne_zero_x1TwentyFive`'s docstring
named its own next cut, in terms: "`frickeSlashOn 25 _ _ _ f` MUST BE GIVEN A `q`-EXPANSION …
that is the natural next CUT, and it is the classical statement `W_N : S₂(N, χ) → S₂(N, χ̄)`".
The reasoning was explicit and looked airtight: *every* route to a series for that integral runs
through `hasSum_axisRestrictOn`, whose only input is `IsWeightTwoEigenformOn`'s `qExpansion` and
`qExpansionSummable` fields, and nothing attaches either to a Fricke transform.

Every clause of that was true, and the conclusion was still wrong. **It read a limitation of this
file's PACKAGING as a limitation of the mathematics.** A `q`-expansion is not an eigenform
property — it needs periodicity, holomorphy and boundedness at `i∞`, which is exactly what the
TYPE `CuspForm G 2` already carries — and mathlib's `UpperHalfPlane.hasSum_qExpansion` supplies it
for any of them. Six lines of transport (`hasSum_qExpansion_cuspFormOn`) discharged the obligation
that had been costed at one Atkin–Lehner leaf. The Atkin–Lehner statement is still owed, but only
for what it was always really needed for — IDENTIFYING the coefficients as `λ·conj(aₙ)` — which is
a strictly smaller thing than "give the partner an expansion". Two obligations that looked like one.

The check is one question, and it is cheap: **is the property you are about to cut a property of
the OBJECT'S TYPE, or of the bespoke structure this development happens to carry it on?** If the
former, grep mathlib for it before writing the leaf. The trap is sharpest exactly where a project
structure bundles a general fact as a *field* — `IsWeightTwoEigenformOn.qExpansion` is a field
because eigenforms need the coefficients NAMED, not because cusp forms lack expansions — since
after that the general fact is invisible to anyone reasoning from the structure outward.

Related and same day, a Lean-level trap worth its own line. **A conclusion mentioning
`(qExpansion 1 F).coeff (n + 1)` where a consumer wants `b (n + 1)` makes every application a
NON-PATTERN higher-order unification** (`?b (n + 1) ≡ coeff (n + 1)`), which does not terminate
inside the default heartbeat budget — it presents as `(deterministic) timeout at whnf`/`isDefEq`
on a one-line `exact`, and raising `maxHeartbeats` tenfold does not help. The fix is to abstract
the sequence into a parameter and pass the identification as a hypothesis:
`(hb : ∀ m, b m = (qExpansion 1 F).coeff m)` with `simp only [hb]` as the first proof line. Every
application is then first-order and instant. Suspect this whenever a timeout appears on a term
whose pieces all elaborate fine alone.

