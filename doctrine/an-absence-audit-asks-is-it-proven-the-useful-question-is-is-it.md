## AN ABSENCE AUDIT ASKS "IS IT PROVEN"; THE USEFUL QUESTION IS "IS IT ALREADY A LEAF"
(2026-07-31.) `X0.lean`'s `exists_heckeCorrespondenceFamily` carried a careful audit concluding
that `IsGamma0Isogeny` cannot be inhabited: Vélu produces a map of POINT GROUPS, the field wants
a morphism of SCHEMES, and "nothing in this development turns a homomorphism of geometric point
groups into a morphism of abelian schemes". Every clause was true, and the audit even named the
three obligations a coordinate-level route would face, one of which — a scheme-theoretic kernel
condition holding over EVERY test scheme, non-reduced ones included — it called uncheckable.
That exact condition is **asserted 22 600 lines below in the same file**, by `exists_isNIsogenyPair`,
whose whole universal-property layer (`epi_of_isNIsogenyPair`, `exists_factor_of_isNIsogenyPair`,
`existsUnique_factor_of_isNIsogenyPair`, `nonempty_isBaseChangeOf_of_isNIsogenyPair`) is PROVEN and
most of which landed *after* the audit was written. Applied at a cyclic subgroup of order `ℓ` it
supplies six of `IsGamma0Isogeny`'s seven fields.
**Why no ordinary check catches this.** The audit searched for something to USE — i.e. something
PROVEN — and an open `sorry` leaf answers that with "no". But "is it proven?" and "is it available
as a reduction target?" are different questions, and only the second one matters when the thing you
are writing is itself a leaf. Reducing a second theory gate onto an existing one is real progress —
it halves what a prover has to build, and it settles the vacuity hedges that hang off the unknown
gate — even though the leaf COUNT does not move, which is why a frontier-number-driven reading of
the work will score it at zero.
Two riders, both of which decided this case:
* **Grep the file's own leaf statements for the CONCLUSION**, not the libraries for a proof. The
  absence tables in this development are stamped to a commit and search `Fermat/`, mathlib and
  `~/cs/FLT` for a *usable* declaration; none of them asks whether the neighbouring `sorry` already
  says it.
* **Then check DECLARATION ORDER, because that is what prices the merge.** Here the shared statement
  has to be phrased in `Gamma0Datum`/`CyclicSubgroupOfOrder` (both defined near line 1000) so it can
  sit above `IsGamma0Isogeny` at ~43189, since `IsNIsogenyPair` is defined at ~65567 — below one of
  its two consumers. A reduction that would need a hoist instead of a restatement is a different,
  much more expensive task in a file with a dozen concurrent editors.
