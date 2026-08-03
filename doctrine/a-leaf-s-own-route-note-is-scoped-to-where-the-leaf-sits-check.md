## A LEAF'S OWN ROUTE NOTE IS SCOPED TO WHERE THE LEAF SITS — check declaration ORDER before believing "must be written here"

(2026-07-31, `exists_stepanovJetLinearForms` in `MoretBailly.lean`.) The leaf's docstring said
the weighted-degree bookkeeping "has to be written here". It does not: `stepanovTotalFilt` and
the whole `StepanovFilt` calculus — `mem_add/_sub/_mul/_sum/_prod/_det`, `lift`, and even
division by a monic `F` with the filtration preserved (`stepanov_exists_wd_rem`) — already
existed, **1600 lines BELOW the leaf in the same file**, together with the entire
`stepanovDerivX`/`stepanovJet` API the leaf's four proof steps run on (another 2100 lines down,
including a fully proven `stepanov_jet_dvd_core`).

So the leaf was not missing machinery; it was **positioned above it**. Every "MISSING AT THIS
PIN" and "has to be written here" claim in a route note is implicitly *as of this line number*,
and line numbers move under merges while the prose does not. A `grep` that finds the name and
stops has confirmed existence, not USABILITY.

The check is one command and belongs in every scoping pass, before any Lean is written:

    grep -n '<the machinery>\|<your leaf>' <file>     # compare the LINE NUMBERS

If the machinery is below, the first move is a HOIST, not a proof — and the hoist is its own
verified step, because a several-hundred-line move in a file with concurrent editors is exactly
the merge shape the class-7 note above warns about. Budget it separately and say so in the
report; do not start the mathematics on top of an unhoisted base.

Corollary in the other direction, from the same day: the route note for
`exists_irreducible_hypersurface_fractionRing_ringEquiv_rat` predicted its last step would be
"several lemmas, not one", and it was four lines — because `Module.Finite.of_isLocalization` is
registered in mathlib as an INSTANCE at exactly the pair wanted. **Route notes are estimates made
without the compiler. Re-price both directions before trusting one.**

### Two mathlib techniques from that proof, both reusable in this development

- **Use `IsField` as a PROP; never install `IsField.toField`.** Adding a `Field` instance to a
  ring that already has a `CommRing` from elsewhere (a `Localization`, a quotient) puts a second
  ring structure in scope and makes every later instance unify through structure eta.
  `IsField.mul_inv_cancel` is a plain existence statement and is usually all that is wanted.
- **To show a localisation at a SMALL submonoid is already the whole fraction ring**, do not
  prove it is a field and transport: use `IsLocalization.isLocalization_of_is_exists_mul_mem`,
  whose hypothesis is `∀ x ∈ S⁰, ∃ m, m * x ∈ M`. Combining `IsField.mul_inv_cancel` with
  `IsLocalization.surj` produces that `m` directly, and the result is `IsFractionRing S
  (Localization M)` with no field structure anywhere in the proof.

