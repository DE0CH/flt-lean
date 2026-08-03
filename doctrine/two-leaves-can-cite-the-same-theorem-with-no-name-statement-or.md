## TWO LEAVES CAN CITE THE SAME THEOREM WITH NO NAME, STATEMENT OR TYPE IN COMMON

(2026-07-31, `X0.lean`, found while working `exists_dedekind_rigidifiedModuli`.) A leaf stated
at a **base variable** and a leaf stated at a **specific base** can carry the identical piece of
mathematics while sharing nothing a checker compares. `isAffine_rigidifiedModuliSchemeData_of_isUnit`
asks for Katz–Mazur (8.1.1) over any `R` with `n`, `N` invertible; `exists_dedekind_rigidifiedModuli`
asked for it again at `R = ℚ`, along with (4.7.2), (5.1.1)+(6.6.1) and (6.6.2) — all four of which
the base-general family already owed. Different names, different statements, different types, one
`Nonempty`/one `∃`. `dupstmt`, `xdup`'s qualified pass and `dedup_cross` all pass; a frontier scan
counts two honest leaves; `own.py` and `leafstat.py` both say "open and unowned", which is true and
useless. **Closing either one would have left the other open with nothing left to prove** — the
`Chebotarev.lean` failure mode, but manufactured inside a single file by two correct cuts made a
day apart.

**The signal that did exist, and it is the only one: the docstring named a route the BODY did not
take.** `exists_isAffine_rigidifiedModuliScheme`'s docstring said "PROVEN over the base-general
citation leaf `exists_rigidifiedModuliSchemeData_of_isUnit` above" while its body went through the
fused `ℚ` leaf instead — a fusion made the next day rewired the proof and left the paragraph. That
is the same shape as `parent-docstring-vs-proof-body-names-duplicate`, and it generalises:

> **When a declaration's docstring names its route, `grep` the route's name in the PROOF BODY.**
> A route claimed and not taken means some other declaration is now carrying that content, and the
> two are invisible to each other.

Two corroborating cheap checks, both of which fired here and neither of which is in any script:

* **A PROVEN theorem with no consumer is evidence of a duplicate, not just of floating code.**
  `exists_rigidifiedModuliSchemeData_of_isUnit` had been proven for a day with zero uses. The
  free-floating rule would eventually have deleted it; the right reading was that its consumer
  had been re-routed through a rival cut.
* **A section comment that states an intention is a claim to verify.** The base-general family's
  own header said it had been hoisted "thereby to subsume the `ℚ` leaf as well as the `𝔽_ℓ` one".
  Nobody had checked whether the subsumption was actually taken, and it was not.

**The repair shape, when you find one: a HYPOTHESIS, not a deletion.** Add the duplicated content
to the redundant leaf as a hypothesis (`hne : Nonempty …`) and discharge it at the call site from
the surviving leaf. The leaf keeps its name, its signature is only weakened, every consumer keeps
compiling, and the frontier count does not move while the citation strictly shrinks. `X0.lean`
already had the pattern in its `𝔽_ℓ` twin (`exists_isAffine_rigidifiedModuliScheme_specF`), whose
docstring explains exactly why: stating the `∃` unconditionally "would ALSO assert representability
and would therefore subsume" the representability leaf. Adding a hypothesis cannot make a true
leaf false, so the audit for such a re-cut is short — but CLAUDE.md still requires it to be
WRITTEN, against the composite, because the earlier audit's reasons may no longer hold. Here
`hn : 3 ≤ n` was demoted from load-bearing-for-truth to load-bearing-for-the-citation (under the
new hypothesis the `n ≤ 2` case is vacuous rather than false) while `hN : 0 < N` survived intact.

### THE SWEEP WAS RUN OVER ALL OF `X0`+`X1` (2026-08-02) — NEGATIVE, and here is the discriminator

All **125** open leaves of `X0.lean` (101) and `X1.lean` (24) were extracted with their
docstrings, grouped by CITATION, by the structures named in their CONCLUSION, and by BASE tag
(`SpecQ` / `SpecF` / `SpecLoc` / `ZMod` / `[Field K]` / `[CommRing R]` / `IsUnit (n : R)`), and
every group with two leaves at two bases was read. **No further instance survives.** Do not
re-run the citation grouping; re-run the discriminator below on anything new.

**THE DISCRIMINATOR, which is what the original find lacked and what makes this checkable rather
than a matter of taste: a candidate pair (general leaf `G`, special leaf `S`) is an INSTANCE iff
`G`'s HYPOTHESES HOLD at `S`'s instantiation.** One line per hypothesis. Both of the two serious
candidates died exactly there, and neither death is visible from the citation or the statement:

* `exists_gamma0AtlasOver_bcQuotient_of_flat` (any `f : R →+* R'` with `f.Flat`) versus
  `exists_gamma0AtlasOver_bcQuotient_specLocSpecial` (`ℤ_(ℓ) → 𝔽_ℓ`). Same object, same
  operation, same citation — Katz–Mazur **(8.1.6)(2)** — and the specific base is **not flat**.
  Katz–Mazur Remark (8.1.7) gives the counterexamples at exactly that base change, and `ℓ` need
  not be prime to `#GL₂(ℤ/n)` either. Two genuinely different theorems.
* `exists_integralHeckeEigensystem_of_isWeightTwoEigenform` (`Γ₀`) versus
  `…_of_isWeightTwoEigenformOn_gamma1` (`Γ₁` with nebentypus). **Character-for-character the same
  conclusion**, `Nonempty (IntegralHeckeEigensystem a)` about the same `a`, and the same citation
  (Shimura §3.5/§7.5, Diamond–Shurman §6.5). Still not an instance: `f` lives on a smaller group
  and `hecke` carries `χ`, so the `Γ₀` producer does not apply; and the reverse is blocked by
  IMPORT ORDER, since `IsWeightTwoEigenformOn` is declared in `X1.lean`, downstream. The content
  that is genuinely shared — the consumer, which mentions only `a` — **has already been factored
  out**, which is the right resolution and is why this pair is healthy.

Two structural facts worth keeping, because they are what make the sweep cheap next time:

* **`X1` `public import`s `X0`.** So a `Γ₁`/`X1` leaf can be discharged by an `X0` leaf and never
  the other way. Any candidate whose general side is in `X1` is blocked by import order before
  any mathematics is looked at — check the direction first, it costs one `grep`.
* **The `Γ₀`/`Γ₁` twin axis is already swept and is largely self-documenting**: 16 of the 24
  `X1` leaves cross-reference `X0` by name in their own docstrings, and the file's standing rule
  ("a cut made on one side must be made on the other by ONE owner") is being followed. The eight
  that do not are listed in the queue entry this sweep left.

**A `∀`-defended rigidity corollary is where the orphans land, and there are three.**
`isAffine_of_isAffine_rigidifiedModuliScheme`, `nonempty_iso_rigidifiedModuliSchemeData` and
`exists_isIso_of_rigidifiedModuliSchemeData` are all PROVEN with **zero** consumers tree-wide —
the "its consumer was re-routed through a rival cut" signal, firing correctly: the 2026-07-31
fusion re-pointed the `ℚ` side at the base-general leaf and left the corollaries behind. The
first one's consumer even re-derives its three lines inline. **None of them can be consumed
without a RELOCATION** — the consumer is declared above the corollary, and the corollary rests on
a namespace block below the consumer — and the corollary is strictly STRONGER (it carries neither
`0 < N` nor `3 ≤ n`), so the delegation does not run the other way either. Documented in place;
queued as a block move, which buys no leaf and is the highest-conflict edit in that file.

**Method note, since two of the four prescribed methods produced nothing.** Grouping by citation
and by conclusion-structure did all the work. "Docstring names a route the body does not take"
produced one hit and it was an artefact — and the artefact is worth knowing about: a
`strip_comments` that blanks the NEWLINES inside block comments silently shifts every line number
it reports, so a scan built on one pairs the right NAME with the wrong LINE and every hit reads as
a misattribution. Preserve `\n` when masking comments; `frontier.py` does, hand-rolled scanners
routinely do not.

