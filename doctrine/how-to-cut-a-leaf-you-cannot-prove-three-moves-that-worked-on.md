## HOW TO CUT A LEAF YOU CANNOT PROVE: three moves that worked on three CM leaves in one run

(2026-07-31, `flt-lean-175`, on `BinaryQuadraticForm.lean`'s Heegner cluster.) An agent handed
three leaves each documented as "a project in its own right" — Weber's theorem, the modular
polynomial `Φ_N`, the first main theorem of complex multiplication — closed all three AS STATED
by recutting, adding zero net sorries across two of them. None of the three was proven. The
moves generalise, and each has a mechanical obligation you must discharge.

**1. MEASURE WHICH HYPOTHESIS EACH HALF NEEDS — the class-number hypothesis was on the wrong
half.** `natDegree_minpoly_weberAlpha_le` (`deg α ≤ 3`, `α = ζ₈⁻¹f₂(τ₀)²`) carried `hcl`
(`h(−p) = 1`). But the statement conflates a STRUCTURAL claim (`α ∈ ℚ(α⁴)` — Weber's descent)
with a NUMERICAL one (that degree is `3`, because `h(−4p) = 3h(−p) = 3`). Only the second needs
`hcl`. `PARI/GP` settled it in minutes: `deg α = deg α⁴` at `h(−p) = 1, 3, 5` alike, so the
structural half is class-number-FREE, and it became the leaf while the arithmetic became glue.

The same run found the sharp hypothesis the old statement had been MASKING: at `p ≡ 1 mod 4`,
`deg α > deg α⁴` (`p = 5`: `4` vs `2`), so the new leaf is FALSE there — `p ≡ 3 mod 4` is
load-bearing and nobody had noticed, because `hcl` is vacuous at those `p` and was covering it.
**A hypothesis that makes a leaf vacuous also hides which OTHER hypothesis is doing the work.**

So: before attacking a leaf, ask of each hypothesis "which HALF of the conclusion needs this",
and test it numerically. `algdep` on a high-precision value answers degree questions directly
(400 digits, accept only residual `< 10⁻²⁹⁰` AND coefficient height `< 10³⁰` — the height test
is essential, `algdep` returns a spurious height-`10¹²³` relation at every degree otherwise).

**2. A TWO-CLAUSE EXISTENTIAL SPLITS IFF THE FIRST CLAUSE PINS THE WITNESS.**
`∃ Φ, P Φ ∧ Q Φ` becomes `∃ Φ, P Φ` and `∀ Φ, P Φ → Q Φ` — two independently ownable leaves —
exactly when `P` determines `Φ`. That is the whole obligation, and it is usually easy: for
`Φ_N`, `P` says `Φ.map (eval at j(z))` is a given product for every `z ∈ ℍ`, `Polynomial.map`
is coefficientwise, and `j` is non-constant, so rival `Φ`s differ by coefficients vanishing at
infinitely many points. Discharge it IN THE DOCSTRING; without it the second leaf is unusable,
because a prover cannot tell which `Φ` it is talking about. The payoff is large: the second
leaf gets to ASSUME the first, which for `Φ_N` removed the entire construction from Kronecker's
`q`-expansion computation.

**3. QUANTIFY OVER ROOTS OF THE MINIMAL POLYNOMIAL, NOT OVER A `Finset` OF CLASSES.** The CM
leaf's docstring said a finer cut "needs a `Finset` of form classes and a `form ↦ τ_f` map,
i.e. new infrastructure". Both halves of that obstruction evaporate if the leaf ranges over
`aeval x (minpoly ℚ y) = 0` instead of over a class group, and RETURNS the point alongside the
form. Neither the class group nor the `τ_f` map is then definable at all. Generally: when a cut
looks blocked on infrastructure, check whether the infrastructure is only there to INDEX
something the leaf could hand back existentially.

**THE TRAP THAT COMES WITH MOVE 3, AND IT IS INVISIBLE IN THE STATEMENT.** `minpoly ℚ x = 0`
for transcendental `x`, and `Polynomial.aeval x 0 = 0` holds for EVERY `x`. So a hypothesis
"`x` is a root of `minpoly ℚ y`" is satisfied by ALL of `ℂ` when `y` is transcendental — and a
conclusion that can hold for only countably many `x` then makes the leaf FALSE. Any leaf stated
through `minpoly` has a silent ALGEBRAICITY dependency on its subject. Say so in the audit and
name what discharges it; here it was the OTHER open leaf of the same file, which means the two
CM leaves are not independent and a reviewer must not treat them as such.

**AND THE COUNT IS NOT THE MEASURE.** Move 1 and move 3 were net zero (one leaf closed, one
opened); move 2 was `+1`. What improved is that `hcl` now appears in ONE leaf instead of three,
that the two `Φ_N` halves share no technique, and that each residue is a statement with a name
in a textbook. Report the recut that way, not by the delta.

**4. PROVE ONE BULLET AND HAND IT BACK AS A HYPOTHESIS — the only recut that does NOT void the
earlier faithfulness audit.** (2026-07-31, same file, next run.) A leaf whose docstring says
"three things must be shown: A, B, C" splits without any pinning obligation at all: prove `A`
outright, and restate the leaf as `A → conclusion`. The old statement comes back by feeding the
proof in, so it is one leaf replacing one leaf with the *same conclusion*, and the residual
prover is left with strictly fewer theories to know.

`exists_intPolynomial_eq_prod` (`Φ_N` exists) listed `Γ`-invariance of `∏_t (X − j(t·z))`,
holomorphy-plus-cusp, and `q`-expansion integrality. The first is elementary and was PROVEN —
`exists_triangularReps_right_mul` (right multiplication by `γ` permutes `triangularReps N`,
via Hermite normal form and a `T^k` absorption) plus `triangularReps_eq_of_right_mul`
(injectivity, which is where `triangular_unique` gets spent) plus `Finset.prod_bij`, with
surjectivity free from injectivity on a finite set. The leaf now takes that as `hinv` and is
PURE ANALYSIS.

Why this is safe in a way the other moves are not: **adding a hypothesis can only weaken a
statement.** `CLAUDE.md`'s "a leaf restated a second time VOIDS its earlier audit" rule exists
because the composite CONCLUSION changed (`exists_artinDivisorNormIndex_le_ray_class` gained a
support clause). Here the conclusion is untouched, so the audit — including a machine-checked
one — carries over verbatim. Say so in the docstring; a reader who sees "RECUT" will otherwise
correctly assume the audit is void.

The one real obligation is that `hinv` be USABLE. State it in the strongest form your proof
actually produces, not the form the leaf's bullet was phrased in: the invariance was proved as
an equality of POLYNOMIALS, though the bullet asked only for each elementary symmetric
function, because the consumer then gets its coefficientwise version by one
`congrArg (Polynomial.coeff · k)` — whereas going the other way costs an ext.

**AND THE TRAP THAT COSTS A BUILD ROUND, which is a direct consequence of the scratch-module
doctrine: your new proof may call a helper that lives LATER in the target file.** The scratch
imports the whole module, so every declaration is in scope and the ordering constraint is
invisible there — it appears only on the first real build, as `Unknown identifier` for a name
you can see with your own eyes. Here `denom_ne_zero_of_det` sat ~1000 lines below the insertion
point and had to be hoisted. So when a scratch-verified block first fails in the file, read the
error before assuming a proof broke: a forward reference is far likelier than an elaboration
difference, and the fix is a move, not a proof.

**5. AFTER A MOVE-2 SPLIT, CHECK WHETHER CLAUSE `P` ALREADY IMPLIES THE AMBIENT HYPOTHESIS —
it is often exactly strong enough, and then the two halves have DISJOINT hypotheses.**
(2026-07-31, `flt-lean-175`, same file, next run.) Splitting `∃ Ψ, P Ψ ∧ Q Ψ` into `∃ Ψ, P Ψ`
and `∀ Ψ, P Ψ → Q Ψ`, the reflex is to copy every hypothesis of the parent leaf into both
halves. Do the check instead: the second half receives `P Ψ` as a hypothesis, and `P` is the
clause chosen to PIN `Ψ`, so it is usually informative enough to reproduce some of them.

`Φ_N`'s construction (`∃ Φ ∈ ℤ[Y][X]` specialising to `∏_t (X − j(t·z))`) split into existence
over `ℂ` and integrality of the coefficients. The parent carried `hinv`, `Γ`-invariance of the
product, and the classical account of the INTEGRALITY half spends `Γ`-invariance too — to know
the coefficients are power series in `q` rather than `q^{1/N}`. So `hinv` looked like it had to
go to both. It does not: `P Ψ` says the coefficient functions ARE polynomials in `j`, and
`j(z+1) = j(z)`, so `T`-invariance is a CONSEQUENCE of the hypothesis. `hinv` stayed on the
rigidity half alone.

**The mirror-image obligation, which the count never shows: a split divides TECHNIQUES, not
PREREQUISITES.** Both halves here still need the `q`-expansion of `j` at a triangular point —
one wants its POLE ORDER, the other its COEFFICIENT RING. That is the single shared cost, and
it means the pair should go to ONE owner even though neither uses the other's technique. Name
the shared prerequisite in the docstring, or the next dispatcher will cost the halves as
disjoint and pay for it twice.

**And before writing "this step needs machinery we do not have", GREP THE PIN FOR THE STEP,
not for the theory — then WRITE IT, because the estimate is usually pessimistic.** The section
note here had recorded step (iv) — `Γ`-invariant holomorphic + meromorphic at the cusp ⟹
polynomial in `j` — as "real work but bounded", correctly ruling out the missing
`M_* = ℂ[E₄, E₆]`. Ten minutes in `Mathlib/NumberTheory/ModularForms/` turned it into four
named lemmas, and **the same afternoon it was PROVEN in about eighty lines**
(`exists_polynomial_eval_jInvariant_of_modularForm`): `levelOne_weight_zero_const` (base case),
`ModularForm.toCuspForm` (constant term zero ⟹ cusp form), `CuspForm.discriminantEquiv`
(divide by `Δ`, and `discriminantEquiv_apply` is `rfl`),
`EisensteinSeries.E_qExpansion_coeff_zero`. The bespoke "notion of pole order" the note said was
owed is not owed either — DEFINE pole order `≤ m` as "`F·Δ^m` extends to a
`ModularForm 𝒮ℒ (12m)`", which is exactly what the induction consumes and produces, so
`Γ`-invariance and holomorphy of `F` become CONSEQUENCES (`Δ` is nowhere zero, weight `12`)
rather than hypotheses. Also: `UpperHalfPlane.cuspFunction` / `qExpansion` /
`analyticAt_cuspFunction_zero` / `qExpansion_coeff_unique` are stated for an ARBITRARY
`f : ℍ → ℂ` under `Periodic`, `MDiff`, `IsBoundedAtImInfty` — no `ModularFormClass` instance —
which is what makes them usable on a function that is not yet known to be a modular form.

**Two Lean traps from that proof, each worth one build round.** (a) `ModularForm.coe_smul` is
stated for scalars acting *through* `ℝ` (`[SMul α ℝ] [SMul α ℂ] [IsScalarTower α ℝ ℂ]`), so at
`α = ℂ` it demands `SMul ℂ ℝ` and fails; the `IsGLPos.coe_smul` variant covers `α = ℂ`, but the
robust move is to state the equation yourself and let DEFEQ place it — `⇑(c • E)` and `c • ⇑E`
are `rfl`-equal, so `have h : <the form you want> := <the mathlib lemma>` typechecks where `rw`
cannot match. (b) A `set`-bound modular form is a local DEFINITION, so `simp` zeta-unfolds it
and then silently reports your hypotheses about it as "unused simp argument" while the goal
sits there unchanged. `clear_value` it once the defining facts are extracted, or introduce the
name with `obtain ⟨c, hc⟩ : ∃ c, … = c := ⟨_, rfl⟩` so it is opaque from the start.

