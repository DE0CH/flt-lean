## A "why the `∀` is legitimate" PARAGRAPH IS AN UNPAID FORMAL DEBT — pay it once and several citation leaves collapse into one

(2026-07-31, `ModularCurve/X0.lean`.) A leaf stated `∀ R : SomeFineModuliStructure, P R`
almost always carries a docstring paragraph of the form *"`universal` is a **fine** moduli
property, so any two inhabitants are related by a unique isomorphism, and `P` is
invariant under isomorphism; therefore the `∀` is not the junk-witness trap."* In `X0.lean`
FOUR leaves carried that paragraph, in near-identical words, and in every case it was
**prose only**. One of them even spelled out the price: *"the formal cost of the `∀` is
exactly that uniqueness argument"* — and then did not pay it.

Pay it. The argument is short, needs **no hypothesis, no citation and no inhabitant**
(it is a theorem about the structure, so it holds vacuously where the structure is empty),
and it is the same two steps every time:

1. *an endomorphism that classifies the object's OWN universal family is `𝟙`* — the
   uniqueness clause of `universal` applied at `(dM, lvlM)`, with `IsBaseChangeOf.refl`
   witnessing that `𝟙` classifies it;
2. *the two classifying maps between any `R` and `R'` are mutually inverse* — each
   composite is such an endomorphism, via `IsBaseChangeOf.comp`.

What that buys is bigger than one leaf. Once rigidity is a theorem, an **`∃`-shaped**
citation delivers every **`∀`-shaped** consumer, so a cluster of leaves that split one
indivisible citation "for dispatchability" can be **fused back into a single leaf with no
statement and no call site changing**. Here `exists_rigidifiedModuliScheme`
(representability, KM 4.7.2/5.1.1/6.6.1/6.6.2) and `isAffine_of_rigidifiedModuliScheme`
(affineness, the parenthesis of KM 8.1.1) both became THEOREMS over the single leaf
`exists_isAffine_rigidifiedModuliScheme`. Frontier −1, and the split was buying nothing:
the affineness parenthesis is a remark *about* the object representability produces, so
neither half was ever dischargeable alone.

Two practical notes:

* **`hn`-style hypotheses change role when you fuse.** In the old `∀` form `3 ≤ n` was
  vacuously satisfiable and NOT load-bearing (no inhabitant exists at `n ≤ 2`, so the `∀`
  was vacuously true). In the `∃` form it is load-bearing **for truth** — drop it and the
  leaf is FALSE, not merely unprovable. Re-run the falsity audit when the quantifier flips;
  an audit written for the `∀` does not transfer.
* **`refl`/`comp` for the base-change relation are usually declared BELOW the leaves**,
  because they were introduced later for a different consumer. Lean's declaration order
  then forces the newly-proven `∀` (and its assembly) to move down past them. Move the
  *consumers*, not the calculus — it is far less text — and leave a `used to be stated
  HERE … MOVED DOWN` note in the file's existing style.

The identical twin cluster in `ModularCurve/X1.lean`
(`exists_gamma1RigidifiedModuliScheme` / `isAffine_of_gamma1RigidifiedModuliScheme`, over
`Gamma1RigidifiedModuliScheme.universal`) is still unfused, and there
`IsBaseChangeOfGamma1.refl` / `.comp` already sit ~2500 lines ABOVE the leaves, so it needs
no movement at all.

**THE PATTERN REPEATS INSIDE ONE FILE, AND THE SECOND INSTANCE IS FREE.** Later the
same day the `𝔽_ℓ` twin ~29000 lines further down in `X0.lean` —
`exists_rigidifiedModuliScheme_specF` / `isAffine_of_rigidifiedModuliScheme_specF`
over `RigidifiedModuliSchemeData.universal` — fused the same way, and the rigidity
pair transcribed **verbatim**: `eq_id_of_isBaseChangeOf_self` and
`nonempty_iso_rigidifiedModuliSchemeData` are the `ℚ`-side proofs with the type name
changed and nothing else. That is not luck. The base `S` enters `universal` only as
the type of a binder that is passed on and never inspected, so the whole two-step
argument is base-agnostic — the same observation
`nonempty_rigidifiedModuliData_of_iso` already records for its own transcription.
**So when you pay this debt once, grep the file for the other `universal` fields
before you stop**; each further instance is a copy-paste plus one build.

Two things that made the second one cheaper, worth copying:

* **Verify the transcription in a SCRATCH module against the still-unedited
  `X0.olean`.** The structure you are transcribing onto is unchanged by your edit, so
  a scratch that `public import`s the target file can compile the whole new cluster —
  rigidity pair, fused leaf as a local `sorry` stand-in, and both derived theorems —
  in ~1 minute, against ~25 for a rebuild of an 80 k-line module. That is the
  general shape: a cut that only ADDS declarations over an unchanged interface is
  fully checkable before you touch the file.
* **When the fused halves were already `∃`-shaped on one side, the falsity audit is
  INHERITED and you should say so explicitly.** The rule further down ("re-run the
  audit when the quantifier flips") exists because a `∀`-vacuous hypothesis can become
  load-bearing for truth. Here only the *affineness* half flipped; the other half was
  `Nonempty` all along, so the fused statement is exactly as strong in `R` as that leaf
  already was and its audit transfers verbatim. Write the one sentence that says WHY it
  transfers — an audit labelled "inherited" with no argument is the failure mode
  recorded under TWO INDIVIDUALLY-CORRECT REPAIRS below.

**Same file, same day, the OTHER shape of unpaid debt: a docstring that has already
worked out the CHEAPER CUT and not taken it.** `exists_qExpansion_gamma0GITPresentation`
bundled one modular citation (the Tate curve over `ℚ((q))` fed to `P.classify`) with a
piece of pure commutative algebra (injectivity, from `B` being a one-dimensional
finite-type `ℚ`-domain). Its own docstring had already established that the OBVIOUS
split is FALSE — "injectivity of an arbitrary `ℚ`-algebra map `B → ℚ((q))`" is refuted
by any `ℚ`-rational point of `Y_0(N)`, via `B ↠ B/𝔪 = ℚ ↪ ℚ((q))` — and had named the
only faithful one, *"`f` is non-constant"*: `∃ f, ∃ x, ¬ IsAlgebraic ℚ (f x)`. Nobody
took it. It cost ~25 lines and it is now `exists_nonConstant_qExpansion_gamma0GITPresentation`
plus two proven mathlib-facing theorems.

**The frontier COUNT does not move for this kind of work, and it is still progress.**
One leaf becomes one leaf. What changes is that everything in the leaf which was not a
citation is gone: the survivor is dispatchable at somebody who knows the Tate curve and
nothing else, and the algebra can never be got wrong again. When judging a cut, ask what
is LEFT in the leaf, not only how many leaves there are — the "fewer OPEN leaves"
tie-breaker recorded further down is for choosing between rival cuts, not a reason to
skip a cut that is count-neutral.

Two mechanical traps, both of which cost a round trip:

* **`Ideal.Quotient.field` is NOT a global instance in mathlib.** The idiom is
  `attribute [local instance] Ideal.Quotient.field in` before the declaration (and it
  must come BEFORE the docstring, not between docstring and `theorem`). Introducing it
  with `haveI : Field (B ⧸ I) := Ideal.Quotient.field I` instead creates a
  `Module ℚ (B ⧸ I)` **diamond** — `Algebra.toModule` against
  `Submodule.Quotient.module'` — and `finite_of_finite_type_of_isJacobsonRing`
  (mathlib's Zariski's lemma, `@[stacks 0CY7]`) then fails to apply with a type mismatch
  that prints two `Module` instances and names no cause.
* **`set I := RingHom.ker f` makes `I` a let-bound local, and instance search stops
  seeing through it**: `Field (B ⧸ I)` and even `Algebra ℚ (B ⧸ I)` fail to synthesize.
  State the ideal-level lemma with the ideal as a genuine VARIABLE and apply it.

And on movement, the mirror of the note above: the three ring facts the algebra needed
(`IsDomain B`, `Algebra.FiniteType ℚ B`, `ringKrullDim B = 1`) sat 200 lines BELOW, in
`isRegularRing_coarseRing_of_gamma0GITPresentation`. Moving that ONE theorem up is 85
lines of text; moving the two consumers down would have been 300. **Move whichever side
is smaller** — and note the docstring's own suggestion ("re-run its three-line domain
half here") was wrong about the price: the "three-line" half is a thirty-line proof.

