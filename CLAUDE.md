# Project Notes — flt-lean

This repository was split out of Deyao's dissertation repo on
2026-07-22 (`git subtree split --prefix=fermat`); the full commit
history of the formalization is preserved. The project root IS the
Lean package (formerly the `fermat/` subfolder).

## AN EXISTENTIALLY-QUANTIFIED CONSTANT CARRIES NO ANALYSIS — and the PROVEN theorem below you may depend on your leaf

(2026-07-31, `flt-lean-92`, `Modularity/TateModule.lean`.) Two traps, one leaf, and the
first of them is worth checking on every leaf in this tree whose conclusion contains a
real number.

**1. `∃ C : ℝ, … ≤ C` IS NOT A BOUND.** `exists_boundedLevelScalar_atPrime_finiteBase` was
titled *"THE RIEMANN HYPOTHESIS FOR `A'`"*, cited Weil 1948, Mumford §19 and Tate 1966,
and its docstring told a prover the residue needed `#A'(k_m) = deg(F^m − 1)` and
**positivity of the Rosati involution**. Its conclusion is

    ∃ C : ℝ, ∀ n, ∃ u, u − s n ∈ Iⁿ ∧ ∀ φ : D →+* ℂ, ‖φ u‖ ≤ C

and the docstring itself says `C = 2√N` is the sharp value *"but the constant is left
EXISTENTIAL because nothing downstream uses it"*. **That clause destroys the analysis.**
`D →+* ℂ` is a FINITE type for a number field (`NumberField.Embeddings` registers the
`Fintype`), so the moment a single global `t` exists, `Set.range (fun φ => ‖φ t‖)` is a
finite set of reals, `Set.Finite.bddAbove` hands you `C`, and the archimedean clause is
five lines with no arithmetic in it. What is left is *"the trace of Frobenius is a global
algebraic integer"* — Weil's **rationality** half, which follows from finite generation of
the endomorphism module and has nothing archimedean in it. Rationality and the Riemann
hypothesis are a whole theory apart, and the leaf was advertising the wrong one.

**The check is mechanical and takes a minute: instantiate the existential yourself.** If
the bounded object is a SINGLE object (not a family), or the index set is finite, or the
constant may depend on everything in sight, then the bound is decoration and the content
is whatever produces the object. Sharp constants only carry content when something
downstream reads them — and a docstring that says nothing does is telling you so.

**2. A PROVEN THEOREM 1000 LINES BELOW YOU MAY BE PROVEN *OVER* YOUR LEAF.** This file's
own "A LEAF CAN BE CLOSED BY MOVING CODE" and "A DECLARATION-ORDER LEAF CLOSES BY MOVING"
sections say to grep below for a proven counterpart. Here there was one, and it was
perfect: `exists_frobEndoCharEq_of_mult_finiteBase`, PROVEN, ~1050 lines down, whose
conclusion subsumes the leaf at every geometric point, differing only in carrying `hdim'`
where the leaf carries `htower`. Everything about it reads as a hoist plus a bridge.

It is **circular**: it is proven over `exists_frobTraceAct_of_mult_finiteBase`, which
calls `exists_frobLevelTrace_of_mult_finiteBase`, which calls
`…_of_levelScalar_…` → `…_of_coherentLevelScalar_…` → the leaf. Five hops, none of them
visible in either docstring — both describe their own cut and neither mentions the other.

**So the declaration-order check is not `grep -n` on line numbers; it is the CALL GRAPH.**
Before treating a below-you theorem as a hoist, grep the file for YOUR leaf's name and
follow every hit that is a call site, not prose:

    grep -n '<yourLeafName>' <file> | grep -v '`'      # call sites, then their callers

If a path comes back to the candidate, the ordering is not an accident of layout — it is
the dependency, and no relocation can fix it.

**Corollary about equivalence, which is what the two checks together established.** Once
the archimedean clause was known free, the leaf turned out to be *equivalent* to the
conclusion of a theorem 200 lines below it — one direction already in the file, the other
proved in six seconds — with the hypothesis that separates them (`hlev`) derivable inline
from machinery already present. A leaf that is provably interchangeable with a downstream
theorem is not thereby closable; but say so in the docstring, because it doubles the
shapes a prover may attack and it stops the next agent re-deriving the equivalence. And
name the inline step: `hlev` here was STEP 2 of a 200-line proof, invisible from outside
until it was pulled out as `exists_frobLevelScalar_of_levelTateFrame_finiteBase`.

## A RED UPSTREAM MODULE DOES NOT BLOCK A CUT THROUGH IT — SHIM THE RELEASE OLEAN, AFTER DIFFING THE ONE NAME YOU USE
(2026-07-31, `flt-lean-389`, on `exists_cubeModel_pic_of_infinite`.) The cheapest correct
cut of a leaf routinely runs through a theorem in another module — here, closing
`HyperellipticJacobian.lean`'s geometric Mordell–Weil half by importing `X0.lean`'s PROVEN
`exists_cubeModel_of_abelianScheme` instead of re-cutting the same sheaf-level obligation.
**That module can be RED at your base**, and it was: `X0.lean` at `merger` `9e7f6e4b` fails
with **103 errors** (release 27 did not publish; `merger` has since gained
`1ead8a94 … why it did not publish, and the X0 repair method`). The obvious readings —
"take the other cut", "wait for the repair", "commit unverified" — are all wrong.
**Verify against the RELEASE SNAPSHOT's olean.** `~/.flt-release-lake/build` holds the
last green build and `~/.flt-release-lake/sha` names its commit. Your edit is checkable
against it **exactly when every name your new text takes from the red module has a
byte-identical STATEMENT at that sha and at your HEAD** — one `git show` per name:
    for R in $(cat ~/.flt-release-lake/sha) HEAD; do
      git show $R:<the red module> | grep -A6 "^theorem <the one name you use>"; done
Here that was a single name and the two outputs matched character for character, so the
shim proves what a real build would. Then (per the existing shim recipe) farm YOUR
worktree's current, mutually consistent oleans and override only the red module:
    cp -rs /scratch/chend-flt/flt-lean-N/.lake/build/lib/lean /tmp/relean-N/
    rm -f /tmp/relean-N/lean/<path>/X0.olean*
    cp -f ~/.flt-release-lake/build/lib/lean/<path>/X0.olean* /tmp/relean-N/lean/<path>/
    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    LEAN_PATH="/tmp/relean-N/lean:$LP" LEAN_SRC_PATH="$LSP" lean <your file>
**Two conditions make this sound rather than wishful, and both must be checked:**
* *the farm must be internally consistent* — take the CURRENT build as the base and
  override ONE module, not the other way round. A wholesale release-era farm would compile
  your file against release-era versions of its other dependencies; here three of the
  target's dependencies had changed since the snapshot, so that would have proved nothing;
* *the overridden olean's own dependencies must not have moved under it*. `git diff` the
  STRUCTURES your borrowed theorem's statement mentions — not the whole files. Here
  `ProjectiveHeight.lean` and `AbelianScheme.lean` had both changed, but `CubeModel`,
  `AbelianSchemeStruct` and `RelPoint` were untouched (the diffs were an added theorem and
  an unrelated pairing repair), which is what makes loading the old `X0.olean` beside the
  new ones safe.
**And weigh the marginal damage before adding the edge at all.** A green module gaining an
import of a red one sounds reckless; compute who is downstream. `HyperellipticJacobian`'s
only consumer is `MazurTorsion.lean`, which already `public import`s `X0.lean`, so while
`X0` is red that consumer is red anyway and the marginal cost of the new edge is exactly
one module's warning set. If instead the red module sits under something that still builds,
do not add the edge.
Two riders from the same run:
* **Put a one-consumer helper DOWNSTREAM, not beside the structure it is about.**
  `CubeModel.congr` (transport of a `CubeModel` along an `AddEquiv`) belongs in
  `ProjectiveHeight.lean` next to `CubeModel`. It is in `HyperellipticJacobian.lean`
  instead, because `ProjectiveHeight.lean` is `public import`ed by `X0.lean`, so touching
  it rebuilds the largest module in the tree — **and the rebuild had already been started
  and would have had to be thrown away.** Dot notation is the price (`cubeModelCongr cm e`
  rather than `cm.congr e`, since a declaration made inside `Fermat.Hyperelliptic` cannot
  extend the `Fermat.CubeModel` namespace); say in the docstring where it belongs and what
  would justify the hoist.
* **A non-public `import` is the right edge for a proof-only dependency, and it is worth
  spelling out why in the import block.** `X0.lean`'s 107 000 lines of names are used here
  only inside one theorem BODY, which a private import reaches; making it `public` would
  re-export all of them through a module whose consumer already has them. What the edge
  still costs is BUILD ORDER, and that is the thing to justify.
## THE DEGENERATE OBJECT REFUTES EVERY UNGUARDED PERFECTNESS CLAUSE

(2026-07-31.) `exists_tateWeilRawFamily_of_qAdicWeilSystem` was refuted with no
arithmetic at all: take the ZERO abelian scheme, `A = S`, `f = 𝟙 S`.
`AbelianSchemeStruct` asks for a group law plus `IsProper`, `Smooth`,
`GeometricallyConnected` — **there is no nontriviality axiom in it**, and `𝟙 S`
satisfies all three, its fibres being points. Then every `RelPoint` is a
singleton, so `TatePt` is a singleton, so the ALTERNATING clause
(`C N t t ∈ 𝔪`) and the PERFECTNESS clause (`∃ t s, IsUnit (C N t s)`) are the
same statement about the same element and contradict each other. The two proven
consumers inherited the defect, because their conclusions carry a unit clause
too.

The general shape, worth running as a standing check: **any leaf whose
conclusion asserts a UNIT VALUE, a NONDEGENERACY, or a BASIS needs a hypothesis
that the object is nonzero, and that hypothesis is easy to lose in a cut** —
the geometric half of a decomposition keeps `hdim`, the arithmetic half gets
the pairing handed to it as a binder, and nobody notices that the pairing's own
axioms are vacuously satisfiable on the zero object. Here the finite-base
sibling had exactly the right hypothesis (`hne`) with the reason written on it,
and the characteristic-zero half had simply dropped it. **When two halves of a
development mirror each other, DIFF THEIR BINDER LISTS** — that is a
five-minute check and it found this one.

Corollary about audits: this leaf carried two 2026-07-30 falsity audits, both
CORRECT, neither of which saw it. They were about the normalisation, and they
presupposed a nonzero Tate module. CLAUDE.md's existing rule — a second
restatement VOIDS the earlier audit — is what prompted re-running it from
scratch, and it earned its keep.

## AN INTERFACE PREDICATE CAN BE UNDER-COMMITTED: SATISFIED BY THE WRONG NORMALISATION

(2026-07-31, same cluster, and it is the subtler half.) `IsTraceDualFunctional`
pins a functional `θ : O → ℤ_q` by four clauses, and
`exists_traceDualFunctional_of_adicPin` PROVES it, so it looks settled. It was
not: at a RAMIFIED `I` the four clauses are satisfied by `θ_m = Tr(δ π^m ·)`
for EVERY `0 ≤ m ≤ e-1`, not only by the correct `m = 0`. Consequences:

- the third clause's hypothesis ("`φ` kills `I^k`") was one the intended input
  never satisfies — the Weil functional kills `I^{e·k}` — so the clause was
  dead at every positive level, and the leaf whose whole route it is could not
  be started;
- every constant it could return lay in `(jπ)^{(e-1)k}`, hence was a NON-UNIT,
  hence could never satisfy the consumer's perfectness clause.

**The producer was already correct** — it builds `θ` as a GENERATOR of
`Hom_{ℤ_q}(O, ℤ_q)`, which is `m = 0` on the nose — so strengthening the
statement cost its proof nothing. One `have hNk : k ≤ N` was deleted, and it
was the line that had been throwing the extra strength away.

The lesson generalises past this file: **when a leaf's prescribed route "just
does not work", check whether the INTERFACE it routes through is weaker than
the object that satisfies it.** A predicate proven inhabited is not thereby
adequate; ask what ELSE inhabits it. The mechanical test is a scaling family —
perturb the intended witness by a unit, a uniformizer power, a twist — and see
which clauses still hold. If a wrong scaling survives every clause, the
predicate cannot support any conclusion that needs the right one.

Related trap in the same vocabulary, since it cost a false start: a
"perfect pairing `𝒪_D/I^k × O/(jπ)^k → ℤ_q/q^k`" gloss in a docstring can be
WELL-DEFINED-FALSE while the formal clauses beside it are true. `Tr(δ I^k 𝒪)`
is `q^{⌊k/e⌋}ℤ_q`, not `q^k ℤ_q`, so that pairing does not descend at all for
`e ≥ 2`. Read the CLAUSES, not the gloss.

## After a fast-forward, RSYNC the release snapshot instead of rebuilding

(2026-07-31, `flt-lean-373`.) A worktree seeded at release *R* and then
fast-forwarded to a later `main` has an `.olean` set for *R*, so the first
`lake build` of anything rebuilds the whole changed cone — >10 minutes before it
even reaches your own module, and that is the state of EVERY worktree whose
targets were introduced after its seed (mine did not contain its three targets
at all until the ff).

`~/.flt-release-lake/build` is the current snapshot and `~/.flt-release-lake/sha`
names the commit it was built at. **The snapshot is valid for your tree exactly
when no commit between that sha and your HEAD touches `Fermat/`:**

    S=$(cat ~/.flt-release-lake/sha)
    git merge-base --is-ancestor $S HEAD && git log --oneline $S..HEAD -- Fermat/

Empty output → the oleans match your sources, so

    rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/

is a complete substitute for the rebuild (2.3G, under a minute). It replaces only
the PROJECT build; `.lake/packages/mathlib/.lake/build` is a separate directory
and is untouched. Kill your own `lake`/`lean` first (**by PID after checking
`/proc/<pid>/cwd`**, never by pattern) — rsyncing under a live build is exactly
the torn-snapshot state the release seeder's own guard exists to prevent.

If the `git log` is NON-empty the snapshot is stale for those modules and you
must build; the check is cheap and there is no partial-credit version of it.

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

## A DISPATCHED WORKTREE IS NOT NECESSARILY AT `main` — check before calling a target a phantom

(2026-07-31, `flt-lean-109`.) The dispatch hook is supposed to fast-forward the worktree to
`main`. Mine arrived **575 commits behind** it, clean and on its own branch, so `HEAD` was a
perfectly ordinary ancestor of `main` and nothing looked wrong. One of the two named targets,
`exists_levelOneGeneratingSeq_space_of_charpoly`, **did not exist anywhere in the tree** — and a
`git log -S`/`git log -m -S` sweep across `--all` found only merge commits, which reads exactly
like the "cut, merged, and deliberately declined" case documented below.

It was none of those. The task prompt's line numbers (`:3800`, `:4093`) matched `main` **exactly**,
which is the cheap tell: prompts are stamped against `main` at queue time, so *line numbers that do
not match your file are a statement about your checkout, not about the leaf.* One
`git merge --ff-only main` and both targets were there at the quoted lines.

So the first three commands of any task, before any archaeology:

    git rev-list --count HEAD..main      # MUST be 0; if not, you are not looking at the frontier
    git merge --ff-only main
    sed -n '<quoted line>p' <the file>   # the declaration should be right there

Corollary for the `.lake` seeding, and it is worth 20 seconds against a multi-hour build:
`~/.flt-release-lake/sha` names the commit the snapshot was built at. If

    git diff --stat $(cat ~/.flt-release-lake/sha) main -- Fermat/

is EMPTY, the snapshot is bit-for-bit `main`'s Lean state (only tooling commits landed since), so
`rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/` gives a
fully warm tree. Mine was, and it did.

And `lake` is **not on `PATH`** in a fresh agent shell even when running locally on the owning
host — `export PATH="$HOME/.elan/bin:$PATH"` first, or the build dies instantly with
`lake: command not found` and an `EXIT=127` that is easy to misread as a build failure.

## `merger` CAN BE RED — never base a branch on it without building it first
(2026-07-31, cost one agent ~90 minutes.) A task prompt described the "STATE OF
THE ART" using facts that exist only on `merger` (a structure field `smoothM`
added on 2026-07-30, and an audit written the same day). The obvious inference —
"so I must work from `merger`, otherwise the premise of my task is absent" — is
what the *previous* release windows had taught. It was wrong that day, and the
failure mode is worth stating because it is invisible from the task prompt:
**`merger` is a work-in-progress tree, not a better `main`.** Release 27 was
NOT published precisely because `ModularCurve/X0.lean` had not built since
release 25 and still had ~193 errors after nine repairs. `main` was
deliberately left at the last GREEN release, and
`~/.flt-release-lake/build` still matches it. So on `merger`:
* `lake build <anything importing X0>` fails with hundreds of errors that are
  none of your business and that you must not "fix";
* the release-artifact seed does not match the tree, so the "51 seconds"
  figure a prompt quotes becomes a multi-hour rebuild of ~5000 modules;
* you cannot verify anything, and an unverified structural edit is worth less
  than no edit.
**The rule: build before you trust a branch, and prefer `main`.** `main` is the
only tree guaranteed to pair with `~/.flt-release-lake/build`. If your task's
premise is merger-only, do the work against `main` anyway (the declarations and
the plumbing sites almost always exist there too, just at an earlier state),
verify it green, and put a precise conflict note in `to_merger` saying where the
two edits collide and how to resolve them. A verified change on `main` plus a
merge note beats an unverified change on `merger`.
Two mechanical consequences, both hit the same day:
* `queue1` records `AUDITED: <sha of main>`. **That sha is the tree the loop
  expects you to work in.** Check it (`head -1 ~/.flt-loop/queue1`) against your
  worktree's HEAD before deciding what to base on — it is the cheapest possible
  disambiguation and it is authoritative.
* If you have already advanced a worktree to `merger` and built, `git reset
  --hard main` is not enough: `.lake/build` is then a mix of merger-built and
  release-snapshot oleans and lake will rebuild everything back. **Re-run the
  seed** (`rsync -a --delete ~/.flt-release-lake/build/ .lake/build/`) before
  building; it takes seconds warm and saves hours.
Also: `lake` is not on `PATH` in a fresh agent shell. Every build line needs
`export PATH="$HOME/.elan/bin:$PATH"` first, or it dies with
`lake: command not found` and `EXIT=127` — which reads like a broken worktree
and is not one.
## Missing tools: brew install is pre-authorized

(Deyao, 2026-07-21.) If a needed tool is missing and available through
Homebrew, run `brew install <tool>` directly — no need to ask first.

## Fleet integration: rescan sorries at every agent completion and re-dispatch

(Deyao, 2026-07-22.) When a subagent finishes: merge and verify its
branch, then SCAN its file(s) for the sorries it left (its report lists
them; confirm against the source), and DISPATCH new agents onto those
leaves — possibly several agents per completion when the leaves are
independent (disjoint decomposable clusters get separate owners rather
than one successor inheriting the whole file by default). The loop
invariant: every sorry has an owner at all times; an agent completing
must never strand its remaining leaves unowned. Track the new leaves in
progress-entries.json (wip flags at dispatch) as part of the same
integration step.

**A prompt MENTION is not ownership — ownership is a record's own TARGET** (2026-07-27).
The rule below (grep the prompt) is necessary but not sufficient, and its naive form
manufactured a phantom *non*-dispatch. Task prompts contain "coordinate, do not edit:
`flt-lean-36` owns `X`" notes written by the orchestrator. When that worktree is
**reallocated** the note goes stale — and a later grep for `X` hits the orchestrator's
own stale claim and reads it back as evidence that `X` is owned. Self-reinforcing:
the more carefully coordination is written down, the more convincing the phantom.

So the check has three parts, all required. A leaf is owned iff some record:
(a) names it in its own **`TARGET:` line** — not merely anywhere in the prompt;
(b) is the **latest** record for its worktree (the file is append-only; earlier
records for a reallocated worktree are history, not state); and
(c) that worktree is still `claimed`.

A hit that fails any part is a stale note. `flt-lean-173` reached this conclusion
correctly against a gate this file's rule had told it to trust, and was right.

**The three-part test does NOT catch a stale claim in a COMMIT MESSAGE** (2026-07-27).
Two `ModThree.lean` leaves sat in an "each owner says the other owns it" loop.
`flt-lean-78`'s commit message ended `Still open in this cluster, owned elsewhere:
aeval_minpoly_eq_prod_sub_integralClosureLE, smul_integralClosureLE` — **true when
written, false by the time it merged**, because `flt-lean-77` closed both
concurrently on a parallel branch (`bb97c541`, which is not an ancestor of
`flt-lean-78`'s tip and reached main separately via `9269f17f`). Nobody was
dispatched at them for a cycle, and when someone finally was, there was nothing
to do.

The note lived in git history, not in `~/.flt-inflight.jsonl`, so grepping records
— however carefully — could not see it. **The only reliable ownership evidence is
the compiler**: a green `lake build`'s `declaration uses 'sorry'` warning set says
what is actually open, and it costs one build. Prefer it to any prose claim about
what is "still open", including your own from an hour ago. A leaf named as open in
a commit message, a docstring, or a report is a *hypothesis to check*, never a fact.

Corollary for agents: **do not write "still open, owned elsewhere" lists into commit
messages.** They are unmaintainable by construction — the commit is immutable and the
frontier is not. Put such observations in the final report, where the orchestrator can
act on them while they are fresh.

**Check overlap by grepping the PROMPT, not the `targets` field** (2026-07-25).
`~/.flt-inflight.jsonl`'s `targets` is harvested by a regex for bold
`**\`name\`**`, so tasks not written in that style get junk targets (one batch
recorded `['diagnostics', 'lean_leansearch', …]`). Before dispatching at a leaf,
grep the full `prompt` of every in-flight record for the leaf NAME. Skipping
this let two agents cut the SAME node — `exists_isWeaklyUniversalOnIdentified`
— along Schlessinger in two incompatible ways, producing an eight-hunk
mathematical conflict that had to go back to an author to reconcile. Noticing
that another worktree is merely "in the same file" is not enough; the file is
not the unit of ownership, the declaration is.

**"Merge FIRST, then dispatch" is an ordering, not a sequence of words**
(violated 2026-07-25). A worktree fast-forwards to main at dispatch, so a
successor dispatched at a leaf that still lives only on an unmerged branch
fast-forwards to a main WITHOUT that leaf and finds nothing — a phantom
dispatch manufactured out of a correct report. It happened with three
`Deformation.lean` successors sent off the strength of an agent's report
while its branch was still resolving a conflict. If the branch cannot be
merged yet, the successors WAIT; queue them, do not dispatch them.

Same-FILE leaves may get concurrent owners (Deyao, 2026-07-22): each
agent works in its own git worktree on its own branch, and merging
concurrent edits to one file is what git is designed to handle — leaves
are disjoint regions, so merges are clean or trivially resolvable at
integration. Do not serialize a file's independent leaves behind one
owner out of conflict fear; partition them.

## Fleet dispatch: fixed pool of 26 numbered worktrees

(Deyao, 2026-07-23; extended 2026-07-24.) Subagent dispatch runs over a
FIXED pool of 26 worktrees, each on its own same-numbered branch, each
with its own already-running systemd instance — `lake serve` on FIFOs,
scoped to that worktree. Live allocation state:
`~/.flt-worktree-pool`, one line per worktree, `<name> free` or
`<name> claimed`.

**STALE BELOW (2026-07-25): the systemd units are DELETED.** The batch
descriptions survive only for the `.lake`-on-`/scratch` layout, which is
still true and still the reason `lake` must run on the assigned host. Every
mention of `flt-report-server@` / `flt-lake-socket@` / `.report-server` is
historical — those unit files were removed from `~/.config/systemd/user`
so nothing can start them, and `.report-server` no longer exists in any
worktree.

- **Batch 1, `~/flt-lean-1` .. `~/flt-lean-13`**: template unit
  `flt-report-server@.service`, `WorkingDirectory=%h/%i`.
- **Batch 2, `~/flt-lean-14` .. `~/flt-lean-26`**: same layout as batch 3 —
  source tree in `$HOME`, only `.lake` and `.report-server` symlinked to
  `/scratch/chend-flt/flt-lean-N/`. Artifacts live off `$HOME` because a
  worktree costs ~5.4G (4.6G of it mathlib oleans in `.lake/packages`, 826M
  project build) and the 67G home volume filled up; `/scratch` is a 9.7T
  local disk. **`/tmp` is NOT an option — it is a 9.7G volume, one
  worktree's worth.** Note `/scratch` is machine-LOCAL and not backed up;
  only `.lake` and uncommitted work would be lost, since branch refs live in
  the main repo's object store.
- **ONE unit template, `flt-report-server@.service`** (`WorkingDirectory=%h/%i`),
  serves every worktree. A second template rooted at `/scratch` existed
  briefly while whole worktrees lived there; it was deleted 2026-07-25 once
  the layout settled on "sources in `$HOME`, artifacts symlinked" — there is
  deliberately only one way to run a worker.
- `.claude/worktree-pool-hook.py` resolves a pool entry by trying each
  root in `ROOTS` in order, so batch-1 names still resolve under
  `$HOME`.
- A fresh batch-2 worktree needs `lake exe cache get` run in it once
  (with `XDG_CACHE_HOME` pointed at scratch so the ltar cache does not
  refill `$HOME`) BEFORE its server is started — otherwise `lake serve`
  tries to build mathlib from source.

- **Batch 3, `~/flt-lean-27` .. `~/flt-lean-42`** (Deyao, 2026-07-24): same
  layout as batch 2 — source tree in `$HOME`, `.lake` and `.report-server`
  symlinked to `/scratch/chend-flt/flt-lean-N/`, served by the ORDINARY
  `flt-report-server@.service` template (the worktree is under `%h`).
  `.gitignore`'s `.lake/` patterns do not match symlinks, so `.lake` and
  `.report-server` are listed in `.git/info/exclude` instead.
- **Pool states**: `free`, `claimed`, and `suspended <agent-id>`. A suspended
  entry is never allocated — that is how a reduced worker count is enforced
  under memory pressure — and its third field is the stopped agent's
  transcript id, so the work can be picked up later with SendMessage.
- **RAM watchdog** (Deyao, 2026-07-24): a 10-minute cron reminds the
  orchestrator to check free memory. Procedure lives in
  `~/.flt-ram-watchdog-prompt.md`: below 200G free, restart a FEW worker LSPs
  at a time (closing their open files releases memory without interrupting the
  agents' work) and email; if that recurs 3× in an hour, suspend workers 4 at a
  time instead. Cron jobs are session-only, so **re-create it after every
  restart**.

- **Max 42 concurrent subagents**, one per worktree, 1:1. The harness cap
  `CLAUDE_CODE_MAX_CONCURRENT_SUBAGENTS` is fixed at launch (currently 50, set
  in the tmux launch line) — the pool, not that number, is the real limit.
- **FIFO task queue** (Deyao, 2026-07-23): `~/.flt-task-queue`, a
  plain text file — full agent prompts separated by lines consisting
  exactly of `=== TASK ===`. The orchestrator reorders and drops tasks
  BY HAND-EDITING THE FILE. To dispatch the queue head, spawn an agent
  whose prompt is the sentinel `{{FLT_QUEUE_POP}}`: the hook pops the
  top task, allocates a worktree, substitutes `{{FLT_WORKTREE}}`
  inside the queued prompt, and replaces the Agent call's prompt with
  the result. A pop with the pool full is denied leaving the queue
  untouched; a non-fleet spawn (no placeholder) while the queue is
  nonempty is denied with a dispatch-the-queue-first reminder.
- **Direct dispatch**: put the literal placeholder `{{FLT_WORKTREE}}`
  in the agent's prompt wherever its worktree path belongs.
  `.claude/worktree-pool-hook.py` (a `PreToolUse` hook on the `Agent`
  tool) finds a `free` entry, checks it is git-clean and its branch is
  an ancestor of main, fast-forwards it to main (`--ff-only`), marks
  it `claimed`, and substitutes the real path for the placeholder. If
  the dispatch cannot run immediately — the queue is nonempty (FIFO)
  or no worktree is free — the hook AUTO-QUEUES it: the prompt is
  appended to `~/.flt-task-queue` by the hook itself and the call is
  denied with a message giving the queue position and the
  `{{FLT_QUEUE_POP}}` instruction. **Agents own `.lake`** (Deyao,
  2026-07-25, reversing the old "never touch `.lake`" rule, which
  existed only because a systemd-managed `lake serve` owned it): the
  orchestrator advances the pointer to main and says in the prompt that
  the artifacts may be stale and may need rebuilding — and does nothing
  else about them. Managing them centrally is what turned private build
  problems into fleet-wide ones. A claimed worktree that is dirty or not an ancestor of main is
  not auto-corrected — the hook hard-crashes (traceback to stderr,
  exit 2, tool call blocked): that state means something beyond
  allocation went wrong.
- **On agent completion**: the orchestrator merges the agent's branch
  into main, then hand-edits `~/.flt-worktree-pool` to mark that
  worktree `free` again (no reliable hook fires on "the orchestrator
  finished merging" — `git merge` is just a Bash call among many, so
  this step is the orchestrator's explicit responsibility). Otherwise
  leave the worktree folder alone.
- **No per-agent server/file lifecycle management**: don't close LSP
  files, don't build reapers or memory-conservation tooling for this.
  Memory grows but stays bounded over time — accepted as fine, not a
  leak to chase.

## File edits: prefer the Write/Edit tool calls over scripts (soft rule)

(Deyao, 2026-07-22.) Edit files with the harness's Write/Edit tools by
default — not with shell/python scripts (heredoc `python3 - <<EOF`
string-replaces, `sed -i`, etc.). A scripted edit that is semantically
equivalent to a Write/Edit call (fixed string replace, whole-file
rewrite of known content) must BE a Write/Edit call: the script form
bypasses read-before-write and diff tracking for zero gain. Scripts
remain allowed where they are genuinely more capable than the tools —
e.g. programmatic transforms over structured data (bulk json updates
computed from state, generated content) — capability, not convenience,
is the test.

## THE GOAL: fully formalize Fermat's Last Theorem, no sorry, no undue axioms

(Deyao, restated 2026-07-16.) The goal is to **fully formalize Fermat's
Last Theorem in Lean 4** in this repository: the whole proof written as
Lean files that **compile without any `sorry`** and without undue
axioms (at most `propext`, `Classical.choice`, `Quot.sound`). The
method is **resolving a dependency tree**: the top theorem is proven;
every gap is an explicit stated-and-sorried node; go down the list,
fill in missing proofs, and iterate walking the tree — decompose deep
nodes into shallower ones, prove the provable ones — until the entire
tree is written and `lake build` passes the sorry gate. `PROGRESS.md`
is the authoritative tree.

**Counting the frontier: DIRECT vs TRANSITIVE sorries, and the comment
trap (2026-07-25 — both of these caused phantom dispatches).**

Two different numbers are both called "the frontier" and they are not
interchangeable:

- *Direct*: the declaration's own body contains `sorry`. This is what
  Lean's `declaration uses 'sorry'` warning reports, and it is the set of
  leaves that can be WORKED ON. **234 across 26 modules** as of `60313518`
  (release 4, 2026-07-27) — up from 175 at `0a976e16` earlier the same day.
- *Transitive*: the declaration's proof term reaches `sorryAx`, i.e. it is
  sorried **or consumes something sorried**. This is what
  `ProgressCensus.lean`'s census reports.

**A RISING count is not a regression — it is usually disclosure.** The jump to
234 is mostly the Cartier-duality island becoming visible: five `HopfAlgebra`
modules that nothing imported, hence never compiled, hence invisible to the
warning set *and* to the census. Wiring them in (`1492cecb`) made their sorries
countable for the first time. Decomposition does the same thing at smaller scale
— a node that closes over three named sub-leaves nets +2 while being real
progress. Read the delta alongside what closed, never alone.

**Do not trust a frontier number in this file — regenerate it.** The figures
above were 85/86 for a single day and were wrong by a factor of two by the next
morning: the tree grows leaves faster than prose records them, and six releases
landed during one bookkeeping run (the frontier moved 138 → 156 → 157 → 174 →
175 *while it was being counted*). Any count is stamped to a commit and stale
immediately. `flt-frontier.py`'s source scan **is** validated against the
compiler — at `a18c5c4d` it matched the build's `declaration uses 'sorry'`
warning set exactly, 157 = 157, zero difference in both directions — so run it
rather than quoting a number.

A consumer of a sorried leaf is transitively sorried but has NOTHING to
prove — dispatching an agent at it wastes a worker. Two whole clusters were
dispatched this way (`Chebotarev.lean`, and three leaves in `Flat.lean`)
before agents reported back that their targets were already proven. **Build
task lists from the DIRECT set; use the transitive set only for judging
whether a subtree still blocks the root.**

**AND THE PER-DECLARATION ANSWER IS `#print axioms`, RUN IN-FILE — a green build
cannot give it to you** (2026-07-31, `HilbertClassFieldNormal.lean`). An agent
arriving at a target needs to know which of three states it is in: open, proven
outright, or proven-but-transitively-tainted. `lake build` distinguishes only the
first from the other two — a module with no `declaration uses 'sorry'` warning is
*direct*-clean and says nothing about the cone — and the fleet has repeatedly
paid a worker to rediscover the difference.

`#print axioms <name>` gives it exactly, but **it must be appended to the END OF
THE FILE THAT DECLARES THE NAME**, not written in a scratch module that imports
it. The module system elides imported proof bodies (`value? = none`, and
`import all` does not help), so from a scratch importer the traversal has nothing
to walk. Cost is one `lake env lean` of the module; restore the file afterwards:

    cp F.lean /tmp/orig.lean
    printf '\n#print axioms Some.Decl\n' >> F.lean
    lake env lean F.lean            # `[propext, Classical.choice, Quot.sound]` = finished
    cp /tmp/orig.lean F.lean

Here it separated four declarations in one run that a build reported identically:
`conj_unramifiedAbelian` and `sup_unramifiedAbelian` came back axiom-clean, while
`exists_hilbertClassField_normal_over_rat` came back `sorryAx` — and the same
output **names the blocking DIRECTION for free**, since the only paths out led
into `UnramifiedClassFieldExistence.lean` and `ArtinSymbol.lean`.

**But the direction is all it gives you — do not queue the named leaves without
re-checking them against `merger`.** `#print axioms` is evaluated against YOUR
import cone, which is `main`, and `main` is the frontier as of the last release.
Measured the same afternoon: the cluster this audit pointed at had four open
leaves on `main` and three on `merger`, because Chebotarev (`closure_frobAt_eq_top`)
and `exists_hilbertClassField_artinIso` were both already proven and merely
sitting in the release window. So the audit is authoritative about *your* target
and merely indicative about everyone else's; pair it with
`git show merger:<file>` before writing a queue entry, or you will pay someone to
prove Chebotarev a second time.

Two corollaries. Record the verdict in the file's module docstring, because it is
the only place the next frontier scan will look and the only thing that stops the
same target being re-dispatched off the transitive census. And note the reverse
reading: `sorryAx` on your target is **not** a failure when every path to it
leaves your file — say so, name the upstream leaves, and do not go prove them.

**Small trap that cost one wasted build: `lake` is NOT on `PATH` in a worker
shell**, even when you are already logged in to the owning host and never touch
`ssh`. The first invocation returns `lake: command not found` / `EXIT=127`, which
reads like a broken worktree rather than a missing environment. Prefix every
command with `export PATH="$HOME/.elan/bin:$PATH"`. The existing note about this
is filed under *ssh* builds; the cause is the login shell not sourcing elan, so
it bites local runs identically.

**`verified: true` does NOT mean the import cone is current** (2026-07-25, hit
independently by two agents). Lean's LSP caches the `lake setup-file` result per
HEADER SNAPSHOT and replays a failed one verbatim until the IMPORT LIST changes.
So when an upstream file is broken and then fixed, `diagnostics` keeps returning
the stale build failure — with `verified: true`, because the call really did
receive that (stale) diagnostic. Meanwhile `build` in the same session compiles
the file fine. A false negative carrying a truth claim is the worst shape of
wrong answer, and it cost two agents a verification cycle each.

Symptom: `diagnostics` reports an error inside an IMPORTED file rather than in
the file you asked about. Remedy: perturb the IMPORT LIST (add or remove an
`import`) to force a re-run, or cross-check with `build`. **A content change is
NOT enough** — a third agent hit this after a real edit and got four successive
byte-identical stale replies, including identical build timings and an error
line whose `simp` no longer existed; only `build` plus lake's `.trace` log told
the truth. Do NOT restart the report server — that discards genuine in-flight
elaboration; and do not conclude the upstream is still broken without checking
`git log` for a fix.

**FAITHFULNESS: a leaf can be FALSE AS STATED, and that is worse than open.**
Three were found and corrected on 2026-07-25 alone. A false leaf can never be
proven, and anything derived from it is worthless — so when a leaf resists,
seriously consider that it may be false rather than merely hard. Refuting one
with an explicit counterexample and restating it correctly is a FULLY successful
outcome; say so in task prompts.

**THERE IS A THIRD OUTCOME, and this development's axiomatized structures produce
it regularly (2026-07-31).** When a leaf is stated over a `structure` that
AXIOMATIZES an object rather than over a construction, it can be neither provable
nor refutable: **the axioms simply do not determine the object where the leaf
looks.** `le_fixedSubmodule_gp_of_mem_Ioo` in `ArtinConductor.lean` was exactly
this — `RamificationFiltration.gp_herbrand` pinned the upper-numbering filtration
only AT the Herbrand values, and inside the gaps the axioms left a sandwich whose
BOTH ends are admissible. Probing with other levels is circular, because the axiom
relates every level to `F` and no two levels to each other. No counterexample can
be exhibited in-tree either, since refuting a `∀ F` needs a filtration built over
an arbitrary `Kᵥ`. So the leaf sits there forever, looking merely hard.

The repair is to the STRUCTURE, and there are exactly two checks that turn it from
a dodge into a decision:

1. **Does the CONSTRUCTION that inhabits the structure satisfy the stronger axiom
   for free?** If it needs new input, the strengthening is a disguised `sorry` and
   the answer is no. (Here it was `iInf_le` one way and the ALREADY-OPEN leaf at
   the interval's right endpoint composed with antitonicity the other — zero new
   leaves.)
2. **Which direction do consumers use the structure in?** Strengthening SHRINKS
   the admissible class, so `∀ F` theorems get weaker and `Nonempty` gets harder.
   Get this backwards and you have quietly weakened a theorem instead of
   sharpening a model. (Here `IsSwanExponentAt = Nonempty ∧ ∀ F, …` and every `F`
   reaching a proof comes from the construction, so both halves were safe — and
   faithfulness improved, the genuine object being a singleton.)

Record it as a numbered FALSITY AUDIT in the structure's own docstring, KEEP the
analysis that showed the old axioms insufficient (it is the evidence for the
repair, and without it the next reader sees only a convenient axiom), and correct
in place any route the leaf's docstring proposed that you found does not work.
Often the structure's own audit has already named the repair — this one had.

The discriminating rule for the commonest trap in this development, from a sweep
of every `𝒪ᵥ`-rational group-scheme leaf (2026-07-25): **over `𝒪ᵥ`, identities
and VALUES descend from `𝒪^nr` (flatness/torsion-freeness, and inertia fixes
`𝒪^nr` pointwise); the EXISTENCE of a coordinate or a normal form does not.** A
leaf is faithful exactly when it asks for a value or an inertia-only
equivariance, and false exactly when it asks for an element of `G` or for
`Γ`-wide rationality. Two corollaries: unramified twists are invisible to
inertia, so inertia-only conclusions are twist-blind; and étale-by-étale is
étale, so the dual/Selmer arguments are twist-blind too. `exists_muType_closure`
died on precisely this — it demanded the μ_p-coordinate over `ℤ_p`, but the
connected order-`p` schemes there are the `p−1` unramified twists `μ_p ⊗ ψ`,
each satisfying every hypothesis with no such coordinate when `ψ ≠ 1`.

Corollary for REVIEWERS: watch for a quantifier over `localInertiaGroup` being
"generalized" to all of `Γ`. `exists_localTorsionQuotient_of_good_ordinary` is
true only because `σ` ranges over inertia — the étale quotient at good ordinary
reduction carries the *unramified* character `α`, trivial on inertia but not on
Frobenius — and widening it makes the leaf false for every curve with `α ≠ 1`.

**Third category, invisible to BOTH counts: an ERRORED declaration**
(2026-07-25). A declaration whose proof fails to elaborate — `maximum
recursion depth`, a failing tactic, anything red — is `sorryAx`-tainted and
poisons the transitive cone, but it emits **no** `declaration uses 'sorry'`
warning and contains no `sorry` token in its source. So it is missed by the
direct-sorry warning set, missed by a source scan, and its `.olean` goes
stale, silently blocking every downstream module from building. Nobody is
ever dispatched at it, because no frontier scan can see it.

Found when `lineNumerator_mul_lineNumeratorNeg` in `WeilPairingDescent.lean`
— PROVEN and verified clean in its author's worktree — began failing after
merge with `maximum recursion depth has been reached`, blocking the whole
file. It surfaced only because an agent working in that file happened to
report it. **So: errors are a separate frontier that only a build or a
per-file `diagnostics` reveals. Treat any hard error as an immediate defect
with a named owner (CLAUDE.md's sorry-gate rule (b)), and do not assume a
clean direct-sorry scan means a clean tree.** A proof that verified in one
worktree can error on main; resource-limit `set_option`s are the usual fix.

**AND AN ERRORED DECLARATION DISGUISES ITSELF AS A MISSING ONE, IN THE SAME
FILE, HUNDREDS OF LINES AWAY** (2026-07-31, `HilbertClassFieldNormal.lean`). A
heartbeat timeout does not merely fail its own declaration — the declaration is
never added to the environment, so every later USE of it reports

    error: …:1029:8: (kernel) unknown constant 'NumberField.conj_unramifiedAbelian'

and that is the error a reader's eye lands on, because it is the last one lake
prints. It reads as a rename, a bad merge, or a declaration lost to a
merge-side removal — exactly the class-6/class-7 shapes this file spends pages
on — and every one of those diagnoses sends you to `git log -m -S` instead of
to the real cause 600 lines above. Here the real cause was two
`(deterministic) timeout at isDefEq` / `at whnf` lines earlier in the same log,
and the fix was one `set_option maxHeartbeats 1600000 in`.

**So read a build log from the TOP, and never diagnose an `unknown constant`
against a name that is declared in the very file being compiled.** If the name
is right there in the source, the constant is not missing — its declaration
errored. Grep the log for `timeout`/`maximum recursion` before touching git.

Two cost-shapes worth knowing, both from that declaration:

* The timeouts were `isDefEq`/`whnf` unification through stacked
  `AlgEquiv → RingHom → FunLike` coercions over `IntermediateField` subtypes.
  Files whose OBJECTS are intermediate fields cannot avoid this, so a heartbeat
  bump there is a legitimate fix rather than a smell.
* **`let`-binding a structure literal is the expensive way to name a map;
  `obtain`-ing it from an `∃` is the cheap one.** A `let`-bound literal stays in
  the local context and every subsequent `isDefEq` unfolds it. Destructing an
  existential makes the map a genuine free variable whose only handle is its
  characterising equation, and nothing can unfold it. Same mathematics, and it
  was the difference between elaborating and not.

**Fourth category, invisible to ALL THREE: a module UNREACHABLE from
`Fermat.lean` is never compiled at all** (2026-07-27). `lake build` builds the
root's import closure. A module no module in that closure imports is simply not
built — so it is invisible to `lake build`, invisible to the
`declaration uses 'sorry'` warning set, and invisible to the transitive census.
It can contain anything, including code that does not compile, and nothing will
say so.

At `a18c5c4d` there were **99** such modules — the whole vendored
automorphic-form / adele / Haar closure, 1690 floating declarations. It is also
a hard blocker for the census, which imports *every* module under `Fermat/`:
one unreachable module that fails to build takes the census down with it. A
release has since wired almost all of them in.

**Root cause, found 2026-07-27 and deeper than a forgotten import: the island was
exactly the set of project files NOT on Lean's module system.** 277 of 286 files
declare `module`; the only non-`module` files were `Fermat.lean`, `Basic`,
`PrimeFive`, `SorryGate` — and the five unreachable ones. **A `module` file cannot
import a non-`module` one** (`cannot import non-module ... from module`), so the
island was *structurally unimportable by any consumer that could plausibly want
it*. Nobody forgot an import; the import was **not expressible**.

The fix is the header treatment its already-wired siblings use: `module`,
`public import`, `@[expose] public section`. So when a module looks orphaned,
check its HEADER before hunting for a missing consumer — and note that wiring an
island in correctly RAISES the reported frontier, because its sorries become
visible for the first time. That is disclosure, not regression.

**Do NOT over-read that into "every name you use needs a `public import`" — that
is false, and the false version has been sitting in a leaf docstring telling
agents to edit a 71 000-line header** (measured and corrected 2026-07-31). A
plain `import M` makes `M`'s names available for elaboration in the importing
module; `public` only controls whether they are RE-EXPORTED to that module's own
importers. Since **theorem proof bodies are elided by the module system**, a
`public theorem` may use privately-imported constants freely. What needs a
`public` edge is a name occurring in a **statement**, or in the body of a
`def`/`abbrev`/`instance` that `@[expose]` publishes.
`ModThree.lean`'s `exists_local_hopf_tensor_etale_algEquiv_of_finite_hopf`
carried the note "whoever takes this leaf must add
`public import Fermat.FLT.GroupScheme.ConnectedEtale` — a transitively-reached or
private import does not make the names available even in proof bodies". The file
had imported that module privately since before the note was written, and 300
lines of new public theorems calling into it elaborate green against exactly that
configuration. The one edge that did have to be `public` was
`Mathlib.RingTheory.HopfAlgebra.Quotient`, because `Ideal.IsHopfIdeal` appears in
two of the new STATEMENTS. Check WHERE the name occurs before touching a header:
the test is one `lake env lean` on a scratch module mirroring the target's import
lines, about ten seconds.

**So a fourth standing check belongs in every bookkeeping cycle: enumerate
modules under `Fermat/` and subtract the root's import closure.** A newly
vendored subtree is the usual way modules land here — vendoring a directory
does not wire it to anything, and the tree looks green precisely because the
new code is not being compiled.

Second trap, same day: a naive `grep sorry` over sources counts the word
inside DOCSTRINGS, and this development's docstrings discuss sorried leaves
constantly. That inflated a scan to 144 "sorried declarations" against a
true 85. Any frontier scan must strip block comments (nested `/- -/`) and
line comments first, then attribute each surviving token to its enclosing
declaration by walking BACKWARDS to the nearest declaration header —
walking forwards mis-attributes a later declaration's sorry to an earlier
proven one, which is exactly how `exists_hardlyRamifiedLift` was twice
mislabelled open when it is proven.

Related: stale `(sorry leaf)` / `(sorry node)` docstring LABELS on
now-proven declarations are a third source of phantom work, since leaf
lists get harvested from them. Correct them when found rather than leaving
them to mislead the next dispatch.

**Tree markers in `PROGRESS.md` (Deyao, 2026-07-17): two symbols per
item.** Every tree item starts with exactly two symbols — first symbol
`✓` (proven here or in mathlib) or `✗` (sorry); second symbol `·`
(normal) or `○` (in progress, i.e. what the model is working on RIGHT
NOW). **Maintain the `○` marks as part of the loop: at the START of a
block of work, set the target node(s) to `○`; at the END of the block
(before/with the commit), set them back to `·` with the new `✓`/`✗`
status.** PROGRESS.md is GENERATED: edit `progress-entries.json` and
run `python3 progress-tree.py`; never hand-edit the tree.

**Use the mathematical literature actively.** When a node needs a proof
whose argument you cannot reconstruct, **download textbooks and papers**
— through the Anna's Archive MCP (`download_annas`; see the annas-mcp
section below) or from the open web — extract the relevant chapters
(see PDF Text Extraction below), and follow the book's argument in
Lean. Standard references for this project: Silverman *AEC* and
*ATAEC* (elliptic curves, Tate curve), Serre's 1987 Duke paper (§4.1,
the Frey-curve conditions), Mazur's torsion papers, Diamond–Shurman
(modular forms), Cornell–Silverman–Stevens (the FLT survey volume),
Neukirch (algebraic number theory, ramification/inertia). Also mine
`~/cs/FLT` (the reference Lean project; NOTE its mathlib pin has
drifted from ours — 81a5d2 vs a3364f as of 2026-07-24, so vendoring
requires a pin-drift audit, not verbatim copying) for
vendorable sorry-free material before proving anything from scratch.
Previously downloaded sources stayed in the dissertation repo — see
`SOURCES.md` for the list.

**CAS tooling (Deyao-approved, installed 2026-07-24): `gp` (PARI/GP,
via brew) and `Singular` (system) are on PATH.** Doctrine:
*untrusted searchers, never provers* — use them to FIND witnesses and
certificates (class numbers, principal-ideal generators, unit groups,
discriminants, Gröbner cofactor certificates for polynomial-ideal
memberships), then VERIFY the concrete witness in Lean
(`norm_num`/`decide`/`ring`/`linear_combination`). External output is
never itself a proof; the kernel remains the only authority. Also use
them to sanity-check a leaf's STATEMENT numerically before dispatching
a proof effort at it. Include an availability note in task prompts
for leaves in these classes.

## A GENERICITY LEAF IS OFTEN A SINGLE-WITNESS LEAF IN DISGUISE — check the direction

(2026-07-31, `MoretBailly.lean`.) Half the hard leaves in this development are of the form
"the GENERIC member of a family has property P": irreducible over the algebraic closure of
the parameter field, geometrically integral, nonsingular, dimension-preserving. The reflex
is to prove them by generic-fibre reasoning, which drags in `FractionRing`,
`AlgebraicClosure`, Gauss, and a base field nobody wants to compute in.

**Ask first whether the implication you actually need runs the OTHER way: does ONE good
`K`-rational member force the generic one?** Very often it does, and that direction is the
CHEAP one, because a factorisation (or a relation, or a degeneracy) over the generic fibre
has coefficients INTEGRAL over the parameter ring whenever the family is MONIC in one
variable — so it descends to a finite extension, and a maximal ideal over the chosen point
has residue field `K` again when `K = K̄`. Push the generic object through that residue map
and it specialises, contradicting the good member.

Concretely, `exists_basisPlane_irreducible_familyPlaneSection` (Schmidt Thm 3D step 2) was
a leaf asking for irreducibility over `\overline{K(y_0 … y_n)}`. It is now PROVEN over a
leaf that says only "some honest plane section of `h` is an irreducible two-variable
polynomial over `K`" — same leaf count, no fraction fields left in the statement. The
bridge is `irreducible_map_of_irreducible_eval_unit`, ~250 lines, over three mathlib bricks
none of which this project had used before:

* `Polynomial.isIntegral_coeff_of_dvd` (stacks 00H6) — the coefficients of a MONIC factor
  of a monic polynomial are integral over the base ring. No field, no fraction ring, no
  integrally-closed hypothesis; this is the whole engine.
* `Ideal.exists_ideal_over_maximal_of_isIntegral` — lying over, to reach the chosen point.
* `IsAlgClosed.ringHom_bijective_of_isIntegral` — the Nullstellensatz form: an integral
  extension field of an algebraically closed field is that field.

Two riders learned the same day. **Monicity is not a technicality — without it the
criterion is FALSE**: `(y·s + 1)(s + t)` is reducible over `K(y)` while its fibre at
`y = 0` is irreducible. And in this development monicity is usually already present under
another name — here it is exactly the leading-form clause `h_d(u₁) ≠ 0` that the leaf was
carrying anyway. **Look for the monicity you already have before concluding the route is
closed.**

For two-variable work specifically: `MvPolynomial.finSuccEquiv`,
`MvPolynomial.finSuccEquiv_coeff_coeff`, `MvPolynomial.natDegree_finSuccEquiv` and
`MvPolynomial.isIntegral_iff_isIntegral_coeff` are enough to move between
`MvPolynomial (Fin 2) R` and `(MvPolynomial (Fin 1) R)[X]` in both directions; "total
degree `≤ d` and the `s^d`-coefficient is a unit" is the usable spelling of "monic of
degree `d` in `s`".

## A BIG `F_q[X]` CERTIFICATE: FACTOR FIRST, TABULATE, AND KEEP EVERY COEFFICIENT POSITIVE

(2026-07-31, all three measured while proving `dvd_X_pow_card_pow_sub_X_hPolyElevenA`,
`H ∣ X ^ (23 ^ 11) - X` for a degree-`55` `H` over `ZMod 23`. The whole file is 159 s green;
the route its own cut docstring prescribed would have been ~40 minutes and RED.)

`ring` over `ZMod p` is the only tool for these, so the single thing that matters is how big
each identity is. Three levers, in decreasing order of payoff:

1. **FACTOR `H` FIRST.** A Frobenius table for a degree-`d` modulus costs `O(d²)` per entry
   and needs `d` entries, so it is CUBIC in `d`. Splitting `55` into five `11`s cut the work
   ~5×. `polisirreducible` in PARI hands you the factors; you never have to prove them
   irreducible — recombine with ten explicit Bézout `IsCoprime` certificates and
   `IsCoprime.mul_dvd`, which are ~264 monomial ops apiece and free by comparison.
2. **TABULATE, NEVER DIVIDE BIG.** The naive step `p ^ 23 - p' = h * q` has `deg q = 196`:
   **46 s for ONE such identity, and `ring_nf; reduce_mod_char` does not even close it.**
   Precompute `u i := (X ^ 23) ^ i mod h` for `i ≤ deg h`, then decompose each step as
   `p ^ 23 - p' = ∑ c i * (X ^ (23 * i) - u i)`. Every identity is then of degree `≤ 21`:
   **0.8 s.** What makes this legal is that over `ZMod p` the Frobenius is LINEAR —
   `f ^ p = f.comp (X ^ p)`, from `Polynomial.map_frobenius_expand` plus
   `ZMod.frobenius_zmod` (note `Polynomial.expand_char` is DEPRECATED in this pin; the live
   name is `map_frobenius_expand`).
3. **STATE THE WITNESS ALL-POSITIVE.** `reduce_mod_char` rewrites `-1` to `22` and then
   leaves an unnormalised `22 * (X ^ 2 * 6)` sitting in the goal, which `ring_nf` has already
   run past — the identity is TRUE and the tactic block fails anyway. Do not chase it with
   more `ring_nf; reduce_mod_char` rounds; remove the minus sign instead. `rw
   [sub_eq_iff_eq_add]` turns the `Dvd` witness goal `A - B = h * q` into `A = h * q + B`,
   after which no negative coefficient exists to be mangled.

Two smaller notes. `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X` is the converse
direction and already in the pin. And GENERATE the file from a script that re-derives every
certificate in a second, independent implementation of `F_q[X]` arithmetic and asserts each
identity before emitting it — every one of the ~2300 lines here was checked in Python before
Lean ever saw it, which is why the first full build had zero errors.

### MEASURED at degree `34`: ~14 min wall per factor, 9.3 GB — the `p = 17` rows ARE affordable

(2026-07-31, `flt-lean-343`, `ZMod 67`, one degree-`34` irreducible factor of the `p = 17`
row's `H`, `m = 34`, elaborated twice on an otherwise-busy `quicksilver`:)

    WALL=987 s
    WALL=829 s   CPU=6989 user + 7013 sys = 14 002 s   MAXRSS=9.3 GB   EXIT=0

Against the whole `p = 11` file — five factors of degree `11`, `m = 11` — at **159 s** idle
and **578 s** under fleet load, that is a per-factor wall blow-up of roughly **7–26×**, well
under the **~90×** that the cost model predicts (`O(d²)` per table entry × `d` entries × `m`
steps is cubic in `deg h`, linear in `m`; `(34/11)³ × (34/11) ≈ 90`). The parallel elaborator
absorbs the rest — see the correction below. **So a `p = 17` row is four factor-blocks at
~14 min each, and both rows are a job of hours, not days.** What to watch is not time but
**memory**: 9.3 GB for ONE factor, so a four-factor file wants headroom in the tens of GB.

Lever 1 (factor first) is what makes the route work at all; it does not make `d = 34` behave
like `d = 11`, since a degree-`34` irreducible cannot be split further. For the `p = 37` row
(`deg H = 666` as `222³`, `ℓ = 397`) the model gives `222³/34³ ≈ 278` on top of the above,
which is what the "DO NOT DISPATCH A PLAIN COMPUTATION AT THIS ROW" note in `X0.lean` is
about; that note stands.

### `/proc` utime+stime IS NOT WALL TIME — and "one core per file" is FALSE for generated files

Both halves of this cost real effort on the same day, and the first nearly went into this
file as a fact.

Watching the probe through `/proc/<pid>/stat` fields 14+15, I read **1631 → 3843 → 4747 CPU-s**
on a run that had started ~16 minutes earlier, and was about to record "still elaborating
after 79 CPU-minutes, never finished". It had in fact finished, in **987 s**. The reading was
right; the interpretation was not — utime+stime sums **all threads**, and this file was
running **110 threads at ~15–17 cores**. A `/proc` CPU delta overstates elapsed time by
exactly the parallelism factor, so **never compare a CPU-seconds reading against a wall-clock
budget.** Wrap the run in `/usr/bin/time` and read `%e`.

That also corrects the standing claim in the throughput section above that **"elaboration is
single-threaded — one core per file"**. Lean elaborates *independent top-level declarations*
in parallel, and here reached ~17 cores. Both observations are true of the files they were
made on, and the discriminator is **dependency structure, not size**: a GENERATED certificate
is thousands of mutually independent theorems and parallelises almost perfectly, whereas
`Interface.lean` — where the original one-core measurement was taken — is a long dependency
chain and cannot. So "split the file to win cores" applies to hand-written chains; a generated
file already gets them. Note the cost: `sys` time here equals `user` time, so ~14 000 CPU-s
buys 829 s of progress — cheap in wall-clock, expensive in machine.

### The coprimality certificate: REDUCE FIRST, or the Bézout cofactor has degree `q ^ k`

A row where some `d > 1` divides `m` and is `≤ n` — the `p = 17` rows, `d = 2` — needs
`IsCoprime H (X ^ (q ^ d) - X)` on top of the divisibility, because
`not_monic_dvd_of_smallDegreePart`'s `hmn` fails there. Writing that Bézout **directly** is
hopeless: a certificate `s * H + t * (X ^ (q ^ 2) - X) = 1` has `deg s ≈ q ^ 2 = 4489`.

Do it mod `h` instead. `X ^ (q ^ 2)` is ALREADY reduced by the table — it is the chain's
`p 2` — so certify `IsCoprime h (p 2 - X)`, where both cofactors have degree `< deg h`, and
transport it along the congruence with

    theorem isCoprime_of_dvd_sub {R} [CommRing R] {a b c : R}
        (hab : IsCoprime a b) (hc : a ∣ c - b) : IsCoprime a c := by
      obtain ⟨u, v, huv⟩ := hab; obtain ⟨k, hk⟩ := hc
      exact ⟨u - v * k, v, by linear_combination huv + v * hk⟩

then recombine the factors with `IsCoprime.mul_left`. `flt-frobenius-cert.py` emits all of
this under `--coprime-exponent k`; verified green end to end.

### A GENERATOR'S ROUND-TRIP TEST EARNS ITS KEEP — it caught a shadowed parameter

`flt-frobenius-cert.py` claims that regenerating its committed output reproduces it byte for
byte. Running that check while ADDING the coprimality option found two things at once. The
real one: the recombination loop wrote its accumulator to a local named `cop`, which is also
the function's `--coprime-exponent` **parameter** — so after the loop `cop is not None` was
always true and *every* run silently emitted a coprimality block, with the Bézout expression
interpolated into the docstring where the exponent belonged. Nothing about the output looked
malformed enough to notice by eye in a 2300-line file.

The second: the committed `MazurNonCMFrobenius.lean` did **not** round-trip, because it
predated the tool's generalisation from `23` to any `q` (`pow_twentythree` → `pow_frob`,
`d12`/`d123` → `d2`/`d3`). The claim in the docstring was simply false, and a regression test
that is known to fail is a regression test nobody runs. Both files are now regenerated and
both round-trip. **If a generator says its output round-trips, run it — and if it does not,
fix the file rather than softening the claim.**

## Continuous work loop: never stop while the frontier is nonempty

Two mechanisms keep the formalization going continuously; use both,
always (Deyao, 2026-07-16).

**Mechanism 1 — the tool-call loop.** Do not end the turn after
completing one or two iterations; a reply containing a tool call is
itself the prompt to keep generating. The loop is: ask the compiler
whether any `sorry` remains; if yes, pick a node and run the full
iteration (resolve or decompose → verify → axiom audit → commit/push →
update `PROGRESS.md`) and then **re-check and continue**. Only an empty
frontier or a genuine blocked-on-user decision ends the turn. Summaries
belong in commit messages and `PROGRESS.md`, not in turn-ending chat
messages. Nothing is "below" anything: never triage a sorry out of
scope — every sorry is an active frontier node.

**Mechanism 2 — the Stop hook.** `.claude/settings.json` registers a
`Stop` hook running `.claude/check-sorries.py` (Python). The hook fires
exactly when Claude tries to end its turn and vetoes it: exit 2 +
stderr blocks the stop and feeds the message back to Claude (exit 0
allows the stop; any other exit code is a non-blocking error — so never
exit 1 on "failure"). The script checks the loop's single exit
condition by asking the Lean compiler through the persistent
environment server (`lean-daemon.py` at the repo root, autostarted on
demand; it keeps a `lake env lean --run` child alive holding the fully
imported environment and answers JSON queries over a Unix socket in
seconds, restarting the child only when the built `.olean`s change):
the child reports every project declaration whose proof term uses
`sorryAx` plus the root-cone status of `fermat_last_theorem`, and the
hook blocks while any remain. The daemon reflects the last built state
(modules edited since are flagged `stale_sources`); only when it
reports zero sorries does the hook run one confirming `lake build`.
`progress-tree.py` uses the same daemon. Deliberately NO
`stop_hook_active` guard; `CLAUDE_CODE_STOP_HOOK_BLOCK_CAP=1000`
raises the per-turn forced-continuation cap; Deyao terminates
externally. The hook only drives the session whose id is recorded in
`.claude/stop-hook-session-id` — a successor session must write its
own id there. Launch sessions at the REPO ROOT.

**Maximize work per turn — a hook reprompt for missed work is a
penalty.** (Deyao, 2026-07-16.) Do as much as possible in one turn:
chain many full iterations into a single turn rather than ending the
turn after one small step and letting the Stop hook re-prompt. The
Stop hook is a SAFETY NET, not a pacing mechanism. Before attempting
to end a turn, ask: is there an obvious next node, a mapped attack, or
an unfinished fix I could continue RIGHT NOW? If yes, continue in the
same turn. Reconnaissance must be embedded in the iteration that
consumes it, not stand alone as a turn.

**No giving-up prose — incapability must surface as a loop that cannot
exit.** The loop has EXACTLY ONE exit condition: the Lean compiler is
satisfied (`lake build` passes the sorry gate) and zero `sorry`
remains. There is no other exit — for each iteration, continue
regardless of how stuck the previous iteration was. When there seems
to be no way to continue, still make concrete attempts: write the
candidate statement or proof, run the compiler, let it fail, adjust,
fail again. A lack of capability must show up as *repeatedly failed
attempts inside a non-exiting loop* — never as a generated paragraph
of the form "I give up / I can't continue". Rationale (Deyao,
2026-07-16): a failed attempt in a loop that visibly cannot exit is a
mechanically checkable, trustworthy signal; a prose surrender is just
generated text. Deyao can always bring the program out of the loop
himself — external termination is his prerogative, not the program's.

**Mechanism 3 — the sorry gate: the root `#assert_no_sorry` is the
single source of truth.**

- *Warnings*: an open `sorry` node emits Lean's standard "declaration
  uses 'sorry'" warning and the module still builds.
- *The root gate*: the root module (`Fermat.lean`) ends with
  `#assert_no_sorry fermat_last_theorem` (command defined in
  `Fermat/SorryGate.lean`): elaboration throws a hard error while the
  top theorem depends on `sorryAx`, and also enforces the axiom
  invariant. This root gate is the sole mechanical completeness check.

Consequences: (a) `lake build` FAILING with exactly the `SORRY GATE
FAILED` error is the *expected* outcome during development — never
remove the gate; (b) any other build error is a genuine defect to fix
immediately; (c) scratch axiom-audit files must `import Fermat.Basic`
and specific leaf modules, never the root `Fermat`; (d) warnings are
not errors — keep the tree warning-clean by ordinary discipline.

**Fifth invisibility class, and by volume the worst: THE RELEASE WINDOW.
`main` IS NOT THE FRONTIER — it is the frontier as of the last release.**

Between an agent finishing and its branch reaching `main` there are hours. In
that window every ownership check this file prescribes gives the WRONG answer,
and they all agree with each other, which is what makes it convincing:

- `main`'s `declaration uses 'sorry'` warning set still lists the leaf;
- a freshly repointed worktree's source still shows the `sorry`;
- the three-part ownership test correctly says nobody is working on it —
  **because that agent already stopped.**

On 2026-07-28 this fired at least eight times in one cycle. Agents were
dispatched at leaves that were already proven (`exists_isDiffChar`,
`comap_le_range_units_integers_of_isCompact`, `isCompact_normOne_infiniteAdele`,
`finiteDimensional_h1_adZeroTwistRestricted`, two in `Patching.lean`), and — the
mirror image — at leaves that **did not exist on `main` at all** because they
had been *cut* on an unmerged branch (`map_pow_twentyFour_eq_self_of_potentiallyGoodModel`,
`exists_ringEquiv_quaternion_of_isTotallyDefinite`, the whole STEP 1a-i′ block in
`KhareWintenberger.lean`, `flat_of_surjective_of_isAdditiveOn`). One agent
produced a complete, green, duplicated degree-1 cochain API before discovering
the same dictionary already existed on the branch it had been told about, and
correctly discarded it.

**`~/.flt-inflight.jsonl` cannot see any of this, because it is PRUNED when a
worktree goes `batched`** — measured 158/158 `claimed` worktrees have a record,
**0/201 `batched` ones do**. So "no record names this leaf" matches *both*
"nobody has worked on it" and "its owner finished and the proof is queued".

The check that resolves it is one command, and it subsumes most of the batch,
because the merge worker merges branches into `merger` continuously:

    git show merger:<the file> | grep -n <name>

An agent that scanned all 54 branches carrying a modified `Patching.lean` found
three of its four candidates already proven — **all three were visible on
`merger` alone.** Then check the handful of `~/.flt-merge-batch` branches that
touch your file, since `merger` lags the batch.

And **a branch is not the whole picture either: check UNCOMMITTED work in the
other worktrees.** Two workers were sent at `henselianLocalRing_adicCompletionIntegers`,
and the decisive evidence was neither a record nor a branch — it was an
**untracked new file** in the incumbent's worktree holding that declaration,
relocated to a different generality under a new module path. That is a conflict
at *file* granularity, which no branch diff shows until merge time.

    for d in ~/flt-lean-*; do
      git -C "$d" status --short 2>/dev/null | grep -q . && echo "== $d" && git -C "$d" status --short
    done

Corollary for dispatch: **name the branch as an INSTRUCTION, not as attribution.**
"`flt-lean-311` proved X" in a credit line is not read as "merge `flt-lean-311`";
three successors fast-forwarded to a `main` without X and found nothing.

**THE UNDERSCORE TELL: on `merger`, read the BINDER LIST, not the body**
(2026-07-31, and it is one `sed` instead of one build). This development has a
hard convention — a hypothesis a `sorry` cannot consume is written `_hℓ`, and the
underscores come OFF when the leaf is proven. So

    git show merger:<file> | grep -n 'theorem <name>' -A6

answers "was this closed while I was being dispatched?" at a glance, and it
answers a second question no `sorry`-scan asks: **whether the SIGNATURE changed.**
`exists_isX1Compactification_specialFibre` was still a `sorry` on `main` and
proven on `merger` — and proven over a *different hypothesis*, the integral model
carrying `IsX1Compactification` rather than only its generic fibre. A check that
had only looked for the token `sorry` would have caught the first fact and missed
the second, which is the one that decides whether your work is a rival cut.

I had already written and VERIFIED GREEN a decomposition of that leaf when the
check ran. Landing it would have re-opened a closed leaf and conflicted with the
release; the right move was to revert my own green work. **A green build is not
evidence that your edit is wanted.**

**And check your payload against `merger` WITHOUT touching your worktree:**

    git merge-tree --write-tree --name-only merger <your-branch>   # prints a tree sha + conflicts
    git show <that-tree-sha>:<path> > /tmp/merged.lean             # the resolved file, markers and all

This is the cheapest instance of the class-7 check two sections below: strip the
markers, then grep the RESULT for every name your edit's interface touches. Mine
was a five-site statement change, and the merged file confirmed all five sites
landed and that no consumer on `merger`'s 3300 newer lines projects the changed
clause — a class-7 "clean merge that does not compile" ruled out in seconds, and
the one conflict located precisely enough to hand the merger a resolution instead
of a warning. It writes nothing outside the object store.

**The checks are TWO SCRIPTS answering DIFFERENT questions, and both must run**
(2026-07-29). `own.py` answers *is somebody working on it*; `leafstat.py` answers
*is it already done*. A dispatch this day named two leaves as "genuinely UNOWNED
— zero hits each in `~/.flt-inflight.jsonl`" and **both clauses were wrong in
different ways**: leaf 1 had five hits, one of them a `TARGET:` line
(`flt-lean-261`, dispatched 21 h earlier); leaf 2 had been PROVEN on `main` for
42 hours, at a commit that was an ancestor of the successor's own dispatch HEAD.

Re-run afterwards, `own.py` reported `flt-lean-261` correctly and instantly. The
tool was right; it had not been run — a hand `grep` was substituted for it. So
the failure was not a gap in the test but the orchestrator improvising around a
script written to stop exactly this. **Run the scripts.**

**`own.py` grew a FOURTH check the same day, and it is the one nothing else
covers: UNCOMMITTED work in the other worktrees.** The three-part test is about
RECORDS. An incumbent's proof can exist only as uncommitted work — invisible to
`merger`, to the batch, and to every branch diff, so `leafstat.py` cannot see it
either. `flt-lean-261` held 399 uncommitted lines of `Interface.lean` proving
its leaf *and renaming it* to `hasFiniteWildMonodromyAt_of_residueChar_ne`; a
successor sent at the old name would have raced a rename it could not observe.
`Interface.lean` had **nine** concurrent uncommitted editors at that moment.
`own.py` now greps every `claimed` worktree's diff plus its untracked `.lean`
files (a relocation lands as a new module, which is a conflict at *file*
granularity) and flags a name that appears in WIP with no record claiming it.

Unrelated but found while fixing it, and it had been corrupting every scripted
check run from the scratchpad: a scratch file named **`grp.py` shadowed the
stdlib `grp` module**, which `shutil`/`subprocess` import on POSIX — so every
python script run from that directory executed an unrelated group-theory
computation at import time and printed its output ahead of the real answer.
Renamed. Watch for scratch filenames that collide with stdlib modules.

**THE RELEASE-WINDOW CHECK HAS MOVED TO THE PROVER (2026-07-31), because the loop
cannot do it.**

Everything above about the release window is addressed to a dispatcher that can run
`own.py` and `leafstat.py` before sending anybody. Since 2026-07-30 the dispatcher is
`flt-loop.py`, a Python state machine: it builds its task list from `main` and has no
way to look at `merger`. `main` IS the frontier as of the last release, and `merger`
runs hours ahead of it. So the check is now the PROVER's, and it is the prover's FIRST
action — before reading the target, before seeding `.lake`:

    git show merger:<the file> > /tmp/x.lean     # then READ the declaration

Measured cost of skipping it, 2026-07-31, `flt-lean-300`: dispatched at three leaves in
`HilbertModularity.lean`, **all three already resolved on `merger`** (release 24, while
the worktree sat at release 23), and the session went into independently rebuilding one
of them. The rebuilt cut turned out to be architecturally identical to the landed one —
same three helper lemmas, and the same non-obvious extra hypothesis, that `ℓ` must be a
NONZERODIVISOR in the coefficient ring (without it `ZMod 4 → ℤ_[2]` refutes the
statement). Two agents converging independently on the same repair is reassuring about
the mathematics and is still one worker-cycle thrown away.

**Grep the NAME and you will conclude the opposite of the truth.** All three names were
present on `merger`. Two carried full proofs. The third had been RESTATED — same name,
different conclusion (`exists_hilbertAuxHeckeModuleData` now PRODUCES `diamond` and
exports `ker diamond = 𝔟_ex`, the repair its own §5a audit demanded) — so a prover
working from `main` would have spent the session proving a statement that has been
withdrawn, and the `sorry` on `main` would have looked like ordinary open work the whole
time. The check must read the DECLARATION, not match its name; and a docstring's own
"DO NOT DISPATCH A PROVER HERE YET" is evidence about the version you are reading, not
about the frontier.

Corollary for what you commit: when `merger` already closes your target, **decline your
own payload** rather than carrying a rival cut. The tie-break is "fewer OPEN leaves
after", and a landed complete proof beats a fresh decomposition every time — carrying
mine would have traded a closed leaf for an open one plus a large conflict. Say so in
the sentinel's `to_merger`, so that an empty or tooling-only diff is not read as the
dropped-merge bug of class six.

**AND THE MERGER-CHECK CAN CONFIRM YOUR LEAF IS OPEN WHILE ITS PROOF SITS 260 LINES
ABOVE IT IN THE SAME FILE** (2026-07-31, `flt-lean-82`).

The variant the rule above does not cover: the name IS on `merger`, it IS still
`sorry`, and the answer is still wrong — because a SECOND declaration with the
IDENTICAL statement under a DIFFERENT name is proven earlier in the same file.
`mem_idl_of_X7_mul_mem` (`sorry`, line 689) and `mem_idl_of_Pz_mul_mem` (PROVEN,
line 423) in `ProjectiveEquationAdd2.lean` are character-for-character the same
proposition. Two branches decomposed `idl_isPrime` the same way under different
names; a union-style conflict resolution kept both blocks, so the file carries the
whole decomposition twice — the saturation half is duplicated too
(`exists_pow_Pz_mul_mem_idl` / `exists_pow_X7_mul_mem_idl`, both open).

This is the worst shape the merger-check takes, because it does not fail: it
returns a positive, correctly-quoted `sorry` at the right line, and every
subsequent step — the task prompt's route, the section docstring, the sorry-warning
count — agrees with it. Nothing anywhere says "look for this under another name".

So when the merger-check finds your leaf open, do not stop there. **Read the
enclosing section, and grep for the STATEMENT rather than the name:**

    git show merger:<the file> > /tmp/x.lean
    grep -n '∈ idl' /tmp/x.lean          # a distinctive fragment of the CONCLUSION
    grep -n '^theorem' /tmp/x.lean       # then scan the section for near-twins

A duplicate block announces itself in the declaration list — two `idl_ne_top`-shaped
runs of the same shape, or one file with two "### Half two" section headings. In this
file the module docstring named the `X7` pair while the proven pair was `Pz`-named,
which is exactly the tell.

What to do when you find it: **delegate, do not re-prove.** Replace your `sorry` with
a one-line application of the existing proof, say in the docstring that the
declaration is a duplicate slated for deletion, and put the deletion in `to_merger`.
Do NOT delete the twin of a leaf that has its own live owner — deleting
`exists_pow_X7_mul_mem_idl` here would have destroyed another agent's in-flight
target for the sake of tidiness. Closing your own by delegation costs one line and
conflicts with nobody.

## A LINE-NUMBER MISMATCH IN YOUR TASK PROMPT MEANS YOUR WORKTREE IS STALE — not that the leaf is gone

(2026-07-31, `flt-lean-23`.) A task named three leaves at `X1.lean:13442`, `:13465`,
`:14526`. The worktree's `X1.lean` was **10 390 lines long**, so two of the three names
did not appear in it at all. The obvious reading — "already proven, or renamed, or the
queue is stale" — is the wrong one and would have burned the whole dispatch.

`HEAD` was `9a2ca10d`, an ancestor of `main` but ~200 commits behind it; `main`'s
`X1.lean` is 16 605 lines and every line number in the prompt matched it EXACTLY. The
worktree had simply not been fast-forwarded at dispatch.

So the first thing to run in any worktree, before reading the target at all:

    git rev-parse HEAD; git rev-parse main
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

**The line numbers in a task prompt are a checksum on your checkout.** If they land on
the right declarations, your tree is current; if they land in the wrong place or the
names are missing, merge `main` and look again *before* concluding anything about the
leaf. This is the cheap, local version of the "MERGE `main` FIRST, then full build,
then believe it" rule above — and note that it fires in the direction that produces a
false "already done" report, which nothing downstream would catch.

Corollary for the `.lake`: the release snapshot at `~/.flt-release-lake` records the sha
it was built from in `~/.flt-release-lake/sha`. `git diff --name-only <that sha> main`
is one command and tells you whether the snapshot is exactly current for Lean purposes
— it was here (the only diffs were `flt-loop.py` and `flt_loop_rows.py`), so an
`rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/`
took 47 s and made `lake build` a 63 s no-rebuild verify instead of an hours-long one.

## THE CHEAPEST LEAF TO CLOSE IS ONE NOBODY CONSUMES — grep every open leaf in your file for a CODE consumer, first

(2026-07-31, `RelativePicard.lean`, and it was worth two leaves in ten minutes.)
The standing checks ask *is this leaf open* and *is it owned*. Neither asks *does anything
use it*, and a leaf with no consumer is either dead code or a duplicate. One `grep` per open
name in the file you are already in settles it, and the arithmetic is unusual: a hit list
whose only entries are the declaration's OWN line and some docstrings means the leaf is
consumerless.

    grep -n '<leafName>' <the file>            # own decl line + prose only  ⇒  DEAD
    grep -rn '<leafName>' --include=*.lean Fermat/ | grep -v '<the file>:'

Here that flagged `exists_trivialization_sectionIdeal_at_section` and
`exists_trivialization_sectionIdeal_at` at once — and they turned out to be
**character-for-character the same proposition**, cut out of the same parent a day apart by
two branches and kept by a union-style merge. Confirm a suspected twin mechanically rather
than by eye, since these statements run to six lines:

    sed -n 'A,Bp' F | sed 's/<nameA>/NAME/' > /tmp/a; sed -n 'C,Dp' F | sed 's/<nameB>/NAME/' > /tmp/b
    diff <(tr -s ' \n' ' ' < /tmp/a) <(tr -s ' \n' ' ' < /tmp/b)

**What had orphaned them is worth recognising on sight: a RESHAPING orphans BOTH halves of an
earlier cut at once.** `isInvertibleSheaf_sectionIdeal` had been re-stated about a bare
morphism (`…_of_isSection`) instead of about a base-changed curve — a good change, and it made
the reshaped parent unable to consume *either* old half, since they still spoke of
`relSection x` on `curveBaseChange strX g`. That is `DELETE × REFACTOR` with *refactor on both
sides*: nothing is deleted, nothing conflicts, no scan complains, and the file silently owes
one theorem three times.

The repair is mechanical once seen, and it is the good kind of −2: **delete the duplicate,
RESHAPE the survivor into the form the reshaped parent needs, and prove the parent over it.**
Here the parent's own docstring had already written down the cut (`by_cases` on
`z ∈ Set.range σ.base`, on-image = the leaf, off-image = an already-proven lemma), so the
proof was six lines. Two riders:

* **a reshaping that ENLARGES the quantified class voids the inherited faithfulness audit** —
  "every proper smooth relative curve" is strictly more than "every base change of a fixed
  one". Re-run it. Here both witnesses survived verbatim *because they had always been stated
  as curves over a base rather than as base changes*, and one clause had to be ADDED, for the
  hypothesis the old form got for free from `relSection` being a section by construction;
* **check the deletion is clean by grepping the dead name afterwards.** The only surviving hit
  should be the sentence in the survivor's docstring that records the deduplication — and say
  in it how to recover the deleted text (`git show <commit>^`).

## A `Nonempty (A ≅ B)` LEAF SHOULD BE RECUT AS `IsIso <named map>` — the map is usually FORMAL, and it is what every route needs first

(2026-07-31, `RelativePicard.lean`, `nonempty_modPullback_sectionIdeal_of_isPullback`.)
A leaf whose conclusion is `Nonempty (A ≅ B)` names no morphism, so a prover has to invent
one before any mathematics can start — and every route invents the SAME one. Build it, prove
it exists, and leave `IsIso` of it as the leaf. The trade is one leaf for one leaf, and what
changes is that the residual is a statement about a *named term* instead of an existential
that a prover could satisfy by an unrelated isomorphism.

**The construction is usually adjunction bookkeeping and nothing else.** Here `A = φ^*ker η_σ`
and `B = ker η_{σ'}`; the map is `φ^*(kernel.ι) ≫ (unit iso)` lifted through `kernel.lift`, and
the side condition is discharged by transposing across `σ'^* ⊣ σ'_*`:

* `F.map (kernel.ι η) = 0` where `η = adj.unit.app X` — because `F.map η` is a **SPLIT MONO**
  (`Adjunction.left_triangle_components` is literally its retraction), so
  `F.map (kernel.ι η) ≫ F.map η = F.map (kernel.ι η ≫ η) = F.map 0 = 0` cancels. This uses
  nothing whatever about the morphism `σ` and is four lines;
* transport that across a commuting square with `Scheme.Modules.pullbackComp` /
  `pullbackCongr` plus a three-line `map_eq_zero_of_natIso` (`F ≅ G`, `G.map u = 0` ⟹
  `F.map u = 0`);
* then `u ≫ adj.unit.app N = 0` follows from `F.map u = 0` by UNIT NATURALITY —
  `u ≫ unit.app N = unit.app M ≫ (F ⋙ G).map u` — not by a `homEquiv` computation.

Both `Scheme.Modules.pullback f` and `pushforward f` are registered `Additive` at this pin, so
`Functor.map_zero` is free; do not go looking for a `PreservesZeroMorphisms` instance to build.

**Say in the commit that the count did not move**, and say what got smaller instead. A
`−1 +1` warning-set delta is indistinguishable from "nothing happened" to every scan.

### THE `(𝟭 C).obj X` WRAPPER ON ADJUNCTION COMPONENTS BREAKS `rw`, AND THE ERROR PRINTS TWO IDENTICAL TYPES

Three round trips went to this and it will bite anyone touching `Adjunction.unit`/`counit`.
`adj.unit.app X : (𝟭 C).obj X ⟶ (F ⋙ G).obj X`, so every object downstream of it carries a
`(𝟭 _).obj` wrapper that is `rfl`-equal to the bare object and **not** syntactically equal.
Consequences, each observed:

* `have htri : … = 𝟙 _ := adj.left_triangle_components _` elaborates the `_` from the LHS and
  produces `𝟙 (F.obj ((𝟭 C).obj X))`, where the surrounding term wants
  `𝟙 ((𝟭 D).obj (F.obj X))`. `rw [htri] at key` then makes `key` ill-typed at `instances`
  transparency and the NEXT rewrite fails with a message about the wrong lemma;
* `simpa using key` fails reporting **`term key has type <T> but is expected to have type <T>`**
  with the two `<T>` printed character-for-character identically;
* `rw [comp_zero]` fails with `Did not find an occurrence of the pattern ?m ≫ 0` on a goal that
  visibly displays `f ≫ 0 = 0`, leaving `⊢ 0 = 0` that `rfl` does not close.

The cures, in order of preference: **do not create the `≫ 𝟙` in the first place** — get
`f = 0` from `f ≫ g = 0` with `g` a split mono via `Limits.zero_of_comp_mono` and
`IsSplitMono` built directly from the triangle identity, rather than by cancelling an
identity; and **use a defeq-checking tactic where `rw` fails** — `exact comp_zero` closes what
`rw [comp_zero]` cannot, and `refine h.trans ?_` crosses the `(𝟭 _).map u` vs `u` gap that
`rw [h]` cannot. This is the same family as the standing "printed pattern equals printed
target ⟹ switch to `exact`/`Eq.trans`" rule, with a new and very common cause.

### `lake env lean` ON A 6000-LINE MODULE EXCEEDS THE 10-MINUTE FOREGROUND LIMIT

`RelativePicard.lean` was ~4400 lines when the task prompt was written ("~25 s with
`lake env lean`, so develop against the real file") and is 6100 now; one elaboration is well
over ten minutes and a foreground Bash call dies with exit 143, which reads like a kill.
**Re-measure a prompt's stated iteration cost before believing it** — these files grow by
thousands of lines per release. The scratch-module route was ~100 s per round here (one
`public import` of the target's own built olean, restating the new declarations under
throwaway names), i.e. a 6× round-trip win, and the text moved into the real file compiled
first try.

## TWO WAYS TO CUT A LEAF THAT LOOKS ATOMIC (2026-07-31, both worked first try)

Both came out of `ModularCurve/RelativePicard.lean`, both closed a leaf the same
day, and both are cheap enough to try BEFORE concluding a node is irreducible.

**1. The leaf's own audit may misattribute where a hypothesis's content comes
from — and separating the two IS the cut.** `nonempty_modPullback_sectionIdeal`
was priced as "`φ^*` does not commute with a kernel; the content is that `D_x`
is FLAT over `T`, which is the content of `isInvertibleSheaf_sectionIdeal` (an
effective relative Cartier divisor is flat over the base)". The last clause is
**false**: invertibility of the ideal is Cartier-ness and says nothing about
flatness. Witness — `T = Spec k[s]`, `Y = Spec k[s,t]`, `D = V(st)`: the ideal
`(st)` is invertible (`st` is a nonzerodivisor) and `D` is not flat over `T`
(`s·t = 0` with `t ≠ 0`). The flatness actually came from a hypothesis the audit
never mentioned — `x` is a **section**, so `D_x ≅ T` over `T`. Once the two
inputs were seen to be independent the leaf split with nothing left over:
invertibility stayed a leaf, flatness became one `pullback.lift_snd`, and the
residual statement lost every mention of a curve (it is now Stacks 062Y/0631
over an abstract cartesian square). So: read a leaf's audit for sentences of the
form "X is the content of Y", and **check them**. A wrong one is a cut line.

**2. Never ask a geometry leaf to produce a bundled algebraic structure.**
`exists_relPicZeroSubgroup` asked for an `AbelianSchemeStruct` on `Pic⁰` —
twelve fields, of which nine are group axioms and two naturality. Not one of the
nine is about the identity component; they are the group axioms of `Pic`,
restricted to a subgroup, so the geometry's owner had to reprove them from
scratch. Replace the structure with **closure clauses** — the image contains the
zero point and is closed under addition and negation, each a bare existential
with no equation to verify — and transport the structure along the injection:
`ab.add p q` is the unique preimage (existence from closure, uniqueness from
injectivity), and every axiom is `inj` applied to a rewrite chain ending in the
corresponding law upstream.

The prerequisite is that the upstream laws exist. Here they did not, and proving
them was the bulk of the work — but each was `hP.inj` applied to a chain of
`RelPicEquiv`s (unitor, associator, braiding, `exists_modTensor_inv`), and all
six elaborated on the first attempt. **Generalisable rule: whenever a leaf's
conclusion contains a bundled structure, ask which fields are INHERITED rather
than constructed. Inherited fields belong in the assembly, never in the leaf.**

Corollary for bookkeeping, since neither cut moved the direct-sorry count: a cut
is one leaf closed and one opened, net zero. **Reading the count alone reports
that nothing happened.** Judge a cut by whether the open statement got smaller —
here one lost every mention of a curve and the other lost nine group axioms —
not by the delta.

**Pin trap found on the way**: `pullback.lift_fst` / `lift_snd` are `@[reassoc]`
but **not** `@[simp]` at `a3364fa`. A plain `simp` on a goal full of
`pullback.lift` silently does nothing and reports "unsolved goals" with the goal
unchanged, which reads as "this is hard". Name them in the simp set.

## A STALE WORKTREE MAKES YOUR OWN TARGET LOOK LIKE A PHANTOM — check the base BEFORE the target

(2026-07-31, `flt-lean-390`.) A task named three leaves with file-and-line references. Two of
the three names did not exist anywhere in the tree, and the third sat ~3600 lines away from the
line the prompt gave. Every naive reading of that is wrong in an expensive direction: "the queue
is stale", "these were renamed", "already proven and the entry survived", "the line numbers were
guessed". The correct reading was none of those — **the worktree was 704 commits behind `main`**,
and the prompt had been written against `main`. After one `git merge --ff-only main` all three
names resolved at exactly the lines the prompt gave, to the character.

The dispatch hook is documented to fast-forward a worktree to `main` at allocation. It did not
here, and nothing in the worktree announces that: `git status` was clean, the branch was a proper
ancestor of `main`, and `git log -1` showed a perfectly ordinary recent-looking commit — a merge
into `merger` from two days earlier, which reads like current work rather than like a stale base.

**So the first command of any task, before reading the target file, is:**

    git rev-list --count HEAD..main     # 0, or you are working against the past
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

This is the same class as the RELEASE WINDOW entry above and its exact mirror image. There, the
leaf is closed on a branch and `main` has not caught up; here, the leaf is *open on `main`* and
your checkout has not caught up. Both make a real target look like a phantom, and both are
invisible to every ownership check in this file, because those checks all reason about records
and branches rather than about **which commit you are standing on**.

Corollary, and it is what makes this cheap to get right: **a file-and-line reference in a task
prompt is a checksum on your base.** If the declaration is not at the named line, do not start
hunting for a rename — check `HEAD..main` first. It costs one command and it is right more often
than any of the interesting explanations.

## THE RELEASE-WINDOW CHECK IS THE PROVER'S FIRST ACT, NOT THE ORCHESTRATOR'S

(2026-07-31, flt-lean-106, and it cost a full duplicate of a day-old file.)
The fifth-invisibility-class section above is written as advice to whoever
DISPATCHES. It is at least as much advice to whoever RECEIVES: a prover agent's
task prompt was built from `main`, and `main` is the frontier as of the last
release. **Run `git show merger:<file> | grep -n <declName>` for every leaf in
your prompt BEFORE your first edit** — it is one command per name and it is the
only thing standing between you and re-doing finished work.

What it cost here, concretely. Three leaves were named. On `merger`, two of the
three were **already proven** (`intBasis_indep_of_isCMByRamifiedMaximalOrder`,
`exists_isogenyCurve_thirtySeven`) and the third's missing bridge already existed
as a better-stated leaf with its own owner (`exists_end_of_relPointEndo`, which
strictly subsumes the `exists_endTransport_of_isCMByRamifiedMaximalOrder` this
worktree cut). Worse, `merger` already carried a
`Fermat/FLT/EllipticCurve/ThirtySevenKernelPolynomials.lean` at the SAME module
path, closing the SAME two rows, reached by the SAME quadratic-twist-by-`37`
insight, written a day earlier. Roughly a megabyte of generated Lean was
produced, compiled and verified for nothing.

Two things make this trap sharper than the section above suggests:

- **The prompt's own leaf list is the bait.** Every ownership check said the
  leaves were unowned, and every one was right: the owners had already stopped.
  "Nobody is working on it" and "it is already done" are the same observation
  from `main`.
- **A NEW FILE you are about to create is the highest-risk case, and the one
  nobody checks.** Ownership tests are written around declaration names in an
  existing file. A file that does not exist on your base has no name to grep and
  no `TARGET:` line to match, so it passes every test — while being exactly what
  a sibling agent decomposing the same leaf would also create, under exactly the
  same obvious name. So: **before writing a new module, `git show merger:<path>`
  and `git ls-tree merger -- <dir>`.** One command, and it is the only check
  that sees this.

The salvage, which is worth knowing because it turns a wasted run into a real
result: an independent second computation of a landed certificate is a genuine
cross-check. `gen37.py` was re-pointed at `merger`'s two models — different from
the ones it had generated — and re-confirmed `r_37 = 0` and the vanishing of the
reduced `multComp` sum at both rows. So the report to the merger is not "I
duplicated your work" but "your certificates are independently verified, decline
mine".

## SEED BEFORE SPAWNING THE NEXT MERGE WORKER — the snapshot comes from the staging `.lake`

(2026-07-29, orchestrator error.) `flt-cycle.py release` seeds worktree artifacts by rsyncing
`MERGER_LAKE = /scratch/chend-flt/flt-staging/.lake/build` — **the merge worker's own build
directory**, hardcoded, with no option to point it elsewhere. So the sequence is not negotiable:

    merger reports green  ->  flt-cycle.py release   (snapshot + seed)
                          ->  dispatch the queue
                          ->  THEN spawn the next merge worker

I spawned release 19's worker first and then ran the seeding. Phase 1 (advance every worktree,
cheap) completed; phase 2 aborted on the built-in **torn-snapshot guard** — `.trace` files with no
matching `.olean`, for `ModThree` and `MazurTorsion`, because the next worker was mid-build in that
very directory. The guard is right and saved a fleet-wide seeding of a half-written olean set; it
also leaves the pool with everything `free` and **nothing `ready`**, i.e. dispatch blocked until the
next release.

There is no recovery that does not wait: `~/.flt-release-lake/build` holds only the *previous*
snapshot (days stale by then), and the release-18 artifacts are gone because the worker overwrote
them starting release 19. Hand-copying from a live worktree is precisely what the guard exists to
prevent. **The cost of getting the order wrong is one full release cycle of idle seeding capacity.**

Corollary worth stating separately: `release` is two phases with very different costs, and only
phase 2 needs the staging worktree quiet. If the order is ever wrong again, phase 1 has still run —
so every worktree IS advanced to the release, and the only thing missing is artifacts. Agents own
their own `.lake` and can rebuild; the loss is throughput, not correctness.

## TWO RIVAL CUTS OF ONE CLUSTER, BOTH MERGED, IS A CYCLE THAT LOOKS LIKE TWO INDEPENDENT SORRIES

(2026-07-31, `flt-lean-334`, `HopfAlgebra/ShortExact.lean`.) The task said "`flat_finrank_cartierDual`
is the ONLY sorry in that file". On `merger` the file had **two**, and the second was not a new leaf
— it was the *old* root of the same cluster, re-introduced by merging a branch that predated the
re-cut. Both routes were mathematically fine. Together they were a **cycle**:

    route A:  exists_lift_span_sup_jacobson  ->  exists_lift_ker_le_span  ->  exists_spanning
                                             ->  exists_basis_cartierDual
    route B:  flat_finrank  ->  nonempty_basis_chooseBasisIndex  ->  exists_lift_ker_le_span  -> ...

Each route derives the other's root from its own. Lean cannot see the cycle, because declaration
order breaks it: whichever root is textually first is a `sorry` and the other is "open" too, so the
file simply carries **two** obligations where it should carry one. Nothing is red. No frontier scan
flags it. Every `declaration uses 'sorry'` warning is honest. It reads as ordinary decomposition
progress, and it is the exact opposite — the merge DOUBLED what the file owes.

**The tell is that the two sorries are visibly about the same mathematics**, and that one of them
has a docstring deriving the other. Whenever a file has two open leaves whose docstrings each cite
the other as the thing they replace, suspect this and check the merge-base: one of them almost
certainly arrived from a branch that forked before the re-cut.

**The resolution rule, and it is decidable rather than a matter of taste: keep the arrangement whose
root leaf is IMPLIED by the rival's root.** That leaves the file owing strictly less. Demote the
rival's declarations to PROVEN corollaries placed below the shared cut, and say in their docstring
that they are corollaries and why moving them back up is a cycle. Here `flat_finrank_cartierDual`
(flat + constant fibre rank) implies the Jacobson generation leaf, so the Jacobson leaf was kept as
the root and `flat_finrank_cartierDual` was closed in ~10 lines from `exists_basis_cartierDual`.
Net: one file, two sorries -> one sorry, and the survivor is the weaker obligation.

Corollary for dispatch: **"the only sorry in that file" in a task prompt is a claim about the commit
the prompt was written against, not about your tree.** Regenerate it — strip comments, grep `sorry`
tokens, compare against the build's warning set — before believing the file has the shape you were
told.

## IF YOUR TARGET IS NOT IN YOUR WORKTREE AT ALL, YOU ARE ON `main` AND `main` IS BEHIND `merger`

(Same task, same day.) The worktree was dispatched onto `main`, and `flat_finrank_cartierDual` did
not exist anywhere in the file. Not renamed, not moved — absent. `main` was **867 commits behind
`merger`**: release 27 had been built on `merger` and not yet promoted, so `main` was two releases
stale while every task prompt was being written against `merger`'s frontier.

This is the "release window" trap in its sharpest form: the usual symptom is a leaf that is already
proven, and this is the mirror — a leaf that does not exist yet. Both come from the same cause and
both are resolved by the same one-line check *before* reading anything:

    git log --oneline -1 main merger
    git merge-base --is-ancestor main merger && echo "main is BEHIND merger"

If `main` is behind, `git merge --ff-only merger` first and work there. The merge worker merges into
`merger`, so basing on `merger` costs nothing and a branch based on a stale `main` silently
re-litigates hundreds of commits at merge time.

## SEVENTH invisibility class: a RED module UPSTREAM hides your module's own errors
(2026-07-31, `flt-lean-79`.) `lake build <Module>` builds an import closure and stops
at the first red module in it. So when `X0.lean` is red — as it was on `merger` at
release 27, 101 errors, mid-repair — **`Patching.lean` is never compiled**, and its own
errors are invisible to `lake build`, to the `declaration uses 'sorry'` warning set, and
to every frontier scan. On that day `Patching.lean` had **52 errors of its own** and
nothing in the fleet could see one of them.
This composes with the other six rather than replacing them: the red upstream module has
a named owner and is being worked on, so the situation reads as "someone is on it" when
in fact a second, unowned, unrelated breakage is sitting behind it.
**The workaround is one command and it does not need the upstream repaired.**
`lake env lean` consumes whatever `.olean`s are on disk and does not rebuild imports, so
restore the red module's artifacts from the last good snapshot and elaborate YOUR file
directly:
    cp -p ~/.flt-release-lake/build/lib/lean/Fermat/FLT/ModularCurve/X0.* \
          .lake/build/lib/lean/Fermat/FLT/ModularCurve/
    lake env lean Fermat/FLT/Modularity/Patching.lean
(A failed `lake build` DELETES the stale outputs of the module that failed, which is why
the copy is needed at all — the first symptom is `object file '….olean' does not exist`.)
The snapshot olean is stale, so treat cross-module errors with the usual suspicion; but
errors internal to your file — parse errors, arity mismatches, unknown identifiers
declared in the same file — are real and are yours to fix.
## READING A MERGE SPLICE: three signatures, and one message that does not mean what it says
Same day, same file. Textual merges in this development produce a recognisable damage
pattern, and one of its symptoms is systematically misread.
* **`error: unexpected token ':='; expected command`** — two declarations spliced: one's
  signature followed by another's `:= by` and body. Seen as
  `… = (taylorWilesAug p q).map diamond :=` immediately followed by
  `Function.Surjective pres := by`.
* **A stray line inside a proof body** (`      (∀ i, n ≤ e i) ∧` between two `obtain`s) —
  a leftover of a conclusion that was edited on one side.
* **A lost `/--`** — the deadliest, because it reports NOTHING at the damage site. The
  prose of the next docstring is absorbed into the previous declaration's *value*, and
  with `autoImplicit` on, every word becomes an auto-bound implicit and the declaration
  elaborates to junk. `abbrev taylorWilesCoordModel … := Fin d → … ⧸ taylorWilesLevelIdeal p e`
  silently swallowed `see the reduction audit recorded there.` and the six lines after it.
**And the message that misleads:** `invalid use of explicit universe parameters, 'X' is a
local variable`. This does NOT mean `X` is shadowed. It means **`X` IS NOT IN THE
ENVIRONMENT AT ALL** — autoImplicit bound the unknown name as a local, and `X.{u, v}` on
a local is then illegal. So the message is a report about a declaration that failed or
was swallowed somewhere *above*, not about the line it points at. Four such messages
(`IsCohenCoefficients`) plus a dozen `Function expected at` (`taylorWilesCoordModel`) all
traced back to that one missing `/--` 8000 lines earlier.
Corollary for triage order: fix the FIRST parse error and the FIRST swallowed declaration
before believing any later diagnostic. In this instance 4 root defects accounted for
about 40 of the 52 reported errors.
## SEVENTH invisibility class: a RUNAWAY DOC COMMENT that deletes 50 declarations while the file still parses
(2026-07-31, `flt-lean-391`, found in `Modularity/Patching.lean` at release 27.) A `/--`
whose terminator a declaration-level merge drops does **not** produce a parse error. Lean's
block comments NEST, so some stray terminator further down — typically the one belonging to
an orphaned *rival* docstring the same merge left behind — closes it. The file parses. Every
declaration in between is silently a comment. Here that was **~1980 lines**, including
`IsCohenCoefficients`, `existsUnique_ringHom_wittVector_of_isNilpotent`,
`surjective_of_span_range_sup_map_eq_maximalIdeal` and `taylorWilesCoordModel`.
**Nothing points at the opening line.** The wound reports itself hundreds of lines away as
`Unknown identifier`, `Function expected at`, and — the unmistakable tell —
`invalid use of explicit universe parameters, X is a local variable`. That last one is what a
*swallowed* name becomes once `autoImplicit` binds it, and it cannot arise any other way,
because nobody writes `X.{u,v}` for a name they did not define. Seeing it, do NOT hunt for a
missing import: run a comment-depth scan (walk the text counting `/-` and `-/`, skipping `--`
lines at depth 0) and report every top-level block longer than ~400 lines. This file has
genuine 600-line docstrings, so length alone is not the signal — depth balance is.
Two traps in the repair itself. **A comment-open or comment-close token spelled inside
block-comment PROSE still nests**, so writing the note that records the wound can reopen it —
re-run the depth scan after editing, every time. And the matching stray terminator downstream
is usually attached to a rival declaration, so fixing only the opener flips the remainder of
the file into a comment instead.
Same release, same file, two more wounds of the same family worth naming: a statement whose
body was replaced by an orphaned rival body, giving `theorem foo : T := <term> := by …` (a
parse error, and one that truncates everything below it — so every error count on a wounded
file is a LOWER BOUND until the parse errors are gone); and a stray conclusion fragment
dropped INTO a tactic block. **Corollary for the merge worker: "every module except X builds"
is only true of modules the build REACHED.** X0 is upstream of `Patching.lean`, so the release
build stopped before it, and `Patching.lean`'s 50 errors were invisible — release 27's handover
called X0 "the only thing between this tree and a release" on exactly that basis. Elaborate a
suspected-unreached module directly with `lake env lean` against the previous release's oleans
before believing a whole-build claim about it.
## SIXTH invisibility class: a merge that fails, records success, and drops the payload

(2026-07-29.) `git merge flt-lean-243` printed `error: Unable to write index` and **still
produced a merge commit whose tree was byte-identical to the pre-merge tree** — none of the
branch's changes, while recording that branch as an ancestor. `git status` then reported "All
conflicts fixed but you are still merging", and `git commit --no-edit` sealed it without
complaint. Suspected trigger: the background `git gc` git itself starts ("Auto packing the
repository in the background") during a preceding merge, so the risk concentrates exactly where
branches are merged back to back.

This is worse than every failure class above it, because **the result compiles.** A green build
is not evidence; a dropped payload builds perfectly. The merged branch is then marked merged and
dropped from the batch, so the work is not merely missing — it is unrecoverable through the
normal flow, and the frontier looks like it regressed with no cause anyone can name.

It was caught only because a declaration the merge was supposed to prove was still `sorry`
afterwards. The check is one command per merge:

    git diff --stat HEAD^1 HEAD     # MUST be non-empty if that branch changed files

Empty for a branch that should have changed something → `git reset --hard HEAD^` and re-merge.
`git config --local gc.auto 0` in the staging worktree prevents background packing from firing
mid-merge; it is local and affects nothing else. This matters most for the merge worker, which
merges a hundred-odd branches in one run.

**Corollary, and the reason this belongs beside the other five: "the branch is an ancestor" is
NOT evidence that its content is present.** Every ownership and integration check in this file
that reasons from ancestry — subsumption claims, "X carries Y's commit", the merge-base test in
the three-part ownership rule — inherits this hole. Ancestry is a claim about the commit graph;
content is a claim about trees. Verify the tree when it matters.

**And the honest, non-buggy version of this bites just as hard (2026-07-29).** A merge that
resolves *against* a branch — `-s ours`, or "taking merger's side wholesale" — is CORRECT
behaviour and still leaves the branch a full ancestor while its declarations are gone.
`git merge-base --is-ancestor <branch> merger` returns SAFE; the leaf does not exist. An agent
was dispatched at `projective_localizedModule_quotient_range_of_lTensor_injective`, whose
defining commit `ace07c06` **is** an ancestor of `main`, and found the declaration nowhere in the
tree: merge `8ce9528e` had declined that whole route in favour of a rival cut that ends at two
leaves instead of three.

**The detection trick, because the obvious command hides it: `git log -S <name>` shows only the
commit that ADDED the name and nothing else, so the history reads as "added, never removed".
Removal inside a merge is only visible with `-m`:**

    git log -m -S '<declName>' --oneline -- <path>     # -m is what shows merge-side removals

So a leaf can be absent for three different reasons that all look alike from `main`: never cut;
cut on an unmerged branch (the release window); or **cut, merged, and deliberately declined**.
Only the third is permanent, and only `-m` distinguishes it. Before reporting a phantom name,
run that command — the merge's own subject line usually says which rival cut won and why.

## "It lands in the GLOBAL ring" is a cuttable leaf — Northcott plus a pigeonhole is ~40 lines

(2026-07-31, `Modularity/TateModule.lean`.) A recurring shape here is a leaf whose stated content is
*a coherent family of level data defines an element of a COMPLETION, and the content is that it lies
in the GLOBAL ring `𝒪_D`*. That sentence reads as atomic. It is not; it factors mechanically:

    coherent (s_b − s_a ∈ Iᵃ for a ≤ b)  +  UNIFORMLY BOUNDED representatives  ⇒  a global t ∈ 𝒪_D

and the second half is **pure algebra with no geometry in it**:
`NumberField.Embeddings.finite_of_norm_le` (Northcott — the algebraic integers of `D` whose
archimedean absolute values are all `≤ C` form a FINITE set), pulled back along the injective
`algebraMap (𝓞 D) D`; pigeonhole the witness sequence `u : ℕ → 𝓞 D` onto a value `t` attained at
INFINITELY many levels; then for each `n` pick `m > n` with `u m = t` and split
`t − s_n = (u_m − s_m) + (s_m − s_n) ∈ Iᵐ + Iⁿ = Iⁿ`. About 40 lines.

It does not reduce the leaf count — one `sorry` replaces one `sorry` — and it does not touch the
missing theory. What it buys is that the residual leaf is a **BOUND**, which is the form the
literature states and names (here `‖φ t‖ ≤ 2√N`, the Riemann hypothesis for abelian varieties),
instead of a mixed completion-versus-global assertion that reads as mysterious.

Two traps, both about quantifier order, and both fatal to the cut:

* State the bound hypothesis as `∀ n, ∃ uₙ`, **never** `∃ u, ∀ n`. The strong form is what is
  classically true, and modulo `⋂ₙ Iⁿ = 0` it is EQUIVALENT to the conclusion — stating it makes the
  new lemma vacuous and the "proof" a one-liner that has moved nothing.
* Leave the constant EXISTENTIAL (`∃ C, ∀ n, ∃ u, …`) unless a consumer reads its value. Baking a
  numeral in makes the leaf harder than the consumer needs and risks a false leaf if the constant is
  off by a factor.
* `hcoh` must stay a hypothesis of the consumer. It is the only thing that propagates the
  pigeonholed value DOWN from level `m` to level `n`, and without it the statement is FALSE: take
  `s_n = 0` for even `n` and `1` for odd `n`, each its own bounded witness; a global `t` would lie in
  `⋂ₙ Iⁿ = 0` and satisfy `t − 1 ∈ ⋂ₙ Iⁿ = 0`.

## A NON-PUBLIC `import` REACHES THEOREM PROOF BODIES BUT NOT `def` BODIES

(2026-07-31, cost one build cycle.) `X0.lean` records that its
`import Fermat.FLT.ModularCurve.EllipticScheme` is non-public **on purpose** — a
`public import` propagates the reserved token `over` through the whole cone and
silently truncates a structure with a field of that name — and that "everything from
`EllipticScheme` stays inside its proof body, which is exactly where the non-public
import does reach". That clause is true and INCOMPLETE.

Every file here opens with `@[expose] public section`, which exposes **`def` bodies**.
So a `def` whose body names a privately-imported constant fails with a bare
`Unknown identifier` — the *same* message a missing declaration gives and the same one
a signature gives, so it reads as "the private import does not work at all" rather
than "it works, and this is the wrong kind of declaration". Measured in `X1.lean`:
`#check @Fermat.OnAffineWeierstrass` fine (a command); the name in a theorem SIGNATURE
fails (expected); the name in a `noncomputable def` body fails (not documented
anywhere).

So before planning a proof around a privately-imported API, ask whether you need it in
a `def` — an `Equiv`, a bundled hom, anything with computational content — or only in
a `theorem`. If a `def`, the private import buys nothing. Three ways out, best first:
**restate the few lemmas locally, specialised** (specialising a functor-of-points
dictionary to `C = K` deleted half of them, `OnAffineWeierstrass` giving way to
mathlib's own `WeierstrassCurve.Affine.Equation`); **add a re-export in the module that
can see it**, written in that module's vocabulary, which is the pattern `X0.lean`
already uses for `exists_weierstrassModel_geomFibreAddEquiv_of_ellipticScheme`; or make
the import public, which for `EllipticScheme` is known-bad.

## THE QUEUE AUDIT CHECKS THE RELEASE; THE FRONTIER IS `merger`. AUDIT AGAINST `merger`.

(2026-07-31, `flt-lean-363`, measured: **three targets out of three** in one dispatch were
already proven.)

The fifth invisibility class above prescribes the right check —
`git show merger:<file> | grep -n <name>` — but states it as advice to the *worker*. The
dispatch side does not run it. A task dispatched this day named
`formalImmersion_of_cuspFormalImmersionCert`, `exists_isCusp_ne_neronSpAut_of_atkinLehnerPin`
and `redX_base_ne_of_isCusp`; all three are `sorry` on `main` and all three are **full `by`
proofs on `merger`**, which was 217 commits ahead. The audit that let them through was correct
about `main` and therefore useless: `main` is the frontier as of the last release, and 217
commits of proofs sit between it and reality.

Two things follow, and the second is the one that costs whole agents:

* **Audit queue entries against `merger`, not against the release.** One `git show` per
  candidate. It is the same command the doctrine already gives workers; run it where the task
  is written, not where it is received.
* **A leaf can be closed on `merger` *under a changed signature*.** All three above were not
  merely proven but restated — `q ≠ N` became `¬ q ∣ N`;
  `exists_isCusp_ne_neronSpAut_of_atkinLehnerPin` grew a generic-fibre pin `(wYQ, hwYQ, hpin)`
  because the integral moduli descent turned out to be impossible. So a worker who "finds it
  already proven" must compare the STATEMENT too before reporting the task obsolete; and a
  worker who proves the `main` version of such a leaf has written something that will not
  even elaborate after the merge.

Not a defect in the loop — the audit does what it says. It is the wrong reference tree.

**Corollary, same day and same shape: a leaf's SUPPORTING lemma can be WEAKENED on `merger`,
which silently invalidates a proof that is green on `main`.** `exists_diffCharScalar`
(`DifferentialCharacter.lean`) concludes an identity at every `P ≠ 0` off `ker φ` on `main`;
on `merger` it was proven, and the price was two new hypotheses in the conclusion,
`B.eval (x P) ≠ 0 → E.eval (x P) ≠ 0 →`. A three-line proof of
`exists_isCotangentScalar` over the `main` form compiles today and is *unprovable* over the
`merger` form. **So before building on a lemma, diff its statement against `merger` — not just
check that it exists.** A green build against a superseded hypothesis set is the "two
individually-correct repairs, fatal together" failure with a shorter fuse.

## "X is one HOIST away" — import direction is necessary and nowhere near sufficient

(2026-07-31.) Three leaves in `ModularCurve/X0.lean` — the
`mem_isolatedJInvariants_of_stable_*` group, Mazur's Theorem 1 — each carried the
sentence *"this leaf is therefore one hoist away from three lines; a successor should
hoist rather than reprove"*, pointing at proven counterparts in
`FreyCurve/MazurTorsion.lean`. The claim had been re-checked once, by exactly the check
the docstring names: **is the import direction still what I think it is?** It was. The
advice was still wrong, and had been sending successors at an impossible operation.

Three things must ALL be true for a hoist to be the repair, and only the first is about
imports:

1. **Import direction** — the standard check, and the only one anybody ran.
2. **DECLARATION ORDER IN THE DESTINATION FILE.** Every declaration the hoisted block
   consumes must end up above it. Here `IsJMapOn` (24058), `exists_jMap` (27456),
   `HasRankZeroJacobian` (30385) and `card_le_of_rankZeroJacobian` (63677) all sit
   *below* the three leaves at 18592–18684 — so the hoist's real precondition is
   relocating the leaves and their whole cluster past line 63677, in a file of 81 530
   lines. Lean's linear order is a dependency edge exactly as much as an import is.
3. **THE LEAF COUNT ON THE OTHER SIDE.** "PROVEN there" almost never means sorry-free.
   The two namespaces to be hoisted carry **18** open leaves between them; the trade is
   3 leaves here for 19 there. A hoist that raises the frontier may still be right —
   it is disclosure, not regression — but "hoist and these close" is a different claim
   and it was the one being made.

And **re-measure the SIZE, every time**: the section was recorded as `3 500` lines when
the note was written and is `13 000` now. These sections grow while the note does not.
`grep -n 'namespace X' file | ...` is two seconds.

The measurement that made this actionable rather than merely negative is worth copying:
take every top-level declaration name in the block to be moved, strip comments, tokenise
with `isalnum` (**not** a unicode identifier regex — `À-￿` swallows `⟨⟩←▸`, see
[[lean-identifier-regex-swallows-brackets]]), and grep the whole file for those names
*outside* the block. Here 132 declarations produced exactly **four** external hits, one
of which was the single declaration that cannot travel with the rest. That turns
"integrator-level refactor, two files, concurrent owners" into "move 131 declarations,
leave one behind" — a claim someone can act on.

Corollary, same finding: **all six leaf names those three docstrings cited as "the open
residue" had since been PROVEN.** A docstring leaf list is a snapshot with no
maintainer. Cite the section, never the leaves; and if you do cite leaves, stamp the
commit — as with every other frontier number in this file, regenerate rather than quote.

## AN EXISTENCE-ONLY UNIVERSALITY CLAUSE PINS ITS RING IN **NO** DIRECTION — AND THE AUDIT THAT FOUND THAT ONCE DOES NOT TRANSFER ITSELF

(2026-07-31, `Patching.lean`.) `IsWeaklyUniversalDeformation` is deliberately the
existence half only, and a 2026-07-28 audit refuted `exists_auxDeformationDiamondControl`
with the family `Runiv₀[[y_1, …, y_m]]`: a classifying map out of `Runiv₀` precomposed with
`constantCoeff` classifies just as well, so weak universality admits arbitrarily large
`Runiv` and any conclusion bounding it from ABOVE is false. That audit was written, the
repair (`hgen`, trace generation) was threaded through eight declarations, and everyone
moved on.

**`AuxDeformationDatum.IsWeaklyUniversal` is the SAME clause on a DIFFERENT ring**, and its
docstring says so in as many words — and both ring leaves take that datum as a hypothesis
and conclude something bounding `𝒟Q.R` from above. The identical family refutes both.
Nobody looked, because the leaf already carried a FALSITY AUDIT (about the `𝒪`-algebra
structure, repaired by `hcohen`) and a leaf that has been audited reads as a leaf that has
been checked.

So: **when an audit refutes a leaf because some bundled object is unpinned, grep for every
OTHER object in the same file with the same defining shape** — here, one `grep -n 'Only the
EXISTENCE half is asked'` would have found it. An audit is scoped to the object it names,
never to the pattern.

Corollary on where such a defect must be repaired: the conclusion is a statement about the
object, so **the leaf must PRODUCE the object, not receive it** (this file's own principle,
"a datum handed across a seam can only be constrained by what already saw it"). Three
cheaper repairs were checked and all fail — a hypothesis naming the received datum is
UNDISCHARGEABLE when the consumer chooses it internally; the universally-quantified form
(`∀ 𝒟, weakly universal → generated`) is refuted by the same witness and makes the package
vacuous; and a new leaf producing a "weakly universal AND trace-generated" datum is FALSE
as stated, because trace generation over `ℤ_[p]` forces the residue field to be the trace
field and nothing pins `k` to it (`ρbar` absolutely irreducible over `𝔽_p`, `k = 𝔽_{p²}`).

## MOVING A DATUM FROM HYPOTHESIS TO CONCLUSION CAN ORPHAN THE SUBTREE THAT PRODUCED IT — PASS THE **EXISTENTIAL**, NOT THE WITNESS

(2026-07-31, same repair.) The obvious way to make a leaf produce its datum is to give it
the raw nonemptiness witness `(𝒟₀ : AuxDeformationDatum …)` and delete the consumer's call
to the theorem that used to build the weakly universal one. That call was the ONLY thing
keeping `exists_isWeaklyUniversal_auxDeformationDatum` — and the whole Schlessinger clause
subtree beneath it — in the root's used-constant cone, and **a sorried body contributes no
dependency edges**, so the leaf's intended proof does not hold it there. The change would
have silently made a large proven subtree free-floating.

The fix costs one character of design: hand the leaf the EXISTENTIAL

    hwu : ∃ 𝒟 : AuxDeformationDatum … , 𝒟.IsWeaklyUniversal

which the consumer discharges with the same call it already made. The leaf still chooses
its own datum, and the producer stays in the cone. **Any time a repair deletes a call from
a proven proof, ask what else that call was holding up.**

## AN "AXIS SEARCHED" VERDICT IS ONLY AS GOOD AS THE LEVEL IT WAS TAKEN AT

(2026-07-31. Two leaves in `ModularCurve/X0.lean` closed the same afternoon, each
against an audit that had explicitly ruled its route out, and each audit's
FACTUAL clauses were true.)

Docstrings in this development carry `AXES SEARCHED` / `WHY THIS IS NOT A
COROLLARY OF X` verdicts, and they are load-bearing: the next owner reads them
and does not re-open what they close. Both failures below were failures of
INFERENCE from a correct observation, and both are cheap to detect.

**Pattern 1 — absence of a lemma about the OBJECT is not absence of the
IDENTITY.** `trace_heckeOpSq_x0OneSixtyNine` recorded that the banked-charpoly
route was closed off: "Mathlib at this pin has `Matrix.trace_eq_sum_roots_charpoly`
(first power sum only) with no counterpart for the second, so the charpoly route
would cost a triangularisation argument." Both clauses TRUE. But Newton's second
identity `Tr(M²) = (Tr M)² − 2e₂` does not need eigenvalues at all:
`Matrix.charpoly_coeff_eq_sum_minors` (which IS in the pin) gives `coeff (n−2)`
as the sum of the `2×2` principal minors, that sum is `∑_{i<j}(MᵢᵢMⱼⱼ − MᵢⱼMⱼᵢ)`,
and doubling it is `(Tr M)² − Tr(M²)` because the summand is symmetric with
vanishing diagonal. Any commutative ring, no splitting, ~120 lines.

The audit had searched for a lemma about the ROOTS and concluded from its
absence that the identity was unreachable. **Before believing "mathlib lacks
this", ask which OTHER presentation of the same quantity the pin does have** —
coefficients vs roots, minors vs eigenvalues, a recursion vs a closed form.

**Pattern 2 — "not a corollary of X" is a claim about X, and X may be an
ASSEMBLY.** `sumSq_isWeilEigenvalues_x0` said, correctly, that `Σ αᵢ²` is not a
function of `Σ αᵢ` and `∏(1 − αᵢ)` once `g ≥ 2`, so it could not be a corollary
of `isWeilEigenvalues_x0_eichlerShimura`. True — and that theorem is itself a
three-line assembly over `isEichlerShimuraTransform_x0`, which supplies the full
PAIRING, and a pairing determines EVERY power sum. The `(sum, product)` form was
a lossy read of a datum still sitting in the file one level down.

**So when a verdict names a theorem as the thing that is insufficient, open that
theorem's PROOF.** If it is `by exact ⟨h.foo, h.bar⟩` over some richer leaf, the
verdict is about the projection, not about what is available. In a development
that decomposes aggressively, yesterday's atomic leaf is today's assembly, and
the docstring recording the old cut does not update itself.

Both repairs cost nothing downstream: the closed leaves rest on leaves that
already existed (`finrank_cuspForm_of_x0HeckeCharpolyTable`,
`charpoly_toMatrix_heckeOp_of_x0HeckeCharpolyTable`,
`isEichlerShimuraTransform_x0`), so the frontier went down by three with zero
new nodes. **A leaf that closes by re-reading an audit is the cheapest kind of
progress there is; budget a pass over the audit before budgeting a proof.**

## A LEAF CAN BE CLOSED BY MOVING CODE — the declaration-order leaf class

(2026-07-31, `flt-lean-2`, on `flat_toImage_of_isAdditiveOn` in `X0.lean`.)

A leaf can be **already proven, in the same file, below itself**. Lean elaborates top
to bottom, so the general theorem is unusable at the leaf's position and the leaf gets
`sorry`d, honestly, with a docstring saying so — and then it sits there, because every
prover who reads it correctly concludes there is no mathematics to do and moves on.
This one survived three days and an audit that diagnosed it exactly and declined to act.

**The repair is a relocation, and moving code DOWN is the safe direction**: it cannot
break the moved code's own dependencies, so the ONLY check is whether anything between
the old and the new position consumes the block. That check is cheap, and it is the
whole risk assessment.

Three things this cost, worth knowing in advance:

* **A docstring's call-site list goes stale the moment the block moves.** The audit here
  named "exactly one CODE call site, at line ~66357" — written when the block lived
  1000 lines earlier, and by the time it was read the line number meant nothing and the
  count was wrong (there were three, two of them for a different declaration). Re-derive
  the list against the current file; do not inherit it. A naive `grep` over-reports
  wildly, because in this project most occurrences of a name are prose in docstrings.
* **`refine ⟨?_, h⟩` fails when `h`'s type mentions the hole.** Restructuring the
  consumer to name the object it used to produce as a `refine` hole is the usual shape
  of this repair; use `refine ⟨?_, ?_⟩` with bullets so the first goal assigns the
  metavariable before the second is checked.
* **Structure literals are indentation-sensitive in a way the error does not name.**
  Re-indenting a `{ field := … }` block by one column produces
  `unexpected identifier; expected '}'` plus a bogus "fields missing" list.

**And the payoff is usually bigger than the one leaf.** Moving this block below the
morphism-level group machinery (`addPairHom`, `sqMap`, `pairSquareMap`,
`pairSquareMap_addPair`) put that machinery ABOVE two sibling leaves that had been
stated in terms of it and could not use it. One of the two was proven the same day
purely because it became expressible. So when choosing WHICH side to move, prefer the
move that leaves the remaining leaves with more machinery above them.

## `IsSchemeTheoreticallyDominant` is the pin's tool for "the image is a subgroup scheme"

(2026-07-31, same task — this is the concrete follow-up to the standing note that
schematic density is in the pin.)

The classical argument for "the scheme-theoretic image of a homomorphism is a subgroup
scheme" goes through "`B ×_ℚ B` is the image of `J ×_ℚ J`, because the source is reduced
and the base is a field". **Reducedness is a detour.** What the argument actually needs
is `AlgebraicGeometry.IsSchemeTheoreticallyDominant` (`f.ker = ⊥`), and the pin carries
everything:

* `IsSchemeTheoreticallyDominant.of_isPullback` — stable under **flat** base change;
* an instance for composition;
* `Scheme.Hom.ker_comp` + `IdealSheafData.map_bot` give **cancellation**:
  `p.ker = ⊥ → (p ≫ h).ker = h.ker`. Since `IsClosedImmersion.lift` asks exactly for
  `ι.ker ≤ (·).ker`, that turns "the composite lands in the subscheme" into "the
  morphism lands in the subscheme". This is the whole mechanism;
* **over `Spec` of a field, flatness is free** — `[Subsingleton Y] [IsIntegral Y] → Flat f`
  — so every base change along a structure morphism to `SpecQ` qualifies with no work.

`q ×_S q` is dominant when `q` is: cut it as `(q × 𝟙) ≫ (𝟙 × q)`, each a base change of
`q` along a projection, pasted with `IsPullback.of_bot`.

**Two things to check BEFORE writing any of it.** `X0.lean` already contained
`isSchemeTheoreticallyDominant_toImage` and a `sqCover` version of the product step —
proven for an unrelated leaf **58 000 lines away**, under names that share no keyword
with the leaf being worked on. Grep for the CONCEPT (`IsSchemeTheoreticallyDominant`,
`ker_eq_bot`, `of_isPullback`), not for the leaf's vocabulary. And develop in a scratch
module that `public import`s the target's built olean: the round trip on this file is
~25 minutes for a build and ~40 seconds for the scratch, and the leaf above went from
first draft to green in four scratch iterations.

Known GAP in the pin, found the same day: **`Smooth f → GeometricallyReduced f` does not
exist**, in any form, at any level. Mathlib DOES have Cartier's theorem
(`AlgebraicGeometry.smooth_of_grpObj`: a locally-finite-type geometrically reduced group
scheme over a field is smooth), so the char-0 smoothness of a group scheme is reachable
in principle — but its `GeometricallyReduced` hypothesis has to be built by hand, and for
an abelian scheme the obvious source is its own `smooth` field, which does not deliver.

## A FALSITY AUDIT THAT PRESCRIBES A CUT MUST BE *PERFORMED*, AND THE CHEAP WAY IS "SORRY THE LOWEST TRUE CONSUMER, DELETE THE FALSE CONE"

(2026-07-31, `Threeadic.lean`.) `eq_one_of_smul_eq_mul_localInertia_connected_threeTorsion`
was refuted on 2026-07-29, re-verified independently on 2026-07-30, and the audit — three
screens of it, with the PARI/GP transcript and a measurement of the `39`-declaration upward
cone — ended *"it is not a decision a single prover agent should take by itself, which is why
it is written down here instead of performed."* So it was not performed, and a FALSE `sorry`
with `39` live consumers stayed in the tree while three agents in a row read the audit,
agreed with it, and left.

**Under the loop there is nobody for "not a single agent's decision" to defer to.** An audit
that names its own repair and does not perform it is a task that will never be dispatched,
because every frontier scan sees a leaf with a careful docstring and no defect.

The reason it kept not being done is that the audit priced the repair as *restate the leaf
correctly, then rewire the consumers* — for this cone, four constructor sites and a new
statement nobody had written. **That price is usually wrong.** The cheap realisation:

1. walk UP the call graph from the false leaf to the LOWEST declaration whose own statement
   is TRUE — typically the first one that carries the real object (`hρ : IsHardlyRamified`,
   a pinned `fG`) instead of quantifying over an arbitrary one;
2. replace THAT body with `sorry`, and put the audit, the witness and the true route in its
   docstring;
3. delete everything below it that the usage graph says now has no consumer.

Here that was `exists_connectedEtale_line_of_hopf_package`: `35` declarations and `6373`
lines left the file, two `sorry`s became one, **and nothing above the cut changed at all** —
no consumer was rewired, because every consumer already reached the finite-flat content
through that one theorem. The whole edit is mechanical once the cut point is chosen.

Two details that make step 3 safe, and both are one script:

* compute the dead set by FIXPOINT on the in-file usage graph (strip comments first, attribute
  each token to the enclosing declaration, iterate "no surviving consumer ⇒ dead"), then
  `grep` every dead name across `Fermat/` — cross-file hits are usually prose citations in
  docstrings, which are harmless but must be named in the commit;
* check the range for `instance`/`@[simp]`/`def`/`section` before deleting. Those are the
  elaboration-invisible dependency classes; a range of plain `theorem`s is safe to cut whole.

And name the cut point by asking *is this statement true*, not *is it convenient*. The
boundary in this cone was exactly the boundary between "quantifies over an arbitrary Hopf
order" (false: an arbitrary connected socle can be `3`-dimensional and carry a unipotent) and
"the Hopf order is the flat model of a rank-`2` representation with a residually trivial
quotient" (true: the residual socle is `2`-dimensional for free, which is the sharp bound).

## A LEAF QUANTIFIED OVER A BUNDLED DATUM MUST SURVIVE EVERY *RELABELLING* THAT DATUM ADMITS

(2026-07-31, `range_base_atkinLehner_cusp` in `ModularCurve/X0.lean` — refuted the day
after it was cut, by two instances of ITSELF.)

`∀ C : SomeStructure, P C` is only as strong as the structure's fields make it. This file
already records the PINCH test for that shape — perturb the *object* the structure
describes and see which clauses survive. There is a second, cheaper and much more easily
missed perturbation: **leave the object alone and permute the INDEXING.** A structure whose
fields are a family `κ : ι → (something about X)` plus constraints that are all invariant
under reindexing admits `C ∘ σ` for every `σ` in a group of permutations of `ι`, and a
conclusion that mentions a *specific* map `ι → ι` is then provable only if that map is
central for the whole group.

`IsX0Compactification.CuspLocus` indexes the cusps of `X_0(N)` by `N.divisors` and pins the
labelling only through `degree d = φ(gcd(d, N/d))`. So `C ∘ σ` is again a `CuspLocus` for
every `σ` preserving that function — `cover` because `σ` is a bijection, `disj` because it
is injective, `ratPoint` by handing back `σ.symm d`, `degree` by hypothesis. The leaf
asserted `w (cusp_d) = cusp_{N/d}`, i.e. that `w`'s cusp permutation is `ι : d ↦ N/d` in
EVERY labelling — which forces every admissible `σ` to commute with `ι`. At `N = 4` the
three values of `φ(gcd(d, 4/d))` are all `1`, so every permutation of `{1, 2, 4}` is
admissible, and the leaf at `C` (`d = 2`) with the leaf at `C ∘ (1 2)` (`d = 1`) gives
`c_2 = c_4` against `C.disj`. **Both are instances of the leaf, so the refutation assumes
nothing about `w` at all** — which is the cheapest possible shape of refutation and the one
to look for first on a `∀ datum` leaf.

**Why it survived the audit it already had.** The docstring carried a paragraph headed
*"THE STATEMENT IS ROBUST TO THE INDEXING CONVENTION"*, correctly observing that `CuspLocus`
fixes no convention and that `φ(gcd(d, N/d))` is symmetric under `d ↦ N/d`. Every clause was
true. The inference was not: it varied the labelling **only along the involution the leaf
was trying to establish**, which is exactly the relabelling that cannot detect the problem.
That is the same failure as *A COUNTEREXAMPLE IS ONLY AS STRONG AS THE HYPOTHESIS LIST* below
and *vary the parameter you did not think of as a parameter*, arriving through a symmetry
argument — and a symmetry argument reads as more conclusive than a witness search, so it is
worse.

**The mechanical test, and it costs one careful read of the structure.** List the fields.
Cross off the ones that are pointwise in the index (`K`, `κ`, `comm`, the instances) and the
ones invariant under bijections (`cover`, `disj`, `ratPoint`). What remains — here just
`degree` — is the whole of what pins the labelling. Then compute the group it leaves: the
permutations preserving that invariant. If the conclusion names a map on the index set,
check it is central in that group. **Do this before writing the leaf**, and record the group
in the docstring; it is the datum's real automorphism group and every later `∀ C` statement
in the file has to respect it.

**The repair is usually a hypothesis, not a restatement.** Adding "the fibre of the pinning
invariant through `d` is exactly `{d, N/d}`" (`hrigid`) makes every admissible `σ` restrict
to that pair, where it is central for trivial reasons. It is sharp — the refutation runs at
every `d` where it fails — it is DECIDABLE, and the sole consumer discharged it with
`decide`, so no signature above the leaf moved. The alternative repair, existentially
quantifying the datum (`∃ C, ∀ d, …`), is the honest general statement and is strictly
weaker; prefer the hypothesis while every consumer satisfies it, and say in the docstring
which levels would need the existential form. Adding a hypothesis is a restatement, so the
old faithfulness audit is VOID — but in this direction re-running it is short, since a
strengthened hypothesis can only shrink the class of counterexamples.

## A COUNTEREXAMPLE IS ONLY AS STRONG AS THE HYPOTHESIS LIST IT WAS TESTED AGAINST

(2026-07-31, flt-lean-110.) `exists_hilbertFixing_rootsOfUnity_discrim_isSquare`
carried a FALSITY AUDIT that three independent passes had confirmed — an explicit
elliptic curve, an exhaustive matrix enumeration, and a by-hand derivation, all
agreeing. I re-verified all three a fourth time (Python enumeration, PARI/GP on the
curve) and they are right. The leaf IS false as stated.

The audits were nevertheless leading the repair in the wrong direction, because
none of them asked **which hypotheses the witness spends that the leaf does not
state but its CONSUMERS do.** Here the witness forces `det ρ̄(Γ F) = {1}`, hence
`Γ F ⊆ ker χ̄_ℓ`, hence `F ⊇ ℚ(ζ_ℓ)` — so **`F` is totally imaginary**. And
`NumberField.IsTotallyReal F` is exactly what the eventual consumer carries, and is
already threaded as an instance binder through 2 800 lines of the same file.

So the refutation is of *the leaf as stated*; the leaf-plus-`htr` is untouched by
it. The two repairs that follow differ by an order of magnitude — threading one
plain hypothesis through eight signatures, discharged at the top, versus a
coefficient-field enlargement `k ↝ k(√d)` rethreaded through a definition whose
Selmer clause would have to move to `k'` — and the audit had recorded only the
expensive one as "forced".

The rule: **before accepting that a leaf needs a structural repair, diff its
hypothesis list against its consumers', and check the witness against the
difference.** A leaf is routinely stated more generally than any call site needs,
and a counterexample living in the gap refutes only the generality. The cheap
repair — push the consumer's hypothesis down to the leaf — is invisible unless
that diff is taken, and it is a move this development has already made
successfully at least once in the same file.

Corollary, for whoever writes the audit: **say which hypotheses your witness
satisfies, not merely that it satisfies "every hypothesis".** All three passes
here truthfully verified every clause the leaf states, and that is precisely why
the gap survived three reviews — the check they each performed cannot see it.

## A LEAF'S OWN "WHAT IT COSTS" IS A HYPOTHESIS — unfold the DEFINITION first

(2026-07-31, flt-lean-110.) `exists_finset_isUnramifiedAt_hilbert_of_notMem` carried a
docstring saying it costs the CONVERSE of `MinkowskiUnramified.lean`'s
`isUnramifiedAt_of_inertia_le_fixingSubgroup` ("`w` unramified in `L/F` ⟹ `I_w` fixes
`L` pointwise"), that the converse is absent from the pin, and that it is SHARED with
`finite_hilbertInertiaOutsideSubgroups` — so "the two leaves are natural companions and
are best given to ONE owner."

Every factual clause was true. The conclusion was wrong twice over. The converse is
expensive (it needs local–global compatibility of ramification indices, which this tree
does not have) and **it is not needed at all.** `localInertiaGroup v` is DEFINED as the
inertia subgroup of the maximal ideal of `IntegralClosure 𝒪ᵥ Kᵥᵃˡᵍ` — "σx − x ∈ 𝔪 for
every integral x" — so "inertia fixes `α`" is checkable DIRECTLY, with no discriminant,
no ramification index and no dictionary: `α` and `σα` are congruent roots of
`minpoly ℤ α` in a local domain, and Hensel-free simple-root separation forces them
equal at every place off the finitely many dividing `(minpoly ℤ (P'(α))).coeff 0`. The
identical retraction had been recorded at the `ℚ` level three days earlier on the twin
leaf in `Modularity/Patching.lean`, and simply was not transferred.

Two rules, the second the one that costs releases:

- **Before buying a dictionary lemma a docstring names, unfold the definition of the
  object it is about.** A "missing dictionary" is often a translation between two
  spellings that the proof never has to cross.
- **A leaf-PAIRING recommendation ("give these two to one owner, they share `X`") is a
  claim about `X`, and it dies with `X`.** Re-derive it; do not inherit it. Here the
  pairing would have chained an already-closable leaf to a genuinely hard one and hidden
  that the hard one stands alone.

Corollary for TWIN leaves generally: this development is full of `ℚ`-level/`F`-level
twins whose docstrings were written by copying. **A correction applied to one twin is
not applied to the other** — nothing propagates it — so when you touch a leaf whose
docstring names a twin, read the twin's CURRENT docstring, not the sentence your leaf
quotes from it.

## A "MISSING MACHINERY" AUDIT NAMES THEOREMS. GO READ THE THEOREMS.

(2026-07-31, `flt-lean-246`.) A mature leaf in this tree carries an inventory
paragraph — "what exists and is usable is X, Y, Z; what is missing is W". Those
paragraphs are written carefully and are usually right about what is ABSENT.
They are much less reliable about **how strong what is PRESENT is**, because the
author summarised the cited theorem in one clause instead of quoting it.

`exists_heightOneSpectrum_mul_span_eq_span_of_sup_eq_top` (Dirichlet for a
narrow ray class) had, in its own docstring and in its consumer's, the sentence
"`GaloisRepresentation/Chebotarev.lean` carries `infinite_setOf_isArithFrobAt`
…, so the DENSITY half does not have to be rebuilt". Read as prose that says
"some density material is available". The theorem's actual STATEMENT is **full
Chebotarev in ideal-theoretic existence form**: for every finite normal `L/F`
and every `τ ∈ Gal(L/F)`, infinitely many places of `F` are unramified in `L`
and carry `τ` as an arithmetic Frobenius — proven, in a file with no `sorry` in
it. Once that is read rather than summarised, the leaf becomes a fifteen-line
assembly over a citation that asks only for the ray class FIELD, with no
analysis in it at all. The same file also holds Weber's per-narrow-ray-class
counting theorem, which none of the three audits in that block mentions.

So the cheap check, before believing any inventory: `grep -n "theorem <name>"`
the cited file and **read the statement and the sorry status**, not the
docstring's clause about it. It costs one grep and it is the difference between
"needs a theory" and "needs fifteen lines".

**The check cuts BOTH ways, and the same agent got the other direction wrong an
hour later.** Two new modules (`NumberField/ArtinSymbol.lean`,
`NumberField/UnramifiedClassFieldExistence.lean`) had appeared on `main` with a
promising declaration list, and I wrote "the unramified existence theorem has
landed in the tree" into a docstring and a commit message on the strength of
that list. It has not: their two core statements
(`exists_hilbertClassField_artinIso`, `artinMap_toPrincipalIdeal`) are `sorry`.
A declaration list is not a proof status. Run `grep -n sorry` on the file and
attribute each hit to its enclosing declaration before writing "is in the tree"
anywhere — the phrase is read downstream as "usable today", and an inventory
that is wrong in this direction sends the next agent to import a leaf.

**The reusable cut this exposed, which applies wherever a leaf asks for a PRIME
with a prescribed splitting/class behaviour:** do not ask for the prime. Ask for
the finite normal extension and the Galois element that CUT OUT the condition,
and let in-tree Chebotarev produce the prime. That moves the whole analytic /
density half out of the citation and leaves the abelian existence theorem,
which is a different and much better-isolated obligation. Two things make the
resulting leaf safe rather than vacuous, and both must be checked: exclude the
places dividing the modulus explicitly (at `w ∣ 𝔣` the ray-class conclusion is
*unsatisfiable*, so a leaf without that clause is FALSE, not merely hard), and
note that Chebotarev itself forbids discharging the leaf by choosing an `L, τ`
whose Frobenius set is empty — the set is infinite for every `L, τ`, and
`Ideal.finite_factors` removes the finitely many divisors of the modulus.

## AN "IRREDUCIBLE" VERDICT SEARCHES FOR A PROOF. CHECK FIRST WHETHER A SIBLING LEAF ALREADY IS ONE.

(2026-07-31.) `birationalOver_affineLine_of_not_injective_aj` carried a dated,
twice-re-run, entirely correct irreducibility audit: Riemann–Roch for curves does
not exist in `Mathlib`, in `~/cs/FLT`, or in `Fermat/` — no `h⁰`, no genus, no
degree of a divisor, and the re-run on 2026-07-28 named the exact greps. Every
word of it was true, and the leaf was **one `exact` away from proven**.

The audit asked *how would I PROVE this*. What it never asked is *does this file
already STATE it*. Eleven hundred lines below, in the same file, sat
`birationalOver_affineLine_of_relPicEquiv_sectionIdeal` — "two distinct linearly
equivalent `K`-points force the fibre to be rational" — the same classical
theorem written in Picard language instead of Albanese language. The two leaves
were carrying **one** theorem twice, and the bridge between them was three lines
of `RelPicEquiv` algebra plus `IsJacobianOf.universal`.

Why the duplication is invisible to every check this file already prescribes:
the two statements share **no identifier**. One mentions `IsJacobianOf`, `aj`
and an `AbelianSchemeStruct`; the other mentions `RelPicEquiv`, `sectionIdeal`
and `curveBaseChangeProj`. A grep for either name finds nothing of the other,
`own.py` and `leafstat.py` both correctly report "unowned, still open", and the
frontier scan counts two leaves because there are two `sorry`s. Only the
DOCSTRINGS gave it away — both say "Riemann–Roch in degree 1" in prose.

So add this to a leaf's audit, before writing "IRREDUCIBLE":

**Grep the file's own docstrings for the NAME OF THE THEOREM you are about to
declare missing** — `RiemannRoch`, `Poincaré`, `Lüroth`, `autoduality` — not for
its identifiers. If another leaf's prose claims the same classical citation,
either one implies the other or the two should be merged; either way the second
`sorry` is not a second obligation. In this instance the payoff was −1 leaf, the
consolidated Riemann–Roch content in one statement, and a stale "IRREDUCIBLE"
retired.

Corollary, and it is the general shape: **a decomposition that lands in a
DIFFERENT vocabulary from an existing leaf will re-derive that leaf rather than
reuse it.** The Picard leaf was cut on 2026-07-28 and the Albanese one on
2026-07-27, one day apart, by owners who could not see each other. When you cut a
node, say in the docstring which classical theorem the pieces are, in words —
that sentence is the only thing that will match.

## AN AUDIT MARKED "RE-VERIFIED <yesterday>" CAN BE STALE ABOUT ITS OWN FILE

(2026-07-31.) `exists_nonconstant_toAbelianScheme_of_one_le_x0Genus`'s docstring in
`ModularCurve/X0.lean` carried a paragraph headed **RE-VERIFIED 2026-07-30**, whose
operative claim was that the modular route's first step "is still unstated — the only
dimension formula anywhere in the tree is `finrank_cuspForm_of_x0HeckeCharpolyTable`,
table-driven and declared below this leaf". The uniform bridge it wanted —
`finrank_cuspForm_eq_x0Genus`, `dim_ℂ S₂(Γ₀(N)) = x0Genus N` for **every** `N ≥ 1` —
had been stated **in the same file, on the same day**, three thousand lines further
down. The audit really was re-verified, against `85ee56a7`; the sibling leaf landed in
a later release a few hours after.

So the release window does not only invalidate OWNERSHIP records. It invalidates the
**absence claims inside docstrings**, and those are the more dangerous half, because a
docstring absence claim is read as a settled fact about the tree and carries a date
that makes it look fresh. **"RE-VERIFIED <date>" is evidence about a commit, not about
`main`** — and the same file is exactly where a rival leaf is most likely to appear,
since that is where the neighbouring work is being dispatched.

The check costs one `grep`: before believing any docstring clause of the form *"no such
theorem exists"*, *"the only one is X"*, or *"it is not in scope here"*, re-grep the
name and re-read the line numbers. Then **correct the docstring in place, next to the
stale claim rather than over it** — the reasoning that produced the claim is usually
still worth reading, and a leaf's audit history is how the next prover knows which axes
are exhausted.

Corollary, from the same leaf: when the correction lands, re-do the ARITHMETIC the stale
claim supported. Here the audit's conclusion — "a decomposition along the modular axis
produces two theory builds where there is now one leaf, which is why it has not been
taken" — was the whole reason the axis was declined, and with the dimension bridge
already stated it is off by one build.

## A RELOCATION PLAN MUST BE MEASURED AGAINST `merger`, NOT `main` — THE BLOCK MOVES

(2026-07-31, third consecutive decline of the same relocation.) The section above
says an audit's *absence claims* go stale in the release window. This is the same
mechanism doing something worse to a *plan*: **every coordinate in a relocation
recipe — line ranges, line counts, which steps are still open, how many use sites
need requalifying — describes a tree that no longer exists by the time anyone acts
on it.** And unlike an absence claim, a plan looks actionable, so the next agent
re-derives it from `main` and gets a *different wrong answer* rather than noticing.

`exists_isWeilEigenvalues_galoisField` in `ModularCurve/X0.lean` is proven one
module downstream, so closing it is a move, not a proof. Three agents in two days
each measured that move against `main` and each recorded a different plan:

| measured | block | length | open steps inside | requalify |
|---|---|---|---|---|
| 2026-07-30 vs `85ee56a7` | `Interface.lean:?` | 761 lines | 3 | ~50 sites |
| 2026-07-31 vs `d451d20b` | `:54431–55801` | 1370 lines | 1 of 3 | ~50 sites |
| 2026-07-31 vs `merger` `d4966bac` | `:55244–56742` | 1499 lines | **1**, renamed | **8**, in 7 decls |

Every row was honest and correctly measured. The block doubled in size while
getting *closer* to done, because proving its steps ADDED lines. And the third
row is the only one you can act on: a branch cutting the move from `main` would
delete `exists_riemannRochGrowth_of_isProperSmoothCurve`'s proof — **re-opening a
leaf `merger` had already closed** — which is the "a branch that was right when
dispatched is wrong when it lands" rule, arriving through a *plan* instead of
through a diff.

Two things follow, and the second is the one that keeps being missed:

1. **Measure the source block on `merger`** (`git show merger:<path> > /tmp/x`),
   never on `main`, and stamp the sha into whatever you write down.
2. **The ~50-site figure was an unstripped whole-file `grep`.** The real count was
   8, in 7 named declarations. A relocation's cost is dominated by exactly this
   number, so an inflated one can kill a cheap move on its own — which is close to
   what happened here. Strip comments and attribute hits to enclosing declarations
   before quoting a use-site count, the same discipline the frontier scans use.

Corollary for the decline itself: **a decline recorded on ownership grounds has an
expiry date that nothing writes down**, so say in the docstring which job held the
lock, and re-check `~/.flt-loop/jobs` before inheriting it. Two of these three
declines were on ownership that had already lapsed.

## A RECORDED ROUTE IS A COST HYPOTHESIS, NOT A SPECIFICATION — and an `∃` licenses a cruder witness

(2026-07-31, measured on `exists_badPrimes_localInertiaGroup_le_of_isOpen_ray_class`.)
Docstrings in this development often carry a fully worked-out route. That route is
evidence the leaf is TRUE; it is not a statement of what must be formalized. When the
conclusion is `∃ T : Finset _, …` — or `∃` a bound, a modulus, a constant — **any
admissible witness discharges it, and the canonical invariant the route names is
usually the most expensive object that would work.**

That leaf's route prescribed a primitive element `α` of `L = fixedField N` and
`Δ := ∏_{β≠γ}(β−γ)` over the roots of `minpoly ℤ α`, with `T :=` the primes dividing
`Δ`. Two substitutions deleted most of the formal cost and no mathematics:

- **A `ℚ`-SPANNING SET beats a primitive element.** An automorphism fixing a spanning
  set of `L` fixes all of `L` by `Submodule.span_induction` — plain linearity, and
  `(⊤ : Submodule ℚ L).FG` supplies the set from `FiniteDimensional`. The primitive
  element theorem only makes that set a *singleton*, which the argument never needs,
  and it costs the `IntermediateField.lift` bookkeeping to move `ℚ⟮α⟯` from inside `L`
  up to an intermediate field of `ℚᵃˡᵍ`.
- **ANY DIVISOR beats the discriminant.** `x − β` is a nonzero algebraic integer for
  every root `β ≠ x` of **any** monic integral witness `g ∈ ℤ[X]` of `x` — *not*
  `minpoly`; any monic `g` with `g(x) = 0` works, because roots of a monic integer
  polynomial are again algebraic integers. Each such difference divides SOME nonzero
  rational integer, and the union of those integers' prime factors is a legitimate
  `T`. No Vieta, no `derivative`, no separability, no Bézout.

So the discipline is: **before formalizing a named classical invariant, ask which
property of it the proof actually uses.** If the answer is "it is nonzero and
everything bad divides it", build the crude divisor instead. Then state in the commit
which reading of the route you took and what would change your mind — here, a consumer
needing `T` to be *exactly* the ramified primes; none of the three named customers
(`finite_hilbertInertiaOutsideSubgroups`, `exists_finset_isUnramifiedAt_hilbert_of_notMem`,
`exists_finset_isUnramifiedAt_of_notMem`) does.

Corollary, general: **`minpoly` is rarely what you need** when a plain `IsIntegral`
witness will do — it drags in irreducibility and the `ℤ`-vs-`ℚ` integrally-closed
bridge for nothing.

## "That theorem HANDS BACK X" is a claim about its CONCLUSION, not about its proof

(2026-07-31.) `exists_span_three_eq_maximalIdeal_and_finrank_eq_of_residueField`'s
docstring said, twice and in bold, that the only thing its proof was missing was one
`public import`, and that `exists_unramified_extension_of_residueField` "delivers
`𝔪_S = 𝔪_R·S` verbatim". The import claim was exactly right and saved real time. The
delivery claim was **false**: that theorem's proof does establish `𝔪_S = 𝔪_R·S`
internally (it is a named `have` in its body, `hmaxS`) and its conclusion does **not**
export it. So the consumer, having added the promised import, still could not close the
leaf.

The recovery was cheap once the shape was clear — `S` is free of rank `n` over `R` and
its residue field already has degree `n`, so `n = e·f` forces `e = 1`, which is a
general lemma (`maximalIdeal_eq_map_of_finrank_residueField_eq`, proved from mathlib's
`IsLocalRing.finrank_quotient_map` plus rank–nullity, ~30 lines) — but it is work
nobody had budgeted, and the docstring said it was not needed.

So: **when a docstring tells you what an upstream theorem gives you, read that
theorem's STATEMENT before believing it.** A `have` inside a proof is invisible to
every consumer. And the repair when the fact really is only internal is a choice with
different costs, worth making deliberately:
* *export it* — add the clause to the upstream conclusion and fix its consumers. Two
  lines, but it rebuilds everything downstream of a widely-imported module;
* *re-derive it downstream* — a self-contained lemma in the file you already own. More
  Lean, zero extra rebuild, no merge conflict with other agents.
Prefer the second when the upstream module has consumers outside your cone.

## A LEAF'S OWN "WHAT REMAINS" NAMES ONE SUFFICIENT THEORY, NOT THE CHEAPEST ONE

(2026-07-31, flt-lean-107. Closed two direct leaves that had each been audited as atomic.)

`galoisConj_cmEndomorphism` in `X0.lean` — the `Γ_ℚ`-action on `End(E_ℚ̄)` is `Gal(K/ℚ)` —
carried a careful sketch routing it through *`End(E)` is commutative in characteristic `0`,
because quaternionic CM occurs only in characteristic `q > 0`*. True, deep, and nowhere in
this tree; that is why the node read as atomic CM theory for three days.

The proof needs no CM theory at all. `λ(φ)`, the scalar an isogeny acts on the invariant
differential by, is a ring map `End(E_ℚ̄) → ℚ̄` that is INJECTIVE in characteristic `0` and
Galois-equivariant — and injectivity into a *field* subsumes the commutativity the sketch
wanted, for free. Then `c := λ(φ)` satisfies `φ`'s own quadratic, `σ c` satisfies it too,
a quadratic has two roots, and injectivity turns each root into an identity of maps. About
sixty lines.

Three transferable rules, in order of how much they cost to skip:

* **A "MISSING MACHINERY" paragraph is evidence about the axis its author searched, and
  nothing more.** It is written *before* anyone tries, so it names the first sufficient
  route that came to mind. Ask what OTHER invariant separates the two cases — here, the
  question "what distinguishes `φ` from `1 − φ`?" has an answer that is a *number*, and any
  faithful numerical invariant would have done.
* **The sibling argument may already be written, in a file that IMPORTS yours.**
  `MazurTorsion.lean` (downstream of `X0.lean`) had `exists_sqrtNegOne_galSign`: the same
  three moves — `exists_isDiffChar`, `isDiffChar_galConj`, `eq_of_isDiffChar` — for
  `Ψ² = [−49]`. This extends `[[flt-missing-machinery-may-be-downstream]]`: the downstream
  sibling is not necessarily something to HOIST. Here it pointed at a third module
  (`EllipticCurve/DifferentialCharacter.lean`) that was upstream-compatible all along, and
  the whole fix was one `public import` in `X0.lean`. **"Not available here" often means
  "not imported here".** Check the import direction before concluding a theory is missing —
  and grep the whole tree, not your own module's cone.
* **A helper you need may exist only DOWNSTREAM, and then you copy it, deliberately.**
  `MazurTorsion.exists_rat_of_galois_fixed` (Galois descent for scalars, three lines under
  `set_option backward.isDefEq.respectTransparency false` because `IsGalois ℚ ℚ̄` does not
  synthesize at this pin) could not be used from upstream. Duplicating it under a different
  name with a docstring saying which copy should survive is right; renaming or moving the
  downstream one mid-task is a signature change with call sites you did not audit.

And the accounting note, because it is the shape that makes this worth writing down: the
leaf under attack was `exists_isogenyCurve_classNumberOne` in `MazurTorsion.lean`, and the
first working route closed it by opening a strictly stronger leaf UPSTREAM (net −1). Only
then did the upstream leaf turn out to be provable outright (net −2). **A cut that moves a
leaf upstream is worth banking even when you cannot close it** — it puts the residue where
the machinery lives, which is exactly where the next attempt can see it.

## A STALE SENTINEL TOKEN MEANS THE PROMPT IS OLD, NOT THAT YOU ARE DISCARDED

(2026-07-31, flt-lean-107. Caught one tool call before the sentinel would have been thrown
away with a finished, green, committed task inside it.)

`~/.flt-loop/jobs/<worktree>.json` rotates `token` on every retry. A RESUMED agent
(`"resume": true`) is handed its original transcript, so **the token in its prompt is the
token of the incarnation that was resumed, not the one the loop is now keyed on.** Mine said
`0194f666`; the job said `fceb21ba`. The prompt is explicit that a mismatched token makes the
loop ignore the whole file — so writing the prompt's token would have registered a completed
two-leaf proof as a death and dispatched retry 10 at work already committed.

`[[flt-loop-spawn-liveness-race]]` says to check your token against `jobs/<name>.json`, and it
reads a mismatch as "you are a discarded incarnation, yield without writing your sentinel".
That is one of TWO causes and, on a resumed job, the less likely one. Both must be
distinguished before you write anything, and neither the token nor `pgrep` alone does it —
`pgrep -af flt-job` lists every worker on the host, and a `pgrep` for your own token matches
your own command line, so it never returns zero.

**The decisive check is your own process ancestry**, because the loop names each worker
process after the token it issued it:

    P=$$; for i in 1 2 3; do P=$(ps -o ppid= -p $P | tr -d ' '); \
      ps -o args= -p $P | cut -c1-40; done      # -> "flt-job-<token>"

If that token equals `jobs/<name>.json`'s, **you are the live owner and the prompt is stale**:
write the sentinel with the JOB's token. Cross-check `session` in the same file against your
own session id — the loop records it, and it is a second independent confirmation. Only if the
ancestry names a DIFFERENT token than the job file are you the discarded twin, and then you
yield silently.

Corollary, and the reason this is worth a section: the failure is invisible from inside. A
sentinel written with a stale token is not rejected, not logged, and not retried — it is
ignored, and the loop's own timeout is what eventually notices. Everything downstream then
looks exactly like an agent that died mid-task, including to the next agent reading the
worktree, which will find the branch already carrying the proof and no record of who wrote it.

## YOUR TARGET MAY BE A FREE-FLOATING `sorry` A SEMANTIC MERGE MANUFACTURED — GREP FOR ITS CONSUMERS BEFORE PROVING IT

(2026-07-31, `flt-lean-113`, on `map_add_relPointWeierstrassEquiv` in `X1.lean`.) The
SEVENTH invisibility class above is about a merge that breaks a build. This is its
quiet twin: a merge that leaves the build **green** and the frontier **wrong**, by
orphaning a cut.

The mechanism needs two branches and no mistake by either author. Branch A proves leaf
`L` outright, by a route in another file. Branch B — cut against a copy of the file in
which `L` was still `sorry` — DECOMPOSES `L` into machinery plus a smaller leaf `L'`,
and re-points `L`'s body at them. Both merge cleanly, because they touch different
regions: B's machinery is an insertion, and only `L`'s body conflicts. The resolution
correctly keeps A's PROOF. Now `L'` and all of B's machinery sit in the file with
**nothing above them**, and `L'` is a `sorry` that no declaration in the tree reaches.

Every instrument agrees it is ordinary open work. It emits `declaration uses 'sorry'`,
so the warning set lists it; a source scan finds it; `own.py` correctly reports it
unowned; its docstring says in bold that it is "all that is left of `L`, which is
PROVEN over this leaf alone" — true when written, false after the merge. It drew a
dispatch, which is how this one was found.

**So the first grep of any prover task is not for the target's line number but for its
CONSUMERS**, comment-stripped, across `Fermat/`:

    grep -rn '<target>' Fermat/ | grep -v '<the file and line range it lives in>'

Zero hits outside its own subsection means it is free-floating, and CLAUDE.md forbids
that — so the task is not to prove it.

**Then compare the two routes before repairing, because restoring the consumption is
usually the WRONG repair.** Ask which leaf is left open by each, and whether that leaf
is SHARED. Here the surviving route rests on one leaf that the `Γ₀` consumer needs
anyway, so restoring B's cut would have left that leaf standing *and* added this one.
And check the direction of strength: an `∃`/`Nonempty` producer of *some* isomorphism
does **not** discharge a statement about *this* isomorphism — `e ∘ φ⁻¹` is then merely a
bijection fixing `0`, on which nothing is known — so the orphan was strictly HARDER than
the leaf beside it. A prover would have had to strengthen somebody else's open leaf to
close a declaration nothing consumed.

**The repair that pays: look for the WEAKER shadow the orphaned machinery already
proves, and find the consumer that only ever needed it.** B's dictionary here was a
sorry-free `Equiv`; only the group law was open. `MazurTorsion.lean`'s consumer took the
`≃+` and projected it to `e.toEquiv` on both lines that used it. Publishing the `Equiv`
alone (`nonempty_relPointEquiv_of_weierstrassModel_finiteField`) moved ~400 lines of
proven machinery into the root cone, deleted the free-floating `sorry`, and removed the
shared citation from that consumer's cone — one grep for `.toEquiv` at the call sites is
what found it. **When a bundled conclusion is `≃+`, `≃ₐ`, `≃ₗ`, or a structure, check
what its consumers actually project out.**

## A DECLARATION-ORDER LEAF CLOSES BY MOVING, NOT BY PROVING — READ THE DOCSTRING FIRST

(2026-07-31, `MazurTorsion.lean`, third instance in this file alone.) Some leaves contain
no mathematics at all. Every input is already PROVEN — one of them just happens to be
declared FURTHER DOWN THE SAME FILE, and Lean has no forward references, so the leaf was
cut in a combined form to dodge the ordering. `A₀-1`
(`exists_mem_localInertiaGroup_cyclotomicCharacterModL_eq`) closed this way on 2026-07-28;
`A₀-3a-i-b` (`det_galoisRep_five_eq_one_of_mem_localInertiaGroup`) closed this way on
2026-07-31 over a 234-line hoist and **fourteen lines of vocabulary glue**, having been
cut the previous day as a "Silverman *AEC* III.8.3 and the Weil pairing" leaf.

**The tell is in the leaf's own docstring**, and this development writes it down every
time: *"is ALREADY PROVEN IN THIS FILE"*, *"declared FURTHER DOWN"*, *"which is the only
reason this leaf is stated in the combined form"*, *"a prover has two honest routes:
hoist …"*. So the first action on any leaf is to read its docstring for that sentence,
and the second is `grep -n` the named declaration — if it exists below you, the leaf is
GLUE and the citation in its header is decoration.

**A hoist is safe exactly when four things hold, and all four are one grep each:**

1. *Namespace*: the source and destination sites are under the same `namespace`/`section`
   (`grep -n '^namespace \|^end \|^section '` and read off the enclosing block). An
   `open X in` binds only the next declaration and does not count.
2. *No backward dependency*: nothing the moved block cites is declared BETWEEN the two
   sites. Resolve each cited name — external (imported) is free, in-file must be above
   the destination.
3. *No stranded consumer*: every consumer of the moved names is BELOW the destination.
   `grep -n '<name>'` over the file; consumers far below are unaffected by definition.
4. *The move is verbatim*. Do it as a line-range relocation guarded by ASSERTIONS on the
   first and last line of the block and on the two lines straddling the insertion point —
   a 234-line block cannot be retyped safely, and `git diff --stat` reading
   `N insertions(+), N deletions(-)` with equal `N` is the receipt that nothing was
   dropped. (Anything else and you have hit class six from the other direction.)

**Do NOT restate the downstream half as a new leaf** to avoid the move. That manufactures
a duplicate cut — invisible to every sorry scan, and it makes the frontier count go UP
while pretending to go down.

**And do not assume the rejection of one hoist rejects yours.** The same file records that
release 12 REJECTED hoisting `WeierstrassCurve.PotentiallyGoodModel` and deleted the file
that did it; that verdict is about a structure with a ~1500-line existence chain and says
nothing about a self-contained two-theorem block. Judge the block you actually have.

**A hoist verified by all four checks can still not COMPILE, and the reason is the next
section.** `det_galoisRep_five_eq_one_of_mem_localInertiaGroup` was hoisted correctly —
namespace clean, no backward dependency, no stranded consumer, block byte-identical — and
the fourteen lines of glue on top of it were red. The four checks are about the MOVE. They
say nothing about the glue, and only a build does.

## A `local instance` UPSTREAM is invisible DOWNSTREAM — even when its term is in your goal

(2026-07-31, `MazurTorsion.lean`, one build cycle.) `WeilPairing.det_galoisRep_eq_cyclotomic`
has `algebraMap ℤ_[p] (ZMod p) (…)` on its right-hand side. `rw` it into a downstream goal
and that term appears there, fully elaborated. Then write `algebraMap ℤ_[5] (ZMod 5)`
yourself — as `WeilPairing.lean` itself does two lines from the end of that very proof — and
you get:

    failed to synthesize instance of type class
      Algebra ℤ_[5] (ZMod 5)

for a class the goal is visibly displaying. The instance is
`noncomputable local instance instAlgebraPadicIntZModWeilPairing`
(`Fermat/FLT/EllipticCurve/WeilPairing.lean:115`). **`local` scopes the ATTRIBUTE, not the
declaration**: the constant is exported and travels inside any imported statement that
mentions it, but instance SEARCH cannot find it after the import. So the term is present and
unwritable at the same time, and a proof step that is legal in the defining file is illegal
one import away. Copying a working tactic block out of the upstream file is exactly how you
hit this.

Three fixes, cheapest first:

1. **Never write the class's `algebraMap`/operation yourself.** Here the instance is
   `RingHom.toAlgebra PadicInt.toZMod`, so `algebraMap ℤ_[5] (ZMod 5)` and `PadicInt.toZMod`
   are DEFEQ and `exact` converts silently: `exact (…).symm.trans h` closed it where a
   `rw [show algebraMap … = PadicInt.toZMod from rfl]` could not even elaborate.
2. `attribute [local instance] WeilPairing.instAlgebraPadicIntZModWeilPairing in` before your
   declaration — needed if you genuinely must MENTION the operation (e.g. to `rw` at it,
   which needs a syntactic match against the goal's copy, so re-declaring your own
   `local instance` with the same body is NOT equivalent and may fail to match).
3. Only if it is wanted repeatedly: promote it upstream to a real instance.

**The diagnostic tell, since the error message points at the wrong thing:** a "failed to
synthesize `C X Y`" for a class that OCCURS in the goal you are staring at means a local or
scoped instance upstream, not a missing one. `grep -n 'local instance\|scoped instance' <the
upstream file>` before hunting mathlib for something to import.

## A LEAF'S OWN "NOT PROVABLE FROM WHAT IS HERE" AUDIT CANNOT SEE DOWNSTREAM
(2026-07-31, `natCast_ne_zero_of_geomBasis` in `X0.lean`.) The leaf shipped with a
careful, correct audit naming two routes and pricing each: a rank (`deg [n] = n²`,
Mumford §6) or invariant differentials of an abelian scheme. Both were genuinely
absent, both were correctly priced as new subtrees, and the dispatch that followed
told its agent not to re-measure them. **Neither was needed.** The arithmetic
already existed, PROVEN the previous day, in `X1.lean` — a file that IMPORTS
`X0.lean` and therefore cannot be seen from inside it. The leaf closed in five
lines over a bridge (`exists_weierstrassModel_geomFibreAddEquiv_of_geomPoint`) that
`X0.lean` itself already proved.
This is the `Missing machinery may be DOWNSTREAM` memory, but with a sharper edge:
there, an agent's *inventory* missed a downstream proof. Here, the leaf's own
authored audit did — and an audit reads as settled fact in a way an inventory does
not, so it propagates into dispatch prompts as "this was measured, do not
re-measure". **An audit's ABSENCE claims are scoped to the import cone it was
written in. Before believing one, grep the whole tree for the mathematical content,
not the file's dependencies.** Hoisting the proof out to a small shared module
(here `Fermat/FLT/EllipticCurve/GeomTorsionBasis.lean`) costs nothing: the
downstream file inherits its own declarations back through the upstream file's
`public import`, under unchanged names, so no call site anywhere changes.
**Corollary, same leaf: a docstring conjecture backed by a BOUNDED search is a
hypothesis, and the bound is usually where the counterexample is.** `X1.lean`
recorded "the bare basis property probably implies `n • y = 0`" on the strength of
a sweep over `n ∈ {3, 4, 5}`. It is false, and the smallest counterexample is
`n = 6`: `G = ℤ/20`, `y = z = 1`, where `∃!` holds exactly on the `n`-torsion
`{0, 10}` while `6 • y = 6 ≠ 0`. Re-run such a search past its recorded bound
before relying on the conjecture — it took seconds and it decided the signature.
## A `sorry` is a PROMISE that the statement is provable

(2026-07-29, orchestrator error, caught only because an agent quoted the file's
own audit back at me.)

A build was red at a call site of `one_le_break`. To unblock a release I told the
merge worker to `sorry` its body. **The statement had already been refuted 700
lines above in the same file** — the audit gave the witness (the 2-dimensional
irreducible of `S₃ = Gal(L/ℚ₃)`, both breaks `1/2`, against a claimed `≥ 1`,
because in the Swan normalisation breaks are positive RATIONALS and `≥ 1` is
Hasse–Arf for a *character* only) and ended "That theorem has been WITHDRAWN".

`sorry`ing it manufactured a **false leaf with two live consumers**, which is
strictly worse than the build error it fixed: a false leaf can never be closed,
and everything above it is worthless. The repair was to DELETE the declaration
and fix its consumers, which is what the audit had already prescribed.

So, before writing `sorry` to unblock anything:

- **Read the file's FALSITY AUDIT sections.** They outrank any instruction,
  including one from the orchestrator. This file's own rules are not a substitute
  for what a module has already established about itself.
- `sorry` is honest only when you can VOUCH the statement is provable. The clean
  case, from the same release: a tower step whose instance argument the merge made
  unreachable — proven on `main` across 241 diffed lines, so the statement is
  vouched and the regression is environmental. That one was `sorry`d correctly,
  with the deleted lines quoted verbatim in the comment so the repair is
  *restore reachability → delete the `sorry` → paste them back*.
- If you cannot vouch for it, **delete the declaration and repair its consumers.**

**Corollary — one `declaration uses 'sorry'` warning can hide SEVERAL sorries.**
`exists_isSwanExponentAt` carries FIVE inner `have … := sorry` behind a single
warning (verified on `main`: lines 4790 `hterm`, 4798 `hsep`, 4801 `hin`, 4807,
4952). The warning set counts DECLARATIONS. Three separate agents reported that
count as "three", under names that do not exist. Strip comments, grep `sorry`
tokens, compare against the warning count; a mismatch is anonymous inner sorries
that no frontier scan will ever surface and nobody will ever be dispatched at.

## A RECUT RENAMES THE OPEN LEAF — and the release audit's existence test does NOT catch it

(2026-07-31, `flt-lean-360`.) A blocked leaf is often best handled by a RECUT: prove the
named target over a smaller, restated leaf. `exists_ratCube_jInvariant_heegnerPoint` ("`j(τ₀)`
is a cube in `ℚ`") became PROVEN over the new `exists_intCube_jInvariant_heegnerPoint`
("`j(τ₀) = n ∈ ℤ` is a cube in `ℤ`"), count unchanged 1 → 1. That is a legitimate and often
correct outcome — but it creates a phantom-dispatch shape none of the sections above covers.

**The old name survives, as a PROVEN theorem.** So every stale queue entry naming it passes
the release audit's "does this name still exist as a Lean declaration" filter (the check the
`flt-release-deletes-nonleaf-tasks` note describes), gets dispatched, and lands an agent on a
declaration with nothing to prove. The other phantom classes are all *absences* — a deleted
name, a declined merge, a stale worktree — and absence is what every existing check looks for.
A recut leaves a PRESENCE that is merely no longer open, which reads as healthy at every gate.

The filter that works is the compiler's, not the tree's: a queued leaf name is live only if it
is in the module's `declaration uses 'sorry'` warning set. Cross-check queue entries against
that set, not against `grep`. And an agent that recuts owes the new name to `queue` and to
`to_merger` explicitly — the loop cannot infer a rename from a warning-set delta, which shows
only that one name left the set and another entered it, with nothing linking the two.

Corollary for the recutting agent: **say "RECUT, count unchanged" in the commit subject and
body.** A warning-set delta of `−1 +1` is indistinguishable from one closure plus one unrelated
disclosure, and the honest reading is the one that has to be written down.

## A TARGET THAT IS NOT IN THE FILE: check the worktree pointer BEFORE concluding anything

(2026-07-31, `flt-lean-360`.) The task prompt named a leaf at
`BinaryQuadraticForm.lean:4806`. The file in the worktree was **2486 lines**, and a
`grep` for the declaration over all of `Fermat/` returned nothing. Every reading
that suggests itself at that point is wrong and expensive: "already proven and
removed", "the queue entry is stale", "the leaf was renamed", "cut on an unmerged
branch". The actual cause was that **the worktree had not been advanced**: `HEAD`
sat on a merger commit one release behind, `main` was 71 files and 92k lines
ahead, and a plain `git merge --ff-only main` produced the 5411-line file with the
target at exactly the promised line.

So the first three commands in any task, before reading the target at all:

    git log -1 --format=%H          # where am I
    git rev-parse main             # where should I be
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

The dispatch hook is supposed to have done this, and normally has. It is cheap to
confirm and catastrophic to skip — a stale worktree makes a live leaf look deleted
and a fixed upstream look broken, and both misreadings produce a confident,
completely wasted report. This is the same "merge `main` FIRST" rule the triage
section below states for hard errors, applied one step earlier: to the question of
whether the target exists.

Note also that `lake` is **not on `PATH`** in an agent's non-login shell —
`lake: command not found`, exit `127`, which looks like a broken toolchain.
`export PATH="$HOME/.elan/bin:$PATH"` first, in every shell that runs it.

And one shell trap that cost two builds here: `pkill -f "lake build <Module>"`
also matches the *new* shell you are starting in the same command, because the
harness passes the whole command line through `bash -c 'eval …'`. Both the old and
the new build died with exit `144`. Do not pattern-kill on a string that your own
command line contains.

## SEVENTH class: an OPEN leaf that is also DEAD — and "it was deleted" is a claim, not a fact

(2026-07-31, `flt-lean-190`.) Every counting rule above asks *is this leaf open?*
None asks *does anything consume it?* A leaf can be open, compile, emit its
`declaration uses 'sorry'` warning, pass the three-part ownership test, survive
`leafstat.py` — and still be **worth nothing to close**, because its only
consumer is itself consumerless. Closing it moves the frontier number and moves
the project not at all.

`X0.lean` carried exactly this. `exists_galoisConj_cmEndomorphism_eq_sub` was a
live sorry leaf whose sole consumer, `not_stable_of_cmEndomorphism`, had **zero**
uses anywhere in the tree — the CM route it served had been replaced days earlier
by a CM-blind certificate table.

**What made it invisible is the interesting part, and it is a new medium for an
old trap.** FOUR docstrings in that file stated that `not_stable_of_cmEndomorphism`
"became consumerless and was DELETED the same day" (2026-07-28). The write-up
landed; the deletion did not. Those four copies **cross-corroborate**: reading any
two looks like independent confirmation, when they are one author's single claim
written in four places. This is the commit-message trap one section up, in
docstring form — and worse, because docstrings are what the next agent reads to
orient.

So add to every bookkeeping cycle, and to every prover agent's first ten minutes:

- **Before working a leaf, establish REACHABILITY, not just openness.** Grep
  comment-stripped source for uses of the leaf's name *and* of each declaration
  that consumes it, transitively, until you hit something in the root cone. One
  `python3` pass over `Fermat/` costs seconds.
- **A docstring saying something WAS deleted is a hypothesis.** So is "PROVEN",
  "consumerless", "now obsolete", and "this leaf is no longer needed". Grep for
  the name. The compiler and a comment-stripped scan are the only witnesses.
- **Deleting the dead pair is a FULL result**, not a consolation prize: it removes
  a leaf that would otherwise keep drawing dispatches forever.

**And a dead consumer can be hiding a NARROWING.** Once the dead theorem was gone,
the surviving leaf `not_forall_galoisScalar_of_cmEndomorphism` had exactly one
call site, which instantiated it at `q = p`. It had been stated for an arbitrary
prime `q`, needing three regimes; narrowed to `q = p` only the ramified one
survives, dropping the Weil-pairing determinant argument — the hardest ingredient
— entirely. **A leaf stated wider than any live call site needs is common, and the
usual cause is a call site that has since died.** Check the width whenever you
delete a consumer.

## A leaf can be open for NO MATHEMATICAL REASON — measure the hoist instead of fearing it

(2026-07-31, `exists_jSection_algClosModel` in `X0.lean`.) That leaf's own audit had
established, correctly and a day earlier, that its mathematics was **already proven and
merely discarded**: `exists_jSectionOnAffine`'s internal `H` is stated at an arbitrary
base ring and its last line throws that generality away by instantiating at `R = ℚ`.
The leaf was open because every ingredient was declared **nine thousand lines below it**,
and a leaf needs no producer while a theorem does.

The audit then priced the two repairs — hoist the machinery up, or split the `j`-theory
into its own module — and both prices were guesses. Measured, they were not close:

* **The hoist was free.** The block is 2966 lines and jumps 178 declarations; a
  comment-stripped token scan says it uses **none** of them, and its only outside input
  is declared near the top of the file. `flt-hoistcheck.py` (added with this note) is
  that scan: `./flt-hoistcheck.py <file> --block A B --to L`, two seconds, both
  directions. It also lists what it cannot see — **anonymous `instance :` declarations**
  in the jumped region, and any `namespace`/`section` the move would carry the block
  into or out of.
* **The module split was the expensive one**, which is the opposite of how it reads.
  The `j`-theory consumes `Gamma0Datum`, `RelPoint` and `AbelianSchemeStruct` from the
  first fifteen thousand lines of the same file, so extracting it means splitting
  `X0.lean` into THREE modules, not two — and a three-way split of a file with a dozen
  concurrent editors is far more merge-hostile than an in-file move.

So: **when a leaf's docstring says "this is blocked by declaration order", run the scan
before believing either cost estimate.** The general rule the two directions share — a
block may be relocated iff it uses nothing declared in the region it jumps — is cheap to
check and almost never checked.

Two riders learned in the same repair:

* **Prefer moving the MACHINERY to moving the CONSUMERS.** The consumer cluster here
  fanned out into Mazur-torsion certificates through `y0HasNoRationalPoint_of_not_stableCyclic`,
  so moving it down would have dragged thousands of unrelated lines; the machinery had
  exactly one consumer left behind (`exists_jLine`, which needs `IsJLine` from the region
  jumped over, and is why the block stops where it does).
* **Strengthen the CONCLUSION, never the structure.** `IsJSection` and
  `IsJSectionOnAffine` were left untouched and their two `Nonempty` producers now return
  the witness *with* the general-base pinning, so no consumer of a structure field was
  disturbed and the whole edit outside the move was two extra proof bullets and two
  `obtain ⟨·⟩ → obtain ⟨·, ·⟩`. A `rw` will not see through a structure LITERAL's
  projection (`{ jt := jtr.jt, … }.jt g d`); `show` will, the projection being `rfl`.

## A RED RELEASE DOES NOT STOP YOU — elaborate your module against the LAST GOOD olean of the broken one

(2026-07-31, `flt-lean-258`.) Release 27 did not publish: `ModularCurve/X0.lean` is red
on `merger` with ~193 errors and has not been built since release 25. Everything
downstream of it is unbuildable, which on this tree is most of the project — including
`Modularity/Patching.lean`, three module hops away through `FreyCurve/MazurTorsion`.

An agent whose target lives in that cone will find, in this order: `lake build` fails
naming a module it never touched; and then **`lake env lean` on its own file dies with
`object file '….X0.olean' does not exist`**, because a failing `lake build` DELETES the
target olean at job start. That second message reads like a torn `.lake` and invites a
reseed, which does not help — the olean is missing because the module cannot be built,
not because the snapshot is damaged.

The escape is the `LEAN_PATH` shim CLAUDE.md already describes for the
"iterate while the final build runs" case, pointed at the *release* copy of the broken
module instead:

    cp -rs /scratch/chend-flt/flt-lean-N/.lake/build/lib/lean /tmp/relean-N/lean
    R=~/.flt-release-lake/build/lib/lean
    cp --remove-destination -f "$R"/Fermat/FLT/ModularCurve/X0.*        /tmp/relean-N/lean/Fermat/FLT/ModularCurve/
    cp --remove-destination -f "$R"/Fermat/FLT/FreyCurve/MazurTorsion.* /tmp/relean-N/lean/Fermat/FLT/FreyCurve/
    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    LEAN_PATH="/tmp/relean-N/lean:$LP" LEAN_SRC_PATH="$LSP" \
      lean -o /tmp/relean-N/lean/<your module path>.olean <your file>.lean

**Two mechanics that are not in the existing write-up and cost a round each:**

* **`cp -f` onto a `cp -rs` farm entry WRITES THROUGH THE SYMLINK** into the real
  `/scratch` build directory. `cp --remove-destination` unlinks first. Getting this
  wrong does not fail loudly — it silently plants a stale olean in your own artifacts,
  which is the inconsistent-olean state this file spends a section on.
* **An olean is FIVE files at this toolchain**, not one: `.olean`, `.olean.private`,
  `.olean.server`, plus `.hash` siblings. Overlaying only `.olean` gives
  `failed to open file '….olean.server'`, which reads like a corrupt snapshot and is
  merely an incomplete copy. Always copy `<module>.*`.

Soundness condition, and it must actually be checked: the shim is honest only if
nothing in your cone uses a name added to the broken module since the release sha.
`git diff <release-sha> merger -- <broken module>` plus a grep for the added names
settles it, and a green result from the shim means nothing without it.

Corollary for triage, and it is the reason this belongs here rather than in a report:
**a build failure naming a module you have never heard of is a statement about the
RELEASE, not about your worktree.** Read `tools/merge/RELEASE-*-HANDOVER.md` before
reseeding anything — the merge worker records exactly which module is blocking and why,
and release 27's handover named X0 and its ~35-minute elaboration in the first screen.

## A DÉVISSAGE A DOCSTRING RECOMMENDS MAY NOT CLOSE ITS OWN INDUCTION — check what the RECURSION needs, not what the CHAIN looks like

(2026-07-31, `flt-lean-258`, on `isSplitTorusAt_of_subring_entries` in `Patching.lean`.)

That leaf's docstring — and its Hilbert twin's, in the same words — recommends
*"Schlessinger dévissage against `hglue` … the chain `C = C₀ ⊂ C₁ ⊂ ⋯ ⊂ C_n = A`
obtained by adjoining one element of `𝔪_A` at a time"*. The chain exists and each of
its steps really is a fibre product. **It still does not close the argument**, because
the fibre-product clause needs the condition on a QUOTIENT of the smaller ring at every
step, and going up the chain that quotient is never available — the recursion is not
well-founded on the index `[A : C]`.

What works is one fibre product and a different induction variable: **induct on
`Nat.card A`, the AMBIENT ring**, using the last nonvanishing power `I = 𝔪_A^{n-1}` as
the ideal to quotient by. Both branches (`ι(C) ∩ I ≠ 0`, use `hglue` on
`C ≅ A ×_{A/J} (C/ι⁻¹J)`; `ι(C) ∩ I = 0`, so `C` embeds in `A ⧸ I` and the SAME goal is
the inductive hypothesis) land at a strictly smaller ambient ring, so a plain
`induction n` on a `Nat.card A ≤ n` bound suffices. The one place the residue-field
hypothesis is spent is showing `ι(C) ∩ I` is an ideal of `A` rather than merely a
sub-`ι(C)`-module: `a = ι(c) + m` and `m·x ∈ 𝔪_A·I = 0`.

Two transferable points:

* **A docstring's dévissage is a picture of a FILTRATION, not a proof of TERMINATION.**
  Before building one, write down the recursive call and check its measure decreases.
  Here the picture was right about the geometry and wrong about which parameter shrinks.
* **State such a descent with an INJECTIVE RING HOM, never with `C : Subring A`.** Every
  recursive call lands at a pair (`C ⧸ ι⁻¹J ↪ A ⧸ J`, `C ↪ A ⧸ I`) that is not a
  `Subring` of the original `A`, and the `Subring.map` bookkeeping is pure cost. Derive
  the `Subring` form as a one-line corollary at `ι := C.subtype`.

**And the hypothesis the prose assumed was not in the signature.** That leaf's docstring
says, parenthetically, *"`C` and `A` having the same residue field (`πA` is surjective
and factors through `C` …)"* — and `Function.Surjective (πA.comp C.subtype)` is **not a
binder of the leaf**, though both of its recorded routes need it and the call site
supplies it for free (`πA.comp f = ι.comp frameEv`, with `frameEv` surjective). So add
to the standing checks on any leaf you are dispatched at: **read the docstring for
sentences of the form "X, because Y", and check that Y is in the binder list.** A
parenthetical justification is exactly where a load-bearing hypothesis goes missing,
because it reads as an explanation rather than as an assumption.

## A background `ssh … lake build` reported STOPPED may still be RUNNING — relaunching gives TWO builds in one worktree
(2026-07-31.) A `run_in_background` Bash whose task record is lost across a session
boundary comes back as `stopped` / "no completion record was found … it may have been
running when the previous Claude Code process exited". **That is a statement about the
harness's bookkeeping, not about the remote process.** The `ssh` client died; the remote
`bash -c '… lake build …'` did not. Relaunching the same command then puts **two
concurrent `lake build`s in one worktree**, racing on one artifact directory.
The symptom is a build failure that reads as a broken tree and is not:
    ✖ [4970/4976] Building Fermat.FLT.Modularity.AmpleSheaf
    error: no such file or directory (error code: 4294967294)
      file: …/.lake/build/lib/lean/Fermat/FLT/Modularity/AmpleSheaf.olean
— one `lake` moves the temp olean away from under the other. Two further tells, both
observed: **two `lean` workers elaborating the SAME file**, and a log that `grep` calls
`binary file matches`, because both builds opened it with `>` and the second's truncation
left the first writing at its old offset into a NUL-padded hole (use `grep -a`, and a
FRESH log filename per launch — a reused one cannot be told from the previous run's).
So before relaunching any remote build, look for a live one, and kill by PID only after
checking the cwd (the host runs ~40 other worktrees):
    ssh $H 'for p in $(pgrep -x "lake|lean"); do
              case "$(readlink /proc/$p/cwd)" in $HOME/flt-lean-N) echo "$p";; esac; done'
Killing a `lake` **orphans its `lean` children**, which keep elaborating and keep writing
oleans into that same tree — kill those by PID too, or the "replacement" build races the
corpse of the one it replaced. And note the harness may report the survivor as your
*failed* job (exit 143) when you kill what you think is the stray: the two are
indistinguishable from the tool side, which is the whole reason to check `/proc` rather
than reason from task ids.
## Verification is the COMMAND LINE. No MCP, no LSP, no servers.

(Deyao, 2026-07-25 — supersedes every "trust the MCP diagnostics" rule
below.) The report-MCP, the `flt-lake-socket@` / `flt-report-server@`
units, the local bridges, `.report-server/`, and `state.json` are all
DELETED. `report-mcp.py`, `flt-report-bridge.py`, `flt-lake-socket.py`
and `.claude/unused-binding-check.py` are removed from the repo.

Agents verify with `lake env lean <file>` and `lake build <Module>`,
run ON THE HOST THAT OWNS THE WORKTREE'S `.lake`:

    H=$(cat ~/.flt-worker-host/flt-lean-N)
    ssh $H 'cd ~/flt-lean-N && lake env lean Fermat/FLT/.../File.lean'

`.lake` is a symlink into machine-local `/scratch` on that host, so
running `lake` anywhere else finds no artifacts. `lake`/`lean`/`elan`
are no longer in `permissions.deny`.

**`lake` IS NOT ON PATH IN AN AGENT'S SHELL, AND THE FAILURE LOOKS LIKE A CLEAN
BUILD** (2026-07-31, cost one round). The harness's `Bash` runs a non-login
shell that never sources the profile, so `~/.elan/bin` is absent — *even when
you are already on the owning host and no `ssh` is involved.* The existing note
about this is filed under ssh, which is why it reads as not applying locally.
It does apply. Export it yourself, every call:

    export PATH="$HOME/.elan/bin:$PATH"

The reason it costs a round rather than a second is the SHAPE of the failure.
`lake: command not found` exits **127**, and the log contains no `error`, no
`warning`, no traceback — so `grep -i error` is EMPTY and `grep -c "declaration
uses 'sorry'"` is `0`. Read as "no errors, no sorries", that is indistinguishable
from a perfect build, and it is the same trap the doctrine's truncated-log
section describes arriving by a different route. **Require the positive
terminators — a literal `EXIT=0` *and* a `Build completed successfully (NNNN
jobs)` line with a plausible job count.** An `EXIT=` that is not `0` is a
failure however empty the log looks; zero sorry warnings from a build that never
ran is the most confident wrong answer available.

**`lake` IS NOT ON THE AGENT'S PATH, EVEN LOCALLY, AND THE FAILURE LOOKS
LIKE A FINISHED BUILD** (2026-07-31, flt-lean-106). Since the loop took
over, a prover agent runs *on* its worktree's host and calls `lake`
directly — no `ssh`, so the `cd`-plus-elan-PATH wrapper the ssh recipe
above carries is skipped, and the agent's shell has only
`~/node/bin:/usr/local/bin:/usr/bin:…`. The result is

    /bin/bash: line 1: lake: command not found
    EXIT=127

which, launched in the background with output redirected, is a **6-line
log that returns in one second and contains no `error:`** — i.e. it
passes the "no errors in the log" eyeball test and the harness reports
exit 0 for the wrapper. Export the PATH in every `lake` call:

    export PATH="$HOME/.elan/bin:$PATH"

and require `EXIT=0` *plus* `Build completed successfully` before
believing a build, per the doctrine's positive-terminator rule. A
127 is a missing binary, not a missing proof.

**Why the change.** Every persistent-server failure mode this project
hit came from documents that were opened and never closed, and from
state shared between client processes: a stale `lake setup-file`
failure replayed with `verified: true`, a false clean from an unheard
publish, four rival elaborations of one file, clients wedged on dead
FIFO handles after a server restart. A command-line invocation is a
fresh process that exits and returns its memory, so none of those can
occur — the fix is structural, not disciplinary. The cost is that each
run pays the import load (minutes for a large cone), which is exactly
why the scratch-module rule below matters more than ever.

The standing agent-facing version of this lives in
`/home/chend/.flt-agent-doctrine.md`, which every task prompt points at.

**`lake env lean` DOES NOT REBUILD IMPORTS — a partially refreshed `.lake`
manufactures phantom hard errors** (2026-07-26; cost at least four agents a
cycle each and produced a top-priority "defect repair" dispatch against a file
that was never broken).

`lake env lean <file>` sets environment variables and runs `lean`; it consumes
whatever `.olean`s happen to be on disk. `lake build <Module>` is the only
command that brings the import cone up to date. So after the worktree pointer
moves — which it does at every dispatch — **`lake build <Module>` FIRST, and
only then iterate with `lake env lean`.** An inconsistent olean set is the
default state of a freshly repointed worktree, not an exception.

Why an inconsistent set is worse than a stale one: **olean loading does not
typecheck.** A statement stored in an olean is deserialised verbatim, so an
olean compiled against an OLD signature keeps its old application arity, and the
mismatch surfaces only when a consumer uses the term — as a type mismatch, a
"rewrite failed, pattern not found", a "function expected", or a `(kernel)
application type mismatch`. All four shapes were observed from ONE cause. A
kernel error normally means "this proof is not accepted", and here it meant
"your `.lake` is inconsistent" — the most misleading possible signal.

The concrete instance: `38e8531` moved `Field.absoluteGaloisGroup.map` (and
`mapAux`, `lift_map`) above `variable [NumberField K]`, dropping an instance
argument. That is source-compatible — there is no `@`-application of it in the
tree — but NOT olean-compatible: oleans built before it store
`@Field.absoluteGaloisGroup.map ℚ Kᵥ Rat.instField _ Rat.numberField (algebraMap …)`
with `Rat.numberField` sitting in the `f` slot. Three worktrees whose
`AbsoluteGaloisGroup.olean` had been refreshed while `Semistable`/`Torsion`/
`WeilPairing` had not each reported the same four "hard errors" in
`MazurTorsion.lean`. A full `lake build` there produced `EXIT=0`, zero errors.

**Corollary for triage: "three agents confirmed it independently" is NOT
independent confirmation** when all three verified the same way in worktrees
sharing the same defect. Before treating a hard error as a source defect,
confirm it survives a complete `lake build` of the module, and check the olean
mtimes in dependency order:

    d=/scratch/chend-flt/flt-lean-N/.lake/build/lib/lean/Fermat/FLT
    stat -c '%y %n' $d/Deformations/RepresentationTheory/AbsoluteGaloisGroup.olean \
                    $d/FreyCurve/Semistable.olean $d/EllipticCurve/WeilPairing.olean

A downstream olean older than an upstream one it really imports means the set is
inconsistent and every diagnostic from it is untrustworthy.

**A FULL-CONE BUILD IS NOT ENOUGH — MERGE `main` FIRST** (2026-07-26, and this
corrects the rule immediately above). An agent applied exactly the test
prescribed here — a complete `lake build` of the cone — the error survived it,
and **the error was still not real**: its tree was ~250 commits stale and
current `main` already carried the repair. A full build proves the tree it is
given is broken; it says nothing about whether that tree is current. The two
failure modes are different and the build only separates one of them:

* *inconsistent oleans* → a full `lake build` clears it;
* *stale sources* → only `git fetch && git merge main` clears it.

So the triage order is **merge `main`, then full build, then believe it**. The
same defect (`MazurTorsion.lean`'s `map_baseChange` rewrite) was diagnosed
independently by at least seven agents and repaired on branches by six of them,
every one of which was working from a base that predated the fix landing. That
is not seven confirmations; it is one bug and seven stale checkouts.

**THE LINE NUMBERS IN YOUR OWN TASK PROMPT ARE A FREE STALENESS DETECTOR — check
them first, before anything else** (2026-07-31, measured). The loop generates a
task prompt's `Fermat/…:NNNN` references by scanning **`main` at the moment the
task is written**; the worktree hook fast-forwards the worktree at the moment the
task is *dispatched*. Those are different times, and under the loop they are
routinely hours apart: `flt-lean-318` was handed three targets at lines
3495/16362/17378 and opened a `TateModule.lean` whose copies of them were at
3303/14089/15105 — the checkout was `1411711d` (2026-07-30 11:54) against a `main`
of `d451d20b` (2026-07-31 00:25), **380 commits and +3057 lines in that one file**.

So the check costs one `grep -n` and settles it: if a target's line number in the
prompt does not match the worktree, the worktree is BEHIND `main` and everything
you are about to read is stale — merge before you read, not after your first
confusing result. The failure it prevents is the expensive one: reading a
docstring's absence table, route history or "already refuted" list from a version
that has since been rewritten, and then proving or re-refuting against it.

Do not "fix" the discrepancy by trusting the prompt's numbers and seeking around
them. A prompt is a snapshot of a file you do not have.

**A TARGET THAT DOES NOT EXIST IN YOUR WORKTREE IS A STALE WORKTREE FIRST, A
PHANTOM SECOND** (2026-07-31). This is the same rule, but its sharpest instance,
because a missing NAME looks like a completely different kind of failure from a
stale ERROR and invites a completely wrong report. `flt-lean-116` was dispatched
at `exists_neronModelData` in `X0.lean`, and the name occurred nowhere in its
copy of that file — zero hits, comments included, which is exactly the evidence
CLAUDE.md's own class-5 section says to read as a phantom dispatch. It was not.
The worktree was simply behind: `HEAD` was an old `merger` commit that happened
to be an ancestor of `main`, and one `git merge --ff-only main` brought the
declaration in along with 43 000 lines of `X0.lean`.
**So run these two commands before any `grep` for the target**, and note the
second is what distinguishes the cases — a phantom leaf and an un-advanced
worktree produce identical greps:
    git log --oneline -1
    git merge-base --is-ancestor HEAD main && echo "BEHIND: merge main first"
"The leaf is not here" and "I am not there yet" are the same observation until
you have run that. The dispatch hook normally fast-forwards a worktree at
allocation, so this state means the pointer did not move — do not treat it as
evidence about the frontier.
**There is NO Lean MCP of any kind (Deyao, 2026-07-25).** Both the
`lean-lsp` MCP and the per-worktree `report-flt-lean-N` servers are gone;
`.mcp.json` holds exactly one entry, `annas-mcp`, which is for downloading
literature and has nothing to do with Lean. So neither the
`lean_leansearch` / `lean_loogle` / `lean_local_search` / `lean_run_code` /
`lean_multi_attempt` tools nor `diagnostics` / `build` exist — task prompts
must not offer them. Substitutes: search mathlib by reading it (`grep`/`Grep` over
`.lake/packages/mathlib`) and by the names other owners have already
recorded in docstrings; prototype in a throwaway scratch module verified
through the report MCP, which is the same loop the performance rule already
prescribes and is what agents were mostly doing anyway.

## `lake build` DOES NOT LOCK — a second build in the same worktree runs RIVAL elaborations

(2026-07-31, measured.) Launching `lake build <Mod>` while an earlier `lake build` is still
running in the SAME worktree does **not** block or queue. Both proceed, and `ps` shows the two
`lake` processes each with their own `lean` children **elaborating the same files**, writing the
same `.olean` paths in `/scratch/chend-flt/flt-lean-N/.lake/build`:

    3307744 lake  lake build Fermat.FLT.FreyCurve.MazurTorsion
    3315601 lean    …/Fermat/FLT/FreyCurve/Semistable.lean      <- child of 3307744
    3330028 lake  lake build Fermat.FLT.FreyCurve.MazurTorsion   <- second invocation
    3330679 lean    …/Fermat/FLT/FreyCurve/Semistable.lean      <- child of 3330028, SAME file

The natural sequence that produces it is innocent: start a baseline build in the background, edit
the file while it runs, then start the verification build. The doctrine's "two rival elaborations
writing one `.olean`" warning was written about a self-detached `ssh`; it applies just as much to
two ordinary foreground builds, and nothing in `lake` prevents it.

**Before launching a build, check for one already running, by cwd:**

    ssh $H 'for p in $(pgrep "^lake$"); do
              case "$(readlink /proc/$p/cwd)" in $HOME/flt-lean-N) echo "$p BUSY";; esac
            done'

**If you find yourself with two, the cheapest safe move is usually to let BOTH finish.** They are
building the same sources, so they write byte-identical content; the torn-olean risk comes from
*killing* one mid-write, not from the overlap. Then run one more `lake build` of the target and
require the `Build completed successfully` line — a replay is cheap and it is what certifies the
artifacts are consistent. Kill only if you must, by PID after a cwd check, never by pattern.

## FOLLOW THE HYPOTHESIS: a "base" argument is usually spent in ONE place

(2026-07-31, closing the general-base half of a `ℚ`-only theorem in `X0.lean`.)
When a leaf is the base-free twin of a proven theorem that carries a base
argument — `g : Z ⟶ SpecQ`, `[CharZero k]`, `(hp : p ∤ N)` — do **not** start
from the mathematics. **Grep the proven proof for that argument and find every
use.** In this development the answer is repeatedly *one*, and it is used to
derive one small consequence.

`g : Z ⟶ SpecQ` ran through six declarations of `X0.lean` and was spent exactly
once, in step 1 of `isReduced_geomFibre_nTorsion_of_specQBase`, to get
`(n : K) ≠ 0`. Restating all six with that consequence as the hypothesis —
every proof copied *verbatim*, only the first line of one of them changed —
turned a leaf whose docstring called for "finiteness and flatness of `E[n]`, the
sections of a constant finite group scheme, and the comparison torsor" into a
single crisp arithmetic leaf about one curve over one field. Cost: an afternoon
of copy-and-elaborate at ~6 s per iteration. **The decomposition was mechanical;
finding it was one `grep`.**

Two corollaries.

* **A leaf's own "MISSING INFRASTRUCTURE" list is a hypothesis, not a fact**,
  and it goes stale silently: the list on this node had been retired three days
  earlier when its `ℚ`-side twin was reproven a different way, and the twin's
  docstring recorded the retirement while the leaf's did not. Check the sibling
  before believing the list.
* **The sibling's falsity audit may prove the wrong thing.** This one said the
  `ℚ`-base "is load-bearing and cannot be dropped: over a base of residue
  characteristic `p ∣ n` the statement is FALSE". The geometry was right and the
  conclusion was wrong — at such a base the *data* the statement quantifies over
  is empty. "The hypothesis is load-bearing for the PROOF" and "for the TRUTH"
  are different claims and audits conflate them.

## AN AUDIT'S "MISSING ATOM" IS A GUESS AT THE COST, AND IT IS USUALLY TOO BIG

(2026-07-31, `HasseBound.lean`.) Two independent audits in that file, months apart,
ended at the same sentence — *"separable and non-constant ⟹ `#ker = deg > 1`"* — and
both priced it the same way: "a fibre-counting statement for a separable rational map
of curves, which is a real piece of work", i.e. blocked on a degree theory this tree
does not have and, in characteristic `p`, cannot cheaply get (`Isogeny.lean`
machine-REFUTES the characteristic-`p` dual isogeny). On that basis the leaf it gated,
the ordinary criterion `exists_ne_zero_qTorsion`, was left open for three days with two
expensive routes written out beside it (Deuring by character sums; the Verschiebung).

**No fibre is ever counted, and the proof is 90 lines.** The audits asked for the
CARDINALITY of a fibre; what the argument needs is only that an injective map has
SINGLETON fibres — which is the hypothesis, not a theorem. Concretely: `φ` injective
with `x`-witness `A/B` in lowest terms, so for each slope `ξ` the polynomial
`A − ξ·B` has exactly ONE distinct root; if its degree is `≥ 2` that root is a
MULTIPLE root, and there the Wronskian `A′B − AB′` vanishes. Distinct slopes give
distinct roots, there are infinitely many slopes, so the Wronskian vanishes
identically — and a vanishing Wronskian is exactly `λ(φ) = 0`, inseparability.

The general lesson, and it is about how to READ the audits this project is full of:

* **An audit's "missing atom" is the cheapest thing its author could see, not the
  cheapest thing there is.** It is a hypothesis about cost, in the same way a
  docstring's "this needs lemma X" is (see *Leaf cost estimates are hypotheses*).
  Both audits here named the right OBJECTS — "the `x`-witness `A/B` and its Wronskian
  `A′B − AB′`, both already handled in that file" — and overestimated what has to be
  done with them. When an audit names the objects and then prices the step high, try
  the objects.
* **A quantitative statement blocking a leaf is often needed only qualitatively.**
  `#ker = deg` was demanded; `#ker > 1` was used. Check which one the consumer
  actually calls before accepting the blockage.
* **The Wronskian is this tree's separability oracle**, and it is cheap:
  `DifferentialCharacter.lean`'s `IsDiffCharCert` says `λ·(…) = (A′B − AB′)·(…)`, so
  `A′B − AB′ = 0` gives `λ = 0` with no side conditions, and `λ(F) = 0` for the
  `q`-power Frobenius is literally `derivative (X^q) = 0`. Reach for it before
  reaching for degree theory, the Cartier operator, or `E[p^∞]` structure theory.

One mechanical trap met on the way, worth knowing before it costs a cycle:
`IsRationalMap` hands you witnesses `A, B` that need NOT be coprime, and the fibre
argument needs coprimality. Dividing by `gcd A B` loses the witness identity exactly
on the (finite) zero set of the gcd, and there is no cheap way to recover it there —
no continuity argument is available for `x(φP)`, which is not a polynomial in `x(P)`.
So carry the gcd as an explicit third polynomial `G` and state every downstream lemma
"for all `P` with `G(x P) ≠ 0`"; then absorb `G` by excluding the finitely many slopes
it is attained at. Do not try to prove the reduced identity holds everywhere.

## `omit [Inst] in` goes ABOVE the doc comment, not between it and the theorem

(2026-07-31, one wasted build round.) The `unusedSectionVars` linter tells you to
write `omit [TopologicalSpace A] in theorem ...`, and the obvious placement — after
the `/-- … -/` docstring, immediately before `theorem` — is a **parse error**:
`unexpected token 'omit'; expected 'lemma'`, reported at the END of the docstring
line, which reads like a problem with the docstring. `omit … in` is a command
combinator and takes the whole declaration, docstring included, so it belongs on
the line ABOVE the `/--`.

Same shape for `open scoped X in` and `set_option … in`. And note the reverse trap:
`open scoped Classical in` on a theorem whose STATEMENT contains a `Finset.filter`
changes which `Decidable` instance the statement elaborates with, so it can silently
make your theorem a different statement from the one its consumers expect. Prefer
the `classical` TACTIC inside the proof.

## `ring` CANNOT SEE A RATIONAL NUMERAL IN `ℚ[X]` — pick the model for writability

(2026-07-31, flt-lean-106, and it decided the shape of a whole leaf.) `ℚ[X]`
carries a `Div` instance — `Polynomial.div`, the *Euclidean* one — and is **not
a `DivisionRing`**. `ring` only evaluates `/` in a `DivisionRing`; everywhere
else it treats the quotient as an **atom**. So in `ℚ[X]` the numeral `3/37` is
opaque, `ring` cannot prove `(3/37)^2 = 9/1369`, and every polynomial identity
containing a non-integral coefficient fails. Measured on a two-line `example`,
not assumed — and the failure is silent in the sense that it looks like an
ordinary `ring` defeat, not like a missing instance.

Consequence for the explicit-certificate files (`GenusOneKernelPolynomials.lean`
and its level-`37` analogue): **the model is chosen for INTEGRALITY of the
derived polynomial, not for minimality of the curve.** At `p = 37` the minimal
conductor-`1225` Mazur–Swinnerton-Dyer curve `[1,1,1,−208083,−36621194]` has a
kernel polynomial with constant term `−N/37` — genuine, since `elldivpol(E,37)`
has leading coefficient `37`, so Gauss's lemma does not force monic factors to
be integral. Mathematically fine for `IsKernelPolynomial`, which asks only for
monicity; unwritable in Lean.

The repair is a change of model, and the arithmetic of *which* model is short:
the models of a fixed `j` are the quadratic twists composed with the
`u`-scalings, which multiply every `x`-coordinate by an arbitrary `c = d·w²`,
and a derived polynomial's coefficients transform as `f_k ↦ c^(deg−k) f_k`. So
integrality of `f_0` is a divisibility condition on `c`, and the optimal `c` is
the smallest one meeting it — here `c = 37`, i.e. the quadratic twist by `37`
(model `[1, 46, 1, −284864943, −1854973327019]`, conductor `1225·37²`), which
clears the `1/37` exactly once and costs only a factor `37^(18−k)` on the
coefficients. Scaling instead (`u = 1/37`, `c = 37²`) is legal and twice as
expensive; there is nothing cheaper than `c = 37`.

**So: compute the certificate polynomial BEFORE committing to a model, and check
its denominators.** Doing it the other way round means generating a megabyte of
Lean that cannot compile, and the diagnosis costs a full build.

## A LARGE EXPONENT LITERAL COSTS RECURSION DEPTH `3n`, AND `maxRecDepth` LARGE MAKES IT WORSE
(2026-07-31, measured over about twenty probe builds while closing the `p = 11` and `p = 17`
rows of Mazur's non-CM table.)
`X ^ n` for a `ℕ` LITERAL `n` is a trap whenever the elaborator has to unify a term containing
it against a pattern. Unification falls through to `whnf`, `whnf` unfolds `npowRec`, and
`npowRec` recurses **once per unit of `n`** — measured depth `≈ 3n`. A chain step at
`n = 3466` elaborates; the same step at `n = 6932` needs `maxRecDepth 20000`; the certificates
here run to `n = 23 ^ 11 = 952809757913927`.
**Three things about this cost a whole session between them.**
1. **The failure has NO LOCATION.** Past the stack it is `Stack overflow detected. Aborting.`
   and nothing else — no line, no declaration, no tactic. Every natural next step is wrong:
   `lake env lean -s 65536`, `-s 262144` and `-s 524288` all still die (the last one is also
   silently misparsed and reports `no such file or directory`). To get a *located* error, drop
   `maxRecDepth` to ~20000 and read the errors; that is diagnosis, not a fix attempt.
2. **`set_option maxRecDepth` LARGE IS THE WRONG DIRECTION.** At `4000000` these files crash;
   at `20000` they compile. A high limit lets a doomed reduction run until the C stack dies
   instead of failing fast so the elaborator can take another route. The predecessor's file
   carried `maxRecDepth 10000000`, which is exactly how a locatable error became a crash.
3. **The symptom mimics whatever you were last worried about.** Because depth scales with the
   exponent and the exponents grow along a chain, the failures appear at a *boundary partway
   down the chain* — which reads convincingly as "the polynomial identities got too big". Two
   full rewrites were spent shrinking the identities (degree 230 → degree 22, `expand` →
   square-and-multiply). Both were sound engineering and **neither fixed anything**, because
   the degree was never the problem.
**The fix is to keep the exponent out of unification, behind a definition:**
```lean
def XPow {q : ℕ} (f : (ZMod q)[X]) (n : ℕ) (a : (ZMod q)[X]) : Prop := f ∣ X ^ n - a
```
State every chain step as `XPow f n a` rather than `f ∣ X ^ n - a`. Now `n` is an *argument*,
unification assigns `?n := 952809757913927` and never looks inside `X ^ ?n`. Same statements,
same proofs, seconds instead of a crash. Cross into the raw `∣` exactly once, at the end,
where the target is fixed and there is no pattern to match.
Corollary, learned the same way: **do not `rw` a `ℕ` equation into exponent position.**
`rw [hexp]` inside `X ^ (Nat.card (ZMod ℓ)) ^ m` puts the literal straight back and the
blow-up returns. Move the arithmetic into a `ℕ`-only lemma (`xpow_card` here) where no
polynomial appears.
Everything lives in `Fermat/FLT/EllipticCurve/MazurNonCMFrobenius.lean`; the four generated
row modules under `MazurNonCMFrobenius/` are produced by `gen_modules.py` at the repo root
(`gen_frobenius.py`, `gen_binpow.py`, `gen_factored.py`, `gen_coprime.py`, `gen_row.py`), which
also re-derives every certificate and cross-checks it against PARI/GP before emitting Lean.
**And a mathematical corollary worth more than the tooling: `H ∣ X ^ (q ^ m) - X` does NOT
need `H`'s factors to be irreducible.** Factor `H = ∏ fᵢ`, prove each `fᵢ ∣ X ^ (q ^ m) - X`
separately, and reassemble with `IsCoprime.mul_dvd` off explicit Bézout certificates. That
needs pairwise COPRIMALITY only — which is a one-line `⟨u, v, by ring_nf⟩` — where proving
irreducibility of a degree-11 factor over `F₂₃` is circular (the standard test *is* this
divisibility). It is also `k²` cheaper, since every `ring_nf` call scales with `(deg f)²`.
## WHEN THE TARGET FILE HAS AN INHERITED RED BASELINE, VERIFY *DIFFERENTIALLY*

(2026-07-31, `flt-lean-112`, on `X0.lean` during the release-27 window, when that
file carried ~193 errors none of which were anybody's current work.)

Every verification rule in this file assumes a green baseline is reachable —
`EXIT=0` plus `Build completed successfully`. Sometimes it is not: a release can
hand you a module that has not built since two releases ago, and then "did my edit
break anything" and "does the file build" are different questions and only the
first is yours. Waiting for someone else to make it green is not an option, and
shipping unverified is the class-7 hazard.

**The differential check answers the first question exactly.** `lake env lean`
writes no `.olean`, so two runs do not race and neither disturbs `.lake`:

    cp <pristine copy of the file> Fermat/.../TargetBase.lean   # a REAL module path
    echo Fermat/.../TargetBase.lean >> $(git rev-parse --git-common-dir)/info/exclude
    lake env lean -DmaxErrors=800 Fermat/.../TargetBase.lean > /tmp/pre.log  &
    lake env lean -DmaxErrors=800 Fermat/.../Target.lean     > /tmp/post.log &
    wait

Then require **post ⊆ pre**, after shifting line numbers by your own diff's
insertion count (`git diff --numstat`). Put the copy at a genuine module path —
the name is derived from the path, so a `module` file elaborates fine there and
its diagnostics carry the *pre-edit* line numbers, which is what makes the two
logs comparable.

Three things that decide whether this works:

* **Do NOT repair the baseline's wounds first.** It is tempting, and it destroys
  the check: one parse error truncates the file, so fixing it unmasks thousands of
  previously-hidden lines and `post ⊆ pre` fails for reasons that have nothing to
  do with you. Repair after the differential, or not at all.
* **Check where the first parse error sits relative to your edit.** If it is
  *below* you, your declarations are still elaborated and the check is meaningful.
  If it is *above* you, the run says nothing about your work and you must fix that
  one wound (and then re-take the baseline).
* **A comment-nesting scan is the cheap companion, and it sees what the compiler
  cannot.** The compiler shows only the FIRST parse error; a character-level
  `/-`/`-/` scan lists them all in one second. Iterating "report first stray, patch
  it in a TEMP COPY, rescan" enumerates the whole set without a single build — three
  wounds here, matching the merge worker's own first entry to two lines.

And the ownership rule that goes with it: **a parse error is a passer-by's to fix,
a 193-error module is not.** Report the list to whoever owns the file, in their
line numbering as well as yours, with the repair for each — a repair chosen by
reading which paragraph belongs to which declaration, since "insert a `/--`" and
"delete the earlier `-/`" both parse and only one of them is faithful.

## Verify in a scratch module, not in the giant file

(Deyao, 2026-07-25, from a measurement — this is the fleet's single
biggest throughput lever.) **Develop against a throwaway scratch module
that imports only what you need, and do exactly ONE final blocking
verify against the real target file.** Delete the scratch before
committing. Agents who worked this way cut their round trip from **~30
minutes to ~1 minute**; several discovered it independently and reported
it unprompted.

Why, measured rather than assumed: **elaboration is single-threaded —
one core per file.** Sampling every `lean --worker` on this 96-core
machine (a `/proc` utime+stime delta, *not* `ps pcpu`, which is a
lifetime average and misleads) found 101 workers consuming **11.1 cores
between them**, 77 of them idle, the busiest at 1.29 cores. iowait was
0–3%; RAM had 1.5 TB free. So the fleet is **not** disk-, CPU- or
memory-bound, and moving `.lake` to tmpfs or deduplicating the 62
mathlib copies would buy nothing. What costs wall-clock is that a
15k-line file such as `Modularity/Interface.lean` re-elaborates on ONE
core however many are idle beside it. The only way to go faster is to
elaborate less.

Corollaries: batch edits and verify once rather than per-edit; a
client-side timeout means the server is still elaborating, so re-issuing
attaches rather than restarting (see the single-flight section); and
splitting oversized modules is what converts idle cores into throughput,
because the file is the unit of elaboration.

### Keep iterating WHILE the final build runs — `lake build` DELETES the target olean first

(2026-07-31.) The scratch-module loop above dies the moment you start the one final
verify: `lake build Fermat.FLT.ModularCurve.X0` removes `X0.olean` at the START of the
job, so every scratch that imports `X0` fails instantly with

    object file '….lake/build/lib/lean/Fermat/FLT/ModularCurve/X0.olean' … does not exist

and you are locked out of the fast loop for the entire build — an hour or more for a
79k-line module. That is exactly the window in which you want to be working on the NEXT
leaf.

**The shim, which costs about a second.** Build a symlink farm of the whole olean tree in
`/tmp`, drop the LAST GOOD copy of the one module into it, and put it FIRST on `LEAN_PATH`:

    cp -rs /scratch/chend-flt/flt-lean-N/.lake/build/lib/lean /tmp/relean-N/lib/     # symlinks, instant
    cp -f  ~/.flt-release-lake/build/lib/lean/<Mod path>/X0.olean* \
           /tmp/relean-N/lib/lean/<Mod path>/                                        # real file, overrides

    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" \
      lean Fermat/FLT/ModularCurve/Scratch.lean

Two things that are easy to get wrong, both of which cost a cycle here:

* **`lake env lean` RESETS `LEAN_PATH`** — prefixing it on the `lake env` call is silently
  discarded. Harvest the environment with `lake env printenv` and invoke bare `lean`.
* **A single-module override is not enough.** Lean resolved `X0` out of `/tmp` and then
  looked for `X0`'s own imports in `/tmp` too, failing on the first one. The farm has to
  mirror the WHOLE tree; `cp -rs` (copy-as-symlinks) does that in 0.3 s and costs no disk.

`~/.flt-release-lake/build` is the natural source for the good copy — and check first that
`git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- Fermat/` is empty, in which case
that whole tree can also just be `rsync`ed over a stale `.lake/build` instead of rebuilding.

This is what let one agent prove two independent leaves in the time of one build.

**AND THE FIRST THING A SCRATCH WILL TELL YOU IS `unknown identifier` — that is
almost never a missing import** (2026-07-31, cost one cycle). A scratch that
`public import`s a giant `module` file and names one of its declarations gets

    Unknown identifier `IsNarrowRayEquivMod`
    ... Lean's `autoImplicit` option causes an unknown identifier to be treated
    as an implicitly bound variable ...

and the hint points at imports. The real cause is usually an enclosing
**`namespace` opened near the top of the file and never closed** —
`ModThree.lean` opens `namespace GaloisRepresentation.IsHardlyRamified` at line
437 and runs 60 000 lines inside it, so every declaration is
`GaloisRepresentation.IsHardlyRamified.foo`. The fix is one `open` line.

Two things make this hard to see, and both are worth knowing because they are
properties of THIS repo rather than of Lean:

* the declaration's own source line is at column 0 with no visible indentation,
  so nothing near it suggests a namespace;
* **scanning for the enclosing scope with `grep '^end '` is wrong twice over.**
  It misses a bare `end` (no trailing space), and — because this project's
  docstrings are prose — it MATCHES lines like
  `end of this docstring carries the counterexample`, which are inside `/-- -/`
  and are not scope delimiters at all. A depth counter built on that grep
  reported the wrong nesting depth by three.

  The reliable check is to grep `^namespace` alone (there are few) and read the
  hits, or just ask the compiler: `#check @Some.Namespace.name` in a two-line
  scratch costs seconds against the built olean.

**THE OLEAN-SCRATCH TRICK WORKS FOR A LEAF *INSIDE* THE GIANT FILE TOO**
(2026-07-31, measured on `heckeOp_traceOp_comm_of_not_dvd`). The doctrine file
says the "import the built olean" form applies "whenever your new material sits
*downstream* of the giant file rather than inside it". That is too weak. A
scratch that `public import`s the already-built `Fermat.FLT.Modularity.Interface`
olean and RESTATES the target under a primed name verified in **6 seconds**,
against ~25 minutes for one `lake build` of `Interface` — roughly forty
edit/verify cycles for the price of one. The finished text was then moved into
the file verbatim for a single blocking verify.

The one soundness condition, and it is easy to honour: the scratch sees the
WHOLE file, so **only use names declared BEFORE your target's line**, and check
each one's line number (`grep -n "theorem <name>"`) before relying on it. Nothing
else about the scratch differs — same namespace, same `open`s, copied from the
enclosing section header.

Two things this makes cheap that were not: (a) `#print axioms` on the finished
proof before it ever touches the real file; (b) warning cleanup — the
`unusedSimpArgs` / "tactic never executed" linters fire in the scratch at
6 s/round, so the text that lands in the shared file is already warning-clean.

Seeding for it is free when `main` has not moved in Lean:
`git diff --stat <release-sha> HEAD -- '*.lean'` empty means
`rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/`
gives you a fully current artifact set in about a minute, and the confirming
`lake build` is a pure replay.

**A DECOMPOSITION'S GLUE IS LEVEL-GENERIC BY CONSTRUCTION — so prototype it
as an `example` that takes the sub-leaf as a HYPOTHESIS** (2026-07-31,
measured in `X0.lean`: **16 s against 8 min**, a 30× round trip, and the
prototype pasted into the 79 000-line file compiled first try).

The scratch-module rule above says "import only what you need". For the
commonest kind of iteration in this development — cutting a leaf into a
smaller leaf plus glue — you can go further and need **none of the project
at all**, because the glue never inspects the project's definitions. Write

    example {XZ AZ SR : Scheme.{0}} {xstr : XZ ⟶ SR} {astrZ : AZ ⟶ SR}
        (U : XZ.Opens) (hcodim : ∀ z : XZ, z ∉ U → 2 ≤ ringKrullDim (XZ.presheaf.stalk z))
        (v : (U : Scheme.{0}) ⟶ AZ) (hv : v ≫ astrZ = U.ι ≫ xstr)
        (purity : ⟨the sub-leaf's full statement, verbatim⟩) :
        ⟨the parent's conclusion, verbatim⟩ := by …

with the project's structures (`IsSmoothProperCurve`, `AbelianSchemeStruct`,
`IsReductionBase`, …) simply DELETED from the signature and abstract
`Scheme` variables in their place. If the glue really is glue it will not
miss them; if it does miss one, that is the useful answer — the cut is not
where you thought it was, and you learned it in seconds.

Two things this buys beyond speed. It **proves the cut is honest**: a glue
that compiles without the hypotheses is demonstrably not smuggling any of
the parent's content into the residue. And the abstracted signature is
worth QUOTING in the residue's docstring — not committing as a module,
which would just be another unreachable file — because it states the
sub-leaf in the one form that matters: stripped of everything the consumer
does not actually use.

**THE BEST SCRATCH IMPORTS THE TARGET MODULE ITSELF** (2026-07-31, measured on
`ModThree.lean`: **18 s** per scratch round trip against **>30 min** for one
`lake build` of the module). The rule above says "imports only what you need",
which reads as "import as little as possible" and leads agents to reconstruct a
minimal import list by hand. When the target module's own `.olean` is CURRENT,
the fastest and most faithful scratch is

    module
    public import Fermat.FLT.<the module you are editing>
    @[expose] public section
    local notation "𝒪₃ᵥ" => …      -- re-declare its `local notation` lines verbatim
    theorem my_attempt … := by …
    end

Loading one big `.olean` costs seconds; you get every lemma already proven in the
file, the exact instance environment, and no guessing about which import supplies
what. Copy the `local notation` block out of the target file — notations are
`local` and do NOT come through the import, and that is the only thing that has to
be repeated.

Two caveats, both real:
* it says NOTHING about the target file's own import surface or notation scope —
  the existing warnings above still apply, and the one final verify is still
  against the real file;
* **`lake build <Module>` DELETES that `.olean` while it runs**, so a scratch
  importing it fails with `object file … does not exist` for the whole duration.
  Do the scratch iteration first and the build last; do not interleave them.

**YOUR OWN `lake build` DISABLES YOUR SCRATCH MODULE FOR ITS WHOLE DURATION**
(2026-07-31, measured). `lake build <Module>` DELETES the target's `.olean`
before elaborating, so from the moment you start a full-file verify until it
finishes — 40+ minutes for `MoretBailly.lean` — every scratch verify fails with
    error: object file '….lake/build/lib/lean/…/MoretBailly.olean' of module
    Fermat.FLT.Modularity.MoretBailly does not exist
That reads like a broken `.lake` and invites a re-seed or a `lake exe cache get`,
which fixes nothing. It is just your own build, and the cost is real: the two
things an agent wants to do most — verify the file and keep developing — are
mutually exclusive by default, so the fast loop stops exactly when it is needed.
**The fix is one line, and it makes scratch work independent of your build:
elaborate the scratch against the RELEASE oleans.**
    BASE=$(lake env printenv LEAN_PATH)
    export LEAN_PATH="/home/chend/.flt-release-lake/build/lib/lean:$BASE"
    lean Scratch.lean          # NOT `lake env lean`
Two traps in that recipe. **`lake env lean` sets `LEAN_PATH` itself**, so it
silently discards whatever you exported — you must invoke `lean` directly with
lake's own path captured first, or the override does nothing and you get the
same "does not exist" error. And this is only sound because
`/home/chend/.flt-release-lake` is the build of a commit with no Lean diff
against `main` (check: `git diff --stat <sha> main -- Fermat/` empty, where the
sha is in `~/.flt-release-lake/sha`); if it is stale in the Lean sources you are
developing against yesterday's statements.
## Sorry and have discipline (glue-first, no floating)

- **Glue first.** At any frontier, first replace the bare `sorry` with
  a full skeleton: definitions and choices as real code, every
  believed-true step as a sorried `have` with its exact statement,
  final assembly written and compiling. Only then prove the sorried
  steps. Proven `have` bricks stacked in front of a trailing `sorry`
  with no written consumer are floating.
- **`sorry` only against a stated goal.** A `sorry` may only replace
  the PROOF of an explicitly written proposition (`have h : <full
  statement> := by sorry`). Never a bare `sorry` covering an unstated
  remainder, never `(by sorry)` as an application argument.
- **Every bound `have`/`let` must be consumed** (Deyao, 2026-07-22).
  Prune unused ones before committing (verify each prune compiles).
  **This is now the AGENT's own responsibility** — the enforcing hook
  (`.claude/unused-binding-check.py`) was deleted on 2026-07-25 along with
  the MCP it fired on. Nothing checks it for you; Lean's own
  `unusedVariables` linter is the closest thing to a signal.
- **Never use `private` to dodge the free-floating check** — open the
  consumer sorry first, always top-down.

## NAME THE WITNESS — an existential leaf pushes hypotheses onto every consumer

(2026-07-31, `X1.lean`.) When a proven theorem is stated as `∃ g, P g` but its
proof is literally `⟨someExplicitTerm, …⟩`, the existential is not abstraction —
it is a **leak**. Every consumer must either `choose` or carry `g` and `P g`
as extra hypotheses through its own statement, and a *sorry leaf* that does the
latter is now quantified over ALL witnesses when only one was ever meant.

That is not merely inelegant; it manufactures an unwritten proof obligation.
`integral_Ioi_one_sub_frickePartner_ne_zero_x1TwentyFive` took a bare cusp form
`g` plus the Fricke functional equation as hypotheses, because
`exists_frickeInvolutionOn` gave it nothing better — and its docstring then had
to record, under "assumptions I am recording rather than resolving", that this
was sound *because `g` is pinned by the relation: a holomorphic function on the
connected upper half plane is determined by its values on the imaginary axis*.
That argument is correct and was never written in Lean. Naming the witness
(`frickeSlashOn N hN h1 h0 f`, which the proof already produced) **deleted the
obligation instead of discharging it**, dropped two hypotheses from the leaf,
and changed what a prover owes from "reason about an unknown partner" to
"compute the `q`-expansion of a named form".

So: **state the named form as the theorem and the existential as its two-line
corollary**, keeping the corollary only where a consumer genuinely does not care
which witness it gets (here `cuspFEPairOn`, which `choose`s). The cost is one
declaration; the check is whether the proof of the existential is an `⟨_, _⟩`
with no `obtain` above it. `X0.lean`'s `axisRestrict_one_div_eq_frickeSlash` is
the same pattern on the `Γ₀` side and predates this note — the `Γ₁` mirror had
simply not been brought into line.

## Free-floating code: definition and policy

**Free-floating code** is any project declaration that is not in the
transitive used-constant cone of the root theorem
`fermat_last_theorem` — i.e. no proof term reachable from the root
actually uses it (a sorried body contributes no dependency edges, so
material built bottom-up for a still-sorried consumer is free-floating
until the consumer's proof skeleton is written to consume it). Only
crossings into external libraries are exempt. Free-floating code is
not allowed: the Stop hook verifies this with the Lean compiler. The
cone itself is computed inside `ProgressCensus.lean`'s `runCensus` (the
`"floating"` field of its JSON output, via ImportGraph's
`Name.transitivelyUsedConstants` — already a vendored transitive
dependency through mathlib's own lakefile, not a hand-rolled BFS),
obtained through `progress-tree.py`'s census, which since 2026-07-25 runs
as ONE `lake env lean ProgressCensus.lean` over ssh on the worktree's
assigned host — no resident server, no cache file. Each run pays the
import load of the project cone (minutes), so run it once per bookkeeping
cycle rather than in a loop, and keep the tree BUILT: the census reads
oleans and dies with `object file '….olean' does not exist` if they are
stale.
`free-floating.py` is a thin standalone entry point over the same
query, applying only the keep-list filter below. Blocks with
instructions to commit and delete. Work top-down.

**Deleted free-floating content (2026-07-18): see the deletion commit
below.** The sweep removed 19 whole modules (the ModThree/Dickson–PGL2
clusters, `TateCurveConstruction`, `TateUniformization`, `OddAbsIrred`
among them) at file granularity with import-closure. The deleted
material — including the full nonarchimedean Lambert/bilateral
machinery for the Tate uniformisation and the ℂ-analytic
`weierstrass_equation` development — remains available in git history;
recover pieces with `git show <deletion-commit>^:<path>`.

DELETION-COMMIT: `52297bf2d7bfe856d7ce01736f0113c11f6fa613` — recover
deleted files with
`git show 52297bf2d7bfe856d7ce01736f0113c11f6fa613^:<path>`.
(This is the post-split hash; the pre-split dissertation-repo hash was
`8282dfb03cd1a390fd979a1d38fa2bb3b863ac20`.)

**Elaboration-invisible dependency classes (learned 2026-07-18).** The
term-level cone under-approximates what elaboration needs; deleting a
"floating" declaration in these classes breaks the build even though
no cone proof term mentions it. Every deletion must be build-verified
(revert-on-red), and these classes must be skipped or handled
specially:

1. *Auto-generated members* (`rec`/`casesOn`/`mk`/`injEq`/`ext`/…)
   share their source lines with the parent declaration.
2. *Instances consumed by typeclass synthesis then inlined*.
3. *rfl-`@[simp]` lemmas* used by `simp` without appearing in proof
   terms.
4. *Syntax-level `simp`-argument references* that never fire.
5. *Section/namespace scaffolding* inside or adjacent to reported
   declaration ranges.
6. *Module-system opaque exports*; also `example` blocks pin their
   instance dependencies at elaboration.

Build-verified members of these classes are recorded in
`free-floating-keep.json`; `free-floating.py` subtracts them and
reports them as `kept_invisible`. Reduce residual floaters by writing
the consuming proofs, not by further blind sweeps.

## Filesystem hazard: macOS case-insensitivity

The filesystem is case-INSENSITIVE: `Fermat` and `fermat` are the SAME
path. On 2026-07-16 an `rm -rf` of a stray capital-F directory deleted
the entire project including its `.lake` cache; recovery worked only
because the tree was committed-clean. Rules: never `rm -rf` a path
that differs from a real path only by case; prefer `git clean -n`
(dry run); keep the tree committed before destructive operations.

## AN AUDIT'S "BLOCKED ON MISSING STRUCTURE" VERDICT EXPIRES — RE-CHECK THE NAMED PRECONDITION

(2026-07-31.) A leaf's atomicity audit is usually written as a conditional: *this cut is
blocked, and it becomes available exactly when X exists*. The condition is the useful part
and it is the part nobody re-reads. `X18.two_divisible_pic`'s descent-axis bullet said the
`2`-descent cut "needs residue fields `κ(v)` and the norms `N_{κ(v) ⊗ L / L}` — precisely
the degree theory `PlaceData` deliberately omits … so the cut is available exactly when
someone extends `PlaceData` with residue fields."

**No extension was ever needed and none happened.** A valuation determines its own valuation
ring, so `O_v`, `m_v`, `κ(v) = O_v ⧸ m_v` and `deg v = [κ(v) : K]` are definable from the
`ord` axioms `PlaceData` already had — and by 2026-07-30 they were IN THE SAME FILE
(`PlaceData.valRing`, `valMax`, `residue`, `degOf`), with `exists_degreeMap` PROVEN over
them, roughly 3600 lines above the audit that declared them absent. The verdict was written
before that work and was never re-read against it.

This is the same failure as the VOID-AUDIT rule above, in the other direction: there, a
statement changed under a valid audit; here, the WORLD changed under a valid audit. Both
produce an audit that is honest, internally correct, carries a date, and is wrong.

So, two rules:

- **When an audit says "blocked until X exists", grep for X before believing it.** One
  `grep -n` is the whole check, and its answer is a fact rather than an opinion.
- **Separate "structurally blocked" from "expressible but very large" in the verdict, and
  say which you mean.** Only the first is a reason never to dispatch. Here the arithmetic
  obstruction (`#Sel₂ = 1`: class groups and `S`-units of a degree-`6` field) is entirely
  real and unchanged — but "nobody can even state it" and "somebody would have to build a
  lot" call for opposite decisions, and the bullet had been read as the first for days.

Corollary for whoever writes the audit: phrase the precondition so it is GREPPABLE — name
the declaration you would need, not the capability. "needs `PlaceData.residue`" would have
been refuted by the next reader in ten seconds; "needs the degree theory `PlaceData`
deliberately omits" survived because there was nothing to look up.

## "THE TARGET EXISTS ONLY ON `merger`" IS USUALLY NOT A REASON TO DROP THE TASK
(2026-07-31, `flt-lean-97`.) A task prompt said: audit against `main` first, and if the release
carrying the target declarations has not landed, DROP and re-queue. It had not landed — the two
targets and their proven prerequisite existed only on `merger`, mid-release-27 — and dropping it
would have idled a worker for a whole release cycle.
The cheap thing to check instead is **how many `Fermat` imports the target FILE has.** A leaf
file near the top of the tree usually has one or two, and then merger's version of it is very
nearly self-contained relative to `main`. Here `HyperellipticJacobian.lean` (10 522 lines on
merger) imports exactly `GroupTheory.Descent` (identical on both) and `NumberTheory.
ProjectiveHeight` (differs). Taking merger's copy of BOTH onto a main-based branch built green
in one shot; taking only the target file failed with a single `Unknown identifier`, which is
what named the second file. So the recipe is:
    git checkout merger -- <the target file>
    lake build <the module>              # the failures name the other files you need
    git checkout merger -- <those too>   # repeat; it converges in one or two rounds
**Prefer this to the two obvious alternatives.** Basing the branch on `merger` drags in the
whole unreleased release (153 k lines here) and couples you to its fate. Re-inventing the
decomposition on top of `main` guarantees a rival-cut conflict with merger's version of the same
names — exactly the "two complete proofs of one theorem cannot both be carried" case that costs
an author a reconciliation. Taking the file verbatim makes the merge a no-op for the imported
lines and a pure content add for what you prove on top.
Two things to tell the merge worker when you do it: which files you imported wholesale, and that
if it DECLINES that release's payload for those files your branch reintroduces it. And build a
downstream consumer — `grep -rln "import <YourModule>" Fermat/` — because a main-era consumer
against a merger-era dependency is exactly the interface split that class 7 is about. (Here the
one consumer, `MazurTorsion.lean`, was green.)
## TWO `lake build`s IN ONE WORKTREE CLOBBER EACH OTHER — including your own two
(2026-07-31, same agent, cost one 20-minute build.) The doctrine's warnings about concurrent
builds are all about TWO AGENTS sharing a worktree. One agent is enough. A downstream build
(`Fermat.FLT.FreyCurve.MazurTorsion`) died with
    error: failed to open file '.../HyperellipticJacobian.olean': No such file or directory
not because anything was wrong, but because I started a rebuild of `HyperellipticJacobian` in
the same worktree while the consumer build was still running, and lake unlinks the olean before
rewriting it. The failure is indistinguishable from a torn `.lake` and reads as a much more
serious problem than it is.
Worse, it is silent until the end: `grep -c error` on the log was **0** while the build was
still running, so an early check says "clean" and the real answer arrives minutes later. Only
the `EXIT=` marker you wrote yourself is a verdict.
So: **one `lake build` per worktree at a time.** If you want a downstream check, run it AFTER
the module it depends on has settled, not alongside an edit-rebuild loop. Scratch-module
`lake env lean` runs are safe to overlap with nothing — they read oleans too.
## A DECLINE IS A COMMIT, NOT A SHRUG — ancestry is the only receipt for a branch

(2026-07-30, medic.) The loop hands a merge worker a list of branches and gets
no itemised answer back — a sentinel says `panic: false` and one line of prose.
So it has exactly one way to tell, per branch, whether that branch was dealt
with: **is it an ancestor of the main you published?** Everything the merger is
allowed to do produces one. A merge does. So does a DECLINE, *provided* it is
recorded the way the class-7 section above prescribes — `git checkout HEAD --
<the files>`, then commit the merge, so the diff against the first parent is
empty on purpose and the message says the payload was declined.

`git merge --abort` and moving on is not a decline. It leaves no receipt, and
the branch is indistinguishable from one you never reached.

That distinction used to cost the work. Adopting a release discharged the whole
claim on the strength of the release being *complete* — main moved, snapshot
and audit current — which says nothing about how much of the payload got
merged. A merger that merged 18 of its 55 branches and was killed before
reporting had the other 37 dropped in one assignment, their worktrees pinned in
`awaiting_merge` for ever, because a worker is freed only by its branch
BECOMING an ancestor of main and nothing was left to merge it. **78 worktrees —
one full day of the fleet's output — were stranded that way**, and nothing
noticed until an invariant check summed two numbers that had never been summed.

Row 10 now folds the unlanded remainder of a claim back into the batch, so a
merger running out of time is safe: merge what you can, publish, and the rest is
re-offered next release. But that only works if a decline is a decline. An
unrecorded one comes back to the next merge worker for ever.

General form, and this is the third time it has bitten in a week: **an
assignment to a field that holds a CLAIM ON WORK is a deletion of work.** Every
other hand-off in the loop is a fold or a move. Both leaks — `r11_action`'s
`.inflight = list(batch)` and `r7_action`'s `.inflight = None` — were single
assignments, and both were invisible because the state they produced is
indistinguishable from a state where the work never existed.

## What the merge batch is for: Lean edits that could turn a green build red

(Deyao, 2026-07-26.) **The batch exists to protect a green build, and nothing
else.** So the dividing line is not "who wrote it" but "can it break the
build":

- **Lean code edits** — anything under `Fermat/` — go to a branch and into
  `~/.flt-merge-batch`, always. They can turn green into red, which is exactly
  what the merger exists to catch.
- **Tooling unrelated to the math content** — `.claude/*`, `flt-*.py`,
  `CLAUDE.md`, memory files — the orchestrator **commits directly to `main`**.
  It cannot make the Lean build red, so routing it through a merge worker buys
  nothing and costs a release cycle of latency: the fix is inert on an
  unmerged branch precisely while the bug it fixes is live.

Deyao amended this the same day he first objected to a tooling commit on
`main`, so both halves are his: the objection was to the orchestrator doing it
*silently and by accident*, not to the act itself.

**One asymmetry to remember either way.** The merger's release step is
`git branch -f main <the sha it built>`, so a commit on `main` that the merger
has not merged is not in its history and that force-move would discard it. In
practice the merger merges `main` before moving it (it has done so at every
release), which is what makes direct tooling commits safe. If you ever see a
release drop one, that is the mechanism.

And note it is effectively irreversible: worktrees fast-forward to `main` at
every dispatch, so within minutes a dozen sit ON the commit, and rewinding
`main` makes their branches non-ancestors of it — which the dispatch hook
hard-crashes on, by design. So the bar for a direct commit is "certainly not
Lean", not "probably fine".

## git is allowed — except force-push

Claude may run `git` commands; exercise ordinary caution with
history-destructive operations. **`git push --force` remains
explicitly banned**: `permissions.deny` in `.claude/settings.json`
blocks all variants. Plain `git commit` (ssh-signing is automatic via
Deyao's agent; if signing fails with "No private key found", the
agent — Bitwarden — is locked: ask Deyao). Commit trailers: the
standard Co-Authored-By and Claude-Session lines.

## Anna's Archive MCP (annas-mcp)

The server is `annas-mcp.py` at the repo root, registered in the
committed `.mcp.json` with `"ANNAS_KEY": "${ANNAS_KEY}"` — the secret
is NEVER stored in the repo; export `ANNAS_KEY` in the shell
environment before launching Claude Code. The script itself reads
`os.environ["ANNAS_KEY"]`.

The `download_annas` tool wraps Anna's Archive
`dyn/api/fast_download.json`, which returns ONE `download_url` per
call. Mirror selection is via the optional `domain_index` /
`path_index` parameters.

**Quota accounting (empirically verified).** Anna's quota tracks
DISTINCT md5s, not raw API calls. Retrying the *same* md5 with a
different `domain_index` (e.g. to dodge a TLS error or 404) is
**free** after the first call that day; a *new* md5 costs one slot.

**SSL / TLS errors on a download URL**: usually a broken cert chain on
that CDN mirror. Retry the *same md5* with a different `domain_index`
(free). **Keep certificate verification on** — never `verify=False`;
a persistent TLS failure means the file is not safe to download.

## "The pin has no Riemann–Roch" is TRUE and often IRRELEVANT — check for a NORM first

(2026-07-31, flt-lean-133.) Three separate leaves in `ModularCurve/X0.lean` were
priced at "needs `Γ(A,−)` as a functor to `R`-modules together with its rank", i.e. a
Riemann–Roch development. For the pole-order one that price was wrong by a whole
development, and the reason generalises.

**A finite free algebra has a NORM, and the degree of the norm is the invariant you
were about to build by hand.** `WeierstrassCurve.Affine.CoordinateRing` is free of
rank 2 over `R[X]`, so `ord z := (Algebra.norm R[X] z).degree` is defined at this pin
with no new theory, and it IS the pole order along the point at infinity (`ord x = 2`,
`ord y = 3`). Everything a degree function needs is already proven upstream:
`Algebra.norm` is a `MonoidHom` and `Polynomial.degree_mul` is additive over a domain,
so `ord` is additive on products *for free*; `CoordinateRing.degree_norm_smul_basis`
computes it as `max (2 • deg p) (2 • deg q + 3)` in the `{1, Y}` basis, which gives
`max` on sums; and `CoordinateRing.degree_norm_ne_one` is exactly "the value semigroup
is `⟨2,3⟩`". That was enough to prove the linear shape of any SURJECTIVE
`R[W] → R[W']` over a domain — no sheaves, no cohomology, no `𝒪(nO)`.

So before accepting "absent from the pin", ask what STRUCTURE the object already has:
finite free ⟹ norm, trace, characteristic polynomial, discriminant. A `grep` for the
missing *theory name* (`RiemannRoch`, `CartierDivisor`) will always come back empty
and always feels conclusive; a grep for the *invariant you actually need* on the
object you actually have will not.

Two corollaries that cost nothing and were both worth more than the proof:

- **Where an argument BREAKS tells you what the leaf is really about.** The
  domain-only step was "leading terms do not cancel", i.e. `gr R[W] = R[t²,t³]` is a
  domain iff `R` is. So the general-`R` residue is purely NILPOTENT — which promoted
  the file's own `ℚ[ε]/(ε²)` counterexample from a peripheral warning to a statement
  of the whole remaining problem, and re-priced the attack from Riemann–Roch to
  deformation theory.
- **Prove the hypothesis you wish you had.** The leaf took an arbitrary compatible
  `Φ`; two open immersions with equal range plus `ι` being a monomorphism force `Φ`
  to be the canonical equivalence, so surjectivity was free and was the only thing
  the argument consumed. A leaf stated for "an arbitrary `Φ` with `hΦ`" was never a
  generalisation, and nobody had checked.

**THE MCP DOES NOT EXIST FOR A LOOP-SPAWNED AGENT — USE THE OPEN WEB**
(2026-07-31, prover on `exists_neronModelData`). A task prompt instructed
"download BLR *Néron Models* through the Anna's Archive MCP
(`download_annas`)". For an agent started by `flt-loop.py` that route is not
available in either half: `annas-mcp` is not in the agent's tool set, and
`ANNAS_KEY` is unset in the agent's environment — it is exported only in the
shell that launches an interactive Claude Code session — so calling
`annas-mcp.py` by hand fails too. **Task prompts should stop offering it**,
the same way they stopped offering the Lean MCP.
The open web served the whole book in fifteen seconds, and the fleet's network
is unrestricted (`curl https://…` returns 200):
    curl -sL -o blr.pdf \
      "https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf"
    pdftotext -layout blr.pdf blr.txt     # 15469 lines, the WHOLE book, no OCR
Two things that could have stopped this and did not: the `_tc` in that filename
is part of the scan's name and **not** an abbreviation for "table of contents" —
the file is all ~350 pages; and a `WebSearch` summary said the page "doesn't
provide direct access to the specific content", which was a statement about the
snippet the search returned, not about the PDF. Fetch it and look.
So the procedure is: **`WebSearch` for the title plus a distinctive internal
section number, then `curl` the first university-mirror hit, then
`pdftotext -layout`.** Do that before concluding a reference is unobtainable.
Running text and theorem numbering survive extraction cleanly; displayed
formulas do not, so read for the ARGUMENT and restate the mathematics yourself,
exactly as the OCR section below prescribes.
**Copy what you download to `~/sources/`** — outside the repo, since these are
8–16 MB scans — so the next agent does not pay for it again. It currently holds
Katz–Mazur and Bosch–Lütkebohmert–Raynaud, each as `.pdf` plus extracted `.txt`.
## PDF Text Extraction

When extracting text from a PDF, the output will be read by an AI, not
a human. Preserve as much information as possible. First try
`pdftotext -layout <input>.pdf <output>.txt`. OCR only when that
output is empty or garbled.

**Use the NATIVE tools — `tesseract`, `pdftoppm` and `pdftotext` are all on
PATH, and Docker is NOT available on this machine** (2026-07-27; the
`ocrmypdf` Docker recipe previously documented here could never have run).
This route recovered Fontaine's Prop. 1.7(i)(a) from an image-only GDZ scan
where `pdftotext` returned nothing but the cover sheet:

```
pdftoppm -r 300 -gray -f <first> -l <last> <input>.pdf /tmp/pg
for f in /tmp/pg-*.png; do tesseract "$f" "${f%.png}" --psm 6; done
cat /tmp/pg-*.txt > <output>.txt
```

`--psm 6` ("assume a single uniform block of text") is what makes running
text come out readable; the default page-segmentation mode shreds
two-column mathematics. OCR page RANGES you actually need rather than whole
books — 300 dpi greyscale is a few seconds per page. Expect mathematical
notation to survive poorly: read OCR output for the ARGUMENT, then restate
the mathematics yourself rather than trusting transcribed formulas.

## Freeing a worktree needs a LIVE-PROCESS check, not a clean `git status`

(2026-07-27, orchestrator error.) `flt-lean-86` was marked `ready` and dispatched into **while another
agent was still working in it**. Two agents then shared one worktree: the newcomer found *two* `lean`
processes elaborating `WeilPairing.lean` into the same `.olean`, its `git add -A` swept the other agent's
uncommitted `HasseBound.lean` edits into an unrelated commit, and when it restored the file the other
agent **rewrote it again** — which is how the collision was finally diagnosed. It also made
`MazurTorsion` look red (two errors) from a defect that was neither on `main` nor in either agent's work.

The trigger was a *correct* observation read as the wrong conclusion. A completing agent reported that
`flt-lean-86` "sits at `81eb57e2`, clean, and its branch was fast-forwarded — nobody is working on it."
Every clause was true at the instant it was measured. **A worktree between edits is indistinguishable
from an idle one by `git status` alone**, and an agent doing a 25-minute `lake build` touches nothing for
25 minutes.

So the rule is: **before promoting any worktree out of `claimed`, check the OWNING HOST for live
processes**, not just the tree:

    H=$(cat ~/.flt-worker-host/flt-lean-N)
    ssh $H "pgrep -af '[l]ean.*flt-lean-N'"

and cross-check `python3 flt-owner.py --all` (latest dispatch per worktree, from the transcripts) against
the completion notifications actually received. **The notification stream is the ground truth for "this
agent has stopped"** — a third party's report that a slot looks idle is not. This is the same principle
`.claude/skills/fleet-revive/SKILL.md` states for staleness sweeps ("staleness cannot distinguish working
from dead"), applied to the promotion direction.

Corollary, and the reason this was recoverable: the intruding agent **tagged the other agent's WIP**
(`flt-lean-86-hassebound-wip`) before touching anything, and left the working tree dirty by design. When
a collision is discovered, preserve first and report loudly; do not clean up to make `git status` tidy.

## A `∀ P : <presentation structure>` LEAF IS ONLY AS TRUE AS THE STRUCTURE PINS ITS OBJECT

(2026-07-31, generalising a refutation found 2026-07-30.) `X1.lean` and `X0.lean` state most
of their geometry as `∀ P : Gamma1GITPresentation N (Spec K), <property of P.A>`. That shape
is only sound for properties the FIELDS force. `Gamma1GITPresentation.classify_dM` pins the
coarse ring `B = A^G` — it says `Spec (algebraMap B A)` IS the classifying map of the
universal family — and pins `A` **not at all**. `smoothCurve_A_of_gamma1GITPresentation` was
refuted on exactly that gap, by an explicit inhabitant nobody had looked for.

**The test is cheap and mechanical: PINCH the honest presentation.** Given any inhabitant `P₀`
with ring `A₀`, group `G₀`, invariants `B₀`, and a `G₀`-stable ideal `0 ≠ I ⊊ A₀`, set

    A := A₀ ×_{A₀ ⧸ I} A₀,   G := G₀ × ℤ⧸2   (G₀ diagonal, the generator swapping),
    dM := (Spec Δ)^* dM₀     for Δ : A₀ → A, a ↦ (a, a).

Every field survives — each datum is a pullback along an explicit ring map, `pr₁ ∘ Δ = id`
carries `cover`, and `A^G = B₀` keeps `classify_dM` — while `Spec A` is two copies of
`Spec A₀` glued along `V(I)`, i.e. nodal. **So no property that fails at a node is provable
from these axioms**, and any leaf asserting one is FALSE, not merely hard.

Two corollaries worth having in advance:

* **The swap is what keeps `B` pinned, and it is also why the pinch is not universal.**
  Dropping it (`G := G₀` alone) would break far more — the two components stop being
  exchanged — but then `A^{G₀} = B₀ ×_{B₀ ⧸ (I ∩ B₀)} B₀ ≠ B₀`, and `classify_dM` rejects it.
  So the pinch family only ever attacks properties destroyed by GLUING (regularity,
  smoothness, normality, being a domain), never properties preserved by it (reducedness,
  Krull dimension, transitivity of `G` on components). Check which side your leaf is on
  before assuming the refutation transfers: `transitiveMinimalPrimes_tensorProduct_of_`
  `gamma1GITPresentation` was audited against the pinch on 2026-07-31 and survives it.
* **The repair is to MOVE the citation, not to weaken the statement.** `Gamma1RigidifiedModuli`
  carries `universal`, a fine-moduli property WITH a uniqueness clause, so it pins `Spec A` up
  to unique isomorphism. State the citation there and carry it down as a structure FIELD
  (`smoothM : SmoothOfRelativeDimension 1 strM` is the worked example). Weakening the
  conclusion instead just makes a second universally-quantified guess of the kind that was
  just refuted.

**And a field added this way SHRINKS the class every other leaf in the file quantifies over.**
Once `smoothM` is a field the pinched `P` is not an inhabitant, so every route audit written
earlier was performed against a strictly larger class — those audits are not void, but they
are not evidence about the new class either. Re-run the ones that turned on a missing
regularity/normality precondition; that precondition is now free.

## A "DOES NOT USEFULLY SPLIT" VERDICT IS SCOPED TO THE CONSTRUCTION ITS AUTHOR HAD IN MIND

(2026-07-31, `ArtinSymbol.lean`.) `closure_frobAt_eq_top` (Chebotarev) carried a careful,
honest docstring verdict: *"audited, faithful, and deliberately NOT decomposed"*, with a
numbered list of three ingredients the fixed-field reduction would need and which the pin
does not have. **Two of the three did not exist.** They were consequences of one unstated
design choice — that the fixed field `M = L^H` should be GALOIS over `K`, so that one can
speak of `frobAt K M`. Galois-ness forces `H` normal, which forces transporting
`Algebra.IsUnramifiedAt` along an automorphism (obstacle 1), and `frobAt K M` forces
functoriality of `arithFrobAt` down a tower (obstacle 2). But the reduction never needs
`frobAt K M`: the only thing wanted from `M` is that its primes have residue degree `1`,
and that is read straight off the congruence `σ y ≡ y^(N𝔭) (mod Q)` restricted to `𝓞 M`,
with `M` used as a RING and no Galois structure at all. With that, the reduction is ~90
lines against mathlib as it stands, and the residual leaf is a clean density statement
naming no Frobenius and no Galois group.

**So when a docstring says a node does not decompose, read the obstacle list as a claim
about ONE route.** Ask which of the obstacles are forced by the goal and which are forced
by the author's chosen intermediate object; the second kind vanishes when you weaken the
intermediate object to the least structure the argument actually uses. The tell here was
that every listed obstacle mentioned `M` being Galois, while the conclusion mentions only
`Subgroup.closure`.

Two corollaries worth keeping separate:

- **The verdict was still right about the OTHER cut it considered**, and said so: the
  contrapositive ("for every proper `H` there is an unramified `Q` with `frobAt K L Q ∉ H`")
  trades one leaf for an equivalent one. The discriminator between a real cut and noise is
  whether the residual statement stops mentioning the project's own vocabulary. That test
  also correctly REJECTS the analogous cut on the sibling leaf `artinMap_toPrincipalIdeal`
  (reduce abelian reciprocity to the cyclic case): the residual still mentions `frobAt` and
  `Gal(L/K)`, and is where the classical proof spends all its effort.
- **Do not add the infrastructure an obstacle list names once you no longer need it.**
  Tower functoriality of `frobAt` is genuinely missing and genuinely reusable — and adding
  it here would have been FREE-FLOATING code, since nothing in the cone consumes it. An
  obstacle that dissolves is not a licence to build it anyway.

## A DIMENSION-COUNT CUT CANNOT USE A RELAXED OBJECT — THE TWO HALVES SQUEEZE FROM OPPOSITE SIDES

(2026-07-31, `flt-lean-120`, on `exists_hilbertAuxCotangentSpanningFamily` in
`HardlyRamified/HilbertModularity.lean`.) The commonest cut this development makes on an
arithmetic leaf is *"define the object `X`, then split into (a) `thing = dim X` and (b)
`dim X = n`"*. It is the right cut when `X` is definable. **It is a FALSE-LEAF FACTORY when
`X` is only definable up to a choice, because (a) and (b) are monotone in `X` in OPPOSITE
directions and the safe-direction trick that works everywhere else does not exist here.**

Concretely: the leaf wanted `dim_k(cotangent of R_Q) ≤ q` cut through the Selmer group
`H¹_Q(F, ad⁰ρbar)`, whose local condition at the hardly ramified places is the FINITE-FLAT
condition in cohomological form — absent from the pin and from `Fermat/`. Two cheap
substitutes are available and BOTH produce a false leaf:

* **relax** at those places (no local condition — the literal untwisted transcription of the
  file's own `hilbertH1TwistUnramified`): `X` grows, so (a) survives and **(b) is false**, by
  exactly the local terms of the Euler-characteristic formula (`+[F_w : ℚ_ℓ]` at each `w ∣ ℓ`);
* **tighten** (full local triviality): `X` shrinks, (b) survives and **(a) is false**.

**The tell, and it generalises past Selmer groups: check the MONOTONICITY of each half in the
object before choosing its definition.** If the two halves are monotone the same way, a cheap
over- or under-approximation is safe and the cut is real; if they are opposed, the object must
be exactly right and the cut costs whatever defining it costs. The same file shows the contrast
one section away: on the DUAL side the clause is a VANISHING (`… = 0`), which is monotone in
one direction only, and the file's own section note correctly argues that relaxing there is
STRONGER hence safe. A vanishing tolerates slack; a dimension count does not.

**Two corollaries that decided what to do.**

* **A definition that cannot appear in a TRUE statement is not merely useless — it is
  FREE-FLOATING CODE, which this project forbids.** The dispatch that produced this had asked
  for ~80 lines of untwisted `ad⁰` vocabulary (the twisted definitions with the `det`-twist
  deleted; the underlying `HilbertAdZero.rep` was already in the file). Writing it would have
  compiled, looked like progress, and had no consumer it could ever legally acquire. **Before
  building vocabulary for a future leaf, write the leaf's STATEMENT first and check it is
  true.**
* **A "this cut was considered and REJECTED as unsafe" verdict is exactly as transferable
  between twins as a falsity audit, and just as reliably not transferred.**
  `Deformation.lean`'s section note above `adZeroCycloChar` had recorded this refutation at the
  `ℚ` level — naming `L_HR`, naming FLATNESS as its condition at `ℓ`, and adding that
  existentially quantifying the local-condition family does not rescue the split because *"an
  existential does not split into two leaves, which is the whole purpose of a cut"*. Every word
  of it applied at the `F` level and nobody had looked. **When a cut looks obvious and the file
  is a `ℚ`/`F` twin pair, grep the OTHER file for the same cut before taking it** — this file's
  existing rule about faithfulness repairs (immediately below) covers repairs and not
  rejections, and the rejection is the cheaper thing to find.

What was delivered instead is the cut that IS affordable and is the same one the `ℚ` level
took: peel the pure commutative algebra off the arithmetic. `hilbertRelCotangentFinrank` (the
relative cotangent space `𝔪/(𝔪²+J)` for an arbitrary `J`, the `F`-level twin of
`CotangentModL` with the hard-coded `J = (ℓ)` generalised) plus BOTH Nakayama directions makes
`∃ t : Fin q → R, 𝔪 = span(range t) ⊔ (𝔪² ⊔ J)` and `finrank ≤ q` provably EQUIVALENT — so the
restatement is not a strengthening and the leaf's existing falsity audits transfer with no
re-derivation, which is worth saying explicitly in the docstring. One leaf becomes one leaf;
what changed is that the arithmetic owner now sees an inequality between natural numbers with
no ideal in it. Judge it by what is LEFT in the leaf, not by the count.

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

## TWO INDIVIDUALLY-CORRECT REPAIRS CAN BE FATAL TOGETHER

(2026-07-27.) `exists_artinDivisorNormIndex_le_ray_class` was refuted-and-restated once (making `mm` an
OUTPUT rather than an input), and a later integration added a support clause to the conclusion
(`∀ w, w.asIdeal ∣ mm → w.asIdeal ∣ mm₀`). **Each change is right in isolation. Together they made the
leaf FALSE**: the support clause confines the chosen `mm` to primes already dividing `mm₀` — enlargement
is permitted only in the EXPONENTS — while the only hypothesis on `mm₀` was `mm₀ ≠ ⊥`. A caller may then
supply an `mm₀` missing a ramified prime, and no admissible `mm` is reachable at all.

Witness: `F = ℚ`, `χ` cutting out `ℚ(i)`, `ℓ = 2`, `k = 1`, `mm₀ = ⊤`. No height-one prime divides `⊤`,
so `mm = ⊤`, `Im = ⊤`, and `P = ⊤` (the congruence is vacuous, i.e. `h⁺(ℚ) = 1` in the formal language),
giving `(P ⊔ N).relIndex Im = 1` against `A.relIndex Im = 2`. The conclusion reads `2 ≤ 1`. Not a
unit-ideal corner case: `mm₀ = (3)` refutes it identically.

**Why no ordinary check catches this.** Both edits pass review against the statement as it stood when each
was made. A falsity audit performed before the second edit certifies a statement that no longer exists,
and the audit *label* survives to say the leaf was checked. So a leaf can carry an honest, correct
FALSITY AUDIT and still be false.

**The rule: when a leaf is restated a second time, the earlier audit is VOID, not inherited.** Re-run it
against the composite statement and write a SECOND audit; do not reason "the first audit covered the hard
part". The repair here was one hypothesis (`hmm₀ram : ∀ w, IsRamifiedCharRayClass F χ w → w.asIdeal ∣ mm₀`)
that the consumer **already held and was discarding** — so the fix cost nothing, and the consumer's
statement did not change. That is the usual shape: the missing hypothesis is often already in the caller's
hand.

### Its cheapest and commonest form: DELETE × REFACTOR = an ORPHAN LEAF, merged cleanly

(2026-07-31, `X0.lean`.) One branch **collapsed** a cut: it deleted the two leaves
`exists_isAbelianWeilEigenvalues` and `prod_one_sub_eq_of_isJacobianOf` and made their consumer
`card_jacobian_of_isWeilEigenvalues` the single leaf. Concurrently, a second branch **refactored**
one of those very declarations the way its curve-side neighbour is built — turning
`exists_isAbelianWeilEigenvalues` into a proven assembly over a NEW leaf
`exists_isAbelianWeilEigenvalues_galoisField`. Both edits are correct in isolation, and — this is the
whole trap — they **do not conflict textually**, because the refactor's new declaration is added at a
line the collapse never touched. So git merged both, silently, and the result was:

* the assembly gone (the collapse deleted it), and
* its sub-leaf still there, `sorry`, with **no consumer anywhere in the tree** — free-floating, and
  carrying a docstring asserting it was "the sole remaining leaf of" a declaration that the same
  commit had deleted.

Net effect of two correct edits: `−2 + 1` instead of `−2`, and a theory build (Tate modules,
Frobenius in char `p`, isogeny degree) still owed by the frontier for nothing at all.

**Nothing in the frontier machinery can see this.** The orphan emits a perfectly ordinary
`declaration uses 'sorry'` warning, contains a real `sorry` token in real source, and lives in a
module on the root's import closure — so it is visible to the compiler, to `flt-frontier.py`, and to
the census, and all three report it as an ordinary open leaf. It is exactly the free-floating-code
condition, which is why the standing free-floating check is the one thing that catches it.

**The rule: whenever a merge deletes a declaration, grep the merged tree for consumers of everything
that declaration consumed.** A leaf whose only consumer was deleted is not "now unowned", it is
**garbage** — delete it and record in its section docstring where to recover it from. Conversely,
when you are about to delete a declaration, check whether anyone is refactoring it (`~/.flt-merge-batch`
and the other worktrees' diffs), because the refactor will survive your deletion rather than conflict
with it.

Corollary for a prover handed a leaf: **`grep` the tree for your target's consumers before proving
it.** Zero consumers means the task is a deletion, not a proof, and the honest sentinel reports that.

## A "DO NOT CUT THIS WAY" PROHIBITION IS DATED EVIDENCE, EXACTLY LIKE AN AUDIT

(2026-07-31, `exists_qAdicPolarizedSystem_finiteBase`.) The rule above says a falsity audit is
VOID once the statement is restated. The same is true in the other direction, and it is easier to
miss because the prose sounds permanent: a docstring paragraph headed **"DO NOT CUT THIS THROUGH
`X` — THE RESULTING LEAF WOULD BE FALSE"** is a claim about `X` **as it stood on the day it was
written**, not a standing law. When `X` changes, the prohibition expires with it — and a later
agent who reads the heading and stops has been stopped by history.

The concrete case. `exists_qAdicPolarizedSystem_finiteBase` (finite base field `k`, char `p`)
carried such a paragraph forbidding the obvious cut through `DualStruct`, and the reasoning was
right: `DualStruct.weil_nondegenerate` was asserted at every `(F, x, I, n)` with `(n : R) ∈ I`,
so at `I = (p)`, `n = p` — where `μ_p(k̄)` is trivial and the pairing is constantly `1` — it
concluded `A[p](k̄) = 0`, which an ordinary elliptic curve over `𝔽_p` refutes. `DualStruct` was
UNINHABITED over any positive-characteristic fibre, so the cut really would have produced a false
leaf.

**But the same paragraph named the repair — "gate `weil_nondegenerate` on `(n : F) ≠ 0`, which is
free in characteristic zero".** One binder in `Modularity/AbelianScheme.lean`, one construction
site to fix (the base-change transport, which gets the new hypothesis handed to it and passes it
straight through), and the cut became legal. The prohibition was not a wall; it was a work item
with a wall-shaped heading.

**AND AN EXPIRED PROHIBITION IS A MAGNET — THIS ONE WAS CUT TWICE, A DAY APART, AND NEITHER
AGENT COULD SEE THE OTHER.** The paragraph above was first written as "and nobody had done it".
That was false when written. The gate had ALREADY been made on 2026-07-30 by another agent, and
that agent had gone on to make the whole downstream cut: `main` at 2026-07-31 had none of it,
`merger` had all of it — `weil_nondegenerate` gated (plus `PolarizationStruct.\
weil_hom_nondegenerate`, which the second cut missed), `exists_qAdicPolarizedSystem_finiteBase`
PROVEN, and the residual geometry left as `exists_dualPolarization_finiteBase`. The second run
independently re-derived the gate, re-cut the same seam, wrote a rival predicate
(`IsQAdicPolarizedHom` against `IsQAdicBoundedPolarizationHom`) and a rival residual leaf
(`exists_dualPolarization_of_mult_finiteBase`) with the *same binders and same conclusion*, and
verified all 390 lines green — all of it discardable, because two proofs of one theorem cannot
both be carried.

This is class 5 (the release window) with a specific accelerant, and it is worth naming because
the accelerant is predictable: **a prohibition that names its own repair is the most attractive
target in the file.** It reads as high-value and cheap, so it is exactly what an agent scanning
for tractable work picks — and several will pick it in the same window. The generic advice
("check `merger` before starting") did not fail here so much as it was not run; but the specific
form is stronger and costs one command, so run it whenever a docstring hands you an unblocking
task:

    git show merger:<file> | grep -n '<the leaf the prohibition blocks>'

If that shows the leaf already proven, the prohibition has been spent and the follow-on work is
done. Check `merger` for the CONSEQUENCE, not just for your own target's name — here the target
was still `sorry` on `main` and already proven on `merger`, which is the whole of the trap.

So, four things worth carrying:

1. **Read the prohibition to its end.** This development's docstrings are unusually good about
   naming what would unblock them. A paragraph that says "this is impossible *until* Y" is a task
   description for Y, and Y is often much smaller than the leaf it blocks.
2. **Check the premise against the source before obeying.** `git log`/`grep` the structure or
   declaration the prohibition is about. It costs a minute; the paragraph may predate its own fix.
3. **A false *hypothesis* leaf poisons more than a false conclusion.** The same defect had already
   been audited on the char-0 sibling `exists_dualPolarization_of_mult`, which was recorded FALSE
   AS STATED on 2026-07-30 with `exists_qAdicWeilSystem_of_mult` PROVEN over it — i.e. a proven
   theorem resting on an uninhabitable hypothesis, worth nothing, and *not visible to any
   sorry-count*. Repairing the structure fixed the char-0 half as a side effect of unblocking the
   finite-base one. When you find an audit saying "leaf L is false and the defect is in shared
   structure `X`", the fix belongs in `X` and it pays out at every consumer at once.
4. **When you DO find you were second, decline your own branch — and leave the receipt.** The
   duplicate here was reverted to `main` on its own branch rather than shipped, so the merge
   worker gets an empty Lean payload instead of a two-sided conflict in a 20 000-line file over a
   theorem it already has. The green work stays recoverable at its own sha (`git show 0025e539`),
   named in the revert's commit message. A decline that is committed and points at its own
   history costs nothing and can be reversed; one that is merged costs whoever resolves it.

## `pkill -f "lake build"` IS A FLEET-WIDE KILL SWITCH — IT MATCHES THE AGENTS THEMSELVES

(2026-07-31, measured on gambit while stopping one worktree's own build.) `pkill`/`pgrep -f`
match against the WHOLE command line of EVERY process on the host, and the fleet runs ~25
worktrees on one machine. So a pattern chosen to mean "my build" means "everyone's build":

    pgrep -f "lake build" | wc -l          # 70 processes, across 25 worktrees

**24 of those 70 were the agents' own `flt-job-*` Claude processes.** Not their builds — the
agents. Every prover prompt contains the sentence *"Verify with `lake build` on the module"*, and
the prompt is passed as an argv element, so the literal string `lake build` is in the command
line of every running agent. `pkill -f "lake build"` therefore SIGTERMs two dozen live agents
mid-proof along with every build on the box. Nothing about the command looks dangerous, which is
the point of writing it down.

Scope the pattern to the worktree PATH, which is the one string that is actually yours:

    pkill -f "/home/chend/flt-lean-N/Fermat"     # only this worktree's lean workers

And note the two traps that follow from it. **`lake build`'s `lean` workers do not have "lake
build" in their command line** — they are `.../bin/lean <path> -o <path>`, so killing the `lake`
parent orphans the children, which keep elaborating and keep writing into `.lake`. Kill by path
or you leave writers behind. And **a module that reports `error: Lean exited with code 143` was
SIGTERMed, not broken** — 143 is 128+15. Two modules failed that way here and neither had
anything wrong with it; reading 143 as a defect is how a phantom "broken on main" report gets
written.

Before any `pkill`, run the same pattern through `pgrep -af` first and read what comes back. It
costs one command and it is the only way to see the blast radius, which on this host is never
just you.

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

## A DECOMPOSITION CAN LEAVE A HYPOTHESIS ON ONLY ONE HALF — and the child inherits the parent's audit, which then certifies nothing

(2026-07-31, `card_relPoint_not_liesIn_le_of_finite_toAffineLine`.) The rule above is about a leaf
restated TWICE. This is its decomposition analogue, and it is commoner, because decomposition is
the main move this development makes.

`card_relPoint_le_of_hasDoubleCoverOfAffineLine` was cut into two leaves along the `U` / `X ∖ U`
seam. The parent's degree hypothesis — the three-point clause `_hthree`, which is what makes
`deg φ ≤ 2` — was restated on the `U` half and **silently omitted from the complement half**,
whose conclusion is the bare bound `≤ 2`. That bound *is* the degree. So the complement leaf was
FALSE from the minute it was written.

Counterexample, and it is not exotic: `S = K = 𝔽₂`, `X = ℙ¹`, `U = ℙ¹ ∖ {0, 1, ∞}`, and
`φ = t + 1/t + 1/(t−1)`, whose polar divisor is `(0) + (1) + (∞)` so that `U = φ⁻¹(𝔸¹)` and `φ` is
finite of degree `3`. Every surviving hypothesis holds — proper, smooth of relative dimension `1`,
geometrically connected, `ι` an open immersion and dominant, `φ` finite over the base — and the
conclusion reads `3 ≤ 2`. Raise `#D` to raise the count arbitrarily.

**Why every ordinary check passed.** The child's docstring was the parent's audit, reproduced
verbatim and correctly — it even *cites* the degree, "at most `d ≤ 2` points". The prose was
true of the parent. It was not true of the child, because the hypothesis the prose depends on
had gone to the sibling. An audit reproduced onto a child certifies the PARENT's statement; it
carries no information about the child's, and its presence makes the child look checked.

**The mechanical check, and it is cheap: after any decomposition, diff each child's hypothesis
list against the parent's and justify every omission in writing.** "It is on the sibling" is a
valid justification only when the children are ALTERNATIVES; when they are CONJOINED — two halves
summed by the consumer, which is the usual shape here — a hypothesis the parent needed is needed
by whichever half uses it, and possibly by both. `_hthree` was needed by both.

**Corollary, a fast smell test for reviewers.** When a leaf's conclusion is a NUMERIC BOUND and no
hypothesis mentions the quantity that bound measures (a degree, a rank, a genus, a conductor), the
leaf is almost certainly false — look for the hypothesis on a sibling before looking for a proof.
The repair here was free, in the shape the section above predicts: the consumer already held
`hthree` from destructuring `HasDoubleCoverOfAffineLine` and was passing it to one child and
discarding it at the other.

## A TASK PROMPT THAT CITES A REPAIR COMMIT IS CITING `merger`, NOT `main`
(2026-07-31, `flt-lean-65`.) A prompt opened with "two repairs landed that day (commits
`f1ca4452` and `b1225666`) and you must read the leaf's docstring before anything else — it
now contains a FALSITY AUDIT and a step-by-step route". Neither commit was an ancestor of the
worktree's HEAD: the dispatch hook fast-forwards to `main`, and both were still sitting on
`merger`. So the docstring in the file was the OLD one, the statement was missing the `htors`
binder the prompt described, and `IsTraceDualFunctional`'s third clause was the weak version
the prompt said had been replaced. **Everything the prompt asserted was true, and none of it
was true in the worktree.** This is the release window (class five) seen from the receiving
end, and it is the normal case for any prompt written by an agent that just finished: the
repair it is telling you about is *its own*, and it has not landed.
The check is two commands and costs nothing:
    git merge-base --is-ancestor <sha> HEAD || echo "NOT PRESENT — go get it"
    git log --oneline main..<sha>          # usually a handful of commits
Then **merge that sha directly, not `merger`.** Here `main..b1225666` was three commits over
two files; merging `merger` wholesale would have dragged an entire release's payload onto a
single-leaf branch for no reason, and made the merge worker's job harder rather than easier.
Say in the report that your branch carries those commits, so the merger knows the duplication
is deliberate.
Corollary for whoever WRITES such a prompt: a sha is not a location. Write
"`b1225666`, on `merger`, not yet on `main` — merge it first", because the reader's tree is
`main` by construction.
## `∉ (small ideal)` IS NOT `∉ 𝔪` — the commonest direction error in a duality argument
(2026-07-31, found while proving `exists_tateWeilRawFamily_of_qAdicWeilSystem`.) A leaf's
prescribed route ended "the contrapositive turns a nonzero pairing value into
`C ∉ span {(q:O)}^N`, and then locality of `O` plus `hker` upgrade that to `IsUnit`". The
first half is right; the second is not, and the error is worth naming because it reads as a
routine last step.
In a local ring, `IsUnit c` is `c ∉ 𝔪` — non-membership in the BIGGEST proper ideal.
A duality hypothesis of the shape `c ∈ J ⟹ (θ-estimate)` contrapositives to `c ∉ J`, and `J`
is always SMALL (here `span {(q:O)}^N ⊆ span {j π}^{eN} ⊆ 𝔪`). Non-membership in a subideal
is *weaker* than non-membership in the whole maximal ideal, so the implication runs backwards.
Getting `IsUnit` needs an UPPER bound on `θ` over `𝔪` itself, which is a different and usually
missing clause — in this development the module's own docstring already recorded that no such
estimate exists at exponents that are not multiples of the ramification index.
Test before believing any "and therefore it is a unit": write down which ideal the argument
actually excludes, and check it is `𝔪` and not something inside it. Eight formal clauses of
that leaf went through exactly as prescribed; this one line was the whole of what was left.
## A PLAIN `import` HIDES EVERYTHING IN THAT FILE FROM EVERY DOWNSTREAM MODULE
(2026-07-31, flt-lean-393.) `Fermat/FLT/ModularCurve/X0.lean` reaches
`Fermat/FLT/ModularCurve/EllipticScheme.lean` through a **plain `import`, not a
`public import`** (line 369, and it is the only such line in that header). Under
Lean's module system that means nothing downstream of `X0.lean` — `MazurTorsion.lean`
included, 40 000 lines of it — can name a single declaration of `EllipticScheme.lean`.
`relPointPost`, `relPointPost_add` (rigidity), `hom_specRat_eq_of_range_eq`,
`exists_isIso_of_affineChart`, `isIso_of_isDominant_of_inverse`,
`isDominant_of_range_eq_compl`: all PROVEN, all invisible.
This defeats the standing "grep the tree before proving anything from scratch" rule
in a way the rule does not warn about. A `grep` finds the theorem, `git log` shows it
green, its docstring says PROVEN — and `#check` says unknown identifier. **So the
availability test is `lake env lean` on a one-line `#check`, not a grep.** A scratch
module importing the target file costs seven seconds; run it before planning around
a reuse.
Two consequences that both bit in one task:
* **The wrapper is invisible, the theorem it wraps often is not.** The valuative
  criterion `AlgebraicGeometry.exists_unique_extension_of_isSmoothProperCurve` lives
  in `Fermat/FLT/Mathlib/`, is reachable, and is stated over an ARBITRARY FIELD;
  only `EllipticScheme.lean`'s ℚ-specialisation of it is hidden. Reproving the
  ~40 lines of wrapper over a general field was the whole cost.
* **Look for a second copy at the RIGHT generality before duplicating.** X0.lean's
  own `isAdditiveOn_of_post_zero` is relative rigidity over an ARBITRARY base — the
  general form of `EllipticScheme.relPointPost_add`, visible, and better. The first
  plan copied 120 lines of the hidden one; the reachable one made that unnecessary.
## PORTING A ℚ PROOF TO ℚ̄: THE STEPS THAT BREAK ARE THE ONES ABOUT ℚ's RIGIDITY
(2026-07-31, flt-lean-393.) `EllipticScheme.hom_specRat_eq_of_range_eq` — "a
`ℚ`-point of a scheme is determined by its image" — is the load-bearing step of the
ℚ-side Weierstrass bridge, and it rests on `Subsingleton (k →+* ℚ)`: a field has AT
MOST ONE ring map to ℚ, because ℚ is the prime field. **`Subsingleton (k →+* ℚ̄)` is
false** — `AlgebraicClosure ℚ` has an enormous automorphism group — so the ℚ proof
does not transfer, and the ℚ̄ statement needs a residue-field argument (it is
recoverable for SECTIONS: `K → κ(x) → K` being the identity forces `κ(x) → K` to be
the inverse of a bijection, hence unique).
The general shape: when a ℚ-argument is transported to `ℚ̄`, the steps that will
break are exactly those using "ℚ has no automorphisms / is the prime field / is
subsingleton as a target of ring maps". Everything topological or scheme-theoretic
(`Spec K` is a one-point space, connectedness, dominance, the valuative criterion)
transfers verbatim with `ℚ` replaced by any field.
**And the repair may be to delete the step rather than port it.** The zero section
was being matched by a range chase, which is what needed the point-determined-by-image
lemma. There are two ways out, and both were built independently the same day: port
the lemma (`section_eq_of_range_eq_algClos`, the residue-field argument — a `K`-point
that is a SECTION has `K → κ(x) → K` equal to the identity, which forces `κ(x) → K`
to be the inverse of a bijection, hence unique), or **avoid needing it**: for an
abelian scheme presented by its functor of points, TRANSLATION by a section costs no
geometry at all — add the pullback of the section to the UNIVERSAL relative point
`⟨𝟙 A, _⟩ : RelPoint f f`, and the group axioms plus `pre_add` alone show it is an
isomorphism with inverse the translation by the negative. Correcting an arbitrary
isomorphism by the translation that undoes `u(O₁)` matches the origins BY
CONSTRUCTION, and the resulting statement — *every* isomorphism over the base yields
an `IsEllipticIsoOf`, with no zero-section hypothesis — is both stronger and shorter.
The ported-lemma route is the one that landed (`flt-lean-182`, release 26); the
translation route is recorded here because it generalises to any abelian scheme over
any base and needs no residue fields.
**Same trick, same file, one leaf earlier: a functor-of-points endomorphism IS a
morphism of schemes.** `IsCMByRamifiedMaximalOrder.phi` is a family of maps on
`RelPoint d.f g` for every test scheme, and evaluating it at `⟨𝟙 d.E, _⟩` gives a
single `Φ : d.E ⟶ d.E`, with `phi_pre` proving every value is postcomposition with
it (six lines). That is the step that makes such a leaf attackable at all: an
`IsIsogeny` certificate is polynomials in the coordinates, and no polynomial can be
extracted from a family of abstract group maps. **Whenever a leaf's hypothesis is a
`∀ T'`-quantified functorial bundle, evaluate at the universal point FIRST and
restate it with the morphism.**
## A CITATION LEAF IS NOT ATOMIC UNTIL YOU CHECK WHAT ITS NEIGHBOURS ALREADY PROVE
(2026-07-31, `exists_isFineGamma1Moduli`.) A leaf whose docstring is one citation
— "Katz–Mazur 4.7.1", "Deligne–Rapoport IV.2" — reads as irreducible, and the
reflex is to price the whole classical theorem. Ask instead **which parts of that
theorem the tree has already proven for a neighbouring leaf**, because a citation
is usually a conjunction and the sibling constructions have often discharged most
of it. Here the arithmetic half (4.7.0 + 2.7.4 + 8.1.1, every hypothesis on `N`
and `ℓ`) was PROVEN in `exists_gamma1AffineModel`, and the uniqueness half fell
out of a field the atlas structure already carried. What remained was one
base-generic, arithmetic-free leaf: the frontier count did not move, but the leaf
lost three hypotheses and became usable over `ℚ` as well.
Two rules came out of it, and both generalise past this file:
* **A `∀` over a structure is safe exactly when it constrains a field the
  structure PINS.** `X1.lean` has a refuted `∀ A : Gamma1Atlas` leaf and a sound
  one. The difference is not the quantifier: `A.M` (the rigidified scheme) varies
  with the auxiliary level and a `∀` about it must hold for all of them at once,
  while `(A.Y, A.classify)` is INITIAL among classifying cocones, so a statement
  about it has the same truth value at every atlas. Before writing or auditing a
  `∀ <structure>`, ask which field the conclusion mentions and whether the
  structure's own universal property determines it.
* **A uniqueness clause with no "over the base" clause is FALSE over any base
  with a nontrivial automorphism.** `IsFineGamma1Moduli.eq_of_isBaseChange`
  carried the note "uniqueness is a statement about `M` alone"; over
  `K = 𝔽_{ℓ²}` with `σ` the Frobenius, `m` and `Spec σ ≫ m` classify the same
  datum and differ. Rigidity pins the classifying morphism only *among morphisms
  over the base*. Such a notion is correct only where `Hom(T, S)` is a
  subsingleton — i.e. at `SpecQ` (`subsingleton_hom_specQ`) and `SpecF ℓ`
  (`subsingleton_hom_specF`), the two bases this development uses — so when you
  move one off its base, carry `∀ Z, Subsingleton (Z ⟶ S)` as a real hypothesis.
Consequence for the second rule that is easy to miss: a hypothesis can be
load-bearing **twice**. `ℓ.Prime` is cited for "`ZMod ℓ` is a field"; it is also
the reason the uniqueness clause is true at all, and that second role is
invisible until the statement is generalised.
## SEVENTH invisibility class: A CLEAN MERGE THAT DOES NOT COMPILE — the interface split

(2026-07-30, release 22, three instances in one batch.) The six classes above are all about
*not seeing work*. This one is about *seeing a merge succeed*. Every check this file prescribes
for a merge — no conflict markers, `git diff --stat HEAD^1 HEAD` non-empty, the sorry counts,
the `declaration uses 'sorry'` warning set — passed on all three, and the tree did not build.

The shape is always the same. **An interface change and its call sites are ONE edit, and a merge
can split them across the conflict boundary.** The half that conflicts gets resolved; the half
that does not conflict lands unexamined; and the two halves now contradict each other.

- `RelativePicard.lean`: `flt-lean-133` CLOSED `nonempty_modTensor_assocPic` by hoisting, deleting
  the leaf and re-pointing the call sites *its base had*. `main` had gained more call sites since.
  Both edits merged without conflict; six calls to a deleted declaration survived.
- `ArtinConductor.lean`: `flt-lean-197` split break POSITIVITY into its own clause, so one theorem
  returns `⟨pos, counting⟩` and another takes two binders. The SIGNATURES were the non-conflicting
  half; the CALL SITES were the conflicted half, resolved to `ours`, still passing one conjunction.
- `Patching.lean`/`Interface.lean`: two owners threaded DIFFERENT hypotheses (`hp5`, `hgen`) through
  the same six-theorem positional argument chain. Signature edits merged cleanly, so the callees
  bind both; each side's call line passes only its own. **Neither `ours` nor `theirs` compiles** —
  and the conflict looks like a trivial whitespace disagreement. Positional argument lists are
  what make this a merge hazard at all.

**Corollary, and it inverts the obvious rule: resolving every conflict to `ours` is NOT a safe way
to decline a payload.** Twice this release it left the tree broken, because the branch's chain
straddled the boundary:
`flt-lean-366`'s three new leaves landed non-conflictingly while the two proven helpers they call
sat in the dropped half (seven live references to nothing); `flt-lean-123`'s hoist inserted 5164
lines into `X0.lean` while `MazurTorsion.lean` kept its copy (duplicate declarations). **To decline
a payload, `git checkout HEAD -- <the files>`** and let the diff against the first parent be empty
on purpose. Say so in the commit message, because an empty payload otherwise reads as the
dropped-merge bug of class six.

**Two checks catch this class before the build, and both cost seconds.**

1. *Duplicate declaration names, WITHIN a file and ACROSS files*, diffed against the previous
   release so the tree's many legitimate same-last-component names in different namespaces do not
   drown the new ones. Two real errors this release: `Gamma0AtlasOver.bcUniversal_transport`
   declared twice in `X0.lean` by two branches whose regions were too far apart to conflict, and
   `Fermat.isInvertibleSheaf_modPullback` declared in two modules one of which imports the other.
   A per-file scan cannot see the second.
2. *Per merge: names declared on the BRANCH but absent from the resolved file, grepped
   (comments stripped) against the resolved file.* This is what found `flt-lean-366`'s breakage
   before a build ran.
3. *A binder RENAMED to `_x` in a SIGNATURE while the body still says `x`.* This is the
   cheapest-to-detect shape of the split and it was live on `merger` at `f6755e85`
   (2026-07-31): `ProperPushforward.lean`'s `eq_span_one_sup_smul_top_appTop_of_isIso_appTop_fiber`
   read `(_hm : m.IsMaximal)` while its body still called
   `exists_point_ker_Γevaluation_eq_of_isMaximal S m hm` — `unknown identifier 'hm'`, i.e. the
   whole module red. It arises when a branch reproves a theorem from a new upstream fact (here
   a hoisted `surjective_appTop_of_isIso_appTop_fiber`), so the hypothesis goes unused and gets
   underscored; the signature edit merges cleanly and the body replacement lands in the
   conflicted half. Grep the resolved file for a signature binder `_foo` whose declaration body
   mentions `foo` — seconds, no build, and it catches the whole class.

And the standing one, which is what caught the rest: **the release build is not optional and its
first failure is not its last.** Fix, rebuild, repeat — FOUR rounds this release, and the reason is
structural rather than bad luck. **The errors are serialised behind each other by the import
graph**, so round *n* only reveals what round *n−1*'s failure was hiding: one interface change
(`IsSwanExponentAt` gaining a third clause) broke a consumer in its own module, found in round 1,
and a second consumer 79 000 lines away in another module from another branch, found only in round
4 after twenty minutes of elaboration. Budget three rounds minimum, and schedule nothing behind the
first green one.

## A DOCSTRING'S "WHAT PROVING IT NEEDS" IS ABOUT A CONSTRUCTION, NOT ABOUT THE STATEMENT

(2026-07-31, `flt-lean-214`.) `exists_involutionSignSplitting` in `X0.lean` had stood
open since 2026-07-28 behind this estimate, written by its author and never re-derived:

> **What proving it needs**: abelian varieties over a field — absent from mathlib
> entirely — together with the quotient of an abelian scheme by an abelian subscheme
> as a faithfully flat map, and fppf descent to see that such a quotient is an
> epimorphism of schemes.

Every clause is a true statement about `P^± := A / B^∓`, the CLASSICAL construction.
None of it was needed. `IsInvolutionSignSplitting` never asks for a quotient: it asks
for a surjective flat epimorphism `p b` on which `ι` acts by `±1`, with finite joint
kernel and a descent for commuting endomorphisms. **`Im(1 ± ι)` is one**, it is
isogenous to the quotient, and nothing in the structure distinguishes them. The leaf
closed over machinery that was already in the file — the image theorem, `flat_`/
`epi_of_surjective_of_isAdditiveOn`, `finite_torsion_geomPt_of_abelianScheme`,
rigidity, and the `EffectiveEpi` that `epi_of_surjective_of_isAdditiveOn` discards.

This is the SECOND time the same substitution has paid in this one file — the first
is recorded on `exists_abelianImage_of_isAdditiveOn` as "the CHEAP replacement for
Poincaré reducibility that the image-not-kernel cut buys". So it is a pattern, not a
coincidence: **over a field, an IMAGE is cheap (scheme-theoretic image + Cartier gives
smoothness) and a QUOTIENT is expensive (fppf descent, the subscheme's own geometry),
and the two are isogenous.** Whenever a leaf's stated obstruction is a quotient, ask
first whether an image satisfies the conclusion.

The general rule, and it applies to every leaf in this development:

- **An absence table is evidence about the ROUTE its author searched.** It is not a
  theorem about the statement, and it does not expire loudly — it just sits there
  looking authoritative while the file grows the machinery that makes it false.
- Before accepting "this needs a theory we do not have", **read the CONCLUSION alone,
  field by field, and ask what each field actually demands.** Here the answer was
  visible in the structure's own docstring: it already said `ker_finite` "is the
  `2`-torsion argument", which is true of the image construction and says nothing
  about quotients.
- The cost of the check is one careful read. The cost of not making it was three days
  of a node the fleet believed was blocked on a missing subtree.

Corollary for anyone WRITING a leaf: say "the construction I have in mind needs X",
not "proving it needs X". The two read identically to the next agent and only one of
them is true.

## A DOCSTRING THAT ARGUES TWO LEAVES ARE EQUIVALENT IS A LEAF-MERGE WAITING TO BE PERFORMED

(2026-07-31, `flt-lean-217`, and it closed two leaves for 30 lines of Lean.)

`X1.lean` carried two open citation leaves, `exists_gamma1RigidifiedModuliScheme`
(`∃ R`) and `isAffine_of_gamma1RigidifiedModuliScheme` (`∀ R, IsAffine R.M`), split
out of one node the day before. The second one's docstring contained this, under the
heading "Why the `∀` is legitimate":

> `universal` is a **fine** moduli property, so any two inhabitants are related by a
> unique isomorphism … `IsAffine` is invariant under isomorphism of schemes. So
> "the Katz–Mazur `𝔐(𝒫, 𝒮)` is affine" and "every inhabitant … has affine `M`" are
> the same statement.

That paragraph was written to *justify the quantifier* — and it is simultaneously a
complete proof that the two leaves are ONE leaf. Nobody read it as one, because it
sits under a heading about faithfulness. Writing it in Lean
(`nonempty_iso_gamma1RigidifiedModuliScheme`: feed each scheme's universal family to
the other's `universal`, then kill both round trips with `universal`'s uniqueness
clause applied to the scheme's OWN universal family) is 30 lines over
`IsBaseChangeOfGamma1.refl`/`.comp`, and it collapses `∃ R` + `∀ R, IsAffine R.M`
into the single `∃ R, IsAffine R.M`. Both names and signatures survive as theorems,
so no consumer changed.

**So: prose of the form "these are the same statement", "this follows from that by
rigidity/uniqueness/invariance", "legitimate as a `∀` because …" is a proof sketch,
not a caveat.** If it is right, one of the two leaves is free. Grep the file's
faithfulness sections for it before dispatching anyone at either leaf.

The structural version, worth checking whenever a structure has a fine-moduli or
universal-property field: **a `∃!`-valued field makes the structure a contractible
groupoid, so `∀ R, P R.M` and `∃ R, P R.M` coincide for every isomorphism-invariant
`P`.** The same merge is available verbatim on the `Γ₀` side of this development
(`X0.lean`'s `exists_rigidifiedModuliScheme` / `isAffine_of_rigidifiedModuliScheme`
over `RigidifiedModuliScheme`, whose `universal` is the same shape and carries no
`m ≫ strM = g` conjunct, so the transcription should be shorter). It was not done
from `flt-lean-217` because that file is owned separately.

Related, and the reason the 2026-07-30 split happened at all: the split's own
docstring recorded the trade honestly as "`1 -> 2` open leaves, not `1 -> 1`". A
split that ADMITS it raises the count is exactly the place to ask whether the second
residue is real, because a leaf that a sibling's docstring can already derive is not
a citation — it is unwritten Lean.

## WRITE INTO A REGION THAT IS BYTE-IDENTICAL ON `main` AND `merger`

(2026-07-31.) The class-7 section above says what an interface split costs. This is the
cheap way to avoid causing one, and it takes two `md5sum`s.

When your target file is one `merger` has heavily rewritten — `HyperellipticJacobian.lean`
was `+1054/-41` against `main` on the day this was written — where you PUT a new declaration
decides whether the merge conflicts, independently of what the declaration says. The check:

    git show merger:<path> > /tmp/m.lean
    sed -n '<merger-lo>,<merger-hi>p' /tmp/m.lean | md5sum
    sed -n '<main-lo>,<main-hi>p'   <path>       | md5sum   # same hash => safe region

Pick a block whose two hashes agree — typically an existing `namespace … end` that neither
side touched — and put the new lemmas and leaves THERE, even if the file's convention would
put them at top level next to the leaf they serve. Then the only edit left in the contested
neighbourhood is the target's own proof body, whose surrounding docstring is usually more
than three lines of unchanged context on both sides, so git never sees a conflict at all.

Concretely, `geomPic_bc_injective` sits ~15 lines below `exists_geomPic`, whose body `merger`
had replaced with a 400-line construction; putting the two new leaves inside `namespace
GeomPic` (identical on both sides) instead of immediately before the theorem turned a certain
conflict into none.

The converse is the warning: **inserting right after a `end <Namespace>` line is the WORST
place**, because that is exactly where another branch's new section will also have been
inserted, and both hunks then anchor on the same context line.

## A RECORDED ROUTE CAN FAIL ON *UNIVERSES*, AND NO AUDIT IN THIS FILE LOOKS THERE

(2026-07-31, `flt-lean-244`.) Every "route audit" discipline above reasons about
mathematics, instances, definitional equality and staleness. A route can be
mathematically correct, instance-correct, current — and still name a term that does
not elaborate, because the two objects live in **independent universes**. That failure
is invisible to a reader, invisible to `git log`, invisible to the frontier scans, and
it does not look like a universe problem when it bites: `@h k` simply reports a type
mismatch between `Type uK` and `Type uR`.

Two instances in one node, both recorded as settled by careful previous owners:

- `isAuxWeaklyUniversalOnFrames_of_isStrictlyUniversalOnFramesFor` prescribed
  "recover `ρbar`'s determinant by instantiating the levelwise pushforward clause at
  `A := k`". That clause quantifies over `A : Type uR`; `k : Type uK`. **It is a hard
  universe error.** The repair took the residue quotient `R ⧸ ker πuniv` instead —
  same mathematics, and it lives in `Type uR` *by construction*, which is the general
  shape of the escape: when you need an object in the coefficient universe, look for a
  QUOTIENT OF SOMETHING ALREADY THERE rather than for the thing itself.
- Its sibling `exists_levelIdealSystem_aux_of_clauses` asks for `P : Type uR`, and the
  base-level construction it is told to transcribe verbatim builds `P` out of one
  polynomial generator per element of `k`, hence in `Type uK`. **`ULift` does not
  repair this** — `ULift.{uR} X` for `X : Type uK` lands in `Type (max uK uR)`, not in
  `Type uR`. The escape again came from a hypothesis that already carried a `Type uR`
  object surjecting onto `k` (a bundled deformation datum's ring), so `k` has a small
  model in the right universe and the generators can be re-indexed by it.

Two things follow, and the second is the useful one.

**A universe generalization that "fixes the universes" may fix only ONE axis.**
`flt-lean-39` freed the COEFFICIENT universe of this chain and its audit says so
accurately; the RESIDUAL-FIELD universe was never mentioned, and that is the axis that
actually blocked the transcription. When a note says universes were dealt with, ask
*which* universe.

**Check universes FIRST when a route is handed to you, before reading the
mathematics.** It costs one `#check`-shaped elaboration of the route's key application
and it is the cheapest disproof available: a route that fails here fails before any of
its mathematics matters, and — unlike a stale claim — no amount of merging `main`,
rebuilding `.lake` or re-reading the literature will ever make it true.

## A LEAF'S "THE CHECK THAT REFUTES THE ROUTE" IS AN UNPAID DEBT — RUN IT, IT COSTS MINUTES

(2026-07-31.) Leaf docstrings here carry two refuting checks: one for the STATEMENT and one for
the ROUTE. The statement's check gets run — that discipline is well established. **The route's
check is written down and then almost never run**, because it looks like the author's problem
rather than the dispatcher's, and because a route recommendation reads with the same authority as
the falsity audit beside it. It is not the same thing: the audit was verified, the route was
guessed.

`ajMinusTorsion_eq_zero_x0OneTwentyFive` recommended, in bold, "`ℓ = 3` is the cheapest" — reduce
mod `3`, use `neronReduction_injective`, conclude from `[P̄] = [w̄ P̄]` in `J_0(125)(𝔽_3)`. **That
equality is false at `ℓ = 3`**, and finding out cost about ten minutes of PARI plus one moduli
count. `X_0(125)(𝔽_3)` has exactly four points — two rational cusps and two non-cuspidal ones —
and `w_125` SWAPS the non-cuspidal pair, so the class the route wants to be zero is not. Worse, it
fails structurally rather than at `3`: the naive one-prime test needs EVERY non-cuspidal
`𝔽_ℓ`-point to be `w`-fixed, hence to have CM by `ℚ(√−5)`, and nothing arranges that at any `ℓ`.

The leaf itself is fine — still true, vacuously. Only the route was wrong, and a route is exactly
what a successor spends its cycle on.

**Two things made this cheap, and both generalise.**

*Cross-check the count two ways that share no input.* `#X_0(125)(𝔽_3) = 4` came out of
Eichler–Shimura (`tr T_3 = 0`, so `3 + 1 − 0`) and, independently, out of counting moduli (two
`𝔽_3`-rational cusps of the ten, plus the two Frobenius eigen-lines of the single ordinary `j`
admitting a cyclic `125`-subgroup). Agreement between two such counts is what let me trust the
finer structural claim — which point is fixed by `w` — that neither count alone establishes.

*A CM/discriminant argument settles "is this point fixed" without a model of the curve.* The fixed
points of `w_N` are CM points of discriminant `−4N`; reduce that order at `ℓ` and compare with the
`a² − 4ℓ` available to `E/𝔽_ℓ`. Here `ℚ(√−5)` versus `{ℚ(√−2), ℚ(√−11)}` — disjoint, so no fixed
point is `𝔽_3`-rational at all. That is a two-line check and it answers a question that otherwise
looks like it needs divisor arithmetic on a genus-`8` curve.

**So: before dispatching at a leaf whose docstring names a route with a concrete parameter — a
prime, a level, a truncation bound — run the route's own refuting check first.** A negative comes
back as a corrected docstring and a correctly-scoped successor; the alternative is an agent that
discovers it after building the machinery. And when you withdraw a recommendation, DELETE the line
rather than appending a caveat under it: the next reader greps for the prime, not for the
paragraph.

## A COUNTEREXAMPLE CAN BE RIGHT AND ITS READING WRONG — check which hypothesis it actually kills

(2026-07-31, `RelativePicard.lean`.) `surj_of_isRelPicOverAffines`'s audit named TWO load-bearing
hypotheses, a section `_o` and `f_*𝒪 = 𝒪` (`_hpush`), and backed both with one counterexample:
"for `X = S ⊔ S` — no section, and `f_*𝒪 = 𝒪 × 𝒪` — the sequence
`0 → Pic T → Pic X_T → P(T) → Br T` breaks". The example is correct and refutes the leaf. But
**`S ⊔ S ⟶ S` has a section** — either inclusion — so it says nothing whatever about `_o`, and
writing the proof showed `_o` is not needed at all: the local twists `Nᵢ` are canonically
`(f_*M)|_{Uᵢ}`, restrictions of ONE sheaf, so there is no cocycle to obstruct and no Brauer class
for a section to kill. `_hpush` alone does the work.

The failure mode is specific and worth naming, because it is invisible to every check this file
prescribes. An audit exhibits ONE object violating SEVERAL hypotheses at once and then reads it as
evidence for each of them separately. Nothing catches that: the leaf is genuinely false, the
witness is genuinely a witness, and a reviewer who checks "does this refute the statement?" gets
yes. **A counterexample licenses exactly one claim — that the statement is false as stated. To
attribute the failure to a particular hypothesis you need a witness satisfying all the OTHERS**,
and the discipline is to say out loud, per hypothesis, which one that is.

Two practical corollaries:

* **the cheapest place to find this is the proof.** Prove the parent over the leaf, then read off
  which hypotheses the route actually spent. Here the parent turned out to spend NONE of the five
  itself — all were forwarded — which is what made the over-attribution visible;
* **a hypothesis you cannot justify is still worth KEEPING in a new leaf's signature** when the
  caller already has it: it costs the prover nothing and cannot make the leaf false. Say in the
  docstring that it is retained defensively rather than needed. Deleting it is the move that can
  go wrong, and it buys almost nothing.

## `lake` IS NOT ON PATH in a fresh agent shell, even on the owning host

Same day, one wasted build round. `lake build …` returns `lake: command not found`, `EXIT=127` —
the harness's Bash shell does not pick up elan's shim directory. Prefix every build with

    export PATH="$HOME/.elan/bin:$PATH"

`EXIT=127` with an otherwise empty log is this, not a broken worktree. Note it looks nothing like
the memory-filed ssh trap (`flt-ssh-build-needs-cd-and-elan-path`), where a missing `cd` makes
`elan` DOWNLOAD a toolchain and the build merely appears slow; this one fails instantly.

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

## THE TOKEN IN YOUR PROMPT GOES STALE ON RESUME — read the job file before writing the sentinel

(2026-07-31, `flt-lean-175`, caught by accident.) A prover agent's ONLY output channel is
`~/.flt-loop/jobs/<name>.sentinel`, and `flt-loop.py` accepts it only if its `token` equals the
token in `jobs/<name>.json` **at harvest time**:

    if d.get("token") == j["token"]:   j["sentinel"] = d      # else: no sentinel at all

The comment beside it says why — *"Resume mints a new token precisely so the old marker goes
inert."* So when a session is RESUMED (the record grows `retries`, `resume: true`, a fresh
`spawned_at`, and `<name>.started` is rewritten with the new token), the token printed in the
prompt text you are still reading belongs to the PREVIOUS incarnation. A sentinel copying it
"verbatim", exactly as the prompt instructs, is discarded whole: the loop then sees
`started ∧ ¬alive ∧ ¬sentinel`, concludes the agent died, and dispatches a replacement that
starts from nothing. **The commits survive on the branch; the `queue` and `to_merger` do not.**

This is invisible from inside the agent. Nothing announces the respawn, the prompt is not
re-read, and the sentinel write succeeds — the file is there, correctly formed, and simply never
matches. It was found here only because a `ls` of the jobs directory happened to show a
`.started` file newer than the sentinel.

So, as the last step before writing the sentinel — always, not only when you suspect a resume:

    python3 -c "import json;print(json.load(open('$HOME/.flt-loop/jobs/<name>.json'))['token'])"

and use THAT. It agrees with the prompt on a first run and disagrees on every resumed one. Same
check applies to a merge worker or medic, whose sentinels carry `panic` / `go` fields that gate
the whole loop.

Corollary for whoever maintains the loop: an agent cannot be asked to copy a value that the loop
may rotate underneath it. Either the prompt should be rewritten on resume (it is — `.prompt` is
regenerated, but a running session never re-reads it), or the sentinel should be matched on the
job's identity rather than on a value the agent must echo.

## A DOCSTRING'S PRESCRIBED ROUTE CAN NAME A STEP THAT THE RIGHT PRESENTATION DELETES

(2026-07-31, `ker_multIdeal_le_span_idealTensorComparison`, [Stacks 10.99.12/13].) The leaf's
docstring named the dimension shift `ker(↥I ⊗_C D → D) ≅ (K ∩ IF)/IK` as the thing to state
first, calling it "the real cost of this leaf" — and it would have been, because it has to be
applied over two rings and the two copies then have to be compared. It was never needed. On
the **tautological** free presentation `F = (D →₀ C)` — the free module on the underlying SET
— the shift degenerates:

* `multIdeal I F` is INJECTIVE (`Finsupp` is free, hence flat), so the tensors themselves are
  a faithful representation and conclusions transport along it; and
* its image is cut out COEFFICIENTWISE, so `K ∩ IF` needs no separate description.

No quotient is ever formed and no comparison is ever checked. ~300 lines instead of a module.

**The generalisable move: before building the machine a route asks for, try the most concrete
model of the object the route quantifies over.** A route is written by someone reasoning
abstractly ("take a free presentation"); an abstract presentation forces you to construct
every identification by hand, while a *specific* one often makes several of them `rfl` or
coefficientwise. Same reason `ker πj = span_{Cj}(ι '' ker π)` was cheaper proved from the
universal property of `⊗` than through mathlib's `lTensor_exact`: the latter first demands
identifying `(D →₀ Cj)` with `Cj ⊗[Ci] (D →₀ Ci)`, and that transport costs more than the
whole proof.

Corollary for cutting: a leaf's stated route is a *hypothesis about cost*, not a
specification. Re-cost it against a concrete model before you accept its first bullet.

**And an unknown-identifier error on a mathlib name that visibly exists in the source is a
RENAME, not a missing import.** `Basis` is `Module.Basis` at this pin (`Basis.ofVectorSpace`
→ `Module.Basis.ofVectorSpace`), and the error was `unknown namespace 'Basis'` even with the
right file imported. Check `grep -n "^namespace" <the mathlib file>` before hunting imports or
suspecting a partial `.lake`. (A genuinely missing olean gives `object file ... does not
exist`, which looks nothing like this.)

## A LEAF THAT INVITES A CUT AND DECLINES IT "BECAUSE NOTHING WOULD CONSUME IT" — the consumer is the leaf

(2026-07-31, `hasCubeIso_of_symm_of_normalized`.) Its docstring said, correctly, "a prover who
wants the general Corollary 2 as a separate leaf should cut it … this statement is three formal
steps below it", and then declined to, "only because this project forbids free-floating
declarations and nothing would yet consume it." That reason is wrong by one step: **the leaf
itself is the consumer.** Cut the general statement, prove the leaf over it, and nothing floats.
It was three formal steps, exactly as advertised — and two survey agents had already read that
paragraph and moved on, because "this is a theory build" is true of the general form too and so
reads as a reason to do nothing.

The trade is worth taking even though the leaf COUNT does not move (one out, one in):

- the open statement shed `[Field K]` and two of its three hypotheses, which were being
  discharged in the derivation all along;
- it is now the statement the literature proves, so a future prover can follow a book instead
  of reverse-engineering a project-specific corollary;
- it is stated for arbitrary points over an arbitrary base, so its OTHER classical consequences
  are reachable from the same leaf rather than needing their own cuts later.

**And when you hoist a field-based statement to an arbitrary base, KEEP THE CONSTANT TERM the
reference drops.** Mumford's cube identity omits `0^* L` because over a field `Pic(Spec k) = 0`
makes it free. Transcribing it verbatim over a general base silently asserts `e^* L ≅ 𝒪` — put
`x = y = z = 0` and every one of the seven factors collapses to `0^* L`, so the identity reads
`(0^*L)^{⊗4} ≅ (0^*L)^{⊗3}`. Restoring the term makes that case a tautology, which is what a
correct third-difference identity must do. **The general test: specialise your statement to the
degenerate point where a reference's ambient hypothesis was doing the work, and check you get a
tautology and not a hidden assertion.**

## A HOIST IS THE HIGHEST-CONFLICT EDIT THERE IS — give the merger a RECEIPT that it is a pure move
(2026-07-31, `flt-lean-76`, closing `birationalOver_affineLine_of_not_injective_aj`.) Some
leaves are not mathematics at all: the theorem already exists in the same file, declared
BELOW its consumer, so the derivation cannot be written. The repair is a relocation, and a
230-line relocation in a file with four other concurrent editors is exactly the edit the
class-7 section above says a merge will split.
Two things make it safe, and both cost seconds.
**1. Prove the move is pure, mechanically, and quote it in the commit message.** A relocation
diff is 50% `-` and 50% `+` and reads like a rewrite; nobody can see by eye that nothing
inside the moved block was also edited. The sorted line multiset can:
    git show HEAD:<path> | sort > /tmp/old.sorted
    sort <path>          > /tmp/new.sorted
    diff /tmp/old.sorted /tmp/new.sorted     # empty => pure move
Empty, with an unchanged line count, means every line still exists exactly once and only the
ORDER changed. **Put the move in its OWN commit**, separate from the proof that consumes it,
with the old and new line ranges and the parent sha in the message — then a conflict is
resolved by RE-APPLYING the move to the merged text, which is the only resolution that cannot
half-land.
**2. Audit the direction words, because the compiler is silent about all of them.** Docstrings
in this development are dense with "`foo` above" / "`bar` below", and a hoist falsifies some of
them in both the moved text and the text that cites it. Grep every mention of each moved name
and check each direction; here exactly two of about a dozen went stale. Also choose the ORDER
of the moved blocks against their own prose — placing `relPicEquiv_sectionIdeal_of_aj_eq`
before `birationalOver_affineLine_of_relPicEquiv_sectionIdeal` kept its self-description
("the shared first half of both degree-`1` Riemann–Roch leaves below") true for free.
And check the close the way CLAUDE.md checks a release, not by reading the diff: X0's
`declaration uses 'sorry'` warnings went 105 → 104 **and** its comment-stripped `sorry` TOKEN
count went 105 → 104. Equal deltas is what rules out an anonymous inner sorry having been
swapped in for the named one.
## AN AUDIT'S DEAD AXES ARE EVIDENCE; ITS RECOMMENDED AXIS IS NOT
(2026-07-31, `exists_x0IntegralCompactifiedModel`.) An IRREDUCIBLE docstring listed four
searched-and-dead axes — all four verdicts correct, re-checked twice — and then named a
fifth as "the honest one a successor should take". Two reviews endorsed it. **It was the
worst option available.** It asked for the Deligne–Rapoport compactified moduli problem,
whose Néron-polygon clause is not definable at this pin; a leaf over a guessed version is
an EXISTENCE claim, hence FALSE if the clause is too strong (no DR object satisfies it) and
FALSE if it is too weak (the enlarged problem need not have a coarse space). The
free-floating rule also forbids defining the structure without wiring it into a leaf, so
"just write the definitions" is not a third option.
Verdict lines and recommendation lines sit in the same docstring in the same voice, and
only the first kind has been tested against anything. **A recommendation carries the
audit's authority without the audit's evidence.**
The axis that actually worked was not on the list, and it has a general shape worth
reaching for first: **which PROVEN pipeline in this repo already builds an object of this
shape over a DIFFERENT BASE?** Here `CurveCompactification.lean` carries Igusa's whole
construction — Nagata for an affine scheme, then relative normalisation — sorry-free over a
FIELD, and exactly two of its steps are field-specific (finiteness of normalisation wants a
Nagata ring, which `ℤ_(ℓ)` is; "normal + dimension one ⟹ smooth" is FALSE over a DVR and is
precisely Igusa's theorem). So the citation cut into a construction leaf plus two named
arithmetic leaves. An audit enumerates what its author searched for, and the search is
nearly always over the same base as the leaf.
Second, smaller, and from the same docstring: it asserted that "a smooth proper
geometrically connected curve over `ℚ` has infinitely many points" was NOT in the tree, and
carried an otherwise-useless `ℚ`-side hypothesis through three leaves for that reason
alone. It had been PROVEN four days earlier as `infinite_of_smoothOfRelativeDimension_one`.
**Grep the named missing lemma before pricing anything off its absence.**
## "A GAP IN OUR MATHLIB PIN" SCOPES THE SEARCH TO MATHLIB — AND THE ANSWER IS USUALLY IN `Fermat/`
(2026-07-31, `flt-lean-145`, and this is the **third** time the same node has been cut.)
A task prompt said: *"a search of the entire pin found NO implication `Smooth →
GeometricallyReduced` … confirm that before starting (it is a two-minute grep over
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`,
`Mathlib/RingTheory/Smooth/` and `Mathlib/AlgebraicGeometry/Geometrically/`)"*. Every word of
that was TRUE, the prescribed grep was run, and it confirmed the absence. The theorem was
nevertheless **already proven, sorry-free, on `main`, four days earlier**, in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean` — together with strictly
stronger statements the task did not ask for (smooth over a **domain**, not just a field). The
duplicate was built, verified green, axiom-audited clean, and thrown away.
**The trap is that the verification instruction is scoped, and the scope is wrong.** A
`Fermat/FLT/Mathlib/…` module is a mathlib-facing extension: it exists precisely *because* the
statement is absent from the pin, so "absent from the pin" is EVIDENCE THAT IT IS THERE, not
evidence that it is missing. Grepping mathlib harder can never find it, and every additional
mathlib grep raises confidence in a false conclusion. This is the same shape as the
self-certifying grep in the doctrine file, one level up: the *scope*, not the pattern, is what
is wrong.
**Two greps, both mandatory, before writing one line of a "missing from mathlib" module.**
They cost seconds and either one would have killed this task at minute two:
    grep -rn '<theConclusionYouIntendToProve>' --include=*.lean Fermat/
    grep -rln 'Fermat/FLT/Mathlib/' -e .            # i.e. read the mathlib-facing subtree's index
Grep for the **conclusion**, not for your intended declaration name — the existing copy is
called something else. Here `GeometricallyReduced` alone found it; so did
`isReduced_of_smooth_over_field`, which the existing file and the duplicate had picked
independently as the same name.
**The compiler says it too, but only at the consumer, and only after a full build.** The
duplicate compiled perfectly *in isolation*; the collision surfaced only as
    import … failed, environment already contains 'AlgebraicGeometry.isReduced_of_smooth_over_field'
    from Fermat.FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothReduced
after a 45-minute `lake build` of `X0.lean`. So a green `lake env lean` on your new module is
**no evidence at all** that it is not a duplicate — a duplicate module is green by
construction. Only wiring it into a consumer and building tests it, which is far too late.
**A duplicate is worse than no work: it is invisible to every frontier instrument** (see the
duplicate-cut section in the agent doctrine — the sorry count goes UP, not down), and it burns
a worker on a node that was closed. Note also that the prior deletion of this very node left a
note *in the file that used to carry it* —
`Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean` ends its account with *"Anyone
tempted to restate a smoothness-to-reducedness fact here should grep
`isReduced_of_smooth_over_field` first"* — which is exactly right and was invisible to anyone
not already reading that file. **A warning parked in the file where the duplicate used to live
does not reach the agent who is about to write the next one.** Warnings about duplication
belong HERE.
## RIVAL CUTS ARE OFTEN COMPLEMENTARY — check before choosing

(2026-07-30.) Nine of 57 branches in one batch were declined because another agent had cut the
same node differently. In one case that verdict would have been wrong. `flt-lean-134` proved
sub-leaf (γ) of `exists_relNormDivisorHom_ray_class` OUTRIGHT and left (α) over a fresh sorry;
`flt-lean-343` proved (α) OUTRIGHT and left (γ) over a fresh sorry. **Taking either branch whole
keeps an avoidable open node; taking one proof from each closes both.** It cost one careful read
of four hunks and netted zero new sorries where either alone netted one.

So when two branches cut one node, the question is not "which cut is better" but "did they close
different halves". Ask it first. The tie-breakers, in the order that has actually decided cases:

- **fewer OPEN leaves after**, not fewer leaves created — `flt-lean-44`'s divisor-set cut left ONE
  leaf and closed 23 of 32 cases outright, against a bound-cut that left TWO and closed none;
- **named beats anonymous** — a cut leaving 8 NAMED leaves beats one leaving 4 declarations with 4
  anonymous inner sorries inside them, even though the headline count is worse, because an inner
  sorry is ownerless by construction;
- **already integrated and consumed by neighbours**, which is the merge worker's only defensible
  ground when the mathematics is genuinely equivalent (two complete proofs of one theorem cannot
  both be carried — the name collides — so that is a CHOICE, not a merge, and it belongs to an
  author; record the rejected branch's sha in the merge commit).

**And a branch that was right when dispatched can be wrong when it lands.** `flt-lean-91` and
`flt-lean-195` independently generalised `EllipticScheme.lean`'s reverse Riemann-Roch chain from
`ℚ` to an arbitrary field, both truthfully reporting "NO LEAF WAS ADDED" — true at their base,
where the three leaves were open. They were PROVEN at `ℚ` by the time the branches merged, so the
same edit would have traded one closed leaf for three re-opened ones. Re-derive a branch's own
accounting against the release, never against its base; and when you decline for this reason, queue
the follow-up, because the work usually got CHEAPER (here: generalise the PROOFS, and both targets
close with no new sorry).

## THE COMMENT-NESTING SCAN MISSES HALF THE DAMAGE — ALSO COUNT STRAY `-/` AT DEPTH ZERO

(2026-07-31, `flt-lean-330`, measured on `merger`.) The release-24 note prescribes
"block-comment nesting depth returns to zero in every file". That check is real and it
found one file here. **It is blind to the mirror case, which was three times as common
in the same sweep**: the merge keeps ONE side's `-/` while the other side's paragraph
lands after it, so the depth balances perfectly and English is parsed as Lean.

Both shapes come out of one 20-line scanner if you also record every `-/` seen while
depth is ZERO. That list is the second half of the check and it is never legitimate:

    depth 0, see `/-`  -> depth 1        depth 0, see `--`  -> rest of line is a comment
    depth>0, see `/-`  -> depth+1        depth>0, see `-/`  -> depth-1
    depth 0, see `-/`  -> RECORD IT      end of file, depth /= 0 -> RECORD THE OPENER

On `merger` at `965d2b54` this found, in seconds and with no build: `EllipticScheme.lean`
(unterminated, at EOF, 2 400 lines from the damage), `X0.lean` (two strays), and two
orphaned docstring OPENERS whose bodies had been dropped — a third shape, which shows up
as `unexpected token '/--'; expected 'lemma'` and is caught by "a `/--` block whose close
is immediately followed by another `/--`".

**Why it is worth running before anything else you do in a worktree: ONE parse error
hides every later error in the file.** `X0.lean` reported `maximum number of errors
(100; from option maxErrors) reached` and stopped at line 76148. Fixing the two syntax
wounds — five minutes, no mathematics — took it to **22** real errors, all beyond that
cap and none of them previously visible to anybody. The frontier classes in this file are
about work you cannot SEE; this is the cheapest instance of the phenomenon and the only
one whose whole cost is a `python3 -` heredoc.

And the corollary that decides what to do next: **a parse error is a passer-by's to fix;
an interface reconciliation is not.** The 22 that remained in `X0.lean` are dropped
binders whose call sites still pass them, a pre-rename name still cited once, and four
duplicate declarations whose two copies carry *different docstrings* (`difflib` ratio
0.34 — same theorems, rival prose). Deleting either copy discards an author's writing, so
that choice belongs to an author. Fix the syntax, publish the list, stop.

## TWO `lake build`s IN ONE WORKTREE PRODUCE FAILURES THAT ARE NOT IN ANY SOURCE FILE

(Same run.) `setsid --fork`ing a build and then, minutes later, forking another in the
same worktree leaves both alive writing the same `.olean`s. The symptom is a build that
ends

    Some required targets logged failures:
    - Fermat.FLT.ModularCurve.HyperellipticJacobian
    - Fermat.FLT.Modularity.AmpleSheaf
    error: build failed

with **`grep -c "^error"` equal to zero** — no module-level error text anywhere in the
log — and naming modules you have just verified GREEN individually. It reads as lake
replaying a cached failure, and it is not; it is the other build.

The doctrine's kill rule already says scope by cwd. The prevention is upstream of that:
**before forking a build, check the worktree has none running.**

    for p in $(pgrep -x lean; pgrep -x lake); do
      case "$(readlink /proc/$p/cwd 2>/dev/null)" in /home/chend/flt-lean-N*) echo "$p";; esac
    done

A poll loop that gives up on a timeout does NOT stop the build it was watching, so every
"poll, time out, fork another" cycle adds one. Three were live here at once.

## AN AGENT WHOSE TARGETS ARE ALREADY PROVEN SHOULD STILL BUILD — that build IS the release build, run a day early

(2026-07-31, `flt-lean-105`.) All three assigned TARGETs were already proven on `merger`
— the release window, class five above — so the honest report was "nothing to do" and the
worktree could have been freed in ten minutes. Building the merged tree anyway found a
**duplicate-declaration blocker sitting on `merger` itself**: `Fermat.modPullbackSheafifyIso`
declared in BOTH `ModularCurve/RelativePicard.lean` (general, at a presheaf) and
`Modularity/AmpleSheaf.lean` (specialised, at a tensor of two sheaves), with the second file
`public import`ing the first. Both files were byte-identical to `merger`, so this was not
merge fallout in one worktree — it was the next release build, failing, found before the
release started.

It is the cross-FILE form of class 7 that the interface-split section already names, and it
is worth restating because of how it hides: the two declarations are 60 000 lines and one
file apart, neither branch conflicted with the other, `git diff` is clean, and the ONLY
symptom is `` `X` has already been declared `` followed by application-type mismatches at
the call sites — where the imported version silently wins and the arity is wrong. A per-file
duplicate scan cannot see it. The repair is a rename plus its call sites: the general
version keeps the short name, the specialisation takes the longer one.

**So the rule: an agent that finds its targets already closed has not finished. Run
`lake build` on its module anyway before writing the sentinel.** The cost is one build in a
worktree that is otherwise idle; the payoff is that release-blocking breakage is found by a
worker with time to fix it rather than by the merge worker with a hundred branches queued
behind it. `to_merger` is then the channel, since the fix lives in files the agent was never
assigned.

Corollary for the same situation: the useful work is one level DOWN. The three targets'
residues — the leaves their proofs opened — are named in their own docstrings, are unowned by
construction (they did not exist when the queue was written), and are exactly what the next
dispatch would have to find anyway.

## MERGING NINETY BRANCHES: the policy that works, and the four checks that must go with it

(2026-07-31, release 24 — 92 branches, 51 clean, 41 conflicting, 1 declined.)

**Resolving to `ours` by default LOSES PAYLOAD, and the loss is silent.** Measured on this
batch: a plain `ours` resolution dropped branch-added declarations in 17 of the 41 conflicting
branches — 71 of them from `flt-lean-362` alone. The branch still becomes an ancestor, the
build is green, and nothing says the work is gone.

The policy that preserved both sides, per conflict hunk:

- **base empty** (both sides ADDED at the same point) → `ours + theirs`, *unless* every
  declaration `theirs` introduces is already declared in `ours` — then `ours` alone, because
  the same content reached `main` by another route and the union would duplicate it;
- **base non-empty** → `ours + theirs` whenever `theirs` declares a name the BRANCH ADDED
  (absent at the merge base) that `ours` does not have; otherwise `ours` plus the blocks
  `theirs` purely INSERTED relative to base (`difflib` opcodes, `insert` only).

That took 41 conflicting branches down to 7 needing hand work. **But the policy is only safe
because of the checks, and three of the four had to be fixed before they told the truth:**

1. *Every branch-added declaration is present in the resolved file.* Compute "branch added" as
   branch-decls minus MERGE-BASE-decls — not minus `main`'s, which flags every name `main`
   legitimately deleted.
2. *No newly duplicated declaration name*, **diffed against pre-merge `main`** — this tree has
   many legitimate same-name pairs.
   - **Qualify by NAMESPACE.** `fieldAct_mul`/`_one`/`_xx`/`_yy` exist in both `GeomPic` and
     `ConstFieldExt` in `HyperellipticJacobian.lean`; a flat scan calls all four duplicates.
   - **Keep DOTS in the name.** A regex ending the name at the first dot collapses
     `IsCharRootMultiset.eq_roots` and four siblings onto `IsCharRootMultiset` and reports it
     five times over.
   - **Strip comments LINE-granularly** (a block starts at a line whose first token is `/-`,
     ends at a line containing `-/`). Character-level nesting goes wrong on this tree's
     docstrings and then the scan cannot see real declarations at all.
3. *Block-comment nesting depth returns to zero in every file.* **This is the new one and it is
   the cheapest check in the list.** A conflict hunk can begin INSIDE a docstring; keeping
   `ours` keeps the `/--` while the `-/` was on the side you dropped, and the docstring then
   swallows the rest of the file. Four files this release. Lean says `unterminated comment` at
   the LAST LINE, thousands of lines from the damage, and the module plus everything importing
   it fails — twenty minutes into the release build. The scan finds all four in a second.
   The mirror case also occurs: `MordellWeil19.lean` kept HEAD's `-/` and then the branch's
   paragraph landed *after* it as bare prose, so 25 lines of English were parsed as Lean.
4. *The release build, three rounds minimum* — for the reason release 22 recorded: the errors
   are serialised behind each other by the import graph.

**And a fifth failure this policy CREATES, which no declaration-level check can see: a
duplicated HYPOTHESIS.** Two branches gave `DualStruct.weil_nondegenerate` the same level gate
in two different styles — one a named binder `(_hnF : (n : F) ≠ 0)`, one an anonymous
`(n : F) ≠ 0 →` — and the union demanded it twice while the sole consumer supplied it once.
That produced 22 `(kernel) application type mismatch` errors plus a
`declaration has metavariables`, all reported at the USE site, which reads exactly like a
broken proof and is not one. **When two branches repair the same statement, the union of their
edits is not the repair.** Diff the two signatures against the merge base before taking both.

Finally, the merge-order effect, since it is cheap to exploit: conflicts are evaluated against
`main` *as it stands when you merge*, so a branch that conflicts in one order can be clean in
another. 15 of this batch's branches went clean on a second pass simply because the earlier
merges had landed first.

## THE FIRST TWO COMMANDS OF EVERY TASK: `git merge --ff-only main`, then `git show merger:<file>`

(2026-07-31, `flt-lean-232`, both measured on the fleet rather than inferred.) A prover agent
under the Python loop can be handed a worktree that is hundreds of commits stale AND a target
that was proven a day earlier. Both are cheap to detect and neither is detectable from inside
the task prompt.

**1. YOUR WORKTREE MAY NOT BE AT `main`, AND THE LOOP WILL NOT SAY SO.** `flt-lean-232` was
dispatched at `9a2ca10d` with `main` at `d451d20b` — **704 commits behind**. A sweep of the 112
live jobs at that moment found **23 behind `main`, 6 of them by the full 704**; the other 17 were
2 behind, which is only the tooling commits after the rebaseline sha and harmless. So this is not
a one-off: it is roughly 5% of dispatches, silently.

**THE CAUSE IS THAT NOTHING ADVANCES A WORKTREE — NOT THE LOOP, NOT THE RELEASE, NOBODY.** This
is worth stating plainly because the old orchestrator DID repoint at dispatch, the sections above
still describe that hook, and it is gone. Read the production code: `flt-loop.py`'s `do_spawn`
composes a prompt and runs `cd <worktree> … claude`, and that is the whole of it — no `merge`, no
`checkout`, no `branch -f`. The merge worker works in `~/flt-staging`; its five ordered duties are
merge, build the snapshot, rewrite `queue1`, stamp `AUDITED:`, stamp the snapshot sha. **None of
them touches a pool worktree.** So a worktree sits at whatever `main` was when its last occupant
last merged, indefinitely.

Which is exactly why the current ones are current: **the agents advance them.** The merge worker's
queued task text opens with *"Run `git merge main`, then `lake build …`"*, so every agent on a
merger-written task drags its worktree forward as a side effect. Tasks that lack that line — older
`queue1` entries, and the one that produced this section — leave the worktree wherever it was. The
repair belongs in the queue text, and it is one line: **put `git merge --ff-only main` in every
task's preamble.**

**Do not "fix" this in `flt-loop-fs.py`.** That file is the SIMULATOR — its `repo()` is
`~/.flt-loop/repo`, a stand-in repository for testing `flt_loop_rows.py`, not `~/flt-lean` — and
its `grepo("branch", "-f", j["worktree"], "main")` is simulation, not the dispatcher. It would not
work against the real pool anyway; git refuses to force a branch that a linked worktree has
checked out, which is every worktree in the pool:

    $ cd ~/flt-lean && git branch -f flt-lean-232 <sha>
    fatal: cannot force update the branch 'flt-lean-232' used by worktree at '/home/chend/flt-lean-232'
    EXIT=128

Any loop-side repoint has to run INSIDE the worktree (`git -C <wt> merge --ff-only main`), and
`--ff-only` rather than a forced checkout, so that a worktree still holding someone's uncommitted
work fails loudly instead of losing it.

**The free detector is the line number in your own prompt.** The task said
`Fermat/FLT/ModularCurve/X1.lean:15893`; the file had **10391 lines**. A `Read` at that offset
returns "the file is shorter than the provided offset", and a `grep` for the target returns
NOTHING — which reads exactly like "this leaf does not exist / was renamed" and is the wrong
conclusion. Before believing any such absence:

    git merge-base --is-ancestor HEAD main && git rev-list --count HEAD..main   # 0 = current
    git merge --ff-only main                                                    # if behind

It is safe: the worktree is clean at dispatch and its branch is an ancestor of `main`, so this is
a fast-forward, never a merge. Do it FIRST, before reading anything.

**2. THEN CHECK `merger`, BECAUSE THE LOOP'S QUEUE AUDIT STRUCTURALLY CANNOT.** `queue1` records
its audit as `AUDITED: <main sha>`, and `flt-loop-fs.py`'s release-time audit computes
`open_leaves()` from the repo at `main`. That is correct by its own contract and it means the loop
**cannot see a leaf proven on `merger` and not yet released** — every such leaf is re-dispatched,
guaranteed, once per release window. This is the fifth invisibility class above, but under the
Python loop it is no longer a judgement call that a careful orchestrator might catch: it is
mechanical, and the only thing standing in front of it is the agent.

`exists_nonconstant_toAbelianScheme_of_notGeometricallyRational` was `sorry` on `main` and
**PROVEN on `merger`** (via `flt-lean-34`, merger commit `df076668`), by decomposition into two
new residues. One command would have found it, and it is the same command CLAUDE.md already
prescribes:

    git show merger:Fermat/FLT/ModularCurve/X1.lean | grep -n <your target>

**3. IF YOUR TARGET IS ALREADY DONE, DO NOT GO LEAF-SHOPPING ON `main` — THE FLEET IS SATURATED.**
Measured the same day: `flt-frontier.py` gave **320 direct leaves** and 112 live jobs named all but
**3** of them in a `TARGET:` line. All three turned out to be accounted for anyway — two were
already `queue2` targets, and the third
(`exists_globalFrobCharScalar_atPrime_of_coherentLevelScalar_finiteBase`) was **already proven on
the unmerged branch `flt-lean-101`** and re-cut there into a queued successor. **Unowned work on
`main` was empty**, and taking an owned leaf duplicates a live agent.

Note what the third one shows: a leaf can be simultaneously open on `main`, absent from every
live `TARGET:` line, and finished — and the evidence lived in the BODY of an unrelated queue
entry, not in any ownership record. So grep `queue1`/`queue2` in FULL, not just their `TARGET:`
lines, before concluding anything is free.

The work that IS unowned is the **residues cut on `merger` since the last release** — new leaves
nobody can be dispatched at, because they do not exist on `main`. Those belong in your `queue`,
written as full task prompts. That is the highest-value output an agent with a finished target
has, and it is invisible to everyone else by construction.

**Do NOT re-prove the target on `main` "so the branch carries it".** `merger` already has it; a
second proof of the same theorem is a name collision the merge worker must resolve by discarding
one, which is a choice that belongs to an author, not a merge.

## A DECLINED DECOMPOSITION IS A STANDING TASK — the reason it was declined goes stale

(2026-07-30, `flt-lean-203`.) `nonempty_fullTranslationDatum_two`'s docstring contained a
paragraph headed **"THE DECOMPOSITION THAT WOULD PAY FOR ITSELF, and it is uniform in `q`"**,
naming the exact cut that merges it with `nonempty_preTranslationDatum_three_of_intCoeff_pos`,
and ending: *"That cut is NOT made here only because
`exists_potentiallyGoodModel_of_jIntegral_three` has a live owner and restructuring it under
them would cost a merge conflict for no mathematical gain."*

The mathematics in that paragraph was right and the coordination reason was **two days stale**.
Making the cut took one 60-line proven bridge
(`nonempty_translationDatum_of_full_of_ne_two`: in residue characteristic `q ≠ 2`, `2` is a
unit of `A`, so `ha₁`/`ha₃` give `u⁻¹s, u⁻³t ∈ A` and the three `s`/`t`-corrections
`u⁻²s²`, `u⁻⁴(2st)`, `u⁻⁶t²` are products of those) and turned **two open leaves into one**,
with no signature change anywhere.

So: **when a docstring names a decomposition and declines it for a COORDINATION reason —
"has a live owner", "would conflict with", "is owned elsewhere" — that is a queued task, not
a closed axis.** Re-check the reason; ownership in this fleet turns over in hours. Distinguish
it from a decline for a MATHEMATICAL reason, which does not go stale: the same file's
**"AXIS SEARCHED AND CLOSED: `(ψ, r)` MUST STAY IN ONE EXISTENTIAL"** on
`exists_fundamentalCharacter_of_semistabilityDefect` comes with an explicit counterexample
(`N = 29`, `e = 4`, `ψ' = ψ_L^15`) and should be believed.

Corollary for anyone tempted by the same merge elsewhere: **two per-prime leaves whose
docstrings state the SAME residual obstruction are one leaf.** Both of these ended with "THE
ONE REMAINING GAP IS ... residue degree `1`", written out twice over two different datum
structures. Grep for repeated obstruction sentences across sibling leaves before proving
anything.

## Verifying a BLOCK MOVE inside a file: sort both versions and diff

Relocating a declaration to satisfy Lean's define-before-use order is a common repair, and a
hand-retyped 100-line block can be silently corrupted in a docstring where nothing will ever
catch it. The check costs two commands and is exact:

    git show HEAD:<file> | sort > /tmp/old.txt
    sort <file>          > /tmp/new.txt
    diff -q /tmp/old.txt /tmp/new.txt      # identical multiset => the move was byte-exact

Any output means content changed as well as moved, which for a *pure* relocation is a defect.
Do the move programmatically (slice the line list, reinsert) rather than by retyping; that is
the case the "prefer Write/Edit" rule exempts as capability rather than convenience, and this
diff is what makes it auditable. Watch the blank lines at both the source and destination
seams — the multiset check catches a doubled blank line too.

## `simpa using h` can normalise the HYPOTHESIS to `True` and still fail

Symptom, and it reads as nonsense: `Type mismatch: After simplification, term h has type True
but is expected to have type <the goal>`. It means simp PROVED `h`'s statement while leaving
the goal unproved — which sounds impossible, since it is simping both.

It happens when a simp lemma rewrites a TYPE INDEX and thereby unlocks an instance for one
side only. Concrete instance (`MazurTorsion.lean`, `N = 1` branch of
`exists_weilPairing_mu_nondeg_of_coprime`): `h : ((1 : ℕ) : ℤ) • ↑x = 0` where
`x : ↥(E.nTorsion 1)`. Normalising `((1:ℕ):ℤ)` to `1` lets `Submodule.torsionBy_one` rewrite
the submodule to `⊥`, whose carrier is a `Subsingleton`, so `eq_iff_true_of_subsingleton`
closes `h`. In the GOAL the same term sits under the `nTorsion` abbrev, which blocks that
rewrite, so the goal only reaches `x = 0`.

Fix: replace `simpa` with `simp only [<the two lemmas you actually want>] at h` plus an
explicit `exact`. General rule — when a `simpa` fails with `has type True`, the problem is
that simp is doing MORE on one side, so name the rewrites instead of widening them.

## Run the `merger` check as step ZERO, not after the proof is built

(flt-lean-250, 2026-07-31.) Dispatched at `exists_hilbertClassField_artinIso` and
`exists_surjective_aut_classGroupQuotient`, I read the file, designed a decomposition, and
proved four of its pieces in Lean — *then* ran

    git show merger:<the file> | grep -n <the target name>

and found both targets already PROVEN on `merger`, in a strictly stronger form, over exactly
the decomposition I had just re-derived (an existence-theorem leaf, the Artin iso recovered by
counting, tower-functoriality of the Frobenius, and transfer of `relNormClassSubgroup` along a
`K`-algebra iso). The check is the one this file already prescribes for the release window; it
cost nothing and it worked. It was simply run too late. **Run it, for every declaration a task
prompt names, BEFORE reading the file.** Task prompts are generated from `main`, and `main` is
the frontier as of the last release.

**And when `merger`'s copy of the file is bigger than `main`'s, read `merger`'s.** The useful
output is not only "already proven" but "already DECOMPOSED": the frontier has moved to names
that only that branch knows. Here the sole remaining leaf,
`exists_unramifiedAbelian_card_classGroup_le_finrank`, **does not exist on `main` at all** — so
it emits no `declaration uses 'sorry'` warning in any build of `main`, no source scan can see
it, no ownership record names it, and a queue audit run against `main` would DELETE a task
naming it. A decomposition performed on an unmerged branch is a *sixth* way for open work to be
invisible, and the only instrument that sees it is the merger's copy of the file.

Corollary for verification: checking out `merger`'s version of a file into your own worktree
and building it is cheap (one module, minutes) and tells the merge worker something it does not
otherwise know — that the branch is green, and the exact warning set it lands with.

## RUN THE `merger` CHECK AS YOUR FIRST ACTION, NOT AS TRIAGE AFTERWARDS

(2026-07-31, `flt-lean-233`, measured.) The FIFTH invisibility class above already gives the
command and already says `merger` is where the answer lives. This is about WHEN to run it.

I was dispatched at three leaves in `ArtinConductor.lean`. I read the file, derived a proof of the
first, and committed it green — and only then ran

    git show merger:Fermat/FLT/Deformations/RepresentationTheory/ArtinConductor.lean | grep -n <name>

which showed **two of the three already PROVEN on `merger` the previous day**, one of them by an
essentially identical argument found independently. The whole run's Lean output had to be reverted
as a rival cut. The check costs one command and five seconds; running it after the work instead of
before cost an agent-run.

So: **before reading the target declaration, grep `merger` for every leaf named in your prompt** —
all of them, not just the one you intend to start with. A queue task is audited against `main` at
release time, and `main` is the frontier as of the last release; a task written a day ago can name
leaves that were closed hours later. Two of three is not an unusual hit rate for a file under
active work.

And when the answer comes back "already proven", the honest deliverable is the DECLINE, made by
you: revert your payload, name your own commit sha so the rival proof stays recoverable, and say
which tiebreak decided it. Leaving both proofs for the merge worker is a guaranteed name collision
on a file it must resolve blind.

## A CUT-ANALYSIS SAYING A ROUTE "CANNOT BE AVOIDED" IS A HYPOTHESIS ABOUT A PROOF

(Same run, and the reason the leaf fell at all.) `mem_gp_one_of_dvd_smul_unif_sub` carried a
careful, signed analysis concluding it "CANNOT BE AVOIDED" without the monogenicity
`𝒪_L = 𝒪_0[unif]` plus Hensel: `δ_x(σ) := (σ•x − x)/unif mod 𝔪` is a DERIVATION in `x`, so it is
"determined by its value on a ring GENERATOR, and nothing weaker". The analysis was right about the
derivation and right about the two substitute routes it examined (both re-verified dead). It was
wrong about the conclusion, and the counter-proof is forty lines.

The move that dissolves it is worth naming, because it generalises: **attack a `∀ x` by CASES on
the element, not by a normal form for it.** Here `mem_gp`'s quantifier splits as unit / non-unit;
non-units are `unif · y` by `unif_spec`, and a UNIT is soft because `R^×` is, modulo `𝔪`, torsion of
order prime to `p` — the residue field of a finite level is FINITE. A derivation is determined on a
generating set, but the generating set may be `{unif} ∪ R^×` rather than `{unif}`, and then no
generator theory is needed at all.

Two agents a day apart found exactly this proof, both against the docstring's own "impossible".
So the standing rule: **a cut-analysis records which routes were tried, and that is all it records.**
Read it for the dead ends it certifies — those are real and save time — and re-derive the negative
conclusion yourself. The same applies to any "needs new theory" or "ATOMIC" verdict in this tree.

## "TENSOR COMMUTES WITH FILTERED COLIMITS" IS ALMOST NEVER THE STEP YOU HAVE TO FORMALISE

(2026-07-31, from closing Half A of [Stacks 00R6],
`exists_le_idealTensorComparison_eq_zero_of_isNoetherianFlatDescentSystem`.)

Several leaves in this development are cut with a docstring that ends "…tensor products
commute with filtered colimits, so the element already dies at a finite stage". Taken
literally that sentence is a whole module-theoretic colimit development — the colimit of
`↥(𝔪 C_j) ⊗_{C_j} D_j` over `j`, built from nothing but the ring-level `surj`/`sep`
fields — and `Ring.DirectLimit` is deliberately banned here, so there is nothing to build
it out of. A prover who takes it literally is looking at hundreds of lines before the
leaf's own argument starts.

**The substitute is mathlib's EQUATIONAL CRITERION FOR FLATNESS**,
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero` (`@[stacks 00HK]`, in
`Mathlib/RingTheory/Flat/EquationalCriterion.lean`). It converts flatness at the COLIMIT
into a **finite amount of data**: from `∑_k a_k x_k = 0` it returns `b_{kp}` and `y_p`
with `x_k = ∑_p b_{kp} y_p` and `∑_k a_k b_{kp} = 0`. Finite data is exactly what
`c_surj`/`d_surj`/`c_sep`/`d_sep`/`directed` descend, one element and one equation at a
time. No colimit of modules is ever constructed; only ring elements and ring equations
are ever moved. The whole colimit step came to ~90 lines.

Two things that fall out and generalise:

- **`exists_ub_finset_of_directed` / `exists_ub_fintype_of_directed`** (added to
  `AbelianSchemeIsogeny.lean`): pairwise directedness upgraded to finite sets and to
  fintype-indexed families, stated for a bare `le : Λ → Λ → Prop` with reflexivity,
  transitivity and directedness as arguments. Every descent argument in this development
  needs one, and there was none — check for them before writing a `Finset.induction` by
  hand. They apply verbatim to `NoetherianLocalBaseSystem` and `NoetherianLocalExtSystem`
  as well as to `IsNoetherianFlatDescentSystem`.

- **`M ⊗[R] S` is NOT an `S`-module in mathlib.** `TensorProduct.leftModule` acts on the
  LEFT factor; there is no right-hand counterpart, so a docstring step of the form "…so
  its submodule is f.g. because `D` is Noetherian", where the submodule sits inside
  `↥𝔪 ⊗[C] D`, is *not directly expressible*. The fix that worked, and it is reusable:
  present the tensor by TUPLES — if `I = (a_1,…,a_r)` then every element of `↥I ⊗[C] M`
  is `∑_k ⟨a_k⟩ ⊗ₜ x_k` (`exists_repr_tmul_of_span_range`) — and run the finite-generation
  argument on the kernel of an honestly `D`-linear map `D^r → D` instead. Do not go
  looking for `TensorProduct.rightModule`; it is not there.

## A DOCSTRING'S CLAIM ABOUT THE IMPORT GRAPH IS A HYPOTHESIS, AND A FALSE ONE PICKS THE EXPENSIVE PLAN

(2026-07-31.) This file already treats a stale `(sorry leaf)` label as a phantom-work source.
The same failure at MODULE scale is worse, because it does not produce a wasted dispatch — it
produces a wasted *architecture*, and the agent that follows it never learns the plan was
avoidable.

`ProjectiveModelOverField.lean`'s header stated, twice, that "`EllipticScheme.lean` is
DOWNSTREAM of `MoretBailly.lean` and so cannot be imported there". Both closures were walked
at `7080929d`, with no module missing from either walk: `EllipticScheme` reaches 56 `Fermat.*`
modules and does not contain `MoretBailly`; `MoretBailly` reaches 170 and does not contain
`EllipticScheme`. **They are INCOMPARABLE.** So the import is available in either direction —
`MoretBailly` importing `EllipticScheme` adds 7 modules and no cycle.

What the false claim was buying: `exists_projGroupLawOverField_geomFibreAddEquiv` wants the ℚ
group-law development at a general base, and its docstring accordingly plans a REWRITE of an
11 832-line chart interface inside a 51 000-line module — ~20 minutes of elaboration per
iteration. The reachable plan is to generalise `ProjCoords`/`exists_projAdd` IN PLACE in
`EllipticScheme.lean`, recover ℚ as `(F := ℚ)`, and import. Nobody had checked, because the
header said not to.

**So before planning around "module A cannot see module B", walk the closures.** It is ten
lines and seconds of runtime:

    def imports(m):  # m.replace('.','/') + '.lean', regex ^(public )?import (Fermat[\w.]*)$
    def closure(m):  # BFS; ASSERT every visited module's file EXISTS — a silent
                     # FileNotFoundError truncates the walk and manufactures "incomparable"

The assertion matters more than the BFS: a swallowed missing file is exactly how this check
produces the answer you were hoping for.

Corollary, and the reason to fix the docstring rather than just route around it: an import-graph
claim is *cheap to verify and expensive to believe*, so it should never be carried as prose
without a stamp. Write the commit it was measured at, the way frontier counts are stamped.

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

## A FALSITY AUDIT THAT SEARCHES ONE SUB-FAMILY PROVES NOTHING — and "hypothesis ⟺ conclusion" is the tell

(2026-07-31.) `IsShortExact.exists_lift_ker_le_span_cartierDual` in
`Fermat/FLT/Mathlib/RingTheory/HopfAlgebra/ShortExact.lean` carried **two** dated FALSITY AUDITS,
both careful, both correct, both concluding "searched, not refuted". They had also both noticed
the same odd thing and written it down as *weak evidence for* the leaf:

> "the hypothesis keeps turning out to be equivalent to the conclusion rather than merely
> implying it, which is why no counterexample has been produced."

**That coincidence was the refutation, not evidence against one.** When a hypothesis you did not
choose keeps coming out *exactly* equivalent to the conclusion across independent-looking
examples, the examples are not independent — you have picked a sub-family in which some identity
forces them together. Find the identity, then vary whatever it constrains.

Here the audits had searched `G' = μ_p`, `G'' = ℤ/p` — **the two groups always of the same
order**. In that shape the one non-trivial fibre of `G → G''` occurs exactly once, so
`Module.Free R O(G)` and the conclusion are literally the same condition on `[L] ∈ Pic(R)`.
Widening the quotient by one factor of `p` (`G'' = ℤ/p²`) makes the bad fibre occur `p` times,
and `p·[L] = 0` makes the hypothesis VACUOUS while the conclusion is untouched. With `p = 2`,
`R = ℤ[√-5]`, `Pic = ℤ/2`, the counterexample is three lines — **over a Dedekind base, which one
of the two audits had explicitly ruled out** ("a counterexample must have Krull dimension ≥ 2").
That ruling-out was a true statement about the sub-family read as a statement about the leaf.

Three transferable rules:

- **An audit's scope is part of its verdict.** Record which family was searched *in the verdict
  sentence*, not just in the working. "No counterexample" is not a result; "no counterexample
  with `ord G'' = ord G'`" is.
- **Vary the parameter you did not think of as a parameter.** Both audits varied the base ring
  (dimension, `Pic`, `K₀`, characteristic) and neither varied the *relative size* of the two
  ends. The unvaried parameter is where the counterexample lives, essentially by construction.
- **Multiplicity kills K-theoretic obstructions.** If a hypothesis says "`m` copies of `P` are
  free" and the conclusion says "`P` is free", they are the same statement only when `m` is prime
  to the order of `[P]` in `K̃₀`. Check that arithmetic before believing a hypothesis is
  load-bearing.

And the repair worth copying: when a leaf is refuted, look for the hypothesis the *real* consumer
already has. Here the whole chain (five declarations) gained `[IsLocalRing R]`, which is true at
the only intended base (`𝒪ᵖᵥ`), makes `CartierDual R A'` semilocal, and turns the remaining
mathematics from "global triviality of a torsor" into mathlib's
`Module.free_of_flat_of_finrank_eq`. Cost: zero, because a grep showed every mention of the
chain outside its own file was a docstring. **Grep for term-level consumers before assuming a
hypothesis cannot be added; in this development most of the tree is not consumed yet.**

**And the refutation paid for itself immediately, which is the general pattern.** Once the false
GLOBAL statement was replaced by the true LOCAL one, the leaf stopped being atomic: it fell in one
sitting to `flat + constant fibre rank` (a new, strictly smaller, Zariski-local sorry) plus two
proven steps — `finite_maximalSpectrum_of_isLocalRing_of_module_finite` (new, ~35 lines, pure
commutative algebra) and mathlib's `Module.nonempty_basis_of_flat_of_finrank_eq`. A leaf that has
resisted every cut for days is worth suspecting of being false *precisely because* falsity is what
makes it uncuttable: no cut can be found, because there is nothing true underneath to cut into.
"Atomic on every axis tried" is evidence about the statement, not only about the prover.

## "FINITE FLAT" OVER A FIELD IS EMPTY — and the leaf it nearly made false

(2026-07-31, caught before it was written down.) A leaf of the shape *"a closed
subscheme of a `ℚ̄`-scheme is determined by its `ℚ̄`-points"* is the residue of at
least three separate nodes in `ModularCurve/X0.lean`. The natural hypotheses to
copy across from the object at hand — a `CyclicSubgroupOfOrder`, whose fields are
`isClosedImmersion`, `isFinite`, `flat` — give a statement that is **FALSE**:

* over a FIELD every module is flat, so `IsFinite + Flat` says only "finite", and
  `A = 𝔸¹`, `C₁ = ` the origin, `C₂ = Spec ℚ̄[ε]` are two finite flat closed
  subschemes with the same `ℚ̄`-points (the only `Spec ℚ̄ ⟶ Spec ℚ̄[ε]` kills `ε`)
  that are not isomorphic.

Reducedness here does **not** come from flatness; it comes from Cartier's theorem,
which needs the GROUP structure — in this tree that is
`CyclicSubgroupOfOrder.etale_of_specQBase`, and the hypothesis to state is
`AlgebraicGeometry.Etale`, not `Flat`. Two further hypotheses are equally
load-bearing and equally easy to drop: `IsAlgClosed` (over `ℚ`,
`Spec ℚ[x]/(x²+1)` and `∅` have the same `ℚ`-points) and `IsClosedImmersion`
(`Spec K ⊔ Spec K` onto one point versus `Spec K`).

General form, and it is the cheap habit: **when a leaf says "determined by its
points", write down what happens at a NON-REDUCED subscheme, at a NON-CLOSED
point, and over a NON-ALGEBRAICALLY-CLOSED base, before you write the binders.**
Each of the three has a two-line counterexample, and each survives review, because
the hypotheses were copied verbatim from a structure where they were sufficient
*in combination with a field the leaf no longer mentions*.

## THE SAME MISSING LEMMA, RECORDED THREE TIMES UNDER THREE NAMES

(2026-07-31.) Before cutting a bespoke leaf, grep the file for the gap you are
about to name. `X0.lean` recorded one statement — the one above — in three
places under three phrasings: as item 3 of
`nonempty_isBaseChangeOf_of_isIso_isWeierstrassModel`'s itemisation ("both are
finite étale, hence reduced, hence determined by their geometric points"), as the
"WHAT REMAINS OF (b)" paragraph of
`exists_gamma0Datum_specQ_isBaseChangeOf_liesIn_of_weierstrassQForm` ("the passage
from `ℚ̄`-points to closed subschemes"), and as the SCOPE paragraph of
`liesIn_spanScheme_iff_mem_zmultiples` ("the new conjunct is about `ℚ̄`-POINTS and
NOT about `T`-points"). None of the three names the other two.

Cutting it ONCE, in the generality that covers all three, turns a 1-leaf-for-2
trade into a 1-leaf-for-2 where one of the two is already owed elsewhere — which
is the difference between adding work and disclosing it. The tell is verbal
rather than structural, so it takes a grep for the *mathematical content* ("points
determine", "reduced", "subscheme"), not for a declaration name.

## A ROUTE AUDIT NEVER CHECKS DECLARATION ORDER — and that is a whole blocking axis

(2026-07-31, flt-lean-210, found by trying to walk a route the file certified as open.)

Every audit shape this project writes — ROUTE AUDIT, ATOMICITY AUDIT, CUT-OBSTRUCTION AUDIT —
reasons about *mathematics* and about *what exists in the tree*. None of them reasons about
**where in the file it exists**, and in a 31k-line module that is a live, independent way for a
leaf to be unattackable.

`exists_framedGaloisRep_descent_hilbertTraceSubring_of_isWeaklyUniversal`
(`HardlyRamified/HilbertModularity.lean`) carried a section headed "ROUTE OBSTRUCTION FOUND —
REPAIRED. THE BINDER IS NOW ON THIS NODE", ending "**The route described below is therefore
AVAILABLE, and a prover dispatched at this leaf now has one**", and the consumer's summary agreed:
"The route is available; the leaf is attackable." The binder repair was real and the mathematics
was right. **Every declaration the route spends sits ~1000–2000 lines BELOW the leaf**, so Lean
forbids the appeal — and restating any of them above it would duplicate a live declaration, which
is worse. The docstring even records the block correctly for ONE of those declarations
(`exists_framedGaloisRep_hilbertTraceSubring`, "blocked mechanically: both live BELOW this point")
without noticing it applies to the whole route.

So: **before certifying a route as available, `grep -n` the line number of every declaration it
spends and compare it with the leaf's own.** It costs one command. And when you record a route,
record the line numbers, because they are the part of an audit that a reader cannot re-derive from
the mathematics.

Two corollaries:

- **The repair is a RELOCATION, and relocations are the worst shape for a merge** (a ~950-line
  block move conflicts with any concurrent edit inside it). So measure it, write the recipe into
  the docstring, and queue it as its OWN commit touching nothing else — do not attempt it while
  the file has another owner. The measurement that makes it safe is one grep: the names declared
  in the moved block, searched for *in code* across the range it moves over.
- **"Blocked, it is another module's region" is the same error one level up, and it is usually
  wrong about CUTS.** The same file declined its own next cut on the ground that the repair lives
  in `Modularity/MoretBailly.lean`. Proving the sub-leaves does live there; **stating** them cost
  nothing, because that module is a `public import` and every name in their signatures was already
  in scope. The cut was taken from the consumer's file, no other file was touched, and it exposed
  a second obstruction nobody had recorded. This is CLAUDE.md's "STATING a theory is not PROVING
  it" in its commonest disguise: an obstruction to the PROOF written down as an obstruction to the
  CUT.

## A loop-dispatched worktree can be HUNDREDS of commits stale, and `lake` is not on `PATH`

(2026-07-31, `flt-lean-235`, cost ~10 minutes but would have cost a whole run had it gone
unnoticed.) Two facts about the state a prover agent actually wakes up in, neither of which is
stated in the task prompt:

- **`lake`/`lean`/`elan` are NOT on the default `PATH`** of a fleet worker's shell. The first
  command run was `lake build …`, which returned `lake: command not found` and **exit 127** — a
  build log that looks like a build failure. Every shell needs
  `export PATH="$HOME/.elan/bin:$PATH"` prepended; it does not persist between Bash calls.
- **The worktree may not be at `main`.** `flt-lean-235` was dispatched sitting on an old `merger`
  commit, **704 commits behind `main`**, with a `.lake/build` to match. The task prompt's line
  numbers were `main`'s, so every one of them pointed at unrelated code, and a repo-wide grep for
  the three target declarations returned **nothing at all** — which reads exactly like "these
  leaves were deleted/renamed since the queue was written", the diagnosis that ends a run in a
  `to_merger` note instead of a proof.

So the first two commands of any prover run, before reading the target file:

    export PATH="$HOME/.elan/bin:$PATH"
    git merge-base --is-ancestor HEAD main && git merge --ff-only main

Then seed artifacts rather than building mathlib: `~/.flt-release-lake/sha` names the commit the
snapshot was built at; if `git log --name-only <sha>..main` touches no `.lean` file the snapshot is
**exactly current** for Lean, and

    rsync -a --delete ~/.flt-release-lake/build/ .lake/build/

turns a 704-commit-stale tree into a green one. `lake build <Module>` then confirmed
`Build completed successfully (5590 jobs)` in a couple of minutes with nothing to elaborate.

Corollary for triage: **"the declaration does not exist anywhere in the tree" is a
wrong-checkout symptom before it is a rename symptom.** Check `git log --oneline -1 main` against
`git log --oneline -1` before believing a grep that returns zero.

## THE `sorry`-WARNING SET IS THE EXACTLY-WRONG EVIDENCE IN THE RELEASE WINDOW

(2026-07-31, `flt-lean-235`. The release-window section above already prescribes the check that
would have caught this; this is a note on WHY an agent following the rest of this file skips it.)

Three leaves were dispatched. I fast-forwarded to `main`, ran `lake build` on the module, and read
the `declaration uses 'sorry'` warning set: all three target line numbers were in it — `42221`,
`53124`, `53285` — matching the task prompt exactly. That is the compiler speaking, and this file
says in bold that **the compiler is the only reliable ownership evidence**. So I started work.

**All three were already PROVEN on `merger`**, over a new file
`Fermat/FLT/NumberField/CyclotomicIdealSymbol.lean` that does not exist on `main` at all. I spent
the run rebuilding a strictly weaker version of one of them, and it had to be thrown away.

The two rules are in tension and the tension is not marked:

- *"Prefer the compiler to any prose claim about what is still open"* is about **`main` being
  wrong in the direction of claiming a leaf is CLOSED** — a stale docstring, a commit message, an
  agent's report.
- The **release window** is `main` being wrong in the other direction: a leaf that is closed on an
  unmerged branch is still `sorry` on `main`, so the warning set lists it, **truthfully and
  uselessly**. A green build cannot see work that has not merged, and by construction the work you
  are being dispatched at is the work most likely to be in flight.

So: **a build tells you the state of the tree you built, and the tree you built is `main`.** For
"is this leaf still open" that is not an answer. Run, before the first edit and before trusting any
line number:

    git show merger:<the file> | grep -n '^theorem <name>'   # then read the body: `sorry` or not?

and check `~/.flt-loop/queue2` / `~/.flt-merge-batch` for branches touching the same file. One
command, ten seconds, ahead of a multi-hour build.

Two smaller traps met on the way, both worth avoiding:

- **Do not `awk` for `/^theorem |^\/--/` to find where a declaration's body ends.** Statements in
  this development run to a hundred lines and the naive scan reports "not sorry" for a sorried leaf
  and vice versa. Locate the `^theorem <name>` line, then print forward and READ it.
- **A superseded branch is worse than an empty one.** My version proved the same theorem over ONE
  large leaf; `merger`'s proves it over FIVE small ones plus a reusable ideal-symbol lemma. Merging
  mine would have cost a conflict resolution and risked replacing the better proof with the worse.
  When your work is superseded rather than partial, **revert the Lean change** and report it —
  the value left is the report, not the code.

## NARROW A TERMINAL LEAF BY SPLITTING ON WHAT THE PROVEN BRANCH ACTUALLY CONSUMES

(2026-07-31, `Interface.lean`'s Serre local criterion.) When a leaf sits behind a
`by_cases`, the split condition is usually the *natural-language* hypothesis somebody
had in mind ("the inertia image is commutative"), not the thing the proven branch's
proof actually uses. Read the proven branch top to bottom and find where the positive
hypothesis is consumed. If it is consumed once, through a **one-directional
implication**, then **the conclusion of that implication is a strictly weaker splitting
condition** — and re-splitting there moves a real class of cases out of the sorry leaf
for zero mathematics.

The instance: the abelian branch took
`∀ σ τ ∈ localInertiaGroup, Commute (σ₀.toLocal σ) (σ₀.toLocal τ)` and used it in
exactly one step — fed through `hfix : σ₀.toLocal σ = 1 → σ r = r` to get
"inertia COMMUTATORS FIX `r`". `hfix` is one-way: `r` can be fixed by far more than
`ker (σ₀.toLocal)`. Splitting on the commutator condition instead moved the whole class
"`r` lies in the maximal subextension abelian over the maximal unramified one" into the
PROVEN branch, while `ℚ₃(σ₀)` itself stays nonabelian. Separating witness, which is what
makes this a cut rather than a rewording: `Gal ≅ S₃` très ramifiée, `r ∈ ℚ₃(μ₃)` — the
commutator `A₃` fixes `r`, so the new condition holds and the old one fails.

Three things this costs, all of which must be in the same commit:

- **The sorry count does not move.** A narrowing closes nothing. Say so plainly; a
  reviewer counting warnings will otherwise read the commit as no-op.
- **The renamed leaf's earlier FALSITY AUDIT is VOID.** Re-run it. Here it passed with
  no mathematics — only hypotheses were strengthened, so the new statement is *implied
  by* the old, and any counterexample refutes both. That argument is short and it is
  the one to look for first when a restatement only strengthens hypotheses.
- **The old branch's theorem can become FREE-FLOATING.** Rewiring the `by_cases` removes
  its only consumer. Either keep it consumed (a subsumed outer branch, two lines, with a
  comment saying why) or delete it in the same edit — do not merely bypass it.

And check for a *further* widening before stopping, because the answer is often no and
recording that saves the next owner the search: here the descent lemma consumes `hcomm`
only to build `(σ τ) r = (τ σ) r`, which looks weaker and is provably equivalent, since
the cyclotomic character kills commutators and so the commutator fixes `ζ^a · r` iff it
fixes `r`. That condition is optimal for that machinery; any further widening has to
come from a different tool.

## A NUMERICAL FORMULA CAN DEGENERATE — check the dimension before calling a leaf ATOMIC

(2026-07-31, `ringKrullDim_stalk_eq_zero_of_mono_of_curve_over_field`.) The leaf's own
docstring named its content correctly — "THE DIMENSION FORMULA FOR FINITE-TYPE `K`-SCHEMES,
and that is the whole of it", `dim 𝒪_{X,x} + trdeg_K κ(x) = dim X` — and concluded that
neither `trdeg` nor the formula "is in the pin as a statement about stalks, which is why
this is a leaf and not a step". Both clauses are true. The conclusion drawn from them was
still too pessimistic, and the reason generalises.

**In relative dimension `1` every term of that formula is `0` or `1`, so the EQUATION
degenerates to a DICHOTOMY**: `ringKrullDim 𝒪_{X,x} = 0` iff `κ(x)` is transcendental over
`K`. A dichotomy between two Props needs no arithmetic and no `trdeg` — it is a statement
about `Algebra.IsAlgebraic` alone, and `Algebra.IsAlgebraic` composes (`IsAlgebraic.trans`)
exactly where `trdeg` would have needed additivity. The whole development came to ~250
lines. So before accepting "this needs theory `T`", ask whether the instance of `T` you
actually need is a degenerate one; the general theory being absent from the pin says
nothing about the special case.

Two reusable facts found on the way, both worth knowing before attacking anything about
smooth curves over a field:

* **`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` is the whole
  toolkit.** It factors a smooth chart as `K → K[X₁,…,Xₙ] → A` with the second map ÉTALE,
  and étale gives `Module.Flat` (hence `Algebra.HasGoingDown`) and
  `Algebra.QuasiFinite` (hence `Algebra.QuasiFinite.eq_of_le_of_under_eq`: two primes with
  the same contraction, one below the other, are equal). Minimality of a prime and the
  vanishing of its contraction are then each other, in one line per direction. The same
  lemma is what closed `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` in
  `CurveExtension.lean` after three audits had declared "smooth ⟹ regular is absent from
  the pin".
* **`Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean` carries an instance
  `Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)`** for `f` formally
  unramified and locally of finite type. So "the residue extension along a quasi-finite map
  is finite/algebraic" is `inferInstance`, not a sub-leaf. `Mono f` supplies
  `FormallyUnramified f` through the diagonal.

**AND THE ONE PLACE THE BOOKKEEPING IS NOT FREE: a `K`-algebra structure on `κ(x)` must be
CANONICAL, never a chart's.** A statement comparing an invariant at `x : X` and at
`u x : J` over a common base `Spec K` needs `IsScalarTower K κ(u x) κ(x)`, and that holds
only if both `K`-structures come from the STRUCTURE MORPHISMS
(`strX.residueFieldMap`, `jstr.residueFieldMap`), where `hu : u ≫ jstr = strX` can be fed
in through `Scheme.Γevaluation_naturality` and `Scheme.Hom.comp_appTop`. A chart-derived
`Algebra K ↥(X.residueField x)` is a different term of the same type, and every transitivity
lemma silently fails to apply to it. The fix is to define the canonical one as a
`@[reducible] def` (not an instance — it depends on data), state the chart lemma with
`letI := that`, and discharge the mismatch once with `Algebra.algebra_ext`. Budget for that
step: it was a third of the proof.

## A "MISSING THEORY" VERDICT WRITTEN BY SOMEONE WHO COULD NOT IMPORT IT IS AN IMPORT FACT IN DISGUISE

(2026-07-31, `flt-lean-83`, `exists_frickeSlash_eq_smul_of_isNewEigenformAt`.) The leaf's
docstring said, in the file's usual careful style, that the proof "needs a genuinely missing
theory: Hecke operators as OPERATORS on `S₂(Γ₀(M))` … the commutation `W_M T_n = T_n W_M` …
and multiplicity one for the newspace", and backed it with a grep over `Fermat/`, the mathlib
pin and `~/cs/FLT/` that "returns no operator-level Hecke theory anywhere on this pin".

Every piece of that theory is PROVEN in this tree, in `Modularity/Interface.lean`:
`heckeTransform_slash_atkinLehnerRep` (the double-coset commutation),
`heckeOp_comm_atkinLehnerOp`, `heckeOp_apply_eq_smul_of_isWeightTwoEigenform` (the exact step
declared impossible — a coefficient-recurrence eigenform IS an operator eigenvector),
`exists_smul_of_heckeOp_eq_smul_of_not_dvd_level` (strong multiplicity one, in the leaf's own
conclusion shape) and the assembled `atkinLehnerOp_apply_eq_neg_qCoeff_smul`. Five
declarations, zero `sorry` among them.

**The mechanism, and it is systematic rather than a slip.** `Interface.lean` `public import`s
`ModularCurve/X0.lean`, so from inside `X0.lean` none of those names resolves, nothing
completes them, and no `example` referencing one will elaborate. An author working there
experiences the material as *absent*, and writes that down as a fact about the pin. The grep
that "confirms" it is then run with a mental filter for what could be used here, which is
exactly the filter that excludes the answer. Same shape as the self-certifying grep, but the
filter is the module graph rather than a spelling.

Two consequences worth acting on:

* **Run absence greps with NO import filter, then check reachability separately.** "Does it
  exist" and "may I name it here" are different questions and must be answered by different
  commands. Merging them turns a 200-line hoist into a "subtree to be built".
* **A cost-wall verdict in a file that sits UPSTREAM of the project's big interface module is
  suspect by default.** `X0.lean` had recorded this same error once before, for `heckeOp`
  itself; the repair was the hoist into `Modularity/HeckeOperator.lean` (612 lines, verbatim,
  justified by a reference scan showing the block named nothing else in `Interface.lean`),
  and `X0.lean` now imports it. That precedent is the template, not a one-off — when a leaf
  in an upstream module reports missing modular-forms theory, look for it in
  `Interface.lean` and price the hoist before pricing the mathematics.
* **Then actually PRICE it, by computing the closure rather than reading the section
  headings.** The five declarations above look like a `qCoeff`-plus-`AtkinLehner` shortlist;
  their transitive closure inside `Interface.lean` is **204 declarations and ≈ 9 000
  non-comment lines**, because multiplicity one runs on the Petersson inner product and drags
  in a fundamental-domain measure-theory block, the degeneracy operators, the oldform
  subspace and the Sturm bound. "The theory exists" and "the hoist is cheap" are separate
  claims; the first was the correction here, the second would have been a second error.
  A closure of that size must be dispatched as its own task and must not race a concurrent
  editor of the same file.
* **Compute the closure of what you ACTUALLY need, not of the headline theorem.** Dropping
  the one declaration whose conclusion names the eigenvalue's VALUE
  (`atkinLehnerOp_apply_eq_neg_qCoeff_smul`) took the closure from 204 declarations
  containing one `sorry` to **193 declarations containing none** — because the leaf being
  closed says `∃ c` and never asks what `c` is. A closure computed from the theorem that
  looks like your goal will routinely be bigger and dirtier than the one your goal needs.

The residue after such a hoist is usually small and is where the real work is. Here it is one
leaf: this file's `IsNewEigenformAt` (the sequence is not a stabilization) against
`Interface`'s `eigensystem_minimal` (no smaller divisor level realizes the eigensystem). The
two carriers do NOT bridge definitionally, and the needed direction is Atkin–Lehner Thm 1 /
Diamond–Shurman Thm 5.8.3.

## THE CM SURVEY, DONE ONCE SO IT IS NOT REDONE: what this pin does and does not have

(2026-07-31, flt-lean-159, while working the `MazurCMForm` cluster in
`MazurTorsion.lean`.  Every line below was checked by `grep`/`ls` against
`.lake/packages/mathlib` at our pin, not recalled.)

Four leaves in this tree ask for complex multiplication in one form or another
(`minpoly_eq_of_isCMJInvariant`, `exists_isCMJInvariant_ne_of_not_equivalent`,
`nonempty_isCMByRamifiedMaximalOrder_geomPoint_mazurLevel`,
`Fermat.exists_cmEndomorphism_of_mem_isolatedCMJInvariants`).  Every one of them
is a *theory build*, and here is exactly which theory is missing, so the next
agent does not spend its first hour rediscovering it:

* **No lattices in `ℂ`, no analytic `j`-function, no uniformisation.**
  `Mathlib/NumberTheory/ModularForms/` has Eisenstein series, `Δ`, the `η`
  function and `q`-expansions — and no `j`, and nothing relating a lattice to an
  elliptic curve.  So Cox's route 3(a) is not "cite mathlib", it is "build the
  theory".
* **No class group of a NON-MAXIMAL order.**  `ClassGroup` in mathlib is for
  Dedekind domains; `ℤ[√−n]` of conductor `> 1` is not one.  The form class group
  and the Cox Theorem 7.7 isomorphism do not exist either.
* **No Hilbert/ring class polynomial, no ring class field.**
* The ALGEBRAIC route (Silverman *ATAEC* II, `E ↦ E/E[𝔞]`) is gated inside this
  tree rather than by mathlib: it needs `Ideal (End W)`, hence a `CommRing`
  instance on `End W`, and `WeierstrassCurve.End.mul_comm_charZero` is an OPEN
  LEAF; it also needs quotients by finite subgroups, which this tree lacks.

**And one trap that looks like it should be free and is not.**  Galois-STABILITY
of "`x` is a CM `j`-invariant" — `IsCMJInvariant n x → IsCMJInvariant n (σ x)` —
would narrow two of those leaves considerably (with it, "there are two distinct
CM `j`-invariants" collapses to "one of them is irrational").  It is NOT
available: **mathlib's `WeierstrassCurve.Affine.Point.map` maps between BASE
CHANGES of one curve `W'` over a fixed base ring, along an `F →ₐ[S] K`.**  It
does not transport a curve over `ℚ̄` along a ring automorphism of `ℚ̄` to the
different curve `W.map σ`.  That transport, and with it the transport of
`IsIsogeny` (whose `IsRationalMap` certificate is a polynomial identity in
`veluPointX`/`veluPointY`, so it does conjugate — the mathematics is easy, the
API is absent), is a real ~200-line build in `Isogeny.lean`.  Price it before
promising it.

**What IS free, and was harvested 2026-07-31**: over `ℚ̄/ℚ`, `∃ σ, σ x = y` and
`minpoly ℚ x = minpoly ℚ y` are interchangeable in one line —
`Normal.minpoly_eq_iff_mem_orbit` (`Mathlib/FieldTheory/Normal/Basic.lean`).
Any CM leaf phrased with a `Gal(ℚ̄/ℚ)`-orbit should be restated with minimal
polynomials, where the arithmetic is visible and the bookkeeping is gone.

## A LEAF CAN CONTAIN ANOTHER LEAF — count what the STATEMENT forces, not what the proof needs

(2026-07-31, found while auditing three `ModularCurve/X0.lean` leaves.) Every leaf in this tree
carries a `WHAT IS MISSING` inventory. **That inventory is a hypothesis about the intended proof,
and it can be silently incomplete** — because it lists the theory the author had in mind, while
what the leaf actually owes is fixed by its STATEMENT.

`exists_isWeilEigenvalues_isEichlerShimuraTransform_x0` listed exactly one missing input, the
Eichler–Shimura congruence relation. Unfolding its two conjuncts and counting cardinalities shows
it also CONTAINS `finrank_cuspForm_eq_x0Genus`, a separate open leaf 700 lines below it in the
same file: `IsEichlerShimuraTransform` forces `card {nonzero entries of β} = 2 · card a` (pair
entries have product `ℓ ≠ 0`, so none is zero), `IsWeilEigenvalues` forces that same count to be
`2g`, and `IsCharRootMultiset` forces `card a = finrank` (two polynomial functions agreeing at
every `c ∈ ℂ` are the same polynomial, so the degrees match). Hence `finrank = g`. An owner sent
at the first leaf with only Deligne–Rapoport in hand reaches the last step and cannot finish.

**The technique, which is cheap and general:** for a leaf whose datum is an existential over a
structured predicate, unfold each predicate and count what it pins — cardinalities, degrees,
supports, which entries are forced nonzero — on both sides of the conclusion. Where two
independent predicates pin the SAME quantity, their agreement is an equation the leaf asserts,
and that equation may be somebody else's leaf.

**Why nothing else catches it.** It is not a sorry, not an error, not an unimported module, not a
release-window artefact. The two leaves are in one file, both visible to `lake build`, both in the
census, neither owned by the other's owner. The dependency exists only in the mathematics of the
two statements, so only reading them together reveals it — and the frontier scan that builds task
lists reads them apart. **Dispatch order matters when it is found: prove the contained leaf first,
or the two together, and never send one owner at each.**

Corollary for the `WHAT IS MISSING` convention: treat those lists the way this file already tells
you to treat "still open, owned elsewhere" claims — as a hypothesis to check, never a fact. Adding
a found dependency to the docstring is worth a commit on its own; it is the only place the next
owner will look.

## A BLOCKED LEAF'S DOCSTRING USUALLY NAMES THE CUT THAT UNBLOCKS THE *GLUE* — take it

(2026-07-31, `flt-lean-205`, on `smoothLocus_pairSquareMap_le` in `X0.lean`.)

That leaf carried a careful pin audit ending "a worker sent here should expect to build a
theory", and the audit was RIGHT: the mathematics it needs is descent of formal smoothness
along a faithfully flat map, which mathlib records as an open `proof_wanted`
(`Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat`, needing
Raynaud–Gruson, Stacks `058B`). Re-checking the pin confirmed all three routes are absent —
the scheme-level `DescendsAlong @Smooth …` descends along a base change of the TARGET and not
of the SOURCE; the `Algebra.IsSmoothAt.of_formallySmooth_fiber` route reduces to formal
smoothness of a fibre over a field, and the only such statement in the pin
(`Algebra.FormallySmooth.of_perfectField`) is about a field EXTENSION, so even
characteristic zero does not shortcut it.

**But the same docstring's last paragraph named, in one sentence, the general lemma that
would discharge everything else** — "prove `p` flat, `x ∈ (p ≫ g).smoothLocus` ⟹
`p x ∈ f.smoothLocus` once, and `⊆` follows". Cutting exactly that out took two compiles and
about forty lines, and the leaf became PROVEN. The frontier count is unchanged (−1 here, +1
there) and that is not the point:

- the residual leaf is now **mathlib-shaped and reusable** — it is Stacks `02VL` at one point,
  stated for arbitrary schemes, and it will be discharged by a mathlib bump or by one
  ring-theory worker, whereas the old leaf could only be discharged by someone who also
  understood `pairSquareMap`;
- the **project-specific glue is gone for good**. Composition of `FormallySmooth` stalk maps,
  which projection is smooth and which is flat, the instance juggling for base changes of
  `Smooth af` — none of that was mathematics, all of it was work, and none of it has to be
  redone by whoever proves the real theorem;
- the audit stops being re-derived. It moved WITH the leaf, so the next owner reads it where
  the sorry is, not two files away.

**So the standing move on a "needs new theory" leaf is: before concluding it is a cost wall,
read its own docstring for the reduction it proposes, and if it proposes one, TAKE it.** A
leaf whose author bothered to write "the cheapest honest reduction is X" has done the design
work already; leaving X uncut wastes it, and every later owner pays the glue again.

Two smaller things from the same task, both measured:

- **Land the cut in an EXISTING mathlib-facing project module if one is already publicly
  imported by the target.** `Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothLocusPerfect.lean`
  is 122 lines, imports only `Morphisms/{Smooth,Flat,FinitePresentation}`, and `X0.lean`
  already `public import`s it. So the cut cost ZERO new imports, zero import-position risk,
  and the helper elaborates in seconds instead of inside an 81 000-line file.
- **To test an edit to a giant file, MOCK the giant file's definitions as opaque variables.**
  The X0 proof was verified before touching X0 by a scratch importing only the helper module,
  in which `pairSquareMap u hu` was replaced by a variable `F : pullback af af ⟶ pullback bf bf`
  and `pairSquareMap_fst/_snd` by two hypotheses of the same shape. That checks the only things
  that can actually fail — instance resolution for the base changes, and whether the general
  lemma's implicit arguments match — in ~30 s rather than in a full rebuild. It is the
  "stub the siblings" trick applied to the target's own DEFINITIONS rather than to its
  neighbours. (It still proves nothing about the target's import surface or token scope; do
  the one real build.)

## AN "UNUSED" FIELD OF A *PRODUCED* STRUCTURE CAN BE LOAD-BEARING THROUGH A SIBLING FIELD

(2026-07-31.) The cheapest-looking way to close a leaf is to show nobody needs it. For a datum
structure that the leaf PRODUCES, the natural check is to grep the consumers of the field the leaf
supplies — and that check can give a confident wrong answer.

`X0.lean`'s `card_compl_range_le_card_divisors` exists only to supply the `⊇` half of
`IsX0Compactification.CuspLocus.cover`, and no consumer of `cover` reads that half: the one
derivation that touches it, `nonempty_cuspIndexing_of_cuspLocus`, uses `⊆` only, and both
docstrings say so. The leaf still cannot be dropped. The surjectivity is spent in the PRODUCER,
`nonempty_cuspLocus_of_residueIndexing`, proving a DIFFERENT field of the same structure —
`ratPoint`, which is obtained by transporting a free theorem along `e.symm` and so needs `e` onto.
`ratPoint` then has a live reader two files away.

So the ownership question for a produced datum is not "who reads this field" but **"what else in
the producer's proof is spent on it"**. Read the producer, not only the consumers.

## A FAITHFULNESS AUDIT'S "IT IS CHEAP WHEN …" WITNESS IS ITSELF A PROOF OBLIGATION

(2026-07-31.) Audits in this development routinely end with a cheap case — "this structure is easy
to satisfy when `A` is finite; here is the witness" — and that clause is doing real work: it is the
evidence that the leaf is not asking a producer for MORE than the mathematics supplies. It is also
the clause nobody checks, because it reads like a reassurance rather than a claim.

`CubeModel`'s (`Fermat/FLT/Mathlib/NumberTheory/ProjectiveHeight.lean`) said "cheap exactly when
`A(ℚ)` is finite — `dim = 1`, `coords ≡ ![1]`, `cube = z`, `relDim = 0`". Two of its four
components are wrong, and both understate the witness: a CONSTANT `coords` satisfies
`injective_of_smul` only for a SUBSINGLETON group (take `c = 1` and the field forces `P = Q` for
every pair), and `z` is homogeneous of degree `1` where `cube_homogeneous` demands `2`. The claim
is true — an indicator witness works — but the recipe as written supported a far weaker statement
than the one it was cited for, and it had been copied verbatim into the audit of the leaf that has
to produce the structure (`nonempty_cubeModel_of_isAmpleSheaf_cube`).

Check the cheap case field by field against the structure, the same way you would check a
counterexample. It costs minutes, it is the half of an audit that can be checked without the
literature, and a wrong one propagates by quotation.

## THE TASK PROMPT'S LINE NUMBERS ARE A CHECKSUM ON THE WORKTREE, AND THEY CAUGHT A 704-COMMIT STALE ONE

(2026-07-31, `flt-lean-16`.) The prompt named three leaves in `X0.lean` at lines 34356,
34410, 34514. `grep` found the first two at 29033 and 29074 and the third **not at all**.
The worktree was on `9a2ca10d` — an ancestor of `main`, **704 commits and 92k lines
behind**, with `X0.lean` 17706 lines shorter than the one the task was written against.
`git status` was clean, the branch was a proper ancestor, `lake build` was green: by every
check an agent naturally runs, the worktree looked fine. It was simply *old*.

Nothing in the dispatch says this can happen. `CLAUDE.md`'s own dispatch section says a
worktree fast-forwards to `main` at dispatch, and the loop's `flt-cycle.py release` phase 1
advances every worktree — so an agent that trusts either statement will edit a file whose
declarations have moved, whose neighbours are missing, and whose `sorry` set is a snapshot
of some earlier release. Every one of the five invisibility classes above then fires at
once, and the resulting work is unmergeable rather than merely wrong.

**So make this the first thing you do, before reading the target file:**

    grep -n '<the target name>' <the file>        # must land ON the prompt's line number
    git log --oneline -1 main; git rev-list --count HEAD..main

A line-number mismatch of more than a few lines is not "the file drifted" — it is a stale
checkout until proven otherwise. `git rev-list --count HEAD..main` is the one-command
version and costs nothing. The repair is `git merge --ff-only main`, plus reseeding
`.lake` from the release snapshot (`rsync -a --delete ~/.flt-release-lake/build/
/scratch/chend-flt/flt-lean-N/.lake/build/`) — 2.3 G, about a minute, and without it the
first `lake build` rebuilds a large part of the tree against a mismatched olean set.

A leaf named in the prompt that does **not** appear in the file at all (here
`exists_gamma0GITPresentationOver_normalModuli_zmod`) is the loudest form of this signal.
Do not conclude it was renamed or already closed; check the freshness first. Both readings
lead to a sentinel reporting "already done", and one of them is a lie.

## `lake` IS NOT ON `PATH` IN A NON-INTERACTIVE SHELL — AND THE FAILURE LOOKS LIKE A BUILD

Same run, same day. A backgrounded `lake build … > log; echo EXIT=$? >> log` produced

    timeout: failed to run command 'lake': No such file or directory
    EXIT=127

The harness's Bash tool initialises from the user profile for *interactive* use, but a
backgrounded compound command got a `PATH` of `/home/chend/node/bin:/usr/local/sbin:…`
with no `~/.elan/bin`. `git` worked, so the shell was clearly functional; only `lake` was
missing. Combined with the doctrine above — *never conclude a build succeeded from the
absence of errors* — note the mirror-image hazard: a 4-line log with no `error` in it and
`EXIT=127` is not a fast clean build, it is a build that never started.

    export PATH=$HOME/.elan/bin:$PATH        # first thing in every lake invocation

The existing memory `flt-ssh-build-needs-cd-and-elan-path.md` records this for `ssh`
invocations. It bites identically for a plain local background Bash call on the owning
host, which is the shape the post-2026-07-30 loop makes agents use most.

## SPECIALISING A LEAF TO ONE CANONICAL BASE CAN MAKE IT HARDER — check the citation's own proviso

(2026-07-31, `flt-lean-19`.) A cut that replaces "for every `R`" by "at the one canonical `R`"
reads as a strict improvement, and the tie-breakers above endorse it: same leaf count, one
instance instead of a family, and "a citation instantiated once is what the citation IS". That
reasoning is right whenever the citation applies at the chosen base. **It is exactly backwards
when the chosen base is the one where the citation's own hypotheses fail.**

`nonempty_gamma0AtlasOver_specLoc` (Katz–Mazur (8.1.1), the `Γ₀(N)`-atlas) was specialised on
2026-07-29 from "every `R : Subring ℚ`" to `ℤ`, with every other subring recovered by flat base
change — `ℤ → R` is flat for all of them, so the derivation is four lines and the cut looks free.
But Katz–Mazur construct `M(𝒫)` under an explicit proviso — *"to define `M(𝒫)` as an `R`-scheme it
suffices to do so locally on `R`, so we may assume some integer `n ≥ 3` is invertible in `R`"* —
and `ℤ` is the **unique** subring of `ℚ` where no `n ≥ 3` is invertible. Every other base
satisfies the proviso outright. So the specialisation silently folded a two-chart Zariski gluing
of the ENTIRE atlas (`Y`, the classifying map, the fppf cover *and* the categorical quotient,
over `D(3)`, `D(5)`, glued along `D(15)`) into a leaf whose docstring still described it as the
citation. The leaf's own text even named the gluing — "where the whole cost of a non-local base
sits" — without drawing the conclusion that this made the leaf strictly harder than the family it
replaced.

Two rules come out of it, and the second is the transferable one.

**1. Before specialising to a canonical instance, check the source's hypotheses AT that instance.**
"Every base is a flat base change of `B`" makes `B` a sufficient base *logically*; it says nothing
about whether the theorem you are citing is proved at `B`. Degenerate/extremal bases — `ℤ`, a
field of small characteristic, `N = 0`, the trivial group — are exactly where citations carry
provisos, and they are exactly the bases a "one canonical instance" argument selects for.

**2. A hypothesis the CONSUMERS already hold costs nothing, and this is worth checking BEFORE
inventing machinery to avoid it.** The repair here was to give the leaf Katz–Mazur's own proviso
(`∃ n ≥ 3, IsUnit (n : R)`) and thread it through three intermediate theorems that lacked `ℓ` in
scope. Every terminal consumer already carried `IsReductionBase ℓ R toF`, which forces `R = ℤ_(ℓ)`
and hence supplies the proviso (`n = 3`, or `4` at residue characteristic `3`) — so the leaf got
strictly weaker and no consumer's statement changed. Same shape as
`exists_artinDivisorNormIndex_le_ray_class` above: *the missing hypothesis is usually already in
the caller's hand, and the reason it is not in the statement is that an intermediate theorem
discarded it.* Trace the consumer chain to its terminal hypotheses before concluding a leaf must
be stated in the generality it currently is.

Corollary for the generality question in general: the right test is not "which statement is more
canonical" but **"at which bases is the cited proof actually run"**. Quantifying over a family of
bases where the citation applies is CHEAPER than one base where it does not, however inelegant the
family looks.

## A REDUNDANT PRINTED COLUMN IS THE ONLY DRIFT GUARD A COMMENT CAN HAVE

(2026-07-31, same run.) `x0HeckeCharpolyTable`'s docstring prints a human-readable table beside
the `def`, including three columns — `Tr`, `ℓ+1−Tr`, `det((ℓ+1)−T)` — that are NOT stored and are
computed from the polynomial by proven lemmas. Its `N = 75` row printed `X⁵ − 9X²` while the
banked list `[0,0,0,-9,0,1]` is `X⁵ − 9X³`.

The `def` was right and the prose was wrong, and the redundancy is what proves it **without any
external tool**: the same row prints `det = 28160`, and `8⁵ − 9·8³ = 28160` while
`8⁵ − 9·8² = 32192`. Two printed columns that must agree, disagreeing.

The general point: a `decide`-backed drift guard (`x0Genus_eq_of_mem_x0HeckeCharpolyTable`,
`exists_charpolyRow_of_x0WitnessTable`) breaks the BUILD when data drifts, which is why this
development uses them. **A docstring table is a comment; nothing checks it, and it is read far more
often than the `def`.** So when banking numerical data, print the derived columns too — they cost
nothing and they are the only thing standing between a typo and a prover chasing the wrong
polynomial. And when reading such a table, cross-check a derived column before trusting a row; a
CAS run is confirmation, not the first line of defence.

## A char-`p` leaf blocked by an "imperfect base": two dodges that keep working

(2026-07-31, closing `InvariantCoarseRing.lean`'s last leaf, which its own docstring had
declared needed "new mathematics — a separability / linear-disjointness argument over
`k(ι)^{1/p^∞}`". It needed neither.)

* **`[PerfectField k]` in a lemma is almost always a proxy for "the extension at hand is
  separable".** Replacing it by `[Algebra.IsSeparable k A]` breaks NO existing call site —
  `Algebra.IsAlgebraic.isSeparable_of_perfectField` is an instance, so a caller with
  `[PerfectField k]` in scope still elaborates unchanged — and it buys the characteristic-`p`
  case, where the base has been enlarged to something imperfect (here `Fk = k(ι)`, a rational
  function field) but the extension being tensored is still separable. The separability then
  has to come from somewhere: for a finitely generated extension of a perfect field mathlib
  now has it, `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`
  (`Mathlib/FieldTheory/SeparablyGenerated.lean`, 2025 — separating transcendence bases).
  **A "this needs new mathematics" verdict written months ago is a hypothesis about the PIN,
  and the pin moves.** Grep mathlib before believing it.

* **A hypothesis that fails only over FINITE fields — `[Infinite k]`, which every
  evaluate-at-`k`-points / specialisation argument carries — is dodged by base-changing to
  `k̄`, not repaired.** `k̄` is infinite and perfect whatever `k` was, and is trivially
  algebraically closed in every extension of it, so the hard theorem only ever runs over `k̄`:

      L ⊗[k] K  ↪  L ⊗[k] Ω  ≅  (k̄ ⊗[k] L) ⊗[k̄] Ω  ↪  Frac (k̄ ⊗[k] L) ⊗[k̄] Ω

  with `Ω` any algebraically closed field over both `K` and `k̄` (take `AlgebraicClosure K`).
  The two injections are flatness over a field; the middle iso is
  `Algebra.TensorProduct.cancelBaseChange`. The ONLY new input is that `k̄ ⊗[k] L` is a
  domain — which is the ALGEBRAIC half of the same theorem, already in hand. The same shape
  applies to any "geometric" statement whose proof needs an infinite (or algebraically
  closed) base: prove it over `k̄` and descend by flatness.

## "The base is not a UFD" is usually a statement about the base you happened to pick

(2026-07-31, `Universal.idl_isPrime` in `ProjectiveEquationAdd2.lean`.) That leaf carried a
carefully-written docstring laying out a two-step tower `Poly ⧸ idl ≅ (B[Px] ⧸ (f₁))[Qx] ⧸ (f₂)`,
proving step 1 by primitivity, and stopping at step 2 with a named obstruction:

> `f₂` is irreducible over the domain `C = B[Px] ⧸ (f₁)`. This half is the real work: **`C` need
> not be a UFD, so the primitivity argument is unavailable.**

The obstruction is real and the sentence is true. It is also **removable by inverting one
variable**, and nothing in the docstring's own data hid that: `f₁` has degree `1` in `a₆` with
coefficient `Pz ^ 3` — the very fact step 1 used to prove `f₁` primitive. Degree one in `a₆` means
that once `Pz` is inverted the relation *solves* for `a₆`, so `C[1/Pz]` collapses back to a
localised polynomial ring, i.e. **a UFD**, and step 2 becomes the same easy primitivity argument as
step 1. The leaf then splits into "prime after inverting `Pz`" plus "`Pz` is a non-zerodivisor mod
the ideal", the second of which needs no primality at all — only uniqueness of division by a monic
polynomial, twice.

The general shape, and why it is worth a standing note: **a quotient by a relation that is degree
`1` in some variable is a graph, not a hypersurface, on the locus where that variable's coefficient
is invertible.** So before accepting "not a UFD / needs new theory" about `R[x]/(f)`:

1. find a variable in which `f` has degree `1`;
2. invert its leading coefficient — the quotient becomes a localisation of a polynomial ring;
3. prove the statement there, and contract back with a non-zerodivisor (saturation) lemma, which is
   normally the *easy* half because the generators are monic in disjoint variables.

Two smaller findings from the same leaf, both worth reusing:

* **Degree-one primitivity is already in mathlib and does not need Gauss's lemma.**
  `Polynomial.irreducible_C_mul_X_add_C : a ≠ 0 → IsRelPrime a b → Irreducible (C a * X + C b)`
  (`Mathlib/Algebra/Polynomial/RingDivision.lean`). `IsRelPrime` *is* the primitivity check.
* **The cost of these leaves is bookkeeping, not mathematics.** All of it sat in viewing
  `MvPolynomial (Fin 11) ℤ` as `B[Px][Qx]` through `renameEquiv`/`finSuccEquiv`. When that fight
  starts, the move is to re-present the universal ring as `B[Px][Qx]` **by construction** rather
  than to win the fight — the surrounding development only ever uses `spec`, so how the ring is
  presented is free to change.

## A "DO NOT SHUFFLE THIS SORRY AGAIN" note is about ARITY, not vocabulary

(2026-07-31, `IsogenyTrace.lean`.) Seven passes moved that file's single `sorry` around a
circle of mutually equivalent statements about the degree of an isogeny — `deg = det` on the
`ℓ`-torsion, the characteristic polynomial, the shift expansion, the parallelogram law, Weil-pairing
adjointness. The file then wrote, correctly, "the two statements are **equivalent**, so nothing is
gained or lost by moving between them, and a future pass should not shuffle them again." Every one of
those restatements really was a lap of the same circle.

The eighth pass found a genuine move anyway, and the discriminator generalises: **every member of the
circle quantified over a PAIR** — two endomorphisms `(φ, ψ)`, or an endomorphism and a prime `(ψ, ℓ)` —
**and the new target quantifies over ONE.** The whole parallelogram law
`deg(φ+ψ) + deg(φ−ψ) = 2 deg φ + 2 deg ψ` follows, unconditionally, from its single instance `φ = 1`,

    deg(χ + 1) + deg(χ − 1) = 2 deg χ + 2,

by a second-order recurrence in `m` for `deg(χ + [m])` and then multiplication by `φ̂`, which converts
the pair `(φ, ψ)` into the pair `(φ̂ψ, [deg φ])`. That is not a lap: the hypothesis mentions no second
endomorphism, no prime, no module, no determinant and no pairing, and it is the shape the classical
`x`-coordinate degree count actually produces, since that count runs one endomorphism at a time.

**So before accepting an "equivalent, do not shuffle" verdict, count the binders on each form.** A
restatement that keeps the arity is the lap the note is warning about; one that drops it is a
reduction, and the note does not cover it. Record the arity when writing such a note, so the next pass
can tell which it is holding.

**Corollary, from the same pass: an "irreducibility" audit is only as wide as the axis its author
searched — and the axis is usually the one the counterexample lives on.** That file's `ℤ[√2]`,
`q := |N|` model shows the five available facts about `deg` cannot give the parallelogram law, and it
is correct. It was checked here against two further facts it does not cover, and it survives both:
`End W` is in fact COMMUTATIVE in characteristic zero — the differential character
`λ : End W → F` of `DifferentialCharacter.lean` is an injective ring homomorphism, so the comment on
`IsogenyTrace.lean`'s `Mathlib.Tactic.NoncommRing` import ("`End W` is a NONcommutative ring") is
mathematically false — though the import must STAY, since no `CommRing (End W)` instance is registered
and `ring` cannot know — and the dual is an involution with `deg ψ̂ = deg ψ`. `ℤ[√2]` has both. What it does
*not* have is a finite unit group, and `{ψ : deg ψ = 1} = Aut W` is finite; so **finiteness of `Aut W`
is a candidate substitute for the missing geometric input**, and it is the only one that pass found.

## A DOCSTRING'S ROUTE CAN NAME A STEP THAT IS IMPOSSIBLE — AND THE LEAF STILL TRUE

(2026-07-31, `exists_lowerRamificationData_phi_one_le`.) The leaf's own docstring ended with a
"WHAT A PROVER MUST NOT DO" paragraph that prescribed the elementwise contradiction and closed:
*"it needs `X` to have `L`-valuation exactly `1` — which is where the 'totally ramified' half of
the construction is actually consumed."* That sentence is wrong twice over, and each way is a
different trap:

* **Not achievable.** The level `L` is constrained from below — it must contain the fixed field of
  the *prescribed* open subgroup `N`, whose ramification index may be divisible by the residue
  characteristic. `v_L(π^{1/M}) = e(L/Kᵥ)/M` then cannot be `1` for any `M` prime to `ℓ`. A prover
  who takes the sentence at face value spends the task trying to arrange something no choice of
  `M` can arrange, and is one step from reporting the leaf FALSE.
* **Not needed.** Generalising the elementwise lemma from "a uniformizer" to "`x = unif ^ e * u`
  with `u` a UNIT" makes the exponent `e` irrelevant: the correction factor `(1 + unif·a)^e` is
  `≡ 1 mod unif` whatever `e` is. The obstruction lived entirely in the route.

**The discriminating question, and it is cheap: is the awkward requirement forced by the
STATEMENT, or only by the ROUTE the docstring happens to describe?** Here the statement never
mentions a uniformizer; only the sketch did. Docstrings in this development are written by whoever
CUT the leaf, from the argument they had in hand — they are a hypothesis about how to prove it,
carrying exactly as much authority as a rival cut would. FALSITY AUDITS still outrank you (a
statement claim); a route sketch does not (a proof claim).

Corollary, generalisable beyond this file: **when an elementwise argument seems to need an element
of exact valuation `1`, try the normal form `x = unif ^ e * u` instead.** That factorisation is
available from the `LowerRamificationData` axioms alone (`unif_spec` strips factors,
`eq_zero_of_forall_pow_dvd_integralClosure` makes the stripping terminate), and it is the honest
formal shape of the classical step "`σ ∈ G₀` acts trivially on the residue field, so the unit
cofactor contributes nothing". It is now
`LowerRamificationData.exists_unif_pow_mul_isUnit`.

## A PROVER CAN DECLINE ITS OWN RIVAL CUT — do it on your branch, not in the merger's lap

(2026-07-31, `flt-lean-238`. All THREE targets of one task were already closed on `merger`; the
check that found it cost one command and ran before any Lean was written.)

The release-window section above says `main` is not the frontier. This is the prover-side
consequence, and it has two halves that are learned separately.

**First: test SORRIEDNESS, not PRESENCE.** The obvious check —
`git show merger:<file> | grep -n <name>` — is necessary and, on its own, actively misleading
when the leaf was DECOMPOSED rather than proven. A decomposed parent **keeps its name and its
line**, so the grep hits either way; what changed is that its body is now a one-line call to a
NEW leaf with a DIFFERENT NAME that no scan keyed on your target can find. Two of the three
targets here were exactly that:

    exists_riemannRochGrowth_of_isProperSmoothCurve       -> exists_riemannRochGrowth_of_pointCountRecursion
    exists_planeModel_birationalOver_of_isProperSmoothCurve -> exists_planeModel_ringEquiv_functionField_of_isProperSmoothCurve

Both parents are PROVEN on `merger` and still `sorry` on `main`. So run the comment-stripping
attribution scan — `flt-frontier.py`'s `scan()` — against the *merger copy of the file*, not a
grep:

    git show merger:Fermat/FLT/.../File.lean > /tmp/m.lean
    # then flt-frontier.py's scan() on /tmp/m.lean; a name absent from its output is PROVEN there

**Second: when the collision is a genuine rival PROOF, decline it yourself.** The third target
had been proven on this branch by an elementary integral-matrix bijection (492 new lines, four
new lemmas) and independently on `merger` through Petersson self-adjointness (zero new
declarations, reusing analytic machinery the file already had). Both sorry-free. Two proofs of
one theorem cannot both be carried, so one had to go, and the file's own tie-breakers — fewer
new declarations, already integrated and consumed by neighbours — both pointed at `merger`'s.

Handing that to the merge worker as a conflict is the worse option, and not only for its time.
The four helper lemmas sat ~280 lines ABOVE the theorem, far enough that git merges them
CLEANLY while conflicting only on the theorem body — so resolving the visible conflict to
`merger`'s side leaves four FREE-FLOATING lemmas behind and no error to notice them by. That is
the interface-split hazard of class seven, arriving through a rival cut instead of a signature
change.

The recipe, and it is three commands:

    BLOB=$(git diff <base> <yourcommit> -- <the file> | git hash-object -w --stdin)
    git tag flt-lean-N-superseded-<what> "$BLOB"
    git checkout main -- <the file>          # decline; NOT `git revert`, which fights the merge

Then **verify the round trip before you commit** — `git show <tag> > /tmp/p.diff &&
git apply --check /tmp/p.diff` must pass against the declined tree. It will FAIL against the
undeclined one, which is the expected reading and not a broken tag.

What this buys: your branch merges trivially, the decline is recorded permanently in a commit
message rather than in a merge nobody re-reads, and the superseded proof stays recoverable in
the shared object store where it conflicts with nothing. A second independent route to a closed
node is an asset — downstream consumers are not hostage to whichever proof survives — so say in
the report that it exists and name the tag; it just must not be a second DECLARATION.

## A HYPOTHESIS SET THAT ONLY *BRACKETS* A VALUE CAN STILL PIN IT — MULTIPLY AND TAKE A LIMIT

(2026-07-31, `Interface.lean`'s Stickelberger cluster.) `exists_valuationExtension_of_liesOver`
hands its consumers a valuation `v` carrying exactly ONE arithmetic axiom,
`z ∈ q^N ↔ (ℓ−1)·N ≤ v z` on `𝓞 CF`. The reflection half of Stickelberger needs
`v(ℓ) = ℓ − 1` on the nose. Reading the axiom off at `N = 1` gives only `≥`, and the
axiom genuinely does not determine `v(ℓ)` pointwise: it brackets it inside
`[(ℓ−1)e, (ℓ−1)(e+1))` where `e = v_q(ℓ)`, and that is ALL a single instance of it says.

The obvious conclusions — "this leaf is under-specified", "the producer must be strengthened
to export `v(ℓ)`", "we need ramification theory here" — are all wrong, and each would have
cost a signature change across a producer, a leaf and a consumer.

**What closes it is that the axiom can be instantiated INFINITELY OFTEN and `v` is
multiplicative.** `v(ℓ^k) = k·v(ℓ)` against `ℓ^k ∉ q^{k+1}` gives `k·v(ℓ) < (ℓ−1)(k+1)` for
EVERY `k`, i.e. `v(ℓ) < (ℓ−1)(1 + 1/k)`, and the `k → ∞` limit collapses the bracket to a
point. Ramification theory enters only to supply `ℓ ∉ q²` — one instance, at `k = 1`; the
rest is Archimedes.

**The general shape, and it is worth checking before ANY "the hypotheses are too weak"
verdict:** when a hypothesis bounds a quantity within an interval rather than fixing it, ask
whether some structure map (multiplicativity, additivity, a group action) lets you apply the
same hypothesis to `x^k`, `k·x` or `gx` and divide back. A bracket of fixed WIDTH around a
quantity that scales linearly is a bracket of width `→ 0` around the quantity itself. The
failure mode this avoids is real and expensive: strengthening a producer's conclusion to
export something its existing conclusion already implies.

### Three Lean traps measured in the same session

* **`Ideal.Quotient.field` is a `def`, not an instance.** Supplying `[q.IsMaximal]` does NOT
  make `Field (R ⧸ q)` synthesisable; mathlib itself writes `attribute [local instance]
  Ideal.Quotient.field`, and in a proof the idiom is
  `letI : Field (R ⧸ q) := Ideal.Quotient.field q` (`letI`, not `haveI` — see the existing
  rule about `haveI` making a `Field` opaque). The confusing symptom is not the honest
  `failed to synthesize Field (R ⧸ q)`; it is a **`(deterministic) timeout at whnf`** inside a
  lemma whose statement carries `[Field R]` — the elaborator burns its budget trying to see
  the `CommRing` through a structure it cannot find.
* **`WithTop ℚ` is not a semiring, so `nsmul_eq_mul` does not fire in it** — and `push_cast`
  will cheerfully push a coercion INWARDS and strand the goal as `n • x = ↑n * x` *at the
  `WithTop` level*, where both `rw [nsmul_eq_mul]` ("pattern not found") and
  `simp [nsmul_eq_mul]` ("no progress") fail on a goal that visibly matches. Descend with
  `congr 1` to the `ℚ` level FIRST, then `push_cast; ring`. The lesson generalises to any
  `WithTop`/`WithBot`/tropical target: get out of it before doing ring arithmetic.
* **Prefer `Nat.card` lemmas to `Fintype.card` ones whenever an instance was introduced by
  hand.** `Fintype.card_units` failed to rewrite a goal about `Fintype.card (R ⧸ q)ˣ` because
  the ambient instance came from `haveI := Fintype.ofFinite _` rather than from
  `instFintypeUnits`; `Nat.card_units [GroupWithZero α] : Nat.card αˣ = Nat.card α - 1` has no
  instance argument to mismatch and closed it immediately. Two `Fintype` instances on one type
  are propositionally equal and syntactically different, which is exactly the gap `rw` cannot
  cross.

**ADOPT THE RIVAL'S SPLIT POINT — copy its statement VERBATIM and contribute only the body**
(2026-07-31, flt-lean-290). All three leaves of one task were already proven on `merger` when the
worker started; the queue had been written against a `main` that was 480 commits behind. Two of the
three were straight duplicates and were dropped. The third was the interesting case, and it
generalises:

`merger` had split `exists_mem_hilbertInertiaOutsideSubgroups_resSubgroup_eq_zero` into a cocycle
half (`…_eval₁_eq_zero`, left `sorry`) plus a one-line cohomological consumer. This worktree had
independently proven the WHOLE of that cocycle half except a uniform Hermite–Minkowski bound — i.e.
its work was exactly the body of the rival's open leaf. Neither "decline mine" nor "decline theirs"
was right: the reconciliation is to **take the rival's name and signature as authoritative, paste
your proof into it, and make your copy of the shared consumer byte-identical to theirs.** The merge
then has nothing to choose — one side is a pure insertion, the other is unchanged.

The general rule, and it is cheaper than it sounds: when you find the node already cut elsewhere,
diff the two cuts and ask *which half of theirs do I already have*. A statement copied verbatim from
the incumbent costs nothing and converts a guaranteed conflict into a no-op; a statement you prefer
for aesthetic reasons costs the merger a decision it has no author to make. Say in the docstring
that the signature is inherited and why, so the next reader does not "fix" it back.

Corollary for the DROPPED halves: a duplicate proof does not merely lose, it *poisons*. This
worktree's rival proof of `cyclotomicCharacter_map_map_eq_one_of_mem_localInertiaGroup` came with
five new general-`K` helper declarations sitting in a NON-conflicting region. Resolving the theorem
to the incumbent's body would have left those five behind as free-floating declarations — class-7's
interface split, in the shape of dead code rather than broken code. Revert the whole payload
(`git apply -R` of your own commit's hunks), not just the colliding declaration.

## `set_option … in` GOES BEFORE THE DOCSTRING, NOT BETWEEN IT AND THE DECLARATION

(2026-07-31.) `/-- doc -/ set_option maxHeartbeats 2000000 in theorem foo …` does not parse:
`unexpected token 'set_option'; expected 'lemma'`. The doc comment must be immediately followed by
a declaration keyword, so the modifier belongs ABOVE it:

    set_option maxHeartbeats 2000000 in
    /-- doc -/
    theorem foo …

Trivial, and it cost a full 40-minute build of a 25 000-line module to discover, because the
elaborator reaches the syntax error only after loading the whole import cone. Cheap insurance: after
inserting any `set_option … in`, grep the file for `-/$` immediately preceding it.

## `∃ n, ∀ z` DOES NOT MEAN `n` IS UNKNOWN UNTIL `z` IS SEEN

(2026-07-31, flt-lean-290.) A leaf's own docstring argued at length that it needed a SECOND,
independent Hermite–Minkowski input, and named the sibling leaf it could not use:

> *"It is NOT supplied by `finite_hilbertInertiaOutsideSubgroups`. That leaf bounds the NUMBER of
> subgroups of index `≤ n` for a GIVEN `n`; here `n` is what is being produced, and no amount of
> counting at a fixed level yields it. … neither implies the other."*

Every clause is wrong, and the whole leaf then fell to one page. **`n` was not what was being
produced.** The thing that must not depend on `z` is the BOUND; the LEVEL at which the counting leaf
gets invoked is free to be any quantity computable from the ambient data. Here `d = N₁.index` and
`p = ringChar k` are fixed by `ρbar` and `k` alone, so `(d·p)!` is such a level — and at that level
the sibling leaf is exactly strong enough, because `⨅ {C : C in that finite set}` is one subgroup,
independent of `z`, that every admissible cocycle dies on.

The general shape, worth checking whenever a `∃ n, ∀ x` leaf is called ATOMIC: **list what is fixed
before `x` is quantified.** In this development that is almost always more than it looks — the
representation, the base field, the finite set of places, the residue characteristic, and every
invariant of them. A "uniform in `x`" obligation is discharged by ANY construction from that list,
not only by one that visibly ignores `x`.

Two corollaries the same day. First, and this is the same family as
[[flt-leaf-cost-estimates-are-hypotheses]] and [[flt-inventory-audits-understate-what-exists]]: a
docstring paragraph saying "leaf A does not imply leaf B" is written by whoever CUT them, before
either was attempted, and is a hypothesis. Try the implication before believing the prose — even
when the prose is careful, cites the right objects, and was written by someone who had just read
both statements. Second: a leaf whose docstring says "the section has TWO Hermite–Minkowski leaves,
best given to one owner" is a dispatch instruction built on that hypothesis, and it survives into
task prompts long after the hypothesis is refuted.

## `LinearMap`'s coercion does not fire inside a `Subgroup` structure instance — `AddMonoidHom`'s does

(2026-07-31, flt-lean-290.) With `letI : Module (ZMod p) M := AddCommGroup.zmodModule …` in scope
and `f : M →ₗ[ZMod p] ZMod p` in context, `f x` elaborates fine in an ordinary `have` and fails
inside

    set NB : Subgroup G := { carrier := {h | h ∈ N₁ ∧ f (e h) = 0}, one_mem' := …, … }

with `Function expected at f, but this term has type M →ₗ[ZMod p] ZMod p` — i.e. the `FunLike`
instance is not found, because it wants the `Module` instance and instance search does not reach a
local `letI` from inside a structure-instance field. The one-line fix is to carry the map as an
`AddMonoidHom` (`LinearMap.toAddMonoidHom`), whose `FunLike` needs no module structure; `map_add`,
`map_zero` and `map_neg` all still apply, so no proof changes. Do the conversion at the `obtain`,
not at the use site.

## A DECLARATION-ORDER BLOCKAGE IS DISCHARGED BY AN OPEN LEAF ABOVE, NOT BY A RELOCATION

(2026-07-31, `flt-lean-390`, and it closed `exists_x0GenusZeroJMapHauptmodul`.) A leaf whose
proof needs a theorem declared THOUSANDS OF LINES BELOW it reads as a restructuring job, and
`X0.lean`'s own docstrings said so twice: hoist the minimal closure, or split the `j`-theory
into its own module. Both are large edits to an 81 000-line file with a dozen concurrent
editors, so both stayed undone for days.

The cheap third option is to look for an **open leaf declared ABOVE you that PRODUCES the same
structure**. Here `exists_jSection` (`Nonempty IsJSection`, PROVEN) sits at line 27631 and is
unreachable; `exists_jSection_algClosModel` sits at 16010, is a `sorry`, and its existential
hands over an `IsJSection` — which is all the proof needed. Fifteen lines of `exists_jMap`
replayed against it, and the blockage is gone with nothing moved.

**The objection, and the accounting that answers it.** Citing a `sorry` to discharge a half that
is not open mathematics looks like trading one leaf for two. Check whether that leaf ALREADY has
consumers in your cone: `exists_jSection_algClosModel` had three, so the citation adds **no new
`sorryAx` edge** and the transitive cone is unchanged. The direct-leaf delta is then whatever
genuinely new leaf you cut, and nothing else. If the leaf has no other consumer the trade is
real and you should say so — but check before assuming it.

Two things this is NOT. It is not "open a local sorried copy of the theorem below" — that
manufactures a phantom leaf, and this file warns against it in those words. And it does not
retire the restructuring: the hoist or the module split is still worth doing, now for
elaboration time rather than to unblock a proof.

Generalises past this file: **before pricing a hoist, grep the region ABOVE you for a leaf whose
conclusion is `∃ x : <the structure you need>, …`.** Existential leaves are usually stated to be
consumed exactly once, so nobody thinks of them as a source of the structure they carry.

## AN "IT IS NOWHERE STATED" AUDIT MUST GREP THE FILE YOU ARE EDITING

(2026-07-31, `flt-lean-108`.) `Deformation.lean`'s obstruction leaf carried a machinery audit
saying `CompactSpace D.R` "is nowhere stated", with the refuting evidence spelled out: a grep of
`ProfiniteLocalNoetherian.lean` showing it takes `[CompactSpace R]` as a HYPOTHESIS throughout,
i.e. proves the converse direction. Every clause of that was TRUE about that file, and the
conclusion was false. `compactSpace_of_isAdic_of_pi` — exactly the wanted direction — sits **6800
lines above the audit IN THE SAME FILE**, and a proven theorem 4000 lines above it already contains
the one-line instantiation `compactSpace_of_isAdic_of_pi D.isAdic D.π D.π_surjective`.

An agent then proved a `HardlyRamifiedDeformation.compactSpace` wrapper against that audit and
verified it green before the original was found. It was a **duplicate of a one-liner, consumed by
nothing, hence free-floating**, and it had to be deleted rather than committed. Note both checks
that normally catch this were silent: it is not a duplicate NAME, so CLAUDE.md's class-7
duplicate-declaration scan does not see it, and it compiles perfectly.

Two rules, and the second is the one that generalises past this leaf.

- **Grep for the CONCLUSION, not for the file the machinery ought to live in.** Here that is
  `CompactSpace` applied to a deformation ring, across the whole tree. Grepping the plausible file
  and reporting what it contains is evidence about that file only.
- **Include the file you are editing.** These modules are 15–80k lines; "not in this module" is
  not something an author knows by having read it, and the audit that made this mistake was
  *written into* the file that refuted it. Search your own file first — it is the cheapest grep you
  will run and the one most likely to hit, because a leaf's machinery tends to have been built for
  its neighbours already.

Corollary for BUILD ORDERS in leaf docstrings: they are hypotheses, not facts, and a stale one
costs a whole dispatch. This one listed four bricks; the first did not exist as work at all. Price
each brick against the tree before dispatching an owner at it, and when a brick evaporates, say so
in the docstring **in place** — the deleted-wrapper story is why the audit was rewritten rather
than silently corrected.

## A LEAF STATED FOR *EVERY* REPRESENTING OBJECT CANNOT CONSUME ITS OWN CITATION

(2026-07-31, `RelativePicard.lean`, and this closed two leaves and created none.)

This development states representability through structures — `IsRelPicOf strX pstr`,
`IsJacobianOf`, `IsAlbaneseOf`, `AbelianSchemeStruct`, `IsRelPicZeroOf` — and then states
properties of the represented object in the shape

    (hP : IsRelPicOf strX pstr) : Smooth pstr

i.e. **EVERY scheme representing the functor has the property**. That shape is *true* (Yoneda pins
the object up to isomorphism) and is what a consumer wants, but **it is not what any textbook
proves.** BLR does not show "every scheme representing `Pic_{X/S}` is smooth"; it CONSTRUCTS one —
inside a Quot/Hilbert scheme, separated and locally of finite type by construction — and reads
smoothness off the construction. So a prover dispatched at the "every" form has no citation to
follow at all: they must first invent the missing bridge, and the leaf reads as research-scale when
the mathematics under it is a page of BLR.

**The bridge is one PROVABLE lemma, and it is pure Yoneda on the points type.** Given two
structures `hP : IsRelPicOf strX pstr` and `hQ : IsRelPicOf strX qstr`:

* `cmp` sends a `T`-point of `P` to the point of `Q` with the same class — `surj` for existence,
  `inj` for uniqueness;
* `cmp_cmp` (round trip) is `inj` again;
* `cmp_pre` (naturality in the test object) is the ONLY step with content — chain the two
  `sheaf_pre` fields with the transport lemma for the equivalence relation;
* `toHom := (cmp (tautological point 𝟙 P)).1`, and `toHom_comp_toHom` is `cmp_pre` at
  `h = toHom` composed with `cmp_cmp`. That gives `P ≅ Q` over `S`.

Roughly 60 lines, no geometry, and it compiled first try. Then **any isomorphism-invariant property
transports**: `rw [← toHom_comp]; infer_instance` proves `Smooth pstr` from `Smooth qstr`, because
an iso is an open immersion and both `Smooth` and `IsSeparated` are stable under composition.

**Then move the property into the EXISTENCE leaf, not into a new leaf.** With the bridge, "every"
reduces to "SOME representing object has it", and that existential is threaded up the chain of
existence theorems to the one leaf where a scheme is actually constructed
(`exists_relPicOf_isAffineOpen`). The clause is absorbed by an EXISTING sorry; no leaf is created.
Here the frontier went **9 → 7** while the total mathematical obligation was unchanged — the two
"every"-shaped leaves disappeared and FGA 232's owner gained a clause they were always going to
have in hand.

**The generalisable test, worth running before attacking any leaf of this shape:** ask whether the
citation named in the docstring proves a statement about *all* objects of a class or about *one
constructed* object. If it is the latter and the leaf says the former, **stop and prove the
uniqueness lemma first** — the leaf is not hard, it is mis-shaped. Symptom to watch for: a leaf
whose only hypothesis with content is a representability structure, and whose conclusion is a
property of a scheme that the structure says nothing about topologically.

Two smaller notes from the same task. **Threading a clause into an existence leaf's conclusion is a
RESTATEMENT**, so every earlier faithfulness audit on that leaf is VOID and must be re-run against
the composite — the strengthened hypothesis and the strengthened conclusion of a gluing leaf move
in *opposite* directions, which is precisely the shape CLAUDE.md already records as able to be
fatal. And the reduction may need a hypothesis the leaf did not have: `smooth_of_isRelPicOf` gained
`o : RelPoint strX (𝟙 S)` because the existence theorem needs a section. Adding a hypothesis
WEAKENS a leaf and is safe **only after checking the consumer can supply it** — here
`exists_relPicZeroOf_of_relPicGroupLaw` already had `o` in scope, so the change cost one argument
at one call site.

## THE SAME DEFECT WEARS A SECOND DISGUISE: A LEAF STATED ABOUT A *BASE CHANGE* OF THE OBJECT ITS CITATION IS ABOUT

(2026-07-31, `RelativePicard.lean`, the day after the "every representing object" section
above, in the same file, from the same root cause.)

The section above says a leaf must be stated in the shape its citation is stated in. The
"every object" shape is one way to violate that. Here is the other, and it is much easier to
miss because the statement looks perfectly ordinary:

    theorem exists_relPicOf_isAffineOpen (strX : X ⟶ S)
        (hproper : IsProper strX) (hsmooth : SmoothOfRelativeDimension 1 strX) …
        (V : S.Opens) (hV : IsAffineOpen V) :
        ∃ P pstr, Nonempty (IsRelPicOf (curveBaseChangeProj strX V.ι) pstr) ∧ …

**The hypotheses are about `strX`; the conclusion is about `X ×_S V ⟶ V`.** BLR 8.2/1 is a
theorem about a relative curve over an affine base. It is not a theorem about the base change
of a relative curve over an open of some other scheme. So a prover arriving at this leaf must
first prove step (i) — the hypotheses survive base change — before a single line of the
citation applies, and step (i) is invisible: it is not in the statement, it is not a leaf, it
is a sentence in the docstring.

The docstring in this case said so explicitly, and priced it as a feature:

> the base-change stability of `IsProper`, `SmoothOfRelativeDimension 1`,
> `GeometricallyConnected`, `HasUniversallyTrivialPushforward` and of the section is routine
> and belongs to whoever proves this, not to the assembly

**That pricing is the bug.** It is 20 lines, it is entirely mechanical, and bundling it into
a research-scale leaf hides it inside the one node nobody can finish. Discharged, the leaf
becomes `exists_relPicOf_of_isAffineBase` — an arbitrary proper smooth geometrically connected
relative curve with a section over an arbitrary affine base — which is *literally* BLR 8.2/1's
hypothesis list, and the assembly is six lines.

**The test, and it is purely syntactic, so run it on every leaf you are dispatched at:** read
the hypotheses and the conclusion and ask whether they are about the SAME morphism. If the
hypotheses name `f` and the conclusion names `pullback.snd f g`, `f ∣_ V`, `f.baseChange g` or
any other derived morphism, the transport between them is a separate obligation. It is almost
always cheap, it belongs OUTSIDE the leaf, and leaving it inside makes the leaf unciteable.

Three mechanical notes that cost time on the way:

* **mathlib's base-change stability is sometimes a `lemma`, not an `instance`.**
  `smoothOfRelativeDimension_isStableUnderBaseChange` is a lemma, so
  `MorphismProperty.pullback_snd` fails with
  `failed to synthesize MorphismProperty.IsStableUnderBaseChangeAlong (@SmoothOfRelativeDimension 1) g`
  — which reads like the fact is missing when it is merely not an instance. `haveI := …` first.
  `IsProper` and `GeometricallyConnected` do have instances.
* **a property defined as `P.universally` needs no stability theorem at all.**
  `HasUniversallyTrivialPushforward f` is `hasTrivialPushforwardProperty.universally f`, and
  `.universally` is stable under base change by construction, so `MorphismProperty.pullback_snd
  (P := …universally)` closes it outright.
* **a section transports by `pullback.lift_snd` and nothing else.** `relSection` of the constant
  section is already the map; the proof obligation is `pullback.lift _ (𝟙 T) _ ≫ pullback.snd = 𝟙 T`.

Corollary for reviewers of a cut: 1 → 1 on the leaf count is a *good* trade when what changes
is that the leaf now matches its citation. Judge a decomposition by whether the remaining leaf
can be handed to someone with the book open, not by the count alone.

**AND THE DEFECT CLUSTERS — WHEN YOU FIND ONE, RUN THE TEST ON EVERY LEAF IN THE FILE.**

(2026-07-31, same file, same day, two more instances found by doing exactly that.)

The syntactic test above costs ten seconds per leaf: *are the hypotheses and the conclusion
about the SAME morphism?* Having applied it once to `exists_relPicOf_isAffineOpen`, applying
it to the file's other seven leaves immediately caught two more —
`isInvertibleSheaf_sectionIdeal` and `nonempty_modPullback_sectionIdeal`, both with hypotheses
on `strX : X ⟶ S` and conclusions about a section of `X ×_S T ⟶ T`. Stacks 0C4S is about a
section of a smooth relative curve; neither leaf was stated about one.

This is not a coincidence, and the reason tells you where else to look: **the mis-shaping is
inherited from the file's central definition.** Everything here is stated relative to a fixed
`strX` because that is what `IsRelPicOf`, `RelPoint` and `RelPicEquiv` are parameterised by, so
a leaf about the base-changed curve gets written with `strX`'s hypotheses out of sheer local
consistency. Any file with one pervasive ambient object will do the same. **So the unit of the
audit is the FILE, not the leaf** — and the transport lemmas you prove for the first instance
are exactly the ones the rest need, which is why instances two and three cost 3 lemmas and 30
lines between them once the first was done.

Three notes from the two extra instances:

* **The hidden hypothesis surfaces as an explicit one, and that is the audit's job to catch.**
  `relSection x` is a section *by construction*, so the old statement never had to say so.
  The citation-shaped statement quantifies over an arbitrary `σ : T ⟶ Y` and therefore MUST
  carry `σ ≫ strY = 𝟙 T` — without it the leaf is false for a silly reason (`σ = 𝟙 Y` makes
  the kernel `0`). Restating always risks dropping such a constructional hypothesis on the
  floor; enumerate what the old form got for free before writing the new one.
* **Cartesianness is the commonest thing a base-change leaf assumes without saying.** The old
  `nonempty_modPullback_sectionIdeal` had "the square is cartesian and the sections match" as a
  docstring *remark* — the prover was expected to re-derive it. Both are now hypotheses of the
  leaf and PROVEN lemmas at the call site (`IsPullback.of_right` for the pasting;
  `pullback.hom_ext` for the section compatibility). A remark that a prover must re-derive is
  an unowned obligation wearing prose.
* **The transport lemmas pay for themselves elsewhere.** `isPullback_curveBaseChangeMap` — that
  `X ×_S T'` really is the pullback of `X ×_S T` along `T' ⟶ T` — was needed here and is also
  precisely the input step 2 of a *different* open leaf's route was asking for. Prove these as
  named lemmas, never inline in a `have`.

## AN AUDIT'S REFUTATION CHECKS DECAY — BUT RE-RUNNING THEM IS ONLY HALF THE JOB

(2026-07-31, `flt-lean-246`, on two atomicity-audited leaves of `KhareWintenberger.lean`.)

A mature leaf here carries an ATOMICITY or CUT audit that names each axis it searched
*and the one-line check that would refute the verdict*. Those checks are the most
valuable thing in the docstring and they are cheap — three greps closed three axes in
under a minute. **Run them; they decay.** Two of the three had moved since the audit was
written: `exists_const_natCard_zeroLocus_sub_le` had gone from an open leaf to **PROVEN**
(111 body lines, zero `sorry`), which turns "blocker 1 is a piece of mathematics" into
"blocker 1 is a relocation job" — a completely different price on the same cut.

**But an audit's checks only cover the axes it thought of, and the gap is systematic
rather than accidental.** A CUT AUDIT that refutes *"derive the node's conclusion FROM
the weaker shape"* says nothing about *"replace the node's conclusion BY the weaker
shape and rewire the consumers"*. Those are different moves with different failure
modes, and the second is the one an attacker actually tries first. Here the audit had
carefully refuted direction one (purity cannot rebuild the point-count package —
`Npt : ℕ → ℕ` effectivity) and was silent on direction two, which is where the whole
decision lived.

**And before weakening any leaf to "what its consumer needs", READ EVERY CONSUMER.**
This is where the trap sprang. Every docstring in that block presented the node as
feeding one lemma to produce `‖φ(a_w)‖ ≤ 2√(Nw)` — true of consumer 1. Consumer 2, 1400
lines away, calls a *sharper* lemma twice and needs `‖γ i‖ = ‖γ j‖ = √q` **exactly**, an
equality rather than a bound. Weakening the node to consumer 1's conclusion — the obvious
move, and the one the prose invites — compiles nowhere. No docstring recorded this; only
reading the second proof did. Generalise: **prose describes the consumer the author was
thinking about**, so the consumer set is something to enumerate mechanically, never to
inherit.

**Finally, "strictly weaker" is not automatically better.** The purity shape here *is*
strictly weaker (the audit's own effectivity argument separates them) and it was still
declined, because it orphans ~190 lines of proven complex analysis into free-floating
code while closing zero leaves and opening zero. Under this file's own tie-breaker —
count OPEN leaves after, not leaves created — a reshaping that is leaf-neutral and
destroys verified material is a loss. **Record the declined option with the condition
that would reverse it** (here: a second consumer appearing for the orphaned lemmas), so
the next owner inherits a decision rather than an open question.

## CUTTING A LEAF DROPS THE ENCLOSING PROOF'S CONTEXT — and a vacuous hypothesis is the usual casualty

(2026-07-31, `flt-lean-313`, two leaves in one file, both FALSE AS STATED.)

`chordSum_xWitness` and `chordSum_yMultiplier` were cut out of
`isDiffCharCert_add_of_ne` in `DifferentialCharacter.lean`. Both carried the witness
certificates of the two summands,

    hrat₁ : ∀ P, φ P ≠ 0 → x(φP)·B₁(x P) = A₁(x P) ∧ y(φP)·E₁(x P) = C₁(x P)·y P + D₁(x P)

and neither carried `φ ≠ 0`. **For `φ = 0` that hypothesis is VACUOUS** — its premise
never fires — so `A₁, …, E₁` is an ARBITRARY tuple and both identities are refutable in
one line (`W = W'`, `φ = 0`, `ψ = id`, witnesses `X,1,1,0,1`, and `A₁ = 0, B₁ = E₁ = 1`,
which even satisfies the nondegeneracy hypothesis `hG : A₂B₁ − A₁B₂ ≠ 0`).

The enclosing proof had `φ ≠ 0` and `ψ ≠ 0` in scope from `hφP : φ P ≠ 0`, so nobody
writing the cut noticed they were being used. That is the general shape:

**A cut statement inherits the WRITTEN hypotheses and loses the AMBIENT ones. Before
publishing a leaf, instantiate every hypothesis of the form `∀ …, <premise> → …` at the
degenerate case where the premise is unsatisfiable, and check the conclusion still holds.**
If it does not, the missing hypothesis is almost always already in the caller's hand — here
`hφ0`/`hψ0` cost the consumer nothing and no statement above them changed.

This file already recorded the same trap one level up ("the degenerate-witness trap" in
`DifferentialCharacter.lean`'s own module docstring, for `IsDiffChar 0 c`). It recurred
because the docstring warned about the DEFINITION, and the new leaves were about the
WITNESSES. A trap documented at one level does not vaccinate the level below it.

### `ring` treats `Polynomial.C 2` as an ATOM — `simp only [map_ofNat]` first

Same day, cost one build cycle, and it will bite anyone moving one of this project's many
`C`-headed polynomial lemmas from point level to polynomial level. `diffChar_yWitness_onePart`
is stated with `C 2 * D * B + …`; every existing consumer uses it after `eval`, where
`eval_C` has already turned `C 2` into the numeral `2`. The FIRST polynomial-level
`linear_combination` over it failed with a residual of exactly the shape

    -(… * C 2 * D * 2) + (… * D * 4) - (B ^ 3 * C 2 ^ 2 * D ^ 2) + (B ^ 3 * D ^ 2 * 4) = 0

i.e. `(4 − 2·C 2)(…) + (4 − (C 2)²)(…)`, which is zero only once you know `C 2 = 2`.
`ring` does not: `Polynomial.C 2` is an opaque application, not a numeral.

    simp only [map_ofNat] at hone      -- turns `C 2` into `2`; then `linear_combination` closes it

Read that residual shape as a diagnosis, not as "my coefficients are wrong": a failure whose
leftover is a *numeral mismatch on a single atom* is this, and re-deriving the coefficients
(which is what one does by reflex) will never fix it.

## A PROOF ROUTE THAT DIES IN ONE CHARACTERISTIC: SPLIT THE LEAF, DO NOT WEAKEN THE PARENT

(2026-07-31, `flt-lean-313`, `exists_diffCharScalar_polyData`.)

The pullback-factor leaf of `DifferentialCharacter.lean` is proved by a valuation-and-degree
count on `ℙ¹` run against `Ψ_{W′}(x) = γ²Ψ_W`. That identity is FREE — a `linear_combination`
of the leaf's own two hypotheses, machine-checked and quoted in the docstring — and in
characteristic `2` it is **VACUOUS**: `Ψ = 4X³ + b₂X² + 2b₄X + b₆ = (a₁X + a₃)²` is a square,
`4 = 0`, and the identity collapses to the OTHER hypothesis squared. So the count proves the
statement everywhere except at one prime, where it proves nothing — and the statement is
still TRUE there (it is *AEC* III.5.2, which is characteristic-free).

**A derived identity can be an identity and still be empty.** Nothing about its derivation
warns you: it type-checks, `ring` closes it, and it is genuinely a theorem. Before building a
count on one, instantiate it in the degenerate characteristic and check it still separates
the things it is supposed to separate.

Two ways out, and they are not equally good:

* add `(2 : F) ≠ 0` to the parent — cheap on paper here, since the only consumer
  (`MazurTorsion.lean`) is over `AlgebraicClosure ℚ`. But it moves an INTERFACE, and an
  interface change together with its call sites is exactly what the seventh invisibility
  class above says a merge can split across the conflict boundary;
* **keep the parent's signature and `by_cases` on the characteristic, with the bad branch a
  NEW NAMED LEAF.** Nothing upstream moves, no consumer in any worktree has to be found and
  edited, and the residual is stated at exactly the generality where it is hard.

The second is right by default. The cost is one declaration; a leaf is much cheaper than an
interface.

And go one further while the algebra is in front of you: in the char-`2` branch `hone`
collapses (its `2DB` term dies) and `hcurve`'s two middle terms fold into it, which removes
`E` and `Cx` from the CONCLUSION and takes the residual from five polynomials to four. That
reduction is REVERSIBLE and cost ten lines, so what a successor is dispatched at is the small
statement. A leaf handed on in its raw form makes the next agent re-derive the collapse
before starting — and there is no reason for two agents to do that.

### `omit [X] in` goes BEFORE the doc comment

`omit [DecidableEq F] in` placed between a `/-- … -/` and its `theorem` is a syntax error —
`unexpected token 'omit'; expected 'lemma'`, reported at the END of the doc comment's last
line, which reads like a problem with the comment. A doc comment must be adjacent to its
declaration. Put the `omit` above the doc comment; `DifferentialCharacter.lean` already does
this in twenty places, so copy a neighbour rather than guessing.

## A "MISSING MACHINERY" AUDIT EXPIRES — but only its PROJECT half

(2026-07-31, `flt-lean-90`.) Two leaves in `Modularity/MoretBailly.lean` carried
careful, dated MISSING MACHINERY audits, written three days apart, each ending in a
named *"the check that would refute this"*. Re-running both against the current tree
gave OPPOSITE answers, and the reason is structural rather than luck:

- `nonempty_ringClassArtinData_anticyclotomic`'s audit (2026-07-28) said *"`grep -rn
  'RayClassGroup|artinMap|HilbertClassField|reciprocity'` returns PROSE ONLY — there is
  no Artin map and no reciprocity anywhere"*, and named as refuting it *"a declaration
  whose CONCLUSION has a Galois group as its codomain and whose HYPOTHESES do not
  already contain one"*. **Both clauses are now false.** `Fermat/FLT/NumberField/`
  gained `ArtinSymbol.lean` (`frobAt`, `artinMap`), `UnramifiedClassFieldExistence.lean`
  (`exists_classField_of_subgroup` — precisely the refuting shape),
  `UnramifiedClassFieldBound.lean` (sorry-free) and `HilbertClassFieldNormal.lean`.
- `exists_isGaloisTwistForm_of_isOpenKernel`'s audit (2026-07-29) re-ran IDENTICAL: no
  `IsStack` instance under `Mathlib/AlgebraicGeometry/`, no `quotientScheme` anywhere.

**The asymmetry: an audit's claims about the mathlib PIN do not expire — the pin is
frozen — while its claims about `Fermat/` expire fast, because the fleet is writing
`Fermat/` continuously.** So do not re-survey a whole audit and do not trust one
either. Split it: believe the pin half, re-run the project half. That is one `grep`,
and it is the difference between "this needs a theory nobody has" and "this needs one
generalisation of a file that already exists".

Corollary that made this concrete and is worth copying: the CFT cluster's own docstring
already said *"whoever builds class field theory should build it once, in THIS file
(generalising `relNormClassSubgroup` to a modulus)"*. A leaf blocked on missing theory
should be checked against the **docstrings of the files that would host that theory**,
not only against declaration names — the owner of the gap has often already written
down where the work goes.

## A BLOCKED-LEAF SURVEY IS A HYPOTHESIS, AND ITS *NEGATIVE* CLAIMS ARE THE ONES THAT ROT

(2026-07-31.) A leaf that resists often acquires a docstring survey — "here is what
blocks this, here is what the tree does not have". Those surveys are worth their
weight; the one on `exists_commutingHeckeAlbaneseFamilyGamma1` correctly identified
the blocking object and correctly killed three cheap witnesses. But it also said
closing the leaf needs "the density statement … plus a separatedness step — and
neither is in the tree", and **the separatedness step was already in the tree**: it
is the UNIQUENESS half of the structure's own universal property. Eleven lines,
verified green in a scratch module the same day.

The pattern generalises past that one leaf. **Universal properties in this
development are stated with `∃!`** — `IsJacobianOf.universal` is `∃! u, …`, and so
are its neighbours — and an `∃!` IS a rigidity lemma: two morphisms satisfying the
same universal datum are equal, for free, no geometry. So **before writing (or
dispatching at) a rigidity, separatedness, or "morphisms agreeing on points are
equal" leaf, check whether the object you are working over already carries an `∃!`.**
The Yoneda-style helper that converts a hypothesis about the representing morphism
into the universal property's own clause is usually already there too
(`IsJacobianOf.aj_val`).

The asymmetry is the point, and it is the reusable part: a survey's POSITIVE claims
("this is what blocks it", "this witness fails because …") are checked by the person
writing them, because they had to do the work. Its NEGATIVE claims ("the tree does
not have X") are a `grep` that was not run, and they cost a leaf each when wrong —
the same failure shape as [Inventory audits understate what exists] and
[Audits search production, not invariants], now in a third place. Treat "not in the
tree" in a docstring exactly as CLAUDE.md already tells you to treat "still open,
owned elsewhere" in a commit message: **a hypothesis to check, never a fact.**

## TWIST THE EMBEDDING, DON'T MOVE THE PRIME — a conjugated local element is a local element

(2026-07-31, `flt-lean-24`, proving `localInertia_le_fixingSubgroup_of_isUnramifiedAt_muSubfield`.)

Every local-to-global inertia leaf in this development quantifies over `σ * ñ * σ⁻¹`, a
CONJUGATE of the image of a local element `n ∈ localInertiaGroup ℓ`. The obvious reading — and
the one both leaf docstrings prescribed — is "build the embedding prime `Q₀ = ι⁻¹(𝔪)`, then move
it along the Galois orbit by `σ` and propagate by transitivity", which is what
`MinkowskiUnramified.lean`'s `inertia_eq_bot_of_exists_prime_over` does and what makes that file
long.

**The conjugation can be absorbed into the EMBEDDING instead.** With `ι : ℚ̄ → (ℚ_ℓ)ᵃˡᵍ` the
embedding underlying `Field.absoluteGaloisGroup.map`, set

    j := ι ∘ σ⁻¹.

`j` is another ring embedding `ℚ̄ → (ℚ_ℓ)ᵃˡᵍ`, and for `g = σ ñ σ⁻¹` one gets, from `lift_map`
alone and with no orbit argument at all,

    j (g x) = n (j x)     for every x.

So relative to `j`, the global `g` acts exactly as the local `n` acts relative to `ι`. The prime
`j⁻¹(𝔪)` is then directly `g`-inertial, and the conjugacy-propagation step does not appear.
Cost: three lines. The orbit route needs a transitivity theorem, `IsGaloisGroup` instances and
`exists_smul_eq_of_isGaloisGroup`.

**Second trick from the same proof: `by_cases` on the prime being `⊥` beats proving it proper.**
`Ideal.comap ψ 𝔪` is prime for free, but the inertia nodes want `Q ≠ ⊥`, and showing the
embedding prime is proper (`ℓ ∈ 𝔪`, i.e. `1/ℓ` is not integral over `ℤ_ℓ`) is where the
corresponding absolute proof spends most of its length. It is never needed: if `Q = ⊥` then
`τ • x - x ∈ ⊥` says `τ • x = x` outright, and `NumberField.eq_one_of_smul_eq_self` closes that
branch in two lines. Split on it rather than ruling it out.

**And the reason the whole thing was cheap: READ THE CALL SITE BEFORE PROVING ANYTHING.** Both
`muSubfield` inertia leaves were stated WITHOUT `IsGalois (muSubfield p) (extendScalars hEle)`,
and without it neither is reachable without first proving "a compositum of everywhere-unramified
extensions is everywhere-unramified" and passing to a normal closure. Both call sites already
held that instance — one `obtain`s it out of `exists_transport_unramifiedAbelian_to_muSubfield`,
the other proves it three lines earlier — so adding it to the statement changed no call site at
all. That is the same shape as `exists_artinDivisorNormIndex_le_ray_class` above: **the missing
hypothesis is usually already in the caller's hand, and a leaf's own docstring will not tell you
so.** Grep the call sites before deciding a leaf needs new theory.

Note `IsGalois ℚ L₀` is NOT similarly available and a prover should not reach for it: the caller
builds `L₀` as `IntermediateField.fixedField M'` for a subgroup `M'` that is only normal in
`Γ_{ℚ(μ_p)}` (it contains the commutators of `ker χ`), not in `Γℚ`. So the absolute node
`isUnramifiedAt_of_inertia_le_fixingSubgroup`, which needs `IsGalois ℚ L`, does not apply to `L₀`
directly — the sibling leaf's docstring suggestion to "reuse the absolute node at every `ℓ ≠ p`"
needs a normal closure first, and that is a real cost, not a bookkeeping step.

## TRANSPORT THE AMBIENT CLOSURE — a "new arithmetic" leaf is often an existing theorem in the wrong `ℚ̄`

(2026-07-31, `flt-lean-24`, the sibling leaf
`isUnramifiedAt_of_localInertia_le_fixingSubgroup_muSubfield`.)

That leaf's own docstring prescribed a split: "at every `ℓ ≠ p` the absolute statement does
apply … only the place above `p` needs the genuinely relative argument." Following it produces a
proof plus a NEW SORRY LEAF for the `ℓ = p` case — which is what the rival cut on `merger` did
(`isUnramifiedAt_muSubfield_of_localInertia_at_p`, one consumer, still open).

No split is needed. `HardlyRamified/HilbertModularity.lean` already proves the RELATIVE
dictionary `isUnramifiedAt_of_hilbertInertiaTrivialAt` — inertia-trivial at `w` ⟹ unramified
above `w`, for a finite Galois subextension of any number field `F`, `p` included. The ONLY
obstruction was that it is stated inside Lean's canonical `AlgebraicClosure F`, whereas the
consumer's whole Galois dictionary (`Γℚ`, `ker χ`, `muSubfield p`) lives in `AlgebraicClosure ℚ`.
Two transports (now `NumberField/RelativeUnramifiedTransport.lean`, ~250 lines, sorry-free) close
the gap and the leaf becomes a 40-line assembly with NO new leaf:

* the dictionary along an `F`-isomorphism `ee : Fᵃˡᵍ ≃ₐ[F] Ω`, with its inertia hypothesis
  phrased as an equation in `Ω` so a consumer never mentions `Fᵃˡᵍ`;
* the group-side companion: a local inertia element of `F` at `w`, read through `ee`, IS a
  `Γ K`-conjugate `σ κ̃ σ⁻¹` of a local inertia element of the base `K`. That is what turns a
  `K`-level hypothesis into an `F`-level one, and it is the ALL-PLACES form of
  `GaloisRepTransport.lean`'s `exists_finset_conj_localInertiaGroup_le` — whose finite exceptional
  set is fatal here, because the excluded place is exactly the one the leaf exists to handle.
  Deleting the `S`/`T` bookkeeping from that proof is the whole of the new proof.

**So before believing a leaf needs arithmetic the tree does not have, ask whether the tree has it
in a DIFFERENT ALGEBRAIC CLOSURE.** This development runs three at once (`AlgebraicClosure ℚ`,
`AlgebraicClosure CF`, `AlgebraicClosure (muSubfield p)`) and a statement is not reusable across
them without an explicit `ee`. Keep `ee` a HYPOTHESIS rather than building `IsAlgClosure.equiv`
inside, for the reason recorded at
`NumberField.exists_unramifiedAbelian_of_algebraicClosureEquiv`: with it opaque, no defeq check
can try to unfold `IsAlgClosed.lift`.

**Two mechanical traps met on the way, both cheap once named.**

1. *A scratch module that `public import`s the target file does NOT see what the target sees.*
   `exists_prime_eq_toHeightOneSpectrumRingOfIntegersRat` is `unknown constant` in a scratch that
   imports `Modularity/Interface`, because `Interface.lean:426` imports `Threeadic`
   NON-publicly — visible inside `Interface`, not re-exported. **Copy the target's non-`public`
   imports into the scratch**, or you will "discover" that a constant the target file can cite
   does not exist.
2. *`Algebra ℚ ℚ_ℓ` has two live spellings*, `DivisionRing.toRatAlgebra` (what you get writing
   `algebraMap ℚ (v.adicCompletion ℚ)` in your own `have`) and
   `HeightOneSpectrum.instAlgebraAdicCompletion` (what the transport theorems carry). They are
   NOT defeq at default transparency, so `exact` fails with three instance arguments differing at
   once. The standing idiom, already all over `Threeadic.lean`, is one `Subsingleton.elim` plus
   `▸`:

       have halg : (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
           (NumberField.RingOfIntegers ℚ) ℚ hℓ.toHeightOneSpectrumRingOfIntegersRat) =
           (DivisionRing.toRatAlgebra) := Subsingleton.elim _ _
       …
       exact halg ▸ hfin

**And the release-window check is worth running BEFORE the proof, not after** (it caught all
THREE of this task's targets, already proven on `merger` and invisible from `main`). It also
changes what the task is: with a rival cut in hand the question stops being "can I prove it" and
becomes **"which cut leaves fewer OPEN leaves"** — here mine leaves zero and `merger`'s leaves
one, so the right output is a `to_merger` note naming the leaf that becomes consumerless, not a
proof race. One command:

    git show merger:Fermat/FLT/Modularity/Interface.lean | grep -n -A3 '^theorem <name>'

## A `Nonempty (A ≃+ B)` LEAF CANNOT SUPPORT ANY CONSUMER THAT NEEDS THE MAP

(2026-07-31, `exists_weierstrassQ_autStable_of_weierstrassAlgClos` in `X0.lean`.) A
leaf whose conclusion is a bare `Nonempty` of an isomorphism type says only that the
two objects are abstractly isomorphic. **Any two witnesses are interchangeable, so a
consumer may use only what is true of EVERY witness** — and for a group isomorphism
that is almost nothing, because composing a witness with any automorphism of the
target yields another witness.

Concretely: `exists_addEquiv_of_weierstrassModel_field` concludes
`Nonempty (RelPoint f (𝟙 (Spec k)) ≃+ (W⁄k).Point)`. At `k = ℚ̄` it looks like exactly
the "points dictionary over `ℚ̄`" that three docstrings in `X0.lean` say is the missing
half — it is not, and no amount of work makes it one. `E(ℚ̄)` is abstractly
`(ℚ/ℤ)² ⊕ ⊕ℚ`, whose automorphisms surject onto `GL₂(ℤ/N)` on `N`-torsion, so the image
of the level structure can be ANY order-`N` cyclic subgroup. Its Galois-stability is
therefore not a property of the datum at all.

**Test before consuming, and it costs one line: is the conclusion invariant under
post-composing the witness with an automorphism of the target?** If not, the leaf is
insufficient however close its statement reads, and the fix is to strengthen the
PRODUCER (add the equivariance/naturality clause), never to try harder downstream.

**And the same test kills the natural CUT**, which is why this belongs beside the
rival-cuts section. Hypothesising the dictionary — `(e : A ≃+ B)` plus "e carries this
sub-object to that one" — and leaving the geometry as the residual leaf produces a
residual that is **FALSE AS STATED**, refuted by the same automorphism. An abstract
`e` in a hypothesis is not a dictionary, it is a relabelling: it has thrown away
exactly the information the residual needs. A cut of a descent statement must either
construct the dictionary inside, or hypothesise it *together with* its semilinearity.

## A STRICT-IMPLICIT LAMBDA DOES NOT BETA-REDUCE IN THE GOAL — `beta_reduce` before `rw`

(2026-07-31, `flt-lean-17`, in `X0.lean`.) Natural families in this development are typed
`∀ {T : Scheme.{0}} (g : T ⟶ SpecQ), RelPoint f g → RelPoint jf g` — `RelPoint.pre`/`post`,
every `c` in the Hecke cluster, `IsHeckeAlbaneseRecipe`, `IsJacobianOf.aj`. When you
discharge such an existential with `refine ⟨fun {T} g x => …, …⟩`, the remaining goals
contain the **unreduced application** `(fun {T} g x => …) g' y`, because the strict-implicit
binder blocks the beta step `instantiateMVars` would otherwise do. Every `rw` then fails with

    Tactic `rewrite` failed: Did not find an occurrence of the pattern …
    in the target expression
      (fun {T} g x => …) g' (RelPoint.pre p hg x) = …

which reads as "my lemma is wrong" and is nothing of the sort. `beta_reduce` as the first
tactic of each branch fixes it; `show` with the reduced form also works but makes you write
out proof terms like `Category.comp_id g'` that the binder produced for you.

Worth its own section only because of where it bites: `X0.lean` is ~80 000 lines and one
elaboration is ~25 minutes, so discovering this against the real file costs a cycle per
branch of the `refine`. **Prototype the glue in a scratch module importing
`Fermat.FLT.Modularity.AbelianScheme` alone** — that import is 4 SECONDS, `RelPoint` and
`AbelianSchemeStruct` both live there, and `RelPoint.post` / `AbelianSchemeStruct.pre_neg`
are eight lines to re-declare locally. The whole base-point-normalisation glue for
`exists_heckeCorrespondenceFamily` was written and debugged in four such 4-second rounds and
then compiled first time in the real file. Mock the SHAPE, not just the content: a
`letI := ab.addCommGroup g` binder in front of a `Finset.sum` behaves differently from a bare
equation, and the mock is what showed the branch needs a trailing `rfl`.

## SEE THE MERGE BEFORE THE MERGE WORKER DOES — `git merge-tree`, from your own worktree

(2026-07-31, `flt-lean-182`.) Every rule above about rival cuts, class-6 dropped payloads and
class-7 interface splits is addressed to the merge worker, at the moment the merge happens. A
prover agent can see the *same* merge hours earlier, for free, and without touching anything:

    git merge-tree --write-tree --name-only HEAD merger    # exit 1 == conflicts; prints tree sha

It merges **in memory**. No working-tree change, no `.lake` disturbance, no conflicted state to
strand the worktree in if you are killed mid-way — which is exactly why this beats the obvious
`git merge --no-commit … ; git merge --abort`. The printed tree sha is browsable with
`git show <tree>:<path>`, so every class-7 check in this file can be run **on the merge that has
not happened yet**.

Do it whenever your branch touched a hot file, and read TWO things, because they fail in opposite
directions:

- **The files that CONFLICTED** are the safe half. Somebody will look at them.
- **The files that `Auto-merging` reported with no conflict are the dangerous half.** That is
  class 7 verbatim: my branch deleted `not_smooth_specMap_coordinateRing_of_singular` (130 lines)
  while `merger` had independently grown a *new call to it* 200 lines away. Too far apart to
  conflict, so `EllipticScheme.lean` auto-merged silently — and the check that settles it is not
  reading the diff but grepping the merged blob for the deleted name:

      git show <tree>:<path> | grep -n '<deletedName>'   # docstring hits only == safe

  Here it happened to resolve correctly (git took my region wholesale, call site and all). "Happened
  to" is the point: nothing would have said otherwise.

**Then check the reverse direction, which is the one nobody thinks of.** Your branch carries the
*old* `sorry` bodies of every leaf it did not touch. If `merger` proved one of them meanwhile,
does the merged tree keep the PROOF or your `sorry`? Grep the merged blob for the body, not the
name. (Both of mine were preserved — untouched regions take merger's side — but that is a fact to
verify, not to assume, and it is invisible from either side alone.)

### What to do when the merge shows your cut and `merger`'s are RIVALS

The `RIVAL CUTS` section above tells the merge worker how to choose. It does not say what the
prover on the other branch should do, and there is one action worth far more than a note: **fold
the loser's surviving information into the winner's docstring on YOUR side, so that "take HEAD" is
a LOSSLESS resolution.** Then say exactly that in `to_merger`.

`merger` had closed my target by NARROWING it to `[PerfectField k]`; my branch had deleted the
hypothesis outright, so mine strictly subsumes it and the conflict was pure docstring. But
merger's docstring held two facts mine did not — that narrowing to `CharZero` instead would have
REGRESSED `X1.lean`'s char-`p` chain, and why the declaration is kept as a thin wrapper (a
non-`public import` makes the upstream name invisible to its real consumer). Taking HEAD would
have silently dropped both. Ten minutes of docstring editing turned a decision requiring the merge
worker to re-derive the mathematics into a one-word one.

And check the loser's docstring for claims that have gone STALE before you copy them: merger's
said the chain was "down to ONE" leaf that had since been proven. Fold in what is durable, correct
what is not, and say which you did.

## A HYPOTHESIS YOU CANNOT SUPPLY MAY BE PURCHASABLE BY BASE CHANGE

(2026-07-31, `flt-lean-202`.) `exists_smoothProperCompactification_affineLine` had a
careful audit that named the right obstruction and then priced only the two most
expensive ways past it. The tool it wanted,
`exists_isSmoothCompactification_of_isAffine`, requires `[PerfectField K]`; the leaf
has a bare `[Field K]`. The audit concluded: either build `ℙ¹_K` by hand via `Proj`,
or descend along `K ⊆ K^perf`. Both are large.

The leaf was three lines away. **`𝔸¹_K` is the base change of `𝔸¹` over the PRIME
field, and the prime field is perfect in both characteristics** (`ℚ` by
`PerfectField.ofCharZero`, `𝔽_p` by `PerfectField.ofFinite`). Build the object where
the hypothesis holds, pull it back, and the imperfect case costs one `rcases` on
`CharP.char_is_prime_or_zero`.

So add this before writing "needs new theory" about a missing hypothesis: **ask
whether the statement is stable under a base change that CAN supply the hypothesis.**
A hypothesis on the BASE is often purchasable by moving the construction to a smaller
base — and the smaller base is usually the prime field, `ℤ`, or `Spec ℤ`, where
finiteness/perfectness/normality hold for free. This is a different question from
"how do I prove it", which is the only question the audit asked, and it is much
cheaper to answer.

Corollary worth its own line: **check which properties you must TRANSPORT and which
you can REDERIVE downstream.** Here properness, smoothness and openness are base-change
stable; FINITENESS OF THE COMPLEMENT is not — transporting it means proving the preimage
of a finite set under `C_K ⟶ C_{𝔽_p}` is finite, a genuine argument about the fibres
`Spec (κ(x) ⊗_{𝔽_p} K)`. It was avoided entirely by not transporting it: the base-changed
curve is still a smooth curve over `K`, so its Krull dimension is `≤ 1` and the existing
`finite_compl_range_of_topologicalKrullDim_le_one` regives the conclusion from density
alone. Rederiving downstream was cheaper than transporting, and that is the common case.

Second audit failure in the same leaf, the same shape as the `Isogeny`-row error
recorded above: the audit reported `SmoothOfRelativeDimension 1 (𝔸¹_R ↘ Spec R)` missing
because **it searched for an INSTANCE and there was none — while the CONSTRUCTOR was
right there.** `Algebra.PreSubmersivePresentation.naive` with the relation family indexed
by `PEmpty` presents the polynomial algebra itself; the Jacobian is the determinant of the
empty matrix, i.e. `1`. "No instance fires" is evidence about the instance database, never
about the library.

## BEFORE DECOMPOSING A NODE, CHECK WHETHER THE PIECE IS EQUIVALENT TO THE WHOLE

(2026-07-31, same worktree, and it is the mirror image of the rule above.)
`isTorsion_jacobian_of_lFunction_ne_zero` ("`J₀(N)(ℚ)` is torsion") was decomposed on
2026-07-27 into Eichler–Shimura (`exists_heckeIsotypicDecomposition`) plus
Kolyvagin–Logachev on one isotypic factor (`isTorsion_factor_of_heckeIsotypic`). The
decomposition is recorded, audited, and reads as real progress.

It moved nothing on the arithmetic side, and since 2026-07-29 that is provable in-tree.
`exists_quasiSection_heckeIsotypicFactor` — Poincaré reducibility, PROVEN — gives
`v : A i ⟶ J` and `m > 0` with `u i (v x) = m • x`. So "`J(ℚ)` torsion" implies "factor
torsion" in three lines, and the consumer already proves the converse. **The piece and
the whole are EQUIVALENT.** The split is still load-bearing for a different branch (the
Atkin–Lehner development is stated over the decomposition), so it was not wrong to make
— but any future proposal to cut the factor leaf further along that axis is dead, and
conversely anything proving `J(ℚ)` torsion by ANY route (Kato, Mazur's Eisenstein ideal)
closes the factor leaf at every `i` without being re-aimed at a factor first.

The check is cheap and it is not the falsity audit: **for each piece, ask whether some
already-PROVEN theorem in the tree derives the piece from the whole.** A section, a
quasi-section, a retraction, a finite-kernel map or an isogeny is exactly the shape that
does it, and those are common. If one does, the cut has renamed the obligation rather
than reduced it, and the docstring should say so — otherwise the next owner reads a
decomposition and infers a reduction.

And when the answer is yes, **say which hoists it retires.**
`exists_quasiSection_heckeIsotypicFactor`'s docstring proposed hoisting its block ~27000
lines so `isTorsion_factor_of_heckeIsotypic` could reach it. That hoist would have bought
that leaf nothing — the only thing it could do with the quasi-section is the circular
step — and the resulting declaration would have been free-floating. A queued hoist is a
dispatch; retiring one is worth the same as closing a leaf.

## MERGING AT DECLARATION GRANULARITY: what it fixes, and the ONE thing it silently breaks

(2026-07-31, release 26 — 24 conflicting branches over files both sides had rewritten
heavily.) Release 24's textual union policy (hunk-level, "base empty ⇒ ours+theirs;
base non-empty ⇒ ours + theirs' pure insertions") **dropped real payload here**: five
branch-added declarations vanished from `MoretBailly.lean` alone, silently, and the
declaration-presence check is the only reason anyone noticed. The reason is structural
— when both sides edit adjacent lines, `difflib` reports one `replace` opcode and the
"pure insertions" rule keeps nothing.

**What worked instead: merge at DECLARATION granularity.** Split BASE / OURS / THEIRS
into blocks (leading docstring+attributes, then the declaration), key them by
namespace-qualified name, and decide per name:

* theirs ADDED it (not in base, not in ours) → splice it in, anchored after the
  theirs-predecessor that exists in ours;
* theirs changed its CODE while ours left the code equal to base → take theirs;
* both changed the code → keep ours and REPORT, with the `sorry`-status of each side
  printed, because that is the only case a human has to look at. Twenty-four branches
  produced **nine** such reports.

Three refinements, each of which was a bug before it was a rule:

1. **Decide on CODE, merge DOCSTRINGS separately.** Comparing whole blocks makes every
   docstring edit look like a code conflict. `flt-lean-88`'s five-site arity repair was
   reported as "both changed, kept ours" purely because merger had appended a paragraph
   to one docstring — and keeping ours on two of the five sites is exactly the class-7
   split that does not compile.
2. **A block that CONSUMES one of theirs' new declarations must come from theirs.**
   Otherwise the new leaf lands orphaned and the parent stays sorried: one closed leaf
   traded for two open ones plus free-floating code. Guard it with "unless ours' body is
   sorry-free and theirs' is not", so the rule cannot resurrect a `sorry`.
3. **Widen the identifier class before you trust any of it.** The stock
   `[A-Za-z0-9_À-ɏͰ-Ͽ℀-⅏.'!?₀-₉]` stops at U+2089, so `mulVecRightₗ` (U+2097) and
   `mulVecRightₗ_apply` both truncate to `mulVecRight` and are reported as a duplicate
   pair that does not exist. Use `₀-ₜ` and `ᴀ-ᵿ`; still avoid `À-￿`, which swallows
   `⟨⟩←▸` (see [[lean-identifier-regex-swallows-brackets]]).

**AND THE ONE THING IT BREAKS, which no check in this file previously covered: SCOPE
LINES.** `namespace X`, `section X`, `variable`, `open … in` live in the glue BETWEEN
declarations, and a block's extent runs to the next block's start — so trailing glue
belongs to the preceding block, and replacing that block with theirs DELETES it. Four
scopes were lost in one release. The symptom is never "missing namespace": it is
`Invalid field 'foo': the environment does not contain X.foo` at every use site
(RelativePicard: 75 errors from one dropped `namespace IsRelPicOf`), or
`Unexpected name X after end: the current section is unnamed`.

The check is ten lines and belongs in every merge:

    walk the file, comment-masked; push on `namespace`/`section`, pop on `end`;
    report an `end X` with nothing (or the wrong thing) open, and any scope left
    open at EOF.

**Run it on the RESULT and difference against PRE-MERGE `main`.** This tree has many
legitimate `section Foo … end` + `end Foo` patterns that the naive check flags; only the
NEW reports are yours. Three of the seven X0 reports were pre-existing and compile fine.

**When you insert the recovered opener, put it where the GAP is, not where the branch's
copy sits.** I inserted `namespace IsRelPicOf` immediately before an existing opener and
gave a whole block the doubled name `Fermat.IsRelPicOf.IsRelPicOf.zeroPoint` — same 75
errors, new cause. **Lean's `linter.dupNamespace` warning named it exactly**, and it was
sitting three lines above the first error in the same log. Read the warnings before the
errors when a merge goes red; they are about causes and the errors are about symptoms.

### The four post-merge checks, in the order they pay off

1. **Scope balance** (above) — seconds, catches whole-module failures.
2. **Every branch-ADDED declaration present in the tree.** Compute "added" as
   branch-decls minus MERGE-BASE-decls, and match on the LAST COMPONENT against the
   whole tree — not the qualified name in the one file, or every relocation and every
   re-nesting reads as a dropped payload. With last-component matching, 23 branches
   reported **zero** missing; with qualified matching the same tree reported eight
   false positives and I chased two of them.
3. **Duplicate declaration names**, namespace-qualified, differenced against pre-merge.
4. **Block-comment nesting depth zero** in every file.

Then the build, three rounds minimum — the errors are serialised behind each other by
the import graph, so round *n* only reveals what round *n−1* was hiding.

## A DUPLICATE PAIR IS A DECISION, AND "DELETE THE LATER ONE" IS OFTEN WRONG

(Release 26, `X0.lean`, five duplicates that predated the batch and made the module —
and everything importing it — unbuildable.) `has already been declared` is a hard error,
so a duplicate must go; but WHICH copy goes is a mathematical choice, and the two cases
look identical to any scan.

* **Byte-identical bodies** → delete the LATER copy. Consumers in both regions then
  resolve upward to the survivor. Deleting the earlier one puts every consumer between
  the two positions above its own declaration. (Three CM-table declarations, ~9k lines
  apart, went this way.)
* **DIFFERENT statements** → the later copy is usually a strengthening somebody landed
  without retiring the original, and the naive "delete the later one" throws the
  generalisation away. `isReduced_geomFibre_nTorsion_of_natCast_ne_zero` and
  `etale_nTorsion_of_natCast_ne_zero` existed at `3 ≤ n` (three live consumers) and at
  `n ≠ 0` (**no consumers anywhere**), the latter over a generalised
  `isFinite_flat_nTorsion_of_ne_zero`. Deleting the later pair would have been the easy
  move and would also have left that helper free-floating. Keeping the STRONGER pair
  cost one hoist of three declarations and `(by omega)` at two call sites.

The discriminator is not which copy is newer but **which consumers exist and what they
pass**. Grep the call sites first; a copy with no consumers anywhere is the one that can
move.

## A `sorry`-FREE MODULE CAN STILL BE A RELEASE BLOCKER: the truncated-header wound

(Release 26, `InvariantCoarseRing.lean`, `HyperellipticJacobian.lean`,
`IsogenyTrace.lean` — three files no branch in the batch had touched, all red on
`merger` before the batch began.)

The shape, and it is what a textual union merge produces when two branches RENAME the
same theorem: the union keeps BOTH headers, the first gets truncated after a binder
line or two, and the second one's orphaned docstring tail lands between them as bare
prose. Lean reports `unexpected token; expected ':'` at the prose line — a *syntax*
error hundreds of lines from anything anyone edited, which reads like corruption rather
than like a merge.

Repairing it is mechanical once seen: delete the truncated header and the orphaned
prose, keep the complete declaration, and **repoint the consumers of the dead name** —
there are usually one or two, and the surviving signature usually accepts them
unchanged (here a `[PerfectField k]` caller supplied `Algebra.IsSeparable` as an
instance). Then look for the *other* half of the same wound: a declaration under the
retired name whose body is byte-identical to the survivor's and which nothing consumes.

**And the same release produced two more instances of the general rule that a signature
can drift out from under a call site with nothing failing until much later:**
`GeomPic.bcDiv_injective` had lost its surjectivity argument and one call site still
passed it; `isDomain_tensorProduct_of_isTranscendenceBasis` had GAINED a separability
argument and one caller did not. In both cases the fix was two characters and the cost
was a build round. **A theorem whose signature you change is not done until
`git grep` over its name is clean** — and if the caller is a branch of a `by_cases`
whose own comment says the other branch covers every case, delete it rather than repair
it. The comment is a licence; use it.

## A DOCSTRING'S "MISSING PIECE" LIST IS ABOUT ABSENCE — GREP THE IMPORT CONE BEFORE BELIEVING IT

(2026-07-31, `flt-lean-109`.) `isMultiplicativeType_corner_of_connected_of_inertiaLevelOneFlag`'s
docstring named exactly one obstruction and told the next owner what to do about it: *"The missing
formal piece is the 'precomposition with a surjective bialgebra map is a monoid hom on points'
lemma; `AlgHom.comp_convMul_distrib` is the POST-composition analogue and is the model to copy.
Whoever writes it should state it as its own named leaf."* Precise, actionable, and **wrong in both
directions**:

* mathlib already has the precomposition lemma — `AlgHom.convMul_comp_bialgHom_distrib`, sitting
  four lines above the postcomposition one the docstring cites as the model;
* and this project had ALREADY wrapped it for its own bare-hom convolution monoid five days
  earlier, as `algHom_convMul_comp_bialgHom` / `algHom_convOne_comp_bialgHom` in
  `Deformations/RepresentationTheory/FlatPointsGroup.lean` — reachable from the file in question
  through its own `public import` of `Modularity/Interface.lean`.

This is the same failure the memory `flt-inventory-audits-understate-what-exists` records, one
level up: an audit is reliable about *what the argument needs* and unreliable about *what exists*.
The docstring writer searched for the shape they expected to write and did not search the tree.

The check is two greps and it is worth running against EVERY "missing"/"unwritten"/"needs a new
lemma" claim before you write a line:

    grep -rn '<the mathlib-ish name>' .lake/packages/mathlib/Mathlib/ | head
    grep -rn '<the concept, 2-3 spellings>' --include=*.lean Fermat/ | head

and when the docstring names a "model to copy", **read the model's file** — the analogue you want
is usually its neighbour.

Second half of the same lesson, and it cuts the other way: the docstring ALSO described the
remaining step as bookkeeping (*"intersecting the ambient flag with the image gives an
inertia-stable chain"*). That one was harder than advertised — `AddSubmonoid.comap` of a one-step
extension is not a one-step extension on the nose, and the proof needs the primality of `p` (via
`ZMod p` being a field) or else a maximal-order choice of generator. It came to ~120 lines against
the ~25 of the bijective transport beside it. **So a docstring's difficulty estimates are
hypotheses in both directions: the "missing" piece was already written, and the "bookkeeping" piece
was the real work.** Cost of not checking: one leaf re-proven, one leaf under-budgeted.

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

## A "this field is PINNED" docstring is a LEMMA — cash it in before cutting

(2026-07-31, `flt-lean-370`, `HyperellipticJacobian.lean`.) Structures in this development
are routinely defended against vacuity in prose: `GeomPic`'s section docstring argued at
length that `fieldAct σ` is *determined* by its two axioms, hence that the leaves quantified
over `gp` are model-independent. That argument was never written in Lean, and the cost was
invisible: the derived facts it implies were unavailable, so nobody could use them.

Proving it is usually cheap and pays immediately. `fieldAct_eq_of` — any ring map that is
`σ` on constants and fixes the two coordinates IS `fieldAct σ` — is 30 lines over the
structure's own `gen` field plus `transcendental_xx`, and it yields `fieldAct_mul`,
`placeAct_mul`, `divAct_mul` and finally **`act_mul`: the Galois action on `Pic⁰` is a group
action**. None of that is an axiom, and none of it can be added as one without making
`exists_geomPic` harder.

That mattered concretely: a Kummer cochain `σ ↦ act σ Q − Q` has NO coset structure until
`act` is known to be multiplicative, so "the cochain factors through a finite quotient of
`Γ`" cannot even be *stated*. With `act_mul` in hand, `finite_kummerCochains_pic` — a leaf
carrying the whole arithmetic of weak Mordell–Weil — became a PROOF over two smaller inputs.

So when a structure's docstring says a field is pinned, forced, or determined: **write that
lemma first.** It is the one piece of the development guaranteed to be provable from the
axioms as they stand, and it is what the interesting proofs turn out to need.

**Same day, same file, the sibling lesson: compare a leaf to its CALL SITE before proving
it.** `geomPic_divisible` asked for `∀ n ≠ 0, ∀ y, ∃ z, n • z = y` — divisibility of the
entire geometric Picard group, i.e. surjectivity of an isogeny on the points of an abelian
surface. Its single consumer used it as `fun P => geomPic_divisible gp p hp.ne_zero (bc P)`:
one prime, and only on the image of `bc`. The leaf was DELETED and its content folded into a
statement matching the call site. A leaf quantified more widely than anything consumes it is
a harder theorem that nobody asked for, and the over-quantification is invisible unless you
go and read the consumer.

## A LEAF'S OWN DOCSTRING NAMES THE CLASSICAL PROOF — WHICH IS OFTEN THE WRONG CUT

(2026-07-31, `flt-lean-370`, `HyperellipticJacobian.lean`, immediately after the two
lessons above and in the same cluster.) `placeAct_transitive` — Galois is transitive on the
geometric places above a place of `F` — carried a docstring giving the textbook argument:
the places above `v` are the `ℚ`-embeddings of the residue field `κ(v)`, and `Gal(ℚ̄/ℚ)` is
transitive on those. Correct mathematics, and a **dead end in this file**: it needs the
residue field of an ARBITRARY place, and the file has residue fields only at the NAMED
points (`finrank_residue_pt_eq_one`, and the whole `exists_localDenom_*` machinery under it).
Following the docstring means first building general residue theory.

The cut that worked ran the other way. The leaf lives over `ℚ̄`, and over an algebraically
closed field **every place IS a named point** — so the general-position tool is not needed,
because base change made the general case special. `placeAct_transitive` then became a proof
about the COORDINATES of two rational points (ordinary field theory: extend `a ↦ a'`, fix the
sign of `b` with the other root of `X² − f(a')`), over one new leaf that contains no Galois
group at all. Same leaf count, and the residue theory is no longer on the path.

Generalise: **when a leaf's stated classical proof needs a tool the file only has in special
position, look for a change of base that puts you in special position.** The docstring is
evidence about the mathematics, not about the cheapest route through *this* development —
and it was written before anyone tried.

Two corollaries worth having separately.

**A hypothesis can be discovered by the recut, and threading it is cheap if you check the
call sites first.** The new leaf is FALSE without separability of the sextic (with a double
root the plane model is singular and TWO places sit over one rational point, so `pt` is not
surjective), so `placeAct_transitive` and `geomPic_descent` both had to gain `hsep`. That
looked like the class-7 interface-split hazard until the call sites were counted: exactly
ONE, and it already had the hypothesis. Count them before you decide a hypothesis is too
expensive to add.

**A mathlib instance can fail to apply because a DIFFERENT, equal instance won synthesis.**
In this file `Algebra ℚ (AlgebraicClosure ℚ)` resolves to `DivisionRing.toRatAlgebra`, not to
`AlgebraicClosure.instAlgebra` — so `Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` does NOT
synthesise, and neither does `IsIntegral`, any `minpoly` argument, or `algHom_bijective`. The
symptom is a bare "failed to synthesize" for a fact mathlib obviously has, and `#synth` on the
*carrier* instance is what diagnoses it. The repair is three lines and belongs in the file
once, as a declared instance:

    have h : (DivisionRing.toRatAlgebra : Algebra ℚ K) = AlgebraicClosure.instAlgebra ℚ :=
      Subsingleton.elim _ _
    have hb := AlgebraicClosure.isAlgebraic (k := ℚ)
    rw [← h] at hb

Minor but it cost a compile cycle: `open Polynomial` at the top of this file is NOT in scope
at line 7000 — intervening `end`s closed it — so `aeval`, `X` and `ℚ[X]` are unknown there.
Wrap a new block in `section ... open Polynomial ... end` rather than opening it globally,
which would change name resolution for the 1500 lines below.

## ASK WHAT THE CRUDE BOUND ALREADY GIVES — the sharp estimate is usually the wrong thing to make cheap

(2026-07-31, `taylor_of_isFontainePresentation` in `ModThree.lean`.) That leaf carried
THREE successive route notes, written on two different days by two different owners, each
of which removed machinery the previous had called unavoidable — and all three still
over-bought, because all three were estimating the cost of the same *shape* of argument:

1. write a Hasse-derivative API for `MvPowerSeries` (the pin has one only for univariate
   `Polynomial`), plus `MvPowerSeries.subst`, and bound each `|r| ≥ 2` term of
   `P(w+μ) = Σ_r (∂^[r]P)(w)·μ^r` using `r!·∂^[r]P = ∂^r P` and `3 ∣ r! → |r| ≥ 3`;
2. *(sharpening)* do the Hasse theory for `MvPolynomial` instead, since `mk_adicEval`
   reduces the whole statement to the degree-`< n+1` truncation;
3. *(sharpening)* only the terms of `μ`-degree `≤ 2` need a divisibility statement, and
   those follow in three lines from `pderiv_eq` and `coeff_pderiv` — "what remains is the
   EXPANSION itself, an identity in `𝒪₃ᵥ[[X ⊕ Y]]`", via `MvPowerSeries.subst`.

Note (3) is *correct*, is the observation that unlocked the leaf, and STILL named the
wrong residue. The expansion is not an identity anybody has to write. What closed the
leaf was:

* the CRUDE first-order estimate — remainder in `(μ)²`, **no hypotheses at all**, one
  `MvPolynomial.induction_on` with one nontrivial case; then
* a single case split per monomial, because the crude estimate is short by exactly one
  factor of `3`: either the COEFFICIENT supplies it (some exponent prime to `3` ⟹ that
  exponent is a unit ⟹ `coeff ∈ (3)`), or the monomial is `g(X³)` and the SUBSTITUTION
  supplies it, since `(w+μ)³ − w³ = 3w²μ + 3wμ² + μ³` and the crude estimate applied at
  the cubed coordinates already lands where it must.

No divided powers, no Hasse derivatives, no `subst`, no `𝒪₃ᵥ[[X ⊕ Y]]`. ~200 lines, all
of it statements about `MvPolynomial` alone.

**The reusable rule: when a leaf's docstring says "this needs theory `T`", the first
framing has usually fixed the SHAPE of every later estimate, and the sharpenings inherit
it. Before costing `T`, ask what the crudest available bound gives and how far short it
falls.** A crude bound with no hypotheses plus a patch for the one case where it is short
is a different proof, not a cheaper version of the same one — and it is the one that is
usually already in reach. This is the same failure the memory note "leaf cost estimates
are hypotheses" records, one level up: not "the cost is wrong" but "the *shape* being
costed was never questioned".

Corollary for docstrings: when you close a leaf by a route its docstring did not
prescribe, REWRITE the docstring to the route taken and keep the rejected ones with a
one-line reason. The next owner of a sibling leaf is reading it for the shape, not the
details.

## "NOT IN MATHLIB, NOT IN `~/cs/FLT`" — CHECK YOUR OWN IMPORT LIST FIRST

(2026-07-31, `exists_idempotentLocalQuotient`.) That leaf's docstring prescribed a
four-step programme — `A` is `3`-adically complete, `A/3A` is artinian hence a product of
local rings, lift the primitive idempotents along the complete surjection, take `ε` to be
the lift of the sum of the ones `ū` kills — and called it "the half of the parent that can
be attacked without any of the complete-intersection theory", i.e. a genuine but bounded
piece of commutative algebra.

The whole programme was already proven in-tree, sorry-free, in a file **`ModThree.lean`
itself publicly imports** (line 435): `exists_isIdempotentElem_isLocalRing_quotient_of_moduleFinite`
in `Fermat/FLT/Mathlib/RingTheory/AdicCompletion/Finite.lean`, whose own docstring opens
by saying it supplies "what a survey of the mathlib pin found to be genuinely absent: the
decomposition of a module-finite algebra over a complete Noetherian local ring into local
factors". Given it, the leaf is ~30 lines: show `ker ū` is maximal (`A ⧸ ker ū` embeds in
the FINITE residue field `𝒪_E/𝔪`, so it is a finite domain, hence a field), feed it in,
and take `ε := 1 − e`.

The existing memory note is "missing machinery may be DOWNSTREAM" — in a file that imports
yours. This is the *easier* case and was missed anyway: it was UPSTREAM, in this module's
own import list, put there by an earlier owner for a different consumer. So the check
before writing any "expect to build it" in a docstring is mechanical:

    grep -n "public import" <your module> | ...        # then grep those files for the concept
    grep -rn "IsLocalRing\|IsIdempotentElem\|Henselian" Fermat/FLT/Mathlib/ | ...

`Fermat/FLT/Mathlib/**` in particular is where every agent's general-purpose commutative
algebra lands, it is small, and it is the first place to look — it exists precisely
because the pin was missing something.

## THE SENTINEL TOKEN IN YOUR PROMPT CAN BE STALE — READ IT FROM THE JOB RECORD

(2026-07-31, `flt-lean-310`. Caught with four commits already on the branch and the
sentinel already written under the wrong token.)

Every prover agent is told: *"`token` — copy it verbatim or the loop ignores the whole
file."* That is true, and the token printed in the prompt is **not always the one the
loop will accept.**

`flt-loop.py` accepts a sentinel whose token is `j["token"]` **or** a member of
`j["prev_tokens"]` (line ~877). Its comment says a resumed job is the same job, so an
earlier incarnation's result is still its result. But `grep -n prev_tokens flt-loop.py`
finds exactly **two** occurrences — the read at 877 and the field-copy at 1033. **Nothing
ever writes it.** It is always `None`.

**CORRECTED 2026-07-31 (`flt-lean-115`): `prev_tokens` IS populated now.** A resumed job
observed on that date read `token: 0028aee5, prev_tokens: ['4f1d1581'], retries: 1,
resume: true`, with `4f1d1581` being exactly the token its prompt carried. So the
fallback the loop reads really does fire, and copying the prompt's token verbatim on a
resumed job is no longer fatal. **Do not relax the check on that account.** The
canonical value is still `j["token"]` — the loop overwrites the sentinel's token with it
at line 1039 — the field could stop being written again as easily as it started, and
reading it costs one command. Cross-check `j["session"]` against your own session id
while you are there; it is the second, independent confirmation that you are the live
owner rather than a discarded twin.

Meanwhile resume mints a NEW token, deliberately, so the old `.started` marker goes
inert. The agent's prompt is the ORIGINAL payload and still carries the ORIGINAL token.
So on any job with `resume: true` / `retries > 0`:

* the live token is in `~/.flt-loop/jobs/<name>.json` and `<name>.started`;
* the prompt's token is the pre-resume one;
* a sentinel written under the prompt's token is rejected, `j["sentinel"]` stays `None`,
  and `started ∧ ¬alive ∧ ¬sentinel` makes the loop conclude the agent **died**.

The result is the worst shape of failure this file catalogues: completed, committed,
compiler-verified work is thrown away, and a replacement is dispatched at leaves that are
already proven — a phantom dispatch manufactured out of a *successful* run.

**So the check is one command, run it before writing the sentinel:**

    python3 -c "import json;j=json.load(open('/home/chend/.flt-loop/jobs/<name>.json'));print(j['token'], j.get('prev_tokens'))"
    cat /home/chend/.flt-loop/jobs/<name>.started

**Write the token the RECORD holds, not the token the prompt holds.** If they agree,
nothing is lost by having checked. If they disagree, the record wins — the loop reads
`j["token"]` out of that file and compares against it, and line 1039 shows the loop
itself overwrites the sentinel's token with `j["token"]` once it accepts one, which
settles which of the two is canonical.

This is NOT a `to_medic` case on its own: the workaround is one line and an agent that
performs it lands its work normally. It is a `to_merger` note, and it belongs here so the
next agent does not have to rediscover it with its branch already committed.

Generalisation, and it is the same shape as "a `sorry` is a PROMISE" and "ancestry is not
content": **a value handed to you in a prompt is a claim about state at dispatch time, not
state now.** Prompts are immutable; the state machine is not. Anything in a prompt that
names live state — a token, a line number, a leaf that is "still open", a worktree said to
be owned by someone else — is a hypothesis to check against the state itself.

## AN EXPRESSIBILITY CUT MOVES NO COUNTER AND IS STILL THE WHOLE STEP

(2026-07-31, `flt-lean-204`, on `nonempty_modularTateCarrierData_of_jacobian`.)

Some leaves are not hard, they are **unsayable**. The Eichler–Shimura leaf's own docstring
had diagnosed itself correctly: it was ATOMIC "and it is a statement about EXPRESSIBILITY,
not about difficulty" — the `p`-adic Tate module of `J₀(M)` could not be *written down* in
Lean, because `Fermat.TatePt` takes a `Mult ab R` argument and no `m : Mult ab 𝒪_ℚ` existed.
Every split anyone could state therefore had to quantify over an ABSTRACT carrier of the
right dimension, and such a split manufactures a FALSE leaf (Eichler–Shimura is false for an
arbitrary faithful Hecke module of the right dimension).

The cut that unblocks it adds the missing datum as a HYPOTHESIS and discharges it in glue:

    theorem X_of_mult … (m : Mult ab 𝒪_ℚ) : C := sorry      -- the leaf, now sayable
    theorem X … : C := by obtain ⟨m⟩ := nonempty_mult_ringOfIntegersRat ab; exact X_of_mult … m

Here `Mult ab 𝒪_ℚ` is free — `Rat.ringOfIntegersEquiv : 𝒪_ℚ ≃+* ℤ` and every abelian group is
a `ℤ`-module, so `act a y := (Rat.ringOfIntegersEquiv a) • y` and the six axioms are the
`zsmul` laws plus `map_zsmul` on the additive map `RelPoint.pre`. Fifty lines, first try.

**Two things to carry forward.**

- **The sorry count does not move**, and neither does the transitive count: one leaf in, one
  leaf out, plus a proven construction. To `flt-frontier.py` and to the `declaration uses
  'sorry'` warning set this cycle produced *nothing*. It produced the only step that made the
  next four possible. So do not judge a cycle by the delta, and do not let a leaf sit because
  the work under it "would not close anything".
- **The tell is in the leaf's own docstring**, and it is a phrase, not a feeling: a leaf that
  says a split "cannot be stated", "would manufacture a false leaf", or "the object does not
  exist yet" is an expressibility leaf, and the task is to BUILD THE OBJECT, not to attack the
  mathematics. Read the docstring for that phrase before costing the leaf as hard.

Corollary for whoever writes the construction: **it must land with its consumer in the same
commit**, since a free-floating definition is not allowed here — which is why the restatement
and the construction are one edit and not two.

## SIBLING LEAVES COSTED AT DIFFERENT DEPTHS MAY BE ONE LEAF — test it before costing either

(2026-07-31, `flt-lean-204`, on the two halves of strong multiplicity one in
`Modularity/Interface.lean`.)

A cut had split one leaf into two and written a careful paragraph explaining that they "want
different machinery and are of different depth": one was inside the Atkin–Lehner theory the
file was already building and "could plausibly be closed without new analysis"; the other
needed Rankin–Selberg or the adelic dictionary, "an input this pin lacks entirely", and
"anyone attacking this leaf should expect to BUILD one of the two missing analytic theories".

**Both were the same leaf.** Each is two lines over one statement — newform block independence
at a common level — instantiated at a different common multiple of the two levels. The
asymmetry was an artefact of reading each leaf's hypothesis at face value: the "deep" one
looked deep because its agreement set was smaller, and the smaller set really does defeat the
obvious attack (Hecke recursion never reaches a NEW prime — that part of the old note was
correct). But the route that closes the sibling does not use recursion; it changes level, and
at the larger level the weaker hypothesis is already enough.

**The general test, and it is cheap.** When a cut leaves siblings, take the machinery named as
missing for the EASY one and ask whether it also discharges the HARD one. Here that was five
minutes of reading and a 10-second scratch verify. Two leaves became one, three declarations
became glue, and — the point that outlives the instance — nobody will now be dispatched to
build Rankin–Selberg for a node that does not need it.

**And the reverse reading matters just as much:** a leaf documented as CHEAP because it sits
inside theory the file already has is suspect the moment its cheap route also proves a sibling
documented as expensive. Either the cheap verdict is wrong or the expensive one is. Say which
in the docstring; do not leave the pair contradicting each other, because the next agent will
believe whichever docstring it opens first.

## A BLOCKING HYPOTHESIS IS NOT A MISSING THEORY — READ THE LEMMA THE COROLLARY CAME FROM

(2026-07-31, `flt-lean-204`, on Serre's type-`A₀` core in `Modularity/Interface.lean`.)

The leaf's docstring named the globalisation half as blocked on **Kronecker–Weber**
(`Γℚ^ab ≅ Ẑˣ`), "ABSENT from mathlib at this pin: grepped 2026-07-28, no `KroneckerWeber` in
`Mathlib/`, in `Fermat/`, or in `~/cs/FLT`". The grep was correct and the verdict was wrong.

What the argument needs is *an everywhere-unramified continuous character of `Γℚ` is trivial*.
The tree has `minkowski_character_trivial`, which says exactly that — **but only for a character
with an OPEN KERNEL**, which a `ℚ̄_p`-valued character of infinite image does not have. That one
hypothesis is the entire reason the node read as blocked on a missing theory.

`minkowski_character_trivial` is a five-line COROLLARY of
`open_normal_subgroup_eq_top_of_inertia_le` in the same file, and **the parent needs no open
kernel** — it needs an open normal subgroup containing every inertia image. For a character into
`ℚ̄_p` that is handed over by ultrametric geometry: each ball `{x : ‖x − 1‖ < ε}`, `ε ≤ 1`, is a
multiplicative subgroup, its preimage is open (continuity), normal (the target is commutative,
so a character is a class function), and contains every inertia image; Minkowski makes it `⊤` for
EVERY `ε`; the balls are a neighbourhood basis of `1`, so `ψ = 1`. Forty lines, no class field
theory, no Kronecker–Weber.

**The general rule: when a lemma's HYPOTHESIS is what blocks you, find the theorem it was derived
from.** Corollaries are specialised to their first consumer, and the specialisation is exactly
what gets thrown away. The tree records "we have X" at the granularity of the corollary, so the
parent's extra strength is invisible to any inventory search. This is the third distinct way this
project has manufactured a phantom "missing theory" — after
[searching for how to PRODUCE an object instead of for the deciding invariant] and [reading a
leaf's own MISSING MACHINERY list as reliable about strength] — and all three are cured by
reading the statement rather than the summary.

**Corollary, same day, same proof, and worth its own line: A CONTINUITY YOU CANNOT PROVE MAY BE
HANDED TO YOU BY A HYPOTHESIS.** The glue needs `χ_cyc : Γℚ → ℚ̄_p` continuous, and nothing on
this pin proves `cyclotomicCharacter` continuous — that alone would have sunk the assembly. But
the leaf already carries `hcyc : ∀ γ, δ₁ γ * δ₂ γ = χ_cyc γ`, and `δ₁`, `δ₂` are continuous by
hypothesis, so `χ_cyc` is continuous by `funext` in two lines. Before costing "`X` is
continuous/measurable/finite" as missing machinery, check whether some hypothesis already equates
`X` to something that has the property. In a statement with many hypotheses this is common and
it is easy to miss, because the hypothesis was written for a different purpose.

## "NOT IN MATHLIB" IS NOT "NOT IN THE PROJECT" — check DOWNSTREAM before believing a leaf is expensive

(2026-07-31, `flt-lean-136`.) `finite_setOf_isWeightTwoEigenform` (`X0.lean`) carried a careful
`WHAT REMAINS GENUINELY MISSING` paragraph: mathlib at this pin has no finite-dimensionality of
`CuspForm`, `~/cs/FLT` has none, so a prover must build the valence formula, or a degree bound on
the Hecke field plus a Sturm bound. Every factual clause was TRUE. The verdict was wrong by a
week: **`cuspForm_finiteDimensional` had been proven on 2026-07-24**, in
`Modularity/Interface.lean` — which carries `public import Fermat.FLT.ModularCurve.X0` and is
therefore DOWNSTREAM, so nothing in it is nameable from `X0.lean`.

That is the whole trap, and it is invisible to the natural check. An audit run *in the file that
needs the theorem* asks "can I name it here", and gets the SAME answer — no — for two situations
that could not be more different:

  * nobody has proven it (weeks of work), and
  * it is proven, one import away, **in the wrong direction** (a hoist, sometimes minutes).

The second is common here precisely because this tree grows downward: the big consumers
(`Interface.lean`, 85k lines) accumulate general-purpose machinery that upstream files then turn
out to need. So:

**Grep the WHOLE tree for the missing statement, not the import cone, and when you find it
downstream, check whether its PROOF is upstream-clean.** If the proof mentions only mathlib — no
project predicate, no leaf, no structure defined below — the hoist is mechanical and the leaf was
never expensive. Here the Sturm-bound proof was 100 lines of `ModularForm.norm`,
`sturm_bound_levelOne` and the `q`-expansion API; moving it to `WeightTwoEigenform.lean` cost four
compile errors (`open scoped Manifold`, `open ModularForm` for the `∣[k]` notation, `_root_.one_zpow`
against the file's `open Matrix`, and a stray `qCoeffL` reference), and the leaf then closed.

**Leave the old paragraph's REASONING in place and mark the verdict.** The archimedean route that
docstring proposed is still a correct route; it is simply not the cheapest one, and the record of
what was searched is what lets the next reader see that the search was of mathlib and not of the
project.

Corollary for the hoist itself: **make the downstream copy a one-line delegation, do not delete it.**
Every consumer keeps its name and its carrier (`Interface.lean`'s version is stated in `qCoeff`,
which is `(qExpansion 1 ⇑f).coeff` by definition, so the delegation is `rfl` on the statement), the
diff in the contended file is a few lines instead of a hundred, and there is exactly one proof.

Same day, same worktree, the mirror-image win: two SORRIED copies of one theorem in two files with
two eigenform predicates (`isIntegral_coeff_prime_of_isWeightTwoEigenform` in `X0.lean` and
`isIntegral_qCoeff_prime_of_isWeightTwoEigenform` in `Interface.lean`). Their common refinement —
stated about mathlib's `qExpansion` coefficients and about no project predicate — goes UPSTREAM of
both, and both become assemblies over it. **A carrier move is a real result when it makes two
leaves into one; it is a wash when it makes one leaf into one.** Say which in the commit message,
because the sorry counts alone cannot tell them apart.

## A `∀`-SHAPED LEAF DEFENDED BY "THE OBJECT IS UNIQUE" IS TWO LEAVES PRETENDING TO BE ONE APIECE

(2026-07-31, `X0.lean`, `flt-lean-400`.) A recurring shape in this development: a
universal-property structure `D` (fine moduli, initial object, coarse space), one leaf
asserting `Nonempty D`, and a SECOND leaf asserting `∀ R : D, P R.M` for some
iso-invariant `P`. The second leaf's docstring always defends the `∀` the same way —
"`universal` is a fine moduli property, so any two inhabitants are related by a unique
isomorphism, hence *some* inhabitant satisfies `P` iff *every* one does" — and then
does **not prove it**, because the leaf is sorried anyway.

**That unproven sentence is the whole cut.** Prove it — it is elementary and carries no
citation — and the two leaves collapse into one `∃ R : D, P R.M`, from which both follow.
Here that took ~55 lines and turned `exists_rigidifiedModuliScheme_specF` +
`isAffine_of_rigidifiedModuliScheme_specF` into theorems over a single fused leaf, with
**no signature and no consumer changed** — only the two bodies moved.

Three things make this worth looking for rather than waiting for:

- **The parallelism the cut buys is usually illusory.** Both halves here needed `Y(n)`
  constructed; whoever built it got the second half in the same sentence of Katz–Mazur.
  Splitting them made two agents build the same object.
- **The rigidity proof is cheap when the base-change relation is a CATEGORY.** The
  argument is: feed each inhabitant's universal family to the other's `universal`, then
  observe that `m' ≫ m` and `𝟙` both solve the *same* `∃!`. That needs exactly a `refl`
  and a `comp` for the relation — in `X0.lean` those are `IsBaseChangeOf.refl` and
  `IsBaseChangeOf.comp`, both already PROVEN. Check for them before assuming the argument
  is expensive.
- **Fusing STRENGTHENS the statement, so re-audit faithfulness.** A `∀`-shaped leaf is
  *vacuously true* when `D` is uninhabited; the fused `∃`-shaped one is false there. In
  this instance that made `hn : 3 ≤ n` load-bearing for TRUTH rather than merely for the
  citation. Say so in the new docstring — an inherited faithfulness audit does not survive
  a restatement (see the two-correct-repairs section above).

The counter-consideration, and it is real: this UNDOES a deliberate cut, so it is only a
win if you actually pay the rigidity proof. Weakening `∀ R, P R.M` to `∃ R, P R.M`
*without* proving rigidity is a strict loss, and is what the leaf docstrings were warning
against. Pay it or leave the cut alone.

**Ordering can block it, and that is worth checking FIRST.** The identical fusion applies
to the `ℚ` twins in the same file and was not done, because `IsBaseChangeOf.refl` is
declared ~600 lines BELOW them: the rigidity lemma cannot be stated where it would be
consumed. Hoisting 34k-line-file material is its own merge hazard (see class seven), so
that one was queued rather than attempted.

## A "NEEDS NEW THEORY + A HOIST" VERDICT CAN BE AN ARTEFACT OF THE ROUTE, NOT OF THE STATEMENT

(2026-07-31, `flt-lean-15`, on `eq_two_or_eq_three_of_stableCyclic_j_eq_zero` /
`…_j_eq_1728` in `ModularCurve/X0.lean`.)

Three separate audit passes (2026-07-28, -30) recorded a MACHINERY survey on those two
leaves, by name, and it was accurate: closing them by the recorded route needed (a) a
HOIST of `MazurCMForm` and `classNumberOne_of_end_closure_eq_top` out of
`FreyCurve/MazurTorsion.lean`, which `public import`s `X0.lean` and therefore cannot be
cited from it; and (b) at `j = 0`, "a genuine generalisation of the encoding
(`ψ² = [−n] + b·ψ`)", because the conductor-`p` order `ℤ[pζ₃]` is not `ℤ[√−n]`. The two
`j`-values were split apart precisely because that survey showed their costs differed.

**Both requirements evaporated under a different proof of the same statement.** The
class-number half (`C` not `𝒪_K`-stable ⟹ `h(p²·disc K) = 1`) has an elementary
substitute: `C` and `ψC` are then distinct lines spanning `E[p]`, `G_K` acts by the SAME
scalar on both, so `det ρ|_{G_K} = α²`, and `det ρ = χ_cyc` (Weil pairing) forces every
element of `𝔽_p^×` to be a square. That needs `det_galoisRep_eq_cyclotomic`, which is
PROVEN, and lives in `EllipticCurve/WeilPairing.lean` — **which does not import `X0.lean`**,
so there is no hoist at all. Both leaves are now proven over ONE shared leaf; the frontier
went 2 → 1 and the `j = 0`/`j = 1728` asymmetry that motivated the split disappeared.

The tell, and it is checkable: **a machinery survey enumerates what the RECORDED argument
needs. It never asks whether the conclusion has a second proof.** So when a survey ends in
"hoist X and generalise Y", that is a report about one route, not a lower bound on the
leaf. Spend one pass looking for another argument before paying for the hoist — and note
the shape of the win here: the blocked module was blocked by an import CYCLE, and the
substitute route's module simply was not in the cycle. Check the import direction of the
alternative's dependencies early; it is a one-command discriminator between "expensive"
and "free".

### Corollary technique: NORMALISE OVER THE BASE FIELD, NOT OVER `ℚ̄`

The construction that made the above writable is worth copying verbatim. To get the CM
automorphism as an endomorphism of `(E⁄ℚ̄).Point` **carrying its Galois conjugation law**,
do NOT put `E⁄ℚ̄` into Weierstrass normal form over `ℚ̄`: the normalising variable change is
then irrational and the transport destroys the `hstab` hypothesis. `exists_smul_eq_quarticModel`
/ `…_sexticModel` are stated over an arbitrary `CharZero` field, so apply them **over `ℚ`**;
the change of variables is then `ℚ`-rational, `Affine.Point.equivVariableChangeBaseChange_galois`
makes the transport `Gal(ℚ̄/ℚ)`-equivariant, and every Galois hypothesis survives it unchanged.
The `ℚ̄`-only data (the root of unity) enters afterwards, as the `u` of a diagonal automorphism
of the *rational* normal form. Same pattern applies to any leaf that has to combine a normal
form with a Galois-stability hypothesis.

## A BUNDLED STRUCTURE'S OBJECT FIELDS MAY CARRY NO CONTENT — TEST WITH AN `iff` FIRST

(2026-07-31, `flt-lean-15`, on `exists_eisensteinFormalImmersionAt` in
`ModularCurve/X0.lean` — the section above is the same failure in a different suit,
and the two together are worth reading as one rule.)

This development cuts leaves by BUNDLING: a leaf produces a `structure` whose fields
name the inputs of the textbook argument, so that "a partial advance on any one of them
is visible". `IsEisensteinFormalImmersionAt` is the archetype — five object fields
(`Eis`, `EisRed`, `ajE`, `ajE'`, `redE`) spelling out Mazur's Eisenstein quotient
`J_e(p)(ℚ)`, its reduction, and the two Abel–Jacobi maps — and **four separate audits
recorded IRREDUCIBLE on the strength of them**: "`J_0(p)`, the Hecke algebra, the
Eisenstein ideal and reduction of an abelian variety are all missing."

All four were auditing a *docstring*. `Eis` and `EisRed` are bare `Type`s under an
existential, so they can be taken to BE the special fibre, with `ajE = redX` and
`ajE' = redE = id`; `red_ajE` is then `rfl` and `redE_inj` is `Function.injective_id`.
The whole structure is inhabited **iff** two conditions on `redX` alone hold —
injectivity on the cuspidal locus, and `cusp_lift`. No abelian variety is asked for
anywhere in the statement. The `iff` is nine lines and now sits in the file.

**The check, and it costs one theorem.** Before believing that a bundled leaf needs a
missing THEORY, ask which of its fields are pinned by the others and which are free:

- a field of type `Type` (or any `Sort`) inside an existential is FREE — nothing
  outside the structure can observe it, so it can be instantiated at anything already
  in scope, usually the object the leaf is quantified over;
- a field whose value is forced by a stated equation (`red_ajE` here) is free once
  its neighbours are chosen to make that equation `rfl`;
- an injectivity/faithfulness field is free at the identity;
- what is NOT free is any field constraining data the leaf receives as a HYPOTHESIS —
  here `redX`, which arrives inside `IsX0JReductionAt` and is what the leaf really
  demands a theorem about.

Then state the reduced form and PROVE the `iff`. If it goes through, the reduced form
is the honest target and the anatomy was decoration; if it does not, you have learned
exactly which field is load-bearing. Either outcome is worth the theorem.

**This is NOT a way to make a leaf cheap, and expecting that is the trap on the other
side.** The reduced form here is still Mazur — the two junk reductions that `red_jm`
permits each die against the condition the other satisfies, and (A) ∧ (B) at `q`
already imply that no rational point of `Y_0(p)` has a `j`-pole at `q`. What the
reduction buys is that the next prover is not sent to build `J_0(p)`, the Hecke
algebra and the Eisenstein ideal in order to discharge fields that `id` discharges.
Vacuous OBJECTS, undiminished CONTENT: keep the two apart when reporting.

Corollary for writing new bundled leaves: the argument that bundling "leaves the least
for a prover to invent" is right about the fields that are pinned and wrong about the
free ones, and the free ones are pure noise in the statement. Carry the anatomy in the
DOCSTRING, where it costs nothing and misleads nobody, and keep it in the type only
where something outside the structure observes it.

## `rw` FAILS ON A COERCION THE GOAL DISPLAYS IDENTICALLY — USE `refine Eq.trans`

(2026-07-31, `flt-lean-15`, proving `eq_two_or_eq_three_of_stableCyclic_of_autPoint_not_stable`
in `ModularCurve/X0.lean`. Three of five compile iterations went to this one trap.)

`Field.absoluteGaloisGroup ℚ` reaches `AlgHom` by more than one coercion path — via
`(σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom`, and via the `AlgHomClass`
instance directly. **Both pretty-print as `↑σ`.** So the failure reads:

    Tactic `rewrite` failed: Did not find an occurrence of the pattern
      (Point.map ↑σ) (ψ g)
    in the target expression
      (Point.map ↑σ) (ψ g) = k • ψ g

— the pattern and the target are *character-for-character identical on screen* and are
different terms underneath. Restating the step in the hypothesis's own syntax does NOT
help; a `have step : <hcomm's exact syntax> := by rw [hcomm …]` failed the same way,
because it is the ELABORATION that differs, not the source text.

**The fix is to stop using `rw` for that step.** `exact`, `refine` and `Eq.trans` unify
up to defeq, so they cross the coercion boundary for free:

    refine Eq.trans (hcomm (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) hσv g) ?_
    refine Eq.trans (congrArg ψ hk.symm) ?_
    exact map_zsmul ψ k g

Same trap, same cure, three more times in that one proof: `↑G` vs `g` after `set`
(fixed by `show _ = … • g`), an instance-level mismatch on `Module.finrank` inside
`LinearMap.det_smul` (fixed by `exact hdetscal _` instead of `rw [hfr]`), and
`(c • P).1` under a `Subtype.ext`. **Rule of thumb: when a rewrite fails and the printed
pattern equals the printed target, the terms differ by a coercion or an instance — switch
to a defeq-checking tactic rather than hunting for the right `simp` lemma.** Turning on
`set_option pp.explicit true` shows the difference if you need to see it.

Corollary, and it is why this cost so little in the end: **develop against a scratch
module.** Iterations on `Scratch15.lean` (one `public import`, ~120 lines) were **5
seconds** each; the same edits against `X0.lean` are a full rebuild of 82 000 lines. Five
iterations of blind coercion-fighting is a fine trade at 5 s and unaffordable at 30 min.

## A MACHINERY SURVEY THAT NAMES *ONE* MISSING ITEM IS USUALLY RIGHT — CUT EXACTLY THAT

Same leaf, and it is the counterweight to the two sections above (a survey that ends in
"hoist X and generalise Y" being an artefact of the route, and four audits auditing a
docstring's anatomy). Those say surveys OVER-state. This one under-stated nothing:

`eq_two_or_eq_three_of_stableCyclic_of_autPoint_not_stable`'s docstring ended
"**GENUINELY MISSING, and the only thing that is**: `K ⊄ ℚ(μ_p)` for `p ≥ 5`". That was
exactly true. Cutting precisely that sentence as its own leaf
(`exists_galoisFixing_cyclotomic_not_isSquare`) and proving *everything else* closed the
node — and the residue is a statement about cyclotomic fields with **no elliptic curve in
it**, provable by someone who never reads `X0.lean`.

The discriminator between this case and the two bad ones is cheap and worth applying:
**does the survey name a specific PROPOSITION, or a body of THEORY to build?** "`K ⊄
ℚ(μ_p)` for `p ≥ 5`" is a proposition — state it, sorry it, prove the rest. "the
Eisenstein quotient, the Hecke algebra and reduction of an abelian variety" is a body of
theory, and that is the shape that turns out to be decoration. A survey naming one
proposition is a gift: the cut is already written.

Two facts the formalisation turned up that no survey predicted, both worth the habit of
re-reading hypotheses after the proof compiles: `hψ`, injectivity of the CM automorphism,
is **never used** (`hnot : ψ g ∉ ⟨g⟩` already gives `ψ g ≠ 0`, since `0 ∈ ⟨g⟩`); and `ψ`
is only ever an **additive** endomorphism, never an isogeny — additivity alone gives
`ψ(E[p]) ⊆ E[p]` and `ψ(k·g) = k·ψ(g)`, which is the whole of what the determinant
argument consumes.

## CONSTRUCT THE ELEMENT; DO NOT PROVE THE GROUP IS BIG

(2026-07-31, `flt-lean-15`, closing `exists_galoisFixing_cyclotomic_not_isSquare` — the
leaf the section above says was correctly cut. It is the sequel to that section: the
survey named the right PROPOSITION, and was still wrong about the ROUTE.)

The leaf asks for `σ ∈ G_ℚ` fixing `v` (`v² = −1` or `v² + v + 1 = 0`) with `χ̄_cyc(σ)` a
non-square mod `p ≥ 5`. Its docstring surveyed two routes and recommended the second:

1. Frobenius + `cyclotomicCharacterModL_globalFrob` — rejected, needs **Dirichlet on
   primes in arithmetic progressions**, which is genuinely not in this tree;
2. a **degree computation**: `K ⊄ ℚ(μ_p)` because `φ(4p) = 2(p−1) ≠ p−1 = φ(p)`, hence
   `K ∩ ℚ(μ_p) = ℚ`, hence `χ̄_cyc` is onto on `G_K` — via `IsCyclotomicExtension.finrank`,
   `Nat.totient_mul` and "the bookkeeping of subfields of `AlgebraicClosure ℚ`".

The proof that closed it does neither. It **never mentions `K`, never compares two
degrees, and never intersects two subfields.** It builds `σ` directly: work at the
COMPOSITE level `m = n·p` (`n = 4` or `3`), take `c` with `c ≡ 1 mod n` and `c ≡ a mod p`
for `a` a non-square (`Nat.chineseRemainder`, legitimate exactly because `p ≥ 5` makes
`gcd(n,p) = 1`), and realise `c` as an automorphism. It fixes `v` because `v ∈ μ_n` and
`c ≡ 1 mod n`; it acts on `μ_p` by `a` because `c ≡ a mod p`. **90 lines, three mathlib
citations, no number theory of `K` at all.**

**The general shape, and it is worth reaching for by default.** Route 2 proves *the image
of a character is large*, then extracts an element from a large group. Constructing the
element skips the middle step — and the middle step is where all the cost was, because
"the image is large" is a statement about a lattice of subfields while "here is the
element" is a statement about one automorphism. Ask which one you actually need. A leaf
of the form `∃ σ, P σ` almost never needs a surjectivity theorem.

**Why it is specifically cheap here: irreducibility of `Φ_m` over `ℚ` is ONE theorem
covering every `m` at once.** `Polynomial.cyclotomic.irreducible_rat` feeds
`IsCyclotomicExtension.autEquivPow` (`Gal(ℚ(μ_m)/ℚ) ≃ (ℤ/m)ˣ`) at level `n·p`, and
`AlgEquiv.liftNormal` extends to `ℚ̄`. The fact `K ∩ ℚ(μ_p) = ℚ` that route 2 would have
established by a totient count is *carried for free* by that one citation. So when a
survey proposes to prove a compositum is as large as possible, check whether a single
irreducibility/degree theorem at the composite modulus already says it.

Reusable pieces this left in `X0.lean`, both stated over an arbitrary modulus and worth
knowing about before re-deriving them: `exists_algEquiv_pow_of_coprime` (surjectivity of
the mod-`m` cyclotomic character of `ℚ`, phrased as "some `σ` raises every `m`-th root of
unity to the `c`") and `exists_galoisFixing_cyclotomicCharacterModL_eq` (the CRT step).

### The `Algebra ℚ ℚ̄` diamond bites every proof that touches `AlgebraicClosure ℚ`

Already documented in `QuarticTwist.lean` and `ComplexConjugation.lean`, repeated here
because it cost an iteration and the symptom is unhelpful: **`Algebra.IsAlgebraic ℚ ℚ̄`
and `IsAlgClosure ℚ ℚ̄` do not synthesise anywhere in this tree**, because search finds
`DivisionRing.toRatAlgebra` while mathlib's instances are stated for
`AlgebraicClosure.instAlgebra`. `IsAlgClosed ℚ̄` *does* synthesise, so the failure looks
arbitrary. Supply them by hand — the `Patching.lean` idiom, which is four lines and works:

    haveI halgQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    haveI hacQ  : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, halgQ⟩
    haveI hnormQ : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
    haveI hintQ : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := halgQ.isIntegral

Do not try to fix it by re-declaring the mathlib instance in your file; the diamond is in
the `Algebra` instance itself, so no re-export reaches it.

And the coercion trap two sections above fired **twice more** in this proof, both times
in its documented shape — printed pattern equal to printed target, `rw` unable to cross:
once on `absoluteGaloisGroup ℚ`'s type ascription (cured by `Eq.trans`), once on
`autEquivPow`'s forward map versus `(zeta_spec …).autToPow`, which are the same function
behind a `MonoidHom`/`MulEquiv` coercion (cured by *stating* the equation and closing it
with `exact`, letting the defeq check do the work). Treat that pair as the standard cure.

## YOUR SENTINEL TOKEN CAN GO STALE WHILE YOU WORK — RE-READ `.started` BEFORE WRITING IT

(2026-07-31, `flt-lean-15`. Cost nothing only because it was noticed; the failure mode is
total, silent, and looks exactly like dying.)

The token in your task prompt is the token that was current **when you were spawned**. The
loop ROTATES it whenever it resumes a job. So an agent that is resumed mid-run — which is
routine, and is what a bare `continue` usually is — holds a prompt naming a token the loop
no longer accepts. Concretely, on this run:

    prompt said        115c51de
    .started said      6c69a75c   (rewritten 5 minutes AFTER the sentinel was written)
    .json said         6c69a75c   with "resume": true and this session's own id

A sentinel written under the old token is **ignored in full** — `queue`, `to_merger` and
all. The loop then sees no sentinel, concludes the agent died, and starts a replacement on
the same worktree. Everything the run learned is discarded, and the branch is left for a
successor who will re-derive it. Note the shape: the work was committed and green, the
report was written and accurate, and it would still have evaporated.

**So the sentinel write is a two-step, always:**

    cat ~/.flt-loop/jobs/<worktree>.started      # the token the loop expects RIGHT NOW
    # write the sentinel using THAT, not the one in your prompt

`.started` is authoritative; `.json`'s `token` field agrees with it and is a fine
cross-check. If they disagree with your prompt, your prompt is the stale one — you were
resumed. Rewriting an already-written sentinel with the fresh token is correct and safe:
the content is unchanged, only the freshness handshake moves.

Corollary, and it is the general form of this and of the `flt-loop spawn/liveness race`
note: **any identifier the loop handed you at spawn is a snapshot, not a fact.** Re-read it
from disk at the moment you need it. The loop's whole state is on disk precisely so that
this is possible; reasoning from what your prompt said is reasoning from a cached value.

Second corollary, for whoever is checking whether work got lost: `~/.flt-worktree-pool`
reading `batched` does NOT mean your sentinel was accepted. Those are independent pieces of
state, and this run observed `batched` while its sentinel was being ignored.

## AN "IRREDUCIBLE / NEEDS A CITATION" VERDICT IS ABOUT THE DOCSTRING'S STORY, NOT THE STATEMENT

(2026-07-31, `nonempty_isJLineZ` in `X0.lean`.) The leaf carried a citation verdict —
"Igusa; `Y_0(1) ≅ 𝔸¹_j` over `ℤ`" — backed by a survey that is *correct*: there is no
integral model of a modular curve in mathlib at our pin, in `~/cs/FLT`, or in this
project. Two agents had recorded and re-recorded it. **The statement does not mention a
modular curve.** `IsJLineZ N R` asks, field by field, for the `j`-invariant of the
elliptic scheme underlying a `Γ₀(N)`-datum over an `R`-scheme, read as a point of
`𝔸¹_R`. There is no `Y_0`, no compactification, no cusp in it.

So the verdict was scoped to the *object the prose names* rather than to the *statement
the compiler sees*, and the check that refutes it costs one grep: **read the conclusion
field by field and look for the object the verdict is about. If it is not there, the
verdict is about the story, not the leaf.** This is the same failure shape as
"AUDITS SEARCH PRODUCTION, NOT INVARIANTS" and "THE SELF-CERTIFYING GREP", one level up:
the survey was run against a true sentence that was not the theorem.

**What was actually in the way was a PARAMETER PINNED AT A SPECIAL VALUE.** The whole
rational `j`-theory — local Weierstrass models, well-definedness and functoriality of
`j`, the gluing, and the Zariski descent from affine bases to all bases — was already
proven, and *none of its proofs read the base or the level*. But it was stated at level
`1` and over `SpecQ`, so nothing integral could reach it. Two mechanical generalisations
made it reachable and the leaf became an assembly:

- `Gamma0Datum 1` → `Gamma0Datum N` in the Weierstrass chain. **Generalising a SORRY
  LEAF's statement in a parameter its content never reads is free**, and it is better
  than cutting a parallel leaf: `exists_weierstrassModel_of_isLocalRing` and
  `..._away_of_atPrime` are now shared by the rational and the integral `j`-theory
  instead of duplicated, and the frontier did not move.
- the `j`-VALUE separated from its PACKAGING: `IsJElt d r` says `r` is the `j`-value as
  an element of the base RING, with no `j`-line in it. The base ring is then free of `ℚ`
  and one element serves `Spec ℚ[X]` and `Spec R[X]` both.

**The generalisable half is usually the BOOKKEEPING, and it is usually most of the
lines.** Before believing that an integral/relative/positive-characteristic analogue
needs new theory, check which of the existing proof's steps actually mention the thing
being varied. Here: zero of them.

## A VACUITY SHIELD CAN BE REMOVED BY A LATER PARAGRAPH OF THE SAME DOCSTRING

(2026-07-31, `jm_eq_jLineZCoord_of_degeneracy`.) Its audit had three findings. (1) and
(2) showed the leaf entails something false. (3) said: *"The leaf is nevertheless NOT
FALSE, because `het` is INCONSISTENT … so this statement is vacuously true."* The LAST
paragraph of the same docstring then read: *"`het` WAS REMOVED FROM THIS SIGNATURE ON
2026-07-30."*

Both were written the same day, by repairs that were each correct. Nobody read them
against each other, and the leaf sat for a day as a FALSE statement with a live
consumer, wearing an audit that said it was safe. The file's own rule had predicted it
verbatim — *"Repairing `etale_of_specLocBase` removes the inconsistency, and AT THAT
MOMENT this leaf turns from vacuously true to FALSE"* — and the prediction fired through
the other available repair (deleting the false leaf rather than fixing it), which the
note did not name.

So: **a vacuity claim names a specific hypothesis, and it expires the moment that
hypothesis is edited. Treat "vacuously true because hypothesis H is inconsistent" as a
claim indexed by `H`, and re-check it against the CURRENT signature — the top of a
docstring is not evidence about the bottom of the same docstring.** Cheap check when
editing any signature: grep the docstring for the removed binder's name.

Corollary found in the same file: **an inconsistent hypothesis makes a PROVEN theorem
useless, not wrong.** `jm_eq_jLineZCoord_of_degeneracy_of_classifyCompat` — advertised as
"the true form, PROVEN, with NO new leaf" — still carried `het`, whose only use had been
deleted with `ofDvd`; the surviving `haveI := het …` was a dead binding. So the "true
form" was vacuous and no consumer could ever have used it. Deleting one unused binder
was the whole repair. **When a theorem is proven but nothing consumes it, check its
hypotheses for one that cannot be supplied.**

## A DECLARATION INSERTED BETWEEN A DOCSTRING AND ITS THEOREM REPORTS AT THE DOCSTRING

(2026-07-31, `X0.lean`.) The commonest way a hand-inserted declaration breaks a huge file,
and the error names neither the inserted block nor the broken declaration:

    X0.lean:57339:67: unexpected token '/--'; expected 'lemma'

Line 57339 is the **closing `-/` of the PRECEDING docstring**, ~40 lines above the edit.
What happened is that a new `/-- … -/ def …` was placed *after* a theorem's docstring and
*before* the theorem, so the docstring is followed by a second docstring rather than by a
declaration. Same reported shape as the reserved-token truncation already recorded above,
different cause — so do not stop at "must be a token clash".

**It is worse than an ordinary error because a parse failure TRUNCATES the file**, so it
hides every later error in a module that takes half an hour to elaborate. Two checks, both
free, and worth running after any hand insertion into a big file:

    # a docstring whose next non-blank line opens another docstring or a /-! block
    awk 'prev ~ /-\/[[:space:]]*$/ && /^\/--/ {print NR": orphaned docstring above"} {prev=$0}' F.lean

Fix by hoisting the new block ABOVE the victim's docstring (check its own dependencies are
still earlier), not by re-indenting or by deleting the docstring.

## AN "IRREDUCIBLE ARITHMETIC RESIDUE" IS STILL WORTH COMPUTING — the answer is not the proof

(2026-07-31, `card_inter_ajPts_redPts_le_of_x0SieveTable`.) That leaf's audit was right that
no soft argument reaches it and that this pin cannot express the object that would close it.
The audit then stopped. But "cannot be PROVEN here" is not "cannot be KNOWN here": the
`N = 26` row was computed outright in about an hour with `gp` and 150 lines of Python, and
the answer (`|ajPts ∩ redPts| = 4`, tight) now sits in the docstring, so whoever eventually
has the machinery formalises a known target instead of searching for one. **Compute the
residue even when you cannot formalise it, and write the ANSWER into the leaf.**

Three transferable pieces, since this shape recurs wherever a modular curve is involved:

* **Get the plane model from `q`-expansions, do not hunt for a quoted one.**
  `mfbasis(mfinit([N,2],1))` gives `f₁, f₂`; put `x = f₂/f₁`, `y = q·(dx/dq)/f₁`, and
  `matker` on 25 `q`-coefficients returns the hyperelliptic relation uniquely. It is faster
  than searching, and it is checkable: `disc` must be supported exactly on `N`'s primes, and
  `#C(𝔽_p)` must equal `p + 1 − Tr T_p` at several good `p` and must FAIL at `p ∣ N`.
  **This is not limited to the hyperelliptic case, and that is the part worth knowing.**
  Take `f₁, …, f_g` as the CANONICAL coordinates and run the same `matker` over the
  degree-`d` monomials in `g` variables: it returned the plane quartic at `g = 3`, the
  quadric-and-cubic at `g = 4`, and the three quadrics at `g = 5`, in seconds each, for
  four levels nobody had a model for. Two free checks come with it — the NUMBER of
  vanishing forms must be what canonical theory predicts (`1` quadric plus one new cubic
  at `g = 4`; `3` quadrics at `g = 5`), and the projective point count over `𝔽_p` must
  again equal `p + 1 − Tr T_p`. Twelve counts across three levels matched on the first
  try. Deriving the model is the cheap half; do it before assuming a model is missing.
* **No rational Weierstrass point does not mean no Cantor.** `#J(𝔽_ℓ)` odd forces no
  rational 2-torsion, hence no rational Weierstrass point, hence no degree-`2g+1` model —
  which looks like a dead end. It is not: pick `a` with `f(a)` a NON-SQUARE, so the fibre
  over `x = a` has no rational point, and `x ↦ a + 1/u` sends the two points at infinity off
  `𝔽_ℓ`. The model is then **inert**, every rational point is finite, the only rational
  divisor at infinity is the canonical class itself, and Cantor with base `K = ∞₊ + ∞₋`
  applies verbatim (compose by polynomial CRT, reduce by `(g − v²)/u`).
* **Let the arithmetic check itself.** The group generated by the Abel–Jacobi classes came
  out at exactly `#J(𝔽_ℓ)` predicted by `charpoly(T_ℓ)` at `ℓ+1`; `aj(P) + aj(ιP)` came out
  constant. Either one failing would have caught a bug. Build such a check in before
  believing any hand-rolled divisor arithmetic.

And one structural payoff worth looking for: `J(𝔽_ℓ)` turned out **cyclic**, so the
order-`#J(ℚ)` subgroup is UNIQUE and `redPts` is pinned without identifying a single cusp.
Check cyclicity first — it can delete the hardest half of the computation.

**And you can check it WITHOUT computing the class group at all**, which is the part that
generalises furthest. By Eichler–Shimura `F² − T_ℓF + ℓ = 0` on `H₁(X_0(N), ℤ) ⊗ ℤ_m`, and
`(F−1)(F̄−1) = ℓ + 1 − T_ℓ`, so `G := H₁/(ℓ+1−T_ℓ)` is an **extension of `J(𝔽_ℓ)` by
itself** — hence `J(𝔽_ℓ)` is a SUBGROUP of `G` and `exp J ∣ exp G`. `G` is one Smith
normal form of an integer matrix (PARI, on the *saturated* cuspidal lattice — `mscuspidal`
returns a ℚ-basis, so saturate with `matkerint(matkerint(M~)~)` or the SNF is meaningless).
`exp G ≪ n` then PROVES not-cyclic. It cost seconds and settled four levels whose class
groups are out of reach; it also bounds `#J(ℚ)`'s exponent, since `J(ℚ)` embeds too.
Two cautions, both real: `G` need not SPLIT (at one level its invariant factors had odd
multiplicities, so `G ≇ J ⊕ J` and the SNF does **not** determine `J`), and the argument
sees only primes `m ∣ n` with `m ≠ ℓ` — check `ℓ ∤ n` before relying on it.

## TEST A PROPOSED CUT ON THE SMALLEST FIELD, NOT THE GENERIC ONE

(2026-07-31, `exists_isAmpleSheaf_of_field`.) The obvious way to cut "an abelian variety is
projective" is to hand out the translation argument as its own leaf: *for every `z` there are
`K`-automorphisms `f₁ … f_k` of `X` with `z ∈ ⋂ fᵢ⁻¹(U)` and `⨂ fᵢ^*L ≅ L^{⊗k}`*, leaving only
formal bookkeeping above it. It reads as obviously true — it IS what Mumford's proof produces —
and **every version of it is FALSE**, for a reason no amount of thinking about the generic case
surfaces.

The witness is four lines of arithmetic. `E : y² + y = x³ + x + 1` over `𝔽₂` is nonsingular
(`Δ = −91`, odd) and has `E(𝔽₂) = {O}`: over `𝔽₂` the left side is `0` for both `y` and the right
side is `1` for both `x`, so there is no affine point. Take `U = E ∖ {O}` and `L = 𝒪((O))`. Any
`K`-automorphism `f` of the SCHEME `E` sends the `K`-point `O` to a `K`-point, hence to `O`, hence
is a group automorphism, hence `f ⁻¹ᵁ U = U`. So every section reachable from `s` by pullback
along automorphisms has non-vanishing locus exactly `U`, and `z = O` is in none of them. Over `ℚ`
the same argument kills it for any curve with trivial Mordell–Weil group.

**The generalisable rule: when a proposed sub-leaf quantifies over AUTOMORPHISMS, RATIONAL POINTS,
or anything else whose supply depends on the base field, instantiate it at `𝔽₂` before writing it
down.** Arguments written over `K̄` silently use Zariski-density of the closed points; the density
is invisible in the statement and is exactly what the cut drops. The smallest field is where a
cut dies, and the test costs a brute-force point count you can run in ten lines of Python (or
check by hand, as above) — far cheaper than dispatching an agent at a leaf that cannot be proven.

Corollary for the ROUTE, not just the cut: once the audit forecloses the cheap sub-leaf, the
docstring must say what the correct field-independent route IS, or the next agent re-derives the
same dead end. Here it is either base change to `K̄` plus faithfully-flat descent OF THE PROPERTY
(the sheaf itself is already defined over `K`, so nothing has to be descended but ampleness), or
staying over `K` and taking norms along `X_κ → X` with Chevalley's affineness theorem. Both are
recorded on the leaf.

## A HOIST COLLIDES WITH A CONCURRENT *PROOF* OF THE HOISTED LEAF — MOVE THE PROOF, NOT THE STATEMENT

(2026-07-31, `flt-lean-86`.) Closing `cuspForm_coe_eq_zero_of_ellipticSturm`
(`ModularCurve/X0.lean`) required HOISTING two leaves out of
`FreyCurve/MazurTorsion.lean`, which is downstream — an `X0.lean` theorem cannot cite
`MazurTorsion.lean`, and both files' docstrings had already prescribed the move. At
that same moment `flt-lean-104` held **369 uncommitted lines in `MazurTorsion.lean`
proving one of the two** (`numCusps_le_order_qExpansion_norm`). Neither agent could see
the other from any branch: the hoist was uncommitted here, the proof was uncommitted
there.

This is not the ordinary same-file collision the fleet is designed for and git handles.
A hoist changes WHERE a declaration lives; a proof changes what its body is. Textual
merge succeeds and produces the declaration in **both** files — a `has already been
declared` hard error that neither diff predicts when read on its own.

**The resolution is asymmetric, and should be applied without deliberation: keep the
hoisted LOCATION and move the PROOF to it.** A statement is what conflicts; a proof
transplants, because a hoist copies the statement verbatim. Restoring the declaration
downstream to keep the proof where it was re-breaks the upstream theorem the hoist
existed to enable, and re-sorrying it upstream manufactures a duplicate leaf — strictly
worse than either branch alone.

If a helper the proof depends on genuinely cannot move upstream, move it FURTHER up
rather than giving up the hoist: `Modularity/HeckeOperator.lean` sits above `X0.lean`
and its own docstring says it exists to host the "norms/traces to level 1" theory.

**The general form, which is the part worth keeping:** before hoisting a declaration out
of a file, grep the *uncommitted diffs* of every claimed worktree for its NAME, not for
the file. `own.py`'s fourth check does exactly this, and this is the case it was written
for — a leaf you are about to relocate is precisely the kind of thing somebody else is
about to prove.

**RESOLVED 2026-07-31 (same worktree, next agent), and the resolution is cheaper than the
rule above suggests — because a hoist's payload is a STATEMENT, so the rival PROOF is
never wasted.** By the time the hoist was picked back up, `flt-lean-104`'s work had landed
on `merger` (`Fermat.relIndex_gamma0GL` *and* `Fermat.numCusps_le_order_qExpansion_norm`,
both PROVEN in `MazurTorsion.lean` over ~1470 lines of new development). So the collision
was no longer symmetric — one side was committed and one was not — and the merge
worker's tie-break rules would have picked the committed side, i.e. would have DISCARDED
the hoist and re-opened `cuspForm_coe_eq_zero_of_ellipticSturm`.

What was done instead: the whole 1478-line development was moved verbatim into `X0.lean`
at the hoisted location, its `Fermat.`-qualified declarations re-namespaced to sit inside
that file's `namespace Fermat`, and `MazurTorsion.lean` keeps only the one-line
`ν₂ = ν₃ = 0` corollary.

**COUNT THE FRONTIER, DO NOT ASSERT IT — this section first claimed `−2` and the true
figure is `0`** (corrected 2026-07-31, same worktree, by counting the two modules'
`declaration uses 'sorry'` sets against release `7080929d`: `X0.lean` `101 → 103`,
`MazurTorsion.lean` `39 → 37`). The `−2` was measured against a base that does not
exist — one where `flt-lean-104`'s proofs had landed *and* the hoist was free. Split by
author the honest numbers are `+2` for the hoist alone, which must carry the statements
up as fresh `sorry`s, and `−2` for the rival proofs alone; landing them together cancels.
This is the same trap CLAUDE.md already warns about two sections up, arrived at from the
other direction: a *decomposition*'s net is as easy to overstate as a release's, and the
temptation is worse because the author knows the work was real. **The argument for a
merge like this one is never the count** — it is that ONE opaque leaf naming four
ingredients in prose became THREE concrete leaves each with a route and a refutation
test. Say that, and give the count separately and correctly.

The move cost one splice and one build because a proof of `X` in file `F` depends
only on things upstream of `X`, and a hoist by construction moves `X` upstream — **so
the proof's own import cone always moves with it.** The only things that can block the
transplant are (a) helpers defined *downstream* of the destination, and (b) `import`s the
destination lacks; (b) was ten mathlib modules and is mechanical.

**Two checks make the transplant safe, and both are cheap.** Before splicing, list every
declaration the moved block introduces and grep the destination for a collision — the
destination here has 74 000 lines and its own `Fermat.*` namespace, so this is a real
risk and not a formality (zero collisions, as it happened). And stage the block in a
throwaway module that `import`s the destination: an `already declared` error there IS the
collision check, and it runs at scratch-module speed rather than at 25-minute
destination-build speed.

## THE ORPHANED HEADER: a merge-damage class that costs ONE RELEASE-BUILD ROUND EACH, and a script that finds all of them in seconds

(2026-07-31, `flt-lean-105`, four instances in one release.) The "MERGING NINETY
BRANCHES" section above already lists *"block-comment nesting depth returns to zero in
every file"* as check 3 and calls it the cheapest in the list. It was not run for
release 25, and four files were damaged: `EllipticCurve/IsogenyTrace.lean:804`,
`EllipticCurve/MordellWeil19.lean:476`, `ModularCurve/EllipticScheme.lean:11144`,
`Modularity/AmpleSheaf.lean:2293`. There is now a script, `flt-comment-balance.py`
(repo root, `python3 flt-comment-balance.py`), so there is no longer an excuse:

    Fermat/FLT/EllipticCurve/MordellWeil19.lean depth=1 unclosed_at=[476]

**The mechanism is narrower than "a conflict inside a docstring", and knowing it gives
you the repair for free.** In all four cases a branch had RENAMED a section header and
MOVED its block elsewhere in the file. The merge then kept the OLD header's first line
at the old position and the NEW block's body after it — so the old header lost its `-/`
and the file now contains a stranded title line immediately above an unrelated `/-!`:

    /-! ### Rank-two linear algebra for the `ℓ`-torsion        <- stranded, no `-/`
    /-! ### The parallelogram law collapses to its UNIT SHIFT  <- the surviving block

**So the repair is to DELETE the stranded line, not to close it with `-/`.** Grep its
title first: in every one of the four cases the block it named was alive elsewhere in
the same file under the new name (`### The Weil pairing on the ℓ-torsion` at ~1036;
`THE level-19 statement` re-proved at ~1388; `#### Δ = 0 forces a rational singular
point` on the very next line; `AN INVERTIBLE SHEAF … LOCALLY FREE OF RANK ONE` at
~2672). Closing the orphan instead leaves a duplicated, stale header that the next
reader will believe.

**Why it is worth a scan rather than a build.** The orphan swallows *every* declaration
after it, so the module emits exactly one diagnostic — `unterminated comment`, reported
at EOF, thousands of lines from the damage — and every module importing it then fails on
names that "do not exist". And because `lake build` stops at the first failing module in
dependency order, **the four were serialised behind one another**: each would have cost
its own release-build round, which is where the "budget three rounds minimum" figure in
the class-7 section comes from. The scan finds all four at once in a couple of seconds.

**`depth < 0` is MOSTLY noise and OCCASIONALLY the mirror defect — check it, cheaply,
and do not "fix" it blind.** The scanner matches two characters and Lean's lexer does
not, so a file Lean accepts can score negative: `X0.lean` scores `−11` and its comments
are fine. But `InvariantCoarseRing.lean` scored `−2` and was genuinely broken, in the
OTHER direction: a merge kept the first two lines of one branch's `theorem` signature
and then the other branch's docstring BODY without its `/--`, so the surviving `-/`
closed a comment that had never opened *and* ten lines of English were parsed as the
continuation of a truncated signature. Lean's diagnostic for that is
`unexpected token; expected ':'` — nothing about comments at all. So: `depth > 0` names
its own culprit and is always real; `depth < 0` is a prompt to run `lake env lean` on
that one file, which settles it in a couple of minutes.

Corollary about doctrine generally, and it is the uncomfortable half: this check was
already written down, in bold, one section up, described as the cheapest available — and
it still did not run, because a prose instruction in a 3 900-line file competes with a
hundred others at the moment somebody is merging ninety branches. **A check that is worth
running every release should be a script with a name, not a paragraph.** Converting one
costs ten minutes and is a full result for a task that has spare time.

## AN ORPHANED OPENER CAN SCORE ZERO — because block comments NEST, and "unknown identifier" is its real symptom

(2026-07-31, `flt-lean-105`, `ModularCurve/RelativePicard.lean`.) The section above
says `depth > 0` names the culprit. That is true and it is not the whole story: **two
defects of opposite sign cancel, and then the balance scan reports the file as clean.**

`RelativePicard.lean` had an orphaned `/--` at ~4230 — the 2026-07-30 docstring of
`𝒪(−σ) COMMUTES WITH BASE CHANGE`, left truncated mid-sentence when a branch replaced
it — and a stray `-/` about 700 lines later, left by the *mirror* damage in a different
docstring. The file scored `depth = 0`. It did not report `unterminated comment` either,
because **Lean's block comments NEST**: the orphan simply swallowed everything up to the
first unmatched `-/`, and the nested `/-!`/`/--` in between raised and lowered the depth
on the way.

**So the symptom is not a comment diagnostic at all. It is:**

    error: Unknown identifier `relSection_comp_curveBaseChangeMap`
    error: Unknown identifier `isPullback_curveBaseChangeMap`
    error: Unknown identifier `exists_abelJacobiPoint`
    error: Unknown identifier `exists_relPicZeroGroupScheme`

for four declarations that `grep -c '^theorem <name>'` finds **exactly once each**. That
combination — *the compiler says a name does not exist, and the source says it does* —
has exactly two causes in this tree, and they are told apart in one command:

* the declaration is BELOW its use (Lean's linear order), which
  `grep -n` settles instantly; or
* **the declaration is inside a comment nobody can see.** Look UP from the first
  reported name for the nearest `/--` or `/-!` and check that it closes before the
  declaration; a docstring that ends mid-sentence is the tell.

Both were present here, which is why fixing the first alone changed nothing.

**Consequences for the release checks.** The nesting-cancellation case is invisible to
`flt-comment-balance.py` by construction, so the balance scan is a cheap FIRST pass and
never a clearance. It stays worth running — it found four files in one release — but
the only instrument that sees this one is `lake env lean` on the single file, which is
minutes rather than a full build. Run it on any module whose errors are a list of
"unknown identifier" for names that exist.

And it argues for one habit when REPAIRING this class: after deleting an orphaned
opener, re-run `lake env lean` even if the scan now reports the file balanced — the
deletion *unmasks* whatever the stray `-/` was hiding, and here that was three further
defects (a second orphaned header, a pair of `_`-prefixed binders used unprefixed in a
body, and a genuine declaration-order break). Repairs in this class arrive in layers,
for the same import-graph reason the release build takes three rounds.

### THE DETECTOR: `tools/merge/commentspan.py`, and the signal is NOT span length

(2026-07-31, `flt-lean-118`. The section above says the only instrument that sees a
cancelling swallow is `lake env lean` on the single file. That was true and it is a
bad deal, because the modules where this happens are exactly the ones that cannot be
built — `Patching.lean` and `Interface.lean` are both downstream of `X0.lean`, which
has been red since release 25.) There IS a static detector, it needs no oleans, and it
runs over the whole tree in two seconds:

    python3 tools/merge/commentspan.py           # 3 reports on this tree, all real

**A legitimate docstring never contains a line that begins a TOP-LEVEL DECLARATION at
column 0.** A block comment that does is a swallow. That is the discriminator, and
getting it wrong in either direction is easy:

* **span length alone is useless** — this project writes 400–800 line module essays,
  so thresholding at 400 lines gives 21 reports of which most are honest;
* **"contains one declaration" alone is useless too** — the docstrings here quote
  Lean at column 0 constantly (route sketches, rejected statements), which gives
  **577** reports. Requiring **five** declarations gives three, and all three are
  wounds. `--min-decls 3` (15 reports) is the eyeball-review setting.

What it found the day it was written, none of it visible to `flt-comment-balance.py`,
`scopecheck.py`, or any build:

    Interface.lean:39911 -> :81532   41621 lines,  644 declarations swallowed
    X0.lean:80904        -> :82118    1214 lines,   47 declarations swallowed
    X0.lean:37098        -> :38245    1147 lines,   17 declarations swallowed
    Patching.lean:10134  -> :12114    1980 lines,  ~30 declarations swallowed  (repaired)

**The shape is always the same and so is the repair**: two branches wrote rival
docstrings for one theorem, the merge kept BOTH `/--` openers and ONE `-/`. Delete the
STALE opener (the live docstring is a few dozen lines below it, and its own header
usually says PROVEN where the stale one says SORRY LEAF), then find the mirror half —
the `-/` that has just become stray — and reopen the bare prose above it as `/--`.
`X0.lean:82118` is on release 27's own list of remaining parse errors, which is the
same wound seen from the other end.

### WHEN THE MODULE CANNOT BE BUILT, RUN THE FILE BOTH WAYS AND DIFF THE ERRORS

Same task, and it is the general technique for editing a module whose cone is red.
`lean <file>` against a FIXED (possibly stale) olean set is not trustworthy in
absolute terms — the doctrine's inconsistent-olean warning applies in full — but it is
perfectly trustworthy as a CONTROL. Run the pre-edit file (`git show <sha>:<path> >
/tmp/Before.lean`) and the post-edit file against the same oleans, and every error
that survives with its line number shifted by exactly your edit's delta is not yours.

Measured here on `Patching.lean`: 52 error lines before, 18 after, every survivor at
+1085 = (1111 deleted − 26 added), and the 34 that vanished were precisely the wound's
signature — `invalid use of explicit universe parameters, IsCohenCoefficients is a
local variable` (a swallowed `def` had become an auto-bound implicit), two
`Unknown identifier`s, and four `Function expected at`. That is a complete, auditable
verification of a 1111-line deletion in a module that cannot be compiled at all, and
it cost two `lean` runs.

## A `variable` USED ONLY IN A PROOF BODY IS NOT INCLUDED — one root cause, thirty-four errors

(2026-07-31, `flt-lean-105`, on inherited work that had never been compiled.)
Lean 4 includes a section `variable` in a declaration only when the variable occurs
in that declaration's **statement** (or is an instance-implicit). A hypothesis used
solely inside the proof is simply not there:

    variable (hv : v ≫ d.f = d.f) (hadd : IsAdditiveOn d.ab d.ab v hv)

    theorem add_fixed {x y : RelPoint d.f g}
        (hx : x.1 ≫ v = x.1) (hy : y.1 ≫ v = y.1) : (d.ab.add x y).1 ≫ v = … := by
      rw [hadd x y, …]        -- error: Unknown identifier `hadd`

**The reason this is worth a section is the BLAST RADIUS.** Six declarations in one
block were affected, and because each then had the wrong arity, every later
reference to them failed too: **34 errors from one cause**, almost all of them
`Application type mismatch` or `Function expected at` pointing at call sites that
are individually correct. Chasing them one at a time is hours; the fix is six
`include` lines. So when a block reports a cloud of arity errors, look for
`Unknown identifier` on a *section variable* in the FIRST error, not the loudest.

Three mechanics, each of which cost a round here:

* **Scope the `include` per declaration, not per section.** `include hv hadd` as a
  bare command after the `variable` line over-includes: a sibling whose statement
  already mentions `hv` (so `hv` was auto-included) now silently gains `hadd` too,
  and its call sites fail with `Invalid projection … has function type` — a message
  that says nothing about arity. Use `include hv hadd in` on exactly the
  declarations whose *bodies* need them.
* **`include … in` goes ABOVE the docstring.** Between the docstring and the
  declaration it is `unexpected token 'include'; expected 'lemma'`.
* A `def` whose result is a class (`Group …`, `AddCommGroup …`) wants
  `@[reducible]`, or Lean warns.

And the standing rule this violates: **work you inherit has not been compiled until
you compile it.** The block carried a careful docstring, a correct design and a
plausible proof, and it had never elaborated once.

### Verifying against the RELEASE olean when the target's own cone is red

The same run could not build `MazurTorsion` at all, because `X0.lean` was red from
merge damage. The block was still verified, in ~90 s per iteration, by the shim the
scratch-module section above describes — with the release snapshot as the source of
the one olean that mattered:

    cp -rs ~/.flt-release-lake/build/lib /tmp/relean-N/          # symlink farm, instant
    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" lean Scratch.lean

**This is sound only under a check you must actually run**: every name the block
uses has to be present and unchanged at the snapshot's sha (`~/.flt-release-lake/sha`).
Here that was seven names, all of them older than the release, so the shim proved
exactly what a real build would have. It is NOT a substitute when your block
consumes something added since — then the shim's `X0` is a *different theory* and a
green scratch means nothing. Check the names first; it takes one `git show`.

## WHAT A DECLARATION-LEVEL MERGE CANNOT SEE: DELETIONS, ORDER, AND `open … in`

(2026-07-31, release 27.  `tools/merge/semmerge.py` is the right tool and these are
the three things it structurally cannot do.  All three were live in one batch of 19
branches and none of them shows in a diff, a conflict marker, or `check-dup`.)

**1. IT PROPAGATES ADDITIONS, NEVER DELETIONS — so a HOIST merges as pure
DUPLICATION.**  `semmerge` iterates over THEIRS' declaration names; a name that is
in the base and in ours but *not* in theirs is simply never considered, and ours
keeps it.  That is right for a branch that dropped something by accident and wrong
for every branch that MOVED something.  flt-lean-86 hoisted ~80 declarations
(`borelZMod` … `numCusps_le_order_qExpansion_norm`, the whole `Gamma0Cusp`
namespace) out of `FreyCurve/MazurTorsion.lean` up into `ModularCurve/X0.lean`;
the X0 copies landed, the MazurTorsion copies survived, and MazurTorsion imports
X0.  Every one of those names would have been `has already been declared`.

**No per-file check sees it, and the obvious cross-file check reports NOTHING.**
`checks.py check-dup` is per file by construction.  A qualified-name cross-file
scan is sound and silent here, because this tree's giant modules contain bare
`end`s that a stack model mis-attributes — from some point in `X0.lean` onward
every name loses its `Fermat.` prefix, so X0's `Fermat.borelZMod` is recorded as
`borelZMod` and does not collide with MazurTorsion's.  What found it was matching
on the LAST COMPONENT.  `tools/merge/xdup.py` now runs both passes: `XDUP`
(qualified, an error) and `XDUP-LAST` (last component, ~7000 hits on this tree, so
a REVIEW list that is only usable **differenced against pre-merge `main`**).  Run
it after every batch; release 27's diff was empty in the qualified pass, which is
the answer you want.

**2. IT DOES NOT REORDER, AND MOVING A DECLARATION ALSO MOVES IT OUT OF SCOPE.**
The README already says a hoisted helper can land below its consumer.  The half it
does not say is worse: `open X in`, `set_option … in` and `open scoped Classical in`
bind to ONE declaration, so relocating a declaration silently changes what is in
scope for it.  Two shapes, both from this release:

* `natDegree_minpoly_weberAlpha_le` (`BinaryQuadraticForm.lean`) took theirs' body
  and ours' position, 4500 lines above the `exists_int_gammaTwo` it calls.  Moving
  it down fixed that and broke it a second way: its old site was inside
  `open _root_.Polynomial in`, its new one was not, so `X` and `C` became unknown
  identifiers — **and the `ℚ⟮…⟯` adjoin notation stopped parsing, which reports as a
  bare `expected token` at a column in the middle of a `have`.**  A parse error that
  names no identifier and no namespace is this.  The branch carried
  `open _root_.Polynomial _root_.IntermediateField in` on exactly that declaration;
  the fix is to carry it with the declaration.
* `geomPic_descent` (`HyperellipticJacobian.lean`) lost `open scoped Classical in`
  entirely.  `semmerge` merges docstrings separately and keeps OURS when ours
  evolved — and an `open … in` line is part of the ATTACHMENT RUN, i.e. part of the
  docstring side.  Symptom: three `failed to synthesize Decidable/DecidableEq` in a
  proof otherwise byte-identical to the branch's.

So after any merge that reports `TOOK-THEIRS` on a declaration, **diff that
declaration's ATTACHMENT RUN, not just its body**, and grep the branch for an
`… in` line immediately above it.

**3. A `whnf` TIMEOUT IS REPORTED AT THE START OF A DOCSTRING — which belongs to the
declaration BELOW it.**  `MoretBailly.lean` reported
`27690:0: (deterministic) timeout at whnf`, and line 27690 is the opening `/--` of a
docstring whose theorem is 130 lines further down.  A `set_option maxHeartbeats … in`
placed on the declaration ABOVE that docstring — the natural reading — changes
nothing, and the run is wasted.  Read the line the error names, see whether it is
`/--`, and if so bump the NEXT declaration.  (The consequent `(kernel) unknown
constant` 700 lines below is the usual cascade; read the log from the top.)

### `flt-frontier.py` UNDER-REPORTS, AND THE QUEUE INVARIANT IS COMPUTED FROM IT

Same release, and it is the more dangerous finding because it is silent and it
shrinks the work the fleet is given.  `flt-frontier.py` reported **5** open leaves
in `Modularity/Interface.lean`; a comment-stripped token scan finds **15**, and two
independent agents' reports say 20-21.  Its total was 321 against a true 333.

`tools/merge/frontier.py` (added here) is the scan that was VALIDATED against the
compiler: on all 25 modules that completed in release 27's first build round its
per-file counts matched the `declaration uses 'sorry'` warning set exactly, 25 out
of 25, including `HyperellipticJacobian` (25) and `MoretBailly` (14).  Use it for
the coverage invariant, and re-validate it the same way — the check is ten lines and
it is the only thing standing between a scanner bug and a release that queues 200
tasks against a 333-leaf frontier.

**IT HARDCODES `ROOT = /home/chend/flt-staging` AND IGNORES ITS ARGUMENTS** (measured
2026-07-31, `flt-lean-115`). Run from a worktree it silently reports the STAGING tree's
frontier, and `python3 tools/merge/frontier.py <your file>` prints the whole staging
scan rather than erroring — so a worker measuring its own delta gets the pre-change
number and concludes it changed nothing. Same trap as
[[flt-hidden-sorries-scans-main-repo]], in the tool the release now depends on. From a
worktree, copy it with `ROOT` rewritten:

    sed "s#/home/chend/flt-staging#$PWD#" tools/merge/frontier.py > /tmp/frontier.py

The tell is that your own new declarations are absent from its output while the count
looks plausible. Cross-check by grepping the output for a name you just added.

Two riders that cost real time here:

* **Tokenise task text unicode-safely before matching leaf names against it.**  A
  `[A-Za-z_][A-Za-z0-9_.']*` token regex misses every name containing `ι`, `Ψ`, `₁`
  or `₂`, and this tree is full of them: the naive pass called 59 queue entries
  obsolete, of which 43 named a live leaf under a subscripted name.  Splitting on
  "not `isalnum()` and not `_ ' .`" — minus the bracket characters
  ([[lean-identifier-regex-swallows-brackets]]) — took the false-obsolete count to
  zero.
* `Fermat/SorryGate.lean` contains the token `sorry` twice inside a STRING LITERAL in
  its `elab`.  Any scan must exclude that file or strip string literals.
## A TASK'S OWN "IS THE FILE QUIET" GUARD — and why rebasing onto `merger` is NOT the dodge
(2026-07-31, `flt-lean-291`.) A well-written task that makes an INTERFACE change sometimes ships
with its own precondition: *skip me if `merger` is still carrying an unmerged restructuring of this
region*. That guard is class 7 above stated in advance, and it is one command:
    diff <(git show main:<path>) <(git show merger:<path>) | grep -E '^[0-9]'
The hunk LINE RANGES are the whole answer — you do not have to read the prose. If a hunk boundary
abuts the declaration you were told to edit, the merge will split your signature change from your
call sites exactly as class 7 describes. In the instance that produced this note the guard hunk was
`1365c1374,1483`, ending on the line immediately above the `theorem` line to be changed: an
adjacent-line edit on both sides, i.e. a guaranteed conflict at the one place where a wrong
resolution silently compiles on one side only.
**The tempting workaround is to base the branch on `merger` instead, so there is no boundary. Do
not.** Two reasons, and the second is fatal on its own:
- `merger` is a LIVE branch — it moved between two consecutive `git rev-parse` calls in this very
  session — so "based on merger" names nothing stable.
- The seeded artifacts (`~/.flt-release-lake/build`, rsynced at each release) track **main**. At the
  time of writing `merger` was **867 commits and 164 000 changed lines** ahead of main across 118
  files, so a worktree rebased onto it has no usable `.lake` and must rebuild an unreleased tree
  that nobody has certified green. You would be paying a full mathlib-adjacent rebuild to verify a
  three-line change, against a base whose redness would not be yours.
So the correct response to a fired guard is the one the task asks for: **skip, and re-queue with the
full edit spelled out**, including the current line numbers and the guard restated. That is a full
success, not a wasted cycle — the queued task is strictly cheaper to run after the release than the
conflict repair would have been before it.
## GENERALISING A BASE FIELD IN PLACE: autoParam the fact that was free, and check whether the morphism already determines the datum
(2026-07-31, `flt-lean-276`, generalising `EllipticScheme.lean`'s `ProjCoords` cluster from `ℚ`
to `F : Type u`.) Two techniques, both reusable, because this tree has several ℚ→field ports
still queued.
**A ℚ-only fact that a hundred call sites use IMPLICITLY becomes an `autoParam`, not a new
argument.** `ProjCoords.base_eq` — `ℚ →+* A` is a subsingleton — was consumed silently by
`add`, `add2`, `ext`, and by every one of the 58 `hom_ext_spec_rat` invocations. Adding
    (hb : c.base = d.base := by exact Subsingleton.elim _ _)
as the LAST binder leaves **every existing `ℚ` call site byte-identical** (the tactic fires and
finds `Rat.subsingleton_ringHom`) while a general-`F` caller gets a hard error until it supplies
the proof. The port becomes opt-in per call site and `ℚ` cannot regress. Two caveats, both hit:
* a `@[simp]` projection lemma ABOUT the autoParam'd definition must take the hypothesis as an
  explicit anonymous binder (`(h) (hb)`), because that lemma's own statement is elaborated at `F`,
  where the default tactic fails;
* what makes `rw`/`exact` still match a goal whose proof term came from the tactic rather than
  from the caller is proof irrelevance — so keep the hypothesis a `Prop`.
**Before threading a datum through, ask whether the MORPHISM already determines it.** The 58
`hom_ext_spec_rat` uses are not 58 obligations: they all sit in one position, the commuting square
of `Limits.pullback.lift c.toHom d.toHom _`. Two lemmas replace the lot:
* `ProjCoords.toHom_comp_projToSpec` — `c.toHom ≫ projToSpec E = X.toSpecΓ ≫ Spec.map (ofHom c.base)`,
  which is mathlib's `Proj.fromOfGlobalSections_toSpecZero` (it already exists — do not rebuild the
  chart dictionary for it) plus "`ringHom` evaluates a constant to itself";
* `ProjCoords.base_eq_of_toHom_eq` — the CONVERSE, `c.toHom = d.toHom → c.base = d.base`, because
  `Γ ⊣ Spec` is an adjunction (`Scheme.toSpecΓ_appTop`, `Scheme.Hom.comp_appTop`,
  `AlgebraicGeometry.ext_to_Spec`, `Spec.map_injective`).
The converse is what makes the port cheap: every rigidity/congruence lemma already knows
`c.toHom = c'.toHom`, so over `F` it needs **no new hypothesis at all**. The estimate that had
been carried in `MoretBailly.lean` for a year — "60 vanished justifications, the group-law port
crosses this obstruction dozens of times" — is right about the count and wrong about the cost.
**And for a PERVASIVE edit inside a monolith, the scratch module is a truncated PREFIX of the same
file.** The "verify in a scratch module" rule above assumes the new code is separable; when the
edit is spread over 3 000 lines of a 12 686-line file it is not. Write `lines[:N]` plus the
closing `end`s to `ScratchN.lean` — same imports, a quarter of the elaboration — and delete it
before committing (an unimported module under `Fermat/` is the fourth invisibility class).
Measured here: the clean file is **72 s**; a ~100-line prefix probing two lemmas is **60 s**; the
same full file carrying a dozen errors ran past **10 minutes**. **Error recovery, not size, is
what makes a broken monolith slow — never price the next round off the last one.**
## A LEAF CAN NAME THE WRONG HALF AS HARD — split the algebra out before building the theory
(2026-07-31, `ProperPushforward.lean`.) That file's single leaf,
`self_mem_smul_adjoin_self_of_appTop_fiberι_eq_zero`, carried six audit blocks — (A)–(D) on
`finiteType_appTop_of_isProper`, (E)–(H) on the leaf — each with an explicit witness, all
correct, all agreeing that closing it is a THEORY BUILD (Grothendieck coherence, absent from
the pin) and that every proposed shortcut is dead. Every one of those conclusions still
stands. And the leaf still closed, because the audits were about the GEOMETRY and the leaf as
stated bundled the geometry with a commutative-algebra bridge that was fully provable at the
pin in ~110 lines.
**The tell was in the file and is worth looking for generally: a statement of the honest
classical input sitting BELOW the leaf and proven CIRCULARLY from it.** Here it was
`exists_finiteFree_ker_linearEquiv_appTop_of_isIso_appTop_fiber` (Mumford's complex in degree
`0`), discharged by "once the leaf is known, `A ≅ R`, so take `R¹ ⟶ R⁰` with `d = 0`". A
declaration whose proof is *"assume the leaf, now the witness is trivial"* is not content —
it is the file telling you its dependency order is inverted. Hoist it above the leaf, make
IT the leaf, and prove the old leaf from it. The two are then provably equivalent, so no
audit is voided and none of the recorded witnesses is lost.
**The technique that made the bridge provable, and it generalises.** The natural hypothesis
on a two-term complex is `Module.Flat R (range d)` — that is what a Tor computation gives
`ker d ∩ 𝔪·C₀ ≤ 𝔪·ker d` from. But the Nakayama step ALSO needs `Module.Finite R (ker d)`,
and in this file the only source of that was downstream of the leaf, so the flat form was
unusable exactly where it was wanted. **Ask for `Module.Projective R (range d)` instead**: it
splits `0 ⟶ ker d ⟶ C₀ ⟶ range d ⟶ 0`, and the retraction `r : C₀ ⟶ ker d` gives BOTH facts
in one line each (`ker d` is a quotient of the finite `C₀`; `r` carries `𝔪·C₀` into
`𝔪·ker d` and fixes `ker d`). The two hypotheses agree in the intended application — a
finitely presented flat module is projective — so nothing is given up. General form: **when a
flatness hypothesis is unusable because the finiteness its Tor argument needs is the very
conclusion, ask for the SPLIT rather than the Tor-vanishing.**
**A third thing, about tensor products.** The dévissage those complexes are for (`H⁰(J) :=
ker(d ⊗ J)`, left exact by flatness of the terms) needs no tensor product to state: flatness
of `C₀` identifies `ker(d ⊗ J)` with the honest submodule `ker d ∩ J·C₀`. Whenever a route is
written with `⊗` over a filtration of ideals, check whether flatness lets it be written with
`Submodule.inf` and `Submodule.smul` first — the Lean cost is an order of magnitude lower.

## "ADJOIN THE LIFT OF A GENERATOR" IS USUALLY WORSE THAN "ADJOIN THE LIFT OF EVERYTHING"

(2026-07-31, `flt-lean-73`, closing step 1 of `exists_traceSubringDescent` in
`Patching.lean`.)  The classical recipe for a coefficient ring inside a complete
local ring with finite residue field is Teichmüller's: `kˣ` is cyclic, lift a
GENERATOR `ḡ` along `X ^ (#k − 1) − 1`, adjoin the lift.  The leaf's docstring
prescribed exactly that, and it is correct mathematics.  It is also the expensive
formalisation, for a reason that has nothing to do with the mathematics:
recovering an arbitrary `y ≠ 0` as `ḡ ^ m` needs
`Submonoid.powers` / `Subgroup.zpowers` / `mem_powers_iff_mem_zpowers`
bookkeeping, and that membership **timed out at `whnf` (200 000 heartbeats)
inside the file's ambient context while elaborating instantly in a two-line
isolated `example`.**  Restructuring — dropping the `set`s, splitting the Hensel
step into its own lemma — did not help; the timeout is a property of the
surrounding context, not of the tactic block.

The escape is to notice that **the generator was only ever there to make the
adjoined set a SINGLETON, and nothing needs it to be one**: `k` is finite, so
`Set.range τ` for the lift map `τ : k → R₀` is finite, and
`Algebra.finite_adjoin_of_finite_of_isIntegral` is stated for exactly a finite
set of integral elements.  Adjoining the Teichmüller lift of EVERY element makes
residual surjectivity a projection (`⟨τ y, subset_adjoin ⟨y, rfl⟩⟩`), deletes the
cyclic-group theory entirely, and the whole thing is ~20 lines.  Use `X ^ #k − X`
rather than `X ^ (#k − 1) − 1`: its derivative is `#k · X ^ (#k−1) − 1`, which
maps to `−1` on the nose since `(#k : k) = 0` (`FiniteField.cast_card_eq_zero`),
so the simple-root hypothesis needs no case split on whether the point is zero.

Generalises past this leaf: **when a recipe adjoins the lift/preimage of a
GENERATOR, ask whether adjoining the whole finite fibre is equally finite.**  If
it is, the group theory was never load-bearing — it was an optimisation of the
*ring*, and you are optimising the *proof*.  Same family as
[[flt-leaf-cost-estimates-are-hypotheses]]: a docstring route is a hypothesis
about cost, written before anyone tried.

Two mechanical traps from the same proof, each one round trip:

* **The monic witness for `IsIntegral R x` lives in `R[X]`, and passing an
  `A[X]` one is reported as a UNIVERSE error.**  `Polynomial.monic_X_pow_sub h`
  with `h : (X : A[X]).degree < n` fed to `⟨X ^ n - X, ·, ·⟩ : IsIntegral R x`
  gives `degree.{uR} X < ↑n` against `degree.{0} X < ↑n` — which reads as a
  `Type*` / universe-polymorphism problem and is not one.  The two `X ^ n − X`
  are simply polynomials over different rings.  Check the RING before touching
  the universes.
* `IsAdicComplete.henselianRing R I` gives `HenselianRing R I`, **not**
  `HenselianLocalRing R`, and mathlib has no instance from the first to the
  second.  Use `HenselianRing.is_henselian` directly: its simple-root hypothesis
  is `IsUnit (Ideal.Quotient.mk I …)`, which for `I = maximalIdeal R` you get
  from `IsUnit …` in `R` by `.map _`, and `IsUnit …` in `R` from
  `IsLocalRing.notMem_maximalIdeal` plus `IsLocalRing.ker_eq_maximalIdeal`.

### When your target module is downstream of a RED module, fill only the MISSING oleans from the release

Same run, and it is the sharp form of the shim recorded above.  `X0.lean` was red
on `merger` (≥100 errors, `maxErrors` reached — release-27 merge damage: dropped
arities on `etale_nTorsion_of_specQBase` / `isFinite_flat_nTorsion`, and
`exists_jSection` used above its declaration), and `X0 → MazurTorsion → Patching`
means `lake build Fermat.FLT.Modularity.Patching` could not reach the module at
all.  `lake` had already brought 5579 of 5597 targets up to date before dying, so
the right farm is **current `.lake/build` plus the release copy of exactly what is
missing** — not the release tree wholesale:

    python3 - # list modules under Fermat/ with no .olean in .lake/build/lib/lean
    cp -rs /scratch/chend-flt/flt-lean-N/.lake/build/lib /tmp/relean-N/      # symlinks, instant
    cp -f ~/.flt-release-lake/build/lib/lean/<the missing module>.olean* /tmp/relean-N/lib/lean/<dir>/
    LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" lean <your file>

Here that was ONE module.  The soundness condition is the usual one — your file
must not name anything added to the substituted module since the release sha —
and it is much more likely to hold when you substitute one olean than when you
substitute the whole tree.  Say in the commit which oleans were substituted; a
shim-verified edit is not a build and must not be reported as one.

**AND WHEN THE SHIM ITSELF COMES BACK RED, DIFF IT AGAINST THE UNEDITED FILE —
that turns an unusable log into a clean verdict.**  The run above produced 52
errors, so on its own it says nothing about whether the edit is sound.  Running
the SAME shim on `git show <base>:<path> > /tmp/Pre.lean` gave 52 errors too, and
comparing the `(line, column)` pairs showed a single distinct offset —
`(+151, same column)` — which is exactly the number of lines the edit inserted
above them.  Identical error set, identical `declaration uses 'sorry'` set (8 in
both, at the same shifted lines).  That is a complete answer to "did I break
anything", and it costs one extra elaboration of a file you were going to
elaborate anyway.  It also detects the reverse — an error that DISAPPEARS is as
much a signal as one that appears, since it usually means a declaration stopped
being reached.

Do the comparison on `(line, column)` pairs and require the shift to be a single
constant; a mixed shift set means your edit changed more than it inserted.
## "THE OTHER SIDE DOES NOT HAVE THIS PROBLEM" MUST NAME THE **OBJECT** IT PROTECTS
(2026-07-31, the Hilbert twin of the `Patching.lean` `𝒟Q` refutation. This is a *different*
failure from "an audit is scoped to the object it names, never to the pattern" — that one is
about not looking; this one is about looking, finding a note, and being told the wrong thing.)
`Patching.lean`'s 2026-07-28 audit refuted a leaf because `IsWeaklyUniversalDeformation` is
existence-only and so pins `Runiv` in no direction. It then wrote, as an aside:
> The Hilbert twin does not have this problem because
> `exists_hilbertAuxDeformationRingPresentation` carries `h𝒟t : 𝒟.IsTraceGenerated`
> alongside `h𝒟w`, and trace generation is exactly what excludes `y`.
**Every clause of that is TRUE — about `𝒟`, the BASE-level datum.** That Hilbert theorem
*also* received `𝒟Q`, the RAISED-level one, under nothing but
`HilbertAuxDeformationDatum.IsWeaklyUniversal` — the same existence-only clause, on a ring
the sentence never mentions. So the Hilbert side had the identical defect, on the other ring,
for three days, PROTECTED BY A CORRECT NOTE. Anyone who checked found the note, read "the
Hilbert twin does not have this problem", and stopped.
A theorem's hypotheses routinely mention several bundled objects of the same kind. A
protection note that names the theorem and the hypothesis but not **which object of that
theorem is thereby pinned** is unfalsifiable by the reader who most needs it. So:
- **Writing one**: name the ring/module/datum. "`𝒟` is pinned by `h𝒟t`; `𝒟Q` is NOT pinned by
  anything" is one clause longer and would have prevented this.
- **Reading one**: before accepting "X does not have this problem", list the objects in X's
  hypotheses of the shape the defect attacks, and check the note covers each. Here that is
  `grep -n 'IsWeaklyUniversal' <the theorem>` — two hits, one covered, one not.
Same shape as "TWO INDIVIDUALLY-CORRECT REPAIRS CAN BE FATAL TOGETHER" above: a true
statement that is *scoped narrower than it reads* is more dangerous than a false one, because
it survives review.
## `| head -N` ON A BUILD KILLS THE BUILD — AND THE TRUNCATED LOG LOOKS LIKE A CLEAN ONE
(2026-07-31, cost one full module build, ~25 min.) The doctrine warns never to pipe a
backgrounded build through `tail`. `head -N` is worse and reads as more innocent: it *exits*
after N lines, so the writers upstream get `SIGPIPE` and the whole pipeline — including
`lake` — dies. Here
    lake build <Module> 2>&1 | tee /tmp/b.log | grep -E "error|declaration uses" | head -40
was killed the instant the 40th matching line was printed. `/tmp/b.log` then held 905 lines
ending mid-stream, with **no error lines and no `Build completed`** — indistinguishable at a
glance from a green build in progress, and `grep -c error` on it returns 0.
**Redirect, never pipe:** `lake build <Module> > /tmp/b.log 2>&1; echo "EXIT=$?" >> /tmp/b.log`
and grep the file afterwards. Judge a build by the presence of `Build completed successfully`
plus an explicit `EXIT=`, never by the absence of the word `error` — absence of errors is also
what a killed build looks like.
## A RECORDED "THIS CUT IS IMPOSSIBLE" REFUTES ONE SPLIT, NOT ALL SPLITS — look for a PINNING clause
(2026-07-31, `exists_fundamentalCharacter_of_semistabilityDefect`, node `A₀-3b-i`.) A leaf whose
conclusion is `∃ x, P x ∧ Q x` invites the obvious split: leaf 1 produces an `x` with `P x`; leaf 2
takes such an `x` as a HYPOTHESIS and proves `Q x`. That split is FALSE whenever `P` fails to
determine `x` — leaf 2 must then prove `Q` for EVERY `P`-satisfying witness, and `Q` typically holds
only for the intended one. This node carried a careful, correct, explicit counterexample to exactly
that split (`N = 29`, `e = 4`, `ψ' = ψ_L^15` is surjective and satisfies `ψ'^e = χ|_J`, yet no
`ψ'^r` with `r ≤ e` equals `λ|_J`), together with a note that strengthening `P` to "`ψ` generates
the character group" does not repair it. A prior agent read that as a proof the node is ATOMIC and
made no change.
**It is not. The counterexample refutes splitting along `P`; it says nothing about splitting along a
DIFFERENT clause.** The repair is not a stronger PROPERTY of `x` but a clause that PINS it — a
defining property with at most one solution, satisfied by the intended witness. Here that was the
compatibility that DEFINES the level-one fundamental character,
    ∀ σ ∈ J, ∃ τ ∈ I_N, τ^e σ⁻¹ ∈ P_N ∧ ψ σ = χ τ,
whose uniqueness proof is two lines (the tame quotient is torsion-free, so `e·τ̄ = e·τ̄'` forces
`τ τ'⁻¹ ∈ P_N`), which kills the recorded witness on sight (it would force `ψ_L^14 = 1`), and which
turned one atomic node into two citable leaves: local-field theory with no curve in it, and
Raynaud's classification with no tame theory in it.
The checklist when a split is blocked by a witness-ambiguity counterexample:
1. Ask what **defines** the intended witness, not what is **true** of it. A defining property is
   usually a compatibility with something already named in the statement — not new vocabulary.
2. Prove the pinning clause has at most one solution and put that argument in the docstring. It is
   the whole of what makes the second leaf faithful, and the only thing a reviewer must check.
3. Re-run the recorded counterexample against the new clause and say in the docstring that it dies.
   The old counterexample is still TRUE and must be KEPT, relabelled as refuting the old cut only.
Expect the pinning clause to be strictly harder to prove than the property it replaces (it was here:
it needs the tame quotient torsion-free, not merely procyclic). That is the right trade — it moves
work off the unprovable side onto the provable one.
## A DOCSTRING THAT ARGUES TWO LEAVES ARE EQUIVALENT IS A LEAF-MERGE WAITING TO BE PERFORMED
(2026-07-31, done twice the same day — `X1.lean`'s `Γ₁` pair, then `X0.lean`'s `Γ₀` pair.)
Both files carried the same cut: one Katz–Mazur citation split into
`exists_<X>ModuliScheme` (`∃ R, …`) and `isAffine_of_<X>ModuliScheme` (`∀ R, IsAffine R.M`).
The `∀`-shaped half is the junk-witness shape this development is rightly afraid of, so each
docstring answered the worry in prose:
> `universal` is a **fine** moduli property, so any two inhabitants are related by a unique
> isomorphism (apply each one's `universal` to the other's universal family, and then to its own
> to see that the two composites are the identity).  `IsAffine` is invariant under isomorphism.
**That paragraph is not a caveat. It is a complete proof that one of the two leaves is free** —
it says `∃ R, IsAffine R.M` implies `∀ R, IsAffine R.M`, so merging the halves into the single
existential costs one thirty-line lemma and closes a leaf. Both files had it written out, in
full, for four days, under a heading that reads like a disclaimer.
Both docstrings also contained the explicit escape hatch — "if a prover would rather not pay it,
the honest weakening is to prove `∃ R, IsAffine R.M` instead … but then the two citation halves
fuse back together, which is the thing this cut exists to prevent." **The warning had the sign
backwards.** The cut was made so that no leaf carried both a citation and a formalisation; what
it actually produced was two leaves carrying ONE citation between them, because (8.1.1)'s
affineness clause is a remark on the construction of (4.7.2) and nobody proves it separately.
Fusing is a strict improvement whenever the two halves are not separately provable.
So, as a standing sweep: **grep docstrings for prose that relates two leaves**, not just for
`sorry`. The phrases that actually found these are `are the same statement`, `up to unique
isomorphism`, `invariant under isomorphism`, `junk-witness`, `would rather not pay`. Each hit is
a hypothesis that a leaf is free; it costs one read to check.
**The mechanical obstacle, and the cheap way through it.** The merge needs a rigidity lemma, and
a rigidity lemma needs the file's `IsBaseChangeOf.refl` / `.comp` calculus — which in `X0.lean`
sat 500 lines BELOW both leaves and below their consumer. Do not relocate the leaves (their
docstrings are long and their consumers are elsewhere): **hoist the calculus**. A line-range move
is safe when (a) it is namespace-balanced — every `namespace`/`end`/`section` pair in the moved
range is inside it — and (b) nothing in the skipped span uses the moved names. Both are one
`grep` each, and the move is then verbatim: `git diff` shows equal insertions and deletions.
**Corollary for the accounting.** `X0.lean` went 130 → 129 direct sorries while GAINING a
declaration. Merging leaves is one of the few moves that lowers the frontier without proving any
mathematics, so it does not show up in any "what got proven" report — say so explicitly, or the
delta looks unexplained.
## AN "ABSENT FROM MATHLIB" VERDICT ABOUT A **POINT** IS OFTEN A VOCABULARY MISS
(2026-07-31, `flt-lean-349`, and it had cost two prior audits a cycle each.) Two audits on
`card_compl_range_le_card_divisors` (`ModularCurve/X0.lean`) deferred the same re-cut because it
needed *a closed point of a finite-type `k`-scheme has `Module.Finite k κ(p)`*, and mathlib "has
nothing packaging that at the scheme level (grepped 2026-07-31)". The second priced it as a
four-step chain of curve theory: `Y ≠ ∅` from integrality → `X` irreducible → the generic point
lies in `Y` → a non-generic point of an integral curve is closed → Zariski's lemma. **None of the
four was needed and the whole obligation was twenty lines**, over
`AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType` and
`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace` (`Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`,
both stacks 01TB) plus `LocallyOfFiniteType.jacobsonSpace`.
**Why the grep missed it, and this generalises.** Mathlib's AG library states facts about a POINT
as properties of the canonical morphism out of it (`X.fromSpecResidueField p`, `Hom.residueDegree`),
and states those as *equivalences between `MorphismProperty`s*. A search in the mathematician's
vocabulary — "closed point", "residue field", "finite over the base" — therefore returns nothing,
and the absence claim reads as verified. Before concluding a point-level scheme fact must be built,
grep `Mathlib/AlgebraicGeometry/Morphisms/*.lean` for the canonical morphism and for `_iff_`-shaped
lemmas between morphism properties.
**Second lever from the same task: a topological argument can delete the geometry outright.** An
open set is stable under generisation, so "the generic point lies in `Y`" became "`closure {p}` is
disjoint from `Y`, hence sits inside the FINITE complement" plus `JacobsonSpace` — no
irreducibility, no integrality, no dimension, no nonemptiness of `Y`. When a chain of geometric
hypotheses is being assembled only to locate the generic point, check first whether finiteness of
the complement already does it.
## AN EXISTENTIAL LEAF OFTEN RE-PROVES AN EXISTENCE THEOREM THE SAME FILE ALREADY HAS
(2026-07-31, `X0.lean`.) `exists_isWeilEigenvalues_isEichlerShimuraTransform_x0` asked a prover
to EXHIBIT a multiset reproducing the point counts of `X_0(N)_{𝔽_ℓ}` over every `𝔽_{ℓⁿ}`. Doing
that at all is **Weil rationality for a curve** — and `exists_isWeilEigenvalues` sat 680 lines
ABOVE it in the same file, proving exactly that over its own named leaf. The existential leaf was
carrying a whole classical theorem a second time, invisibly, because the redundancy is between a
CONCLUSION (`∃ β, IsWeilEigenvalues …`) and a HYPOTHESIS nobody had written down.
So: **when a leaf asks you to produce an object, grep the file above it for an existence theorem
for that same object before doing anything else.** The leaf's real content is usually only the
IDENTIFICATION — "the object you can already get is *this* one" — and splitting the existence off
is a provable reduction, not a repackaging: derive the old leaf from the new one plus the existing
existence theorem, and check the converse holds too, so you can state in the docstring that nothing
was made harder.
**BUT: check who consumes the DERIVATION before you reverse a cut.** The tempting move here was
shorter — sorry the universally-quantified `isEichlerShimuraTransform_x0` and derive the existential
from it. It is mathematically better (same delegation, one less statement). It is **wrong
mechanically**, and the reason generalises: a five-theorem "pinning" chain
(`multiset_eq_of_forall_pow_sum_eq` and friends) had **exactly one consumer in the tree** — the
proof that transports the EXISTENTIAL leaf's witness to an arbitrary multiset. Reversing the cut
deletes that proof's reason to exist and strands all five as free-floating code, which this project
forbids. The existential shape was load-bearing for ~200 lines of proven algebra, and nothing in
either statement says so.
The check is one grep per lemma in the block you are about to orphan:
    grep -rn '<lemma-name>' --include=*.lean . | grep -v '<the file>:'   # external consumers
    grep -n '<lemma-name>' <the file>                                    # internal, minus docstrings
A cut is only free to reverse when the derivation it deletes is not the sole consumer of anything.
## A DOCSTRING THAT INVITES YOU TO DROP A HYPOTHESIS IS A TRAP WITH A WELCOME MAT
(2026-07-31, closing two of the three cases of `exists_ringHom_gamma0GITPresentationOver_of_atlas_aux`
in `X0.lean`.) `exists_rigidifiedModuliData_specF` carried `hℓN : ¬ ℓ ∣ N` under a
Faithfulness note saying it is "**not claimed** to be load-bearing … it is passed in
because it is available at the call site and because whether the development's
`CyclicSubgroupOfOrder` is the Drinfeld notion at `ℓ ∣ N` has not been checked. **A
prover who does not need it should say so and drop it.**"
Dropping it would have closed my leaf in one line. It would also have been the
`one_le_break` failure in a new suit: the two leaves underneath are SORRIES, so widening
them costs nothing at build time and cannot be caught by any test. **A hypothesis on a
sorry leaf is the only thing standing between the leaf and being false; deleting one is
not a simplification, it is an unaudited new claim.**
The check the docstring said had not been run took ten minutes and was not in the
literature — **it was in the file, in the structure definition**. `CyclicSubgroupOfOrder`'s
`geom_cyclic` field demands, at every geometric point, an honest point of order exactly
`N` generating the fibre — i.e. `N` DISTINCT geometric points. `ker F` on a supersingular
curve in characteristic `p` has one. So the structure is the NAIVE notion, the Katz–Mazur
6.6.1 citation attached to it (relative representability and finite flatness, which is a
DRINFELD statement) is not about it at `ℓ ∣ N`, and the invitation was withdrawn in the
docstring rather than accepted.
Generalisable: **when a docstring says a hypothesis is "carried but probably not needed",
treat that as an OPEN QUESTION with a named owner, never as a licence.** Two moves settle
it cheaply, in this order: unfold the DEFINITION the hypothesis is about (not the theorem,
and not the literature), and check what the statement's conclusion asserts about the
degenerate case the hypothesis excludes. Only a written audit of both buys the deletion.
## COUNT BOTH DIRECTIONS BEFORE DOING DECLARATION-ORDER SURGERY
Same leaf, same day, and it is the reason the leaf was reachable at all. Its docstring
recorded the blockage correctly — "a declaration-order artifact and nothing else",
`exists_gamma0GITPresentationOver_zmod` proves the `p ∤ N` case verbatim ~2300 lines
below — and prescribed the fix as **hoisting the producer UP**: the whole `𝔽_ℓ`
rigidification chain, ~2000 lines, in an 82 000-line concurrently-edited module. Two
successive task prompts repeated that as the plan.
**Moving the CONSUMERS DOWN was six declarations and ~430 lines.** The producer's
dependency cone is usually much larger than the consumer's, so the obvious direction is
usually the expensive one. Count both before cutting; the cheap direction is found by
grepping what sits BETWEEN the two positions and consumes the block (here: nothing — the
furthest-reaching of the six is next used ~700 lines below the destination).
**And a block move can be made SAFE in a contended file, which is what makes this
tractable at all.** Do it with a script that slices line ranges, then verify the result is
a PURE PERMUTATION of the original lines:
    python3 - <<'PY'
    from collections import Counter
    a=Counter(open('/tmp/X0.before').read().split('\n'))
    b=Counter(open('Fermat/.../X0.lean').read().split('\n'))
    print("added:",dict(b-a)); print("removed:",dict(a-b))
    PY
Anything in `removed` is a bug in your slice indices; `added` must contain exactly the
section/`open`/blank lines you meant to insert. That check costs a second and is stronger
than reading the diff, because a 1200-line reordering diff is unreadable. Leave a
breadcrumb at BOTH positions — the old one saying what left and where to, the new one
saying what arrived and why — since the next reader of either site will otherwise
rediscover the blockage.
## VERIFY AGAINST THE LAST GREEN RELEASE'S OLEANS WHEN YOUR IMPORT CONE IS RED — and prove the shim sound by DIFFING THE API
(2026-07-31, `flt-lean-115`.) A target can live only on `merger`, and `merger` can be
RED in a module your file imports, for a reason that is not yours and whose repair is
somebody else's multi-hour task. Release 27 was in exactly that state: it was **not
published** (`tools/merge/RELEASE-27-HANDOVER.md`), `main` stayed at the last green
release, and `ModularCurve/X0.lean` carried ~193 errors *inherited from release 25*. So
`git merge merger` — which the doctrine correctly prescribes when your target exists
nowhere else — buys you the declaration and takes away `lake build`, because
`ModularCurve/X1.lean` imports `X0`.
**You are not blocked, and you must not "fix" X0 to unblock yourself.** The scratch shim
this file already documents for the *lake-deletes-the-target-olean* case is the general
answer, and this is its strongest use:
    cp -rs ~/.flt-release-lake/build/lib /tmp/relean-N/          # symlink farm, ~0.3 s
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" lean Fermat/Scratch.lean
The farm is the LAST GREEN RELEASE's artifacts, so the red module is replaced by its
green predecessor and a scratch that `public import`s it elaborates in about a minute.
Here it verified 440 lines — three new leaves, five proven transport declarations and
the target's whole proof — first try, with exactly the three intended
`declaration uses 'sorry'` warnings.
**THE SOUNDNESS CONDITION IS NOT "the shim ran green"; it is that every name you use is
PRESENT AND UNCHANGED at the snapshot's sha, and you check that mechanically:**
    git show main:<the upstream file> > /tmp/up-main.lean
    # then, per name, compare the declaration text in /tmp/up-main.lean with your tree's
Nine names were compared this way (`IsFibreIdent`, `fibreIdentPullback`,
`IsSmoothProperCurve`, `finite_compl_range_fibreBaseChangeMap_generic`,
`genericFibreClassify`, and the four `Γ₁` structures) and all nine were byte-identical,
which is what makes the green scratch a genuine verification of the text that goes into
the file. The check also FOUND the one place it fails:
`exists_unit_natCast_of_isReductionBase` is merger-only, so a leaf stated over the
Katz–Mazur proviso `∃ n, 3 ≤ n ∧ IsUnit (n : ↥R)` could not have been verified — the
leaf was stated over `IsReductionBase` instead, with the improvement named in its
docstring for whoever takes it. **Design your cut around what the shim can verify**;
that is a cheap constraint and it is much cheaper than an unverifiable commit.
Two riders. Extract the scratch from the REAL FILE by line range once the edit is in
place, rather than keeping a hand-typed parallel copy — that way the thing you verified
and the thing you committed are the same characters. And a full shim run of the edited
module itself is worth launching in the background as a second opinion, but it is only
evidence about the parts that do not touch merger-only upstream names.
## A DEGENERATE-CASE ESCAPE HATCH IS THE ONE PART OF A TWIN TRANSCRIPTION THAT DOES NOT TRANSFER
(2026-07-31, the `Γ₀` → `Γ₁` transport of `X0.lean`'s integral-model trio into
`X1.lean`.) This development is built out of twin layers, and transcribing one onto the
other is a standard and highly productive move: five declarations came across here with
`Gamma0Datum` → `Gamma1Datum` and `IsBaseChangeOf` → `IsBaseChangeOfGamma1` and *nothing
else changed*, because none of those proofs ever looks at the level structure.
**The exception is the degenerate parameter, and it is exactly where the two problems
genuinely differ.** `X0.lean`'s `exists_unique_genericFibre_universal` carries no
positivity hypothesis and discharges `N = 0` by EMPTINESS: `isEmpty_of_gamma0Datum_zero`,
because a cyclic subgroup scheme of order `0` cannot exist, so the coarse space is empty,
hence initial, and the `∃!` is trivial. Copy that and you have written a false
justification: `Gamma1Datum` carries a `PointOfExactOrder`, whose clause is
`addOrderOf … = N`, and `addOrderOf x = 0` is the ordinary statement that `x` has
INFINITE order — which an elliptic curve over an algebraically closed field has in
abundance. So `Gamma1Datum 0 T` is INHABITED where `Gamma0Datum 0 T` is not, `[Γ₁(0)]` is
not a Katz–Mazur moduli problem, and the transcribed statement at `N = 0` is neither
supported nor refuted by anything in the tree.
That is the [[flt-third-outcome-strengthen-the-axioms]] situation, and the cheap response
is to EXCLUDE rather than gamble: add `0 < N` to the leaf. It weakens the leaf, so it
cannot make it false, and here it cost nothing at all — the only consumer already carried
`¬ ℓ ∣ N`, and every `ℓ` divides `0`.
**The general rule: when transcribing between twins, list the places the SOURCE proof
discharges a degenerate case, and re-derive each one at the target.** They are easy to
miss because they are usually a single `rcases … with hN | hN` branch inside an otherwise
mechanical proof, and because the transcription compiles perfectly without them — the
degenerate branch of the source is exactly the part you are NOT copying when the target's
version is a `sorry`. Grep the source for `Nat.eq_zero_or_pos`, `isEmpty_of_`,
`Subsingleton`, and `IsInitial`; those four cover most of them here.
Corollary about the leaf count, since it is the shape of this whole task: cutting the
trio took `X1.lean` from 24 direct sorries to 26. **One leaf became three and that is
DISCLOSURE.** What changed is that a single citation naming three classical theorems in
prose became three statements naming one theorem each, and that everything between them
and the node — the generic classifying map, its naturality, the coarse structure of the
generic fibre, the cusp-locus count and the three geometric fields — is Lean instead of
promise. Judge it by what is LEFT in each leaf, not by the delta.
## A DELETION COMMIT IS NOT A CURRENT ABSENCE — and the recovery instruction is what fossilises it
(2026-07-31, `exists_rationalCuspSectionsX1_field`.) A task prompt for this leaf ranked its
second route as "needs the Tate uniformisation, which was DELETED as free-floating in
`52297bf2` — recover with `git show 52297bf2...^:<path>`". Every clause of that is checkable and
the first two are TRUE: the sweep really did delete `TateCurveConstruction` (1551 lines) and
`TateUniformization` (2890 lines) on 2026-07-18. The conclusion is false. Both were rebuilt and
are in the tree today at **16 000 lines across six modules**, and `TateSepClosure` is
`public import`ed by `FreyCurve/Semistable.lean` and `Modularity/Interface.lean`, so the whole
chain compiles on every build. One `ls` of the directory refutes it.
**The recovery instruction is what makes this worse than an ordinary stale claim.** "Deleted —
recover it with `git show`" reads as *already checked, and here is the workaround*, so the reader
runs the `git show` rather than the `ls`. It also carries a citation, which is the shape doctrine
already flags as self-certifying: the commit is real, the diff is real, and the claim is still
wrong about the present. **A deletion commit is evidence about a moment, and this tree re-adds
deleted material routinely** — the free-floating sweep deletes what has no consumer *yet*, and
the same theory comes back when a consumer appears.
So: **before quoting any absence, `ls` the directory and `grep` the tree at HEAD.** And when the
absence turns out to be stale, do not just fix your own note — the false claim propagates through
prompts, so correct it where the next agent will read it (the declaration's docstring), and say
what IS there.
The correction changed the whole cost estimate, and a four-line scratch settled it in one
`lake env lean`: for a bare `(K : Type) [Field K]`, `TopologicalSpace K⸨X⸩`, `CompleteSpace K⸨X⸩`
and `WeierstrassCurve.tateCurve q : WeierstrassCurve K⸨X⸩` all elaborate, with no hypothesis on
`K` and no characteristic assumption — the in-tree Tate curve is defined over
`{k : Type*} [Field k] [TopologicalSpace k]` by `tsum`s, not over a characteristic-zero local
field. So the route is to INSTANTIATE an existing theory, not to build one. **"Needs a theory
nobody has written" and "needs an instantiation nobody has run" are different dispatches, and
only the second is one an agent can finish.**
The same scratch also located the real blocker one layer lower than the mathematics predicts:
the first missing instance is `ValuativeRel K⸨X⸩` — mathlib has `Valued K⸨X⸩ ℤᵐ⁰` and a
`Valued`-to-`ValuativeRel` bridge and nobody has connected them — not local compactness, which
is the *second* obstruction and only bites over infinite residue fields. **A negative instance
probe is worth writing even when you are sure of the answer**: "which instance fails FIRST" is a
different question from "which hypothesis is mathematically false", and it is the one that sizes
the next task.
## A target that exists only on `merger` is workable — put it in a NEW MODULE
(2026-07-31, `flt-lean-335`.) The dispatch prompt for
`exists_nonconstant_toAbelianScheme_of_baseChange_relPoint` said: it was cut on a
branch, it is on `merger`, and if it is not in your worktree, **"WAIT for the release
rather than restating it"**. The check was right — the leaf was on `merger` at
`df076668` and absent from `main` — but "wait" is not an action an agent can take. The
loop has no pause; ending the turn is death, and a worker that reports "blocked until
the release" burns a whole worktree-cycle and delivers nothing.
There is a third option between *restating it in the file* (which conflicts with the
merge worker's own copy, guaranteed, because that file is being rewritten by thousands
of lines per release) and *waiting*:
**State the theorem VERBATIM in a new module, prove it there over named atoms, and
leave the merge worker a one-line delegation to write.**
- A new file cannot conflict with anything. The only edit to the contested file is one
  `public import` line, which merges trivially wherever it lands.
- Put it under `Fermat/FLT/Mathlib/…` when the statement mentions nothing specific to
  the file it was cut from — which is common, since leaves get cut *because* they are
  the level-free residue. Then the sibling curve file wanting the same theorem gets it
  for free instead of restating it a third time.
- Use a distinct NAMESPACE (`Fermat.WeilRestriction.foo`), not a distinct name. The
  merge worker's job is then `:= Fermat.WeilRestriction.foo h₁ h₂ h₃` with the
  hypotheses in the same order, and nothing has to be renamed if the release lands
  first.
- Say so in `to_merger`. The commit alone is not read.
Cost of getting this wrong in the other direction is asymmetric: a duplicate proof of
one theorem cannot be carried (the name collides), so restating in-file forces a merge
worker to CHOOSE between two branches' mathematics; a new module forces nobody to
choose anything.
The residue's top theorem is then FREE-FLOATING until the release wires it — that is
expected and is not a defect to chase. Record it in the module docstring so the next
floating sweep does not delete it.
**Also: `lake` is not on `PATH` in a fresh agent shell**, even working locally on the
worktree's own host, and the failure is `lake: command not found` with `EXIT=127` —
which reads like a broken worktree rather than a shell setup. `export
PATH="$HOME/.elan/bin:$PATH"` first, in every Bash call (shell state does not persist
between calls).

## AN IMPORT CYCLE IS A WHOLE-PROJECT OUTAGE, AND THE BRANCH THAT CAUSES IT CHECKS THE DIRECT EDGE ONLY

(2026-07-31, release 28, and it cost the first two build rounds.) `flt-lean-389`
closed a leaf in `ModularCurve/HyperellipticJacobian.lean` by adding
`import Fermat.FLT.ModularCurve.X0`, under a comment that said in as many words
*"there is no cycle, since `X0.lean` does not mention"* this file.  The direct edge
really is absent.  The cycle is two hops long:

    X0  -->  FreyCurve/IsogenySignature  -->  HyperellipticJacobian  -->  X0

and both of the other edges are years-old and pre-existing.  The result is not a
red module: `lake build` fails on the ROOT target with `build cycle detected` and
**nothing in the project builds at all**, which reads like a catastrophically
broken tree rather than like one bad import line.

Three things follow, and the third is the one worth institutionalising.

* **Any import you ADD must be checked against the transitive closure, not the
  direct edge.**  Ten lines of Python, and it must ASSERT that every visited
  module's file exists — a swallowed `FileNotFoundError` truncates the walk and
  manufactures exactly the "incomparable, no cycle" answer you were hoping for.
* **A cycle-breaking hoist should go into a NEW MODULE, not into the destination
  the offending comment names.**  `flt-lean-389`'s note prescribed
  `Modularity/AbelianSchemeIsogeny.lean`, which is right architecturally and
  expensive in practice: `X0.lean` `public import`s it, so adding one import there
  rebuilds the largest cone in the tree.  A new module rebuilds only its own
  consumers, and it cannot conflict with anything.  Move the declarations
  VERBATIM with their docstrings; the only edit should be spelling out any
  `abbrev` (here `SpecQ`) that is declared in the module you are moving OUT of.
  An `abbrev` is reducible, so every existing call site elaborates unchanged and
  no delegation is needed.
* **The merge worker must run a cycle check as a standing release check**, beside
  the comment and scope scans.  It costs a second and its failure mode is total.

## semmerge's SCOPE-LINE HOLE HAS THREE SHAPES, AND ONLY ONE OF THEM SAYS "end"

(Same release, four instances in one batch.)  `tools/merge/README.md` already warns
that `namespace`/`section`/`variable` live in the GLUE between declaration blocks,
so taking theirs for a block deletes the glue that followed ours.  What it does not
say is that the three ways this surfaces look nothing like each other:

1. **A lost `end <Name>`** — reported at the END OF THE FILE as
   `Invalid name after 'end': Expected X, but found Y`, thousands of lines from the
   damage.  This is the only shape that mentions scopes at all.
2. **An unclosed `section` whose `variable` stays in scope** — every later
   declaration silently gains a binder, and the errors are `Function expected at`
   and `Tactic introN failed` at the USE sites.  In `MoretBailly.lean` one lost
   `end StepanovDerivationCalculus` produced 39 of these and no scope message
   until the very last line of the file.
3. **BOTH sides' closing `end`s kept** — the second half of the file lands OUTSIDE
   the namespace, so its declarations get the wrong qualified names and consumers
   report `Unknown identifier` on names `grep` finds.

`scopecheck.py` sees all three, and it earns its 93 baseline false positives: every
one of the four real wounds this release was in its DELTA against pre-merge merger,
and two of them were in modules no build has ever REACHED (they sit behind X0), so
nothing else could have found them.  **Difference against the baseline with the LINE
NUMBERS NORMALISED AWAY** — most reports move by exactly the number of lines your
edits inserted, and a naive set-diff calls all of them new.

**Repair direction: restore the missing opener rather than deleting the surviving
closer.** Deleting an `end` can leave a `variable` in scope past where its author
intended, which is shape 2 — i.e. the cheap-looking repair is the bug.

## semmerge DOES NOT REORDER: a branch's CONSUMERS can land above merger's PRODUCER

(Same release, `MoretBailly.lean`.)  The README says an added helper can land BELOW
its consumer.  The mirror happens too and is commoner when the branch RESTRUCTURED
the file: `flt-lean-294` had `stepanovTotalFilt` at line 14885 and its new
`stepanov_totalFilt_*` block after it; merger had `stepanovTotalFilt` at 18423.
semmerge placed the branch's new block next to its merger-side neighbours, i.e. at
~15500 — **2900 lines above the definition it consumes**.

The symptom is `Function expected at` on `(stepanovTotalFilt R).mem`, which reads as
an arity bug in a definition that is perfectly correct.  `grep` finds the name, so
none of the phantom-declaration checks fire.

**Diagnose by comparing the DECLARATION LINE with the first USE line**, and repair by
computing the MINIMAL producer block: list the declarations below the first use, and
keep only those actually named above it.  Here that took a 590-line candidate down to
171 (`StepanovFilt` through `stepanovTotalFilt_mem_monomial`); everything past
`stepanovTotalFilt_mem_monomial` was needed only by later consumers and could stay.
Then hoist that block, with the standard receipt — sorted line multiset identical
before and after, and a token scan showing the block uses none of the declarations it
jumps over.

## WRITING THE NOTE THAT RECORDS COMMENT DAMAGE CAN REOPEN IT

(Same release, caught by re-running the scan.)  CLAUDE.md already says a comment
delimiter spelled inside block-comment prose still NESTS.  It bites hardest in the
one place you are guaranteed to write such prose: the note explaining the repair.
My first draft of three "orphaned docstring body, reopened" notes contained the
opener and closer as inline code, which added two levels of nesting per note and
turned three STRAY reports into an UNCLOSED one.

Name the delimiters in WORDS in any comment about comments, and say in the note that
you did — the next editor will otherwise "improve" it back.  And re-run the scan
after every such edit, not just after the repair it documents.

`tools/merge/commentscan.py` (added this release) is the scanner: character-level,
nesting-aware, and it reports **UNCLOSED and STRAY separately** because the two
cancel.  `checks.py check-comment` walks LINES and clears a block at the first line
containing a terminator, so it cannot see either shape — it reported the whole tree
balanced while four files were wounded.  Run the new one tree-wide, every release,
before the first build: it is the cheapest check there is and one parse error hides
every later error in an 84 000-line module.

## A RED MODULE CAN HIDE 249 DUPLICATE DECLARATIONS IN THE MODULE BEHIND IT, FOR THREE RELEASES

(2026-07-31, release 28, found by running `tools/merge/xdup.py` and DIFFERENCING it
against the last GREEN release rather than against the previous merge base.)

`FreyCurve/MazurTorsion.lean` has not been compiled since release 25.  It is
downstream of `ModularCurve/X0.lean`, X0 has been red since release 25, and
`lake build` stops at the first red module in a cone — the SEVENTH invisibility
class this file already documents.  What that class does not say is how much can
accumulate behind one red module, and the answer here is **249 hard
`has already been declared` errors**:

    165   FreyCurve/IsogenySignature.lean  <->  FreyCurve/MazurTorsion.lean
     84   ModularCurve/X0.lean             <->  FreyCurve/MazurTorsion.lean

with `MazurTorsion.lean` `public import`ing both.  Every one is a build-stopping
error, and not one of them is visible to `lake build`, to the
`declaration uses 'sorry'` warning set, or to any frontier scan.

**The cause is a hoist that never deleted its source, and `git` proves it in two
commands.** At the last green release `7080929d`, `IsogenySignature.lean` declared
`GaloisRepresentation.globalValuationSubring` ZERO times, `MazurTorsion.lean`
declared it, and `MazurTorsion` did not import `IsogenySignature` at all.  Now both
declare it and the import is there.  `semmerge.py` propagates a branch's ADDITIONS
and never its DELETIONS, so no merge could have removed the originals.

Three things to carry:

* **Difference `xdup.py` against the last GREEN release, not against the previous
  merge base.** Release 27 differenced against its own base, got EMPTY, and
  concluded the tree was clean — correctly, and uselessly, because the duplicates
  predate that base.  A check whose baseline is itself broken certifies the
  breakage.  The green release is the only baseline that means anything.
* **A module nothing has built is not "probably fine".** Behind a red module, ALL
  the ordinary evidence is silent by construction, so the prior should be that it
  is broken in proportion to how long it has been dark and how much has merged.
  Elaborate it directly with the LEAN_PATH shim rather than waiting for the cone.
* **When you HOIST a block, the deletion of the source is part of the hoist**, and
  it is the half a declaration-level merge cannot carry for you.  Say in the branch
  report which declarations you removed from where; that note is the only thing
  standing between the hoist and this.
## WHEN A RED MODULE ELSEWHERE IN YOUR CONE BLOCKS THE BUILD, ELABORATE AGAINST THE **PRISTINE** RELEASE SNAPSHOT
(2026-07-31, `flt-lean-117`, on `HilbertModularity.lean`.) The scratch-module and
`LEAN_PATH`-farm tricks above are written for one situation — `lake build` has deleted
the olean of the very file you are editing. There is a second, and under a
non-publishing release it is the commoner one: **your file is fine and some unrelated
module in its import cone is RED.** `ModularCurve/X0.lean` has not built since release
25; it is in the cone of 8 modules including this one; and
`tools/merge/RELEASE-27-HANDOVER.md` hands its repair to a dedicated owner as a
multi-hour job. So `lake build <your module>` cannot terminate green for anybody
downstream of X0, however correct their own work is.
The move is **not** to patch the missing olean into your own `.lake`. That produces
exactly the inconsistent-olean state CLAUDE.md already warns about — here it would have
mixed merger-era oleans for the 46 changed cone modules with release-era oleans for the
7 that sit under X0 and therefore never got rebuilt, and every diagnostic from that mix
is untrustworthy. Use a **pristine, internally consistent** set instead:
    rm -rf /tmp/relean-N && mkdir -p /tmp/relean-N
    cp -rs ~/.flt-release-lake/build/lib /tmp/relean-N/          # symlink farm, 0.3 s
    LEAN_PATH="/tmp/relean-N/lib/lean:$LP" LEAN_SRC_PATH="$LSP" \
      lean -DmaxErrors=200 Fermat/FLT/.../YourModule.lean
`~/.flt-release-lake/build` is the last PUBLISHED release, so it is green and consistent
with itself by construction; `lake env printenv` is required because `lake env lean`
resets `LEAN_PATH` and silently discards your prefix.
**State the caveat, because it is real and it is narrow.** That run does not see the cone
modules that changed between the release and `merger`. It is nevertheless the *relevant*
check for new text whose every dependency is declared EARLIER IN THE SAME FILE, which is
the usual shape of a decomposition — and it is a complete check on the rest of the file
too, in the weaker sense that it proves the file elaborates against SOME consistent
environment. Here it returned `EXIT=0` with zero errors and 13 `declaration uses 'sorry'`
warnings on a 37 000-line module, which is exactly the evidence a decomposition needs:
the old leaf's warning is gone and the new leaf's is present.
Two riders.
* **`tools/merge/frontier.py` hardcodes `ROOT = /home/chend/flt-staging`.** Running it from
  your worktree silently scans the MERGE WORKER'S tree and reports its leaves with its line
  numbers — the same trap as `flt-hidden-sorries.py`
  ([[flt-hidden-sorries-scans-main-repo]]), and it is much harder to notice here because
  the answer *looks* like your file. For a single-file leaf count, read the
  `declaration uses 'sorry'` lines out of your own `lean` log instead; that is the
  compiler and it costs nothing extra.
* **`git diff HEAD~1 HEAD -- <file> | grep -E '^[+-] *sorry *$'` is the one-line receipt
  for a RECUT.** One `+  sorry` and one `-  sorry` is the mechanical form of "count
  unchanged, 1 → 1", and it belongs in the commit message next to the prose claim, for the
  reason the RECUT section above gives: a warning-set delta of −1 +1 is otherwise
  indistinguishable from one closure plus one unrelated disclosure.
## YOUR TASK MAY BE DONE ON `merger` AND ITS **RESIDUE** STILL UNOWNED — TAKE THE RESIDUE
(Same run.) The release-window rule says to run `git show merger:<file> | grep -n <name>`
before your first edit, and it says what to do when the answer is "already proven":
decline and report. That is right for a leaf. It is **too weak for a CUT-LEVEL task**,
because a cut-level task names a repair with several steps, and the agent that landed it
on `merger` may deliberately have taken only some of them.
Here the assigned task was the ten-signature `IsTraceGenerated` transport to
`HilbertAuxDeformationDatum`. Steps 1–3 (define the predicate, add the hypothesis to the
two leaves, thread it down the one-call-site-per-step chain) were all on `merger`. Step 4
— the TERMINUS, which the task itself called "the only mathematics in the task" — had been
opened as a named leaf exactly as the task's own fallback instructed, and **nobody was
dispatched at it**, because it did not exist on `main` when the queue was written. That is
the class-5 invisibility of a decomposition performed on an unmerged branch, and the agent
whose task created the leaf is the one best placed to see it.
So the procedure when your target is already closed on `merger`:
1. read the landed version and **enumerate which of your task's steps it took**;
2. if a step was converted into a NEW leaf, that leaf is unowned by construction — grep
   `~/.flt-loop/jobs/*.prompt` to confirm, then take it;
3. **fast-forward your branch to `merger`** (`main` is an ancestor of it, so the FF is
   clean) rather than re-deriving anything against `main`. Your branch then merges as a
   fast-forward, and you cannot land a rival cut of work that is already in.
The cost of (3) is the section above: `merger` may not build. Weigh that before FF-ing —
but note the alternative is worse, since the declaration you need to edit only exists
there.
## SPLITTING `A ∧ B` INTO `A` AND `A → B`: THE CHECK IS AGAINST THE *WEAKENED* `A`
(2026-07-31, `RelativePicard.lean`, third cut of that day.)
`exists_relPicZeroSubfunctor` carried two classical chapters at once and said so in its own
docstring — the identity component of a group scheme (SGA3 VI_B 3.10) and properness of `Pic⁰`
(BLR 9.4) — with "whoever takes the leaf takes both". They share no machinery, so they split:
one leaf is the old conclusion **minus** `IsProper jstr`, the other takes that entire conclusion
as its hypotheses and returns `IsProper jstr`. The assembly is `obtain` + repackage.
**The trap, and it is not the obvious one.** Splitting a conjunction looks faithfulness-neutral
because each half is implied by the parent. The first half genuinely is. The second half is
`A → B`, and `A` is now WEAKER than the parent's conclusion — so it admits witnesses that the
deleted conjunct used to exclude, and `A → B` must hold for **every one of them**, not for the
intended `J`. Here `J = P`, `incl = id` satisfies the first half's every clause except
geometric connectedness, and `Pic` is not proper: had the connectedness clause not been there,
the properness half would have been FALSE while both halves still "followed from the parent".
So the cut's real cost is one audit paragraph, and it is the only nontrivial thing about the cut:
**enumerate what the deleted conjunct used to exclude, and name the surviving clause that
excludes it now.** Write it on the second half, where its owner reads it. If no surviving clause
does the excluding, the cut is wrong — put the discriminating property back into the first half's
conclusion rather than hoping the second half's owner will notice.
## A LAW PROVEN INSIDE AN EXISTENTIAL IS INVISIBLE — RECOVER IT BY UNIQUENESS
(2026-07-31, same file, and this one is worth more than the cut it enabled.)
`exists_abelJacobiPoint` is PROVEN and yields `∃ aj, spec ∧ aj_pre ∧ aj_base`. Every leaf below
it receives `aj` and `spec` as *hypotheses* — and therefore holds neither `aj_pre` (naturality)
nor `aj_base`. Four leaves had been stated that way. The geometry owner could not even say the
Abel–Jacobi image passes through the origin, which is the hypothesis of the SGA3 theorem being
invoked; the identity-component argument was unstartable for a packaging reason.
Nothing was missing mathematically. **The spec DETERMINES `aj` pointwise** (via the file's own
`IsRelPicOf.eq_of_relPicEquiv_tensor`), so any family satisfying it *is* that family and both
laws transport to it. Three short theorems — a uniqueness lemma plus one transport each — put
them in the hands of any consumer, and the hard proof inside `exists_abelJacobiPoint` is not
repeated even once: the new lemmas `obtain` its witness and rewrite along uniqueness.
**Generalisable, and this codebase is full of the pattern.** Whenever a leaf's hypothesis list
is `(f, one clause about f)` and some proven `exists_f` theorem produces `f` with MORE clauses,
ask whether the one clause pins `f` uniquely. If it does, every other clause is free to the leaf,
and withholding them is pure loss. Symptom to grep for: a leaf whose hypothesis is a *choice
function* plus a *specification*, where a sibling `exists_…` theorem in the same file bundles
extra laws about the same object.
Corollary for whoever states such a leaf: **do not hand a consumer a bare `(f, spec)` pair when
you have proven more about `f`.** Hoist the extra laws to standalone theorems quantified over an
arbitrary `f` satisfying the spec, and pass them in. It costs a uniqueness lemma once.
**Unrelated, measured while doing this:** `RelativePicard.lean` takes **11 minutes** under
`lake env lean`, not the ~25 s a task prompt claimed. Time an iteration before planning around it;
at that length the scratch-module rule matters more than usual, and batching every edit into one
verification is not optional.
## A REFUTATION POISONS PROOFS, NOT STATEMENTS — compute the poisoned subgraph before deleting a tower
(2026-07-31, `flt-lean-124`, on `Threeadic.lean`.) `dc6836b9` did the right thing in
the right direction: `eq_one_of_smul_eq_mul_localInertia_connected_threeTorsion` was
refuted, so the cut walked UP its call graph to the lowest declaration whose own
statement is TRUE, sorried that, and deleted the `35` declarations below. The
deletion was verified carefully — exact sorry ledger, zero dangling references,
green builds of the module and all three importers — and every one of those checks
was correct.
**It deleted twice as much as the refutation touched.** Building the citation graph
of the pre-cut file restricted to the `35` deleted names and taking the transitive
closure of the false leaf's consumers gives **18 poisoned and 17 clean**. The clean
17 are ordinary proven theorems that were deleted only because they became
consumerless once the tower above them went — which is a consequence of the
deletion, not evidence for it.
**What you want is not the poisoned SET but its MINIMAL elements — where the poison
ENTERS.** The transitive closure necessarily swallows everything above an entry point,
including the theorem the cut was aiming at, so reading it as "all of this is unusable"
is exactly the mistake. Along the chain to the target the poison entered at just two
declarations; the four above them cite the false leaf only THROUGH those two, so
re-sorrying the two entry points restores all four with their original, previously
verified proofs. That moved the frontier from one bundled leaf to two crisp
coefficient-free ones, put ~840 lines of proof back in the tree, and left strictly less
open mathematics — at the cost of `+1` on the sorry count, which is the disclosure
trade this file already describes.
So the procedure when a leaf is refuted, before deleting anything:
    for each declaration D in the cone:
        poisoned(D)  iff  D cites the false leaf, or D cites a poisoned declaration
computed on the COMMENT-STRIPPED source of the pre-cut file, attributing each
citation to its enclosing declaration by walking backwards to the nearest header.
Delete the poisoned set; keep the clean set if anything still consumes it; and cut
at the *lowest poisoned* statements rather than at the lowest true one, because a
poisoned statement is usually still true and is a better leaf than the theorem three
levels above it.
Two corollaries that are easy to get backwards:
* **"Its proof used the false leaf" is not a falsity audit of its statement.** Both
  statements re-cut here are untouched by the recorded counterexample — one is about
  scalar-stability of a connected locus and the witness is about how wild inertia
  acts on a large socle. Check what the witness actually instantiates before
  concluding a statement went down with its proof.
* **A clean-but-consumerless proven theorem is worth listing by name in the cut's
  docstring**, with the fact that it is clean. Four of the 17 here were exactly what
  the restoration needed, and one — `le_span_singleton_sup_smul_pow_of_displacement_surjective`
  — carries a counterexample (`N = A·(1,0) + A·(0,3)` over `ℤ/9`) showing why the
  naive Nakayama step everyone reaches for is FALSE. That kind of content is
  unrecoverable in practice once it is only in a deleted range nobody remembers.
## A "PROVEN OVER <your leaf>" CLAIM IN A DOCSTRING IS WHAT THE TASK PROMPT WILL SAY — GREP THE PROOF, AND GREP THE CONSUMERS
(2026-07-31, `flt-lean-141`, on `ModTriv.eq_coord_smul_genAt` in
`Modularity/AmpleSheaf.lean`.)
The task prompt opened: *"Everything else about that theorem is now written and green:
`exists_trivialization_of_modTensor_trivial` is PROVEN over this leaf alone … Closing
this leaf closes `exists_trivialization_of_modTensorPow`,
`isInvertibleSheaf_of_isAmpleSheaf` and the numerical-semigroup bridge."* Every clause
was false, and none of it was invented by the dispatcher — it is a **verbatim
paraphrase of that theorem's own docstring**, which says *"(PROVEN 2026-07-31 over
`exists_modPair_eq_one` and `ModTriv.eq_coord_smul_genAt`)"*. The theorem's actual
`by` block cites neither. It was proven the PREVIOUS day, by an unrelated route
(`isIso_of_isIso_modTensorMap` over `exists_modUnitHom_isIso_modTensorMap`), and a
later agent building a second route wrote its own intent into the consumer's docstring
without re-reading the proof.
So the leaf was **open, live in the warning set, unowned, and DEAD** — the seventh
invisibility class — and the whole cluster it sits in (`modPair`, `ModTriv`,
`exists_modPair_eq_one`, `trivOfPair`) is a complete, consumerless SECOND ROUTE.
`trivOfPair` and `exists_modPair_eq_one` each occur **exactly once** in `Fermat/`, at
their own declarations.
Two checks, both cheap, and the first is the one nobody runs:
* **Read the PROOF of the theorem the prompt says your leaf unblocks.** Not its
  docstring, not its headline — the `by` block. If your leaf's name does not occur in
  it, the dependency claim is prose. This is the same rule as *"THAT THEOREM HANDS BACK
  X is a claim about its CONCLUSION"*, one level down: here it was a claim about its
  *proof*, and proofs are even easier to check.
* **Then grep the CONSUMERS of your leaf's own downstream chain**, transitively, until
  you reach something in the root cone. Openness and reachability are different
  properties and every frontier instrument reports only the first.
**AND A DEAD LEAF CAN OFTEN BE CLOSED BY DERIVING IT FROM THE THEOREM IT WAS MEANT TO
PROVE.** Once the real proof exists, the leaf is usually a *consequence* of it rather
than an input. Here local freeness (`exists_trivialization_of_modTensor_trivial`) gives
one generator `g` near each point, `ModDual.eq_smul_gen` writes `x = r·g` and
`s = c·g`, and the symmetry `x = ⟨x,t⟩·s` is the rearrangement `(r·d)·c = r·(c·d) = r`
where `c·d = 1` is the unimodularity — thirty lines, plus one
`Presheaf.IsSheaf.section_ext` on `L.isSheaf` to glue the local statement. No
circularity: Lean's declaration order enforces that for you, and here it forced the
tail of the `ModTriv` namespace to be relocated below the theorem it now cites.
**Report the accounting honestly, because it is unflattering.** This is `−1` on the
direct-sorry count and `0` on the mathematics: nothing became provable that was not
provable before, and the transitive cone did not move, since the theorem cited was
already in the root cone (per *"A DECLARATION-ORDER BLOCKAGE IS DISCHARGED BY AN OPEN
LEAF ABOVE"*). Say so in the commit and in the docstring, or the next reader will
believe a theory gap closed.
**The residue is the useful output, and it is a different name.** The live leaf of that
file is `exists_restrict_modTensor_tensorSection` — the pinned comparison
`(L ⊗ N)|_W ≅ L|_W ⊗ N|_W` — which `exists_modUnitHom_isIso_modTensorMap` consumes and
which everything downstream of `isInvertibleSheaf_of_isAmpleSheaf` actually waits on.
The dead second route retains exactly one possible value: proving its symmetry
*independently* (the idempotent route its own audit describes) would make that leaf
consumerless. Write that into the docstring, since it is the only thing that would ever
make the block pay for itself.
## A GROUP SCHEME IS BUILT BY YONEDA, NOT BY THE PULLBACK CALCULUS
(2026-07-31, `flt-lean-146`, closing `smooth_schemeTheoreticImage_of_isAdditiveOn`.)
Mathlib's Cartier theorem `AlgebraicGeometry.smooth_of_grpObj` wants `GrpObj (Over.mk f)`,
and the recon for that leaf priced the `GrpObj` as "no mathematics, a lot of plumbing, and
by volume the bulk of the work" — because the obvious construction gives `mul : X ⊗ X ⟶ X`,
`one : 𝟙_ ⟶ X`, `inv : X ⟶ X` and checks five diagrams, each an equation of morphisms out
of an iterated fibre product, in `CartesianMonoidalCategory`'s associator/unitor vocabulary
against this project's `Limits.pullback` one. The recon also prescribed a refactor of the
neighbouring proof to export its three `IsClosedImmersion.lift`s as named declarations.
**None of that was needed.** `CategoryTheory.GrpObj.ofRepresentableBy` builds a group object
in ANY cartesian monoidal category out of a REPRESENTABLE PRESHEAF OF GROUPS. Supply a
functor to `GrpCat` and a `Functor.RepresentableBy`, and every axiom becomes an equation
between ELEMENTS of a type — here `RelPoint bstr g` — with the pullbacks never appearing.
The three morphisms were never written down. Total cost: one general lemma
(`nonempty_grpObj_of_relPointGroup` in `X0.lean`, ~25 lines of proof) plus five two-line
bullets instantiating it.
Three facts that make it work here, all worth knowing before starting:
* **`Over S`'s monoidal structure IS `Limits.pullback`, on the nose.** `tensorObj_left`,
  `lift_left`, `fst_left`, `snd_left`, `toUnit_left` are all `rfl`
  (`Mathlib/CategoryTheory/Monoidal/Cartesian/Over.lean`), and
  `AlgebraicGeometry/Pullbacks.lean:705` registers the instance globally for `Over S` with
  `S : Scheme`. So the "matching two vocabularies" cost the recon feared is zero — but you
  only find that out by reading the file, and the `RepresentableBy` route means you never
  need to.
* **The naturality obligations are exactly two**, `pre_mul` and `pre_one`, because a group
  homomorphism is a `MonoidHom`: nothing has to be said about inversion.
* **`GrpObj` is DATA, so the result is `Nonempty (GrpObj …)`**, discharged by `obtain` at
  the one consumer, whose conclusion is a `Prop`. Do not fight to make it an instance.
**The precedent was already in this repo and was not connected to the leaf.**
`Fermat.nonempty_grpObj_of_yoneda` (`Fermat/FLT/GroupScheme/AffineGroupHopf.lean`) is the
same trick on the affine/Hopf side, and `CyclicSubgroupOfOrder.exists_hopfAlgebra_geomFibre`'s
docstring records it being chosen there on 2026-07-28 over "transport a `GrpObj` along an
equivalence", with the reason spelled out: *"it is enough to give a functorial group
structure on the points, with no monoidal functor anywhere."* The generalisation to
`Over SpecQ` is mechanical, and three days passed without anybody making it.
So: **when a leaf asks for a group/monoid/ring object in a cartesian monoidal category,
look for `ofRepresentableBy` before writing a single morphism.** `MonObj`, `IsCommMonObj`,
`GrpObj` and `CommGrpObj` all have one, in `Mathlib/CategoryTheory/Monoidal/Cartesian/`.
The general form of the lesson: *a functor-of-points presentation and a
morphisms-and-diagrams presentation are Yoneda-equivalent, and mathlib carries the bridge —
so pick whichever side the data is already on, and never pay to cross.* This development's
group laws are primitively functor-of-points data (`AbelianSchemeStruct`), so the crossing
was never necessary in the first place.
