## scratch module techniques

(Cut verbatim out of CLAUDE.md's `Verify in a scratch module, not in the giant file` section at the 2026-08-03 doctrine split; nothing reworded.)

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

### THE FARM ALSO WORKS WHEN YOUR TARGET'S MODULE CANNOT BE BUILT AT ALL — the soundness condition is a `git show`, not a build

(2026-07-31, `flt-lean-319`.) The section above assumes the target's cone is merely
*mid-build*. The stronger case is that it is **broken**: `merger` carried a genuine
module import CYCLE (`X0 → IsogenySignature → HyperellipticJacobian → X0`), so
`X0.olean` and `X1.olean` were unbuildable by anybody, for hours, and a
`lake build Fermat.FLT.ModularCurve.X1` could never go green however correct the proof.

The release farm still verifies your text, and the check that makes it HONEST is one
command per name you consume from the broken module:

    R=$(cat ~/.flt-release-lake/sha)
    git show $R:<file>      | grep -A12 "^theorem <name>" > /tmp/a
    git show merger:<file>  | grep -A12 "^theorem <name>" > /tmp/b
    diff /tmp/a /tmp/b        # identical statement => the farm's olean is faithful FOR THIS NAME

Here that was two names (`HasNoFibreAffineLine`, `birationalOver_affineLine_of_not_exists_section`),
both byte-identical between the snapshot and `merger`, and the proof compiled green against
the release `X0.olean` in **4 seconds**. Say in the commit which names you checked; that
list is exactly the strength of the claim, and a reviewer can re-run it.

**Two mechanical notes that make this practical.**

* **Compile a NEW module into the build tree with `lake env lean -o`, never `lake build`.**
  `lake env lean -o .lake/build/lib/lean/<path>.olean <src>` writes the olean directly, takes
  seconds, and — unlike a second `lake build` — cannot start a rival elaboration of anything.
  But the module system also wants `<name>.olean.server` (and `.olean.private`): copy the
  WHOLE `X.olean*` set into the farm, or the scratch dies with
  `failed to open file '….olean.server'`, which reads like a corrupt farm and is not.
* **A declaration absent at the snapshot commit sinks the whole farm run.** Two
  `RelativePicard` base-change wrappers postdated the snapshot, so the scratch reported
  `unknown identifier` for them; the fix is to INLINE their one-line mathlib bodies in the
  scratch (`MorphismProperty.pullback_snd (P := @…)`) and verify the named form separately
  against the current olean. Do NOT overlay a current olean onto the release farm to "fix"
  it — that is exactly the inconsistent-olean-set trap, and every diagnostic after it lies.

**And match the scratch's SCOPE to the target's, not to what is convenient.** `X1.lean`
does not `open Limits` — every declaration in it writes `Limits.pullback.…` — so a scratch
that opens `Limits` proves nothing about whether your block resolves in the file. Read the
target's own `open`/`namespace` header (and remember `^open ` greps hit prose in this
project's docstrings) and reproduce it exactly; then, if you do need `Limits`, add
`open Limits in` to your declaration — ABOVE the doc comment.

**THE ONE THING A SCRATCH STRUCTURALLY CANNOT CHECK IS DECLARATION ORDER**
(2026-07-31, `flt-lean-397`). The scratch `public import`s the whole target module,
so it sees EVERY declaration in it; the paste site sees only what is above it. A
block that compiles in 6 seconds in the scratch can fail in the file for no reason
but position. That bit here: the natural proof of the 6.6.2 assembly in `X0.lean`
wants `exists_fullLevelStructure_baseChange`, which is PROVEN — 1500 lines BELOW
the insertion point. The scratch cannot notice.

So before pasting, run one `grep -n` per non-local name and compare against your
insertion line. It is mechanical and it is not optional. And when a name you need
really is below you, the cheap repair is usually to make it a HYPOTHESIS of the
sub-leaf you are opening rather than to hoist a chain of declarations through a
file the merge worker is concurrently reconciling — say so in the leaf's docstring,
with the exact deletion a future hoister should make.

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
**THE SCRATCH DOES NOT HAVE TO IMPORT THE TARGET FILE AT ALL — abstract the
base ring and the glue compiles without it** (2026-07-31, `flt-lean-193`,
`exists_pderiv_eq_of_minimalPresentation` in `ModThree.lean`). The rule above
says "import only what you need", which is usually read as "import the target's
dependencies". Often you need LESS than that: **the glue of a leaf in a huge
file typically does not depend on any of that file's content.** Here the whole
decomposition — build the ideal `ker α + (3)`, prove it differential, feed it to
the key lemma, divide the result by `3` — mentions `𝒪₃ᵥ` only as "some commutative
ring". So the prototype was
    variable {𝒪 : Type} [CommRing 𝒪] {A : Type} [CommRing A] [Algebra 𝒪 A]
    theorem leaf1 ... := sorry     -- one abstract stand-in per intended leaf
    theorem main ... := by ...     -- the real glue, verified against the stand-ins
in a scratch importing one 400-line support file. **30 seconds per iteration
instead of 25 minutes**, and the transplant into the real file was mechanical:
substitute `𝒪₃ᵥ` for `𝒪`, rename the stand-ins, and the proof script is unchanged.
The generalisation, and the reason this is worth writing down separately: the
scratch's import cone should be sized by **what the PROOF mentions**, not by what
the STATEMENT lives next to. Deciding those are different is a ten-second read of
your own proof sketch, and when they are different it is a 50× round trip.
Two corollaries that fall straight out:
- **Stand-ins force the decomposition to be honest.** You cannot write the glue
  against an abstract `leaf1` without first committing to `leaf1`'s exact
  statement, so the cut is designed before any of it is proved — which is what
  "glue first" asks for anyway. If a stand-in's statement turns out to be
  unusable, you find out in seconds rather than after a 25-minute build.
- **A leaf whose statement is base-ring-agnostic belongs in the support file, not
  in the giant one.** The key lemma cut here (`MvPowerSeries.pderiv`'s
  differential-ideal theorem) went into
  `Fermat/FLT/Mathlib/RingTheory/MvPowerSeries/AdicEval.lean` precisely because
  nothing in it is about `𝒪₃ᵥ`. Whoever is dispatched at it pays a 30-second
  import instead of 25 minutes — the placement decision IS a throughput decision,
  and it is made once, by the agent that cuts the leaf.
**And check whether the API a leaf's STATEMENT uses actually exists** (same task).
`MvPowerSeries.pderiv` had been *defined* in `AdicEval.lean` — enough to state
`pderiv_eq` in a structure field — with exactly one lemma about it
(`coeff_pderiv`) and NO algebra: no additivity, no Leibniz, nothing about
constants. This pin has `Polynomial.derivative`, `MvPolynomial.pderiv` and
`PowerSeries.derivative`, but nothing for `MvPowerSeries`, so there was nothing
to import either. Any leaf mentioning that definition therefore starts with
building the API (the Leibniz rule is the load-bearing one; it is a reindexing of
`antidiagonal (n + eⱼ)` and ran to ~70 lines). A definition existing is not an
API existing, and a docstring that cites the definition does not tell you which.
**COPY THE DEFINITIONS INTO THE SCRATCH; DO NOT `import` THE TARGET FILE**
(2026-07-31, measured, and it turned a dead workflow into a live one).
The obvious scratch — `module` + `public import Fermat.FLT.Modularity.MoretBailly`
— **does not behave like the target file**. A VERBATIM copy of
`exists_inverted_intLift_retraction_localizationAway_integralSystemModel`'s
statement, pasted into such a scratch with `sorry` for its proof, died with
`(deterministic) timeout at isDefEq` after 2 minutes at **five times** the default
heartbeat budget — while that same statement compiles inside `MoretBailly.lean`
itself. Nothing about the mathematics differs; only the environment does, and the
scratch is the one that is wrong.
The workflow that works: a scratch importing **only the mathlib modules you
need**, with the three or four project `def`s you depend on **copied into it
verbatim** (`integralSystemIdeal`, `IntegralSystemModel`, `integralSystemClass`
were ten lines). Round trip went from *timeouts at 5–10 minutes* to **8 seconds**,
and the ~380 lines developed that way transplanted into the real file **unchanged**.
This is a strengthening, not a restatement, of the rule already recorded above
that a scratch shares neither the target's import surface nor its notation scope:
it does not share its **unification behaviour** either. Budget one final blocking
build of the real module, and expect that build — not the scratch — to be the
thing that can still surprise you.
