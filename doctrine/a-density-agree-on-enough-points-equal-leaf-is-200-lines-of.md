## A DENSITY / "AGREE ON ENOUGH POINTS ⟹ EQUAL" LEAF IS ~200 LINES OF MATHLIB, NOT A THEORY BUILD — and the general lemma is the SPECIAL one's neighbour
(2026-08-02, `flt-lean-237`, hoisting the step-2 density argument of
`exists_commutingHeckeAlbaneseFamily_values` out of `X0.lean` into a reusable module.)
This development is full of leaves of the shape *"two morphisms out of `X` that agree at
every point of some moduli-theoretic family are equal"* — generation of a Jacobian by
differences, density of CM points, `∀ d, aj [d] = …` pins an endomorphism. They read as
needing a theory (Riemann–Roch, generation of `J(ℚ̄)`, a descent along `Spec ℚ̄ ⟶ Spec ℚ`),
and the docstrings that cut them price them that way. **They are an application of
`Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean`, a 2026 file this tree had never
imported, plus about two screens of bridge.**
**THE TRAP IS THAT THE FILE'S HEADLINE LEMMA IS THE SPECIALISED ONE.**
`AlgebraicGeometry.ext_of_apply_eq` is exactly the wanted statement, is what the file's
module docstring advertises, and demands an **ALGEBRAICALLY CLOSED BASE** — so over
`Spec ℚ` it costs a base change to `Spec ℚ̄` and a descent back, which is where the plan's
"faithfully flat for the descent" input was going. Its neighbour
`AlgebraicGeometry.ext_of_fromSpecResidueField_eq` (in `Morphisms/Separated.lean`) is
stated over an **ARBITRARY** base and costs neither; it merely asks for agreement after
`X.fromSpecResidueField x` instead of after a `K`-point. This is the standing
"MATHLIB OFTEN STATES THE SAME LEMMA TWICE" rule in its most expensive form — the two are
in *different files*, so reading the section around the one you found does not surface it,
and the specialised one is the one every consumer cites.
**THE BRIDGE, now `Fermat/FLT/Mathlib/AlgebraicGeometry/DenseFieldPoints.lean`**, and
worth knowing because every step is one mathlib name:
* `K`-point ⟹ residue-field point: `Scheme.SpecToEquivOfField` factors `p` as
  `Spec.map φ ≫ fromSpecResidueField x` **on the nose** (that direction of the equivalence
  is `rfl`), `Spec.map φ` is dominant for a map of FIELDS (both spectra are points), and
  `ext_of_isDominant_of_isSeparated` cancels it. There is no `IsDominant (Spec.map φ)`
  instance at this pin — supply it.
* a `K`-point over every CLOSED point, for `K` algebraically closed over the base field
  `F`: `{y}` closed makes `Y.fromSpecResidueField y` a CLOSED IMMERSION
  (`isClosed_singleton_iff_isClosedImmersion`), so `Spec κ(y) ⟶ Y ⟶ Spec F` is locally of
  finite type into a Jacobson scheme, hence **FINITE**
  (`isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`, `@[stacks 01TB]`) — **that is where
  Zariski's lemma is spent, and it is spent inside mathlib.** Then integral ⟹ algebraic ⟹
  `IsAlgClosed.lift`.
* density of the closed points: `LocallyOfFiniteType.jacobsonSpace` then
  `Topology.closure_closedPoints`. A nonempty OPEN of an irreducible `X` is dense
  (`IsOpen.dense`), and continuity moves a dense subset of the open onto a dense subset of
  `X` (`image_closure_subset_closure_image` — `range f = f '' closure S ⊆ closure (f '' S)`).
* `IsReduced X` and `IrreducibleSpace X` both come from one call to this tree's
  `isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`.
**THE `F`-ALGEBRA STRUCTURE ON `κ(y)` IS THE ONE FIDDLY STEP AND IT HAS ONE RIGHT ANSWER:**
take it from `Spec.preimage (Y.fromSpecResidueField y ≫ str)`, i.e. through full
faithfulness of `Spec`, and from nothing else. Any other route (a chart, a hand-built
`algebraMap`) gives a second `Algebra F κ(y)` instance and the `IsScalarTower` that
`IsAlgClosed.lift` needs silently fails to synthesize.
**AND A DENSE-OPEN PACKAGING IS THE RIGHT SHAPE WHEN THE CONSUMER'S POINTS ARE MODULI
POINTS** — *"`u = v` as soon as they agree after every `K`-point of a NONEMPTY OPEN
`Y ⊆ X`"*, so that the consumer owes only "my moduli points are the `K`-points of `Y`",
which in this tree is one call to
`IsCoarseModuliY0.exists_gamma0Datum_of_algClosPoint`. `Nonempty Y` is load-bearing there —
with `Y = ∅` the hypothesis is vacuous and the conclusion false. But a consumer whose
clause already ranges over ALL `K`-points of `X` (which is what the `X0.lean` cut of
2026-08-01 chose) does NOT need it, and then the packaging has no consumer and must not be
committed. See the note in `DenseFieldPoints.lean` for where the green text is recoverable
from.
### THE COST OF SKIPPING THE RIVAL-CUT CHECK, measured on this very task
**I proved this, committed it green, and then had to throw the `X0.lean` half away**,
because `flt-lean-182` had cut the same leaf a day earlier, better, and my task prompt was
the entry `queue2` itself marks as SUPERSEDED. The prompt's own instruction — check
`merger` — was run and passed, because the rival was on neither `main` nor `merger`: it was
one commit on an unmerged worktree branch. **`git show merger:<file>` is not the whole
check.** The two commands that would have found it in ten seconds, and that belong before
the first edit on any task naming a leaf in a hot file:
    grep -n '<your target>' ~/.flt-loop/queue1 ~/.flt-loop/queue2
    for b in $(git branch --format='%(refname:short)'); do \
      git show "$b:<the file>" 2>/dev/null | grep -q '<your target>' && echo "$b"; done
The queue grep is the sharper of the two here: the superseding entry said in as many words
*"THIS SUPERSEDES the older queue entry beginning …"*, quoting my prompt's first line.
**And the reconciliation, once found, is the one CLAUDE.md already prescribes: ADOPT THE
RIVAL'S SPLIT POINT.** Merge its branch, resolve the contested region wholesale to its side,
and contribute only what it lacks — here a general module it had inlined in bespoke form.
Keeping the STATEMENT byte-identical and replacing only the BODY leaves the merge worker one
hunk with nothing semantic to decide. Judge the two cuts by **what is LEFT in the leaf**:
182's residual had shed the junk arities, the points-to-morphisms passage and the density,
while mine had shed only the density, so 182's won and the count (`101 → 101`) said nothing.
### Two mechanical notes measured on the same run
* **A hand-rolled `namespace`/`end` stack walk over an 119 000-line file of this tree
  returns garbage** — mine reported an EMPTY stack for a file every declaration of which is
  in `Fermat`, even with block comments masked, because the prose contains `end …` at column
  0. CLAUDE.md already says to ask the compiler instead; the concrete cheapest form is a
  two-line scratch that `public import`s the target and `#check @Fermat.someName`, which
  against the built olean answers in **seconds** and also tells you every name you were
  planning to use is really in scope.
* **`IsEmpty.false` is `∀ a, False`, not `¬T`**, so `absurd x (h : IsEmpty T).false` is an
  application type mismatch. Write `((h.false x)).elim`.
