## A LEAF WHOSE CONCLUSION IS A BUNDLED CLASS IS ONE LEAF PER FIELD — UNFOLD IT BEFORE PRICING
(2026-08-02, `flt-lean-196`, `isProper_relPicIdentityComponent` in
`ModularCurve/RelativePicard.lean`.)  That leaf was cut the previous day with a
three-screen docstring pricing it at BLR 9.4 — the valuative criterion for line
bundles on a relative curve — and a FAITHFULNESS audit establishing that its
hypotheses pin `J = Pic⁰`.  Both were right.  **Two thirds of it were free**, and
the check that finds that costs one `grep` of mathlib:
    class IsProper : Prop extends IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f
`LocallyOfFiniteType jstr` is the already-present `Smooth jstr`, through mathlib's
`Smooth → LocallyOfFinitePresentation → LocallyOfFiniteType` instances.
`IsSeparated jstr` is the already-present `IsSeparated pstr` plus the injectivity
clause, through `isSeparated_of_mono` and stability under composition.  Only
`UniversallyClosed` is BLR.  The residue is now a leaf that says exactly the one
classical thing, and the count did not move (`1 → 1`).
**The generalisable check, and it applies to every conclusion in this tree that
is a mathlib typeclass rather than an equation:** open the class definition and
read its `extends` list / field list, then try to discharge each component
SEPARATELY from the hypotheses the leaf already carries.  A leaf is priced by
whoever cut it against the hardest component, because that is the one they were
thinking about; the cheap components are invisible in the docstring precisely
because they were never the point.  Same family as *A LEAF WHOSE CONCLUSION IS AN
ISO OF SHEAVES OF MODULES IS TWO LEAVES* above, with the conjunction supplied by
mathlib instead of by the project.  Candidates worth the grep whenever they are a
CONCLUSION: `IsProper`, `IsFinite`, `IsAffineHom`, `IsClosedImmersion`,
`Smooth`, `IsIntegralHom`, `AbelianSchemeStruct` — each is a conjunction, and this
development's leaves routinely arrive with most of the conjuncts in hand.
**And a docstring's FAITHFULNESS argument can BE the Lean proof of the cheap
components.**  Clause 1 of this leaf's audit read, in prose:
> `_hinclpre` and `_hinj` make `incl` a monomorphism of functors on `Over S`.  By
> Yoneda (evaluate at `T = J`, `g = jstr`, on the tautological point) it is
> `(· ≫ ι)` for a unique `ι : J ⟶ P` over `S`, and `ι` is a monomorphism of
> schemes.
It was written to argue the leaf is TRUE.  It is simultaneously a complete recipe
for the step that closes separatedness, and it is **two lines**, because
`RelPoint f g` is *literally* `{x : T ⟶ A // x ≫ f = g}` — a subtype of
morphisms.  So `ι := (incl J jstr ⟨𝟙 J, _⟩).1` and `ι ≫ pstr = jstr` is *the
subtype property of the point that comes back*; nothing is constructed and
nothing is checked.  `_hinclpre` at `(h := p.1, p := taut)` then gives
`incl T g p = ⟨p.1 ≫ ι, _⟩` on the nose.  This is the standing
*A FUNCTORIAL FAMILY OF POINT-MAPS **IS** A MORPHISM* rule in its cheapest
possible form; the new half is that **the prose which justifies a leaf's
faithfulness is a place to look for its proof**, exactly as
*A DOCSTRING THAT ARGUES TWO LEAVES ARE EQUIVALENT IS A LEAF-MERGE WAITING TO BE
PERFORMED* says for equivalence prose.
**One monicity trap worth copying, since the obvious statement does not typecheck
directly.**  `_hinj` quantifies over relative points over a COMMON base point
`g`, while `Mono ι` quantifies over bare `u v : Z ⟶ J`.  The bridge is that the
base point is recoverable: from `u ≫ ι = v ≫ ι` and `ι ≫ pstr = jstr` one gets
`v ≫ jstr = u ≫ jstr`, so `⟨u, rfl⟩` and `⟨v, _⟩` are both points over
`u ≫ jstr` and `_hinj` applies.  Take `g := u ≫ jstr`, never `g := v ≫ jstr`.
**Do NOT drop the hypotheses the cheap components leave idle.**  Four of this
leaf's hypotheses (`_hequiv`, `_haj`, `_hajpre`, `_hajbase`) are untouched by the
assembly, and deleting them from the residue would have STRENGTHENED it — and
broken it as a target, because they are what make `aj` the Abel–Jacobi map rather
than an arbitrary function, without which clause 4 of the faithfulness argument
(the step that upgrades "`J` is *some* abelian subvariety" to "`J` IS `Pic⁰`") is
satisfied by `aj :=` the constant zero point.  Forward the whole binder list to
the residue; it costs the caller nothing and it cannot make the leaf false.
**Two bookkeeping riders, both of which this change needed.**  Keep the proven
declaration's signature BYTE-IDENTICAL if you can — the project's "underscores
come off when the leaf is proven" tell is worth less than a signature that cannot
be split across a merge boundary in a file with concurrent editors — and say in
the docstring that you did it on purpose.  And a recut like this is invisible to
every count, so print the receipt in the commit:
    git diff -- <file> | grep -E '^[+-].*\bsorry\b'     # one `-`, one `+`
    # plus: comment-stripped sorry-token count HEAD vs worktree, and the
    # compiler's own `declaration uses 'sorry'` set, all three agreeing
Here that was `13 = 13 = 13`, with `isProper_relPicIdentityComponent` gone from
the warning set and `universallyClosed_relPicIdentityComponent` in it.
**Import cost can decide where a cut stops, and that is a legitimate reason to
stop.**  Mathlib factors the residue further —
`UniversallyClosed.of_valuativeCriterion [QuasiCompact f] (ValuativeCriterion.Existence f)`
— into two leaves from two different chapters, which is the honest split.  It was
NOT taken, because `ValuativeCriterion` is not in this module's import cone and
`ModularCurve/X0.lean` is downstream, so the edge costs a rebuild of the largest
cone in the tree for a statement nobody can discharge yet.  Record the split, the
lemma name and the import in the residue's docstring so the next owner gets it
for free, and let them pay the rebuild when they can also use it.
**AND THE CONSUMER SCAN THAT SHOULD HAVE COME FIRST: IT MUST BE A FIXPOINT, NOT
ONE HOP.**  The target's own consumer grep came back positive — `exists_relPicZeroSubfunctor`
calls it — so the leaf looked live and the work started.  It is not: chasing the
chain ONE MORE HOP shows `exists_relPicZeroSubfunctor` has exactly one code
occurrence in `Fermat/`, its own declaration.  This file carries **two rival cuts
of `exists_relPicZeroSubgroup`**, both landed by a clean merge and both correct
when written — the 2026-07-30 `relPicZeroGroupScheme` pair, which that theorem's
PROOF BODY calls, and the 2026-07-31 `relPicIdentityComponent` pair, whose
assembly nothing calls — so the file owes the SAME two obligations twice, four
leaves where two would do.  Every instrument reports four honest open leaves.
Two things follow, and the second is what turned a wasted run into a real one:
* **stop chasing only when you reach a declaration in the root cone**, or a
  `sorry`-free consumer that has one.  "My target has a consumer" is one hop and
  proves nothing; the doctrine's `#print axioms` check on the row's PUBLIC
  theorem is the version that cannot be short-circuited.
* **when a cut applies to a leaf on a dead branch, check whether the LIVE rival
  has the same shape — it usually does, because the two cuts are cuts of one
  node.**  Here `isProper_of_relPicZeroGroupScheme` bundles the same clauses
  inside `RelGroupSchemeStruct` (which carries `smooth`) and `IsRelPicZeroIncl`
  (whose first and fourth conjuncts are the injectivity and naturality the Yoneda
  step needs), so the identical proof transplanted with three lines changed and
  the LIVE properness leaf closed too.  Do both: they are interchangeable, so
  whichever cluster the merge worker keeps, the work lands.
Do NOT delete the dead cluster on your own initiative — choosing between two
rival cuts is an author's decision and the loser may have a live owner.  Write
the finding into the section heading where an agent dispatched there will read
it, and put the recommendation in `to_merger`.
