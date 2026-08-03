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

### And its worst variant: CUT × HOIST, where the orphan is DOWNSTREAM of its own consumer

(2026-08-02, `flt-lean-234`, `exists_cubeForms_of_veryAmpleSystem`.) The section above is
`DELETE × REFACTOR`. Replace the deletion by a **hoist** and the same clean merge produces a
strictly worse state, because the orphan is not merely unconsumed — it is *unconsumable*.

Two branches, one node, one day. Branch A CUT `nonempty_cubeModel_of_isAmpleSheaf_cube` into an
embedding half and a forms half, **in `X0.lean`, where the parent then lived**, and re-pointed
the parent at them. Branch B — release 28's cycle repair — HOISTED the parent into a new
upstream module `Modularity/AbelianCubeModel.lean`, taking its **PRE-CUT body**, because that is
what a hoist does: it copies the declaration as it stands on the hoisting branch. Both landed;
they touch different files, so nothing conflicted. Result:

* the parent, upstream, still `sorry` — B silently reverted A's proof of it;
* the two halves, in `X0.lean`, which `public import`s the parent's new home. **No declaration
  in the project can ever reach them**, and no relocation of the parent can fix it, because the
  parent's position is exactly what breaks the import cycle.

**Every instrument reports ordinary work.** Both halves compile; both emit
`declaration uses 'sorry'`; both pass the three-part ownership test; `xdup`/`dupstmt` are silent
(no duplicated name, no duplicated statement); the build is green. The frontier counts THREE
leaves where the mathematics has two — and it counted them for two days, and dispatched me at one.

**The detector is the standing one and it is one command**, so run it before reading the target:

    grep -rn '<target>' --include=*.lean Fermat/     # own decl + docstrings only ⇒ DEAD

**What is new is the second question, and it is what tells you the repair.** When the grep comes
back dead, do NOT stop at "consumerless". Ask *where did my consumer GO* — `git log --oneline`
the file it used to be in, and grep the tree for its name. A consumer that was DELETED means your
leaf is garbage; a consumer that MOVED means your leaf is misplaced, and those have opposite
repairs. Here the parent's new module even documents its own hoist in its header, so the whole
diagnosis was two greps.

**The repair moves the ORPHAN, never the consumer**, and it is cheap because a hoist destination
is by construction upstream of everything the orphan needs. Three things make it auditable:

* **verify the move is verbatim, mechanically.** The destination is upstream of the `abbrev`
  `SpecQ`, so 34 occurrences had to become `(Spec (CommRingCat.of ℚ))` — done with an
  IDENTIFIER-BOUNDARY regex (`(?<![A-Za-z0-9_'.])SpecQ(?![A-Za-z0-9_'])`) so that `ratOfSpecQ`,
  `nonvanishingAt_iff_ratOfSpecQ` and `nonvanishingAt_modUnit_specQ` survive untouched, and then
  REVERSE-substituted and `difflib`-compared against the original 284 lines: identical. That is
  a stronger receipt than reading the diff, and it is the sorted-line-multiset check adapted to a
  move that is not a pure permutation.
* **`git diff -U0 | grep -E '^[+-] *sorry$'`** — here `−3 +2`, which is the whole accounting.
* **grep every moved name for uses outside the block before deleting**, per name, comment-stripped.

**And the payoff is usually a proof, not just a tidy-up.** Once the halves are upstream the parent
is provable over them, and the assembly is small by construction — the halves were cut so that
what remains is bookkeeping. Here: `coords` from `ptSectionValue`, `coords_ne_zero` from
base-point freeness, `injective_of_smul` from the separation clause read contrapositively
(`coords P = c • coords Q` makes every `2×2` minor vanish), and eight fields passed through.
First try, `3 → 2`.

**Two riders.**

* **Say in `to_merger` that the two file edits are ONE edit.** Taking the downstream deletion
  without the upstream insertion loses both leaves outright; taking the insertion without the
  deletion duplicates eight declarations across two modules one of which imports the other. That
  is the class-7 interface split, pre-announced.
* **Moving work upstream buys you the iteration loop for free.** `lake env lean` on the 380-line
  upstream module is **7 seconds**; the same declarations in `X0.lean` cost **419 s** to rebuild
  and are unreachable from a scratch that does not import the giant. The whole apparatus plus the
  assembly was developed at 7 s per round and the one real build was run once, at the end.

