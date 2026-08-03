## A CYCLE-BREAKING HOIST TAKES A STATEMENT AND LEAVES A PROOF — the payload of the cut is stranded DOWNSTREAM, where nothing can ever reach it

(2026-08-02, `flt-lean-228`, on `exists_veryAmpleSystem_of_isAmpleSheaf`.  Repaired;
net **−1** leaf, no mathematics done.)

The hoist sections above are about a MOVE that lands in the wrong place.  This is a
move that lands in the RIGHT place and takes only half of what it needed, and it is
the most expensive shape yet recorded, because the half it drops is a PROOF and
proofs leave no trace when they are replaced by `sorry`.

The sequence, and every step of it is defensible in isolation:

1. `nonempty_cubeModel_of_isAmpleSheaf_cube` is CUT in `X0.lean` into an EMBEDDING
   half and a FORMS half, PROVEN over the two, with ~150 lines of new proven
   apparatus underneath (`ptSectionValue`, `ratOfSpecQ`, the `nonvanishingAt_*`
   family, `SpansSquare`).  Frontier `1 → 2`, correctly reported as a cut.
2. A release discovers an import CYCLE and repairs it by hoisting that parent into a
   new upstream module — exactly the right repair, done for exactly the right reason.
   It carries the parent's **statement** and writes `sorry` for its body.

The result is `1 → 3`: the parent is open again upstream, and the two halves plus
the apparatus sit **downstream of the only declaration that could consume them**, so
no edit anywhere can ever give them a consumer.  Nothing in the tree said so.  Both
halves emit `declaration uses 'sorry'`, both are unowned, both are in the census,
both have careful fresh faithfulness audits, and the release build is green.  A leaf
was dispatched at one of them, which is how it was found.

**THE TELL, and it costs one grep, so run it before reading your target at all:**

    grep -n '<your target>' <the file>          # own decl + docstrings only ⇒ ORPHANED
    grep -rn '<your target>' --include=*.lean Fermat/

Then read your target's docstring for *"cut out of `P`"* and locate `P`.  **If `P` is
in a module that YOURS imports, that is the damage** — a cut cannot run upstream, so
the parent's proof must have been discarded when it moved.  Confirm with
`git log --diff-filter=A` on the new module and `git show <that commit> -- <your
file>` : the removed `theorem P … := by` will still show its assembly proof in the
diff, and `git show <cut-commit>:<your file>` recovers it verbatim.

**THE REPAIR IS THE REST OF THE HOIST, and it is mechanical.**  Move the apparatus
and both halves up beside the parent and paste the recovered assembly back.  Three
things make it cheap and auditable:

* **scratch-test the whole block against the DESTINATION's import cone first** — a
  scratch that `public import`s the destination module and carries the block verbatim
  elaborated in seconds and settled feasibility before any edit.  It also proves the
  block needs no `open` the destination lacks, which is the thing that usually bites;
* **a one-line `abbrev` may have to travel too, and that is fine.**  `SpecQ` is
  declared in `X0.lean`, so the release's hoist had to spell out
  `Spec (CommRingCat.of ℚ)` in the moved statements and said so in the new module's
  header.  Hoisting `SpecQ` as well — same name, same `namespace Fermat`, reached by
  the existing `public import` — makes the rest of the move VERBATIM and changes no
  call site anywhere;
* **the receipt is the line multiset over BOTH files.**  `Counter(before) - Counter(after)`
  and its reverse should list only the breadcrumb notes, the module note, and the
  restored proof.  Here the only line that disappeared was the parent's `  sorry`,
  which is the whole claim in one line of output.

**And say `3 → 2` in the commit, with "no mathematics done".**  A `−1` from a repair
of this kind reads exactly like a closed leaf and is not one.

Corollary for whoever performs the NEXT cycle-breaking hoist: **a declaration you are
about to move is not just its statement.**  Before moving it, read its proof body,
list the names it calls, and check each is in the destination's cone — anything that
is not must move with it or the hoist silently converts a theorem into a leaf and its
inputs into free-floating code.  `git show <sha> -- <file> | grep -A40 '^-theorem <name>'`
shows exactly what you are discarding, and the release that did this can be seen doing
it in its own diff.

