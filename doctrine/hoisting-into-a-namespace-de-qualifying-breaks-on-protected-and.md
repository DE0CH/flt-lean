## HOISTING *INTO* A NAMESPACE: DE-QUALIFYING BREAKS ON `protected`, AND THE AUTO-GENERATED STRUCTURE `ext` IS PROTECTED
(2026-08-01, `flt-lean-5`, moving the form-to-`ℍ` dictionary from
`FreyCurve/MazurTorsion.lean` into `Mathlib/NumberTheory/BinaryQuadraticForm.lean`.)
A hoist into the namespace that OWNS the vocabulary comes with a mechanical rewrite:
strip the now-redundant qualification, `Fermat.BinaryQuadraticForm.discr → discr` and so
on. That rewrite is correct for ordinary declarations and **silently wrong for
`protected` ones**, because `protected` means precisely *"the short name does not work,
even inside the declaration's own namespace"*. The failure is one line of a 300-line
move, it survives every structural check a relocation is normally given — the block was
byte-identical modulo the rewrite, delimiters balanced, scopes balanced, line multiset
accounted for — and it reports as
    error: Unknown identifier `ext`
for a name that visibly exists and that the SOURCE file was citing successfully as
`Fermat.BinaryQuadraticForm.ext` five minutes earlier. Read as a missing declaration it
sends you hunting for a lost `import` or a bad merge; the cause is the rewrite you just
performed on purpose.
**The specific instance is worth memorising, because this tree is full of structures:
Lean's AUTO-GENERATED `Foo.ext` and `Foo.ext_iff` are `protected`.** So any block using
a structure's extensionality lemma breaks on exactly this move and nothing else does.
Five other names in the same block (`discr`, `discr_act`, `eval`, `act`, and the type
itself) de-qualified without complaint.
**The fix is one qualifier, not the full path**: `BinaryQuadraticForm.ext` resolves,
because Lean tries the current-namespace prefixes and `Fermat.BinaryQuadraticForm` +
`.ext` is an exact full-name match, which is legal for a protected name. Bare `ext` is
not. Leave a one-line comment saying why the qualifier survived, or the next reader
"tidies" it back.
**The check, and it costs one elaboration of the TARGET file alone.** Do not discover
this from the downstream build: the target here elaborates in 52 s while its consumer
`MazurTorsion.lean` is ~25 min and the full `lake build` of the consumer is far more.
So the order for any hoist is *(1) seed `.lake` from the release snapshot, (2)
`lake env lean` the DESTINATION file by itself and get it to `EXIT=0`, (3) only then
build the consumer*. Step 2 catches every de-qualification error, every missing `open`,
and every collision, because all of them are internal to the destination.
Two riders from the same move, both cheap and both worth doing every time:
* **The `open`s do not transfer — recompute them at the destination.** The source
  section carried `open Fermat.BinaryQuadraticForm.Heegner` and `open scoped
  MatrixGroups`; the destination needed `open Heegner` (the namespace is now an ancestor)
  and still needed `MatrixGroups` for the `SL(2, ℤ)` notation. Conversely the SURVIVORS
  stopped needing `MatrixGroups` — nothing left behind used the notation — so it was
  deleted rather than left as dead scaffolding. Grep both sides for what each half
  actually uses; do not copy the header.
* **A pure relocation must show `sorry` tokens moving, not changing.** Comment-stripped
  counts went `BinaryQuadraticForm 6 → 7` and `MazurTorsion 37 → 36`. Two numbers, one
  command, and they are the receipt that no leaf was created or closed — which is the
  claim a relocation commit is actually making, and the one a reviewer cannot get from
  the diff.
