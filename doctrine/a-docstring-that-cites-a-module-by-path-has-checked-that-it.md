## A DOCSTRING THAT CITES A MODULE BY PATH HAS CHECKED THAT IT EXISTS, NOT WHAT IS PROVEN IN IT
(2026-08-02, `flt-lean-224`, closing
`exists_nonconstant_toAbelianScheme_of_one_le_isCurveGenus` in `X0.lean`.)
That leaf's docstring called the missing `K`-rational point *"the only delicate
part of the statement"*, listed the two standard repairs, and for the second one
wrote — in parentheses, as a helpful aside —
> *Weil restriction*: pass to `L := κ(z)` … and push `A_L` down to `K` by
> `Res_{L/K}` (**which this tree carries,
> `Fermat/FLT/Mathlib/AlgebraicGeometry/WeilRestriction.lean`**).
**That module does not merely "carry Weil restriction". It carries the finished
theorem, PROVEN, in exactly the applied form this leaf needs**
(`exists_nonconstant_toAbelianScheme_of_baseChange_relPoint`: a curve which
acquires a nonconstant map to an abelian variety over every extension at which it
acquires a rational point already has one over `K`) — and its own docstring names
this file's Abel–Jacobi node as the consumer it was written for. The leaf sat open
for two days with its whole "delicate part" already discharged one `import` away.
**The failure is specific and it is not the ordinary absence-claim failure.** A
docstring saying *"X is not in the pin"* announces itself as a claim to re-check;
this file already has five sections about that. A docstring that names a module
**by path** announces the opposite — it reads as a check that was RUN, and the
path is evidence the author opened a file. What the author verified was that the
module EXISTS. Nothing in the sentence is false; the inference a reader draws from
it is.
**So: any time a docstring cites a project module by path, `grep -n '^theorem'`
that module before pricing anything it is cited for.** These modules are small
(this one is 300 lines and has three declarations), the grep is seconds, and the
question it answers — *which of these are PROVEN, and is one of them my
statement?* — is not the question the citation answered.
Two riders, both of which decided this task.
* **The check that finds it is a grep for the CONCLUSION'S SHAPE over the whole
  tree, not for your leaf's vocabulary.** `grep -rn 'nonconstant' Fermat/
  --include=*.lean` returned the proven theorem in the first screen. A search for
  the leaf's own words (`Albanese`, `IsCurveGenus`, `Pic⁰`) returns nothing from
  that module, which is named after neither the leaf nor the mathematics it
  supplies.
* **`Fermat/FLT/Mathlib/**` is where an earlier agent's general-purpose work
  lands, filed under the name of the TECHNIQUE rather than the consumer.** Its
  import closure is usually tiny — this one's whole `Fermat`-closure was already
  inside `X0`'s, so the import cost ONE module and could not cycle. **Compute
  that before assuming an import is expensive**; ten lines of Python over the
  `^public import Fermat` lines settles it, and it turned "add a dependency to the
  largest module in the tree" into a decision with no downside.
