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

