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

