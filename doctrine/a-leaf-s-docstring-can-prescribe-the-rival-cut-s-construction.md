## A LEAF'S DOCSTRING CAN PRESCRIBE THE RIVAL CUT'S CONSTRUCTION BY NAME — GREP THE FILE FOR THE CONSTRUCTION BEFORE BUILDING IT
(2026-08-02, `flt-lean-34`, `exists_valuationSubring_arithFrob_of_heightOneSpectrum`
in `Modularity/TateModule.lean`.)  The duplicate-cut sections above give the
shapes and `tools/merge/dupstmt.py` for finding them.  This one was invisible to
all of it, and the thing that gave it away costs one `grep`.
The node "a Frobenius-equivariant place of `F̄` above `w`" was cut TWICE, one day
apart, and a merge kept both — in the SAME FILE, 300 lines apart:
* **Cut A (2026-07-30)**: `exists_valuationSubring_arithFrob_of_heightOneSpectrum`
  (produce `V`, `gV`, `hcentre`, `hw`, the Galois clause, the congruence) plus
  `exists_residueField_ringHom_of_valuationSubring` (residue field of an
  ARBITRARY such `V`), assembled by `exists_localRing_arithFrob_of_heightOneSpectrum`.
* **Cut B (2026-07-31)**: `placeAbove` / `frobAbove` / `frobRestrict` /
  `algebraMap_mem_placeAbove` — all PROVEN — plus the single residual leaf
  `exists_residueHom_placeAbove`, assembled by `exists_frobEquivariant_placeAbove`.
**Cut A's assembly has ZERO consumers.**  Cut B's is consumed by
`exists_finset_abelianReductionDatum_of_mult`.  So Cut A contributed TWO dead
leaves to the frontier, and the cluster drew THREE dispatches — `flt-lean-33` at
Cut B's live leaf, `flt-lean-332` and `flt-lean-34` at Cut A's dead ones.  **Two
agent-runs out of three were spent on leaves nothing reaches.**
**WHY EVERY EXISTING INSTRUMENT WAS SILENT.**  The two cuts share no identifier:
Cut A says `ValuationSubring`, `gV`, `hcentre`; Cut B says `placeAbove`,
`frobRestrict`, `algebraMap_mem_placeAbove`.  So `check-dup` and `xdup.py` (name
based) see nothing, and `dupstmt.py` sees nothing either — the two statements are
not alpha-variants, they are DIFFERENT PACKAGINGS of one theorem, one existential
over an abstract `V` and one over a named `def`.  Every frontier scan counted two
honest leaves; `own.py` and `leafstat.py` correctly reported both unowned and
open.
**THE TELL, AND IT IS THE TRANSFERABLE PART: the dead leaf's own docstring
PRESCRIBES the live cut's construction, by name.**  Cut A's docstring says
> put `V := L ⁻¹' (localValuationSubring w)`
and carries a "VERIFIED STARTING POINT" code fragment which is, character for
character, the body of Cut B's `placeAbove`.  The author wrote that paragraph,
then went and built it 450 lines EARLIER as a rival cut, and never came back to
close the leaf.  So:
> **When a leaf's docstring tells you what to construct, grep the file for that
> construction before you construct it.**  Grep the CONSTRUCTION — `comap`,
> `localValuationSubring`, the defining expression — not the leaf's own
> vocabulary, which by construction the rival does not share.
Here `grep -n 'localValuationSubring' <the file>` returns `placeAbove` in one
line, three hundred lines above the leaf.  That is cheaper than every scan in
`tools/merge/` and it is the only thing that finds this shape.
**THE RESOLUTION, and it follows the standing rule rather than improvising.**
Cut B wins on both tie-breaks: it owes ONE leaf where Cut A owes two, and its
leaf is about a single explicit ring where Cut A's quantifies over an arbitrary
one — strictly stronger, strictly harder, and needed by nothing.  So **close your
own leaf by DELEGATION to the winner and do not delete the sibling**: here Cut A's
target is eight lines over `exists_residueHom_placeAbove` (`hw` is
`IsLocalRing.mem_maximalIdeal` + `mem_nonunits_iff` chained with the `π z = 0 ↔
¬ IsUnit z` clause; the congruence is `map_sub`/`map_pow` plus `hσ`), and it adds
**no `sorryAx` edge**, because the winner's leaf is already in the cone.
* **The proof IS the receipt.**  "These two cuts are duplicates" is prose; a
  derivation of one from the other is machine-checked, and it is what lets
  whoever performs the deletion do it without re-deriving the mathematics.  Prove
  first, recommend the deletion second.
* **Do not re-point the dead assembly — check declaration order first.**  The
  obvious tidy-up (make `exists_localRing_arithFrob_of_heightOneSpectrum` go
  through `exists_frobEquivariant_placeAbove`, orphaning the second dead leaf) is
  ILLEGAL here: the live assembly is declared ~200 lines BELOW the dead one.
  Deleting the dead component is cheaper than relocating it, and loses nothing.
