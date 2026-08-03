## A leaf can be open for NO MATHEMATICAL REASON — measure the hoist instead of fearing it

(2026-07-31, `exists_jSection_algClosModel` in `X0.lean`.) That leaf's own audit had
established, correctly and a day earlier, that its mathematics was **already proven and
merely discarded**: `exists_jSectionOnAffine`'s internal `H` is stated at an arbitrary
base ring and its last line throws that generality away by instantiating at `R = ℚ`.
The leaf was open because every ingredient was declared **nine thousand lines below it**,
and a leaf needs no producer while a theorem does.

The audit then priced the two repairs — hoist the machinery up, or split the `j`-theory
into its own module — and both prices were guesses. Measured, they were not close:

* **The hoist was free.** The block is 2966 lines and jumps 178 declarations; a
  comment-stripped token scan says it uses **none** of them, and its only outside input
  is declared near the top of the file. `flt-hoistcheck.py` (added with this note) is
  that scan: `./flt-hoistcheck.py <file> --block A B --to L`, two seconds, both
  directions. It also lists what it cannot see — **anonymous `instance :` declarations**
  in the jumped region, and any `namespace`/`section` the move would carry the block
  into or out of.
* **The module split was the expensive one**, which is the opposite of how it reads.
  The `j`-theory consumes `Gamma0Datum`, `RelPoint` and `AbelianSchemeStruct` from the
  first fifteen thousand lines of the same file, so extracting it means splitting
  `X0.lean` into THREE modules, not two — and a three-way split of a file with a dozen
  concurrent editors is far more merge-hostile than an in-file move.

So: **when a leaf's docstring says "this is blocked by declaration order", run the scan
before believing either cost estimate.** The general rule the two directions share — a
block may be relocated iff it uses nothing declared in the region it jumps — is cheap to
check and almost never checked.

Two riders learned in the same repair:

* **Prefer moving the MACHINERY to moving the CONSUMERS.** The consumer cluster here
  fanned out into Mazur-torsion certificates through `y0HasNoRationalPoint_of_not_stableCyclic`,
  so moving it down would have dragged thousands of unrelated lines; the machinery had
  exactly one consumer left behind (`exists_jLine`, which needs `IsJLine` from the region
  jumped over, and is why the block stops where it does).
* **Strengthen the CONCLUSION, never the structure.** `IsJSection` and
  `IsJSectionOnAffine` were left untouched and their two `Nonempty` producers now return
  the witness *with* the general-base pinning, so no consumer of a structure field was
  disturbed and the whole edit outside the move was two extra proof bullets and two
  `obtain ⟨·⟩ → obtain ⟨·, ·⟩`. A `rw` will not see through a structure LITERAL's
  projection (`{ jt := jtr.jt, … }.jt g d`); `show` will, the projection being `rfl`.

