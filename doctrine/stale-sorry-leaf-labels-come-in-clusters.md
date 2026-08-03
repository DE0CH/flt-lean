## stale sorry leaf labels come in clusters

(Cut verbatim out of CLAUDE.md's `THE GOAL: fully formalize Fermat's Last Theorem, no sorry, n` section at the 2026-08-03 doctrine split; nothing reworded.)

**They come in CLUSTERS, and the sweep is cheap and compiler-validated**
(2026-07-31, `MoretBailly.lean`). Six of the seven declarations in that file's
Bertini cluster carried a `(sorry leaf, …)` / `(sorry node, …)` header while
being PROVEN — including two whose OWN docstring said `CLOSED` or `PROVEN`
further down, so the header contradicted its own body text. The cause is
structural rather than careless: a header is written when the leaf is cut and
nobody edits it when the leaf closes, whereas the closing agent naturally
appends a note at the END. So expect the whole neighbourhood of any leaf you
touch to be mislabelled, not just one declaration.

The check costs nothing beyond a build you were running anyway:

* take the build's `declaration uses 'sorry'` warning LINE NUMBERS for the file
  (that is the ground truth — a source `grep` is not);
* list the file's declaration start lines and attribute each warning to the
  declaration it falls in;
* for every declaration NOT in that set, look at the FIRST THREE LINES of its
  docstring only, and flag `(sorry leaf` / `(sorry node`.

Restricting to the opening paragraph is what makes it usable: scanning whole
docstrings gave 40 hits in one file, almost all of them cross-references to
*other* leaves ("glue over the sorry leaf `X` below"), and the opening-paragraph
form cut it to 16 with no false negatives in the cluster checked by hand.

**And a 50k-line file's own doctrine is NOT consistent with itself.** The same
file argued BOTH ways about the same cut, ~800 lines apart, each honestly and
each correct when written: `exists_bertiniConnectedLocus_isAlgClosed`'s
2026-07-27 correction says the general section must be proved IRREDUCIBLE
(because a nonempty open of a merely connected space need not be connected),
while `exists_bertiniConnectedLocus_of_affine_geometricallyIrreducible`'s "WHY
CONNECTEDNESS AND NOT IRREDUCIBILITY" paragraph says connectedness is the
Lefschetz half and the right target. Both survive: the second's upgrade needs
the section to be SMOOTH, which the first does not have in hand. So before
taking a cut that one docstring appears to endorse, **grep the file for the
opposite claim and reconcile the two in writing** — and record the
reconciliation where the cut is made, because the next reader will hit whichever
paragraph is nearer.

