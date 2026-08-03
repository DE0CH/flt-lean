## A BLOCK MOVE WHOSE END IS OFF BY ONE SWALLOWS THE NEXT DOCSTRING'S OPENER — AND EVERY RECEIPT STILL PASSES
(2026-08-02, `flt-lean-334`, caught by accident three edits later.) The
pure-move receipt this file already prescribes — sorted line multiset unchanged
— is exact for *"did any line change"* and says NOTHING about *"did the block
end where the declaration ends"*. Take one line too many and the block carries
away the `/--` OPENER of the next declaration's docstring. Then:
* the line multiset is unchanged, so `blockmove.py` writes and `sort`+`diff`
  agrees;
* the comment depth still returns to zero, because the orphaned opener at the
  DESTINATION runs away into the terminator of whatever docstring follows it
  there, and the orphaned BODY at the source is absorbed by the docstring above
  it. So `tools/merge/commentscan.py` is silent and
  `tools/merge/parsecheck.py` says `delimiters OK`;
* `git diff --stat` reads `N insertions(+), N deletions(-)`, the pure-move
  signature;
* and the file still PARSES, so a build does not necessarily fail either — it
  silently loses every declaration the runaway comment now covers.
That is the runaway-doc-comment defect this project already knows from merges,
manufactured by a *relocation* instead, with all four of its usual detectors
answering "fine". Here it swallowed `IsAdditiveOn`'s docstring opener and would
have commented out the whole `IsNIsogenyPair` structure.
**The check that does work costs four `sed`s and must be run BEFORE the move:
print the first and last line of every block, and the two lines straddling the
destination.** A block ends at the last line of the declaration BODY (plus at
most the blank after it) — not at "the line before the next `/--`", which is what
an off-by-one from a `sed -n 'A,Bp'` window looks like. And after the move, grep
the file for a `-/` line whose next non-blank line opens another doc comment, and
for a `/--` line whose next line is another `/--`:
    awk 'prev ~ /^\/--/ && /^\/--/ {print NR": doc opener directly after doc opener"} {prev=$0}' F.lean
The second form is the tell that fires here, and it is one command.
