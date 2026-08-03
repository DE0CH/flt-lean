## A HOIST'S BLOCK RUNS DOCSTRING-TO-DOCSTRING, AND BOTH ENDS BITE

(Same release, and I got each end wrong once in the same 4770-line move.)

`flt-hoistcheck.py` answers whether a block MAY move.  It says nothing about
where the block STARTS and ENDS, and a Lean declaration's block is
`[start of its docstring, line before the start of the NEXT declaration's
docstring]`.  Both off-by-one errors are silent in the multiset receipt — the
move really is a pure permutation — and both are parse errors thousands of lines
from the move:

* **end taken at the next `theorem` line**: that declaration's docstring travels
  with the block and lands wherever the block lands, where a `section` or another
  docstring follows it.  `unexpected token '/--'; expected 'lemma'`.
* **start taken at the `structure`/`theorem` line**: the moved declaration's OWN
  docstring stays behind, immediately above whatever followed the block.  Same
  error, at the source position instead of the destination.

So compute both ends with the same docstring-walk, and after any block move grep
the file for a `-/` line whose next non-blank line opens another doc comment.
`tools/merge/parsecheck.py` does not catch this — the delimiters are balanced.
