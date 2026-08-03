## A GENERALISING RECUT ORPHANS ITS SPECIAL CASE — AND THE TELL IS AN UNUSED BINDER IN THE CONSUMER
(2026-07-31, `flt-lean-16`, `HardlyRamified/Family.lean`.) The duplicate-cut sections above
are about two branches cutting one node two ways. This is the ONE-branch version, it is
commoner, and it needs no merge accident at all: a recut GENERALISES a leaf — here
`isMultiplicativeType_corner_of_connected_of_cornerLevelOneFlag` (`hflag`/`hconn` on
`G ⧸ cornerIdeal e₀`) was superseded by `isMultiplicativeType_of_connected_of_inertiaLevelOneFlag`
over an abstract `A` — and the author correctly re-points the CONSUMER straight at the new
abstract leaf. The old specialisation is now a strict INSTANCE of the new one, with **no
consumer anywhere in the tree**, and it stays on the frontier for ever.
**Every instrument reports it as ordinary open work, and each is right.** It emits a real
`declaration uses 'sorry'` warning; its name is unique, so `xdup.py` and `dupstmt.py` are
silent (the two statements are not textual variants — one is the other *instantiated*, which
no statement-level scan normalises); `own.py`-style ownership checks correctly say it is
unowned. It had a 60-line docstring with a re-run faithfulness audit, so it read as a
carefully-maintained live node. It drew a dispatch — mine.
**THE DETECTOR IS FREE, BECAUSE IT IS ALREADY IN YOUR BUILD LOG.** The consumer keeps the
PACKAGING arguments it needed only in order to feed the specialised form, and once it calls
the abstract leaf directly they become dead:
    warning: Family.lean:5555:14: Variable name `he₀` is not explicitly referenced.
    warning: Family.lean:5556:5:  Variable name `hε₀` is not explicitly referenced.
An unused-binder warning on a theorem whose own docstring says it is "the ASSEMBLY of
<named specialisation> with <named bridge>" is the tell that it stopped going through that
specialisation. Grep the log for `is not explicitly referenced` and read the docstring of
each declaration it names; that is seconds and it is the only signal that fires here.
**Both docstrings will still describe the chain as running through the orphan**, because
prose is not re-pointed when a proof body is. Here the orphan's docstring said the consumer
"just below is now the ASSEMBLY of this statement", and the consumer's said "see
<the orphan> **just below**" — while the orphan was 120 lines ABOVE it. That stale direction
word is the second free tell, per the standing rule that "above"/"below" is an order
assertion to check.
**THE REPAIR IS NOT DELETION BY DEFAULT.** Prove the orphan as the one-line instance and
**re-point the consumer through it**. That closes the leaf, restores the documented chain,
puts the declaration back in the root cone — a PROVEN declaration nothing reaches is
free-floating, which this project forbids, so proving it and walking away is not an option —
and spends the consumer's dead binders again (155 → 153 warnings here). Deletion is the
alternative; prefer re-pointing when the file has a live concurrent editor, since a deletion
is the higher-merge-risk half of `DELETE × REFACTOR`. Underscore the binders the orphan
itself no longer uses; call sites pass them positionally and do not move.
**AND SAY IN THE COMMIT THAT THE `−1` IS BOOKKEEPING.** No mathematics was done: one
redundant instance of an open leaf stopped being counted separately from it. A frontier
delta of `−1` on a file whose headline citation is still open reads as progress on that
citation and is not.
Corollary for dispatch, measured the same day: all FOUR of that file's sorries were held by
four DISTINCT live agents simultaneously (`flt-lean-131`, `-178`, `-203`, `-16`). Before
widening scope to a neighbouring leaf "while you are in the file", check
`~/.flt-loop/jobs/*.prompt` for its `TARGET:` line — under the Python loop a hot file is
saturated, and the abstract leaf that supersedes yours is exactly the one most likely to
have just been dispatched to somebody else.
