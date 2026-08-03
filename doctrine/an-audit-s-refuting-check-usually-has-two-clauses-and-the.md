## AN AUDIT'S REFUTING CHECK USUALLY HAS TWO CLAUSES, AND THE SECOND IS ABOUT THE **CONSUMERS**
(2026-07-31, `flt-lean-168`, on `exists_x0JReductionDatum_cuspInjective` in
`ModularCurve/X0.lean` — a leaf four audits had recorded as unsplittable.)
This file already says to RUN the refuting check an audit prescribes. There is a
sharper version, because these checks are routinely a disjunction and the two
halves are not equally easy to look at:
* the FIRST clause is always about the blocker itself — *"a declaration of
  `SpecLoc` (or of `IsX0JNeronDatum`) ABOVE this point"*. It is one grep, it is
  the one every reader runs, and for a declaration-order block it essentially
  never fires, because the blocker is where it is for a reason;
* the SECOND clause is about who CONSUMES the thing that cannot move — here
  *"any consumer-free route from `y0HasNoRationalPoint_prime` to the
  prime-square and semiprime nodes"*. Nobody ran it, three times, over four
  days.
It fired. `y0HasNoRationalPoint_prime`'s only CODE consumers were at the very
END of the file, below the integral-model subsection; every occurrence between
the leaf and that subsection was docstring prose. So the entire cluster — six
declarations plus its two consumers, 673 lines — could be relocated 46 000 lines
down in one verbatim move, and the leaf restated over the PINNED
`IsX0JNeronDatum` instead of over an unpinned `IsX0JReductionAt`. Frontier
`1 → 1`; what left the leaf is the integral-model existence it had been
re-demanding (`exists_x0JNeronDatum` is PROVEN), and what is left is Mazur.
**The audits' own account of the second clause was FACTUALLY STALE**, and that
is the part to expect: they asserted the consumer "is consumed further up this
very section by `cuspidal_x0_isogenyPrimeSq` and by the semiprime nodes", and a
stale docstring elsewhere in the same file even said the declaration sat "2200
lines BELOW" a point it is 80 000 lines above. **A consumer claim in a docstring
is a measurement, and measurements in this tree rot at the rate the file is
reorganised.** Re-derive it — comment-stripped, and classify every hit as CODE
or PROSE before counting.
**The cost of a relocation is set by the CONSUMERS of the moved block, not by
its size or by the distance.** Ask, in this order:
1. does the block use anything in the region it jumps? — `./flt-hoistcheck.py
   <file> --block A B --to L`, seconds, and it handles both directions;
2. does the jumped region use anything the block declares? — hoistcheck does
   NOT answer this; grep each declared name and classify code vs prose;
3. is the destination at the same scope? — walk `namespace`/`section`/`end` with
   comments MASKED. In this file a naive walk drifts, because prose lines begin
   `section …` and `end …` at column 0 inside docstrings; the robust check is to
   list the column-0 scope lines in the jumped region and confirm every genuine
   opener closes inside it.
**Then move it as a PURE PERMUTATION and prove that it is one**, in its own
commit, with no content edit anywhere: `git show HEAD:<path> | sort` and
`sort <path>` must differ nowhere, and the line count must be unchanged. That
receipt is what lets a merge conflict be resolved by RE-APPLYING the move to the
merged text rather than by merging 900 lines of relocation. Do the restatement
in the NEXT commit.
Two mechanical notes from the same move:
* **take one LEADING blank line into each block** and none trailing; then both
  seams close up with no doubled blank and no missing one, and the multiset
  receipt still holds;
* **a scratch that `public import`s the target verifies the restatement in 9
  seconds** against a 35-minute build of the file — extract the new
  declarations from the real file by line range and `sed` their names to a
  throwaway prefix, so what you verify is the characters you are committing and
  not a hand-retyped copy.
