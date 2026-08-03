## A LEAF CAN BE CLOSED BY MOVING CODE — the declaration-order leaf class

(2026-07-31, `flt-lean-2`, on `flat_toImage_of_isAdditiveOn` in `X0.lean`.)

A leaf can be **already proven, in the same file, below itself**. Lean elaborates top
to bottom, so the general theorem is unusable at the leaf's position and the leaf gets
`sorry`d, honestly, with a docstring saying so — and then it sits there, because every
prover who reads it correctly concludes there is no mathematics to do and moves on.
This one survived three days and an audit that diagnosed it exactly and declined to act.

**The repair is a relocation, and moving code DOWN is the safe direction**: it cannot
break the moved code's own dependencies, so the ONLY check is whether anything between
the old and the new position consumes the block. That check is cheap, and it is the
whole risk assessment.

Three things this cost, worth knowing in advance:

* **A docstring's call-site list goes stale the moment the block moves.** The audit here
  named "exactly one CODE call site, at line ~66357" — written when the block lived
  1000 lines earlier, and by the time it was read the line number meant nothing and the
  count was wrong (there were three, two of them for a different declaration). Re-derive
  the list against the current file; do not inherit it. A naive `grep` over-reports
  wildly, because in this project most occurrences of a name are prose in docstrings.
* **`refine ⟨?_, h⟩` fails when `h`'s type mentions the hole.** Restructuring the
  consumer to name the object it used to produce as a `refine` hole is the usual shape
  of this repair; use `refine ⟨?_, ?_⟩` with bullets so the first goal assigns the
  metavariable before the second is checked.
* **Structure literals are indentation-sensitive in a way the error does not name.**
  Re-indenting a `{ field := … }` block by one column produces
  `unexpected identifier; expected '}'` plus a bogus "fields missing" list.

**And the payoff is usually bigger than the one leaf.** Moving this block below the
morphism-level group machinery (`addPairHom`, `sqMap`, `pairSquareMap`,
`pairSquareMap_addPair`) put that machinery ABOVE two sibling leaves that had been
stated in terms of it and could not use it. One of the two was proven the same day
purely because it became expressible. So when choosing WHICH side to move, prefer the
move that leaves the remaining leaves with more machinery above them.

