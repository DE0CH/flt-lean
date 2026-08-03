## TWO FILES CAN CARRY THE SAME CUT UNDER DIFFERENT NAMES — READ THE CONSUMER'S PROOF, NOT THE LEAF'S NAME
(2026-07-31, `flt-lean-355`.)  `AlgebraicGeometry.mem_smoothLocus_of_comp_of_flat` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothLocusPerfect.lean` and
`Fermat.mem_smoothLocus_of_comp_of_smooth` in
`Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothLocusDescent.lean` are the same theorem,
cut ONE DAY APART into two different files that `X0.lean` `public import`s side by
side.  Both are open, both compile, both pass the three-part ownership test, both are
in the frontier scan.  One is consumed and one is dead.
**Nothing keyed on the leaf's NAME can see this.**  The two names share no component;
the two docstrings cite the same fact under two different Stacks tags (`02VL` and
`036M`); `own.py` and `leafstat.py` both correctly report "unowned, still open" for
each.  This is the sibling of the already-recorded
"[A leaf can name the same theorem in a different vocabulary]" trap, with an extra
twist: here the duplication is across FILES, so even reading the whole enclosing
module does not reveal it.
**The check that does work is one grep, and it is at the CONSUMER:** open the proof
body of the theorem the leaf claims to serve and read which name it actually calls.
    grep -n 'smoothLocus_pairSquareMap_le' -A6 Fermat/FLT/ModularCurve/X0.lean
Two lines of proof term settled it: `Fermat.mem_smoothLocus_of_commSq`, i.e. the
`SmoothLocusDescent` copy.  Then a comment-stripped scan of `Fermat/` for the other
three names returned zero code hits — an OPEN leaf that is also DEAD, the seventh
invisibility class, arrived at through duplication rather than through a dead
consumer.
**And the dead copy was the more GENERAL one, which is why it looked like the real
target.**  It asked only `Flat p` where the live one asks `Smooth p`.  That extra
generality is exactly the unreachable part — see the next section — so the leaf that
read as "the same thing, stated better" was the one nobody could ever close and
nobody needed.  **When two rival cuts differ by a hypothesis, price the DIFFERENCE
before assuming the stronger statement is the one to keep.**
