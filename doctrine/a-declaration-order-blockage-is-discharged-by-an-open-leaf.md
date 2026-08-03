## A DECLARATION-ORDER BLOCKAGE IS DISCHARGED BY AN OPEN LEAF ABOVE, NOT BY A RELOCATION

(2026-07-31, `flt-lean-390`, and it closed `exists_x0GenusZeroJMapHauptmodul`.) A leaf whose
proof needs a theorem declared THOUSANDS OF LINES BELOW it reads as a restructuring job, and
`X0.lean`'s own docstrings said so twice: hoist the minimal closure, or split the `j`-theory
into its own module. Both are large edits to an 81 000-line file with a dozen concurrent
editors, so both stayed undone for days.

The cheap third option is to look for an **open leaf declared ABOVE you that PRODUCES the same
structure**. Here `exists_jSection` (`Nonempty IsJSection`, PROVEN) sits at line 27631 and is
unreachable; `exists_jSection_algClosModel` sits at 16010, is a `sorry`, and its existential
hands over an `IsJSection` — which is all the proof needed. Fifteen lines of `exists_jMap`
replayed against it, and the blockage is gone with nothing moved.

**The objection, and the accounting that answers it.** Citing a `sorry` to discharge a half that
is not open mathematics looks like trading one leaf for two. Check whether that leaf ALREADY has
consumers in your cone: `exists_jSection_algClosModel` had three, so the citation adds **no new
`sorryAx` edge** and the transitive cone is unchanged. The direct-leaf delta is then whatever
genuinely new leaf you cut, and nothing else. If the leaf has no other consumer the trade is
real and you should say so — but check before assuming it.

Two things this is NOT. It is not "open a local sorried copy of the theorem below" — that
manufactures a phantom leaf, and this file warns against it in those words. And it does not
retire the restructuring: the hoist or the module split is still worth doing, now for
elaboration time rather than to unblock a proof.

Generalises past this file: **before pricing a hoist, grep the region ABOVE you for a leaf whose
conclusion is `∃ x : <the structure you need>, …`.** Existential leaves are usually stated to be
consumed exactly once, so nobody thinks of them as a source of the structure they carry.

