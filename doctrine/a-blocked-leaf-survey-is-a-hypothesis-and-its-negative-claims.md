## A BLOCKED-LEAF SURVEY IS A HYPOTHESIS, AND ITS *NEGATIVE* CLAIMS ARE THE ONES THAT ROT

(2026-07-31.) A leaf that resists often acquires a docstring survey — "here is what
blocks this, here is what the tree does not have". Those surveys are worth their
weight; the one on `exists_commutingHeckeAlbaneseFamilyGamma1` correctly identified
the blocking object and correctly killed three cheap witnesses. But it also said
closing the leaf needs "the density statement … plus a separatedness step — and
neither is in the tree", and **the separatedness step was already in the tree**: it
is the UNIQUENESS half of the structure's own universal property. Eleven lines,
verified green in a scratch module the same day.

The pattern generalises past that one leaf. **Universal properties in this
development are stated with `∃!`** — `IsJacobianOf.universal` is `∃! u, …`, and so
are its neighbours — and an `∃!` IS a rigidity lemma: two morphisms satisfying the
same universal datum are equal, for free, no geometry. So **before writing (or
dispatching at) a rigidity, separatedness, or "morphisms agreeing on points are
equal" leaf, check whether the object you are working over already carries an `∃!`.**
The Yoneda-style helper that converts a hypothesis about the representing morphism
into the universal property's own clause is usually already there too
(`IsJacobianOf.aj_val`).

The asymmetry is the point, and it is the reusable part: a survey's POSITIVE claims
("this is what blocks it", "this witness fails because …") are checked by the person
writing them, because they had to do the work. Its NEGATIVE claims ("the tree does
not have X") are a `grep` that was not run, and they cost a leaf each when wrong —
the same failure shape as [Inventory audits understate what exists] and
[Audits search production, not invariants], now in a third place. Treat "not in the
tree" in a docstring exactly as CLAUDE.md already tells you to treat "still open,
owned elsewhere" in a commit message: **a hypothesis to check, never a fact.**

