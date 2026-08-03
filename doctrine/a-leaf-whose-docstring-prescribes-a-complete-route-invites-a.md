## A LEAF WHOSE DOCSTRING PRESCRIBES A COMPLETE ROUTE INVITES A SECOND AGENT TO EXECUTE IT UNDER A NEW NAME
(2026-08-01, `flt-lean-85`, `HardlyRamified/ModThree.lean`.) The duplicate-cut sections in this
file all describe two agents cutting one PARENT blind. There is a commoner and cheaper way to
manufacture the same defect, and this development's docstring style causes it: **a leaf whose
docstring writes out a complete, correct, executable route gets its route executed — into a NEW
declaration — while the leaf that asked for it stays open.**
`isHopfIdeal_nilradical_of_finite_hopf_of_perfectField` was cut 2026-07-30 with three screens of
docstring naming its route exactly: `A ⧸ nil A` is étale, so `A_red ⊗_k A_red` is étale hence
reduced, so `(π ⊗ π) ∘ Δ` kills the nilradical, which is the coideal condition. On 2026-07-31
somebody built the counit-idempotent block ~190 lines ABOVE it and, inside that block, proved
`isHopfIdeal_nilradical` — **that route, verbatim, under a different name.** The leaf was never
touched. It stayed open, became consumerless when the parent was re-proven over the new block,
and drew a dispatch two days later.
**Two rules, one for each side.**
* *If you EXECUTE a leaf's prescribed route, close THAT leaf.* Landing the result under a new
  name is not a smaller edit — it is the same edit plus a permanent duplicate, and the duplicate
  is invisible to every instrument (it emits an honest `declaration uses 'sorry'`, its name is
  unique, and `own.py` correctly reports it unowned).
* *If you ARRIVE at a leaf, read the region between it and its parent for a theorem whose PROOF
  is your docstring's ROUTE.* Not whose name resembles yours, and not whose statement you can
  grep for — the route. Here the leaf's docstring and the proven theorem's proof are the same
  four steps in the same order, and that was the only textual link between them.
**AND THE STATEMENTS CAN SHARE NO SPELLING AT ALL, WHICH IS WHY `dupstmt.py` MISSED IT.** The
pair here is
`Ideal.IsHopfIdeal k (nilradical A)` against `(nilradical A).IsHopfIdeal k` — the SAME
proposition. Mathlib declares the class under `variable (R) in`, so its base argument is FIRST
in application order and LAST in dot notation, and the ring argument is implicit. Two spellings
of one proposition therefore share neither their head token nor their argument order, and no
normalisation of binder names, grouping or bracketing brings them together. **When checking
whether two statements are the same, elaborate them** — `example : <A> = <B> := rfl` for
`Prop`-valued applications, or just `#check` both and compare the pretty-printed types — rather
than diffing the source. It is seconds against a scan that cannot see it.
Bookkeeping note, since it is what the delta looks like: deleting the duplicate took ModThree
from 14 sorried declarations to 13 and proved nothing. That is still worth doing — a dead leaf
draws a dispatch every time the queue is regenerated, and this one had drawn at least one.
