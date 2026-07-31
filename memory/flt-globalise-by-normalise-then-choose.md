---
name: flt-globalise-by-normalise-then-choose
description: To globalise a one-place ultrametric independence argument, normalise the coefficients so one is a unit, then CHOOSE the place where that unit lives — "units at the other places" is never enough
metadata:
  type: project
---

Globalising a local ultrametric argument (one place → a sum over finitely many
places) fails in a way that looks like it should work, and the fix is two moves,
neither of which the local proof suggests. Found 2026-07-31 while proving the
single-place half of Stichtenoth I.4.11(a) in
`Fermat/FLT/ModularCurve/HyperellipticJacobian.lean`; the full write-up is in
`degOf_poleDivisor_le_finrank_of_transcendental`'s docstring.

**The trap.** The local proof separates terms by their order mod `e`. Give the
other places' data "units at `v₀`" — the obvious globalisation — and every term
from every other place lands in the residue class `0 mod e`, the *same* class as
the local `k = 0` group. The classes `k ≥ 1` still separate; the class-`0`
aggregate has no controlled order at all, so the strict-minimum step dies. And
when the local `k ≥ 1` coefficients all vanish there is no contradiction at `v₀`
to be had at all.

**Move 1 — control ORDERS elsewhere, not just nonvanishing.** The family must be
an *approximation*: `ord_{v₀}(b − local target) ≥ e_{v₀}` **and**
`ord_w(b) ≥ e_w` at every other place. That is a CRT/weak-approximation
statement, not a genericity statement, and it is the whole reason approximation
appears in the classical proof.

**Move 2 — NORMALISE, then CHOOSE the place.** Divide the relation by the
extreme coefficient (here `g^{−d}` with `d` the maximum degree over *all*
indices) so every coefficient becomes regular at every place at once and exactly
the extremal ones stay units. Then run the argument at **the place belonging to
an index that attains the extremum** — not at an arbitrary place. That is what
guarantees a term of order `< e` to beat the `≥ e` remainder.

Move 2 is the one with no counterpart in the local proof, and it is why the
globalisation is not a routine induction. The same shape is what makes the
ring-theoretic proof work (`Σ e f = n` via CRT: divide the coefficients by the
largest power of the uniformiser, so one is a unit mod `p`), so expect it
wherever a local-to-global count is being formalised.

Related: [[flt-two-leaves-may-be-one]], [[flt-crude-bound-plus-patch]].
