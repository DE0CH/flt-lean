---
name: flt-proven-over-a-sorry-is-not-proven
description: A route audit that prices a bridge by checking the target theorem is PROVEN must check the target's own sorry cone, not its `:= by` status.
metadata:
  type: feedback
---

A docstring that recommends *"the cheapest route is a BRIDGE to `X` elsewhere in the tree,
because `X` is **PROVEN**"* has priced the bridge by the wrong measurement. `X` being proven
says nothing about what `X` rests on, and in this development a theorem is routinely PROVEN
over one or two `sorry` leaves declared a few lines above it.

Measured 2026-08-02 on `poleDegree_inv_eq_poleDegree`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/PrincipalDivisorDegree.lean`). Its route analysis said
the bridge to `HyperellipticJacobian.lean`'s abstract-places formulation *"closes this leaf
with no new mathematics"*, on the strength of `PlaceData.degOf_divisor_eq_zero` being PROVEN
over `degOf_poleDivisor_eq_finrank_of_transcendental`. That last theorem is
`le_antisymm` of **two leaves that are both still `sorry`** — weak approximation on one side,
Riemann spaces on the other. So the bridge trades ONE open leaf for TWO plus the bridge. It
may still be the right architecture; it is not free, and it must not be dispatched as if it
were.

**Why:** "is it proven?" and "is it *finished*?" are different questions, and only the second
prices a bridge. `grep 'theorem X'` answers the first. The audit that made this mistake even
told the reader the name was a moving target and to *"check the tree before quoting a
count"* — and then quoted a count. Writing the check down is not running it
(cf. [[flt-audit-refuting-check-unrun.md]]).

**How to apply:** before believing any "bridge to X closes this", open X's proof and grep the
`sorry` status of every name it calls, transitively, or run `#print axioms X` appended to X's
own file (it must be that file — imported proof bodies are elided). Then state the trade in
leaves: *one open leaf becomes N*. Two further things the same run measured and the audit had
never established — both worth checking on any cross-module bridge: the import direction (here
legal: `HyperellipticJacobian`'s `Fermat`-cone is 21 modules and reaches neither `X0.lean` nor
the target module), and whether the theorem you would cite is stated at the generality you
need (here it is not — it is over the sextic-specific `PlaceData`, so a `PlaceSystem` hoist
inside an 11 000-line contended file is the bridge's real precondition).

Related: [[flt-inventory-audits-understate-what-exists.md]] is the mirror failure — an
absence claim that is wrong in the other direction.
