## AN AUDIT'S "BLOCKED ON MISSING STRUCTURE" VERDICT EXPIRES — RE-CHECK THE NAMED PRECONDITION

(2026-07-31.) A leaf's atomicity audit is usually written as a conditional: *this cut is
blocked, and it becomes available exactly when X exists*. The condition is the useful part
and it is the part nobody re-reads. `X18.two_divisible_pic`'s descent-axis bullet said the
`2`-descent cut "needs residue fields `κ(v)` and the norms `N_{κ(v) ⊗ L / L}` — precisely
the degree theory `PlaceData` deliberately omits … so the cut is available exactly when
someone extends `PlaceData` with residue fields."

**No extension was ever needed and none happened.** A valuation determines its own valuation
ring, so `O_v`, `m_v`, `κ(v) = O_v ⧸ m_v` and `deg v = [κ(v) : K]` are definable from the
`ord` axioms `PlaceData` already had — and by 2026-07-30 they were IN THE SAME FILE
(`PlaceData.valRing`, `valMax`, `residue`, `degOf`), with `exists_degreeMap` PROVEN over
them, roughly 3600 lines above the audit that declared them absent. The verdict was written
before that work and was never re-read against it.

This is the same failure as the VOID-AUDIT rule above, in the other direction: there, a
statement changed under a valid audit; here, the WORLD changed under a valid audit. Both
produce an audit that is honest, internally correct, carries a date, and is wrong.

So, two rules:

- **When an audit says "blocked until X exists", grep for X before believing it.** One
  `grep -n` is the whole check, and its answer is a fact rather than an opinion.
- **Separate "structurally blocked" from "expressible but very large" in the verdict, and
  say which you mean.** Only the first is a reason never to dispatch. Here the arithmetic
  obstruction (`#Sel₂ = 1`: class groups and `S`-units of a degree-`6` field) is entirely
  real and unchanged — but "nobody can even state it" and "somebody would have to build a
  lot" call for opposite decisions, and the bullet had been read as the first for days.

Corollary for whoever writes the audit: phrase the precondition so it is GREPPABLE — name
the declaration you would need, not the capability. "needs `PlaceData.residue`" would have
been refuted by the next reader in ten seconds; "needs the degree theory `PlaceData`
deliberately omits" survived because there was nothing to look up.

