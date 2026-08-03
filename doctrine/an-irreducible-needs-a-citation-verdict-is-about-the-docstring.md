## AN "IRREDUCIBLE / NEEDS A CITATION" VERDICT IS ABOUT THE DOCSTRING'S STORY, NOT THE STATEMENT

(2026-07-31, `nonempty_isJLineZ` in `X0.lean`.) The leaf carried a citation verdict —
"Igusa; `Y_0(1) ≅ 𝔸¹_j` over `ℤ`" — backed by a survey that is *correct*: there is no
integral model of a modular curve in mathlib at our pin, in `~/cs/FLT`, or in this
project. Two agents had recorded and re-recorded it. **The statement does not mention a
modular curve.** `IsJLineZ N R` asks, field by field, for the `j`-invariant of the
elliptic scheme underlying a `Γ₀(N)`-datum over an `R`-scheme, read as a point of
`𝔸¹_R`. There is no `Y_0`, no compactification, no cusp in it.

So the verdict was scoped to the *object the prose names* rather than to the *statement
the compiler sees*, and the check that refutes it costs one grep: **read the conclusion
field by field and look for the object the verdict is about. If it is not there, the
verdict is about the story, not the leaf.** This is the same failure shape as
"AUDITS SEARCH PRODUCTION, NOT INVARIANTS" and "THE SELF-CERTIFYING GREP", one level up:
the survey was run against a true sentence that was not the theorem.

**What was actually in the way was a PARAMETER PINNED AT A SPECIAL VALUE.** The whole
rational `j`-theory — local Weierstrass models, well-definedness and functoriality of
`j`, the gluing, and the Zariski descent from affine bases to all bases — was already
proven, and *none of its proofs read the base or the level*. But it was stated at level
`1` and over `SpecQ`, so nothing integral could reach it. Two mechanical generalisations
made it reachable and the leaf became an assembly:

- `Gamma0Datum 1` → `Gamma0Datum N` in the Weierstrass chain. **Generalising a SORRY
  LEAF's statement in a parameter its content never reads is free**, and it is better
  than cutting a parallel leaf: `exists_weierstrassModel_of_isLocalRing` and
  `..._away_of_atPrime` are now shared by the rational and the integral `j`-theory
  instead of duplicated, and the frontier did not move.
- the `j`-VALUE separated from its PACKAGING: `IsJElt d r` says `r` is the `j`-value as
  an element of the base RING, with no `j`-line in it. The base ring is then free of `ℚ`
  and one element serves `Spec ℚ[X]` and `Spec R[X]` both.

**The generalisable half is usually the BOOKKEEPING, and it is usually most of the
lines.** Before believing that an integral/relative/positive-characteristic analogue
needs new theory, check which of the existing proof's steps actually mention the thing
being varied. Here: zero of them.

