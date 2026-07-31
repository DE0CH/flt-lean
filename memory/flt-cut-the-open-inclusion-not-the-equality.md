---
name: flt-cut-the-open-inclusion-not-the-equality
description: When a leaf is an EQUALITY of submodules/subgroups, check which direction the axioms already give — cut only the open inclusion, and a "supremum attainment" difficulty often dissolves at the same time
metadata:
  type: feedback
---

Two techniques that together turned `exists_breaks_of_hasFiniteWildMonodromyAt`
(ArtinConductor.lean, 2026-07-31) from "attainment of a supremum of rationals,
the sharp falsity risk of the section" into one small inclusion.

**1. Cut the inclusion, not the equality.** The leaf wanted
`V^{G^u} = V^{G_{m+1} ⊓ P_v}` for `u` in a Herbrand gap. One direction was
already free from the existing axioms (`gp_le_gp` antitonicity plus
`gp_herbrand` at the right endpoint, i.e. two lines of `calc`). Stating the
leaf as the *equality* would have handed the next prover a goal half of which
they would re-derive from scratch. So: prove the free half as its own named
theorem, state the leaf as the remaining `≤`, and recover the equality by
`le_antisymm`. Before cutting any equality leaf, try each direction against
the axioms in hand — in an axiomatised structure one direction is very often
already there.

**Why:** the sandwich an axiom system gives you is usually one-sided. Naming
which side is free also *localises the falsity risk*: it says precisely which
inequality a counterexample must break.

**2. A supremum you cannot attain may not be a supremum.** The docstring had
framed the break list as `μ k = sup {u | c u > k}` and flagged attainment and
rationality as the danger. But once `c` is the step function of ONE finite
level, its jumps ARE the Herbrand values `φ_D(m)` — rational by construction —
and the `k`-th break is just `Nat.findGreatest (fun m => k < γ m) bound`. No
sup, no reals, no left-continuity argument. **How to apply:** when a leaf's
stated route goes through a supremum over ℚ, look for a discrete parameter
that indexes the jumps; if one exists, reindex and the analytic difficulty
disappears.

See [[flt-finrank-zero-means-infinite-rank]], the other lesson from the same
proof.
