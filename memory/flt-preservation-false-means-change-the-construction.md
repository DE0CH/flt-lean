---
name: flt-preservation-false-means-change-the-construction
description: "When an audit refutes a preservation lemma, the repair is often to change how the object is BUILT, not to prove a harder lemma — the unramified clause of item (5) cost nothing once the lift was taken through G_{Q,S}"
metadata:
  type: project
---

An audit that says *"property P is not preserved along the map, here is why"* has
answered a question nobody needs answered. The consumer never wanted preservation;
it wanted **some** object with P. So before pricing the hard lemma, ask **how the
object is constructed** and whether P is free for objects built that way.

Measured on item (5) of `exists_obstructionCocycle_smallExtension_deformation`
(`HardlyRamified/Deformation.lean`, 2026-07-31). The audit's warning was correct
on all four clauses of `IsHardlyRamified`: a lift `ρ̃` of an unramified `ρ` along
a small extension really can be ramified — `ρ̃(I_p) ⊆ 1 + M₂(ker π)` is an
elementary abelian `ℓ`-group and the tame quotient of `I_p` (`p ≠ ℓ`) surjects
onto `ℤ_ℓ`, so nontrivial continuous maps abound. That is a genuine refutation of
the preservation reading, and it reads as *"this clause is work"*.

It is not. Obstruction theory builds the lift as a representation of
`G_{ℚ,S} = Γ ℚ ⧸ N_S`, and a representation killing `N_S` is unramified at every
place outside `S` **by the definition of `N_S`**. The whole clause is ~10 lines
(`isUnramifiedAt_of_ramificationKernel_le_ker`), and the hypothesis to state is
`ramificationKernel S ≤ ρ.ker`, not anything about `π`.

The same move re-priced the `det` clause: the audit called the correction "a
choice, not an implication" and left it open. A choice that is *canonical* is a
construction — `η = (det ρ̃ · d⁻¹)^{-1/2}` inside `1 + ker π`, unique because `2`
is invertible there — so it is provable, and it is
(`exists_lift_det_eq_of_squareZero_ker`).

**How to apply.** When a leaf's audit refutes a preservation/functoriality
statement, do not inherit the verdict as a cost. Re-read the CONSUMER: it usually
asks for existence, and the producer usually has more structure than the
preservation statement was allowed to see. Two of four clauses of a "single
binding item" fell to this in one pass. See also
[[flt-inventory-audits-understate-what-exists]] and
[[audit-searched-production-not-invariant]] — same family: the audit answered a
narrower question than the leaf poses.
