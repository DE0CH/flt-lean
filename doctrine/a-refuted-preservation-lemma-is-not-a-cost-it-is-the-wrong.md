## A REFUTED PRESERVATION LEMMA IS NOT A COST — IT IS THE WRONG QUESTION
(2026-07-31, measured on item (5) of
`exists_obstructionCocycle_smallExtension_deformation` in
`HardlyRamified/Deformation.lean`.)
An audit that refutes *"property P is preserved along this map"* has answered a
question no consumer asked. The consumer wants **some** object with P. So the
next move is not to price the harder lemma — it is to ask **how the object is
CONSTRUCTED**, and whether P is free for objects built that way.
Item (5) was recorded as "the single binding item" of its audit, with a WARNING
correctly showing that all four clauses of `IsHardlyRamified` fail the naive
preservation reading. Two of the four then cost almost nothing:
- `isUnramified`: the refutation is real — a lift of an unramified `ρ` along a
  small extension can be ramified, since `ρ̃(I_p) ⊆ 1 + M₂(ker π)` is elementary
  abelian and the tame quotient of `I_p` surjects onto `ℤ_ℓ` for `p ≠ ℓ`. But
  obstruction theory builds the lift as a representation of `G_{ℚ,S}`, and a
  representation killing `N_S` is unramified outside `S` **by the definition of
  `N_S`**. Ten lines.
- `det`: the audit called the square-root correction "a choice, not an
  implication" and left it open. A choice that is CANONICAL is a construction —
  `2` is invertible on the square-zero `ker π`, so the square root in `1 + ker π`
  is unique — hence provable, and now proven.
The other two clauses (`isFlat`, `isTameAtTwo`) really are the local smoothness
theorems. **A "state it per clause" instruction does not mean the clauses are
comparable**: here four clauses split into three kinds, and the split is worth
finding before dispatching four equal-sized tasks at them.
Corollary for reviewers of audits: a refutation paragraph is evidence about the
statement it refutes, and about nothing else. Re-read the CONSUMER before
inheriting its verdict as a cost. Same family as the memory entries
`flt-inventory-audits-understate-what-exists` and
`audit-searched-production-not-invariant`.
**Second half of the same lesson: when NO global form is true, say so on the
declaration.** The two remaining clauses are local conditions, and both readings
a prover reaches for first are FALSE: "given a global homomorphism lift, some
global lift is flat at `ℓ`" needs surjectivity of
`H¹(G_{ℚ,S}, ad) → H¹(G_ℓ, ad)/H¹_f`, which is the dual-Selmer obstruction; and
"there is a global rep whose restriction at `ℓ` is a flat lift" needs a local
homomorphism to extend globally. So the leaves are stated on `GaloisRep ℚ_v`,
with local readings of the conditions carrying `Iff.rfl` bridges to the global
ones — which is what proves they are the same conditions and not weakenings.
Writing the two refutations into the section header costs four lines and stops
the next owner from spending a cycle rediscovering them.
