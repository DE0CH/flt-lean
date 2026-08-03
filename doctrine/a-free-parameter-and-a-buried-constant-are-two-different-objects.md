## A FREE PARAMETER AND A BURIED CONSTANT ARE TWO DIFFERENT OBJECTS
(2026-07-31, `CyclotomicIdealSymbol.lean`.) A leaf can be false because two of its
hypotheses talk about *the same mathematical object chosen twice*, and nothing in the
statement says they are the same choice. `globalFrob_map_mul_inv_mem_of_isArithFrobAt`
pins one side of a comparison through a **free parameter** `ι : CF →ₐ[ℚ] ℚ̄` and the
other side through the **fixed but arbitrary** `IsAlgClosed.lift` buried inside
`Field.absoluteGaloisGroup.mapAux`. Both sides are individually right; the leaf asks for
`[w] = [γ w]` in `Cl(ℚ(μ_p))`, `γ` being the Galois element relating the two embeddings.
Refuted with `p = 23`: `Cl = ℤ/3`, `h⁺ = 1` so complex conjugation acts by `−1`, and at
`ℓ = 47` a degree-one prime of class `1` conjugates to one of class `2`.
The general shape, which this development is unusually exposed to: **a definition that
depends on a noncomputable arbitrary choice exports that choice as part of its meaning.**
`Field.absoluteGaloisGroup.map` is the standing example — the file already knew it has no
functoriality equation (that is why `exists_conj_of_two_embeddings` exists), and the same
fact makes every statement that pairs it with a *quantified* embedding suspect. So when
auditing a leaf, list the choices each side makes and ask whether the statement forces
them to agree; a `∀ ι` on one side and a `Classical.choice` on the other is a defect even
when both sides are conjugate, because conjugacy is not what the conclusion measures.
Corollary for the repair: the fix is a STATEMENT change, so it is not the leaf owner's to
make alone when the consumer's signature has to move with it. Write the falsity audit,
prove whatever survives it (here the final absorption step, which consumes only the SHAPE
of the discrepancy and none of the geometry), and escalate the interface decision.
