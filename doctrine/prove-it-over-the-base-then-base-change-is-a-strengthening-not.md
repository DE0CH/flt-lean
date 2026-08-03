## "PROVE IT OVER THE BASE, THEN BASE-CHANGE" IS A STRENGTHENING, NOT A REFACTOR

(2026-07-31, decomposing `exists_nonconstant_toAbelianScheme_of_nontrivial_cuspForm` in
`ModularCurve/X0.lean`.) A leaf of the shape

    ∀ (K : Type) [Field K] (k : Spec K ⟶ S), ∃ (A over Spec K) (c : X ×_S Spec K ⟶ A), P c

looks like it is *begging* to be cut into "∃ one `A ⟶ S` and one `φ : X ⟶ A` over `S`" plus "base
change along `k`". The base-change half is usually free — `AbelianSchemeStruct.baseChange` and the
three `curveBaseChangeProj` stability lemmas in `RelativePicard.lean` already exist — and the
assembly is four lines. **It is also a strictly stronger statement, and the strengthening is exactly
the part nobody prices.** Moving the `∃ A` outside the `∀ K` asserts that the object *spreads out
over the whole base*, i.e. that it has good reduction everywhere on `S`. For `A_f`, a quotient of
`J_0(N)`, that means `N` invertible on `S` — which `IsX0Compactification` does not say. It says
`strX` is smooth, which morally forces it and is not the same statement.

So the cut can manufacture a leaf that is FALSE at a base where the original is TRUE, and no
frontier instrument will ever say so: the assembly compiles, the leaf count is unchanged, and the
new statement reads like a cleaner version of the old one.

**The test is one question: does the quantifier move put an existential outside a universal?** If it
does, you are not refactoring, you are conjecturing — and you owe the same faithfulness audit as for
a brand-new leaf, against the *pathological* members of the outer quantifier's range, not the
intended one. When the answer is unclear, keep the `∃` inside and cut along some other seam. **A
leaf that is false is strictly worse than a leaf that is open** — the file's own doctrine — and this
is one of the few ways to turn the second into the first while believing you are doing bookkeeping.

The dual observation is what made the cut that *was* taken worth taking: a decomposition that
strengthens nothing can still pay, if the assembly absorbs bookkeeping the leaf would otherwise
carry. Here it discharged base change of smooth/proper/geometrically-connected, integrality, local
Noetherianness and the existence of a genus witness, so both halves are stated about a curve over a
field with a number attached — and neither mentions the other's vocabulary.

