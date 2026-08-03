## BEFORE DECOMPOSING A NODE, CHECK WHETHER THE PIECE IS EQUIVALENT TO THE WHOLE

(2026-07-31, same worktree, and it is the mirror image of the rule above.)
`isTorsion_jacobian_of_lFunction_ne_zero` ("`J₀(N)(ℚ)` is torsion") was decomposed on
2026-07-27 into Eichler–Shimura (`exists_heckeIsotypicDecomposition`) plus
Kolyvagin–Logachev on one isotypic factor (`isTorsion_factor_of_heckeIsotypic`). The
decomposition is recorded, audited, and reads as real progress.

It moved nothing on the arithmetic side, and since 2026-07-29 that is provable in-tree.
`exists_quasiSection_heckeIsotypicFactor` — Poincaré reducibility, PROVEN — gives
`v : A i ⟶ J` and `m > 0` with `u i (v x) = m • x`. So "`J(ℚ)` torsion" implies "factor
torsion" in three lines, and the consumer already proves the converse. **The piece and
the whole are EQUIVALENT.** The split is still load-bearing for a different branch (the
Atkin–Lehner development is stated over the decomposition), so it was not wrong to make
— but any future proposal to cut the factor leaf further along that axis is dead, and
conversely anything proving `J(ℚ)` torsion by ANY route (Kato, Mazur's Eisenstein ideal)
closes the factor leaf at every `i` without being re-aimed at a factor first.

The check is cheap and it is not the falsity audit: **for each piece, ask whether some
already-PROVEN theorem in the tree derives the piece from the whole.** A section, a
quasi-section, a retraction, a finite-kernel map or an isogeny is exactly the shape that
does it, and those are common. If one does, the cut has renamed the obligation rather
than reduced it, and the docstring should say so — otherwise the next owner reads a
decomposition and infers a reduction.

And when the answer is yes, **say which hoists it retires.**
`exists_quasiSection_heckeIsotypicFactor`'s docstring proposed hoisting its block ~27000
lines so `isTorsion_factor_of_heckeIsotypic` could reach it. That hoist would have bought
that leaf nothing — the only thing it could do with the quasi-section is the circular
step — and the resulting declaration would have been free-floating. A queued hoist is a
dispatch; retiring one is worth the same as closing a leaf.

