## AN AXIOM ON A STRUCTURE **FIELD** IS WEAKER THAN THE SAME SENTENCE ABOUT THE CLASSICAL OBJECT
(Same task, and it nearly produced a false falsity report.) `DualStruct.weil_nondegenerate`
is asserted at EVERY pair `(I, n)` with `(n : 𝒪_D) ∈ I`, not only at `I = (n)`. That looks
refutable at a ramified prime: `D = ℚ(√2)`, `𝔭 = (√2)`, `I = 𝔭`, `n = 2` (legal, `2 = (√2)²
∈ 𝔭`), `A'` an abelian surface with RM by `ℤ[√2]` and `T_2 A'` free. Then `A'[𝔭] = √2·A'[2]`
and `Â'[𝔭] = √2·Â'[2]`, so the CLASSICAL Weil pairing gives
`e_2(√2 y', √2 z') = e_2(2y', z') = 1` identically, while `A'[𝔭] ≅ 𝔽_2² ≠ 0` — the axiom
apparently concludes `A'[𝔭] = 0` and every leaf producing a `DualStruct` is FALSE.
**It is not, because `weil` is a FIELD of the structure and nothing ties it to `e_2`.** No
axiom of `DualStruct` relates `weil` at one `(I, n)` to `weil` at another — the only
compatibility in the file is `IsQAdicWeilTower`, a separate predicate constraining the
`q`-tower alone. So one may choose `weil` at `(𝔭, 2)` to be the evaluation pairing of
`Â'[𝔭] ≅ A'[𝔭]^∨`, which is `Γ_F`-equivariant and perfect because `√2 : A'[2]/A'[𝔭] → A'[𝔭]`
is an isomorphism. The remaining axioms are free there: `weil_gal` because `galRoot` is
trivial on `μ_2`, and `weil_act` because `√2` KILLS both sides, so the adjointness identity
reads `1 = 1`.
**The rule: to refute an axiomatized structure you must beat EVERY admissible field, not the
intended witness.** The cheap computation refutes the classical object and says nothing about
the structure. This is the exact mirror of the standing rule that a PREDICATE proven inhabited
may still be satisfied by the wrong normalisation: there the danger is under-commitment, here
the danger is reading a structure as if it were committed. Both are settled by the same
question — *what else inhabits this field?* — asked in the two directions.
Corollary, and it is why the audit is worth writing down rather than just passing: an audit
that SURVIVES is as valuable as one that refutes, because the computation is the obvious next
attack and the next owner will otherwise spend the cycle re-deriving it. Record it on the leaf
with the witness in full, and say which sibling leaves it also covers (this one covers
`exists_dualPolarization_of_mult`, which shares `DualStruct`).

