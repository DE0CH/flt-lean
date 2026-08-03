## A STRENGTHENING CAN FAIL TO DELIVER THE THING IT WAS MADE FOR
(2026-07-31, found while cutting `exists_twistedHilbertBlumenthalCocycle_of_split`.)
`HasSplitHilbertBlumenthalModuli` was strengthened on 2026-07-28 to export the two
`IsStandardLevelModule`s, and its docstring says in so many words that the point is the
`galRoot`-equivariance clause, "**i.e. `det ρ₀ = χ̄_ℓ`**". Every later docstring — the `Γ`-ACTION
AUDIT, the two cocycle leaves, the COUPLING AUDIT — quotes that reading and builds on it.
**The implication is FALSE as the predicate was written.** `IsStandardLevelModule` required `Λ`
only BIADDITIVE, and a biadditive alternating nondegenerate `μ_n`-valued form on `kI²` need not
be `φ ∘ det₂`: over `kI = 𝔽_{q²}` take `Λ = ψ ∘ Tr ∘ H` with `H` the hermitian form of
`𝔽_{q²}/𝔽_q`. Its isometry group contains the **norm-one scalars**, whose determinant is a
nontrivial square — so a representation twisted by a norm-one scalar character satisfies every
clause and has the wrong determinant. The repair is one free clause (`Λ` is `kI`-BALANCED,
`Λ (a • v) w = Λ v (a • w)`); the only producer's witness is `φ ∘ det₂`, which satisfies it by
`ring`.
Two things generalise:
* **The gap is always ADDITIVE-where-the-geometry-is-BILINEAR.** The object being axiomatised
  here is a Weil pairing, which is `𝒪_D`-bilinear (`DualStruct.weil_act`, `D` totally real).
  The predicate recorded only what was needed at the time — additivity — and the missing
  scalar clause is invisible until someone tries to *use* the predicate for the conclusion its
  docstring advertises. Whenever a `Prop` axiomatises a form, a pairing or a level structure,
  check the SCALAR clauses against the geometry before trusting a determinant/trace reading of it.
* **A docstring's "i.e." is a claim, not a definition.** Three separate audits repeated
  "`galRoot`-equivariance, i.e. `det ρ₀ = χ̄_ℓ`" without anyone deriving it, and the derivation
  is where it dies. Treat every "i.e." linking two differently-shaped statements as a lemma with
  no owner: either name it as a leaf, or refute it.
Corollary for CUTS: when the cut needs a group ("the pairing-preserving subgroup"), prefer the
one that is base-field-independent and definable from the geometry (`SL₂`) over the literal
stabiliser of the axiomatised form. The stabiliser reading was refuted twice here — once because
the two representations carry DIFFERENT normalisations, once because `IsStandardLevelModule`'s
equivariance clause constrains `Λ F` only for `σ` in the image of `Γ_F ⟶ Γ_ℚ`, so a form at
`F = ℚ(i)` is unconstrained at complex conjugation.
