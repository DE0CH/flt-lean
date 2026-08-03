## THE TWIN FILE'S DEPENDENCY ORDER TELLS YOU WHICH OF TWO SHAPES OF ONE NODE IS THE WEAKER LEAF
(2026-08-02, `flt-lean-89`, on `exists_gamma1AtlasData_pullbackSpecial` in
`ModularCurve/X1.lean`.)  This development is built out of `Γ₀`/`Γ₁` twins, and a
`Γ₁` leaf is routinely cut by transcribing whichever `Γ₀` declaration a reader's
eye lands on.  That choice is not free: the `Γ₀` file usually contains SEVERAL
statements of the same node, and **their dependency order is a proof that one is
strictly weaker than the other.**  Read it before transcribing.
Here `X0.lean` carries both `universal_classifyPullback_special` (the INITIALITY
clause for the special fibre) and `exists_gamma0AtlasData_pullbackSpecial`
(Katz–Mazur's CONSTRUCTION data over `𝔽_ℓ`), and the first is **upstream** of the
second — atlas data is derived from initiality plus the `𝔽_ℓ`-side GIT
presentation, and initiality is itself proven from an atlas over `ℤ_(ℓ)`.  So on
the `Γ₁` side the construction form was the stronger obligation, and it had been
transcribed because it is the one whose name matches the consumer's route.
**Two riders that made the recut cheap and safe.**
* **Compile the implication before you touch the file.**  "The old leaf implies
  the new one" is the whole faithfulness argument for a recut, and it is one
  scratch declaration: state the old leaf's structure as a hypothesis, apply the
  existing glue, and let the elaborator check it.  Mine was 20 lines and came
  back green in 25 s, which is what licensed deleting the glue afterwards.  A
  recut argued in prose and not compiled is a conjecture.
* **A construction-shaped leaf carries hypotheses its consumer does not.**  The
  old leaf asked for a moduli scheme over `𝔽_ℓ`, and the only in-tree producers
  of one (`exists_gamma1AffineModel`, `exists_gamma1GITPresentation`) carry
  `4 ≤ N`, while every consumer of the node reaches it with no bound on `N` at
  all.  Its own docstring flagged that gap and left "deciding which is part of
  this leaf".  The initiality form asks for no scheme, so the gap does not exist
  — **an arity mismatch between a leaf and its producers is evidence the leaf is
  cut at the wrong shape**, not merely a chore for whoever takes it.
**The cost, stated plainly: the count does not move, and the recut STRANDS the
glue.**  `Gamma1AtlasData` and `isCoarseModuliY1_of_atlasData` had exactly one
consumer between them — the old assembly — so they were deleted, recoverably, and
the note that replaces them quotes the three-line derivation that restores the
old route.  Nothing unique went with them: the cocone argument they carried is
the body of the live `Gamma1Atlas.toIsCoarseModuliY1`.  **Check that before
deleting a stranded pair** — if the argument exists nowhere else, keep the pair
and take the other cut.
