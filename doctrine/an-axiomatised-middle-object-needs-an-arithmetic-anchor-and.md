## AN AXIOMATISED MIDDLE OBJECT NEEDS AN ARITHMETIC ANCHOR — and usually the anchor IS the object
(2026-07-31, executing the `D_pst` cut on
`exists_level_not_hasFlatProlongationAt_of_isWeightTwoNewform_of_sq_dvd`.)
"Introduce X as DATA carrying axioms, in the `RamificationFiltration` shape, and split the leaf
across it" is now a standard move here. It has a failure mode that is invisible until you write
the axioms out, and `RamificationFiltration`'s own audit already stated the general form: **no
axiom set expressed in the abstract language of the object alone can pin it — the tie to the
thing it is a middle for must be ARITHMETIC.**
So before landing such a definition, sort every candidate anchor into three classes. For a middle
`X` splitting `A → False` into `A → ∃ X, adm X ∧ good X` and `hyp → ∀ X, adm X → ¬ good X`:
* **formal axioms only** (shape, dimension, nilpotence, equivariance): the TRIVIAL `X` is
  admissible for every input, so the universal half is REFUTABLE. That is a FALSE leaf — strictly
  worse than the open one it replaces, and it typechecks;
* **an anchor `good X → P` with `P` implied by the existential half's own HYPOTHESIS**: the
  existential half becomes a three-line tautology (take the trivial `X`, discharge the anchor from
  the hypothesis) and the universal half becomes the original leaf. The cut collapses — one leaf
  for one equally hard leaf plus a definition;
* **an anchor demanding something the hypothesis does NOT immediately give.** This is the only
  class that is a real cut, and there is usually exactly one candidate. Here it was "the flat
  models at the successive levels can be chosen COMPATIBLY", i.e. that they assemble into a
  `p`-divisible group.
And then the punchline, which is what to expect rather than a special case: **once you know the
one anchor, the axiomatised wrapper has no field with a consumer, and the honest move is to
DEFINE the anchor object explicitly and drop the wrapper.** The Weil–Deligne parameter here
became `PDivisibleTowerAt`, a structure of finite flat Hopf algebras with `Γ`-equivariant
bijections on geometric points and compatibility maps — explicit data, no axioms about an
unformalisable functor. Layer the named literature object on later, when a leaf needs a VALUE it
carries (Saito is really `a(WD) = ord_p M₀`; the leaf used only `a ≠ 0`).
**The risk profile is why this is not merely tidier.** With an axiomatised middle, both failure
modes are live: too weak ⇒ the universal half is FALSE (silent), too strong ⇒ the existential half
is unprovable. With an explicit-data middle the first is STRUCTURALLY ABSENT — there is nothing to
fake about a Hopf algebra with a bijection on points — and the second is visible as an unprovable
leaf, further guarded by a one-term inhabitedness witness (here: the subsingleton representation,
carrier `𝒪ᵥ`, identity inclusions). That witness is the `Nonempty (RamificationFiltration v)`
conjunct's job, discharged by a term instead of carried as a hypothesis.
Also worth copying: **the TYPING of the compatibility field is itself a check** no degenerate
witness can perform. `incl k : G k →ₐ G (k+1)` and the tower reduction `k+1 → k` must line up;
reverse either and the field does not elaborate.
**Corollary trap, and it cost nothing only because the FALSITY AUDIT was read first: the
`unusedSectionVars` linter will tell you to `omit` an instance that is load-bearing and
syntactically invisible.** Both new leaves need `[Module.Finite ℤ_[p] R]` — it is what makes the
`𝔪`-adic tower cofinal with the `p`-adic one — and it appears nowhere in either statement. The
linter's suggested `omit` would have made both leaves FALSE (witness: `R = 𝒪_L` for `L/ℚ_p`
infinitely ramified, where `𝔪² = 𝔪` and the tower collapses to the residue field). When the
linter names an instance, check the file's falsity audits before obeying it; the fix is
`set_option linter.unusedSectionVars false in` plus a comment saying why.
