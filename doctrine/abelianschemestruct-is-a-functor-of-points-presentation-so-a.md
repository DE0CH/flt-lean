## `AbelianSchemeStruct` IS A FUNCTOR-OF-POINTS PRESENTATION, SO A REPRESENTABILITY LEAF NEED NOT CARRY A GROUP LAW
(Same task, and it is what made the recut worth making.)  `AbelianSchemeStruct f`
has twelve fields: nine are the group law on `RelPoint f g` plus its naturality,
and three are `IsProper`, `Smooth`, `GeometricallyConnected`.  **The nine are
transported by any bijection `RelPoint f' g ≃ RelPoint f (…)` that is natural in
the test object.**  So a leaf whose content is "this new scheme represents that
functor" should assert the THREE geometric conditions and the bijection, and
never the group structure — the consumer builds it, in about forty lines of
`Equiv.apply_symm_apply` plus one `(Φ _ _).injective` per naturality field.
`exists_weilRestriction_of_finiteEtale` is the worked instance: the residue of
Weil restriction is now BLR 7.6/4 + 7.6/5 and nothing else, where the leaf it
replaced also owed the group law, the `t = 𝟙` step and the nonconstancy transfer.
* **The count does not move** — one leaf out, one leaf in — so say so in the
  commit and give the receipt (`git diff` shows one `-  sorry` and one `+  sorry`
  in that module).  Judge it by what is LEFT: here the residue lost every mention
  of a group, of a curve and of nonconstancy.
* **A structure-instance field written as `pre_add h hg x y := …` binds the
  IMPLICIT binders too.**  `AbelianSchemeStruct.pre_add` is
  `∀ {T' T} (h) {g} {g'} (hg) (x y), …`, and `pre_add h hg x y :=` bound `hg` to
  the implicit `g`; the goal then still starts with a `∀` and every `simp only`
  reports "made no progress".  Use `pre_add := by intro T' T h g g' hg x y` and
  the problem disappears.  The symptom — a `simp only` failing on a goal that
  looks right in the error message — reads as a missing lemma and is not one.
