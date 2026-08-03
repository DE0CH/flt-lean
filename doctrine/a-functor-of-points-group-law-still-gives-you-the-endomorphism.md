## A FUNCTOR-OF-POINTS GROUP LAW STILL GIVES YOU THE ENDOMORPHISM RING — `RelPoint f f` IS IT, AND `post = pre` AT THE UNIVERSAL POINT BY `rfl`
(2026-08-01, `flt-lean-173`, closing `atkinLehnerFactor_eq_pm_one_of_new` in
`ModularCurve/X0.lean`.)  That leaf's own ROUTE MAP had localised its content
perfectly — *the endgame is one line of ring theory,
`(1 − w)(1 + w) = 1 − w² = 0`, so the leaf IS "the Hecke-commuting
endomorphisms of `A i` have no zero divisors"* — and then declined to make the
cut, for a reason recorded in the task prompt and in the file:
> stating it faithfully needs endomorphisms formed as `1 ± w`, which are NOT
> morphisms of schemes here — `AbelianSchemeStruct` gives a group structure on
> the `RelPoint` functors, not on `Hom` — so it would have to quantify over
> additive natural transformations of point functors with a naturality side
> condition, and a leaf of that shape is easy to state slightly wrong.
**Every clause is true and the conclusion is false, because the object the
sentence says is missing is one the development already has under another
reading.**  `RelPoint f g` is `{x : T ⟶ A // x ≫ f = g}`; take the test object
to be `A` itself and the base point to be `f`, and
    RelPoint f f = {v : A ⟶ A // v ≫ f = f}
**is** the group of endomorphisms of `A` over the base — and it carries
`ab.addCommGroup f`, the very instance the structure hands out at every base
point.  So `1 ± w` are formed with `ab.add`/`ab.neg` and nothing else; no
morphism-level `addHom` is needed, and none was used.  Better, the Yoneda step
that was feared is `rfl`:
    RelPoint.post φ.1 φ.2 x = RelPoint.pre x.1 x.2 φ      -- both are ⟨x.1 ≫ φ.1, _⟩
i.e. **evaluating an endomorphism at a point is precomposition at the universal
point.**  Every naturality obligation is therefore an existing FIELD of
`AbelianSchemeStruct`: additivity of `φ ↦ post φ x` in the ENDOMORPHISM is
`pre_add`, the zero endomorphism evaluates to zero by `pre_zero`, and inversion
by `pre_neg`.  The whole bridge is ~15 short lemmas and every one compiled first
try; the parent then fell out in forty lines.
**The generalisable check, and it is one line of thought: when a development
presents a structure only through its functor of points and a docstring says
some derived object "is not available at this level", ask whether the functor
EVALUATED AT ITS OWN BASE is that object.**  A functor-of-points presentation
is not weaker than a morphism-level one — it is Yoneda-equivalent — so the
morphism-level object is always recoverable, and usually as a special case of
the data you already have rather than through a construction. In this file the
morphism-level group law had actually been built (`addHom`, `negHom`,
`add_eq_addHom`), 85 000 lines above and only over `SpecQ`, and it is exactly
what a reader reaches for and exactly what is NOT needed.
Three riders, all measured in the same run.
* **One term, three readings, and each is used once.**
  `endComp φ ψ = pre φ.1 φ.2 ψ = post ψ.1 ψ.2 φ`, all by `rfl`.  Right-additivity
  of composition is `pre_add` and is FREE; left-additivity is `IsAdditiveOn` of
  the right factor and is NOT.  Knowing which reading to use at each step is the
  whole proof: expand `(1 − w)(1 + w)` in the SECOND argument (free) and the
  residual `(1 − w) ∘ w` in the FIRST (paid, one `IsAdditiveOn`).
* **`rw` will not see `𝟙 A` through a wrapper.**  `RelPoint.post_id` exists and
  is exactly the fact wanted, and it does not fire on
  `RelPoint.post (RelPoint.endOne f).1 …` because `endOne f` is not syntactically
  `𝟙 A`.  Restate it once against the wrapper (`RelPoint.post_endOne`, two lines)
  rather than unfolding at every use site — the same "printed pattern equals
  printed target" family the file already records, with a `def` as the cause.
* **A recut that leaves the count at 1 → 1 must say so, and say what got
  smaller.**  Here `X0.lean` has 101 sorried declarations before and after.  What
  changed is that the surviving leaf is stated about the endomorphisms of one
  isotypic factor and mentions no Atkin–Lehner datum, no `w`, no `D.form` and no
  `D.coeff` — and its junk-factor degeneracy is now a SINGLETON endomorphism
  group, so the conclusion holds outright there rather than needing an argument.
