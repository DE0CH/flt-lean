---
name: flt-relpoint-ff-is-the-endomorphism-ring
description: "In flt-lean, \"the group law is only on the functor of points, not on Hom\" is not an obstruction — RelPoint f f IS End over the base, and post = pre at the universal point by rfl"
metadata: 
  node_type: memory
  type: project
  originSessionId: 50fad7c1-dc17-45fc-b771-890bdc684d72
  modified: 2026-08-01T01:01:53.924Z
---

`Fermat.AbelianSchemeStruct` presents an abelian scheme's group law only through
its functor of points, and several `X0.lean` docstrings record that as blocking a
cut: *"`1 ± w` are NOT morphisms of schemes here, so the leaf would have to
quantify over additive natural transformations of point functors with a
naturality side condition."*

**That is false.** `RelPoint f g = {x : T ⟶ A // x ≫ f = g}`; take `T := A` and
`g := f` and

    RelPoint f f = {v : A ⟶ A // v ≫ f = f}

**is** the endomorphism group of `A` over the base, carrying `ab.addCommGroup f`.
And the Yoneda step is `rfl`:

    RelPoint.post φ.1 φ.2 x = RelPoint.pre x.1 x.2 φ     -- both ⟨x.1 ≫ φ.1, _⟩

so evaluating an endomorphism at a point is precomposition at the universal
point, and every naturality obligation is an existing FIELD of the structure
(`pre_add`, `pre_zero`, `pre_neg`). No `addHom` is needed — `addHom`/`negHom`
exist 85 000 lines up and only over `SpecQ`, and are exactly the wrong tool.

**Why:** this closed `atkinLehnerFactor_eq_pm_one_of_new` (2026-08-01) after the
obstruction had stood for three days; the supporting API is ~15 short lemmas and
every one compiled first try.

**How to apply:** when a functor-of-points structure is said not to supply some
derived object, evaluate the functor AT ITS OWN BASE before believing it. The
API now in `X0.lean` is `RelPoint.endComp`, `RelPoint.post_eq_pre`,
`RelPoint.endOne`, `post_add_end`/`post_neg_end`/`post_zero_end`,
`post_endSub`/`post_endAdd`, `isAdditiveOn_endSub`/`_endAdd`,
`comm_endSub`/`_endAdd`, `endComp_endSub_endAdd`. One term has three readings,
`endComp φ ψ = pre φ ψ = post ψ φ`, all `rfl`: right-additivity of composition is
`pre_add` and FREE, left-additivity is `IsAdditiveOn` of the right factor and is
not — choosing the reading per step is the whole proof.

Related: [[flt-leaf-cost-estimates-are-hypotheses]],
[[flt-cut-at-the-image-not-the-quotient]].
