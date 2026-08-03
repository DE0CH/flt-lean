## A LEAF STATED OVER A SHEAF REDUCES TO **ONE AFFINE CHART**, AND THE PIN HAS ALL THREE BRIDGES

(2026-08-01, `flt-lean-193`, `exists_generator_sectionIdeal_at_section` in
`ModularCurve/RelativePicard.lean`: two recuts in one run, count `1 → 1` each time, and the
surviving leaf went from "a clause at every open `W ≤ U`" to "one affine chart, `ker φ = (s)`
with `s` a nonzerodivisor" — Stacks 0C4S in the form the literature states it.)

A leaf whose clauses are quantified over OPENS is almost never a leaf about sheaves. It is a
leaf about ONE RING wearing sheaf clothing, and the undressing is two mechanical steps that
mathlib supports end to end. Run them before pricing any geometry:

1. **all opens `≤ U` → a BASIS of `U`.** Separatedness (`TopCat.Sheaf.eq_of_locally_eq'`) for
   any clause of the form "`… = 0 → … = 0`", gluing (`TopCat.Sheaf.existsUnique_gluing'`) for
   any clause of the form "`∃ r, x = r · s`". **Prove the first clause for every open FIRST
   and then consume it**: it is exactly what makes the local cofactors agree on overlaps, so
   the two halves are not independent and the order is forced. ~55 lines, and it should take
   the basis as an ABSTRACT predicate so the caller picks the family it can compute on.
2. **a basis → ONE affine chart.** The basis to take is the BASIC OPENS of an affine `U`,
   because there — and only there — `Γ` is a localization of `Γ(Y, U)`:
   * `IsAffineOpen.exists_basicOpen_le` — inside an affine `U`, every open `W` and every
     `z ∈ W` admit `D(f)` with `z ∈ D(f) ≤ W`. This is the basis fact, and it is stated for
     an affine OPEN of an arbitrary scheme (`isBasis_basicOpen` is only for an affine
     SCHEME, i.e. for `⊤`, and transporting it by hand is the wrong move);
   * `IsAffineOpen.isLocalization_basicOpen` — `IsLocalization.Away f Γ(X, X.basicOpen f)`,
     with the `Algebra` instance being restriction (`algebra_section_section_basicOpen`), so
     `X.presheaf.map (homOfLE (X.basicOpen_le f)).op a` **IS** `algebraMap … a`, by `rfl`;
   * **`IsAffineOpen.app_basicOpen_eq_away_map`** — the one nobody finds. It factors
     `f.app (Y.basicOpen r)` as `IsLocalization.Away.map` of `f.app U` followed by the
     transport along `f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app U r)`. That is what turns
     "the kernel of `f^♯` localizes" from a theory into six lines. It needs
     `IsAffineOpen (f ⁻¹ᵁ U)` as well as `IsAffineOpen U`.

**A GREP FOR THE CONCEPT WILL NOT FIND THE THIRD ONE.** "kernel", "localize", "exact" return
nothing; the lemma is named after the SHAPE of the factorization. When you want a statement
about `f.app` on a distinguished open, read `Mathlib/AlgebraicGeometry/AffineScheme.lean`'s
`isLocalization_basicOpen` neighbourhood top to bottom — `appLE_eq_away_map`,
`app_basicOpen_eq_away_map` and `appBasicOpenIsoAwayMap` are all there, within thirty lines
of each other, and they are the whole affine-chart dictionary.

**DERIVE THE BRIDGE'S EXTRA HYPOTHESIS IN THE ASSEMBLY; DO NOT ASK THE LEAF FOR IT.** Step 2
needs `IsAffineOpen (σ ⁻¹ᵁ U)`, and the reflex is to add it as a third conjunct the leaf must
produce. It was free from hypotheses the leaf already had: `IsProper` + "σ is a section" makes
`σ` a closed immersion, `IsClosedImmersion → IsAffineHom` is an instance, and
`IsAffineOpen.preimage` finishes. **So the general check when a bridge wants a hypothesis: try
to derive it from the leaf's EXISTING binders before widening the leaf's conclusion.** Here
that also corrected the leaf's own audit, which said `_hproper` was not needed in this half —
on the route now taken it is.

**Two accounting points, because the count never moves for this kind of work.** Both recuts
were `1 → 1`, verified twice over (the build's `declaration uses 'sorry'` warning set AND a
comment-stripped token scan, `13 → 13`); say so in the commit or the delta reads as nothing
having happened. And both are EQUIVALENCES, not strengthenings, so the faithfulness audit
transfers — but write the `⇐` direction out, in one paragraph, or the next reader has to
re-derive it to know whether the audit still applies.

**Throughput note, since it is what made two recuts fit in one run.** The module is 9 000
lines and builds in ~56 s; a scratch that `public import`s its already-built olean and
restates the new declarations under throwaway names verified every round in **7 seconds**. The
whole second bridge — five `IsLocalization` steps and an `eqToHom` injectivity — went from
first draft to green in six such rounds and then compiled in the real file first try.

### The `ConcreteCategory.hom` / `CommRingCat.Hom.hom` split, and the one-line cure

Both forms print as the same coercion and are defeq, and mathlib's own statements mix them:
`hU.app_basicOpen_eq_away_map` produces a term containing `CommRingCat.Hom.hom (σ.app U)`
while the goal carries `ConcreteCategory.hom (σ.app U)`. Consequences met in one proof:
`simp only [CommRingCat.ofHom_apply]` reports itself UNUSED on a goal that visibly contains
`ConcreteCategory.hom (CommRingCat.ofHom g) x`, and every `rw` keyed on the other form fails.
**The cure is a type-ascribing `have`, which is checked up to defeq**:

    have hx' : IsLocalization.Away.map ↑Γ(Y, D f) ↑Γ(T, D (σ.app U f)) (σ.app U).hom f
        (IsLocalization.mk' _ a y) = 0 := hx      -- `hx` is the `ConcreteCategory.hom` form

after which `simp only [IsLocalization.Away.map, IsLocalization.map_mk',
IsLocalization.mk'_eq_zero_iff]` fires. Same trick for a hypothesis coming back from
`Submonoid.powers` membership (`hk : (fun x => φ f ^ x) k = ↑m`): restate it beta-reduced with
`have hk' : σ.app U f ^ k = (m : Γ(T, σ ⁻¹ᵁ U)) := hk` and `rw` works. This is the standing
"printed pattern equals printed target ⟹ switch to a defeq-checking tactic" rule; the new part
is that a `have` with an explicitly written type is the cheapest such tactic and it lets the
REST of the proof stay in `rw`/`simp`.

Two smaller ones from the same proof: an element obtained from `existsUnique_gluing'` has type
`ToType (Z.sheaf.obj.obj (op W))`, which is defeq to `Γ(Z, W)` and not syntactically it, so
`g * s` fails to elaborate with `failed to synthesize HMul …` — `obtain ⟨g, hg⟩ : ∃ g : Γ(Z, W),
…` crosses it once and everything below is a ring element. And `pow_mem`, not
`Submonoid.pow_mem`, is the one that takes a membership proof.

