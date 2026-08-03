## "LEFT OPEN FOR WANT OF TIME, NOT FOR WANT OF A ROUTE" IS THE ONE ROUTE NOTE TO BELIEVE — and the missing dictionary is usually eight lines
(2026-08-02, `flt-lean-159`, `ModularCurve/PoleOrderValuation.lean`, closing
`exists_sub_smul_poleOrd_lt` outright.)  This file spends pages on route notes being
hypotheses written before anyone tried.  There is a recognisable exception and it is worth
naming, because it is the cheapest leaf on the board: **a route written by the agent who had
just BUILT the surrounding machinery, naming the two or three mathlib declarations by name,
and saying explicitly that the leaf is open for want of time.**  That one is usually exact.
Here the cut's docstring said the route was `Scheme.Hom.stalkClosedPointTo` plus the section
`zeroSection ab ≫ f = 𝟙`, and it was, verbatim; the leaf closed in one run with no residue.
**The discriminator is who wrote it.**  A route note attached to a leaf by someone DECLINING
it ("this needs a theory we do not have") is the unreliable kind that the sections below are
about.  A route note attached by the person who cut the leaf OUT of a proof they had just
finished is a piece of their own working knowledge — they know which mathlib lemma the
neighbouring steps ran on.  Read the cut commit before pricing the leaf.
### THE `Scheme.ord`-TO-`Ring.ord` DICTIONARY, WHICH MATHLIB DOES NOT STATE
`AlgebraicGeometry.Scheme.ord` (`Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`, the order
of vanishing at a codimension-one point) is defined through `Scheme.ordHom`, which is defined
as `Ring.ordFrac (X.presheaf.stalk z)`, which is defined through `Ring.ord` — the LENGTH of
`R ⧸ (x)`.  Nothing relates the two ends, so every leaf about `Scheme.ord` reads as opaque.
**It is eight lines, and the reason it is eight lines is proof irrelevance.**  `ordHom` is
`haveI : Ring.KrullDimLE 1 …; Ring.ordFrac (X.presheaf.stalk z)`; the `haveI` supplies a
`Prop`, so the instance the definition uses and the one instance search finds are DEFEQ, and
one `show` crosses the gap:
    lemma schemeOrd_algebraMap (hO : Order.coheight O = 1) {x : A.presheaf.stalk O} (hx : x ≠ 0)
        {n : ℕ} (hn : Ring.ord (A.presheaf.stalk O) x = n) :
        Scheme.ord (algebraMap (A.presheaf.stalk O) A.functionField x) O = n := by
      haveI : Ring.KrullDimLE 1 (A.presheaf.stalk O) := krullDimLE_of_coheight_le hO.le
      have hne : … ≠ 0 := fun h => hx (IsFractionRing.injective _ _ (by simpa using h))
      rw [Scheme.ord_eq_iff hO hne]
      show Ring.ordFrac (A.presheaf.stalk O) _ = _      -- <- the whole trick
      rw [Ring.ordFrac_eq_ord _ hx]
      exact Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hx) hn
With it, a `Scheme.ord` statement at a point whose stalk is a DVR becomes
`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` plus `Ring.ord_mul_of_isUnit_left`,
`Ring.ord_pow`, `Ring.ord_of_irreducible` and `Ring.ord_le_ord_of_dvd` — ordinary algebra.
Note `schemeOrd_algebraMap` needs NO discrete-valuation hypothesis, only `coheight O = 1`.
`IsFractionRing (X.presheaf.stalk x) X.functionField` and `IsDomain (X.presheaf.stalk x)` are
already instances for an integral scheme, so `IsFractionRing.div_surjective` writes any
element of the function field as a ratio of stalk elements with no work.
### A "RESIDUE FIELD AT A SECTION IS `K`" STATEMENT ROUTES THROUGH GLOBAL SECTIONS
There is no morphism from `K` to `𝒪_{X,O}` and none between `𝒪_{X,O}` and the function field
except the specialisation map, so the two `K`-algebra structures cannot be compared directly.
`Γ(X, ⊤)` maps to BOTH, and `Scheme.algebraMap_germ_eq_germToFunctionField` is a `simp` lemma
identifying the two routes.  So the shape is: build the constant global section
`(Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop : K ⟶ Γ(X, ⊤)`, then germinate it at `O`
and at the generic point, and compare each side against `Γ(X, ⊤)` rather than against the
other.  `hstr`-type hypotheses (`ι ≫ f = Spec.map (algebraMap K R)`) are consumed exactly once,
by `Scheme.Hom.comp_appTop` plus `appTop_Spec_map`, on global sections.
**And `ρ ∘ ιK = id` makes `IsLocalHom` unnecessary.**  The classical statement is "the residue
map is local, so its kernel is `𝔪`".  When you have a SECTION, the cheaper route is: `ρ` is
surjective onto a field, so `RingHom.ker ρ` is maximal, so it IS the maximal ideal —
`IsLocalRing.ker_eq_maximalIdeal ρ (fun k => ⟨ιK k, hsec k⟩)`, one line, no local-hom
bookkeeping anywhere.
### TWO CATEGORY-THEORY TRAPS THAT COST FOUR OF THE ~15 ITERATIONS
* **`eqToHom_refl` and `Functor.map_id` DO NOT FIRE on the `f ⁻¹ᵁ ⊤ = ⊤` transport that
  `Scheme.germ_stalkClosedPointTo` leaves behind**, even though the two opens are
  definitionally equal.  The tell is the `unusedSimpArgs` linter reporting them as unused simp
  arguments while the goal is unchanged.  What works is the `appLE` calculus:
  `Scheme.Hom.app_eq_appLE` then `Scheme.Hom.appLE_map_assoc` then
  `AlgebraicGeometry.appLE_top_top_eq_appTop` (the last is this project's own, in
  `CurveAffineComplement.lean`).  Mathlib's own `Spec_stalkClosedPointTo_fromSpecStalk` is
  proved the same way, which is where to look for the idiom.
* **`rw [← Category.assoc]` reassociates the OUTERMOST pair, which is never the one you
  want.**  In `a ≫ (b ≫ (c ≫ d))` it produces `(a ≫ b) ≫ (c ≫ d)`, so a subsequent
  `rw [h]` for `h : a ≫ b ≫ c = …` still fails.  Put `@[reassoc]` on your own helper and use
  the generated `h_assoc`; that is exactly why mathlib carries `appLE_map_assoc` and
  `map_appLE`.  Alternatively state the `have` in the already-composed form you need
  (`f.appTop ≫ g.appTop ≫ iso.hom = iso.hom` rather than `f.appTop ≫ g.appTop = 𝟙`), which
  costs nothing and removes the reassociation step entirely.
### AND THE THROUGHPUT NOTE: 6 SECONDS PER ROUND, ON A FILE THAT TAKES 93
The scratch module that `public import`s the target and restates everything under primed names
ran at **6 s** per iteration against **93 s** for one `lake env lean` of the target — and the
finished text transplanted into the real file compiled first try, with the module's own build
a 13 s replay.  Seed first (`git diff --stat $(cat ~/.flt-release-lake/sha) HEAD -- Fermat/`
empty ⇒ `rsync -a --delete ~/.flt-release-lake/build/ /scratch/chend-flt/flt-lean-N/.lake/build/`,
13 s here) and the scratch loop is available immediately.
