## WHEN AN AUDIT REFUSES A CUT BECAUSE "IN THE DEGENERATE REGIME THE HYPOTHESIS CONSTRAINS NOTHING", CUT AT THE NON-DEGENERACY — NOT AT THE UNDER-CONSTRAINED OBJECT
(2026-08-01, `flt-lean-184`, closing `exists_commutingHeckeAlbaneseFamily_values`
in `ModularCurve/X0.lean` and `exists_commutingHeckeAlbaneseFamilyGamma1` in
`ModularCurve/X1.lean`.)
Both leaves carried a long, correct audit refusing the obvious cut:
> for distinct primes `ℓ, ℓ' ∤ N`, any two additive `a, b : J ⟶ J` pinned by
> `IsHeckeAlbaneseRecipe` at `ℓ` and at `ℓ'` satisfy `a ≫ b = b ≫ a`
>
> is **NOT KNOWN TO BE TRUE**, and cutting it would manufacture a possibly-false
> leaf with two live consumers — at a datum `d` where no valid decomposition data
> exists the recipe constrains `a` at `d` not at all, and `End(J) ⊇ M₂(ℤ)` refutes
> the conclusion for unconstrained `a, b`.
That verdict is right, and it is right about MORE than the shape it names: it
kills **every** `∀ a b pinned, …` statement, including the DIFFERENCE form
`post (a≫b) (aj[d] − aj[d']) = post (b≫a) (aj[d] − aj[d'])` that the task
prompt and three docstrings proposed as the cut to make. Differencing cancels
the base-point constants; it does nothing about a datum the recipe never
reaches. So the prescribed decomposition would have landed a possibly-false
leaf, and the previous owner's refusal to land it was correct for a reason its
own notes did not quite state.
**THE CUT THAT IS AVAILABLE IS THE ONE THAT ASSERTS THE NON-DEGENERACY.** What
makes the `∀`-form possibly-false is exactly that valid data may not exist. So
state a leaf that SAYS IT DOES, and say nothing about `a` and `b`:
> for every `ℚ̄`-point `y` of `Y` and distinct primes `ℓ, ℓ' ∤ N` there EXIST a
> datum `d` classifying `y`, enumerations of the cyclic `ℓ`- and `ℓ'`-subgroups
> by `Γ₀`-isogenies out of `d`, the same at each quotient, and the two double
> sums of Abel–Jacobi images agree.
It is an EXISTENTIAL over moduli data; no endomorphism of `J` occurs in it; it
is the classical correspondence plus Diamond–Shurman Prop. 5.2.4; and it cannot
be refuted by a partially-vacuous pin because it is the very statement whose
absence made that refutation possible. In the fully vacuous regime it is
vacuously true for a *different* reason worth writing into such a leaf: with
`Gamma0Datum N ℚ̄` empty the empty scheme is a cocone for the moduli problem, so
`IsCoarseModuliY0.universal` forces `Y = ∅` and there is no `y`.
**The generalisable rule.** An audit of the form *"in the degenerate regime the
hypothesis `H` constrains the object `x` not at all, so `∀ x, H x → P x` may be
false"* is telling you where the cut is: **assert the non-degeneracy as its own
leaf, phrased so that the quantified object does not appear.** The `∀`-form and
the audit's own repair are then both unnecessary, and the residue is a statement
a citation can discharge. Weakening the conclusion (to differences, to points,
to a subset of the arities) never helps, because the defect is in the
QUANTIFIER, not in the conclusion.
**THE CONSTANT LOOKS LIKE IT NEEDS A BASE CHANGE AND DOES NOT — CHECK WHICH
BASE IT LIVES OVER.** Expanding `post (a ≫ b) (aj[d])` by two recipes leaves
`m • e_b + post b e_a`, and the mirror expansion a different constant; their
difference `γ` does not visibly vanish. The obvious repairs are both wrong or
expensive: running the whole argument on DIFFERENCES `aj[d] − aj[d']` (which
cancels `γ` and is what three docstrings and the task prompt proposed) leaves a
leaf still quantified over the unconstrained `a, b`; and proving `γ = 0` by
"the difference is constant on a dense set, hence constant" reads as needing a
base change to `ℚ̄`, because a constant is a `ℚ̄`-point. **It is not: `e_a` and
`e_b` are relative points over `𝟙 SpecQ`, so `γ` is a `ℚ`-POINT and the constant
morphism it defines is a morphism `X ⟶ J` over `ℚ`.** Density then identifies
the two composites up to `γ`, and EVALUATING AT THE ABEL–JACOBI BASE POINT `o`
— where `aj o = 0` and both composites are additive — forces `γ = 0`. So the
residual geometry is PURE DENSITY, *two morphisms `X ⟶ J` agreeing at every
`ℚ̄`-point of `Y` are equal*, with no group law, no `IsJacobianOf` and no
differences in it. **Before pricing a "constant on a dense set" argument at a
base change, look at which base the constant is a point of.**
**AND PIN THE ARITY, or the constant is not a constant.** `γ` contains
`m • e_b` with `m` the arity of the first enumeration. The whole argument turns
on that being independent of `d`, so a leaf that leaves `m` existential is
unusable even though it looks stronger-by-being-vaguer. Classically `m = ℓ + 1`
always, so writing `Fin (ℓ + 1)` into the leaf costs its prover nothing and is
what makes the consumer close. Same family as the standing "an
existentially-quantified constant carries no analysis": here it is an
existentially-quantified *arity*, and it carries the failure of the whole
argument.
**Two riders from the same run.**
* **The residual scheme theory is level-free and should be stated ONCE.**
  `IsX0Compactification` and `IsX1Compactification` are field-for-field the same
  structure apart from `coarse`, so the density half —
  `eq_of_forall_sub_aj_algClosPoint`, *two additive endomorphisms of `J` agreeing
  on all `aj[y] − aj[y']` for `ℚ̄`-points `y` of `Y` are equal* — takes the five
  geometric fields as loose arguments, mentions no moduli problem, lives in
  `X0.lean` and is consumed unchanged by `X1.lean`. So the `Γ₁` transcription is
  ONE leaf, not two: 2 leaves became 3, not 2 became 6 as the prescribed
  `(D)/(I)/(S)` decomposition would have. **And a queued task and a green
  handoff for exactly that density statement already existed** — the entry
  reading *"prove the DENSITY statement that step 2 of … needs"*, resting on
  `HANDOFF-flt-lean-296-dense-field-points.lean` at the repository root, which
  compiles against MATHLIB ALONE. Grep `~/.flt-loop/queue1` for your leaf's name
  before designing its residue: the shape somebody has already prepared for is
  the shape to cut to.
* **`o` is used TWICE and for two different things, and only one of them is
  obvious.** It makes the density statement non-vacuous (with `Y` empty the
  hypothesis is vacuous and the conclusion false), and it is what kills the
  constant. Both consumers supply the required `ℚ̄`-point of `Y` for free — at
  `Γ₀` from the `d₀` the leaf already carries, at `Γ₁` from the `by_cases` on
  `Nonempty (Gamma1Datum N ℚ̄)` its assembly runs anyway.
**Process note, measured: the whole 300-line decomposition was developed at 5
SECONDS per iteration** in a scratch that `public import`s the target module and
restates the three new declarations under primed names with `sorry` bodies (the
"stub the siblings" recipe), against ~13 minutes for one `lake env lean` of
`X0.lean` at 119 000 lines. Both assemblies compiled on the first attempt in the
real files. The one thing the scratch cannot check is DECLARATION ORDER, so
every name the assembly uses was `grep -n`'d against the insertion line first —
which is what caught that `IsJacobianOf.eq_of_post_aj_eq`, `RelPoint.post_comp`
and `IsAdditiveOn.comp` all sit ~20 000–36 000 lines BELOW the leaf and had to
be re-proven locally rather than hoisted (one line each except the rigidity,
which is eleven).
