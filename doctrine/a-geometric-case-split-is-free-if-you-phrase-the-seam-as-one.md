## A GEOMETRIC CASE SPLIT IS FREE IF YOU PHRASE THE SEAM AS ONE `Prop` — `by_cases`, not semicontinuity
(2026-07-31, `flt-lean-10`, decomposing
`exists_birationalOver_affineLine_of_relPicEquiv_sectionIdeal_of_sqZero` in `X0.lean`.)
A leaf whose recorded strategy is *"split on the genus / rank / dimension of the fibres and
argue separately in each case"* looks like it needs the invariant to be well behaved on the
base — locally constant, semicontinuous, constant in a flat family. That leaf's own re-audit
spent a paragraph establishing exactly this ("the genus is locally constant on `Spec R₀`, so
the two branches exhaust the case distinction even when `Spec R₀` is DISCONNECTED"), and the
paragraph is correct.
**It is also unnecessary, and phrasing the seam as a single `Prop` over the WHOLE base deletes
it.** Define `HasGenusZeroFibre strX g : Prop` as *"SOME field-valued point of the base has a
genus-`0` fibre"*, and `by_cases` on it: `em` splits it, the disconnected case costs nothing,
and no statement about components is ever made. Local constancy would be needed only for a
formulation quantified over connected components — which is the formulation to avoid.
So: **before proving anything about how a fibrewise invariant varies, ask whether the case
split can be stated as one existential over the base.** The two branches then receive
`h : P` and `h : ¬P` and nothing has to be shown to exhaust anything.
**AND THE BRANCH THAT NEEDS AN INPUT SHOULD RECEIVE IT BY THE SHAPE OF THE PREDICATE.** That
leaf's docstring carried a warning in bold: the genus-`0` branch is closed by the rational
point that `x` reduces to, so *"a proof that produces `k` at a prime OUTSIDE the image of `g`
cannot close that branch even though the statement permits any `k`"*. The obvious reading is
that a prover must CHOOSE a prime carefully and carry a compatibility. It does not: quantify
the existential over field-valued points of the BASE `T` (`r : Spec K ⟶ T`) rather than of
`S`, and the branch hands back `k := r ≫ g`, which is in the image of `g` by construction and
receives `x` as `RelPoint.pre r rfl x`. The warning is discharged structurally, with no extra
hypothesis and no choice.
**The generalisable form: when a docstring warns that an OUTPUT must be compatible with an
INPUT, look for a formulation in which the output is BUILT from the input.** A compatibility
that cannot be violated needs no clause, and a clause you do not state is one no consumer has
to discharge.
Two smaller things from the same cut, both reusable in this tree:
* **A predicate over an object carrying DERIVABLE instance arguments can be made total by
  `∃`-binding the instances.** `AlgebraicGeometry.IsCurveGenus` takes `[IsIntegral X]` and
  `[IsLocallyNoetherian X]`; on a fibre of a proper smooth geometrically connected curve both
  are theorems, but a `def` has no hypotheses to derive them from. Write
  `∃ (hi : IsIntegral Z) (hl : IsLocallyNoetherian Z), @IsCurveGenus … hi hl …` — both classes
  are `Prop`s, so proof irrelevance makes the choice immaterial and no consumer can exploit
  it. The alternative (instance binders in the `∀`/`∃` telescope) elaborates too, but the `@`
  form is what a `by_cases`/`obtain` on the predicate destructures cleanly.
* **State the geometric half over an ABSTRACT curve, not over the fibre.** The first draft of
  the genus-`0` leaf took `x : RelPoint strX k` and concluded about
  `curveBaseChangeProj strX k`; restating it as a curve `cstr : C ⟶ Spec K` with a SECTION
  (`s ≫ cstr = 𝟙`) removed `RelPoint`, `curveBaseChange`, `RelPicEquiv` and the base `S` from
  the statement, made it relocatable to `CurveGenus.lean`, and connected it directly to the
  divisor layer's own `residueDegree_eq_one_of_section`. The assembly pays one lemma for it,
  `relSection_comp_curveBaseChangeProj`, which was already proven.
