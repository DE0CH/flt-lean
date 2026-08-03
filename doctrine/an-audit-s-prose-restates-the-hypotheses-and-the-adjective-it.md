## AN AUDIT'S PROSE RESTATES THE HYPOTHESES, AND THE ADJECTIVE IT ADDS IS THE MISSING BINDER
(2026-08-02, `exists_boundarySubscheme_of_projectiveCompactification` in
`Modularity/MoretBailly.lean`.)  That leaf carried the strongest clean bill of health
this project's conventions can express — a conjunct-by-conjunct faithfulness audit,
one bullet per clause of the conclusion, ending
> **None of the four can fail, so this leaf is not one that will turn out to be FALSE
> AS STATED**
— and it was false, refuted by the empty scheme.  The audit's own second paragraph
opens *"`X̄` is a smooth proper geometrically irreducible curve over `ℚ` and `C` is a
**nonempty** open subscheme"*.  That word appears in the PROSE and in NO BINDER: `C`
was an arbitrary `Scheme`.
**So the check on any faithfulness audit is to diff its prose restatement of the
hypotheses against the binder list, adjective by adjective.**  An audit is written by
someone holding the intended instance in their head, so its opening sentence
describes that instance rather than the quantifier; every adjective the prose adds
and the binders do not is a candidate missing hypothesis.  This is the same family as
DECOMPOSITION DROPS A HYPOTHESIS and A DEGENERATE CASE DOES NOT TRANSFER BETWEEN
TWINS above, and it is worse than either, because an audit is what the next reader
consults *instead of* re-deriving — all four of this leaf's bullets are individually
true of the intended instance, so a reviewer checking the bullets finds nothing.
Three riders, each of which cost something here.
* **A nonemptiness binder elsewhere in the list is not the one you need, and its
  presence is what hides the gap.**  This leaf carries `hZ : (range j.base)ᶜ.Nonempty`,
  which reads as ruling out degeneracy; it rules out the OPPOSITE degeneracy, and
  `C = ∅` satisfies it most easily of all (the complement becomes everything).  When a
  statement names two objects, check nonemptiness of EACH.
* **`Scheme.emptyTo X` is an `IsOpenImmersion` INSTANCE at this pin** — `inferInstance`
  closes it — so "the empty scheme is not a legitimate `C`" is not available as a
  defence.  Any leaf quantifying over an open immersion `C ⟶ X` admits it.
* **The refutation was worth writing down even though the repair is one binder**, and
  the reason is the standing rule that a hypothesis can only WEAKEN a leaf: adding
  `hCne : Nonempty ↥C` cannot make a true leaf false, so the audit for the repair is
  short, and the whole cost of the run was the PROOF rather than the escalation.  The
  sole call site already held `hreal : HasRationalPoint fC (ULift ℝ)`, i.e. a morphism
  `Spec (ULift ℝ) ⟶ C`, so the discharge is four lines and no statement above the leaf
  moved.  Check the caller before reporting a refutation as a blocker.
### The companion absence claim: a verdict scoped to the NAME you would have chosen
Same leaf, and it is why the leaf read as expensive.  Its docstring priced the work at
the one construction it believed missing:
> what it needs is the REDUCED INDUCED CLOSED SUBSCHEME … (searched 2026-07-31:
> `Mathlib/AlgebraicGeometry/` has `IsClosedImmersion` and `Scheme.restrict` for OPENS,
> but no `Scheme.reducedInduced`)
`Scheme.reducedInduced` really is absent.  The construction is not:
`Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean` has
`Scheme.IdealSheafData.vanishingIdeal (Z : Closeds X)`, whose **own docstring** says
*"the reduced induced scheme structure on the closed set is the quotient of this
ideal"*, and `IdealSheaf/Subscheme.lean` turns any `IdealSheafData` into a scheme with
a closed immersion (`subscheme`, `subschemeι`, `range_subschemeι`, plus an
`IsClosedImmersion` instance).  Two rewrites give the leaf's first two conjuncts, and
the docstring's suggested fallback — build `Z` by hand as `Spec` of a product of
residue fields — was never needed.
**Mathlib routinely files a construction under the machinery it is built from rather
than under the classical name of the thing constructed, so grep for what the object
IS.**  `grep -rn 'reduced induced' Mathlib/` finds it in one call, in the docstring of
the definition itself, while every search for `reducedInduced` returns nothing for
ever.  And when you WRITE such a verdict, quote what you searched FOR and not only
where — "searched for `reducedInduced`" invites the fix; "searched
`Mathlib/AlgebraicGeometry/`" reads as exhaustive and is what the next reader re-runs.
**The rest of the leaf was likewise cheaper than advertised, and all of it came off
the shelf**: `Flat (ι ≫ fX)` is `inferInstance` (mathlib has
`[Subsingleton Y] [IsIntegral Y] → Flat f`, and `Spec ℚ` is a one-point integral
scheme — the audit's "free at this base" was exactly right); `IsFinite (ι ≫ fX)` is
Zariski's main theorem in the form `IsFinite.of_isProper_of_locallyQuasiFinite`, whose
quasi-finiteness side is `locallyQuasiFinite_iff_finite_preimage_singleton` against a
FINITE `Z`; and the finiteness of `Z` is this project's own
`finite_of_isClosed_of_ne_univ_of_topologicalKrullDim_le_one`, in a module
`MoretBailly.lean` already imports.  Total: 45 lines, four scratch rounds at ~10 s.
**Before costing a geometric leaf at a construction, list the four conjuncts and grep
each separately** — here three of the four were one lemma apiece and the fourth was an
instance.
