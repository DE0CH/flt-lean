## N USES OF A SUBSINGLETON SHORTCUT ARE NOT N OBLIGATIONS — PORT THE SHORTCUT, NOT ITS CALL SITES

(2026-07-31, `flt-lean-81`, on the `ℚ ↝ F` port that
`exists_projGroupLawOverField_geomFibreAddEquiv` is waiting for.)

A development written over a special base accumulates a *shortcut lemma* that is true
only there — here `Fermat.hom_ext_spec_rat`, "any two morphisms `X ⟶ Spec ℚ` are equal",
because `ℚ →+* A` is a subsingleton. `EllipticScheme.lean` invokes it **59 times**
(comment-stripped), and every cost estimate of the port has been quoted as "59 vanished
justifications", "each of those is a step whose justification disappears entirely rather
than one that needs rewriting", and — in one docstring — a per-range breakdown of where
the 59 sit. All of that is true and all of it is the wrong unit of work.

**The right question is: what does the shortcut COMPUTE, and is that computable over a
general base?** `hom_ext_spec_rat` is used almost everywhere in one syntactic position,
the obligation of `Limits.pullback.lift c.toHom d.toHom _`, i.e.
`c.toHom ≫ projToSpec E = d.toHom ≫ projToSpec E`. Over `ℚ` it holds because the target
is `Spec ℚ`. Over `F` it holds because **both sides are computable**: `ProjCoords.toHom`
is `Proj.fromOfGlobalSections c.ringHom _`, and mathlib's
`Proj.fromOfGlobalSections_toSpecZero` computes any such composite. One five-line lemma
(`WeierstrassCurve.Projective.fromOfGlobalSections_comp_projToSpec`, now in
`ProjectiveModelOverField.lean`) turns all 59 sites into `congrArg` applied to
`c.base = d.base`. The port's real residue is the threading of that ONE hypothesis
(11 `base_eq` sites, 14 `ProjCoords.ext` sites), not 59 commuting squares.

Three transferable rules:

* **Before costing a port by counting shortcut uses, find the shortcut's general-base
  replacement and check whether it is one lemma.** It usually is, because the shortcut
  exists precisely where a *universal property* is available and was not needed. The
  tell is that the uses are all in the same syntactic position — grep the call sites and
  look at their SHAPE, not their number.
* **A docstring can state the right reduction and still be unusable, because the lemma it
  needs does not exist.** `Fermat.ProjCoords`'s own docstring already said "all 77 follow
  from `base_eq` alone" and named `c.base = d.base` as the thing to thread. That is a
  correct plan that nobody could execute, because "follow from" was doing the work of an
  unwritten lemma. **When you read a plan of that shape, write the missing lemma first —
  it is small, it is checkable in isolation, and until it exists the plan is a guess.**
* **Land the brick with a consumer.** Free-floating code is banned here, and a
  general-base lemma has no consumer until the port happens. The cheap consumption is to
  REPROVE the special case over it: `projInfty_comp_projToSpec` had its own bespoke
  `fromOfGlobalSections_toSpecZero` invocation, which is now deleted in favour of the
  general lemma. Look for the existing special case before inventing a consumer.

Corollary about what "progress" looks like on a leaf whose residue is a six-thousand-line
port: **the count does not move and should not be expected to.** What moved here is that
six of the ten fields of `ProjGroupLawOverField` (`e`, `i`, `he`, `hi`, and the two
compatibilities inside `hunit`/`hinv`) are now REAL CODE via
`ProjGroupLawOverField.ofMul`, so the leaf names one morphism and four equations. Judge by
what is LEFT in the leaf.

