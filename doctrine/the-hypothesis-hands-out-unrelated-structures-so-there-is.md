## "THE HYPOTHESIS HANDS OUT UNRELATED STRUCTURES, SO THERE IS NOTHING TO GLUE" — EVALUATE THE NATURALITY FIELD AT THE TAUTOLOGICAL POINT

(2026-07-31, `flt-lean-266`, on `nonempty_isRelPicOverAffines_of_restrict` in
`ModularCurve/RelativePicard.lean`.)

A representability structure in this development is `sheaf`/`classify` — an arbitrary
FUNCTION on points — plus a naturality field. A leaf whose hypothesis is `∀ V, Nonempty
(IsRelPicOf … (pstr ∣_ V))` therefore carries, after choice, one such function per `V`, and
the docstring said so at length and correctly: *"two structures on the same `pstr ∣_ V` need
not agree — replace `sheaf` by `fun p => modDual (sheaf p)` and every field survives — so the
local `sheaf`s differ by an automorphism of the functor and there is nothing to glue along."*
Every clause is true. The task prompt repeated it in bold as the reason the cut sits where it
does, and told me to read it *"before you start — it will save you a wasted attempt"*.

**The repair is one formal step and nobody had taken it.** The structure has a `sheaf_pre`
field, and the object it is about has a TAUTOLOGICAL point (`𝟙 P`, read as a `P`-point of `P`
over its own structure morphism). Evaluate `sheaf_pre` there:

    RelPoint.pre p.1 p.2 (tautological) = p          -- `Subtype.ext (Category.comp_id _)`
    sheaf_pre p.1 p.2 (tautological)    : sheaf p ~ p^* (sheaf tautological)

so **ANY ONE such function is the pullback of a single universal object**, namely its own
value at the tautological point, and `inj`/`surj` transfer to that pullback by transitivity
and symmetry of the relation. The unrelated FUNCTIONS become pinned OBJECTS — a universal
sheaf per affine open — which is step 1 of every classical gluing argument, and it cost
fifteen lines.

**So the observation and the obstacle are about different things, and the docstring conflated
them.** "The classifying functions differ by an automorphism of the functor" is true and does
not matter; what a gluing argument needs is objects, and the objects are canonical up to the
same automorphism, which rigidification then kills. Whenever a leaf's docstring blames a
`Nonempty` hypothesis for handing out incomparable data, **look for a naturality field and a
tautological/identity point before believing it** — in a functor-of-points development there is
almost always one, and Yoneda is exactly the statement that it pins everything.

Two riders from the same run, both about how to report this kind of work.

* **CASH IN a route note's "these fields are immediate", even when you cannot close the leaf.**
  This one said `invertible` and `sheaf_pre` are "immediate from that description" once the
  classifying function is pinned to `p ↦ p^* poin`. They are: `invertible` is
  `isInvertibleSheaf_modPullback`, and `sheaf_pre` is `curveBaseChangeMap_comp` +
  `modPullbackCompIso` + `relPicEquiv_of_iso`, four lines, first try. Three of the five fields
  of the target structure are now theorems and no future prover will look at them again. A
  field a docstring calls immediate is a field nobody has actually written; writing it is
  cheap and permanent.
* **A RECUT that leaves the count at 1 → 1 must say so in the commit subject AND in the
  docstring**, with what got smaller. Here: the leaf stopped receiving `IsRelPicOf` structures
  and started receiving universal sheaves, and the two hypotheses are EQUIVALENT — one
  direction proven and consumed, the other one-line and not in Lean because nothing needs it —
  which is what lets the old faithfulness audit be inherited rather than re-run. Say WHY it
  transfers; an audit labelled "inherited" with no argument is the failure mode this file
  already records.

**And the residual obligation that no earlier note in that file named: TRANSPORT.** The
hypothesis lives in the local world (`RelPoint (pstr ∣_ V) gV`, `curveBaseChange
(curveBaseChangeProj strX V.ι) gV`) and the conclusion in the global one (`RelPoint pstr g`,
`curveBaseChange strX g`); bridging them is `isPullback_morphismRestrict` plus pullback
pasting, compatibly with the projections so the equivalence relation crosses. Three successive
route notes call those two sublemmas "routine" and "not stated as a leaf because nothing
consumes them" — they are routine and they are also, now, the first thing the leaf owes. When
a note dismisses a sublemma with "nothing consumes it", check whether the cut you are about to
make is the thing that consumes it.

