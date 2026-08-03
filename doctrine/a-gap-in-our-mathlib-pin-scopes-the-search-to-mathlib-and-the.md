## "A GAP IN OUR MATHLIB PIN" SCOPES THE SEARCH TO MATHLIB — AND THE ANSWER IS USUALLY IN `Fermat/`
(2026-07-31, `flt-lean-145`, and this is the **third** time the same node has been cut.)
A task prompt said: *"a search of the entire pin found NO implication `Smooth →
GeometricallyReduced` … confirm that before starting (it is a two-minute grep over
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`,
`Mathlib/RingTheory/Smooth/` and `Mathlib/AlgebraicGeometry/Geometrically/`)"*. Every word of
that was TRUE, the prescribed grep was run, and it confirmed the absence. The theorem was
nevertheless **already proven, sorry-free, on `main`, four days earlier**, in
`Fermat/FLT/Mathlib/AlgebraicGeometry/Morphisms/SmoothReduced.lean` — together with strictly
stronger statements the task did not ask for (smooth over a **domain**, not just a field). The
duplicate was built, verified green, axiom-audited clean, and thrown away.
**The trap is that the verification instruction is scoped, and the scope is wrong.** A
`Fermat/FLT/Mathlib/…` module is a mathlib-facing extension: it exists precisely *because* the
statement is absent from the pin, so "absent from the pin" is EVIDENCE THAT IT IS THERE, not
evidence that it is missing. Grepping mathlib harder can never find it, and every additional
mathlib grep raises confidence in a false conclusion. This is the same shape as the
self-certifying grep in the doctrine file, one level up: the *scope*, not the pattern, is what
is wrong.
**Two greps, both mandatory, before writing one line of a "missing from mathlib" module.**
They cost seconds and either one would have killed this task at minute two:
    grep -rn '<theConclusionYouIntendToProve>' --include=*.lean Fermat/
    grep -rln 'Fermat/FLT/Mathlib/' -e .            # i.e. read the mathlib-facing subtree's index
Grep for the **conclusion**, not for your intended declaration name — the existing copy is
called something else. Here `GeometricallyReduced` alone found it; so did
`isReduced_of_smooth_over_field`, which the existing file and the duplicate had picked
independently as the same name.
**The compiler says it too, but only at the consumer, and only after a full build.** The
duplicate compiled perfectly *in isolation*; the collision surfaced only as
    import … failed, environment already contains 'AlgebraicGeometry.isReduced_of_smooth_over_field'
    from Fermat.FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothReduced
after a 45-minute `lake build` of `X0.lean`. So a green `lake env lean` on your new module is
**no evidence at all** that it is not a duplicate — a duplicate module is green by
construction. Only wiring it into a consumer and building tests it, which is far too late.
**A duplicate is worse than no work: it is invisible to every frontier instrument** (see the
duplicate-cut section in the agent doctrine — the sorry count goes UP, not down), and it burns
a worker on a node that was closed. Note also that the prior deletion of this very node left a
note *in the file that used to carry it* —
`Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean` ends its account with *"Anyone
tempted to restate a smoothness-to-reducedness fact here should grep
`isReduced_of_smooth_over_field` first"* — which is exactly right and was invisible to anyone
not already reading that file. **A warning parked in the file where the duplicate used to live
does not reach the agent who is about to write the next one.** Warnings about duplication
belong HERE.
