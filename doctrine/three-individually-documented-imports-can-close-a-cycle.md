## THREE INDIVIDUALLY-DOCUMENTED IMPORTS CAN CLOSE A CYCLE

(2026-07-31, same release.) Release 28 assembled `X0 → IsogenySignature →
HyperellipticJacobian → X0` out of three merges, **every edge added by a different
branch, every edge carrying a comment at its own site explaining why it was safe** —
one of them stating outright "none of the four project modules below imports this one,
so no cycle is created", which was true when written.

`lake` reports this only as `build cycle detected`, and it takes down not just those
three modules but everything downstream — `X0.lean` could not be built at all, so no
agent dispatched into that file could verify anything. It is invisible to every check
in this file: no `sorry`, no error inside any declaration, and each branch is green on
its own base.

The edge to cut is the **dead** one, and there usually is one, because these edges
arrive with hoists: `IsogenySignature.lean` was created by hoisting Mazur steps 1–3 out
of `MazurTorsion.lean` and **inherited that file's import header verbatim**, including
`import Fermat.FLT.ModularCurve.HyperellipticJacobian` with a comment advertising a
declaration (`MazurLevel18.no_noncuspidal_point_on_smooth_model`) that stayed behind.
Neither that name nor anything else from the module occurs in its 14 655 lines.

**So when a hoist creates a new module, audit the copied import header — an unused
import is free until somebody closes a loop through it.** And when triaging a cycle,
grep each edge for actual usage before arguing about which one is architecturally
wrong; the dead edge is both the cheapest and the correct cut.

