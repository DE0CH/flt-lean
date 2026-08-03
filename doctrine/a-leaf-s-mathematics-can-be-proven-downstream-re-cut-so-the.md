## A LEAF'S MATHEMATICS CAN BE PROVEN DOWNSTREAM — RE-CUT SO THE RESIDUE IS EXACTLY WHAT A HOIST WOULD DISCHARGE
(2026-08-02, `flt-lean-160`, on `poleOrd_ne_one_and_exists_two_three` in
`ModularCurve/PoleOrderValuation.lean` — "the genus is one".)
That leaf carried the sharpest kind of absence audit: *"a Riemann–Roch theorem, a genus, or a
theory of divisors/linear systems on a curve, in `Fermat/`, `.lake/packages/mathlib` or
`~/cs/FLT`. Absent from all three as of 2026-07-31."* Two thirds of it survive re-running.
The `Fermat/` third was **false on the day it was written** —
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveGenus.lean` (`rrSet`, `ell`, `divisorDegree`,
`IsDivisorOn`, `IsCurveGenus`, `IsCurveGenus.unique` PROVEN, `exists_isCurveGenus` a leaf) is
dated the same day, as are `CurveDivisorDegree.lean` and `PrincipalDivisorDegree.lean`. The
standing rule ("a MISSING MACHINERY audit expires, but only its PROJECT half") is right; what
this instance adds is that the project half can be stale **at zero days**, because the fleet
lands modules in parallel with the audits that deny them. `ls` the plausible directory —
`Fermat/FLT/Mathlib/AlgebraicGeometry/` is 23 files — rather than grepping for the theory's
name; the file that has your theorem is named for somebody else's consumer.
**And the half that mattered more was not missing at all: it was PROVEN, DOWNSTREAM.** The
`genus ≥ 1` half — no function has a simple pole — is rigidity, *a rational curve maps
constantly to an abelian scheme*, and that is `exists_section_of_affineLine_toAbelianScheme`
in `ModularCurve/X0.lean`, PROVEN since 2026-07-28. `X0 → EllipticScheme → PoleOrderValuation`,
so the name is unreachable and the leaf was blocked by IMPORT DIRECTION, not by mathematics.
**THE MOVE THAT PAYS, AND IT IS NOT "NOTE THAT IT IS DOWNSTREAM": RE-CUT YOUR LEAF SO ITS
RESIDUE IS THE HYPOTHESIS THE DOWNSTREAM THEOREM CONSUMES, AND PROVE THE REDUCTION.** Here
that was ~90 lines and it is all pure algebra: a function with `poleOrd r = 1` generates the
chart (`L(n) = K[r]_{≤ n}`, strong induction on `(poleOrd s).toNat` over the file's own two
sibling leaves) and generates it FREELY (algebraic ⟹ unit ⟹ `poleOrd = 0`), so the residue
became `IsEmpty (Polynomial K ≃ₐ[K] R)` — no pole order, no `Scheme.ord`, no chart embedding,
no `hgen`. A successor now owes a block move out of `X0.lean` plus ~40 lines of `Spec`-of-an-
`AlgEquiv` assembly, instead of the genus of a curve. **A leaf whose statement is shaped to
be discharged by a hoist is a different task from one that merely mentions the hoist in prose.**
Two riders.
* **Say the count out loud.** This is `1 → 2` leaves. What is bought is that the two halves
  (rigidity; Riemann's inequality) share no technique and are separately dispatchable, and
  that one of them is now a relocation. Judge by what is LEFT in each leaf.
* **`IsCurveGenus strX g` BOUNDS NOTHING, and that will trap the next reader.** It is
  `∃ B, ∀ D, IsDivisorOn X D → B ≤ divisorDegree strX D → ℓ(D) = deg D + 1 − g`, and its own
  docstring says it does not assert the sharp `deg D ≥ 2g − 1` form. So `ℓ(2·[O]) = 2` cannot
  be read off it: an argument that needs small divisors must go through LARGE `n` plus a gap
  count (`ℓ(n[O])` = number of pole orders in `[0, n]`, one gap when `g = 1`, and the `genus
  ≥ 1` half says which gap it is).
