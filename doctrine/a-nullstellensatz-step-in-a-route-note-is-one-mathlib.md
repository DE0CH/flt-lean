## "A NULLSTELLENSATZ STEP" IN A ROUTE NOTE IS ONE MATHLIB DECLARATION — and the note's SOURCE of finiteness is usually the expensive one
(2026-07-31, `flt-lean-106`, closing `isFinite_fixedLocus_of_geomFixed` in
`FreyCurve/MazurTorsion.lean`.) That leaf carried a careful reconnaissance block — written the
day before, correct about the route, and correct that "both inputs of Zariski's main theorem are
already available" — whose one remaining paragraph read:
> passing from "finitely many `ℚ̄`-points" to "finitely many points" needs `Fix(v)` to be Jacobson
> and of finite type over `ℚ̄`, i.e. **a Nullstellensatz step**. Note `N = 0` must be handled.
Both halves of that sentence are avoidable, and each in a way worth generalising.
**1. The Nullstellensatz step is `AlgebraicGeometry.pointEquivClosedPoint`**
(`Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean`, a 2026 file this project had never cited):
for `f : X ⟶ Spec k` LOCALLY OF FINITE TYPE with `k` algebraically closed, the sections
`{p : Spec k ⟶ X // p ≫ f = 𝟙}` are in BIJECTION with `closedPoints X`. So "finitely many
`k`-points" IS "finitely many closed points", by `Finite.of_equiv`, with no ring theory at all.
The rest is three lines of topology: `LocallyOfFiniteType.jacobsonSpace f` makes `X` a
`JacobsonSpace`, `closure_closedPoints` says the closed points are dense, and a FINITE set of
closed points is closed — so it is its own closure, hence everything, hence `Finite ↥X`.
(`JacobsonSpace.discreteTopology`'s proof is that argument; copy its first three lines.)
**The standing rule this instantiates: a route note names a classical THEOREM where mathlib has
a DECLARATION, and the declaration is usually filed under the objects rather than the theorem.**
Grep `Mathlib/AlgebraicGeometry/` by DIRECTORY listing before pricing a "step" — `AlgClosed/`,
`Morphisms/QuasiFinite.lean`, `Morphisms/Finite.lean` and `Topology/JacobsonSpace.lean` are the
four files this whole class of argument lives in, and none of them contains the word
"Nullstellensatz".
**2. THE `N = 0` CASE DOES NOT ARISE, BECAUSE THE NOTE PICKED THE WRONG FIELD OF THE STRUCTURE.**
It routed the finiteness of `C(ℚ̄)` through `CyclicSubgroupOfOrder.geom_cyclic` — a cyclic group
of order `N` — which is infinite at `N = 0` and therefore forces a degenerate case split (and,
with it, `isEmpty_of_gamma0Datum_zero` and a page of group theory). The SAME structure carries
`isFinite : IsFinite (ι ≫ f)`, and `X0.lean`'s `finite_sections_of_isFinite` turns that into
`Finite {w : Spec K ⟶ C // w ≫ (ι ≫ f) = t}` directly, at every `N`. **When a route note
derives a finiteness from a COUNT, check whether the structure has a finiteness FIELD** — the
count is what the narrative is about, the field is what the proof wants, and the count is the
only one of the two that can degenerate.
The tell that the note was reading the narrative: `isEmpty_of_gamma0Datum_zero`, 30 000 lines
upstream, uses BOTH — `geom_cyclic` for the infinite group and `finite_sections_of_isFinite` for
the contradiction — because it is proving `N = 0` impossible. A consumer that only needs
finiteness needs only the second half of that proof.
**3. AFTER SPLITTING A CONJUNCTION, RE-READ EVERY "THIS HYPOTHESIS IS LOAD-BEARING" CLAIM PER
HALF.** The parent leaf's docstring argues at length that `hv` is load-bearing and the leaf FALSE
without it. The finiteness half consumes neither `hv` nor `hadd`: its witness (a `v` acting on
`ℚ̄` by a nontrivial field automorphism) makes `hgeom` VACUOUS rather than false, and step 1 above
then concludes `Fix(v) = ∅`, which is finite. The claim is true of the REDUCEDNESS half and of
the `τ_Q ∘ ψ` description. Keep the binders — `hv` occurs in `hadd`'s type and both are free at
the call site — but say in the docstring which half spends what; here `hadd` turned out to be
consumed only by reducedness and `hgeom` only by finiteness, i.e. the two hypotheses PARTITION
across the two halves, which is the strongest evidence available that a split was made along the
right seam.
### The Lean trap: a `Scheme` in a TOPOLOGY class needs `↥`, and the error names the wrong category
`closedPoints (equalizer v (𝟙 X))`, `JacobsonSpace (equalizer v (𝟙 X))` and
`Finite (equalizer v (𝟙 X))` all fail, because those classes want a TYPE and `equalizer …` is a
`Scheme`. The diagnostic is actively misleading — Lean re-elaborates `equalizer` in `Type`,
reports
    failed to synthesize instance of type class TopologicalSpace (equalizer ?m.574 ?m.579)
    Application type mismatch: 𝟙 d.E has type d.E ⟶ d.E but is expected to have type ?m ⟶ ?m
    in the application @equalizer (Type ?u.283) ?m ?m types ?m (𝟙 d.E)
and the `(Type ?u)` in the last line reads as a universe problem in the SCHEME equalizer. It is
not: write `↥(equalizer v (𝟙 X))` and it goes away. Two of the three iterations of this proof
went to that, one per occurrence, since each is reported only after the previous is fixed.
### Throughput note, measured
A scratch module that `public import`s `Fermat.FLT.ModularCurve.X0` and restates the target
under a primed name elaborated in **6 seconds**; `lake build Fermat.FLT.FreyCurve.MazurTorsion`
is ~25 minutes. The proof used NO name from `MazurTorsion.lean` itself — every ingredient was
mathlib's or `X0.lean`'s — so the scratch was a complete test and the transplant was verbatim.
**Check that first**: if the names your proof cites are all upstream, the scratch's usual
declaration-order blind spot does not apply to you at all.
