## AN UNCONSUMED HANDOFF LEMMA IS EVIDENCE YOUR CUT IS ON THE WRONG SEAM
(2026-08-02, `flt-lean-43`, landing `HANDOFF-flt-lean-266-relpic-transport.md` into
`ModularCurve/RelativePicard.lean`.) This project forbids free-floating declarations, so
verified work with no consumer gets parked in a root-level `HANDOFF-*.md` — and the handoff
correctly says "paste it in as part of the recut that consumes it". What no note says is
that **which of the handoff's declarations your recut consumes is a TEST of the recut.**
The transport here is six declarations: two point maps `RelPoint (pstr ∣_ V) gV ⇄ RelPoint
pstr (gV ≫ V.ι)`, their two round trips, and the curve comparison plus its projection
identity. My first recut stated the leaf's new hypothesis over LOCAL points — the obvious
choice, because it is what the local hypothesis already hands you — and it compiled green.
It consumed **three of the six**; the two round trips and one point map had no consumer, so
landing them would have been exactly the free-floating code the handoff was parked to avoid.
Restating the same predicate over GLOBAL points (`RelPoint pstr (gV ≫ V.ι)`, restricted by a
one-line `relPointRestrictOpen`) consumed **all six** — and the second version is better for
every other reason too: the leaf's hypothesis is now in the same vocabulary as its conclusion
(`RelPicClassifiesOverAffines`, which quantifies over global points), so a prover attacking
the residue never meets a local/global mismatch at all. Same leaf count, same proof length,
one extra definition.
**So: after drafting a recut, list the handoff's declarations and check each has a consumer.
An unconsumed one means the seam is in the wrong place — almost always because you cut on the
side the HYPOTHESIS is phrased in, rather than the side the CONCLUSION is phrased in.** The
general rule it instantiates: *put the bridge in the derived half, and state the residual leaf
in the conclusion's vocabulary.* It is also the cheapest available check that a decomposition
is honest, because it is mechanical and needs no mathematics.
Three riders, all measured on the same run.
* **A handoff's "the one further piece this still needs" is an absence claim, and it decays
  at the target file's edit rate.** This one named `relPicEquiv_modPullback` generalised to an
  arbitrary comparison morphism as the single missing input. It was **already proven**, as
  `relPicEquiv_modPullback_of_comm`, 800 lines above the leaf — landed for an unrelated
  cluster (`IsRelPicOf.ofIsPullback`) *on the same day the handoff was written*. One `grep`
  for the CONCLUSION's shape rather than for the name found it. Same family as
  [[flt-inventory-audits-understate-what-exists]], with the shortest possible fuse: the
  author had read the file that morning.
* **Two propositionally equal presentations of one morphism are a choice about WHERE the
  transport cost lands — make it deliberately and record it.** `(pstr ∣_ V) ≫ V.ι` and
  `(pstr ⁻¹ᵁ V).ι ≫ pstr` are equal by `morphismRestrict_ι`. The first keeps every point
  transport in the bridge definitional; the second is what a gluer wants when identifying
  `X ×_S (pstr ⁻¹ᵁ V)` as an OPEN of `X ×_S P`. Picking the first puts ONE
  `morphismRestrict_ι` rewrite in the gluing proof; picking the second would have needed an
  `eqToHom` transport in the STATEMENT, because `rw` cannot reach a morphism that occurs only
  in a helper `def`'s inferred type argument. State which you chose and why, or the next owner
  will "simplify" it back.
* **`simp` fails on `pullback.lift` for TWO independent reasons at this pin, and fixing one
  leaves the goal looking untouched.** `pullback.lift_fst`/`lift_snd` are `@[reassoc]` but not
  `@[simp]` (already recorded); *and* `curveBaseChange`/`curveBaseChangeProj` are `abbrev`s, so
  a goal can carry `pullback.snd strX V.ι` on one side and `curveBaseChangeProj strX V.ι` on
  the other and no lemma matches. Name the `lift` lemmas **and** put the abbrevs in the simp
  set; with only one of the two the reported goal is verbatim the input.
**And the reconnaissance that decides the residue, so nobody repeats it (2026-08-02):
`CategoryTheory.Pseudofunctor.IsStack` has ZERO instances anywhere in mathlib at this pin** —
not for sheaves of modules, not for anything, so there is not even a worked example to copy.
`Mathlib/CategoryTheory/Sites/Descent/` gives the class, `IsStack.of_isStackFor` and
`isEquivalence_toDescentData`, and nothing inhabited. The fibred category itself DOES exist
(`AlgebraicGeometry.Scheme.Modules.pseudofunctor`, `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`)
but lands in `Adj Cat` where `IsStack` wants `Cat`, so even connecting them needs a
"take the left adjoint" pseudofunctor that is absent. **A leaf whose route is "descend sheaves
of modules along an open cover" should therefore NOT be priced at the stack machinery**: the
open-cover case is much weaker, and `Scheme.Modules.restrictFunctor` (with `restrictAdjunction`,
`restrictFunctorIsoPullback`, `restrictFunctorId`) is the vocabulary that exists for it.
