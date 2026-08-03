## "THAT THEOREM HANDS BACK X" FAILS ONE LEVEL DOWN TOO — grep for a `_compat_` SIBLING before pricing the link
(2026-08-02, `flt-lean-80`, on `exists_variableChange_image_of_gamma0Model_isBaseChangeOf`.)
CLAUDE.md already records that a docstring's claim about what an upstream theorem *gives*
you must be checked against its CONCLUSION rather than its proof. The same defect stacks,
and a route note that survives the first check can die at the second.
That leaf's route is *"with the pin repaired the statement is true and its proof is the chart
comparison"*. The chart comparison needs the variable change to be **the one the two
Weierstrass charts induce**; the leaf was handed `∃ Cv, E'⁄ℚ̄ = Cv • (E⁄ℚ̄)`, which is not
that. So the route was unrunnable for a second, unrecorded reason on top of the `α`-gap
everyone had written about.
**The link was already proven upstream and simply not exported, twice over:**
* `Fermat.exists_coordinateRingAlgEquiv_compat_of_isWeierstrassModel` (`X0.lean`, PROVEN)
  concludes `Spec.map Ψ ≫ ι = ι'` — `Ψ` IS the identity of the total space read in the two
  charts;
* `Fermat.exists_linearAlgHom_of_isWeierstrassModel` (`X0.lean`, PROVEN) obtains its `Φ`
  from exactly that and returns `Φ := Ψ.toAlgHom` **with the compatibility dropped**;
* `Fermat.exists_variableChange_of_linearAlgHom` (`X0.lean`, PROVEN) then builds `V` from
  `Φ`'s coordinate shape and does not export `a = u²`, `b = u³`, `c = u² s` either.
So a five-line re-run of the middle theorem's own proof, keeping the conjunct, gives
`Fermat.exists_variableChange_chartCompat_of_isWeierstrassModel` — `V`, both open
immersions, the chart-compatible `Ψ`, its linear shape and the two `IsUnit`s. It compiled
**first try**, and it is stated DOWNSTREAM (in `MazurTorsion.lean`) rather than as a widening
of `X0.lean`, per the standing rule: re-derive downstream when the upstream module's
consumers are outside your cone.
**The cheap check this argues for: when a route needs "the map induced by the charts", grep
the upstream chain for a `_compat_` / `_compatible_` sibling.** In this development the
compatible version usually exists, is PROVEN, and is consumed only inside a proof body — so
it is invisible to anyone reading conclusions. `grep -n 'compat' <the upstream module>` is
the whole check.
Corollary on how to bank it: a proven bridge with no consumer is free-floating and forbidden
here, so land it by **moving it into the blocked leaf's binders**. Widening a leaf's
hypotheses can only weaken it, so the old faithfulness audit is inherited verbatim (say so)
— but the **NOT VACUOUS witness must be re-checked against the new binders**, because that
is the one thing extra hypotheses can break. Count unchanged, `1 → 1`; what changed is that
the residue is now the pin's `α`-gap plus one two-line statement widening, instead of an
unbounded "chart comparison".
