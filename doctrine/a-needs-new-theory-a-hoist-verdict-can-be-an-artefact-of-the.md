## A "NEEDS NEW THEORY + A HOIST" VERDICT CAN BE AN ARTEFACT OF THE ROUTE, NOT OF THE STATEMENT

(2026-07-31, `flt-lean-15`, on `eq_two_or_eq_three_of_stableCyclic_j_eq_zero` /
`…_j_eq_1728` in `ModularCurve/X0.lean`.)

Three separate audit passes (2026-07-28, -30) recorded a MACHINERY survey on those two
leaves, by name, and it was accurate: closing them by the recorded route needed (a) a
HOIST of `MazurCMForm` and `classNumberOne_of_end_closure_eq_top` out of
`FreyCurve/MazurTorsion.lean`, which `public import`s `X0.lean` and therefore cannot be
cited from it; and (b) at `j = 0`, "a genuine generalisation of the encoding
(`ψ² = [−n] + b·ψ`)", because the conductor-`p` order `ℤ[pζ₃]` is not `ℤ[√−n]`. The two
`j`-values were split apart precisely because that survey showed their costs differed.

**Both requirements evaporated under a different proof of the same statement.** The
class-number half (`C` not `𝒪_K`-stable ⟹ `h(p²·disc K) = 1`) has an elementary
substitute: `C` and `ψC` are then distinct lines spanning `E[p]`, `G_K` acts by the SAME
scalar on both, so `det ρ|_{G_K} = α²`, and `det ρ = χ_cyc` (Weil pairing) forces every
element of `𝔽_p^×` to be a square. That needs `det_galoisRep_eq_cyclotomic`, which is
PROVEN, and lives in `EllipticCurve/WeilPairing.lean` — **which does not import `X0.lean`**,
so there is no hoist at all. Both leaves are now proven over ONE shared leaf; the frontier
went 2 → 1 and the `j = 0`/`j = 1728` asymmetry that motivated the split disappeared.

The tell, and it is checkable: **a machinery survey enumerates what the RECORDED argument
needs. It never asks whether the conclusion has a second proof.** So when a survey ends in
"hoist X and generalise Y", that is a report about one route, not a lower bound on the
leaf. Spend one pass looking for another argument before paying for the hoist — and note
the shape of the win here: the blocked module was blocked by an import CYCLE, and the
substitute route's module simply was not in the cycle. Check the import direction of the
alternative's dependencies early; it is a one-command discriminator between "expensive"
and "free".

### Corollary technique: NORMALISE OVER THE BASE FIELD, NOT OVER `ℚ̄`

The construction that made the above writable is worth copying verbatim. To get the CM
automorphism as an endomorphism of `(E⁄ℚ̄).Point` **carrying its Galois conjugation law**,
do NOT put `E⁄ℚ̄` into Weierstrass normal form over `ℚ̄`: the normalising variable change is
then irrational and the transport destroys the `hstab` hypothesis. `exists_smul_eq_quarticModel`
/ `…_sexticModel` are stated over an arbitrary `CharZero` field, so apply them **over `ℚ`**;
the change of variables is then `ℚ`-rational, `Affine.Point.equivVariableChangeBaseChange_galois`
makes the transport `Gal(ℚ̄/ℚ)`-equivariant, and every Galois hypothesis survives it unchanged.
The `ℚ̄`-only data (the root of unity) enters afterwards, as the `u` of a diagonal automorphism
of the *rational* normal form. Same pattern applies to any leaf that has to combine a normal
form with a Galois-stability hypothesis.

