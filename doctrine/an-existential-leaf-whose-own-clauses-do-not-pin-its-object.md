## AN EXISTENTIAL LEAF WHOSE OWN CLAUSES DO NOT PIN ITS OBJECT CANNOT BE SPLIT — MAKE THE OBJECT A `def` FIRST, AND THAT IS USUALLY THE CHEAP HALF

(2026-07-31, `flt-lean-259`, on `exists_poleOrderValuation_of_affineComplement` in
`ModularCurve/EllipticScheme.lean`.) That leaf asked for a pole order `deg : R → ℕ`
with nine clauses, of which three are the genus (`deg r ≠ 1`, `∃ x, deg x = 2`,
`∃ y, deg y = 3`) and the rest are valuation theory. The obvious split — prove the
valuation clauses, leave the genus — is **illegal**, and its predecessor had recorded
exactly why: `deg' = 2 · deg` satisfies every valuation clause *and* `deg' r ≠ 1`, so a
standalone leaf saying *"for ANY `deg` with those clauses, `∃ x, deg x = 2`"* is FALSE.
A leaf that is stuck like this reads as atomic and is not.

**The repair is to stop quantifying and BUILD the object**, so the residual leaves can
name it. That is the whole of the trick, and the surprise is how cheap the building is:
`poleOrd r := -ord_O (φ r)` over `Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`'s
`Scheme.ord`, plus multiplicativity, the ultrametric inequality and the `ℤ → ℕ`
normalisation, came to ~200 lines and closed six of the nine clauses. The three
survivors are now *named classical theorems* (`Γ(A,𝒪_A) = K`; the residue field at a
section is `K`; the genus is one) instead of one existential no citation could discharge.

**`Mathlib/AlgebraicGeometry/OrderOfVanishing.lean` was imported NOWHERE in `Fermat/`**
before this, and it is the engine for every "order of vanishing / pole order / divisor
of a function" leaf in the tree: `Scheme.ord`, `ord_mul` (needs `coheight z = 1`),
`ord_add` (needs `[IsDiscreteValuationRing (X.presheaf.stalk z)]`), `ord_zero`,
`ord_of_isUnit`, `ord_le_smul`. Two things it needs that this project already owns:
`isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one` and
`isIntegral_of_smoothOfRelativeDimension_of_geometricallyConnected`, both in
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`.

Three reusable pieces that had to be written and are worth knowing before re-deriving
them (all in `Fermat/FLT/ModularCurve/PoleOrderValuation.lean`):

* **the chart-to-function-field embedding**, which is three composable isos and not the
  fight it looks like:
  `(Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (ι.appIso ⊤).inv ≫ A.presheaf.germ (ι ''ᵁ ⊤) (genericPoint A) hgen`.
  Take the membership `hgen` as a PROOF ARGUMENT, not as a `[Nonempty ↥U]` instance —
  the instance form fails to synthesize at every use site and the coercion in its
  statement (`Nonempty ↥↑U`) is not what you will write;
* **`not_isField_stalk_of_ne_genericPoint`** — on an integral scheme the stalk at a
  non-generic point is not a field. Mathlib has only the CONVERSE
  (`isField_stalk_of_closure_mem_irreducibleComponents`), and this direction is the
  hypothesis every DVR lemma wants. Eight lines:
  `ringKrullDim_stalk_eq_coheight` + `ringKrullDim_eq_zero_of_isField` +
  `Order.coheight_eq_zero` (`↔ IsMax x`) + the generic point being above everything, with
  `Specializes.antisymm … .eq` for the `T0` step. **The points of a scheme carry only a
  `Preorder`, not a `PartialOrder`** — `le_antisymm` fails with a bare
  `failed to synthesize PartialOrder ↥A` — so `Inseparable.eq` is the closing move;
* `coheight_eq_one_of_ne_genericPoint`, read backwards off the DVR through
  `IsDiscreteValuationRing.ringKrullDim_eq_one`. This is `ord`'s own precondition.

Two accounting notes, because the count moves the wrong way. **1 leaf → 3 leaves is the
right trade here and must be reported as such**: what the count cannot show is that ~200
lines of plumbing are gone for good and that each survivor has a name in a textbook.
And **check the clauses for redundancy while you have them unfolded** — `deg 0 = 0`
follows from the submodule clause (`0 ∈ L 0`) and `⨆ n, L n = ⊤` is automatic for any
`ℕ`-valued `deg`, so two of the nine were never obligations at all.

Mechanical trap that cost two rounds: **`refine ⟨fun r => g r, …⟩` leaves the remaining
goals with an UNREDUCED application `(fun r => g r) x`**, and `rw`/`omega` then fail on a
goal that prints correctly. `show` the beta-reduced form at the head of each branch (or
`beta_reduce`). This is the plain-lambda cousin of the strict-implicit case already
recorded under `A STRICT-IMPLICIT LAMBDA DOES NOT BETA-REDUCE`; a hypothesis in the same
shape is fixed for free by `have h2 : <reduced form> := h1`, since the two are defeq.

