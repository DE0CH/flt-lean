---
name: flt-ord-nonneg-means-in-the-stalk
description: "`0 ≤ Scheme.ord g x` ⟺ g lies in the stalk at x is absent from mathlib and is ~25 lines; it is now Fermat.PoleOrder.exists_algebraMap_eq_of_ord_nonneg."
metadata: 
  node_type: memory
  type: project
  originSessionId: c676a19e-84e7-4cb5-898f-60f019c575a0
  modified: 2026-08-02T11:51:02.816Z
---

(2026-08-02, `flt-lean-158`.) Mathlib's `Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`
has `ord_mul`, `ord_add`, `ord_of_isUnit`, `le_ord_iff`, `ord_eq_iff` — and **not** the
statement that `0 ≤ ord_x g` means `g` is in the image of `𝒪_{X,x} → K(X)`. That is what
every gluing/extension argument about a rational function needs.

It is ~25 lines, from three mathlib pieces:

* `ValuationRing.isInteger_or_isInteger (R) (g)` — `g` or `g⁻¹` is in the DVR (note the
  fraction field is IMPLICIT; passing it explicitly is an arity error);
* `ord g + ord g⁻¹ = ord 1 = 0` with both summands `≥ 0`
  (`Ring.ordFrac_ge_one_of_ne_zero` through `Scheme.le_ord_iff` at `n = 0`) forces both to
  vanish;
* `Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` then makes the preimage a unit,
  so `g` is the image of its inverse.

Now `Fermat.PoleOrder.exists_algebraMap_eq_of_ord_nonneg` in
`Fermat/FLT/ModularCurve/PoleOrderValuation.lean`, stated for an arbitrary `X` at a point
of coheight one — **reuse it rather than re-deriving**. `Order.coheight x = 1` is
load-bearing: at any other point `ord` is identically `0` and the hypothesis says nothing.
It belongs in `Fermat/FLT/Mathlib/AlgebraicGeometry/`; it is where it is because no second
consumer existed, and it names nothing from that file, so the hoist is verbatim.

**Companion trap: `Nonempty ↥(⊤ : X.Opens)` does not synthesize**, even with `IsIntegral X`
(hence `Nonempty X`) in scope — and it is what `Scheme.germToFunctionField ⊤`,
`Scheme.ord_of_isUnit` at `U = ⊤` and `exists_germToFunctionField_eq_of_forall_isInteger`
all want. Do NOT write the instance: `Nonempty ↥(⊤ : X.Opens)` and the `[Nonempty U]`
binder elaborate to different terms (`↥⊤` against `↥↑⊤`) and a hand-written instance
silently fails to match. Use the repo idiom
`haveI : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩` inside the proof,
and phrase your own STATEMENTS with `X.presheaf.germ ⊤ x trivial`, which needs no instance
and is proof-irrelevantly the same term, so `exact` crosses the gap for free.
