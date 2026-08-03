## A ROUTE THAT PRESCRIBES *GLUING TWO SECTIONS* IS USUALLY THE EXPENSIVE ONE — LOOK FOR A POINTWISE CRITERION IN THE SAME FILE
(2026-08-02, `flt-lean-158`, closing `nonneg_poleOrd_and_eq_zero_iff` in
`ModularCurve/PoleOrderValuation.lean`.) That leaf's route note said, in three numbered
steps, that the way to turn a chart function regular at `O` into a GLOBAL section is to take
the section on `U = A ∖ {O}`, take a section near `O`, check they agree on the overlap with
`AlgebraicGeometry.exists_res_eq_of_germ_eq`, and glue with
`AlgebraicGeometry.exists_glue_of_agree`. Both lemmas exist, both are proven, and the route
works. It is also the wrong one: **`exists_germToFunctionField_eq_of_forall_isInteger`, in
the same file, produces a section over `U` from a purely POINTWISE hypothesis** — *for every
`x ∈ U`, some element of `𝒪_{X,x}` maps to `f` in `K(X)`* — and at `U = ⊤` there are exactly
two kinds of point, the ones in the chart (germ of the chart function's own section) and the
one bad point (the hypothesis). No overlap, no agreement check, no second open, no cocycle.
**The generalisable check, and it is one `grep` of the file the route already names:** when a
route says *glue `a` on `V` to `b` on `W`*, look for a lemma in the same file whose hypothesis
is quantified over POINTS rather than over a pair of opens. In this development those exist
because somebody needed them for a different consumer, and they are named for that consumer,
so the route's author did not see them. The tell in the docstring is that the route names TWO
gluing lemmas — a pointwise criterion needs none.
Two smaller things from the same run, both reusable:
* **`0 ≤ Scheme.ord g x ↔ g lies in the stalk at x` is NOT in mathlib and is ~25 lines.**
  `ValuationRing.isInteger_or_isInteger` puts `g` or `g⁻¹` in the DVR; `ord g + ord g⁻¹ =
  ord 1 = 0` with both summands `≥ 0` (`Ring.ordFrac_ge_one_of_ne_zero` through
  `Scheme.le_ord_iff`) forces both to vanish; then
  `Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing` makes the preimage a unit and `g`
  is the image of its inverse. It is now `Fermat.PoleOrder.exists_algebraMap_eq_of_ord_nonneg`,
  stated for an arbitrary `X` at a point of coheight one — reuse it rather than re-deriving.
  `Order.coheight x = 1` is load-bearing: at any other point `ord` is identically `0` and the
  hypothesis says nothing.
* **`Nonempty ↥(⊤ : X.Opens)` does not synthesize**, even with `IsIntegral X` (hence
  `Nonempty X`) in scope, and it is what `Scheme.germToFunctionField ⊤`,
  `Scheme.ord_of_isUnit` at `U = ⊤` and `exists_germToFunctionField_eq_of_forall_isInteger`
  all want. Do NOT try to write the instance: the elaborations of `Nonempty ↥(⊤ : X.Opens)`
  and of the `[Nonempty U]` binder differ by a coercion (`↥⊤` against `↥↑⊤`) and a
  hand-written instance silently fails to match. Use the repo's existing idiom,
  `haveI : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩`, inside the proof,
  and phrase your own STATEMENTS with `X.presheaf.germ ⊤ x trivial` — which needs no instance
  and is proof-irrelevantly the same term, so `exact` crosses the gap for free.
