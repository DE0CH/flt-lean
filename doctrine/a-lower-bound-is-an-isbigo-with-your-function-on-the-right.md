## A **LOWER** BOUND IS AN `IsBigO` WITH YOUR FUNCTION ON THE **RIGHT** — which is why nobody greps for it
(2026-07-31, `flt-lean-171`, closing `exists_isBoundedAtImInfty_coeff_prod`.) The task prompt
named one step as *"THE ONE INPUT THAT IS NOT BOOKKEEPING"* — a lower bound `|Δ(z)| ≥ c|q|` for
`Im z` large — and prescribed a three-stage route for it: analyticity of
`UpperHalfPlane.cuspFunction 1 Δ` at `0`, plus `discriminant_qExpansion_coeff_one`, plus a
slope/`hasDerivAt_iff_tendsto_slope` argument to divide by `q`. It even said *"if that estimate
turns out to be the bulk of the work, consider cutting IT off as the leaf"*.
It is **one name in mathlib**:
    ModularForm.exp_isBigO_discriminant :
      (fun τ ↦ Real.exp (-2 * π * τ.im)) =O[atImInfty] Δ
proven there from `Δ = q ∏(1 − qⁿ)²⁴` and the product tending to `1`. The whole leaf then came
to ~150 lines of ordinary estimates and **the "one hard input" never existed**.
**The reason it is easy to miss is structural, not careless, and it generalises to every
growth/decay estimate in analysis.** Mathlib does not state bounds as inequalities with names
like `le_`, `ge_`, `lower_bound` or `bounded_below`; it states them as `IsBigO` along a filter.
And an `IsBigO` is *asymmetric*: an UPPER bound on `f` is `f =O g`, a LOWER bound on `f` is
`g =O f` — **`f` on the RIGHT**. So a search for "a lower bound on `Δ`" fails twice over: the
wrong vocabulary, and the wrong side of the relation. Grep instead for the OBJECT with `=O`
either side of it:
    grep -rn "isBigO.*discriminant\|discriminant.*isBigO\|=O\[atImInfty\]" <the file that defines it>
and read the whole declaration list of the file that DEFINES the object rather than the file
where the theory lives. Both of this leaf's inputs (`exp_isBigO_discriminant` and the cusp-form
decay `CuspFormClass.exp_decay_atImInfty`) are in `Mathlib/NumberTheory/ModularForms/`,
adjacent to `Δ`'s definition and nowhere near anything named "bound".
Same family as [[flt-inventory-audits-understate-what-exists]] and
[[mathlib-states-point-facts-as-morphism-properties]]: a route note prices the construction its
author would have BUILT, and is silent about the spelling the library actually uses.
### The conversion that this class of leaf always needs: `=O[atImInfty]` ⟶ a bound on a HALF-PLANE
An `=O[atImInfty]` bound is applied *at `z`*. The estimate here had to be applied at
`(a z + b)/d` — a DIFFERENT point, whose imaginary part is `a·Im z/d` — so "eventually in `z`"
is the wrong shape and no amount of `filter_upwards` reaches it. One lemma fixes it, and it is
worth having by name:
    lemma eventually_atImInfty_iff {p : ℍ → Prop} :
        (∀ᶠ z in atImInfty, p z) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
      UpperHalfPlane.atImInfty_mem _
Composed with `Asymptotics.isBigO_iff` it turns every `=O[atImInfty]` into
`∃ C A, ∀ w, A ≤ w.im → ‖f w‖ ≤ C ‖g w‖`, i.e. a genuine statement about the half-plane
`{Im ≥ A}`, which is the only form that survives substituting a transformed point.
`UpperHalfPlane.isBoundedAtImInfty_iff` does the same job in the other direction for the
conclusion. **Whenever a leaf's estimate is consumed at a MOVED point, budget this conversion
first — it is what decides whether the proof is a filter argument or a real-variable one.**
Two smaller riders from the same proof, both about making a crude bound *uniform*:
* **Prove the coefficient bound `k`-INDEPENDENTLY.** The consumer needs one `m` serving every
  `k` at once, so the sharp `binom(n,k) M^{n−k}` is the wrong target; `(1 + M)^n` for all `k`
  falls out of one `Finset.induction_on` over `Polynomial.coeff_mul`'s antidiagonal, with
  `∑_{i ≤ k} ‖(X − C c).coeff i‖ ≤ 1 + ‖c‖` as the one-step input. Crudeness is not laziness
  here, it is what makes the induction close.
* **A ratio of two parameters that is bounded on both sides is what makes ONE threshold work.**
  On `triangularReps N` one has `1 ≤ a, d ≤ N`, so `a/d ∈ [1/N, N]`: the lower bound is what
  puts every triangular point inside the half-plane where the `j`-estimate holds (take
  `Im z ≥ N·A`), and the upper bound is what makes one exponential rate `e^{2πN·Im z}` serve
  every `t`. Check both directions before choosing the threshold; only one of them is obvious.
