## TAKE NORMS AT THE FIRST STEP — a "root of unity, hence ±1" argument is an ABSOLUTE-VALUE argument
(2026-08-01, `flt-lean-126`, closing `isUnit_leadingCoeff_diag_of_eq_prod` — Kronecker's
leading coefficient for the modular polynomial, Cox Lemma 11.23 — in
`Fermat/FLT/Mathlib/NumberTheory/BinaryQuadraticForm.lean`.)
A leaf whose conclusion is `IsUnit c` for an integer `c` is very often proved classically as:
*compute `c` as a product of roots of unity; a root of unity lying in `ℤ` is `±1` (Kronecker)*.
Formalised literally that costs the whole cyclotomic layer — here `q^{1/d}`-Puiseux expansions
of `j((az+b)/d)`, the coefficients `−ζ_d^{−b}`, and Kronecker's theorem.
**`IsUnit c` for `c : ℤ` is `|c| = 1`, so pass to `‖·‖` before doing anything else and every
root of unity becomes `1` on the spot.** The three cases the leaf's docstring enumerated
(`a < d`, `a > d`, `a = d`, with coefficients `1`, `−ζ_d^{−b}`, `1 − ζ_a^{−b}`) collapsed to
the SINGLE statement `‖j(z) − j(t·z)‖·|q|^{max(1,a/d)} → 1`, proven by a two-sided squeeze
from `‖u‖e − ‖v‖e ≤ ‖u−v‖e ≤ ‖u‖e + ‖v‖e`. No root of unity and no Kronecker anywhere.
**The hypothesis that survives the collapse is the one that was load-bearing.** `hns :
¬ IsSquare N` is spent exactly once, ruling out `a = d` — which is precisely the case where
the two leading terms share a `q`-power and can cancel, i.e. where the squeeze has no room.
So the leaf's recorded `N = 4`, `N = 9` counterexamples become visible as the ONE step of the
proof that breaks. That is the shape to aim for: after a collapse like this, re-read where
each hypothesis is spent, and expect the count to be one.
**Two riders, and the first is the reason the leaf was affordable at all.**
* **A "shared prerequisite" stated as a `q`-EXPANSION is usually needed only to LEADING
  ORDER, and mathlib has leading orders.** The task priced "the `q`-expansion of `j` at a
  triangular point" as an unowned shared cost. What the whole argument consumes is
  `j(z)·q → 1` as `Im z → ∞` — and that is `E₄ → 1` divided by `Δ/q → 1`, both in the pin
  (`EisensteinSeries.E_qExpansion_coeff_zero` through the cusp function, and
  `ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow`). ~35 lines, no leaf. Before
  costing an expansion, write down the single limit the proof actually uses.
* **A quantity you would have to COMPUTE may be forced by the comparison instead.** The
  degree `D` of the diagonal is never computed here. Two limits — `‖P(j z)‖·|q|^D → ‖c‖` and
  `‖P(j z)‖·|q|^M → 1` with `M = ∑_t max(1, a/d)` — divide to give `|q|^{D−M} → ‖c‖`, and on
  a `NeBot` filter where `|q| → 0` that forces `D = M` and `‖c‖ = 1` (`D > M` sends it to `0`,
  hence `c = 0`, hence the polynomial is `0`, contradicting the second limit; `D < M` sends it
  to `∞`, which has no finite limit). So `M` is allowed to be an a-priori REAL number and no
  combinatorics about `ψ(N)` is needed. **Whenever two asymptotics of the same object are
  available, subtract them before computing either exponent.**
Mechanical notes worth keeping, all met in one afternoon on `atImInfty`:
`UpperHalfPlane.atImInfty` is `atTop.comap im`, so `Tendsto (fun z : ℍ => z.im) atImInfty
atTop` is literally `tendsto_comap` and it is `NeBot` by instance; a level-one modular form's
limit at the cusp is `ModularFormClass.analyticAt_cuspFunction_zero` composed with
`qParam_tendsto_atImInfty`, with `SlashInvariantFormClass.eq_cuspFunction` to congr (note the
`eq_cuspFunction` you want is in `SlashInvariantFormClass`, NOT `ModularFormClass`); and
`Tendsto.div` produces `(f / g)` rather than `fun x => f x / g x`, so a following
`filter_upwards` needs `simp only [Pi.div_apply]` before any `rw`.
