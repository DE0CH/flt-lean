## A TEMPLATE'S STRUCTURE IS FORCED BY ITS ANALYTIC TOOL, NOT BY THE MATHEMATICS — check before transcribing it
(2026-08-01, `flt-lean-169`, closing `numEllipticThree_le_analyticOrder_norm_rho`
and `numEllipticTwo_le_analyticOrder_norm_I` in `ModularCurve/X0.lean`.)
Both leaves' docstrings, and the task prompt built from them, prescribed the same
route: *"partition the cosets into the orbits of the order-`3` stabilizer `⟨ST⟩`
… an orbit of size `1` is exactly an elliptic point"*, pointing at
`numCusps_le_order_qExpansion_norm` as the template — which really does partition
`Γ₀(M)\SL(2,ℤ)` into `⟨T⟩`-orbits, with a setoid, fibre `Finset`s, an
`orbitProd`, and a `Finset.prod_nbij'` permutation argument, ~300 lines.
**The orbits are an artefact of the CUSP tool and are not needed at an interior
point.** At the cusp the analytic instrument is `UpperHalfPlane.qExpansion` at
width `1`, which demands `1`-PERIODICITY — and an individual translate
`f ∣[2] r⁻¹` is not `1`-periodic while the product over a `⟨T⟩`-orbit is. That is
the whole reason the orbit is the unit there. At `ρ` and `i` the instrument is
`analyticOrderAt`, which is ADDITIVE over a finite product of functions analytic
at the point (`analyticOrderAt_mul`, one `Finset.cons_induction`) with no
side condition whatever. So the decomposition is just *the cosets*, the
`⟨ST⟩`-FIXED ones contribute `≥ 2` and the rest `≥ 0`, and no orbit relation is
ever defined.
**So before transcribing a template: ask which of its steps its ANALYTIC TOOL
forces, and re-derive them for yours.** The mathematics ("the orbits are the
points of `X₀(M)` above `ρ`") is correct and is what a textbook says; it is not
what the Lean proof needs, and copying it costs a setoid, a fibre family and a
permutation argument for nothing.
### The classical congruence is needed only `e` steps deep, and those are DERIVATIVES
Both docstrings listed as missing machinery *"the local congruence
`ord ≡ −k/2 (mod e)` at an elliptic point of order `e`"*. That congruence in full
is a change to a local coordinate at the elliptic point plus a primitive-root-of-
unity computation. **A LOWER bound needs only its first `e` steps**, and mathlib
turns those into derivative evaluations:
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf : AnalyticAt 𝕜 f z₀) :
      (n : ℕ∞) ≤ analyticOrderAt f z₀ ↔ ∀ i < n, iteratedDeriv i f z₀ = 0
So `2 ≤ ord_ρ F` is exactly `F ρ = 0 ∧ deriv F ρ = 0`, and each is one line of
algebra off the functional equation `Φ = (Φ ∘ m) · denom(·)^(-k)`:
* at `z₀`: `F z₀ = F z₀ · lam^(-k)`, so `F z₀ = 0` as soon as `lam^(-k) ≠ 1`;
* differentiating, with `F z₀ = 0` killing the second product-rule term and
  `deriv m z₀ = det/lam²`: `F' z₀ = F' z₀ · lam^(-(k+2))`.
At `k = 2`, `lam = ρ + 1` is a primitive SIXTH root of unity (`(ρ+1)² = ρ`), so
`lam^(-2) ≠ 1` and `lam^(-4) ≠ 1` and the bound is `2`; at `i`, `lam = i` and only
`lam^(-2) = −1 ≠ 1` is available, so the bound is `1`. **That is the whole of the
`2ν₃`-versus-`ν₂` asymmetry** the two docstrings insist is not a typo — it is one
extra root-of-unity clause, not a different argument.
**The pin has the ℍ↔ℂ derivative dictionary, and it is not where you would look.**
`Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean` carries
`hasStrictDerivAt_smul` (`deriv (g • ofComplex ·) τ = det / denom g τ ^ 2`),
`hasDerivAt_denom_zpow`, `analyticAt_smul`, `deriv_smul_ne_zero` and
`mdifferentiableAt_iff`. A search for the modular-forms module
(`NumberTheory/ModularForms/Derivative.lean`, which has the slash law for `D`
outright) is the natural one and is a dead end here — that module is NOT in
`X0.lean`'s import cone, while `Manifold.lean` is, and the four lemmas above are
enough to do it by hand. **Grep the cone before planning around a header edit.**
### Two mechanical notes
* **`λ` is a reserved token**, so `hλ` is not an identifier: `unexpected token
  'λ'; expected command`, reported at the *next* declaration. Name it `hden`.
* **Mathlib's `MDifferentiable.prod` is stated at `{ι : Type}`, universe `0`**, not
  `Type*`. A product lemma written over `{ι : Type*}` fails with a universe
  mismatch printing two `Finset.prod` applications that differ only in a universe
  argument. The coset space is at `Type 0`, so matching mathlib costs nothing.
* **A generator that attaches docstrings must not attach a SECOND one.** Inserting
  `/-- … -/` above a declaration that already had one gives `unexpected token
  '/--'; expected 'lemma'` — the orphaned-docstring shape this file warns about,
  manufactured by your own tooling. Strip existing docstrings first, and re-run
  `flt-comment-balance.py` after any scripted comment edit.
