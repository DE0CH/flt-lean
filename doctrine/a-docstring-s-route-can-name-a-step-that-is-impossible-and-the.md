## A DOCSTRING'S ROUTE CAN NAME A STEP THAT IS IMPOSSIBLE — AND THE LEAF STILL TRUE

(2026-07-31, `exists_lowerRamificationData_phi_one_le`.) The leaf's own docstring ended with a
"WHAT A PROVER MUST NOT DO" paragraph that prescribed the elementwise contradiction and closed:
*"it needs `X` to have `L`-valuation exactly `1` — which is where the 'totally ramified' half of
the construction is actually consumed."* That sentence is wrong twice over, and each way is a
different trap:

* **Not achievable.** The level `L` is constrained from below — it must contain the fixed field of
  the *prescribed* open subgroup `N`, whose ramification index may be divisible by the residue
  characteristic. `v_L(π^{1/M}) = e(L/Kᵥ)/M` then cannot be `1` for any `M` prime to `ℓ`. A prover
  who takes the sentence at face value spends the task trying to arrange something no choice of
  `M` can arrange, and is one step from reporting the leaf FALSE.
* **Not needed.** Generalising the elementwise lemma from "a uniformizer" to "`x = unif ^ e * u`
  with `u` a UNIT" makes the exponent `e` irrelevant: the correction factor `(1 + unif·a)^e` is
  `≡ 1 mod unif` whatever `e` is. The obstruction lived entirely in the route.

**The discriminating question, and it is cheap: is the awkward requirement forced by the
STATEMENT, or only by the ROUTE the docstring happens to describe?** Here the statement never
mentions a uniformizer; only the sketch did. Docstrings in this development are written by whoever
CUT the leaf, from the argument they had in hand — they are a hypothesis about how to prove it,
carrying exactly as much authority as a rival cut would. FALSITY AUDITS still outrank you (a
statement claim); a route sketch does not (a proof claim).

Corollary, generalisable beyond this file: **when an elementwise argument seems to need an element
of exact valuation `1`, try the normal form `x = unif ^ e * u` instead.** That factorisation is
available from the `LowerRamificationData` axioms alone (`unif_spec` strips factors,
`eq_zero_of_forall_pow_dvd_integralClosure` makes the stripping terminate), and it is the honest
formal shape of the classical step "`σ ∈ G₀` acts trivially on the residue field, so the unit
cofactor contributes nothing". It is now
`LowerRamificationData.exists_unif_pow_mul_isUnit`.

