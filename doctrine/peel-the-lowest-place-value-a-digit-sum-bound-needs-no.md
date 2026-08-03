## PEEL THE LOWEST PLACE VALUE — a digit-sum bound needs no Frobenius invariance
(Same run, and it is what took the node from two leaves to one.) A recurring shape:
a subadditive `t : ℕ → WithTop ℚ` must be bounded by the base-`ℓ` digit sum,
`t(a) ≤ s_ℓ(a)`, from a base case. The obvious recursion is the digit recursion
`a = a₀ + ℓ·a₁`, and it forces a SECOND input, because the `a₁` branch needs
`t(ℓ·b) ≤ t(b)` — Frobenius invariance, which in this development is a genuine
extra leaf (mathlib's `gaussSum_frob` is stated under `CharP` on the TARGET ring
and is inapplicable when the target has characteristic `0`).
**Recurse on `a ↦ a − ℓ^j` instead, where `ℓ^j` is the lowest place value
occurring in `a`** — i.e. `j` is the `ℓ`-adic valuation of `a`, so `a = ℓ^j · b`
with `ℓ ∤ b`. Then
    s_ℓ(a) = s_ℓ(b),   s_ℓ(a − ℓ^j) = s_ℓ(b − 1) = s_ℓ(b) − 1,
so subadditivity against the base case AT `ℓ^j` closes the step in one case with
no second branch. The two digit facts are elementary and are worth writing once:
`s_ℓ(ℓ^j · c) = s_ℓ(c)` (induction on `j` over `s_ℓ(0 + ℓ·c) = s_ℓ(c)`) and
`ℓ ∤ c → s_ℓ(c) = s_ℓ(c−1) + 1`.
What this costs is that the base case is now needed at every `ℓ^j` rather than at
`1` alone — which is FREE when, as here, the classical proof of the base case
re-runs the same computation at each `j` anyway. **So the question to ask is not
"which recursion is prettier" but "does the base case generalise along the
recursion's step for free?"** If it does, absorbing the transport into the base
case is one leaf instead of two. `Nat.ordProj_mul_ordCompl_eq_self` and
`Nat.not_dvd_ordCompl` are the pin's names for the split.
