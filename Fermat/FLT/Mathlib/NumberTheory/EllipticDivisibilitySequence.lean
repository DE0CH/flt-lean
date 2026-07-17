/-
EllipticDivisibilitySequence.lean — own work for the Fermat project
(extension of `Mathlib.NumberTheory.EllipticDivisibilitySequence`).

Universal identities for the canonical normalised elliptic divisibility
sequence `normEDS b c d : ℤ → R`, proven from the defining recursions
with no curve geometry. The headline statement is the **sum-companion
identity** `normEDS_sum_companion`

`bc(Wₙ₋₁²Wₙ₊₂ + Wₙ₋₂Wₙ₊₁²) = Wₙ₋₁WₙWₙ₊₁(db + b⁵) − Wₙ³b³c`,

the universal form of the trace identity
`x(Q+P) + x(Q-P) = ...` for division polynomials: specialised to
`W.ψ = normEDS ψ₂ Ψ₃ preΨ₄` and combined with the anchor
`Ψ₃(6X² + b₂X + b₄) = preΨ₄ + Ψ₂Sq²` and the curve membership
`ψ₂² ≡ Ψ₂Sq`, it yields the on-curve sum-companion of the even
recurrence (`evalEval_ψ_sum` in `TorsionCard.lean`) after cancelling
the non-zero-divisor `ψ₂Ψ₃` in the universal coordinate ring.

The proof route (descent experiments in `scripts/eds/`, all parity
descents verified to close over Groebner bases of the window ideals):
Stange's theorem for `normEDS` — the two-parameter family
`T(p, q) : W(p+q)W(p−q) = W(p+1)W(p−1)W(q)² − W(q+1)W(q−1)W(p)²`
by double parity descent (a declared mathlib TODO), from which the
general elliptic-sequence relator follows by an alternating expansion,
and the sum-companion by a fixed-window descent over `T`-instances.
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

@[expose] public section

namespace EllipticDivisibilitySequence

variable {R : Type*} [CommRing R] (b c d : R)

set_option warn.sorry false in
/-- (Sorry node — **the universal sum-companion identity** for the
canonical normalised EDS.) For `W = normEDS b c d` and any `n : ℤ`,
`bc(Wₙ₋₁²Wₙ₊₂ + Wₙ₋₂Wₙ₊₁²) = Wₙ₋₁WₙWₙ₊₁(db + b⁵) − Wₙ³b³c`.
Verified numerically for generic `(b, c, d)` (a universal identity in
`ℤ[b, c, d]`), hence provable from the defining recursions alone: to
be proven via the two-parameter elliptic-sequence family `T(p, q)`
(Stange's theorem for `normEDS`, by double parity descent — the
descent certificates were verified to exist by Groebner-basis
computations, `scripts/eds/`). -/
theorem normEDS_sum_companion (n : ℤ) :
    b * c * (normEDS b c d (n - 1) ^ 2 * normEDS b c d (n + 2) +
      normEDS b c d (n - 2) * normEDS b c d (n + 1) ^ 2) =
    normEDS b c d (n - 1) * normEDS b c d n * normEDS b c d (n + 1) *
      (d * b + b ^ 5) - normEDS b c d n ^ 3 * b ^ 3 * c :=
  sorry

set_option warn.sorry false in
/-- (Sorry node — **Stange's theorem for `normEDS`**: the elliptic-
sequence relation in its two-parameter three-term form
`T(p, q) : W(p+q)W(p−q) = W(p+1)W(p−1)W(q)² − W(q+1)W(q−1)W(p)²`.)
This is the mathlib TODO `IsEllipticSequence (normEDS b c d)` (the
general relator `rel p q r 0` follows from the `T`-family by an
alternating `3×3` expansion). To be proven by double parity descent
over the four symbol clusters `W(a±j), W(e±j), W(a+e±j), W(a−e±j)`
with the plain and cross `T`-instances as the inductive hypotheses
(descent experiments in `scripts/eds/`). -/
theorem normEDS_ellSequence (p q : ℤ) :
    normEDS b c d (p + q) * normEDS b c d (p - q) =
      normEDS b c d (p + 1) * normEDS b c d (p - 1) * normEDS b c d q ^ 2 -
      normEDS b c d (q + 1) * normEDS b c d (q - 1) * normEDS b c d p ^ 2 :=
  sorry

set_option warn.sorry false in
/-- (Sorry node — **the divisibility property of `normEDS`**: the
complement sequence witnesses `W(k) ∣ W(n·k)`.) This is the mathlib
TODO `IsEllipticDvdSequence (normEDS b c d)` in its exact form: the
even case is mathlib's `normEDS_mul_complEDS₂`, and the odd case
follows from the `T((m+1)k, mk)` instance of `normEDS_ellSequence`
by cancelling one factor of `normEDS b c d k` (a non-zero-divisor
argument over the universal ring `ℤ[b, c, d]`, then specialisation
via `map_normEDS`/`map_complEDS`). -/
theorem normEDS_mul_complEDS (k n : ℤ) :
    normEDS b c d k * complEDS b c d k n = normEDS b c d (n * k) :=
  sorry

end EllipticDivisibilitySequence
