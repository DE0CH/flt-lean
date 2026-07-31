---
name: flt-transport-the-twins-recut
description: Before attacking a Γ₀/Γ₁ (or any twinned) leaf, diff it against its twin — a recent RECUT of the twin is often the whole task, and transporting it costs an hour and shrinks the leaf permanently
metadata:
  type: project
---

`X0.lean` and `X1.lean` carry twinned statements (`…_isWeightTwoEigenform` /
`…_isWeightTwoEigenformOn_gamma1`, and the same for the isotypic-quotient
chain). When a leaf in one file resists, the first move is not to attack it but
to **read its twin's current source**: the twin may have been recut since the
task was queued, and the cut transports.

Instance, 2026-07-31. `isIntegral_coeff_of_isWeightTwoEigenformOn_gamma1`
(Shimura's algebraicity for `Γ₁(N)`, general `n`) was dispatched as an atomic
leaf gated on the integral homology `H₁(X_1(N), ℤ)` — theory that exists nowhere
in this repo, in mathlib at this pin, or in `~/cs/FLT`. Its `Γ₀` twin
`isIntegral_coeff_of_isWeightTwoEigenform` had been **proven the day before**,
over a strictly smaller leaf at a PRIME plus multiplicativity and the two Hecke
recursions. Transporting that cut made the `Γ₁` general-`n` statement PROVEN too,
in one session, leaving only `isIntegral_coeff_prime_of_isWeightTwoEigenformOn_gamma1`.

**Why the transport is nearly free, and what the one real difference costs.**
The `hecke`/`atkin` fields of `IsWeightTwoEigenformOn` differ from
`IsWeightTwoEigenform`'s only by a factor `χ (p : ZMod N)` at `p ∤ N`. That
factor is a CONSTANT through every induction, so it rides along in
`linear_combination`/`ring` and changes nothing structurally — the `Γ₀` proof
scripts transplant essentially verbatim. The only genuinely new ingredient is
`IsIntegral ℤ (χ (p : ZMod N))`, which is unconditional: `MulChar.map_nonunit`
sends non-units to `0`, and `MulChar.pow_card_eq_one` read at a unit gives
`χ(u)^|Mˣ| = 1`, so `IsIntegral.of_pow` finishes. No hypothesis on `χ` needed.

Two details that generalise beyond this pair:

* **Side conditions are often DERIVED, not assumed.** The prime-power step needs
  `N ≠ 0` only inside the `¬ p ∣ N` branch — where `p ∣ 0` makes it free. So the
  recursion lemma carries no level hypothesis and `hN` survives only on the leaf.
* **State the transported lemmas at the WIDEST binder the proof supports** (free
  `G`, free `χ`) — but only for the lemmas that are CONSEQUENCES of the eigenform
  fields. The leaf itself must keep `G := Gamma1GL N`, because at `G = ⟨T⟩` the
  level-`0` degeneracy satisfies every field with a non-integral `a 2`.

Related: [[flt-one-citation-two-bases]], [[flt-two-leaves-may-be-one]],
[[flt-cleaner-statement-harder-proof]].
