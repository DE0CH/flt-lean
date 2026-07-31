---
name: flt-degenerate-case-does-not-transfer-between-twins
description: Transcribing a proof between the Γ₀/Γ₁ (or any) twin layers carries the mathematics verbatim but NOT the degenerate-case escape hatch — that is exactly where the two objects differ.
metadata:
  type: project
---

(2026-07-31, transporting `X0.lean`'s integral-model trio into `X1.lean`.) Five
declarations came across with `Gamma0Datum` → `Gamma1Datum` and `IsBaseChangeOf` →
`IsBaseChangeOfGamma1` and nothing else changed — none of those proofs looks at the level
structure. The one thing that did NOT transfer was the `N = 0` branch.

`X0.lean`'s `exists_unique_genericFibre_universal` needs no positivity hypothesis:
`isEmpty_of_gamma0Datum_zero` says a cyclic subgroup scheme of order `0` cannot exist, so
the coarse space is empty, hence initial, and the `∃!` is trivial. **The `Γ₁` analogue is
false.** `PointOfExactOrder`'s clause is `addOrderOf … = N`, and `addOrderOf x = 0` is
"`x` has infinite order" — abundant on an elliptic curve over an algebraically closed
field. So `Gamma1Datum 0 T` is INHABITED, `[Γ₁(0)]` is not a Katz–Mazur moduli problem,
and the statement at `N = 0` is neither supported nor refuted by anything in the tree.

**Why:** the degenerate branch is the one place a twin transcription is not mechanical,
and it is invisible — the transcription compiles perfectly without it, because the
target's version is a `sorry` and you were never copying a proof body there.

**How to apply:** when transcribing, list every degenerate case the SOURCE proof
discharges and re-derive each at the target. Grep the source for `Nat.eq_zero_or_pos`,
`isEmpty_of_`, `Subsingleton`, `IsInitial`. When the case is undecided, EXCLUDE it — an
added hypothesis weakens a leaf and cannot make it false. Here `0 < N` cost nothing: the
only consumer already had `¬ ℓ ∣ N`, and every `ℓ` divides `0`.

Related: [[flt-third-outcome-strengthen-the-axioms]], [[flt-transport-the-twins-recut]].
