## A DEGENERATE-CASE ESCAPE HATCH IS THE ONE PART OF A TWIN TRANSCRIPTION THAT DOES NOT TRANSFER
(2026-07-31, the `Γ₀` → `Γ₁` transport of `X0.lean`'s integral-model trio into
`X1.lean`.) This development is built out of twin layers, and transcribing one onto the
other is a standard and highly productive move: five declarations came across here with
`Gamma0Datum` → `Gamma1Datum` and `IsBaseChangeOf` → `IsBaseChangeOfGamma1` and *nothing
else changed*, because none of those proofs ever looks at the level structure.
**The exception is the degenerate parameter, and it is exactly where the two problems
genuinely differ.** `X0.lean`'s `exists_unique_genericFibre_universal` carries no
positivity hypothesis and discharges `N = 0` by EMPTINESS: `isEmpty_of_gamma0Datum_zero`,
because a cyclic subgroup scheme of order `0` cannot exist, so the coarse space is empty,
hence initial, and the `∃!` is trivial. Copy that and you have written a false
justification: `Gamma1Datum` carries a `PointOfExactOrder`, whose clause is
`addOrderOf … = N`, and `addOrderOf x = 0` is the ordinary statement that `x` has
INFINITE order — which an elliptic curve over an algebraically closed field has in
abundance. So `Gamma1Datum 0 T` is INHABITED where `Gamma0Datum 0 T` is not, `[Γ₁(0)]` is
not a Katz–Mazur moduli problem, and the transcribed statement at `N = 0` is neither
supported nor refuted by anything in the tree.
That is the [[flt-third-outcome-strengthen-the-axioms]] situation, and the cheap response
is to EXCLUDE rather than gamble: add `0 < N` to the leaf. It weakens the leaf, so it
cannot make it false, and here it cost nothing at all — the only consumer already carried
`¬ ℓ ∣ N`, and every `ℓ` divides `0`.
**The general rule: when transcribing between twins, list the places the SOURCE proof
discharges a degenerate case, and re-derive each one at the target.** They are easy to
miss because they are usually a single `rcases … with hN | hN` branch inside an otherwise
mechanical proof, and because the transcription compiles perfectly without them — the
degenerate branch of the source is exactly the part you are NOT copying when the target's
version is a `sorry`. Grep the source for `Nat.eq_zero_or_pos`, `isEmpty_of_`,
`Subsingleton`, and `IsInitial`; those four cover most of them here.
Corollary about the leaf count, since it is the shape of this whole task: cutting the
trio took `X1.lean` from 24 direct sorries to 26. **One leaf became three and that is
DISCLOSURE.** What changed is that a single citation naming three classical theorems in
prose became three statements naming one theorem each, and that everything between them
and the node — the generic classifying map, its naturality, the coarse structure of the
generic fibre, the cusp-locus count and the three geometric fields — is Lean instead of
promise. Judge it by what is LEFT in each leaf, not by the delta.
