## A char-`p` leaf blocked by an "imperfect base": two dodges that keep working

(2026-07-31, closing `InvariantCoarseRing.lean`'s last leaf, which its own docstring had
declared needed "new mathematics — a separability / linear-disjointness argument over
`k(ι)^{1/p^∞}`". It needed neither.)

* **`[PerfectField k]` in a lemma is almost always a proxy for "the extension at hand is
  separable".** Replacing it by `[Algebra.IsSeparable k A]` breaks NO existing call site —
  `Algebra.IsAlgebraic.isSeparable_of_perfectField` is an instance, so a caller with
  `[PerfectField k]` in scope still elaborates unchanged — and it buys the characteristic-`p`
  case, where the base has been enlarged to something imperfect (here `Fk = k(ι)`, a rational
  function field) but the extension being tensored is still separable. The separability then
  has to come from somewhere: for a finitely generated extension of a perfect field mathlib
  now has it, `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`
  (`Mathlib/FieldTheory/SeparablyGenerated.lean`, 2025 — separating transcendence bases).
  **A "this needs new mathematics" verdict written months ago is a hypothesis about the PIN,
  and the pin moves.** Grep mathlib before believing it.

* **A hypothesis that fails only over FINITE fields — `[Infinite k]`, which every
  evaluate-at-`k`-points / specialisation argument carries — is dodged by base-changing to
  `k̄`, not repaired.** `k̄` is infinite and perfect whatever `k` was, and is trivially
  algebraically closed in every extension of it, so the hard theorem only ever runs over `k̄`:

      L ⊗[k] K  ↪  L ⊗[k] Ω  ≅  (k̄ ⊗[k] L) ⊗[k̄] Ω  ↪  Frac (k̄ ⊗[k] L) ⊗[k̄] Ω

  with `Ω` any algebraically closed field over both `K` and `k̄` (take `AlgebraicClosure K`).
  The two injections are flatness over a field; the middle iso is
  `Algebra.TensorProduct.cancelBaseChange`. The ONLY new input is that `k̄ ⊗[k] L` is a
  domain — which is the ALGEBRAIC half of the same theorem, already in hand. The same shape
  applies to any "geometric" statement whose proof needs an infinite (or algebraically
  closed) base: prove it over `k̄` and descend by flatness.

