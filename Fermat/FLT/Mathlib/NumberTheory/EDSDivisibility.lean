/-
EDSDivisibility.lean — own work for the Fermat project.

The divisibility property of the canonical normalised EDS: the
complement sequence witnesses `W(k) ∣ W(n·k)`, i.e.
`normEDS b c d k * complEDS b c d k n = normEDS b c d (n * k)`.
This is the mathlib TODO `IsEllipticDvdSequence (normEDS b c d)` in
its exact quantitative form, proven here MODULO the Stange node
`normEDS_ellSequence`:

* the even step is mathlib's `normEDS_mul_complEDS₂`;
* the odd step is the `T((m+1)k, mk)` instance of the elliptic-sequence
  relation, after cancelling one factor of `normEDS b c d k`;
* the cancellation happens over the GENERIC coefficients `ℤ[b, c, d]`
  (a domain), where `normEDS b c d k ≠ 0` for `k ≠ 0` because its
  image under `(b, c, d) ↦ (mk ψ₂, mk CΨ₃, mk C preΨ₄)` in the
  coordinate ring of the universal Weierstrass curve is
  `mk (Ψ k) ≠ 0` (by the `preΨ`-degree theory over `ℤ[A][X]` and the
  `{1, Y}`-basis);
* the general case follows by specialising along
  `map_normEDS`/`map_complEDS`.
-/
module

public import Fermat.FLT.Mathlib.NumberTheory.EDSStange

@[expose] public section

namespace EllipticDivisibilitySequence

open Polynomial WeierstrassCurve WeierstrassCurve.Affine PsiSumCompanion

open scoped Polynomial.Bivariate

set_option backward.isDefEq.respectTransparency false in
/-- **The divisibility identity for generic coefficients**: over
`ℤ[b, c, d]`, `W(k) ⬝ Wᶜ(k, n) = W(nk)`. Even step: mathlib's
`normEDS_mul_complEDS₂`; odd step: the `T((m+1)k, mk)` instance of
the Stange node, cancelling one `W(k)` in the domain. -/
theorem normEDS_mul_complEDS_generic (k n : ℤ) :
    normEDS genB genC genD k * complEDS genB genC genD k n =
      normEDS genB genC genD (n * k) := by
  by_cases hk : k = 0
  · subst hk
    simp
  -- reduce to `n ≥ 0` and induct with a bound
  have key : ∀ N : ℕ, ∀ m : ℤ, 0 ≤ m → m ≤ (N : ℤ) →
      normEDS genB genC genD k * complEDS genB genC genD k m =
        normEDS genB genC genD (m * k) := by
    intro N
    induction N with
    | zero =>
      intro m hm hle
      rw [show m = 0 from by omega, complEDS_zero, mul_zero, zero_mul,
        normEDS_zero]
    | succ N IHN =>
      intro m hm hle
      by_cases hm0 : m = 0
      · rw [hm0, complEDS_zero, mul_zero, zero_mul, normEDS_zero]
      by_cases hm1 : m = 1
      · rw [hm1, complEDS_one, mul_one, one_mul]
      rcases Int.even_or_odd m with ⟨m', hm'⟩ | ⟨m', hm'⟩
      · -- even: `m = 2m'`
        have hIH := IHN m' (by omega) (by omega)
        rw [hm', show m' + m' = 2 * m' from by ring, complEDS_even,
          ← mul_assoc, hIH, normEDS_mul_complEDS₂,
          show 2 * (m' * k) = 2 * m' * k from by ring]
      · -- odd: `m = 2m' + 1`
        have hIH1 := IHN m' (by omega) (by omega)
        have hIH2 := IHN (m' + 1) (by omega) (by omega)
        have hT := normEDS_ellSequence genB genC genD ((m' + 1) * k)
          (m' * k)
        rw [show (m' + 1) * k + m' * k = (2 * m' + 1) * k from by ring,
          show (m' + 1) * k - m' * k = k from by ring] at hT
        have hodd := complEDS_odd genB genC genD k m'
        have hkey : normEDS genB genC genD k *
            (normEDS genB genC genD k *
              complEDS genB genC genD k (2 * m' + 1) -
             normEDS genB genC genD ((2 * m' + 1) * k)) = 0 := by
          have hexp := congrArg
            (fun z => normEDS genB genC genD k ^ 2 * z) hodd
          simp only [mul_sub] at hexp
          linear_combination hexp - hT +
            (normEDS genB genC genD ((m' + 1) * k + 1) *
              normEDS genB genC genD ((m' + 1) * k - 1) *
              (normEDS genB genC genD k * complEDS genB genC genD k m' +
                normEDS genB genC genD (m' * k))) * hIH1 -
            (normEDS genB genC genD (m' * k + 1) *
              normEDS genB genC genD (m' * k - 1) *
              (normEDS genB genC genD k *
                complEDS genB genC genD k (m' + 1) +
                normEDS genB genC genD ((m' + 1) * k))) * hIH2
        rcases mul_eq_zero.mp hkey with hc | hc
        · exact absurd hc (normEDS_generic_ne_zero hk)
        · rw [hm']
          exact sub_eq_zero.mp hc
  rcases le_or_gt 0 n with hn | hn
  · exact key n.toNat n hn (by omega)
  · have hpos := key (-n).toNat (-n) (by omega) (by omega)
    have h1 : complEDS genB genC genD k n =
        -complEDS genB genC genD k (-n) := by
      rw [← complEDS_neg, neg_neg]
    rw [h1, mul_neg, hpos, show -n * k = -(n * k) from by ring,
      normEDS_neg, neg_neg]

set_option backward.isDefEq.respectTransparency false in
/-- **The divisibility property of `normEDS`** (the mathlib TODO
`IsEllipticDvdSequence (normEDS b c d)`, quantitative form): the
complement sequence witnesses `W(k) ∣ W(n·k)` over any commutative
ring — by specialising the generic identity along
`map_normEDS`/`map_complEDS`. -/
theorem normEDS_mul_complEDS {R : Type*} [CommRing R] (b c d : R)
    (k n : ℤ) :
    normEDS b c d k * complEDS b c d k n = normEDS b c d (n * k) := by
  have h := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![b, c, d])
    (normEDS_mul_complEDS_generic k n)
  rw [map_mul, map_normEDS, map_complEDS, map_normEDS] at h
  simpa only [genB, genC, genD, MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons] using h

end EllipticDivisibilitySequence
