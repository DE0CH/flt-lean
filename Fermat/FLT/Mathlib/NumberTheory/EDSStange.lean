/-
EDSStange.lean — own work for the Fermat project.

The first slice of Stange's theorem for the canonical normalised EDS:

* `normEDS_quadratic` (the `T(·, 2)` family, van der Poorten–Swart
  Proposition 1(4)): `W(n+2)W(n-2) = b²W(n+1)W(n-1) - cW(n)²` for all
  `n : ℤ`, proven by strong parity descent whose two certificates
  (found by multivariate division, `scripts/eds/`) use only
  `T(·, 2)`-instances at roughly half the index — after multiplying by
  a power of `c`, cancelled over the generic domain `ℤ[b, c, d]`.
* `normEDS_sum_companion` (van der Poorten–Swart Proposition 1(5)):
  `bc(Wₙ₋₁²Wₙ₊₂ + Wₙ₋₂Wₙ₊₁²) = Wₙ₋₁WₙWₙ₊₁(db + b⁵) - Wₙ³b³c`, by the
  telescope `W(n-1)·S(n+1) - W(n+2)·S(n) ∈ ideal(T(·,2))` (the
  "cute insertion" footnote of van der Poorten–Swart) plus generic
  cancellation of `W(n-1)`.

The generic nonvanishing `normEDS_generic_ne_zero` (witnessed by the
universal Weierstrass curve) powers all cancellations.
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence
public import Fermat.FLT.EllipticCurve.UniversalCurve

@[expose] public section

namespace EllipticDivisibilitySequence

open Polynomial WeierstrassCurve WeierstrassCurve.Affine PsiSumCompanion

/-- The generic EDS parameter `b`: a variable of `ℤ[b, c, d]`. -/
noncomputable abbrev genB : MvPolynomial (Fin 3) ℤ := MvPolynomial.X 0
/-- The generic EDS parameter `c`. -/
noncomputable abbrev genC : MvPolynomial (Fin 3) ℤ := MvPolynomial.X 1
/-- The generic EDS parameter `d`. -/
noncomputable abbrev genD : MvPolynomial (Fin 3) ℤ := MvPolynomial.X 2

set_option backward.isDefEq.respectTransparency false in
/-- **Generic nonvanishing of `normEDS`**: over `ℤ[b, c, d]`,
`normEDS b c d k ≠ 0` for `k ≠ 0` — witnessed by the universal curve,
whose division polynomial `mk (ψ k) = mk (Ψ k)` is nonzero in the
coordinate ring. -/
theorem normEDS_generic_ne_zero {k : ℤ} (hk : k ≠ 0) :
    normEDS genB genC genD k ≠ 0 := by
  intro hzero
  have himg := congrArg (MvPolynomial.eval₂Hom
    (Int.castRingHom Wuniv.toAffine.CoordinateRing)
    ![CoordinateRing.mk Wuniv Wuniv.ψ₂,
      CoordinateRing.mk Wuniv (Polynomial.C Wuniv.Ψ₃),
      CoordinateRing.mk Wuniv (Polynomial.C Wuniv.preΨ₄)]) hzero
  rw [map_zero, map_normEDS] at himg
  simp only [genB, genC, genD, MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons] at himg
  rw [← map_normEDS (CoordinateRing.mk Wuniv),
    show normEDS Wuniv.ψ₂ (Polynomial.C Wuniv.Ψ₃)
      (Polynomial.C Wuniv.preΨ₄) k = Wuniv.ψ k from rfl,
    Affine.CoordinateRing.mk_ψ] at himg
  exact mk_Ψ_univ_ne_zero hk himg

/-- Local shorthand for the generic sequence in this file. -/
local notation "E" => normEDS genB genC genD

set_option backward.isDefEq.respectTransparency false in
/-- The `T(·, 2)` relation is invariant under `n ↦ -n`. -/
theorem quadratic_symm {n : ℤ}
    (h : E (n + 2) * E (n - 2) = genB ^ 2 * E (n + 1) * E (n - 1) -
      genC * E n ^ 2) :
    E (-n + 2) * E (-n - 2) = genB ^ 2 * E (-n + 1) * E (-n - 1) -
      genC * E (-n) ^ 2 := by
  rw [show -n + 2 = -(n - 2) from by ring, show -n - 2 = -(n + 2) from by
    ring, show -n + 1 = -(n - 1) from by ring, show -n - 1 = -(n + 1)
    from by ring, normEDS_neg, normEDS_neg, normEDS_neg, normEDS_neg,
    normEDS_neg]
  linear_combination h

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 3200000 in
/-- **The `T(·, 2)` family for the generic normalised EDS** (PROVEN by
strong parity descent; the two step certificates use only `T(·, 2)`
instances at half the index, multiplied by `b²c⁵` resp. `b²c⁴` and
cancelled in the generic domain). -/
theorem normEDS_quadratic_generic (n : ℤ) :
    E (n + 2) * E (n - 2) = genB ^ 2 * E (n + 1) * E (n - 1) -
      genC * E n ^ 2 := by
  have hBC : genB ^ 2 * genC ^ 5 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (MvPolynomial.X_ne_zero 0))
      (pow_ne_zero 5 (MvPolynomial.X_ne_zero 1))
  have hBC4 : genB ^ 2 * genC ^ 4 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (MvPolynomial.X_ne_zero 0))
      (pow_ne_zero 4 (MvPolynomial.X_ne_zero 1))
  have key : ∀ N : ℕ, ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) →
      E (n + 2) * E (n - 2) = genB ^ 2 * E (n + 1) * E (n - 1) -
        genC * E n ^ 2 := by
    intro N
    induction N with
    | zero =>
      intro n hn hle
      rw [show n = 0 from by omega]
      norm_num [normEDS_neg, normEDS_zero, normEDS_one, normEDS_two]
      ring1
    | succ N IHN =>
      intro n hn hle
      by_cases h0 : n = 0
      · subst h0
        norm_num [normEDS_neg, normEDS_zero, normEDS_one, normEDS_two]
        ring1
      by_cases h1 : n = 1
      · subst h1
        norm_num [normEDS_neg, normEDS_zero, normEDS_one, normEDS_two,
          normEDS_three]
      by_cases h2 : n = 2
      · subst h2
        norm_num [normEDS_zero, normEDS_one, normEDS_two, normEDS_three,
          normEDS_four]
        ring1
      -- `n ≥ 3`: parity descent
      have hIH : ∀ j : ℤ, j.natAbs < n → E (j + 2) * E (j - 2) =
          genB ^ 2 * E (j + 1) * E (j - 1) - genC * E j ^ 2 := by
        intro j hj
        rcases le_or_gt 0 j with hj0 | hj0
        · exact IHN j hj0 (by omega)
        · have := IHN (-j) (by omega) (by omega)
          simpa only [neg_neg] using quadratic_symm this
      rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- even `n = 2m`, `m ≥ 2`
        have hmn : n = 2 * m := by omega
        have hm2 : 2 ≤ m := by omega
        have hIm3 := hIH (m - 3) (by omega)
        have hIm2 := hIH (m - 2) (by omega)
        have hIm1 := hIH (m - 1) (by omega)
        have hIp0 := hIH m (by omega)
        have hIp1 := hIH (m + 1) (by omega)
        rw [show m - 3 + 2 = m - 1 from by ring, show m - 3 - 2 = m - 5 from by ring, show m - 3 + 1 = m - 2 from by ring, show m - 3 - 1 = m - 4 from by ring] at hIm3
        rw [show m - 2 + 2 = m from by ring, show m - 2 - 2 = m - 4 from by ring, show m - 2 + 1 = m - 1 from by ring, show m - 2 - 1 = m - 3 from by ring] at hIm2
        rw [show m - 1 + 2 = m + 1 from by ring, show m - 1 - 2 = m - 3 from by ring, show m - 1 + 1 = m from by ring, show m - 1 - 1 = m - 2 from by ring] at hIm1
        rw [show m + 1 + 2 = m + 3 from by ring, show m + 1 - 2 = m - 1 from by ring, show m + 1 + 1 = m + 2 from by ring, show m + 1 - 1 = m from by ring] at hIp1
        have hE2 := normEDS_even genB genC genD (m + 1)
        have hE0 := normEDS_even genB genC genD (m - 1)
        have hE1 := normEDS_even genB genC genD m
        have hO1 := normEDS_odd genB genC genD m
        have hO0 := normEDS_odd genB genC genD (m - 1)
        rw [show 2 * (m + 1) = 2 * m + 2 from by ring,
          show m + 1 + 2 = m + 3 from by ring,
          show m + 1 - 1 = m from by ring,
          show m + 1 - 2 = m - 1 from by ring,
          show m + 1 + 1 = m + 2 from by ring] at hE2
        rw [show 2 * (m - 1) = 2 * m - 2 from by ring,
          show m - 1 + 2 = m + 1 from by ring,
          show m - 1 - 1 = m - 2 from by ring,
          show m - 1 - 2 = m - 3 from by ring,
          show m - 1 + 1 = m from by ring] at hE0
        rw [show 2 * (m - 1) + 1 = 2 * m - 1 from by ring,
          show m - 1 + 2 = m + 1 from by ring,
          show m - 1 - 1 = m - 2 from by ring,
          show m - 1 + 1 = m from by ring] at hO0
        have hP22 := congr(($hE2) * ($hE0))
        have hP11 := congr(($hO1) * ($hO0))
        have hPsq := congr(($hE1) * ($hE1))
        have hkey : (E (n + 2) * E (n - 2) -
            (genB ^ 2 * E (n + 1) * E (n - 1) - genC * E n ^ 2)) *
            (genB ^ 2 * genC ^ 5) = 0 := by
          rw [hmn, show (2 * m : ℤ) + 2 = 2 * m + 2 from by ring,
            show (2 * m : ℤ) - 2 = 2 * m - 2 from by ring,
            show (2 * m : ℤ) + 1 = 2 * m + 1 from by ring,
            show (2 * m : ℤ) - 1 = 2 * m - 1 from by ring]
          linear_combination (genC ^ 5) * hP22 -
            (genB ^ 4 * genC ^ 5) * hP11 + (genC ^ 6) * hPsq +
            (genB ^ 4 * genC * (E (m - 1)) * (E m) * (E (m + 1)) * (E (m + 2)) ^ 3 - genB ^ 2 * genC ^ 2 * (E (m - 1)) * (E (m + 1)) ^ 3 * (E (m + 2)) ^ 2 - genB ^ 2 * genC * (E (m - 1)) ^ 2 * (E (m + 1)) * (E (m + 2)) ^ 2 * (E (m + 3))) * hIm3 +
      (genB ^ 4 * genC ^ 3 * (E (m - 1)) * (E m) * (E (m + 1)) ^ 3 * (E (m + 2)) - 2 * genB ^ 2 * genC ^ 4 * (E m) ^ 3 * (E (m + 1)) ^ 2 * (E (m + 2)) + genB ^ 2 * genC ^ 2 * (E (m - 3)) * (E m) * (E (m + 1)) * (E (m + 2)) ^ 3 + genC ^ 5 * (E m) ^ 2 * (E (m + 1)) ^ 4 - genC ^ 4 * (E (m - 1)) ^ 2 * (E (m + 1)) ^ 2 * (E (m + 2)) ^ 2 + genC ^ 4 * (E (m - 1)) * (E m) ^ 2 * (E (m + 1)) ^ 2 * (E (m + 3)) - 2 * genC ^ 3 * (E (m - 3)) * (E (m + 1)) ^ 3 * (E (m + 2)) ^ 2 - genC ^ 2 * (E (m - 3)) * (E (m - 1)) * (E (m + 1)) * (E (m + 2)) ^ 2 * (E (m + 3))) * hIm2 +
      (genB ^ 4 * genC ^ 4 * (E (m - 1)) ^ 2 * (E (m + 1)) ^ 4 - genB ^ 4 * genC ^ 4 * (E (m - 1)) * (E m) ^ 3 * (E (m + 1)) * (E (m + 2)) - genB ^ 4 * (E (m - 5)) * (E m) * (E (m + 1)) * (E (m + 2)) ^ 3 + genB ^ 2 * genC ^ 4 * (E (m - 2)) * (E m) ^ 3 * (E (m + 2)) ^ 2 - genB ^ 2 * genC ^ 3 * (E (m - 3)) * (E (m - 1)) * (E (m + 1)) ^ 2 * (E (m + 2)) ^ 2 + genB ^ 2 * genC * (E (m - 5)) * (E (m + 1)) ^ 3 * (E (m + 2)) ^ 2 + genB ^ 2 * (E (m - 5)) * (E (m - 1)) * (E (m + 1)) * (E (m + 2)) ^ 2 * (E (m + 3)) - 2 * genC ^ 5 * (E (m - 2)) * (E m) ^ 2 * (E (m + 1)) ^ 2 * (E (m + 2)) + genC ^ 5 * (E (m - 1)) ^ 2 * (E m) ^ 2 * (E (m + 2)) ^ 2 + genC ^ 3 * (E (m - 4)) * (E m) * (E (m + 1)) ^ 2 * (E (m + 2)) ^ 2) * hIm1 +
      (-genB ^ 4 * genC ^ 4 * (E (m - 2)) * (E (m - 1)) * (E m) * (E (m + 1)) ^ 3 + genB ^ 4 * genC ^ 4 * (E (m - 2)) * (E m) ^ 4 * (E (m + 2)) - genB ^ 4 * genC ^ 3 * (E (m - 3)) * (E (m - 1)) * (E m) * (E (m + 1)) ^ 2 * (E (m + 2)) + genB ^ 2 * genC ^ 4 * (E (m - 3)) * (E (m - 1)) * (E (m + 1)) ^ 4 + 2 * genB ^ 2 * genC ^ 3 * (E (m - 4)) * (E m) ^ 2 * (E (m + 1)) ^ 2 * (E (m + 2)) - genB ^ 2 * genC ^ 3 * (E (m - 3)) * (E (m - 2)) * (E m) * (E (m + 1)) * (E (m + 2)) ^ 2 - genC ^ 4 * (E (m - 4)) * (E m) * (E (m + 1)) ^ 4 + 2 * genC ^ 4 * (E (m - 3)) * (E (m - 2)) * (E (m + 1)) ^ 3 * (E (m + 2)) - genC ^ 4 * (E (m - 3)) * (E (m - 1)) * (E m) ^ 2 * (E (m + 1)) * (E (m + 3)) - genC ^ 3 * (E (m - 4)) * (E (m - 1)) * (E m) * (E (m + 1)) ^ 2 * (E (m + 3)) + genC ^ 3 * (E (m - 3)) * (E (m - 2)) * (E (m - 1)) * (E (m + 1)) * (E (m + 2)) * (E (m + 3))) * hIp0 +
      (-genB ^ 4 * genC * (E (m - 4)) * (E (m - 2)) * (E (m - 1)) * (E (m + 1)) * (E (m + 2)) ^ 2 + genB ^ 4 * (E (m - 5)) * (E (m - 2)) * (E m) * (E (m + 1)) * (E (m + 2)) ^ 2 - genB ^ 2 * genC ^ 3 * (E (m - 4)) * (E (m - 1)) * (E m) * (E (m + 1)) ^ 3 + genB ^ 2 * genC ^ 3 * (E (m - 3)) * (E (m - 2)) * (E (m - 1)) * (E (m + 1)) ^ 2 * (E (m + 2)) - genB ^ 2 * (E (m - 5)) * (E (m - 3)) * (E (m + 1)) ^ 2 * (E (m + 2)) ^ 2 + genC ^ 3 * (E (m - 4)) * (E (m - 2)) * (E m) * (E (m + 1)) ^ 2 * (E (m + 2)) + genC ^ 2 * (E (m - 4)) * (E (m - 3)) * (E m) * (E (m + 1)) * (E (m + 2)) ^ 2) * hIp1
        rcases mul_eq_zero.mp hkey with hz | hz
        · exact sub_eq_zero.mp hz
        · exact absurd hz hBC
      · -- odd `n = 2m + 1`, `m ≥ 1`
        have hmn : n = 2 * m + 1 := by omega
        have hm1 : 1 ≤ m := by omega
        have hIm2 := hIH (m - 2) (by omega)
        have hIm1 := hIH (m - 1) (by omega)
        have hIp0 := hIH m (by omega)
        have hIp1 := hIH (m + 1) (by omega)
        rw [show m - 2 + 2 = m from by ring, show m - 2 - 2 = m - 4 from by ring, show m - 2 + 1 = m - 1 from by ring, show m - 2 - 1 = m - 3 from by ring] at hIm2
        rw [show m - 1 + 2 = m + 1 from by ring, show m - 1 - 2 = m - 3 from by ring, show m - 1 + 1 = m from by ring, show m - 1 - 1 = m - 2 from by ring] at hIm1
        rw [show m + 1 + 2 = m + 3 from by ring, show m + 1 - 2 = m - 1 from by ring, show m + 1 + 1 = m + 2 from by ring, show m + 1 - 1 = m from by ring] at hIp1
        have hO2 := normEDS_odd genB genC genD (m + 1)
        have hO0 := normEDS_odd genB genC genD (m - 1)
        have hO1 := normEDS_odd genB genC genD m
        have hE2 := normEDS_even genB genC genD (m + 1)
        have hE1 := normEDS_even genB genC genD m
        rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
          show m + 1 + 2 = m + 3 from by ring,
          show m + 1 - 1 = m from by ring,
          show m + 1 + 1 = m + 2 from by ring] at hO2
        rw [show 2 * (m - 1) + 1 = 2 * m - 1 from by ring,
          show m - 1 + 2 = m + 1 from by ring,
          show m - 1 - 1 = m - 2 from by ring,
          show m - 1 + 1 = m from by ring] at hO0
        rw [show 2 * (m + 1) = 2 * m + 2 from by ring,
          show m + 1 + 2 = m + 3 from by ring,
          show m + 1 - 1 = m from by ring,
          show m + 1 - 2 = m - 1 from by ring,
          show m + 1 + 1 = m + 2 from by ring] at hE2
        have hPoo := congr(($hO2) * ($hO0))
        have hPee := congr(($hE2) * ($hE1))
        have hPosq := congr(($hO1) * ($hO1))
        have hkey : (E (n + 2) * E (n - 2) -
            (genB ^ 2 * E (n + 1) * E (n - 1) - genC * E n ^ 2)) *
            (genB ^ 2 * genC ^ 4) = 0 := by
          rw [hmn, show (2 * m : ℤ) + 1 + 2 = 2 * m + 3 from by ring,
            show (2 * m : ℤ) + 1 - 2 = 2 * m - 1 from by ring,
            show (2 * m : ℤ) + 1 + 1 = 2 * m + 2 from by ring,
            show (2 * m : ℤ) + 1 - 1 = 2 * m from by ring]
          linear_combination (genB ^ 2 * genC ^ 4) * hPoo -
            (genB ^ 2 * genC ^ 4) * hPee +
            (genB ^ 2 * genC ^ 5) * hPosq +
            (-genB ^ 8 * (E m) * (E (m + 1)) ^ 2 * (E (m + 2)) ^ 3 + genB ^ 6 * genC * (E (m + 1)) ^ 4 * (E (m + 2)) ^ 2 + genB ^ 6 * (E (m - 1)) * (E (m + 1)) ^ 2 * (E (m + 2)) ^ 2 * (E (m + 3))) * hIm2 +
      (genB ^ 6 * genC ^ 2 * (E m) ^ 2 * (E (m + 1)) ^ 2 * (E (m + 2)) ^ 2 - 2 * genB ^ 4 * genC ^ 3 * (E m) * (E (m + 1)) ^ 4 * (E (m + 2)) + genB ^ 2 * genC ^ 4 * (E (m + 1)) ^ 6 + genB ^ 2 * genC ^ 3 * (E (m - 1)) * (E (m + 1)) ^ 4 * (E (m + 3)) - genB ^ 2 * genC ^ 3 * (E m) ^ 3 * (E (m + 1)) * (E (m + 2)) * (E (m + 3)) - genB ^ 2 * genC ^ 2 * (E (m - 2)) * (E m) * (E (m + 1)) * (E (m + 2)) ^ 2 * (E (m + 3))) * hIm1 +
      (genB ^ 8 * genC * (E (m - 2)) * (E m) * (E (m + 1)) ^ 2 * (E (m + 2)) ^ 2 - genB ^ 6 * genC ^ 2 * (E (m - 2)) * (E (m + 1)) ^ 4 * (E (m + 2)) - genB ^ 6 * genC * (E (m - 2)) * (E (m - 1)) * (E (m + 1)) ^ 2 * (E (m + 2)) * (E (m + 3)) + genB ^ 4 * genC ^ 3 * (E (m - 1)) * (E m) ^ 2 * (E (m + 1)) * (E (m + 2)) ^ 2 - genB ^ 4 * genC ^ 2 * (E (m - 2)) * (E m) ^ 2 * (E (m + 1)) * (E (m + 2)) * (E (m + 3)) - 2 * genB ^ 2 * genC ^ 4 * (E (m - 1)) * (E m) * (E (m + 1)) ^ 3 * (E (m + 2)) + genB ^ 2 * genC ^ 4 * (E m) ^ 4 * (E (m + 2)) ^ 2 + genB ^ 2 * genC ^ 2 * (E (m - 3)) * (E m) * (E (m + 1)) ^ 2 * (E (m + 2)) * (E (m + 3))) * hIp0 +
      (-genB ^ 8 * genC * (E (m - 2)) * (E (m - 1)) * (E (m + 1)) ^ 3 * (E (m + 2)) + genB ^ 8 * (E (m - 3)) * (E (m - 1)) * (E (m + 1)) ^ 2 * (E (m + 2)) ^ 2 - genB ^ 6 * (E (m - 4)) * (E m) * (E (m + 1)) ^ 2 * (E (m + 2)) ^ 2 + genB ^ 4 * genC ^ 3 * (E (m - 2)) * (E m) * (E (m + 1)) ^ 4 + genB ^ 4 * genC ^ 2 * (E (m - 3)) * (E m) * (E (m + 1)) ^ 3 * (E (m + 2)) - genB ^ 2 * genC ^ 3 * (E (m - 3)) * (E (m + 1)) ^ 5 + genB ^ 2 * genC ^ 3 * (E (m - 2)) * (E (m - 1)) * (E m) * (E (m + 1)) * (E (m + 2)) ^ 2) * hIp1
        rcases mul_eq_zero.mp hkey with hz | hz
        · exact sub_eq_zero.mp hz
        · exact absurd hz hBC4
  rcases le_or_gt 0 n with hn | hn
  · exact key n.toNat n hn (by omega)
  · have h := key (-n).toNat (-n) (by omega) (by omega)
    simpa only [neg_neg] using quadratic_symm h

set_option backward.isDefEq.respectTransparency false in
/-- **The `T(·, 2)` family for any normalised EDS** (PROVEN): by
specialising the generic case. -/
theorem normEDS_quadratic {R : Type*} [CommRing R] (b c d : R) (n : ℤ) :
    normEDS b c d (n + 2) * normEDS b c d (n - 2) =
      b ^ 2 * normEDS b c d (n + 1) * normEDS b c d (n - 1) -
      c * normEDS b c d n ^ 2 := by
  have h := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![b, c, d])
    (normEDS_quadratic_generic n)
  simpa only [map_mul, map_sub, map_pow, map_normEDS, genB, genC, genD,
    MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using h

set_option backward.isDefEq.respectTransparency false in
/-- **The telescope** (van der Poorten–Swart's "cute insertion"): the
sum-companion difference at `n + 1`, multiplied by `W(n-1)`, equals
the one at `n` multiplied by `W(n+2)`, modulo two `T(·, 2)`
instances. -/
theorem sum_companion_telescope (n : ℤ) :
    E (n - 1) * (genB * genC *
        (E n ^ 2 * E (n + 3) + E (n - 1) * E (n + 2) ^ 2) -
      (E n * E (n + 1) * E (n + 2) * (genD * genB + genB ^ 5) -
        E (n + 1) ^ 3 * genB ^ 3 * genC)) =
    E (n + 2) * (genB * genC *
        (E (n - 1) ^ 2 * E (n + 2) + E (n - 2) * E (n + 1) ^ 2) -
      (E (n - 1) * E n * E (n + 1) * (genD * genB + genB ^ 5) -
        E n ^ 3 * genB ^ 3 * genC)) := by
  have h0 := normEDS_quadratic_generic n
  have h1 := normEDS_quadratic_generic (n + 1)
  rw [show n + 1 + 2 = n + 3 from by ring,
    show n + 1 - 2 = n - 1 from by ring,
    show n + 1 + 1 = n + 2 from by ring,
    show n + 1 - 1 = n from by ring] at h1
  linear_combination (genB * E (n - 1) * E (n + 3) -
      genB ^ 3 * E n * E (n + 2)) * h0 +
    (genB ^ 3 * E (n - 1) * E (n + 1) -
      genB * E (n - 2) * E (n + 2)) * h1

set_option backward.isDefEq.respectTransparency false in
/-- The sum-companion is antisymmetric under `n ↦ -n`. -/
theorem sum_companion_symm {n : ℤ}
    (h : genB * genC * (E (n - 1) ^ 2 * E (n + 2) +
        E (n - 2) * E (n + 1) ^ 2) =
      E (n - 1) * E n * E (n + 1) * (genD * genB + genB ^ 5) -
        E n ^ 3 * genB ^ 3 * genC) :
    genB * genC * (E (-n - 1) ^ 2 * E (-n + 2) +
        E (-n - 2) * E (-n + 1) ^ 2) =
      E (-n - 1) * E (-n) * E (-n + 1) * (genD * genB + genB ^ 5) -
        E (-n) ^ 3 * genB ^ 3 * genC := by
  rw [show -n - 1 = -(n + 1) from by ring,
    show -n + 2 = -(n - 2) from by ring,
    show -n - 2 = -(n + 2) from by ring,
    show -n + 1 = -(n - 1) from by ring, normEDS_neg, normEDS_neg,
    normEDS_neg, normEDS_neg, normEDS_neg]
  linear_combination -h

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 16000 in
/-- **The sum-companion identity for the generic normalised EDS**
(PROVEN): base cases at `n = 0, 1, 2`, the telescope upward with
generic cancellation of `W(n-1)`, and antisymmetry downward. -/
theorem normEDS_sum_companion_generic (n : ℤ) :
    genB * genC * (E (n - 1) ^ 2 * E (n + 2) +
        E (n - 2) * E (n + 1) ^ 2) =
      E (n - 1) * E n * E (n + 1) * (genD * genB + genB ^ 5) -
        E n ^ 3 * genB ^ 3 * genC := by
  have key : ∀ N : ℕ, ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) →
      genB * genC * (E (n - 1) ^ 2 * E (n + 2) +
          E (n - 2) * E (n + 1) ^ 2) =
        E (n - 1) * E n * E (n + 1) * (genD * genB + genB ^ 5) -
          E n ^ 3 * genB ^ 3 * genC := by
    intro N
    induction N with
    | zero =>
      intro n hn hle
      rw [show n = 0 from by omega]
      norm_num [normEDS_neg, normEDS_zero, normEDS_one, normEDS_two]
    | succ N IHN =>
      intro n hn hle
      by_cases h0 : n = 0
      · subst h0
        norm_num [normEDS_neg, normEDS_zero, normEDS_one, normEDS_two]
      by_cases h1 : n = 1
      · subst h1
        norm_num [normEDS_neg, normEDS_zero, normEDS_one, normEDS_two,
          normEDS_three]
        ring1
      by_cases h2 : n = 2
      · subst h2
        norm_num [normEDS_zero, normEDS_one, normEDS_two, normEDS_three,
          normEDS_four]
        ring1
      -- step: `n ≥ 3`, from `n - 1 ≥ 2`
      have hIH := IHN (n - 1) (by omega) (by omega)
      rw [show n - 1 - 1 = n - 2 from by ring,
        show n - 1 + 2 = n + 1 from by ring,
        show n - 1 - 2 = n - 3 from by ring,
        show n - 1 + 1 = n from by ring] at hIH
      have htel := sum_companion_telescope (n - 1)
      rw [show n - 1 + 3 = n + 2 from by ring,
        show n - 1 + 2 = n + 1 from by ring,
        show n - 1 + 1 = n from by ring,
        show n - 1 - 1 = n - 2 from by ring,
        show n - 1 - 2 = n - 3 from by ring] at htel
      have hz : genB * genC * (E (n - 2) ^ 2 * E (n + 1) +
          E (n - 3) * E n ^ 2) -
          (E (n - 2) * E (n - 1) * E n * (genD * genB + genB ^ 5) -
            E (n - 1) ^ 3 * genB ^ 3 * genC) = 0 := by
        linear_combination hIH
      have hmul : E (n - 2) * (genB * genC *
          (E (n - 1) ^ 2 * E (n + 2) + E (n - 2) * E (n + 1) ^ 2) -
          (E (n - 1) * E n * E (n + 1) * (genD * genB + genB ^ 5) -
            E n ^ 3 * genB ^ 3 * genC)) = 0 := by
        linear_combination htel + E (n + 1) * hz
      rcases mul_eq_zero.mp hmul with hc | hc
      · exact absurd hc (normEDS_generic_ne_zero (by omega))
      · linear_combination hc
  rcases le_or_gt 0 n with hn | hn
  · exact key n.toNat n hn (by omega)
  · have h := key (-n).toNat (-n) (by omega) (by omega)
    simpa only [neg_neg] using sum_companion_symm h

set_option backward.isDefEq.respectTransparency false in
/-- **The universal sum-companion identity** for any normalised EDS
(PROVEN, formerly the `(★s′)` sorry node): for `W = normEDS b c d`,
`bc(Wₙ₋₁²Wₙ₊₂ + Wₙ₋₂Wₙ₊₁²) = Wₙ₋₁WₙWₙ₊₁(db + b⁵) − Wₙ³b³c`. -/
theorem normEDS_sum_companion {R : Type*} [CommRing R] (b c d : R)
    (n : ℤ) :
    b * c * (normEDS b c d (n - 1) ^ 2 * normEDS b c d (n + 2) +
      normEDS b c d (n - 2) * normEDS b c d (n + 1) ^ 2) =
    normEDS b c d (n - 1) * normEDS b c d n * normEDS b c d (n + 1) *
      (d * b + b ^ 5) - normEDS b c d n ^ 3 * b ^ 3 * c := by
  have h := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![b, c, d])
    (normEDS_sum_companion_generic n)
  simpa only [map_mul, map_add, map_sub, map_pow, map_normEDS, genB,
    genC, genD, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] using h

end EllipticDivisibilitySequence
