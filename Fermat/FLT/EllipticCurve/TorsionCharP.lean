/-
TorsionCharP.lean — own work for the Fermat project.

The characteristic-`p` counterpart of `TorsionCard.prime_torsion_card`:
over an algebraically closed field `k` in which `p` vanishes, the
geometric `p`-torsion of an elliptic curve is CYCLIC (`#E(k)[p] ∣ p`),
where for `(p : k) ≠ 0` it is `(ℤ/p)²`.

The mathematical content is the inseparability of the
multiplication-by-`p` isogeny, and it is extracted here from the
Wronskian identity `Φₙ′ ⬝ ΨSqₙ − Φₙ ⬝ ΨSqₙ′ = n ⬝ preΨ₂ₙ`
(`PsiSumCompanion.wronskian`, proven at the tautological point of the
universal curve) together with the coprimality of `Φₙ` and `ΨSqₙ`
(`WeierstrassCurve.isCoprime_Φ_ΨSq`, proven from `Δ ≠ 0`):

* in characteristic `p` the right-hand side of the Wronskian identity
  vanishes at `n = p`, so `ΨSqₚ ∣ Φₚ ⬝ ΨSqₚ′`, and coprimality forces
  `ΨSqₚ ∣ ΨSqₚ′`, whence `ΨSqₚ′ = 0` by degrees
  (`derivative_ΨSq_eq_zero_of_charP`);
* over the (perfect) field `k` a polynomial with vanishing derivative
  is a `p`-th power (`exists_pow_eq_ΨSq_of_charP`), so `ΨSqₚ`, of
  degree at most `p² − 1`, has at most `p − 1` DISTINCT roots
  (`card_roots_ΨSq_le_of_charP`). This is the polynomial shadow of
  "`[p]` has separable degree at most `p`".

The count then closes the cyclicity statement
(`exists_zsmul_eq_of_charP`): if some `p`-torsion `P` were not a
multiple of a nonzero `p`-torsion `Q`, the `p²` points `a • Q + b • P`
(`0 ≤ a, b < p`) would be pairwise distinct, giving `p² − 1` nonzero
`p`-torsion points; each has its `x`-coordinate among the at most
`p − 1` roots of `ΨSqₚ` (`TorsionCard.smul_some_eq_zero_iff`), and at
most two points lie over each `x` (`TorsionCard.pointsAt_card` and the
`y`-fibre quadratic), so `p² − 1 ≤ 2(p − 1)` — false for every prime.

Note that no separate nonvanishing input is needed: `ΨSqₚ ≠ 0` already
follows from coprimality with `Φₚ`, which has degree `p² > 0` and is
therefore not a unit (`ΨSq_ne_zero`).

ADDED 2026-07-30, and it is the OTHER half of the dichotomy — cyclicity
above bounds `E(k)[p]` from ABOVE, and what a consumer usually wants next is
whether it is nonzero at all.  `exists_ne_zero_torsion_iff_natDegree_ΨSq_ne_zero`
turns that existence question into a statement about a single explicit
polynomial:

    (∃ P ≠ 0, n • P = 0)  ↔  (ΨSqₙ).natDegree ≠ 0.

It is characteristic-AGNOSTIC and holds for every `n ≠ 0` — the only inputs
are `TorsionCard.smul_some_eq_zero_iff` (an affine point is `n`-torsion iff
its `x`-coordinate is a root of `ΨSqₙ`), `ΨSq_ne_zero`, and the surjectivity
of the `x`-coordinate map over an algebraically closed field
(`exists_nonsingular_of_isAlgClosed`).  At `n = p` in characteristic `p` it
reads, through `exists_pow_eq_ΨSq_of_charP`, as `deg g ≥ 1`: ORDINARY on the
left, SUPERSINGULAR (`ΨSqₚ` constant) on the right.  `HasseBound.lean`
consumes it in exactly that case.
-/
module

public import Fermat.FLT.EllipticCurve.TorsionCard
public import Fermat.FLT.EllipticCurve.WronskianInduction
import Fermat.FLT.EllipticCurve.PhiPsiCoprime
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

namespace TorsionCharP

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

omit [DecidableEq k] in
/-- **The division polynomial `ΨSqₙ` of an elliptic curve is nonzero**
(PROVEN 2026-07-25), in ANY characteristic and with no hypothesis
beyond `n ≠ 0`. This is the piece that the leading-coefficient route
cannot supply in characteristic `p` at `n = p`, where
`coeff_ΨSq n = n²` vanishes: instead it comes from the coprimality of
`Φₙ` and `ΨSqₙ` (`WeierstrassCurve.isCoprime_Φ_ΨSq`, which needs only
`Δ ≠ 0`). Indeed `IsCoprime a 0` forces `a` to be a unit, while
`Φₙ` has degree `n² > 0`. -/
theorem ΨSq_ne_zero {n : ℤ} (hn : n ≠ 0) : (E⁄k).ΨSq n ≠ 0 := by
  haveI : (E⁄k).IsElliptic := inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  intro h0
  have hcop : IsCoprime ((E⁄k).Φ n) ((E⁄k).ΨSq n) :=
    WeierstrassCurve.isCoprime_Φ_ΨSq (E⁄k) hn (E⁄k).isUnit_Δ
  rw [h0] at hcop
  have hdeg0 : ((E⁄k).Φ n).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit (isCoprime_zero_right.mp hcop)
  rw [WeierstrassCurve.natDegree_Φ (E⁄k) n] at hdeg0
  exact hn (Int.natAbs_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hdeg0))

omit [DecidableEq k] in
/-- **Inseparability of `[p]` in characteristic `p`, in its polynomial
form** (PROVEN 2026-07-25): the derivative of the `p`-division
polynomial `ΨSqₚ` vanishes identically.

This is the whole arithmetic content of the char-`p` torsion bound,
and it is exactly the differential criterion `[p]* ω = p ⬝ ω = 0`
transcribed through the Wronskian identity
`Φₚ′ ⬝ ΨSqₚ − Φₚ ⬝ ΨSqₚ′ = p ⬝ preΨ₂ₚ` (`PsiSumCompanion.wronskian`):
in characteristic `p` the right-hand side is `0`, so
`ΨSqₚ ∣ Φₚ ⬝ ΨSqₚ′`; coprimality of `Φₚ` and `ΨSqₚ` promotes this to
`ΨSqₚ ∣ ΨSqₚ′`, and a nonzero polynomial cannot divide its own
derivative unless that derivative vanishes. -/
theorem derivative_ΨSq_eq_zero_of_charP {p : ℕ} (hp : p.Prime) (hchar : (p : k) = 0) :
    Polynomial.derivative ((E⁄k).ΨSq (p : ℤ)) = 0 := by
  haveI : (E⁄k).IsElliptic := inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  have hpZ : ((p : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hΨne : (E⁄k).ΨSq (p : ℤ) ≠ 0 := ΨSq_ne_zero E hpZ
  -- the Wronskian identity, with its right-hand side killed by the characteristic
  have hpX : ((p : ℕ) : k[X]) = 0 := by
    simpa using congrArg (Polynomial.C (R := k)) hchar
  have hW := PsiSumCompanion.wronskian (E⁄k) (n := p) hp.one_lt.le
  rw [hpX, zero_mul] at hW
  -- `ΨSqₚ` divides `Φₚ ⬝ ΨSqₚ′`, hence (coprimality) its own derivative
  have hdvd : (E⁄k).ΨSq (p : ℤ) ∣ (E⁄k).Φ (p : ℤ) * Polynomial.derivative ((E⁄k).ΨSq (p : ℤ)) :=
    ⟨Polynomial.derivative ((E⁄k).Φ (p : ℤ)), by linear_combination -hW⟩
  have hcop : IsCoprime ((E⁄k).ΨSq (p : ℤ)) ((E⁄k).Φ (p : ℤ)) :=
    (WeierstrassCurve.isCoprime_Φ_ΨSq (E⁄k) hpZ (E⁄k).isUnit_Δ).symm
  have hdvd2 : (E⁄k).ΨSq (p : ℤ) ∣ Polynomial.derivative ((E⁄k).ΨSq (p : ℤ)) :=
    hcop.dvd_of_dvd_mul_left hdvd
  -- a nonzero polynomial dividing its own derivative has zero derivative
  by_contra hne
  rcases eq_or_ne ((E⁄k).ΨSq (p : ℤ)).natDegree 0 with h0 | h0
  · refine hne ?_
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C]
  · have hlt := Polynomial.natDegree_derivative_lt h0
    have hle := Polynomial.natDegree_le_of_dvd hdvd2 hne
    omega

omit [DecidableEq k] in
/-- **`ΨSqₚ` is a `p`-th power in characteristic `p`** (PROVEN
2026-07-25, from `derivative_ΨSq_eq_zero_of_charP` and perfectness of
`k`): a polynomial over a perfect field of characteristic `p` whose
derivative vanishes lies in `k[Xᵖ]`, and every coefficient there is
itself a `p`-th power, so the polynomial is a `p`-th power. -/
theorem exists_pow_eq_ΨSq_of_charP [IsAlgClosed k] {p : ℕ} (hp : p.Prime) (hchar : (p : k) = 0) :
    ∃ g : k[X], (E⁄k).ΨSq (p : ℤ) = g ^ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr hchar
  haveI : ExpChar k p := ExpChar.prime hp
  refine ⟨(Polynomial.contract p ((E⁄k).ΨSq (p : ℤ))).map (frobeniusEquiv k p).symm, ?_⟩
  rw [← polynomial_expand_eq,
    Polynomial.expand_contract p (derivative_ΨSq_eq_zero_of_charP E hp hchar) hp.ne_zero]

/-- **In characteristic `p` the `p`-division polynomial has at most
`p − 1` distinct roots** (PROVEN 2026-07-25). This is the polynomial
shadow of "the separable degree of `[p]` is at most `p`": `ΨSqₚ` is a
`p`-th power `gᵖ` with `p ⬝ deg g = deg ΨSqₚ ≤ p² − 1`, so
`deg g ≤ p − 1`, and `gᵖ` has exactly the distinct roots of `g`.

Contrast `(p : k) ≠ 0`, where `ΨSqₚ` is separable of degree `p² − 1`
and there are `p² − 1` distinct roots — the `(p²−1)/2` `x`-coordinates
of the nonzero `p`-torsion, twice over. -/
theorem card_roots_ΨSq_le_of_charP [IsAlgClosed k] {p : ℕ} (hp : p.Prime) (hchar : (p : k) = 0) :
    (((E⁄k).ΨSq (p : ℤ)).roots.toFinset).card ≤ p - 1 := by
  haveI : (E⁄k).IsElliptic := inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  have hpZ : ((p : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hΨne : (E⁄k).ΨSq (p : ℤ) ≠ 0 := ΨSq_ne_zero E hpZ
  obtain ⟨g, hg⟩ := exists_pow_eq_ΨSq_of_charP E hp hchar
  have hgne : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hg
    exact hΨne hg
  -- the degree of the `p`-th root
  have hdeg : p * g.natDegree ≤ p ^ 2 - 1 := by
    have h1 := WeierstrassCurve.natDegree_ΨSq_le (W := (E⁄k)) (p : ℤ)
    rw [hg, Polynomial.natDegree_pow] at h1
    simpa using h1
  have hgdeg : g.natDegree ≤ p - 1 := by
    have hp2 : 2 ≤ p := hp.two_le
    have hpow : p ^ 2 = p * p := sq p
    have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : p * g.natDegree < p * p := by omega
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  -- the distinct roots of `gᵖ` are the distinct roots of `g`
  rw [hg, Polynomial.roots_pow, Multiset.toFinset_nsmul _ _ hp.ne_zero]
  calc (g.roots.toFinset).card
      ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' g
    _ ≤ p - 1 := hgdeg

/-- **At most two points of the curve lie over a given `x`-coordinate**
(PROVEN 2026-07-25): the `y`-fibre is cut out by the monic quadratic
`yQuad`, so it has at most `2` roots. -/
theorem card_pointsAt_le_two (x : k) : (TorsionCard.pointsAt E x).card ≤ 2 := by
  rw [TorsionCard.pointsAt_card]
  calc ((TorsionCard.yQuad E x).roots.toFinset).card
      ≤ Multiset.card (TorsionCard.yQuad E x).roots := Multiset.toFinset_card_le _
    _ ≤ (TorsionCard.yQuad E x).natDegree := Polynomial.card_roots' _
    _ = 2 := TorsionCard.yQuad_natDegree E x

/-- Arithmetic helper for the distinctness of the `p²` combinations
below: two residues strictly below `p` differing by a multiple of `p`
are equal. -/
theorem eq_of_natCast_sub_dvd {p a b : ℕ} (ha : a < p) (hb : b < p)
    (h : ((p : ℕ) : ℤ) ∣ ((a : ℤ) - b)) : a = b := by
  obtain ⟨t, ht⟩ := h
  rcases lt_trichotomy t 0 with hlt | rfl | hgt
  · have h1 : ((p : ℕ) : ℤ) * t ≤ -((p : ℕ) : ℤ) := by
      have := mul_le_mul_of_nonneg_left (show t ≤ -1 by omega)
        (show (0 : ℤ) ≤ ((p : ℕ) : ℤ) by positivity)
      linarith
    omega
  · rw [mul_zero] at ht
    omega
  · have h1 : ((p : ℕ) : ℤ) ≤ ((p : ℕ) : ℤ) * t := by
      have := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ t by omega)
        (show (0 : ℤ) ≤ ((p : ℕ) : ℤ) by positivity)
      linarith
    omega

/-- **The geometric `p`-torsion of an elliptic curve in characteristic
`p` is cyclic** (PROVEN 2026-07-25): over an algebraically closed field
`k` in which the prime `p` vanishes, every `p`-torsion point is a
`ℤ`-multiple of every NONZERO `p`-torsion point.

Both cases of the classical dichotomy satisfy this, and the statement
is not vacuous: ordinary, `E(k)[p] ≅ ℤ/p`, any nonzero point
generates; supersingular, `E(k)[p] = 0`, the hypothesis `Q ≠ 0` is
unsatisfiable. It is exactly what fails for `p` invertible in `k`,
where `TorsionCard.prime_torsion_card` gives `(ℤ/p)²`.

Proof: were `P` not a multiple of `Q`, the `p²` combinations
`a • Q + b • P` with `0 ≤ a, b < p` would be pairwise distinct — the
only way two could coincide is `(b − b′) • P = (a′ − a) • Q` with
`p ∤ (b − b′)`, and Bézout for `p` then exhibits `P` as a multiple of
`Q`. All `p² − 1` nonzero ones are `p`-torsion, so their
`x`-coordinates are roots of `ΨSqₚ`
(`TorsionCard.smul_some_eq_zero_iff`), of which there are at most
`p − 1` by inseparability (`card_roots_ΨSq_le_of_charP`), with at most
two points over each; so `p² − 1 ≤ 2(p − 1)`, i.e. `(p − 1)² ≤ 0`. -/
theorem exists_zsmul_eq_of_charP [IsAlgClosed k] {p : ℕ} (hp : p.Prime) (hchar : (p : k) = 0)
    (P Q : (E⁄k).Point) (hP : ((p : ℕ) : ℤ) • P = 0) (hQ : ((p : ℕ) : ℤ) • Q = 0) (hQ0 : Q ≠ 0) :
    ∃ n : ℤ, P = n • Q := by
  haveI : (E⁄k).IsElliptic := inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  by_contra hcon
  have hpZ : ((p : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hΨne : (E⁄k).ΨSq ((p : ℕ) : ℤ) ≠ 0 := ΨSq_ne_zero E hpZ
  -- `Q` has additive order exactly `p`
  have hQord : addOrderOf Q = p := by
    have hQdvd : (addOrderOf Q : ℤ) ∣ ((p : ℕ) : ℤ) := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hQ
    rcases hp.eq_one_or_self_of_dvd _ (Int.natCast_dvd_natCast.mp hQdvd) with h | h
    · exact absurd (by
        have : (1 : ℤ) • Q = 0 :=
          addOrderOf_dvd_iff_zsmul_eq_zero.mp (by rw [h]; exact one_dvd _)
        rwa [one_zsmul] at this) hQ0
    · exact h
  have hQz : ∀ m : ℤ, m • Q = 0 ↔ ((p : ℕ) : ℤ) ∣ m := by
    intro m
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hQord]
  -- the `p²` combinations `a • Q + b • P`
  classical
  set f : ℕ × ℕ → (E⁄k).Point := fun ab => (ab.1 : ℤ) • Q + (ab.2 : ℤ) • P with hf
  have hinj : Set.InjOn f ↑(Finset.range p ×ˢ Finset.range p) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hab hcd
    obtain ⟨ha, hb⟩ := hab
    obtain ⟨hc, hd⟩ := hcd
    simp only [hf] at heq
    have hkey : ((b : ℤ) - d) • P = ((c : ℤ) - a) • Q := by
      have e1 : ((b : ℤ) - d) • P + ((d : ℤ) • P + (a : ℤ) • Q)
          = (a : ℤ) • Q + (b : ℤ) • P := by rw [sub_zsmul]; abel
      have e2 : ((c : ℤ) - a) • Q + ((d : ℤ) • P + (a : ℤ) • Q)
          = (c : ℤ) • Q + (d : ℤ) • P := by rw [sub_zsmul]; abel
      exact add_right_cancel (e1.trans (heq.trans e2.symm))
    have hbd : b = d := by
      by_contra hbd
      have hnd : ¬ ((p : ℕ) : ℤ) ∣ ((b : ℤ) - d) := fun h => hbd (eq_of_natCast_sub_dvd hb hd h)
      obtain ⟨u, v, huv⟩ :=
        ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hnd
      refine hcon ⟨v * ((c : ℤ) - a), ?_⟩
      calc P = (1 : ℤ) • P := (one_zsmul P).symm
        _ = (u * ((p : ℕ) : ℤ) + v * ((b : ℤ) - d)) • P := by rw [huv]
        _ = u • (((p : ℕ) : ℤ) • P) + v • (((b : ℤ) - d) • P) := by
            rw [add_zsmul, mul_zsmul, mul_zsmul]
        _ = v • (((c : ℤ) - a) • Q) := by rw [hP, smul_zero, zero_add, hkey]
        _ = (v * ((c : ℤ) - a)) • Q := (mul_zsmul _ _ _).symm
    subst hbd
    have hac : a = c := by
      have h0 : ((c : ℤ) - a) • Q = 0 := by rw [← hkey, sub_self, zero_zsmul]
      exact (eq_of_natCast_sub_dvd hc ha ((hQz _).mp h0)).symm
    subst hac
    rfl
  set S : Finset ((E⁄k).Point) := (Finset.range p ×ˢ Finset.range p).image f with hS
  have hScard : S.card = p * p := by
    rw [hS, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range]
  -- everything in `S` is `p`-torsion
  have htor : ∀ Z ∈ S, ((p : ℕ) : ℤ) • Z = 0 := by
    intro Z hZ
    rw [hS] at hZ
    obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp hZ
    have h1 : ((p : ℕ) : ℤ) • ((a : ℤ) • Q) = 0 := by
      rw [← mul_zsmul, mul_comm, mul_zsmul, hQ, smul_zero]
    have h2 : ((p : ℕ) : ℤ) • ((b : ℤ) • P) = 0 := by
      rw [← mul_zsmul, mul_comm, mul_zsmul, hP, smul_zero]
    simp only [hf]
    rw [smul_add, h1, h2, add_zero]
  -- the nonzero ones are fibred over the roots of `ΨSqₚ`
  have hsub : S.erase 0 ⊆
      (((E⁄k).ΨSq ((p : ℕ) : ℤ)).roots.toFinset).biUnion (TorsionCard.pointsAt E) := by
    intro Z hZ
    have hZ0 : Z ≠ 0 := Finset.ne_of_mem_erase hZ
    have hZt := htor Z (Finset.mem_of_mem_erase hZ)
    obtain ⟨x, y, h, rfl⟩ :
        ∃ (x : k) (y : k) (h : (E⁄k).toAffine.Nonsingular x y),
          Z = Affine.Point.some x y h := by
      cases Z with
      | zero => exact absurd rfl hZ0
      | some x y h => exact ⟨x, y, h, rfl⟩
    have hev : ((E⁄k).ΨSq ((p : ℕ) : ℤ)).eval x = 0 :=
      (TorsionCard.smul_some_eq_zero_iff E hpZ h).mp hZt
    refine Finset.mem_biUnion.mpr ⟨x, ?_, ?_⟩
    · exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hΨne, hev⟩)
    · exact (TorsionCard.mem_pointsAt_iff E).mpr ⟨y, h, rfl⟩
  -- and there are at most two points over each root
  have hcount : (S.erase 0).card ≤ (p - 1) * 2 :=
    calc (S.erase 0).card
        ≤ ((((E⁄k).ΨSq ((p : ℕ) : ℤ)).roots.toFinset).biUnion
            (TorsionCard.pointsAt E)).card := Finset.card_le_card hsub
      _ ≤ ∑ x ∈ (((E⁄k).ΨSq ((p : ℕ) : ℤ)).roots.toFinset),
            (TorsionCard.pointsAt E x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ (((E⁄k).ΨSq ((p : ℕ) : ℤ)).roots.toFinset), 2 :=
          Finset.sum_le_sum fun x _ => card_pointsAt_le_two E x
      _ = (((E⁄k).ΨSq ((p : ℕ) : ℤ)).roots.toFinset).card * 2 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (p - 1) * 2 :=
          Nat.mul_le_mul_right 2 (card_roots_ΨSq_le_of_charP E hp hchar)
  have h0S : (0 : (E⁄k).Point) ∈ S := by
    refine Finset.mem_image.mpr ⟨(0, 0), ?_, ?_⟩
    · simp [hp.pos]
    · simp [hf]
  rw [Finset.card_erase_of_mem h0S, hScard] at hcount
  obtain ⟨N, hN1, hN2⟩ : ∃ N, p * 2 ≤ N ∧ N - 1 ≤ (p - 1) * 2 :=
    ⟨p * p, Nat.mul_le_mul_left p hp.two_le, hcount⟩
  have := hp.two_le
  omega

omit [DecidableEq k] in
/-- **Over an algebraically closed field every `x` carries a point of the
curve** (PROVEN 2026-07-30): the `y`-fibre quadratic `yQuad` is monic of
degree `2`, hence has a root, and for an elliptic curve `Δ ≠ 0` promotes the
resulting `Equation` to `Nonsingular`
(`WeierstrassCurve.Affine.equation_iff_nonsingular`).

This is the surjectivity of the `x`-coordinate map, and it is what turns a
ROOT of a division polynomial into an actual torsion POINT. -/
theorem exists_nonsingular_of_isAlgClosed [IsAlgClosed k] (x : k) :
    ∃ y : k, (E⁄k).toAffine.Nonsingular x y := by
  haveI : (E⁄k).IsElliptic := inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  have hne := TorsionCard.yQuad_ne_zero E x
  have hdeg : (TorsionCard.yQuad E x).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hne, TorsionCard.yQuad_natDegree]
    exact by decide
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨y, (WeierstrassCurve.Affine.equation_iff_nonsingular (W := (E⁄k).toAffine)).mp
    ((TorsionCard.eval_yQuad_eq_zero_iff_equation E x y).mp hy)⟩

/-- **Nonzero `n`-torsion exists exactly when the `n`-division polynomial is
NON-CONSTANT** (PROVEN 2026-07-30), over an algebraically closed field, in
ANY characteristic and for every `n ≠ 0`.

This is the dictionary that lets an existence question about the geometric
torsion be asked instead about a single explicit polynomial over the base
field — `ΨSqₙ` is defined over the base and `natDegree` survives base change
along a field map, so the right-hand side may be read on the base curve.

* `→` is `TorsionCard.smul_some_eq_zero_iff`: a nonzero point is affine, its
  `x`-coordinate is a root of `ΨSqₙ`, and a nonzero polynomial with a root is
  non-constant.
* `←` is the same equivalence run backwards, with `IsAlgClosed.exists_root`
  supplying the `x` and `exists_nonsingular_of_isAlgClosed` the `y`.

Both directions need `ΨSqₙ ≠ 0`, which is `ΨSq_ne_zero` — available with no
characteristic hypothesis, which is why this statement needs none either. In
characteristic `p` at `n = p` it is exactly the ordinary/supersingular
dichotomy: `ΨSqₚ = gᵖ` (`exists_pow_eq_ΨSq_of_charP`), so the right-hand side
reads `deg g ≥ 1`, and `deg g = 0` is the supersingular case `E(k)[p] = 0`. -/
theorem exists_ne_zero_torsion_iff_natDegree_ΨSq_ne_zero [IsAlgClosed k]
    {n : ℤ} (hn : n ≠ 0) :
    (∃ P : (E⁄k).Point, P ≠ 0 ∧ n • P = 0) ↔ ((E⁄k).ΨSq n).natDegree ≠ 0 := by
  haveI : (E⁄k).IsElliptic := inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  have hΨne : (E⁄k).ΨSq n ≠ 0 := ΨSq_ne_zero E hn
  constructor
  · rintro ⟨P, hP0, hPn⟩ hdeg
    obtain ⟨x, y, h, rfl⟩ :
        ∃ (x : k) (y : k) (h : (E⁄k).toAffine.Nonsingular x y),
          P = Affine.Point.some x y h := by
      cases P with
      | zero => exact absurd rfl hP0
      | some x y h => exact ⟨x, y, h, rfl⟩
    have hev : ((E⁄k).ΨSq n).eval x = 0 :=
      (TorsionCard.smul_some_eq_zero_iff E hn h).mp hPn
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, Polynomial.eval_C] at hev
    exact hΨne (by rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, hev, map_zero])
  · intro hdeg
    have hdeg' : ((E⁄k).ΨSq n).degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hΨne]
      exact fun h => hdeg (by exact_mod_cast h)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg'
    obtain ⟨y, h⟩ := exists_nonsingular_of_isAlgClosed E x
    refine ⟨Affine.Point.some x y h, ?_, ?_⟩
    · exact fun hh => nomatch hh.trans (show (0 : (E⁄k).Point) = Affine.Point.zero from rfl)
    · exact (TorsionCard.smul_some_eq_zero_iff E hn h).mpr hx

end TorsionCharP
