import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.FieldTheory.Finite.Basic

universe u

namespace IsDedekindDomain.HeightOneSpectrum

open IsLocalRing Polynomial

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

theorem isAdicComplete_adicCompletionIntegers :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
  sorry

instance henselianLocalRing_adicCompletionIntegers :
    HenselianLocalRing (v.adicCompletionIntegers K) := by
  haveI := isAdicComplete_adicCompletionIntegers v (K := K)
  haveI : HenselianRing (v.adicCompletionIntegers K)
      (maximalIdeal (v.adicCompletionIntegers K)) := inferInstance
  exact ⟨fun f hf a₀ h₁ h₂ => HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)⟩

theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers {r : R} (hr : r ∈ v.asIdeal) :
    algebraMap R (v.adicCompletionIntegers K) r ∈
      maximalIdeal (v.adicCompletionIntegers K) := by
  have h : Valued.v (algebraMap R (v.adicCompletion K) r) < 1 := by
    rw [valuedAdicCompletion_eq_valuation]
    exact (v.valuation_lt_one_iff_mem (K := K) r).2 hr
  exact (Valuation.mem_maximalIdeal_iff _ _).2 h

theorem isUnit_algebraMap_adicCompletionIntegers {r : R} (hr : r ∉ v.asIdeal) :
    IsUnit (algebraMap R (v.adicCompletionIntegers K) r) := by
  have h : ¬ Valued.v (algebraMap R (v.adicCompletion K) r) < 1 := by
    rw [valuedAdicCompletion_eq_valuation, not_lt]
    exact ((v.valuation_eq_one_iff_notMem (K := K)).2 hr).ge
  rw [← IsLocalRing.notMem_maximalIdeal]
  exact fun hmem => h ((Valuation.mem_maximalIdeal_iff _ _).1 hmem)

theorem coe_algebraMap_adicCompletionIntegers (r : R) :
    ((algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap K (v.adicCompletion K) (algebraMap R K r) := rfl

end IsDedekindDomain.HeightOneSpectrum

section Leaves

open IsDedekindDomain IsLocalRing Polynomial

theorem leaf_a (F : Type u) [Field F] [NumberField F] :
    ∃ n : ℕ, ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∈ w.asIdeal →
      ∀ c : NumberField.RingOfIntegers F,
        c - 1 ∈ Ideal.span {(2 : NumberField.RingOfIntegers F) ^ n} →
        ∃ t : w.adicCompletion F,
          t ^ 2 =
            algebraMap F (w.adicCompletion F)
              (algebraMap (NumberField.RingOfIntegers F) F c) := by
  refine ⟨3, fun w hw2 c hc => ?_⟩
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.1 hc
  have hmem : (2 : NumberField.RingOfIntegers F) * e ∈ w.asIdeal := Ideal.mul_mem_right _ _ hw2
  set A : w.adicCompletionIntegers F :=
    algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F) (2 * e) with hA
  have hAmem : A ∈ maximalIdeal (w.adicCompletionIntegers F) :=
    HeightOneSpectrum.algebraMap_mem_maximalIdeal_adicCompletionIntegers w hmem
  set f : (w.adicCompletionIntegers F)[X] := X ^ 2 + X - C A with hf
  have hmonic : f.Monic := by rw [hf]; monicity!
  have heval : f.eval 0 ∈ maximalIdeal (w.adicCompletionIntegers F) := by
    have h0 : f.eval 0 = -A := by simp [hf]
    rw [h0]
    exact neg_mem hAmem
  have hderiv : IsUnit (f.derivative.eval 0) := by
    have h0 : f.derivative.eval 0 = 1 := by simp [hf]
    rw [h0]; exact isUnit_one
  obtain ⟨S, hS, -⟩ := HenselianLocalRing.is_henselian f hmonic 0 heval hderiv
  have hSroot : S ^ 2 + S = A := by
    have h := hS
    rw [Polynomial.IsRoot, hf] at h
    simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h
    linear_combination h
  refine ⟨((1 + 2 * S : w.adicCompletionIntegers F) : w.adicCompletion F), ?_⟩
  have key : (1 + 2 * S : w.adicCompletionIntegers F) ^ 2 =
      algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F) c := by
    have hc' : c = 1 + 2 ^ 3 * e := by linear_combination he
    rw [hc']
    have h8 : algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F)
        (1 + 2 ^ 3 * e) = 1 + 4 * A := by
      rw [hA]
      simp only [map_add, map_mul, map_pow, map_one, map_ofNat]
      ring
    rw [h8]
    linear_combination (4 : w.adicCompletionIntegers F) * hSroot
  rw [← HeightOneSpectrum.coe_algebraMap_adicCompletionIntegers (K := F) w c, ← key]
  push_cast
  ring

theorem leaf_b (F : Type u) [Field F] [NumberField F]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hw2 : (2 : NumberField.RingOfIntegers F) ∉ w.asIdeal)
    (b : NumberField.RingOfIntegers F) (hb : b ∉ w.asIdeal) :
    ∃ x y : w.adicCompletion F,
      x ^ 2 + y ^ 2 =
        algebraMap F (w.adicCompletion F)
          (algebraMap (NumberField.RingOfIntegers F) F b) := by
  have h2unit : IsUnit (2 : w.adicCompletionIntegers F) := by
    have h := HeightOneSpectrum.isUnit_algebraMap_adicCompletionIntegers (K := F) w hw2
    rwa [show algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F)
      (2 : NumberField.RingOfIntegers F) = (2 : w.adicCompletionIntegers F) from
      map_ofNat _ 2] at h
  -- ONE Hensel step, used twice by the symmetry of `x ^ 2 + y ^ 2`
  have step : ∀ p q : NumberField.RingOfIntegers F, p ∉ w.asIdeal →
      p ^ 2 + q ^ 2 - b ∈ w.asIdeal →
      ∃ x y : w.adicCompletion F,
        x ^ 2 + y ^ 2 =
          algebraMap F (w.adicCompletion F)
            (algebraMap (NumberField.RingOfIntegers F) F b) := by
    intro p q hp hpq
    set A : w.adicCompletionIntegers F :=
      algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F) (q ^ 2 - b) with hA
    set a₀ : w.adicCompletionIntegers F :=
      algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F) p with ha₀
    set f : (w.adicCompletionIntegers F)[X] := X ^ 2 + C A with hf
    have hmonic : f.Monic := by rw [hf]; monicity!
    have heval : f.eval a₀ ∈ maximalIdeal (w.adicCompletionIntegers F) := by
      have h0 : f.eval a₀ = algebraMap (NumberField.RingOfIntegers F)
          (w.adicCompletionIntegers F) (p ^ 2 + q ^ 2 - b) := by
        simp only [hf, ha₀, hA, eval_add, eval_pow, eval_X, eval_C]
        simp only [map_add, map_sub, map_pow]
        ring
      rw [h0]
      exact HeightOneSpectrum.algebraMap_mem_maximalIdeal_adicCompletionIntegers w hpq
    have hderiv : IsUnit (f.derivative.eval a₀) := by
      have h0 : f.derivative.eval a₀ = 2 * a₀ := by simp [hf] <;> norm_num
      rw [h0]
      exact h2unit.mul (HeightOneSpectrum.isUnit_algebraMap_adicCompletionIntegers (K := F) w hp)
    obtain ⟨X0, hX0, -⟩ := HenselianLocalRing.is_henselian f hmonic a₀ heval hderiv
    have hroot : X0 ^ 2 + A = 0 := by
      have h := hX0
      rw [Polynomial.IsRoot, hf] at h
      simpa using h
    refine ⟨(X0 : w.adicCompletion F),
      ((algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F) q :
        w.adicCompletionIntegers F) : w.adicCompletion F), ?_⟩
    have key : X0 ^ 2 + (algebraMap (NumberField.RingOfIntegers F)
        (w.adicCompletionIntegers F) q) ^ 2 =
        algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F) b := by
      rw [hA] at hroot
      have h1 : algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F)
          (q ^ 2 - b) =
          (algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F) q) ^ 2 -
            algebraMap (NumberField.RingOfIntegers F) (w.adicCompletionIntegers F) b := by
        simp only [map_sub, map_pow]
      rw [h1] at hroot
      linear_combination hroot
    rw [← HeightOneSpectrum.coe_algebraMap_adicCompletionIntegers (K := F) w b, ← key]
    push_cast
    ring
  -- the residue field computation
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : Finite (NumberField.RingOfIntegers F ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  haveI : Fintype (NumberField.RingOfIntegers F ⧸ w.asIdeal) := Fintype.ofFinite _
  letI : Field (NumberField.RingOfIntegers F ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  have h2k : (2 : NumberField.RingOfIntegers F ⧸ w.asIdeal) ≠ 0 := by
    rw [show (2 : NumberField.RingOfIntegers F ⧸ w.asIdeal) =
      Ideal.Quotient.mk w.asIdeal 2 from (map_ofNat _ 2).symm, Ne,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hw2
  have hcard : Fintype.card (NumberField.RingOfIntegers F ⧸ w.asIdeal) % 2 = 1 := by
    obtain ⟨p, hp⟩ := CharP.exists (NumberField.RingOfIntegers F ⧸ w.asIdeal)
    haveI := hp
    obtain ⟨n, hprime, hcard'⟩ :=
      FiniteField.card (K := NumberField.RingOfIntegers F ⧸ w.asIdeal) p
    have hne2 : p ≠ 2 := by
      rintro rfl
      exact h2k (by simpa using CharP.cast_eq_zero (NumberField.RingOfIntegers F ⧸ w.asIdeal) 2)
    rw [hcard']
    exact Nat.odd_iff.1 ((hprime.odd_of_ne_two hne2).pow)
  set bbar : NumberField.RingOfIntegers F ⧸ w.asIdeal := Ideal.Quotient.mk w.asIdeal b with hbbar
  obtain ⟨xb, yb, hxy⟩ :=
    FiniteField.exists_root_sum_quadratic
      (f := (X : (NumberField.RingOfIntegers F ⧸ w.asIdeal)[X]) ^ 2)
      (g := (X : (NumberField.RingOfIntegers F ⧸ w.asIdeal)[X]) ^ 2 - C bbar) (degree_X_pow 2)
      (degree_X_pow_sub_C (by norm_num) _) hcard
  simp only [eval_pow, eval_X, eval_sub, eval_C] at hxy
  have hbne : bbar ≠ 0 := by
    rw [hbbar, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective xb
  obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective yb
  have hpq : p ^ 2 + q ^ 2 - b ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_add, map_sub, map_pow]
    rw [hp, hq, ← hbbar]
    linear_combination hxy
  by_cases hx0 : xb = 0
  · have hy0 : yb ≠ 0 := by
      intro h
      apply hbne
      rw [hx0, h] at hxy
      linear_combination -hxy
    refine step q p ?_ ?_
    · rw [← Ideal.Quotient.eq_zero_iff_mem, hq]; exact hy0
    · have hswap : q ^ 2 + p ^ 2 - b = p ^ 2 + q ^ 2 - b := by ring
      rw [hswap]; exact hpq
  · refine step p q ?_ ?_
    · rw [← Ideal.Quotient.eq_zero_iff_mem, hp]; exact hx0
    · exact hpq

end Leaves
