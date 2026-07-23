/-
TorsionCardSep.lean — own work for the Fermat project.

The separability node `separable_preΨ'` and the torsion-count
theorems that consume it, split out of `TorsionCard.lean` so that the
proof can use the composition cross-identity `(C)` (`cross_two`) and
the Wronskian identity `(W)` (`wronskian`) — both derived at the
tautological point of the universal curve through machinery that
itself imports `TorsionCard`.
-/
module

public import Fermat.FLT.EllipticCurve.TorsionCard
public import Fermat.FLT.EllipticCurve.WronskianInduction
import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Points
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Fermat.FLT.EllipticCurve.PhiPsiCoprime
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Set.Card

@[expose] public section

namespace TorsionCard

open WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]
  [DecidableEq k]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **The generic chord value** (PROVEN): over an algebraically closed
field there is a value `c` for which `Φₚ − c ⬝ ΨSqₚ` is separable of
degree `p²`, `c` is not a `2`-torsion abscissa, and every root of
`Φₚ − c ⬝ ΨSqₚ` avoids the zeros of `ΨSqₚ` and of `Ψ₂Sq`. The bad
values form a finite set: images under `x ↦ Φₚ(x)/ΨSqₚ(x)` of the
roots of the Wronskian `Φₚ′ΨSqₚ − ΦₚΨSqₚ′ = p ⬝ preΨ₂ₚ ≠ 0` and of
`Ψ₂Sq`, together with the roots of `Ψ₂Sq`. -/
theorem exists_good_chord [IsAlgClosed k] {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hpk : (p : k) ≠ 0) :
    ∃ c : k,
      ((E⁄k).Φ (p : ℤ) -
        Polynomial.C c * (E⁄k).ΨSq (p : ℤ)).Separable ∧
      ((E⁄k).Φ (p : ℤ) -
        Polynomial.C c * (E⁄k).ΨSq (p : ℤ)).natDegree = p ^ 2 ∧
      ((E⁄k).Ψ₂Sq).eval c ≠ 0 ∧
      ∀ x₀ : k, ((E⁄k).Φ (p : ℤ) -
          Polynomial.C c * (E⁄k).ΨSq (p : ℤ)).eval x₀ = 0 →
        ((E⁄k).ΨSq (p : ℤ)).eval x₀ ≠ 0 ∧
          ((E⁄k).Ψ₂Sq).eval x₀ ≠ 0 := by
  classical
  haveI : (E⁄k).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  set Φp := (E⁄k).Φ (p : ℤ) with hΦdef
  set Sp := (E⁄k).ΨSq (p : ℤ) with hSdef
  have hpz : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- no common roots of `Φₚ` and `ΨSqₚ`
  have hnocommon : ∀ x : k, Φp.eval x = 0 → Sp.eval x ≠ 0 := by
    intro x hΦ0 hS0
    obtain ⟨F, G, hFG⟩ := WeierstrassCurve.isCoprime_Φ_ΨSq (E⁄k) hpz
      (WeierstrassCurve.isUnit_Δ _)
    have hev := congrArg (Polynomial.eval x) hFG
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_one, ← hΦdef, ← hSdef, hΦ0, hS0] at hev
    simp at hev
  -- `Ψ₂Sq ≠ 0`
  have hΨ₂ne : (E⁄k).Ψ₂Sq ≠ 0 := by
    intro h0
    have hcop := WeierstrassCurve.isCoprime_Φ_ΨSq (E⁄k)
      (two_ne_zero : (2 : ℤ) ≠ 0) (WeierstrassCurve.isUnit_Δ _)
    rw [WeierstrassCurve.ΨSq_two, h0] at hcop
    have hunit := hcop.isUnit_of_dvd' dvd_rfl (dvd_zero _)
    have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hunit
    rw [WeierstrassCurve.natDegree_Φ (W := (E⁄k)) 2] at hdeg
    norm_num at hdeg
  -- the Wronskian is nonzero
  set Wr := Polynomial.derivative Φp * Sp - Φp * Polynomial.derivative Sp
    with hWrdef
  have hW := PsiSumCompanion.wronskian (E⁄k) (n := p) hp.one_lt.le
  have hSne : Sp ≠ 0 := by
    intro h0
    have hcop := WeierstrassCurve.isCoprime_Φ_ΨSq (E⁄k) hpz
      (WeierstrassCurve.isUnit_Δ _)
    rw [← hSdef, h0] at hcop
    have hunit := hcop.isUnit_of_dvd' dvd_rfl (dvd_zero _)
    have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hunit
    rw [WeierstrassCurve.natDegree_Φ (W := (E⁄k))] at hdeg
    simp only [Int.natAbs_natCast] at hdeg
    have := hp.pos
    have hne : p ^ 2 ≠ 0 := by positivity
    exact hne hdeg
  have hWrne : Wr ≠ 0 := by
    rcases eq_or_ne (2 : k) 0 with hchar2 | hchar2
    · -- char 2 : `Sp′ = 0`, `Wr = Φₚ′ ⬝ Sp ≠ 0`
      have hSodd : Sp = (E⁄k).preΨ' p ^ 2 := by
        rw [hSdef, show ((p : ℤ)) = ((p : ℕ) : ℤ) from rfl,
          WeierstrassCurve.ΨSq_ofNat,
          if_neg (Nat.not_even_iff_odd.mpr hodd), mul_one]
      have hS' : Polynomial.derivative Sp = 0 := by
        rw [hSodd, sq, Polynomial.derivative_mul]
        have h2 : ∀ q : Polynomial k, Polynomial.derivative q * q +
            q * Polynomial.derivative q =
            2 * (q * Polynomial.derivative q) := fun q => by ring
        rw [h2, show ((2 : Polynomial k)) = Polynomial.C (2 : k) from
          (map_ofNat _ 2).symm, hchar2, Polynomial.C_0, zero_mul]
      have hΦ'ne : Polynomial.derivative Φp ≠ 0 := by
        intro h0
        have hc := congrArg (fun q => Polynomial.coeff q (p ^ 2 - 1)) h0
        simp only [Polynomial.coeff_derivative,
          Polynomial.coeff_zero] at hc
        rw [show p ^ 2 - 1 + 1 = p ^ 2 from
            Nat.sub_add_cancel (Nat.one_le_pow 2 p hp.pos)] at hc
        rw [hΦdef, show (p ^ 2) = ((p : ℤ)).natAbs ^ 2 by
          simp, WeierstrassCurve.coeff_Φ, one_mul] at hc
        apply hpk
        have h2 : ((p ^ 2 - 1 + 1 : ℕ) : k) = 0 := by exact_mod_cast hc
        rw [show p ^ 2 - 1 + 1 = p * p by
          rw [Nat.sub_add_cancel (Nat.one_le_pow 2 p hp.pos), sq]] at h2
        push_cast at h2
        rcases mul_eq_zero.mp h2 with h | h <;> exact h
      rw [hWrdef, hS', mul_zero, sub_zero]
      exact mul_ne_zero hΦ'ne hSne
    · -- char ≠ 2 : `Wr = p ⬝ preΨ₂ₚ ≠ 0` by the top coefficient
      rw [hWrdef, hΦdef, hSdef, hW]
      intro h0
      rcases mul_eq_zero.mp h0 with h | h
      · rw [show ((p : Polynomial k)) = Polynomial.C ((p : k)) from
          (Polynomial.C_eq_natCast p).symm, Polynomial.C_eq_zero] at h
        exact hpk h
      · apply WeierstrassCurve.coeff_preΨ_ne_zero (W := (E⁄k))
          (n := 2 * (p : ℤ)) ?_
        · rw [h, Polynomial.coeff_zero]
        · push_cast
          exact mul_ne_zero hchar2 hpk
  -- the bad set and the good value
  set r : k → k := fun x => Φp.eval x / Sp.eval x with hrdef
  set B : Finset k :=
    ((Wr.roots.toFinset ∪ ((E⁄k).Ψ₂Sq).roots.toFinset).image r) ∪
      ((E⁄k).Ψ₂Sq).roots.toFinset with hBdef
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset B
  have hcB1 : ∀ x : k, Wr.eval x = 0 → Sp.eval x ≠ 0 → c ≠ r x := by
    intro x hx _ hcr
    apply hc
    rw [hBdef]
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, ?_, hcr.symm⟩)
    exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
      (Polynomial.mem_roots hWrne |>.mpr hx))
  have hcB2 : ∀ x : k, ((E⁄k).Ψ₂Sq).eval x = 0 → c ≠ r x := by
    intro x hx hcr
    apply hc
    rw [hBdef]
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, ?_, hcr.symm⟩)
    exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr
      (Polynomial.mem_roots hΨ₂ne |>.mpr hx))
  have hcB3 : ((E⁄k).Ψ₂Sq).eval c ≠ 0 := by
    intro hx
    apply hc
    rw [hBdef]
    exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr
      (Polynomial.mem_roots hΨ₂ne |>.mpr hx))
  -- degree
  have hCS : (Polynomial.C c * Sp).natDegree < Φp.natDegree := by
    calc (Polynomial.C c * Sp).natDegree ≤ Sp.natDegree :=
          Polynomial.natDegree_C_mul_le c Sp
      _ ≤ p ^ 2 - 1 := by
          rw [hSdef]
          simpa using WeierstrassCurve.natDegree_ΨSq_le (W := (E⁄k)) (p : ℤ)
      _ < p ^ 2 := by have h := Nat.one_le_pow 2 p hp.pos; omega
      _ = Φp.natDegree := by
          rw [hΦdef, WeierstrassCurve.natDegree_Φ (W := (E⁄k))]
          simp
  have hdeg : (Φp - Polynomial.C c * Sp).natDegree = p ^ 2 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hCS, hΦdef,
      WeierstrassCurve.natDegree_Φ (W := (E⁄k))]
    simp
  -- roots of `Φ − cS` avoid `S` and `Ψ₂Sq`
  have hroots : ∀ x₀ : k, (Φp - Polynomial.C c * Sp).eval x₀ = 0 →
      Sp.eval x₀ ≠ 0 ∧ ((E⁄k).Ψ₂Sq).eval x₀ ≠ 0 := by
    intro x₀ h0
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      sub_eq_zero] at h0
    have hSx : Sp.eval x₀ ≠ 0 := by
      intro hS0
      exact hnocommon x₀ (by rw [h0, hS0, mul_zero]) hS0
    refine ⟨hSx, fun hΨ0 => ?_⟩
    exact hcB2 x₀ hΨ0 (by rw [hrdef]; field_simp [hSx]; linear_combination -h0)
  -- separability
  have hsep : (Φp - Polynomial.C c * Sp).Separable := by
    by_contra hsep
    set g := Φp - Polynomial.C c * Sp with hgdef
    rw [Polynomial.separable_def] at hsep
    have hgcd : ¬IsUnit (EuclideanDomain.gcd g (Polynomial.derivative g)) :=
      fun h => hsep (EuclideanDomain.gcd_isUnit_iff.mp h)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
      (p := EuclideanDomain.gcd g (Polynomial.derivative g))
      (fun h0 => hgcd (Polynomial.isUnit_iff_degree_eq_zero.mpr h0))
    have hgx : g.eval x = 0 :=
      Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
        (EuclideanDomain.gcd_dvd_left g (Polynomial.derivative g)) hx
    have hg'x : (Polynomial.derivative g).eval x = 0 :=
      Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
        (EuclideanDomain.gcd_dvd_right g (Polynomial.derivative g)) hx
    have hSx : Sp.eval x ≠ 0 := (hroots x hgx).1
    have hΦx : Φp.eval x = c * Sp.eval x := by
      have := hgx
      rw [hgdef, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, sub_eq_zero] at this
      exact this
    have hΦ'x : (Polynomial.derivative Φp).eval x =
        c * (Polynomial.derivative Sp).eval x := by
      have h1 := hg'x
      rw [hgdef, Polynomial.derivative_sub, Polynomial.derivative_C_mul,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        sub_eq_zero] at h1
      exact h1
    have hWrx : Wr.eval x = 0 := by
      rw [hWrdef, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_mul, hΦx, hΦ'x]
      ring
    exact hcB1 x hWrx hSx (by
      rw [hrdef]
      field_simp [hSx]
      linear_combination -hΦx)
  exact ⟨c, hsep, hdeg, hcB3, hroots⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- **A fibre of `[p]` of size `p²`** (PROVEN via the generic chord
value): the `p²` roots of `Φₚ − c ⬝ ΨSqₚ` each carry two curve points,
all `2p²` of them mapping under `[p]` into `{R, −R}` for the affine
point `R` with abscissa `c`; the involution `P ↦ −P` exchanges the two
classes, which therefore have `p²` elements each. -/
theorem exists_large_fibre [IsAlgClosed k] {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hpk : (p : k) ≠ 0) :
    ∃ (R : (E⁄k).Point) (S : Finset (E⁄k).Point),
      S.card = p ^ 2 ∧ ∀ P ∈ S, (p : ℤ) • P = R := by
  classical
  haveI : (E⁄k).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  obtain ⟨c, hsep, hdeg, hΨ₂c, hroots⟩ := exists_good_chord E hp hodd hpk
  have hpz : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set g := (E⁄k).Φ (p : ℤ) - Polynomial.C c * (E⁄k).ΨSq (p : ℤ)
    with hgdef
  have hgne : g ≠ 0 := fun h0 => by
    have hd := hdeg
    rw [h0, Polynomial.natDegree_zero] at hd
    have := Nat.one_le_pow 2 p hp.pos
    omega
  set X := g.roots.toFinset with hXdef
  have hXcard : X.card = p ^ 2 := by
    rw [hXdef, Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots hsep),
      Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits g)]
    exact hdeg
  -- the two points above each root
  set Spts := X.biUnion (fun x₀ => pointsAt E x₀) with hSptsdef
  have hdisj : ∀ x₁ ∈ X, ∀ x₂ ∈ X, x₁ ≠ x₂ →
      Disjoint (pointsAt E x₁) (pointsAt E x₂) := by
    intro x₁ _ x₂ _ hne
    rw [Finset.disjoint_left]
    intro P hP1 hP2
    obtain ⟨y₁, h₁, rfl⟩ := (mem_pointsAt_iff E).mp hP1
    obtain ⟨y₂, h₂, hP⟩ := (mem_pointsAt_iff E).mp hP2
    exact hne (Affine.Point.some.inj hP).1
  have hroot_mem : ∀ x₀ ∈ X, g.eval x₀ = 0 := by
    intro x₀ hx₀
    rw [hXdef, Multiset.mem_toFinset, Polynomial.mem_roots hgne] at hx₀
    exact hx₀
  have hpts2 : ∀ x₀ ∈ X, (pointsAt E x₀).card = 2 := by
    intro x₀ hx₀
    have hΨ₂x := (hroots x₀ (hroot_mem x₀ hx₀)).2
    have hsepy := yQuad_separable E hΨ₂x
    rw [pointsAt_card, Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots hsepy),
      Polynomial.splits_iff_card_roots.mp
        (IsAlgClosed.splits (yQuad E x₀)),
      yQuad_natDegree]
  have hSpts_card : Spts.card = 2 * p ^ 2 := by
    rw [hSptsdef, Finset.card_biUnion hdisj,
      Finset.sum_congr rfl hpts2, Finset.sum_const, hXcard]
    ring
  -- the common image abscissa
  have hkey : ∀ P ∈ Spts, ∃ (y' : k)
      (h' : (E⁄k).toAffine.Nonsingular c y'),
      (p : ℤ) • P = Affine.Point.some c y' h' := by
    intro P hP
    obtain ⟨x₀, hx₀, hPx⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨y₀, h₀, rfl⟩ := (mem_pointsAt_iff E).mp hPx
    have hS0 := (hroots x₀ (hroot_mem x₀ hx₀)).1
    obtain ⟨x', y', h', heq, hx'⟩ :=
      exists_smul_some_eq E hpz h₀ hS0
    have hxc : x' = c := by
      have hg0 := hroot_mem x₀ hx₀
      rw [hgdef, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, sub_eq_zero] at hg0
      exact mul_right_cancel₀ hS0 (hx'.trans hg0)
    subst hxc
    exact ⟨y', h', heq⟩
  -- the base point and its image
  have hXne : X.Nonempty := by
    rw [← Finset.card_pos, hXcard]
    have := Nat.one_le_pow 2 p hp.pos
    omega
  obtain ⟨x₁, hx₁⟩ := hXne
  have hpts1 : (pointsAt E x₁).Nonempty := by
    rw [← Finset.card_pos, hpts2 x₁ hx₁]
    norm_num
  obtain ⟨P₀, hP₀⟩ := hpts1
  have hP₀S : P₀ ∈ Spts := Finset.mem_biUnion.mpr ⟨x₁, hx₁, hP₀⟩
  obtain ⟨d, hd, hR⟩ := hkey P₀ hP₀S
  set R : (E⁄k).Point := Affine.Point.some c d hd with hRdef
  -- `R` is not `2`-torsion: `ψ₂(R)² = Ψ₂Sq(c) ≠ 0`
  have hs2 : 2 * d + (E⁄k).a₁ * c + (E⁄k).a₃ ≠ 0 := by
    intro h0
    apply hΨ₂c
    have hsq := congrArg (Polynomial.evalEvalRingHom c d)
      (WeierstrassCurve.C_Ψ₂Sq (W := (E⁄k)))
    simp only [map_sub, map_mul, map_pow, map_ofNat] at hsq
    rw [Polynomial.coe_evalEvalRingHom] at hsq
    have heq0 : ((E⁄k).toAffine.polynomial).evalEval c d = 0 := hd.1
    rw [Polynomial.evalEval_C] at hsq
    rw [show ((E⁄k).ψ₂).evalEval c d =
        2 * d + (E⁄k).a₁ * c + (E⁄k).a₃ from by
      rw [WeierstrassCurve.ψ₂, Affine.evalEval_polynomialY], h0,
      heq0] at hsq
    rw [hsq]
    ring
  have hRneg : R ≠ -R := by
    rw [hRdef, Affine.Point.neg_some]
    intro hc
    obtain ⟨-, hy⟩ := Affine.Point.some.inj hc
    apply hs2
    rw [Affine.negY] at hy
    linear_combination hy
  -- dichotomy of the images
  have himg : ∀ P ∈ Spts, (p : ℤ) • P = R ∨ (p : ℤ) • P = -R := by
    intro P hP
    obtain ⟨y', h', heq⟩ := hkey P hP
    rcases Affine.Y_eq_of_X_eq h'.1 hd.1 rfl with hy | hy
    · left
      rw [heq, hRdef]
      subst hy
      rfl
    · right
      rw [heq, hRdef, Affine.Point.neg_some]
      subst hy
      rfl
  set SR := Spts.filter (fun P => (p : ℤ) • P = R) with hSRdef
  set SN := Spts.filter (fun P => (p : ℤ) • P = -R) with hSNdef
  have hcover : Spts = SR ∪ SN := by
    ext P
    simp only [hSRdef, hSNdef, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hP
      rcases himg P hP with h | h
      · exact Or.inl ⟨hP, h⟩
      · exact Or.inr ⟨hP, h⟩
    · rintro (⟨hP, -⟩ | ⟨hP, -⟩) <;> exact hP
  have hdisj2 : Disjoint SR SN := by
    rw [Finset.disjoint_left]
    rintro P hP1 hP2
    rw [hSRdef, Finset.mem_filter] at hP1
    rw [hSNdef, Finset.mem_filter] at hP2
    exact hRneg (hP1.2.symm.trans hP2.2)
  have hsum : SR.card + SN.card = 2 * p ^ 2 := by
    rw [← Finset.card_union_of_disjoint hdisj2, ← hcover, hSpts_card]
  have hnegmem : ∀ P ∈ Spts, -P ∈ Spts := by
    intro P hP
    obtain ⟨x₀, hx₀, hPx⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨y₀, h₀, rfl⟩ := (mem_pointsAt_iff E).mp hPx
    refine Finset.mem_biUnion.mpr ⟨x₀, hx₀, ?_⟩
    rw [Affine.Point.neg_some]
    exact (mem_pointsAt_iff E).mpr ⟨_, _, rfl⟩
  have hbij : SR.card = SN.card := by
    apply Finset.card_bij (fun P _ => -P)
    · intro P hP
      rw [hSNdef, Finset.mem_filter]
      rw [hSRdef, Finset.mem_filter] at hP
      exact ⟨hnegmem P hP.1, by rw [smul_neg, hP.2]⟩
    · intro P _ Q _ h
      exact neg_injective h
    · intro Q hQ
      rw [hSNdef, Finset.mem_filter] at hQ
      refine ⟨-Q, ?_, neg_neg Q⟩
      rw [hSRdef, Finset.mem_filter]
      exact ⟨hnegmem Q hQ.1, by rw [smul_neg, hQ.2, neg_neg]⟩
  refine ⟨R, SR, by omega, ?_⟩
  intro P hP
  exact (Finset.mem_filter.mp hP).2


set_option backward.isDefEq.respectTransparency false in
omit [E.IsElliptic] in
/-- **Torsion lower bound from a large fibre** (PROVEN): fibres of the
group homomorphism `[p]` are cosets of the kernel — the shift
`P ↦ P − P₀` carries a fibre of size `p²` into the `p`-torsion. -/
theorem torsion_finset_of_fibre {p : ℕ}
    (h : ∃ (R : (E⁄k).Point) (S : Finset (E⁄k).Point),
      S.card = p ^ 2 ∧ ∀ P ∈ S, (p : ℤ) • P = R) :
    ∃ T : Finset (E⁄k).Point, T.card = p ^ 2 ∧
      ∀ P ∈ T, (p : ℤ) • P = 0 := by
  obtain ⟨R, S, hcard, hall⟩ := h
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨S, hcard, fun P _ => by simp⟩
  have hne : S.Nonempty := by
    rw [← Finset.card_pos, hcard]
    positivity
  obtain ⟨P₀, hP₀⟩ := hne
  refine ⟨S.image (fun P => P - P₀), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (sub_left_injective)]
    exact hcard
  · intro Q hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    rw [smul_sub, hall P hP, hall P₀ hP₀, sub_self]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Separability from the torsion count, backwards** (PROVEN): a
`p`-torsion finset of size `p²` has `p² − 1` nonzero points, which
map to roots of `preΨ' p` (the dictionary) with fibres of size at
most `2` (the `y`-quadratic), so `preΨ' p` has at least
`(p²−1)/2 = natDegree`-many distinct roots — hence exactly that many,
so it splits with no repeated roots and is separable. -/
theorem separable_of_torsion_finset {p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hpk : (p : k) ≠ 0)
    (hT : ∃ T : Finset (E⁄k).Point, T.card = p ^ 2 ∧
      ∀ P ∈ T, (p : ℤ) • P = 0) :
    ((E⁄k).preΨ' p).Separable := by
  classical
  obtain ⟨T, hcard, hall⟩ := hT
  set f := (E⁄k).preΨ' p with hfdef
  have hpz : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hfne : f ≠ 0 := by
    intro h0
    apply WeierstrassCurve.coeff_preΨ'_ne_zero (W := (E⁄k)) hpk
    rw [← hfdef, h0, Polynomial.coeff_zero]
  -- the total coordinate functions
  let xc : (E⁄k).Point → k := fun P =>
    match P with
    | .zero => 0
    | @Affine.Point.some _ _ _ x _ _ => x
  let yc : (E⁄k).Point → k := fun P =>
    match P with
    | .zero => 0
    | @Affine.Point.some _ _ _ _ y _ => y
  -- nonzero torsion maps into the roots of `f`
  have hmaps : ∀ P ∈ T.erase 0, xc P ∈ f.roots.toFinset := by
    intro P hP
    have hPne : P ≠ 0 := Finset.ne_of_mem_erase hP
    have hPT : P ∈ T := Finset.mem_of_mem_erase hP
    cases P with
    | zero => exact absurd rfl hPne
    | @some x y h =>
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hfne]
      have h0 := hall _ hPT
      rw [smul_some_eq_zero_iff E hpz h] at h0
      rw [WeierstrassCurve.ΨSq_ofNat,
        if_neg (Nat.not_even_iff_odd.mpr hodd), mul_one,
        Polynomial.eval_pow] at h0
      exact pow_eq_zero_iff two_ne_zero |>.mp h0
  -- fibres of the `x`-coordinate have at most two elements
  have hfibre : ∀ x₀ ∈ f.roots.toFinset,
      ((T.erase 0).filter (fun P => xc P = x₀)).card ≤ 2 := by
    intro x₀ _
    have hstep : ((T.erase 0).filter (fun P => xc P = x₀)).card ≤
        (yQuad E x₀).roots.toFinset.card :=
      Finset.card_le_card_of_injOn yc ?_ ?_
    · refine hstep.trans ?_
      calc (yQuad E x₀).roots.toFinset.card
          ≤ Multiset.card (yQuad E x₀).roots :=
            Multiset.toFinset_card_le _
        _ ≤ (yQuad E x₀).natDegree := Polynomial.card_roots' _
        _ = 2 := yQuad_natDegree E x₀
    · intro P hP
      obtain ⟨hP', hx⟩ := Finset.mem_filter.mp hP
      have hPne : P ≠ 0 := Finset.ne_of_mem_erase hP'
      cases P with
      | zero => exact absurd rfl hPne
      | @some x y h =>
        have hxx : x = x₀ := hx
        subst hxx
        rw [Finset.mem_coe, Multiset.mem_toFinset,
          Polynomial.mem_roots (yQuad_ne_zero E x)]
        exact (eval_yQuad_eq_zero_iff_equation E x y).mpr h.1
    · intro P hP Q hQ hy
      obtain ⟨hP', hxP⟩ := Finset.mem_filter.mp hP
      obtain ⟨hQ', hxQ⟩ := Finset.mem_filter.mp hQ
      have hPne : P ≠ 0 := Finset.ne_of_mem_erase hP'
      have hQne : Q ≠ 0 := Finset.ne_of_mem_erase hQ'
      cases P with
      | zero => exact absurd rfl hPne
      | @some xP yP hP'' =>
        cases Q with
        | zero => exact absurd rfl hQne
        | @some xQ yQ hQ'' =>
          have h1 : xP = x₀ := hxP
          have h2 : xQ = x₀ := hxQ
          have hxx : xQ = xP := h2.trans h1.symm
          have h3 : yP = yQ := hy
          subst hxx
          subst h3
          rfl
  have hcount := Finset.card_le_mul_card_image_of_maps_to hmaps 2 hfibre
  have herase : p ^ 2 - 1 ≤ (T.erase 0).card := by
    have h := Finset.pred_card_le_card_erase (s := T) (a := 0)
    omega
  have hnoteven : ¬ Even p := Nat.not_even_iff_odd.mpr hodd
  have hdeg : f.natDegree = (p ^ 2 - 1) / 2 := by
    rw [hfdef, WeierstrassCurve.natDegree_preΨ' (W := (E⁄k)) hpk,
      if_neg hnoteven]
  have hle : f.roots.toFinset.card ≤ Multiset.card f.roots :=
    Multiset.toFinset_card_le _
  have hle2 : Multiset.card f.roots ≤ f.natDegree :=
    Polynomial.card_roots' _
  have hp2 : p ^ 2 - 1 = 2 * ((p ^ 2 - 1) / 2) := by
    obtain ⟨s, _⟩ := hodd.pow (n := 2)
    omega
  have h1 : f.roots.toFinset.card = f.natDegree := by omega
  have h2 : Multiset.card f.roots = f.natDegree := by omega
  have hnodup : f.roots.Nodup :=
    Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega)
  have hsplits : f.Splits := Polynomial.splits_iff_card_roots.mpr h2
  exact (Polynomial.nodup_roots_iff_of_splits hfne hsplits).mp hnodup

set_option backward.isDefEq.respectTransparency false in
/-- **Separability in characteristic two over an algebraically closed
field** (DECOMPOSED 2026-07-17 into the three generic-fibre-counting
nodes above; the characteristic-two hypothesis is not even needed on
this route). -/
theorem separable_preΨ'_char_two_closed {K : Type u} [Field K]
    [IsAlgClosed K] (E' : WeierstrassCurve K) [E'.IsElliptic]
    [DecidableEq K] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpk : (p : K) ≠ 0) (_ : (2 : K) = 0) :
    ((E'⁄K).preΨ' p).Separable :=
  separable_of_torsion_finset E' hp hodd hpk
    (torsion_finset_of_fibre E' (exists_large_fibre E' hp hodd hpk))

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq k] in
/-- **Separability in characteristic two** (DECOMPOSED 2026-07-17):
reduced to the algebraically closed case by the separability
transfer along the base change to `AlgebraicClosure k`. -/
theorem separable_preΨ'_char_two {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpk : (p : k) ≠ 0) (hchar2 : (2 : k) = 0) :
    ((E⁄k).preΨ' p).Separable := by
  classical
  set K := AlgebraicClosure k
  set φ : k →+* K := algebraMap k K
  haveI : (E.map φ).IsElliptic :=
    inferInstanceAs ((E.map φ).IsElliptic)
  have hpK : (p : K) ≠ 0 := by
    intro h0
    apply hpk
    have : φ ((p : k)) = (p : K) := map_natCast φ p
    exact (map_eq_zero φ).mp (this.trans h0 : φ ((p : k)) = 0)
  have hchar2K : (2 : K) = 0 := by
    have : φ ((2 : k)) = (2 : K) := map_ofNat φ 2
    rw [← this, hchar2, map_zero]
  have hclosed := separable_preΨ'_char_two_closed (E.map φ) hp hodd
    hpK hchar2K
  have hcurve : (E⁄k).map φ = ((E.map φ)⁄K) := by
    show (E.map (algebraMap k k)).map φ = (E.map φ).map (algebraMap K K)
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    congr 1
  have hpoly : ((E⁄k).preΨ' p).map φ = ((E.map φ)⁄K).preΨ' p :=
    (WeierstrassCurve.map_preΨ' (W := (E⁄k)) (f := φ) p).symm.trans
      (congrArg (fun W => WeierstrassCurve.preΨ' W p) hcurve)
  rw [← Polynomial.separable_map φ, hpoly]
  exact hclosed



set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Separability of the division polynomial** (PROVEN 2026-07-17 in
characteristic `≠ 2` via the multiplicity endgame; characteristic two
is the separate node above): for an odd prime `p` invertible in `k`,
the reduced `p`-division polynomial `preΨ' p` is separable. If `π`
were a common irreducible factor of `f := preΨ′ₚ` and `f′` with
`f = πᵃg`, `π ∤ g`, then `π^{a+1} ∣ (ΨSqₚ)′ = 2ff′`, the Wronskian
identity `(W)` gives `π^{a+1} ∣ preΨ₂ₚ`, hence
`π^{2a+1} ∣ ΨSq₂ₚ = preΨ′₂ₚ² Ψ₂Sq`; the composition cross-identity
`(C)` and coprimality of `Φ₂ₚ, ΨSq₂ₚ` push this to
`π^{2a+1} ∣ H = ΨSqₚ ⬝ H₁`, so `π ∣ H₁ ≡ 4Φₚ³ (mod ΨSqₚ)`, forcing
`π ∣ Φₚ` — contradicting the coprimality of `Φₚ, ΨSqₚ`. -/
theorem separable_preΨ' {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpk : (p : k) ≠ 0) :
    ((E⁄k).preΨ' p).Separable := by
  haveI : (E⁄k).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  rcases eq_or_ne (2 : k) 0 with hchar2 | hchar2
  · exact separable_preΨ'_char_two E hp hodd hpk hchar2
  by_contra hsep
  set f := (E⁄k).preΨ' p with hfdef
  -- `f ≠ 0` since its top coefficient is nonzero
  have hfne : f ≠ 0 := by
    intro h0
    apply WeierstrassCurve.coeff_preΨ'_ne_zero (W := (E⁄k)) hpk
    rw [← hfdef, h0, Polynomial.coeff_zero]
  -- a common irreducible factor of `f` and `f′`
  rw [Polynomial.separable_def] at hsep
  have hgcd : ¬IsUnit (EuclideanDomain.gcd f (Polynomial.derivative f)) :=
    fun h => hsep (EuclideanDomain.gcd_isUnit_iff.mp h)
  have hgcdne : EuclideanDomain.gcd f (Polynomial.derivative f) ≠ 0 := by
    intro h0
    exact hfne ((EuclideanDomain.gcd_eq_zero_iff.mp h0).1)
  obtain ⟨π, hπirr, hπgcd⟩ :=
    WfDvdMonoid.exists_irreducible_factor hgcd hgcdne
  have hπprime : Prime π := hπirr.prime
  have hπf : π ∣ f := hπgcd.trans (EuclideanDomain.gcd_dvd_left _ _)
  have hπf' : π ∣ Polynomial.derivative f :=
    hπgcd.trans (EuclideanDomain.gcd_dvd_right _ _)
  -- the exact power decomposition
  obtain ⟨a, g, hπg, hfg⟩ := WfDvdMonoid.max_power_factor hfne hπirr
  have ha : 1 ≤ a := by
    by_contra hc
    rw [Nat.lt_one_iff.mp (not_le.mp hc), pow_zero, one_mul] at hfg
    exact hπg (hfg ▸ hπf)
  -- `ΨSqₚ = f²`
  have hΨodd : (E⁄k).ΨSq ((p : ℕ) : ℤ) = f ^ 2 := by
    rw [WeierstrassCurve.ΨSq_ofNat,
      if_neg (Nat.not_even_iff_odd.mpr hodd), mul_one, hfdef]
  -- step 3: `π^{a+1} ∣ (ΨSqₚ)′ = f′f + ff′`
  have hpowf : π ^ a ∣ f := hfg ▸ dvd_mul_right _ _
  have hΨ' : π ^ (a + 1) ∣ Polynomial.derivative ((E⁄k).ΨSq (p : ℤ)) := by
    rw [show ((p : ℤ)) = ((p : ℕ) : ℤ) from rfl, hΨodd, sq,
      Polynomial.derivative_mul]
    refine dvd_add ?_ ?_
    · rw [pow_succ']
      exact mul_dvd_mul hπf' hpowf
    · rw [pow_succ]
      exact mul_dvd_mul hpowf hπf'
  -- step 4–5: the Wronskian identity gives `π^{a+1} ∣ preΨ₂ₚ`
  have hpsq : π ^ (2 * a) ∣ (E⁄k).ΨSq (p : ℤ) := by
    rw [show ((p : ℤ)) = ((p : ℕ) : ℤ) from rfl, hΨodd, sq, two_mul,
      pow_add]
    exact mul_dvd_mul hpowf hpowf
  have hW := PsiSumCompanion.wronskian (E⁄k) (n := p) hp.one_lt.le
  have hpre : π ^ (a + 1) ∣ (p : Polynomial k) * (E⁄k).preΨ (2 * (p : ℤ)) := by
    rw [← hW]
    refine dvd_sub ?_ ?_
    · exact ((pow_dvd_pow π (by omega : a + 1 ≤ 2 * a)).trans
        hpsq).mul_left _
    · exact hΨ'.mul_left _
  have hpre' : π ^ (a + 1) ∣ (E⁄k).preΨ (2 * (p : ℤ)) := by
    have h2 : π ^ (a + 1) ∣ Polynomial.C (((p : k))⁻¹) *
        ((p : Polynomial k) * (E⁄k).preΨ (2 * (p : ℤ))) := hpre.mul_left _
    rwa [← Polynomial.C_eq_natCast, ← mul_assoc, ← Polynomial.C_mul,
      inv_mul_cancel₀ hpk, Polynomial.C_1, one_mul] at h2
  -- step 6: `π^{2a+1} ∣ ΨSq₂ₚ`
  have hΨ2p : π ^ (2 * a + 1) ∣ (E⁄k).ΨSq (2 * (p : ℤ)) := by
    have hcast : (2 * (p : ℤ)) = ((2 * p : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, WeierstrassCurve.ΨSq_ofNat, if_pos (even_two_mul p)]
    have hpre'' : π ^ (a + 1) ∣ (E⁄k).preΨ' (2 * p) := by
      rw [← WeierstrassCurve.preΨ_ofNat, ← hcast]
      exact hpre'
    refine dvd_mul_of_dvd_left ?_ _
    calc π ^ (2 * a + 1) ∣ π ^ (2 * (a + 1)) :=
          pow_dvd_pow π (by omega)
      _ = π ^ (a + 1) * π ^ (a + 1) := by ring
      _ ∣ (E⁄k).preΨ' (2 * p) ^ 2 := by
          rw [sq]
          exact mul_dvd_mul hpre'' hpre''
  -- step 7: the composition cross-identity pushes it to `H`
  have hcross := PsiSumCompanion.cross_two (E⁄k)
    (n := (p : ℤ)) (by exact_mod_cast hp.ne_zero)
  have hπΨ2p : π ∣ (E⁄k).ΨSq (2 * (p : ℤ)) :=
    (dvd_pow_self π (by omega : 2 * a + 1 ≠ 0)).trans hΨ2p
  have hΦ2p : ¬ π ∣ (E⁄k).Φ (2 * (p : ℤ)) := by
    intro hd
    exact hπirr.not_isUnit
      ((WeierstrassCurve.isCoprime_Φ_ΨSq (E⁄k)
        (by have := hp.pos; omega : (2 * (p : ℤ)) ≠ 0)
        (WeierstrassCurve.isUnit_Δ _)).isUnit_of_dvd' hd hπΨ2p)
  have hH : π ^ (2 * a + 1) ∣
      (4 * (E⁄k).Φ (p : ℤ) ^ 3 * (E⁄k).ΨSq (p : ℤ) +
        Polynomial.C (E⁄k).b₂ * (E⁄k).Φ (p : ℤ) ^ 2 *
          (E⁄k).ΨSq (p : ℤ) ^ 2 +
        2 * Polynomial.C (E⁄k).b₄ * (E⁄k).Φ (p : ℤ) *
          (E⁄k).ΨSq (p : ℤ) ^ 3 +
        Polynomial.C (E⁄k).b₆ * (E⁄k).ΨSq (p : ℤ) ^ 4) := by
    refine hπprime.pow_dvd_of_dvd_mul_left _ hΦ2p ?_
    rw [hcross]
    exact (hΨ2p.mul_right _)
  -- step 8: factor `H = ΨSqₚ ⬝ H₁ = π^{2a} (g² H₁)` and cancel
  set H₁ : Polynomial k := 4 * (E⁄k).Φ (p : ℤ) ^ 3 +
    Polynomial.C (E⁄k).b₂ * (E⁄k).Φ (p : ℤ) ^ 2 * (E⁄k).ΨSq (p : ℤ) +
    2 * Polynomial.C (E⁄k).b₄ * (E⁄k).Φ (p : ℤ) *
      (E⁄k).ΨSq (p : ℤ) ^ 2 +
    Polynomial.C (E⁄k).b₆ * (E⁄k).ΨSq (p : ℤ) ^ 3 with hH₁def
  have hHfac : (4 * (E⁄k).Φ (p : ℤ) ^ 3 * (E⁄k).ΨSq (p : ℤ) +
      Polynomial.C (E⁄k).b₂ * (E⁄k).Φ (p : ℤ) ^ 2 *
        (E⁄k).ΨSq (p : ℤ) ^ 2 +
      2 * Polynomial.C (E⁄k).b₄ * (E⁄k).Φ (p : ℤ) *
        (E⁄k).ΨSq (p : ℤ) ^ 3 +
      Polynomial.C (E⁄k).b₆ * (E⁄k).ΨSq (p : ℤ) ^ 4) =
      π ^ (2 * a) * (g ^ 2 * H₁) := by
    rw [hH₁def, show (E⁄k).ΨSq (p : ℤ) = π ^ (2 * a) * g ^ 2 by
      rw [show ((p : ℤ)) = ((p : ℕ) : ℤ) from rfl, hΨodd, hfg]
      ring]
    ring
  have hg2H₁ : π ∣ g ^ 2 * H₁ := by
    have h1 : π ^ (2 * a) * π ∣ π ^ (2 * a) * (g ^ 2 * H₁) := by
      rw [← hHfac, ← pow_succ]
      exact hH
    exact (mul_dvd_mul_iff_left (pow_ne_zero (2 * a)
      hπprime.ne_zero)).mp h1
  have hπH₁ : π ∣ H₁ := by
    rcases hπprime.dvd_mul.mp hg2H₁ with hd | hd
    · exact absurd (hπprime.dvd_of_dvd_pow hd) hπg
    · exact hd
  -- step 9: `H₁ ≡ 4Φₚ³ (mod ΨSqₚ)`, so `π ∣ Φₚ`
  have hπΨp : π ∣ (E⁄k).ΨSq (p : ℤ) := by
    rw [show ((p : ℤ)) = ((p : ℕ) : ℤ) from rfl, hΨodd]
    exact hπf.trans (dvd_pow_self f two_ne_zero)
  have hπ4Φ : π ∣ 4 * (E⁄k).Φ (p : ℤ) ^ 3 := by
    have hdiff : H₁ - 4 * (E⁄k).Φ (p : ℤ) ^ 3 =
        (E⁄k).ΨSq (p : ℤ) *
          (Polynomial.C (E⁄k).b₂ * (E⁄k).Φ (p : ℤ) ^ 2 +
            2 * Polynomial.C (E⁄k).b₄ * (E⁄k).Φ (p : ℤ) *
              (E⁄k).ΨSq (p : ℤ) +
            Polynomial.C (E⁄k).b₆ * (E⁄k).ΨSq (p : ℤ) ^ 2) := by
      rw [hH₁def]
      ring
    have h2 : π ∣ H₁ - 4 * (E⁄k).Φ (p : ℤ) ^ 3 :=
      hdiff ▸ hπΨp.mul_right _
    have h3 := dvd_sub hπH₁ h2
    rwa [sub_sub_cancel] at h3
  have h4unit : IsUnit (4 : Polynomial k) := by
    have h4 : (4 : k) ≠ 0 := by
      intro h0
      apply hchar2
      have h22 : (2 : k) * 2 = 0 := by
        rw [show (2 : k) * 2 = 4 by norm_num, h0]
      exact mul_self_eq_zero.mp h22
    rw [show (4 : Polynomial k) = Polynomial.C (4 : k) from (map_ofNat _ 4).symm]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr h4)
  have hπΦ : π ∣ (E⁄k).Φ (p : ℤ) := by
    have h3 : π ∣ (E⁄k).Φ (p : ℤ) ^ 3 := by
      rcases hπprime.dvd_mul.mp hπ4Φ with h | h
      · exact absurd (isUnit_of_dvd_unit h h4unit) hπirr.not_isUnit
      · exact h
    exact hπprime.dvd_of_dvd_pow h3
  exact hπirr.not_isUnit
    ((WeierstrassCurve.isCoprime_Φ_ΨSq (E⁄k)
      (by exact_mod_cast hp.ne_zero : ((p : ℤ)) ≠ 0)
      (WeierstrassCurve.isUnit_Δ _)).isUnit_of_dvd' hπΦ hπΨp)


set_option backward.isDefEq.respectTransparency false in
/-- **The prime-level count** (DERIVED 2026-07-17 from the dictionary
node and the three division-polynomial separability/coprimality
nodes): for a prime `p` with `(p : k) ≠ 0`, the `p`-torsion of an
elliptic curve over a separably closed field has exactly `p²`
elements. The nonzero `p`-torsion is fibred over the roots of the
relevant division polynomial (`preΨ' p` for odd `p`, with two points
per root since the `y`-fibre quadratic is separable there by the
coprimality node; `Ψ₂Sq` for `p = 2`, with one point per root since
the quadratic is then a square), and the separability nodes count the
roots: `2 ⬝ (p² - 1)/2` resp. `1 ⬝ 3` of them. -/
theorem prime_torsion_card [IsSepClosed k] {p : ℕ} (hp : p.Prime)
    (hchar : (p : k) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (E⁄k).Point p) = p ^ 2 := by
  classical
  haveI : (E⁄k).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  have hpZ : ((p : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  have hpkZ : (((p : ℕ) : ℤ) : k) ≠ 0 := by exact_mod_cast hchar
  -- the counting skeleton, shared between `p = 2` and odd `p`:
  -- a separable polynomial `g` whose roots are the torsion
  -- `x`-coordinates, and a uniform `y`-fibre count `m`
  have key : ∀ (g : Polynomial k) (m : ℕ), g.Separable →
      (∀ x₀ y (h : (E⁄k).toAffine.Nonsingular x₀ y),
        ((p : ℤ) • (Affine.Point.some x₀ y h : (E⁄k).Point) = 0 ↔
          g.eval x₀ = 0)) →
      (∀ x₀, g.eval x₀ = 0 → (yQuad E x₀).roots.toFinset.card = m) →
      Nat.card (Submodule.torsionBy ℤ (E⁄k).Point p) =
        1 + m * g.natDegree := by
    intro g m hgsep hdict hfib
    have hg0 : g ≠ 0 := hgsep.ne_zero
    -- the root finset of `g`
    have hgroots : g.roots.toFinset.card = g.natDegree := by
      rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hgsep)]
      exact (IsSepClosed.splits_of_separable g hgsep).natDegree_eq_card_roots.symm
    -- the finset of nonzero `p`-torsion points
    set F : Finset ((E⁄k).Point) := g.roots.toFinset.biUnion (pointsAt E)
      with hF
    have hdisj : ∀ x₁ ∈ g.roots.toFinset, ∀ x₂ ∈ g.roots.toFinset, x₁ ≠ x₂ →
        Disjoint (pointsAt E x₁) (pointsAt E x₂) := by
      intro x₁ _ x₂ _ hne
      refine Finset.disjoint_left.mpr fun P hP₁ hP₂ => ?_
      obtain ⟨y₁, h₁, rfl⟩ := (mem_pointsAt_iff E).mp hP₁
      obtain ⟨y₂, h₂, hP⟩ := (mem_pointsAt_iff E).mp hP₂
      simp only [Affine.Point.some.injEq] at hP
      exact hne hP.1
    have hFcard : F.card = m * g.natDegree := by
      rw [hF, Finset.card_biUnion hdisj,
        Finset.sum_congr rfl fun x₀ hx₀ => (pointsAt_card E x₀).trans
          (hfib x₀ (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hx₀)).2),
        Finset.sum_const, smul_eq_mul, hgroots, mul_comm]
    -- the torsion submodule is `{0} ∪ F` as a set
    have hset : (Submodule.torsionBy ℤ (E⁄k).Point p : Set ((E⁄k).Point)) =
        ↑(insert (0 : (E⁄k).Point) F) := by
      ext P
      simp only [SetLike.mem_coe, Submodule.mem_torsionBy_iff,
        Finset.coe_insert, Set.mem_insert_iff]
      constructor
      · intro hP
        cases P with
        | zero => exact Or.inl rfl
        | some x y h =>
          refine Or.inr (Finset.mem_biUnion.mpr ⟨x, ?_,
            (mem_pointsAt_iff E).mpr ⟨y, h, rfl⟩⟩)
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0]
          exact (hdict x y h).mp hP
      · rintro (rfl | hP)
        · exact smul_zero _
        · obtain ⟨x₀, hx₀, hPx⟩ := Finset.mem_biUnion.mp hP
          obtain ⟨y, h, rfl⟩ := (mem_pointsAt_iff E).mp hPx
          exact (hdict x₀ y h).mpr
            (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hx₀)).2
    -- count
    calc Nat.card (Submodule.torsionBy ℤ (E⁄k).Point p)
        = Set.ncard (Submodule.torsionBy ℤ (E⁄k).Point p :
            Set ((E⁄k).Point)) := (Nat.card_coe_set_eq _)
      _ = (insert (0 : (E⁄k).Point) F).card := by
          rw [hset, Set.ncard_coe_finset]
      _ = 1 + m * g.natDegree := by
          rw [Finset.card_insert_of_notMem, hFcard, add_comm]
          intro h0
          obtain ⟨x₀, -, hPx⟩ := Finset.mem_biUnion.mp h0
          exact zero_notMem_pointsAt E x₀ hPx
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- `p = 2`: one point per root of the two-torsion cubic
    have h2 : (2 : k) ≠ 0 := by exact_mod_cast hchar
    have hdeg : ((E⁄k).Ψ₂Sq).natDegree = 3 := by
      have h4 : (4 : k) ≠ 0 := by
        intro h
        exact h2 (by
          have : (4 : k) = 2 * 2 := by norm_num
          rcases mul_eq_zero.mp (this ▸ h) with h' | h' <;> exact h')
      rw [WeierstrassCurve.Ψ₂Sq]
      compute_degree!
    rw [key ((E⁄k).Ψ₂Sq) 1 (separable_Ψ₂Sq E h2) ?_ ?_, hdeg]
    · norm_num
    · -- the dictionary at `2` is `ΨSq 2 = Ψ₂Sq`
      intro x₀ y h
      have := smul_some_eq_zero_iff E (by norm_num : (2 : ℤ) ≠ 0) h
      rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) from rfl, this, WeierstrassCurve.ΨSq_two]
    · -- one `y` above each two-torsion `x`-coordinate
      intro x₀ hx₀
      have hval : ((E⁄k).a₁ * x₀ + (E⁄k).a₃) ^ 2 +
          4 * (x₀ ^ 3 + (E⁄k).a₂ * x₀ ^ 2 + (E⁄k).a₄ * x₀ + (E⁄k).a₆) = 0 := by
        have hv : ((E⁄k).Ψ₂Sq).eval x₀ =
            ((E⁄k).a₁ * x₀ + (E⁄k).a₃) ^ 2 +
              4 * (x₀ ^ 3 + (E⁄k).a₂ * x₀ ^ 2 + (E⁄k).a₄ * x₀ + (E⁄k).a₆) := by
          rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
            WeierstrassCurve.b₆]
          simp only [Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
          ring
        rw [← hv, hx₀]
      -- the unique `y`-root is `-(c/2)`
      have hroot : ∀ y : k, (yQuad E x₀).eval y = 0 ↔
          y = -(((E⁄k).a₁ * x₀ + (E⁄k).a₃) / 2) := by
        intro y
        rw [yQuad]
        simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
        constructor
        · intro hy
          have hsq : (y + ((E⁄k).a₁ * x₀ + (E⁄k).a₃) / 2) ^ 2 = 0 := by
            field_simp
            linear_combination (4 : k) * hy + hval
          have := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
          exact eq_neg_of_add_eq_zero_left this
        · rintro rfl
          field_simp
          linear_combination -hval
      rw [show (yQuad E x₀).roots.toFinset =
          {-(((E⁄k).a₁ * x₀ + (E⁄k).a₃) / 2)} from ?_, Finset.card_singleton]
      ext y
      rw [Multiset.mem_toFinset, Finset.mem_singleton,
        Polynomial.mem_roots (yQuad_ne_zero E x₀), Polynomial.IsRoot, hroot]
  · -- odd `p`: two points per root of `preΨ' p`
    have hnoteven : ¬ Even p := Nat.not_even_iff_odd.mpr hodd
    have hdeg : ((E⁄k).preΨ' p).natDegree = (p ^ 2 - 1) / 2 := by
      rw [WeierstrassCurve.natDegree_preΨ' (W := (E⁄k)) hchar, if_neg hnoteven]
    -- `ΨSq p` vanishing is `preΨ' p` vanishing (odd `p`)
    have hΨodd : ∀ x₀ : k, ((E⁄k).ΨSq ((p : ℕ) : ℤ)).eval x₀ = 0 ↔
        ((E⁄k).preΨ' p).eval x₀ = 0 := by
      intro x₀
      rw [WeierstrassCurve.ΨSq_ofNat, if_neg hnoteven, mul_one,
        Polynomial.eval_pow, pow_eq_zero_iff two_ne_zero]
    rw [key ((E⁄k).preΨ' p) 2 (separable_preΨ' E hp hodd hchar) ?_ ?_, hdeg]
    · -- `1 + 2 ⬝ (p² - 1)/2 = p²`
      obtain ⟨t, ht⟩ := hodd.pow (n := 2)
      omega
    · -- the dictionary
      intro x₀ y h
      rw [smul_some_eq_zero_iff E hpZ h, hΨodd]
    · -- two `y`s above each root of `preΨ' p`
      intro x₀ hx₀
      have hΨ₂ : ((E⁄k).Ψ₂Sq).eval x₀ ≠ 0 := by
        intro h0
        obtain ⟨F, G, hFG⟩ := isCoprime_Ψ₂Sq_preΨ' E hp hodd hchar
        have hev := congrArg (Polynomial.eval x₀) hFG
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
          Polynomial.eval_one, h0, hx₀] at hev
        simp at hev
      have hsep := yQuad_separable E hΨ₂
      rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
        ← (IsSepClosed.splits_of_separable _ hsep).natDegree_eq_card_roots,
        yQuad_natDegree]

/-- **The torsion count** (PROVEN from the nodes above):
`#E(k̄)[n] = n²` for `(n : k) ≠ 0`, by strong induction peeling off the
minimal prime factor. -/
theorem card_torsionBy [IsSepClosed k] :
    ∀ n : ℕ, (n : k) ≠ 0 →
      Nat.card (Submodule.torsionBy ℤ (E⁄k).Point n) = n ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    rcases eq_or_ne n 1 with rfl | hn1
    · -- `E[1]` is trivial
      have hbot : Submodule.torsionBy ℤ (E⁄k).Point ((1 : ℕ) : ℤ) = ⊥ := by
        rw [Nat.cast_one]
        exact Submodule.torsionBy_one
      rw [hbot]
      simp
    · -- peel off the minimal prime factor
      have hp : n.minFac.Prime := Nat.minFac_prime hn1
      obtain ⟨m, hm⟩ := n.minFac_dvd
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hm
        exact hn0 hm
      have hmn : m < n := by
        have h2 := hp.two_le
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        rw [hm]
        nlinarith
      have hpk : (n.minFac : k) ≠ 0 := by
        intro h
        apply hn
        rw [hm, Nat.cast_mul, h, zero_mul]
      have hmk : (m : k) ≠ 0 := by
        intro h
        apply hn
        rw [hm, Nat.cast_mul, h, mul_zero]
      have hcast : ((m : ℤ)) * ((n.minFac : ℤ)) = ((n : ℤ)) := by
        exact_mod_cast (by rw [mul_comm]; exact hm.symm : m * n.minFac = n)
      -- multiplication by the prime, restricted to the torsion tower
      have hwd : ∀ P : Submodule.torsionBy ℤ (E⁄k).Point n,
          ((n.minFac : ℤ) • (P : (E⁄k).Point)) ∈
            Submodule.torsionBy ℤ (E⁄k).Point m := by
        intro P
        have hP := (Submodule.mem_torsionBy_iff _ _).mp P.2
        rw [Submodule.mem_torsionBy_iff, smul_smul, hcast]
        exact hP
      set f : Submodule.torsionBy ℤ (E⁄k).Point n →+
          Submodule.torsionBy ℤ (E⁄k).Point m :=
        { toFun := fun P => ⟨(n.minFac : ℤ) • (P : (E⁄k).Point), hwd P⟩
          map_zero' := by
            apply Subtype.ext
            show (n.minFac : ℤ) •
              ((0 : Submodule.torsionBy ℤ (E⁄k).Point n) : (E⁄k).Point) = 0
            rw [ZeroMemClass.coe_zero, smul_zero]
          map_add' := fun P Q => by
            apply Subtype.ext
            show (n.minFac : ℤ) • ((P + Q :
              Submodule.torsionBy ℤ (E⁄k).Point n) : (E⁄k).Point) = _
            rw [Submodule.coe_add, smul_add]
            rfl }
      have hfsurj : Function.Surjective f := by
        rintro ⟨Q, hQ⟩
        obtain ⟨P, hP⟩ := smul_surjective E hpk Q
        have hP' : (n.minFac : ℤ) • P = Q := hP
        have hPn : P ∈ Submodule.torsionBy ℤ (E⁄k).Point n := by
          rw [Submodule.mem_torsionBy_iff, ← hcast, ← smul_smul, hP']
          exact (Submodule.mem_torsionBy_iff _ _).mp hQ
        exact ⟨⟨P, hPn⟩, Subtype.ext hP'⟩
      -- the kernel is the `p`-torsion
      have hple : Submodule.torsionBy ℤ (E⁄k).Point (n.minFac) ≤
          Submodule.torsionBy ℤ (E⁄k).Point n :=
        Submodule.torsionBy_le_torsionBy_of_dvd _ _
          (Int.natCast_dvd_natCast.mpr n.minFac_dvd)
      have hkerEquiv : Submodule.torsionBy ℤ (E⁄k).Point (n.minFac) ≃
          f.ker := by
        refine ⟨fun P => ⟨⟨P.1, hple P.2⟩, ?_⟩, fun x => ⟨x.1.1, ?_⟩,
          fun P => ?_, fun x => ?_⟩
        · rw [AddMonoidHom.mem_ker]
          ext
          exact (Submodule.mem_torsionBy_iff _ _).mp P.2
        · have hx := AddMonoidHom.mem_ker.mp x.2
          rw [Submodule.mem_torsionBy_iff]
          exact congrArg Subtype.val hx
        · rfl
        · rfl
      have hker : Nat.card f.ker = n.minFac ^ 2 := by
        rw [← Nat.card_congr hkerEquiv]
        exact prime_torsion_card E hp hpk
      -- Lagrange plus the first isomorphism theorem
      have hlag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (f.ker)
      have hquot : Nat.card
          ((Submodule.torsionBy ℤ (E⁄k).Point n) ⧸ f.ker) =
          Nat.card (Submodule.torsionBy ℤ (E⁄k).Point m) :=
        Nat.card_congr
          (QuotientAddGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv
      calc Nat.card (Submodule.torsionBy ℤ (E⁄k).Point n)
          = Nat.card ((Submodule.torsionBy ℤ (E⁄k).Point n) ⧸ f.ker) *
            Nat.card f.ker := hlag
      _ = Nat.card (Submodule.torsionBy ℤ (E⁄k).Point m) *
            n.minFac ^ 2 := by rw [hquot, hker]
      _ = m ^ 2 * n.minFac ^ 2 := by rw [ih m hmn hmk]
      _ = (n.minFac * m) ^ 2 := by ring
      _ = n ^ 2 := by rw [← hm]

end TorsionCard
