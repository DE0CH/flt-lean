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
import Fermat.FLT.KnownIn1980s.EllipticCurves.Flat
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Set.Card

@[expose] public section

namespace TorsionCard

open WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]
  [DecidableEq k]

set_option warn.sorry false in
/-- **Separability in characteristic two over an algebraically closed
field** (sorry node): the core case of `separable_preΨ'_char_two`
after the base-change reduction. Over a perfect field the Frobenius
decomposition `f = u² + X ⬝ v²`, `f′ = v²` is available, so a common
factor of `f, f′` is a common factor of `u, v`. Candidate routes: the
Gunji char-2 discriminant formula for `ψₚ`, or the universal
discriminant specialization (the generic-fiber separability over
`ℚ(A₁,…,A₅)` is now a THEOREM — `separable_preΨ'` at the generic
curve — so `disc(preΨ'ₚ) ≠ 0` in `ℤ[A]`; what is missing is the
`±pˢΔᵗ`-structure of the discriminant). -/
theorem separable_preΨ'_char_two_closed {K : Type u} [Field K]
    [IsAlgClosed K] (E' : WeierstrassCurve K) [E'.IsElliptic]
    [DecidableEq K] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpk : (p : K) ≠ 0) (hchar2 : (2 : K) = 0) :
    ((E'⁄K).preΨ' p).Separable :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Separability in characteristic two** (DECOMPOSED 2026-07-17):
reduced to the algebraically closed case by the separability
transfer along the base change to `AlgebraicClosure k`. -/
theorem separable_preΨ'_char_two {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpk : (p : k) ≠ 0) (hchar2 : (2 : k) = 0) :
    ((E⁄k).preΨ' p).Separable := by
  classical
  set K := AlgebraicClosure k
  set φ : k →+* K := algebraMap k K with hφ
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
      intro x₁ hx₁ x₂ hx₂ hne
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
            rfl } with hf
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
