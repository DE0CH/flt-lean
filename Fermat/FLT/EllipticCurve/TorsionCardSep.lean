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
/-- **Separability of the division polynomial** (sorry node): for an
odd prime `p` invertible in `k`, the reduced `p`-division polynomial
`preΨ' p` (whose square is `ΨSq p`) is separable — its roots, the
`x`-coordinates of the nonzero `p`-torsion, are simple. Classically
via the discriminant companion of the resultant identity
(`disc(ψₚ) = ± pᵃ Δᵇ`). -/
theorem separable_preΨ' {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpk : (p : k) ≠ 0) :
    ((E⁄k).preΨ' p).Separable :=
  sorry

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
