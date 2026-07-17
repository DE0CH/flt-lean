/-
TorsionCard.lean — own work for the Fermat project (not vendored from the
FLT project).

Decomposition of `WeierstrassCurve.n_torsion_card`
(`#E(k̄)[n] = n²` for `(n : k) ≠ 0`, `Torsion.lean`) into two faithful
arithmetic nodes, plus the PROVEN derivation:

* `TorsionCard.smul_surjective` (sorry node): **divisibility of the
  points group** — over a separably closed field, multiplication by
  `n` with `(n : k) ≠ 0` is surjective on the points of an elliptic
  curve. (The multiplication-by-`n` map is a finite separable isogeny of
  degree `n²`; over a separably closed field a separable isogeny is
  surjective on points.)

* `TorsionCard.prime_torsion_card` (sorry node): **the prime-level
  count** — for a prime `p` with `(p : k) ≠ 0`, the `p`-torsion of an
  elliptic curve over a separably closed field has exactly `p²`
  elements.

* `TorsionCard.card_torsionBy` (PROVEN): the general count by strong
  induction peeling off a minimal prime factor: multiplication by
  `p := n.minFac` restricts to a surjection `E[n] → E[n/p]`
  (divisibility node) whose kernel is `E[p]` (prime-level node), so
  `#E[n] = p² ⬝ (n/p)²` by Lagrange and the first isomorphism theorem.
  No CRT is needed.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.FieldTheory.IsSepClosed
-- the division polynomials `Φ`, `ΨSq`, `preΨ'` appearing in the
-- point-level nodes below
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
-- `WeierstrassCurve.isCoprime_Φ_ΨSq` (Bézout from the resultant node),
-- used to rule out common roots of `Φ n` and `ΨSq n` in the proofs
import Fermat.FLT.KnownIn1980s.EllipticCurves.Flat
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card

@[expose] public section

namespace TorsionCard

open WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic]
  [DecidableEq k]

set_option warn.sorry false in
/-- **The division-polynomial torsion dictionary** (sorry node): an
affine point `P = (x, y)` satisfies `n • P = 0` precisely when its
`x`-coordinate is a root of the division polynomial `ΨSq n`
(classically: the roots of `ψₙ` are exactly the `x`-coordinates of the
nonzero `n`-torsion points; Washington, *Elliptic curves*, Lemma
combined with the recursion of Theorem 3.6). -/
theorem smul_some_eq_zero_iff {n : ℤ} (hn : n ≠ 0) (hnk : (n : k) ≠ 0)
    {x y : k} (h : (E⁄k).toAffine.Nonsingular x y) :
    (n • (Affine.Point.some x y h : (E⁄k).Point) = 0) ↔
      ((E⁄k).ΨSq n).eval x = 0 :=
  sorry

set_option warn.sorry false in
/-- **The multiplication-by-`n` `x`-coordinate formula** (sorry node):
if `P = (x, y)` is an affine point with `ΨSq n` not vanishing at `x`
(so `n • P ≠ 0` by the dictionary above), then `n • P` is an affine
point whose `x`-coordinate `x'` satisfies `x' ⬝ ΨSq n (x) = Φ n (x)` —
the classical `x([n]P) = Φₙ(x)/ψₙ²(x)` (Washington, *Elliptic curves*,
Theorem 3.6), stated in multiplied-out form to avoid division. -/
theorem exists_smul_some_eq {n : ℤ} (hn : n ≠ 0) (hnk : (n : k) ≠ 0)
    {x y : k} (h : (E⁄k).toAffine.Nonsingular x y)
    (hΨ : ((E⁄k).ΨSq n).eval x ≠ 0) :
    ∃ (x' y' : k) (h' : (E⁄k).toAffine.Nonsingular x' y'),
      n • (Affine.Point.some x y h : (E⁄k).Point) =
        Affine.Point.some x' y' h' ∧
      x' * ((E⁄k).ΨSq n).eval x = ((E⁄k).Φ n).eval x :=
  sorry

set_option warn.sorry false in
/-- **Rational points in the multiplication fibres** (sorry node): over
a separably closed field, every fibre of the `x`-coordinate of the
multiplication-by-`n` map contains a rational point — there is a
nonsingular point `(x₀, y₀)` of the curve with `Φ n (x₀) = ξ ⬝ ΨSq n
(x₀)`. This is where separability of the multiplication-by-`n` isogeny
enters (`[n]` is étale for `(n : k) ≠ 0`, so its fibres, cut out by
`Φ n - ξ ⬝ ΨSq n` on the `x`-line, acquire points over a separably
closed field). -/
theorem exists_point_x_smul [IsSepClosed k] {n : ℤ} (hn : n ≠ 0)
    (hnk : (n : k) ≠ 0) (ξ : k) :
    ∃ (x₀ y₀ : k) (h : (E⁄k).toAffine.Nonsingular x₀ y₀),
      ((E⁄k).Φ n).eval x₀ = ξ * ((E⁄k).ΨSq n).eval x₀ :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **Divisibility of the points group** (DERIVED 2026-07-17 from the
three division-polynomial nodes above): over a separably closed field,
multiplication by `n` with `(n : k) ≠ 0` is surjective on the points of
an elliptic curve. Given a target affine point `(ξ, η)`, the fibre node
provides a curve point `(x₀, y₀)` with `Φ n (x₀) = ξ ⬝ ΨSq n (x₀)`;
`ΨSq n (x₀) ≠ 0` by the Bézout identity `isCoprime_Φ_ΨSq` (a common
root would contradict `F ⬝ Φ + G ⬝ ΨSq = 1`), so the formula node
computes `n • (x₀, y₀)` as an affine point with `x`-coordinate `ξ`;
its `y`-coordinate is `η` or `negY ξ η`, and in the latter case
negating the preimage fixes it. -/
theorem smul_surjective [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Function.Surjective (fun P : (E⁄k).Point => (n : ℤ) • P) := by
  classical
  have hn0 : n ≠ 0 := fun h => hn (by simp [h])
  have hnZ : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn0
  have hnk : (((n : ℤ) : ℤ) : k) ≠ 0 := by exact_mod_cast hn
  haveI : (E⁄k).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k k)).IsElliptic)
  -- points with equal coordinates are equal
  have hpoint : ∀ {x₁ y₁ x₂ y₂ : k} (h₁ : (E⁄k).toAffine.Nonsingular x₁ y₁)
      (h₂ : (E⁄k).toAffine.Nonsingular x₂ y₂), x₁ = x₂ → y₁ = y₂ →
      (Affine.Point.some x₁ y₁ h₁ : (E⁄k).Point) = Affine.Point.some x₂ y₂ h₂ := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ hx hy
    subst hx
    subst hy
    rfl
  intro P₀
  cases P₀ with
  | zero => exact ⟨0, smul_zero _⟩
  | some ξ η h₀ =>
    obtain ⟨x₀, y₀, hns, hrel⟩ := exists_point_x_smul E hnZ (by exact_mod_cast hn) ξ
    -- `ΨSq n (x₀) ≠ 0` by coprimality
    have hΨ : ((E⁄k).ΨSq (n : ℤ)).eval x₀ ≠ 0 := by
      intro h0
      obtain ⟨F, G, hFG⟩ := WeierstrassCurve.isCoprime_Φ_ΨSq (E⁄k) hnZ
        (WeierstrassCurve.isUnit_Δ _)
      have hev := congrArg (Polynomial.eval x₀) hFG
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
        Polynomial.eval_one, hrel, h0] at hev
      simp at hev
    obtain ⟨x', y', h', hsmul, hx'⟩ :=
      exists_smul_some_eq E hnZ (by exact_mod_cast hn) hns hΨ
    -- the `x`-coordinate of `n • (x₀, y₀)` is `ξ`
    have hx : x' = ξ := by
      rw [hrel] at hx'
      exact mul_right_cancel₀ hΨ hx'
    -- the `y`-coordinate is `η` or its negation
    rcases Affine.Y_eq_of_X_eq h'.1 h₀.1 hx with hy | hy
    · exact ⟨Affine.Point.some x₀ y₀ hns, hsmul.trans (hpoint h' h₀ hx hy)⟩
    · refine ⟨-(Affine.Point.some x₀ y₀ hns), ?_⟩
      show (n : ℤ) • (-(Affine.Point.some x₀ y₀ hns) : (E⁄k).Point) = _
      rw [smul_neg, hsmul, Affine.Point.neg_some]
      exact hpoint _ h₀ hx (by rw [hy, hx, Affine.negY_negY])

set_option warn.sorry false in
/-- **The prime-level count** (sorry node): for a prime `p` with
`(p : k) ≠ 0`, the `p`-torsion of an elliptic curve over a separably
closed field has exactly `p²` elements — the kernel of the separable
degree-`p²` isogeny `[p]` has as many points as its degree. -/
theorem prime_torsion_card [IsSepClosed k] {p : ℕ} (hp : p.Prime)
    (hchar : (p : k) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (E⁄k).Point p) = p ^ 2 :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- **The torsion count** (PROVEN from the two nodes above):
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
