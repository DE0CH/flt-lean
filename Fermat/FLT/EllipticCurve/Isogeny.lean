/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Fermat.FLT.EllipticCurve.Velu
-- Only for the `𝔽₅` counterexample in the FALSITY AUDIT of `IsIsogeny.add`.
public import Mathlib.Algebra.Field.ZMod

/-!
# Isogenies of elliptic curves as morphisms

This file supplies the vocabulary that the `X_0(N)` descent leaves in
`Fermat/FLT/FreyCurve/MazurTorsion.lean` need and that neither mathlib (at this
pin) nor `~/cs/FLT` provides in any form: **an isogeny as a morphism**, with a
`degree`, a `dual`, a `comp`osition, and an endomorphism **ring**.

## Why a bare group homomorphism is not enough

Everything the development had until now — `exists_quotient_isogeny`,
`exists_velu_quotient_isogeny` — produces only an *additive, Galois-equivariant
map on `ℚ̄`-points*. That is provably too weak to state the conditions the
descent needs, and the failure is not a matter of difficulty: the statement one
would write is **empty**.

The concrete instance, which is the reason this file exists. The Atkin–Lehner
condition at level `125` is `ψ² = [−125]` with `ker ψ` cyclic of order `125`.
Written for an arbitrary additive endomorphism of the point group it says nothing
whatever: as an abstract group `E(ℚ̄)` has torsion `(ℚ/ℤ)²`, whose endomorphism
ring is `M₂(Ẑ)`, and the matrix

  `[[0, −125], [1, 0]]`

squares to `−125` and has cyclic kernel of order `125` **on every elliptic curve
over every field**. So the "condition" would be satisfied by all curves and would
carry none of the arithmetic it was supposed to.

What defeats that junk witness — and the whole class it belongs to — is
`IsRationalMap` below: the requirement that the map be given by *rational
functions in the coordinates*. An abstract endomorphism of `(ℚ/ℤ)²` admits no
such description, so it is not an element of `endSubring`, and `ψ * ψ = -125` in
`End W` is a genuine assertion of complex multiplication.

## Design, and why it is this one

The base is a field `F` (in the application, `AlgebraicClosure ℚ`). Two choices
are load-bearing:

* **The rational-function certificate is a `Prop`, not data.** `IsIsogeny φ` is a
  predicate on `φ : W.Point →+ W'.Point`, so `Isogeny W W'` is a *subtype* and two
  isogenies are equal exactly when their point maps are. Had the polynomials been
  fields of a structure, one map with two presentations would give two distinct
  terms and the ring axioms on `End` would fail.

* **`degree` is the cardinality of the kernel.** In characteristic zero every
  isogeny is separable, so this agrees with the classical degree, and — unlike a
  degree read off the presenting polynomials — it is manifestly a function of the
  point map alone, so it needs no well-definedness lemma. The pay-off is large:
  multiplicativity of the degree, the construction of the dual and
  `ψ̂ ∘ ψ = [deg ψ]` all become pure group theory over the two geometric inputs
  `nsmul_surjective` and `finite_nsmulKer`. **This file is therefore correct only
  in characteristic zero**, which is where all its consumers live.

## Main definitions

* `WeierstrassCurve.IsRationalMap` — the algebraicity certificate.
* `WeierstrassCurve.IsIsogeny` — rational, plus surjective with finite kernel
  away from the zero map.
* `WeierstrassCurve.Isogeny` — the subtype; `WeierstrassCurve.Isogeny.degree`.
* `WeierstrassCurve.endSubring` — `End W` as a `Subring (AddMonoid.End W.Point)`,
  hence a `Ring`, in which `(n : End W)` **is** multiplication by `n` (`rfl`, see
  `End.intCast_apply`).
* `WeierstrassCurve.Isogeny.dualHom` / `dual` — the dual isogeny, with
  `Isogeny.dualHom_comp` giving `ψ̂ ∘ ψ = [deg ψ]`.

## `IsIsogeny` is only usable over an algebraically closed base

`IsIsogeny.add` was FALSE as originally cut, and `endSubring` therefore did not
define a subring. The refutation is machine-checked in
`WeierstrassCurve.NotIsIsogenyAdd` and written out in the FALSITY AUDIT next to
`IsIsogeny.add`; in one line, `IsIsogeny.id` holds over every field, so the
unconditional `IsIsogeny.add` asserts that `[2] = id + id` is surjective on
`W(F)`, which fails already for `y² = x³ - x` over `𝔽₅`.

`IsIsogeny.add`, `endSubring`, `End` and the `End.*` API therefore carry
`[IsAlgClosed F]`, matching `nsmul_surjective`, `finite_nsmulKer` and
`Isogeny.dual`, which always did. All consumers work over `AlgebraicClosure ℚ`,
so nothing downstream changes. `IsIsogeny.zero`, `.id`, `.neg` and `.comp` remain
unconditional and remain proven.

## Open leaves left by this file

`IsRationalMap.add`, `IsRationalMap.isIsogeny`, `nsmul_surjective`,
`finite_nsmulKer`, `Isogeny.isRationalMap_dualHom`, `Isogeny.degree_comp`.

`IsRationalMap.neg` was on this list and is now PROVEN.

`IsRationalMap.comp` was on this list and is now **PROVEN and axiom-clean**, hence
so is `IsIsogeny.comp`. It rests on `homogSubst` (substitute `A/B`, clear
denominators), `eval_homogSubst`, `exists_const_of_homogSubst_eq_zero` (the
degeneracy criterion) and `IsRationalMap.comp_of_constX` (the constant-`x` case) —
all proven here.

`IsIsogeny.add` was on this list; it is now PROVEN from `IsRationalMap.add` and
`IsRationalMap.isIsogeny`, after being refuted and restated (above).

## Two techniques from `IsRationalMap.comp` that the remaining leaves will want

1. **Kill a bad locus by multiplying the witness through by its defining
   polynomial.** `IsRationalMap`'s certificate must hold at *every* point, but a
   derivation typically only works where some denominator `B` is nonzero. Taking
   the witness pair to be `(A'' * B, B'' * B)` instead of `(A'', B'')` repairs this
   for free: where `B` vanishes both sides of the certificate become `0`. This is
   used in `comp_of_constX` and is why `eval_homogSubst` deliberately carries no
   nonvanishing hypothesis.

2. **The only obstruction to a substituted witness is a constant `x`-coordinate.**
   The `B ≠ 0` side condition of `IsRationalMap` is the whole difficulty in
   `comp`, and `exists_const_of_homogSubst_eq_zero` reduces it to a single
   degenerate case. Expect the same shape elsewhere.
-/


@[expose] public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] {W W' W'' : Affine F}

/-! ### The algebraicity certificate -/

/-- `IsRationalMap φ` says that the map `φ` on points is computed, away from its
kernel, by **rational functions in the coordinates**: there are polynomials
`A, B, C, D, E` over the base field with

  `x(φ P) = A(x P) / B(x P)`,  `y(φ P) = (C(x P) · y P + D(x P)) / E(x P)`,

written multiplicatively so that no division is needed. This is the normal form
of a morphism of Weierstrass curves in characteristic zero.

This predicate is the entire faithfulness content of `IsIsogeny`. Without it,
`End W` would be the endomorphism ring of an abstract abelian group — see the
`M₂(Ẑ)` discussion in the module docstring — and every condition stated in it
would be vacuous. -/
def IsRationalMap (φ : W.Point →+ W'.Point) : Prop :=
  ∃ A B C D E : F[X], B ≠ 0 ∧ E ≠ 0 ∧
    ∀ P : W.Point, φ P ≠ 0 →
      veluPointX (φ P) * B.eval (veluPointX P) = A.eval (veluPointX P) ∧
      veluPointY (φ P) * E.eval (veluPointX P)
        = C.eval (veluPointX P) * veluPointY P + D.eval (veluPointX P)

/-- The zero map is rational: its defining condition is vacuous. -/
theorem IsRationalMap.zero : IsRationalMap (0 : W.Point →+ W'.Point) :=
  ⟨0, 1, 0, 0, 1, one_ne_zero, one_ne_zero, fun P hP =>
    absurd (AddMonoidHom.zero_apply P) hP⟩

/-- The identity is rational, with `A = X`, `B = C = E = 1`, `D = 0`. -/
theorem IsRationalMap.id : IsRationalMap (AddMonoidHom.id W.Point) := by
  refine ⟨X, 1, 1, 0, 1, one_ne_zero, one_ne_zero, fun P _ => ?_⟩
  simp

/-- A negated rational map is rational.

`x(-Q) = x(Q)`, so `A, B` are unchanged; `y(-Q) = negY (x Q) (y Q)
= -y(Q) - a₁ x(Q) - a₃`, so substituting `x(φ P) = A/B` and clearing the extra
denominator gives the `y`-witness
`(C', D', E') = (-C·B, -D·B - a₁·A·E - a₃·B·E, E·B)`. -/
theorem IsRationalMap.neg {φ : W.Point →+ W'.Point} (h : IsRationalMap φ) :
    IsRationalMap (-φ) := by
  obtain ⟨A, B, C, D, E, hB, hE, hcert⟩ := h
  refine ⟨A, B, -(C * B),
    -(D * B) - Polynomial.C W'.a₁ * A * E - Polynomial.C W'.a₃ * B * E, E * B,
    hB, mul_ne_zero hE hB, fun P hP => ?_⟩
  have hφP : φ P ≠ 0 := fun hc => hP (by show -(φ P) = 0; rw [hc, neg_zero])
  obtain ⟨hx, hy⟩ := hcert P hφP
  have hnegapp : (-φ) P = -(φ P) := rfl
  refine ⟨?_, ?_⟩
  · rw [hnegapp, velu_pointX_neg]
    exact hx
  · rw [hnegapp, velu_pointY_neg _ hφP]
    simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sub,
      Polynomial.eval_C]
    linear_combination (-(B.eval (veluPointX P))) * hy
      - (W'.a₁ * E.eval (veluPointX P)) * hx

/-! #### Clearing denominators after substitution

`IsRationalMap.comp` needs to substitute `A/B` into the certificate of the second
map and clear denominators. `homogSubst A B d Q` is exactly that: `Q(A/B)`
multiplied through by `B ^ d`. The two facts about it that matter are
`eval_homogSubst` (what it computes) and `exists_const_of_homogSubst_eq_zero` (when
it degenerates to the zero polynomial, which is the only thing that can obstruct
the `B ≠ 0` side condition of `IsRationalMap`). -/

/-- `homogSubst A B d Q` is `Q(A/B)` with denominators cleared to degree `d`, i.e.
`B ^ d * Q (A / B)` written without division. -/
noncomputable def homogSubst (A B : F[X]) (d : ℕ) (Q : F[X]) : F[X] :=
  ∑ i ∈ Finset.range (d + 1), Polynomial.C (Q.coeff i) * A ^ i * B ^ (d - i)

omit [DecidableEq F] in
/-- What `homogSubst` computes. Note there is **no** nonvanishing hypothesis on
`B.eval t`: the identity `u * B.eval t = A.eval t` is enough, and both sides
degenerate to `0` together when `B.eval t = 0`. That is what lets the composite
certificate hold at *every* point rather than away from a bad set. -/
theorem eval_homogSubst {A B Q : F[X]} {d : ℕ} (hd : Q.natDegree ≤ d) {t u : F}
    (hu : u * B.eval t = A.eval t) :
    (homogSubst A B d Q).eval t = (B.eval t) ^ d * Q.eval u := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd) (x := u), Finset.mul_sum]
  simp only [homogSubst, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hsplit : (B.eval t) ^ d = (B.eval t) ^ i * (B.eval t) ^ (d - i) := by
    rw [← pow_add]; congr 1; omega
  rw [← hu, mul_pow, hsplit]
  ring

omit [DecidableEq F] in
theorem homogSubst_eq_pow_mul {A B Q : F[X]} {d : ℕ} (hd : Q.natDegree ≤ d) :
    homogSubst A B d Q = B ^ (d - Q.natDegree) * homogSubst A B Q.natDegree Q := by
  have hsub : Finset.range (Q.natDegree + 1) ⊆ Finset.range (d + 1) := fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) (Nat.succ_le_succ hd))
  have hzero : ∀ i ∈ Finset.range (d + 1), i ∉ Finset.range (Q.natDegree + 1) →
      Polynomial.C (Q.coeff i) * A ^ i * B ^ (d - i) = 0 := by
    intro i _ hi
    have hlt : Q.natDegree < i := by
      simp only [Finset.mem_range, not_lt] at hi; omega
    rw [Q.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul, zero_mul]
  unfold homogSubst
  rw [Finset.mul_sum, ← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ Q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hb : B ^ (d - i) = B ^ (d - Q.natDegree) * B ^ (Q.natDegree - i) := by
    rw [← pow_add]; congr 1; omega
  rw [hb]; ring

omit [DecidableEq F] in
theorem homogSubst_mul_left (g A B Q : F[X]) (m : ℕ) :
    homogSubst (g * A) (g * B) m Q = g ^ m * homogSubst A B m Q := by
  unfold homogSubst
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hg : g ^ m = g ^ i * g ^ (m - i) := by rw [← pow_add]; congr 1; omega
  rw [mul_pow, mul_pow, hg]; ring

omit [DecidableEq F] in
/-- The coprime core of the degeneracy criterion: substituting a **coprime** pair
into a nonzero `Q` can only give `0` when both members of the pair are constants.

`B` divides the top term `C (Q.coeff m) * A ^ m` of the sum, so by coprimality it
divides the nonzero constant `Q.coeff m` and is a unit; the remaining identity is
then `Q.comp (C b⁻¹ * A) = 0`, which forces `A` constant by
`Polynomial.comp_eq_zero_iff`. -/
theorem natDegree_eq_zero_of_coprime_homogSubst {A B Q : F[X]} (hcop : IsCoprime A B)
    (hQ : Q ≠ 0) (h : homogSubst A B Q.natDegree Q = 0) :
    A.natDegree = 0 ∧ B.natDegree = 0 := by
  set m := Q.natDegree with hm
  have hqm : Q.coeff m ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hQ
  have hsplit : homogSubst A B m Q
      = (∑ i ∈ Finset.range m, Polynomial.C (Q.coeff i) * A ^ i * B ^ (m - i))
        + Polynomial.C (Q.coeff m) * A ^ m := by
    unfold homogSubst
    rw [Finset.sum_range_succ]
    simp
  have hdvdsum : B ∣ ∑ i ∈ Finset.range m, Polynomial.C (Q.coeff i) * A ^ i * B ^ (m - i) := by
    refine Finset.dvd_sum fun i hi => ?_
    have : 1 ≤ m - i := by have := Finset.mem_range.1 hi; omega
    exact Dvd.dvd.mul_left (dvd_pow_self B (by omega)) _
  have hdvd : B ∣ Polynomial.C (Q.coeff m) * A ^ m := by
    have hrw : Polynomial.C (Q.coeff m) * A ^ m
        = homogSubst A B m Q
          - ∑ i ∈ Finset.range m, Polynomial.C (Q.coeff i) * A ^ i * B ^ (m - i) := by
      rw [hsplit]; ring
    rw [hrw, h, zero_sub]
    exact dvd_neg.2 hdvdsum
  have hBdvd : B ∣ Polynomial.C (Q.coeff m) :=
    (hcop.symm.pow_right (n := m)).dvd_of_dvd_mul_right hdvd
  have hBunit : IsUnit B :=
    isUnit_of_dvd_unit hBdvd (Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 hqm))
  have hBdeg : B.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hBunit
  refine ⟨?_, hBdeg⟩
  obtain ⟨b, hb⟩ := Polynomial.natDegree_eq_zero.1 hBdeg
  have hbne : b ≠ 0 := by
    rintro rfl
    exact hBunit.ne_zero (by rw [← hb, map_zero])
  have hscalar : ∀ i ≤ m, b ^ m * Q.coeff i * b⁻¹ ^ i = Q.coeff i * b ^ (m - i) := by
    intro i hi
    have hsplitb : b ^ m = b ^ (m - i) * b ^ i := by rw [← pow_add]; congr 1; omega
    have hinv : b ^ i * b⁻¹ ^ i = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hbne, one_pow]
    calc b ^ m * Q.coeff i * b⁻¹ ^ i
        = Q.coeff i * b ^ (m - i) * (b ^ i * b⁻¹ ^ i) := by rw [hsplitb]; ring
      _ = Q.coeff i * b ^ (m - i) := by rw [hinv, mul_one]
  have hce : Q.comp (Polynomial.C b⁻¹ * A)
      = ∑ i ∈ Finset.range (m + 1), Polynomial.C (Q.coeff i) * (Polynomial.C b⁻¹ * A) ^ i :=
    Polynomial.eval₂_eq_sum_range' Polynomial.C (Nat.lt_succ_self m) (Polynomial.C b⁻¹ * A)
  have hcomp : Polynomial.C (b ^ m) * Q.comp (Polynomial.C b⁻¹ * A) = 0 := by
    rw [hce, Finset.mul_sum, ← h]
    unfold homogSubst
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [← hb, mul_pow, ← Polynomial.C_pow]
    calc Polynomial.C (b ^ m)
          * (Polynomial.C (Q.coeff i) * (Polynomial.C (b⁻¹ ^ i) * A ^ i))
        = Polynomial.C (b ^ m * Q.coeff i * b⁻¹ ^ i) * A ^ i := by
          simp only [Polynomial.C_mul]; ring
      _ = Polynomial.C (Q.coeff i * b ^ (m - i)) * A ^ i := by rw [hscalar i hi']
      _ = Polynomial.C (Q.coeff i) * A ^ i * Polynomial.C b ^ (m - i) := by
          simp only [Polynomial.C_mul, Polynomial.C_pow]; ring
  have hQcomp : Q.comp (Polynomial.C b⁻¹ * A) = 0 := by
    have hCb : (Polynomial.C (b ^ m) : F[X]) ≠ 0 := by simpa using pow_ne_zero m hbne
    exact (mul_eq_zero.1 hcomp).resolve_left hCb
  rcases Polynomial.comp_eq_zero_iff.1 hQcomp with h0 | ⟨_, hconst⟩
  · exact absurd h0 hQ
  · have hdeg : (Polynomial.C b⁻¹ * A).natDegree = 0 := by
      rw [hconst]; exact Polynomial.natDegree_C _
    rwa [Polynomial.natDegree_C_mul (inv_ne_zero hbne)] at hdeg

/-- **The degeneracy criterion.** `homogSubst A B d Q` can vanish for a nonzero `Q`
only when `A / B` is a *constant* rational function.

This is the whole reason `IsRationalMap.comp` needs a case split: the composite
witness is `homogSubst A B d B'`, and its `≠ 0` side condition can fail exactly when
the first map has a constant `x`-coordinate. -/
theorem exists_const_of_homogSubst_eq_zero {A B Q : F[X]} (hB : B ≠ 0) (hQ : Q ≠ 0)
    {d : ℕ} (hd : Q.natDegree ≤ d) (h : homogSubst A B d Q = 0) :
    ∃ c : F, A = Polynomial.C c * B := by
  classical
  have hm : homogSubst A B Q.natDegree Q = 0 := by
    rw [homogSubst_eq_pow_mul hd] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hB)
  letI : GCDMonoid F[X] := EuclideanDomain.gcdMonoid F[X]
  set g := GCDMonoid.gcd A B with hg
  have hgne : g ≠ 0 := gcd_ne_zero_of_right hB
  have hA : A = g * (A / g) :=
    (EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left A B)).symm
  have hBeq : B = g * (B / g) :=
    (EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_right A B)).symm
  have hcop : IsCoprime (A / g) (B / g) := isCoprime_div_gcd_div_gcd hB
  have hsub : homogSubst (A / g) (B / g) Q.natDegree Q = 0 := by
    have hml := homogSubst_mul_left g (A / g) (B / g) Q Q.natDegree
    rw [← hA, ← hBeq, hm] at hml
    exact (mul_eq_zero.1 hml.symm).resolve_left (pow_ne_zero _ hgne)
  obtain ⟨hAd, hBd⟩ := natDegree_eq_zero_of_coprime_homogSubst hcop hQ hsub
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.1 hAd
  obtain ⟨b, hbb⟩ := Polynomial.natDegree_eq_zero.1 hBd
  have hbne : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hbb
    exact hB (by rw [hBeq, ← hbb, mul_zero])
  refine ⟨a / b, ?_⟩
  rw [hA, hBeq, ← ha, ← hbb, ← mul_assoc, mul_comm (Polynomial.C (a / b)) g, mul_assoc,
    ← Polynomial.C_mul, div_mul_cancel₀ a hbne]

omit [DecidableEq F] in
/-- A nonzero point is determined by its two coordinates. -/
theorem eq_of_veluPoint_eq {Q₁ Q₂ : W.Point} (h1 : Q₁ ≠ 0) (h2 : Q₂ ≠ 0)
    (hx : veluPointX Q₁ = veluPointX Q₂) (hy : veluPointY Q₁ = veluPointY Q₂) : Q₁ = Q₂ := by
  rcases Q₁ with _ | ⟨x₁, y₁, hh₁⟩
  · exact absurd rfl h1
  rcases Q₂ with _ | ⟨x₂, y₂, hh₂⟩
  · exact absurd rfl h2
  exact velu_point_some_eq hx hy

omit [DecidableEq F] in
/-- Two nonzero points with the same `x`-coordinate are equal or negatives — the
fibres of `x` have at most two elements. This is `Affine.Point.X_eq_iff` phrased
through `veluPointX`. -/
theorem eq_or_eq_neg_of_veluPointX_eq {Q₁ Q₂ : W.Point} (h1 : Q₁ ≠ 0) (h2 : Q₂ ≠ 0)
    (hx : veluPointX Q₁ = veluPointX Q₂) : Q₁ = Q₂ ∨ Q₁ = -Q₂ := by
  rcases Q₁ with _ | ⟨x₁, y₁, hh₁⟩
  · exact absurd rfl h1
  rcases Q₂ with _ | ⟨x₂, y₂, hh₂⟩
  · exact absurd rfl h2
  exact Affine.Point.X_eq_iff.1 hx

/-- The composite is rational in the degenerate case, where the first map has a
*constant* `x`-coordinate away from the zeros of `B`.

This is the residue of `IsRationalMap.comp` that the substitution argument cannot
reach, and it is genuinely different in kind: there is no denominator to clear,
because `x(φ P) = c` is already constant, and the content is instead the geometry of
the (at most two-point) fibre of `x` over `c`.

Note `ψ` needs **no** rationality hypothesis here: only two points of `W'` have
`x`-coordinate `c`, namely some `R` and `-R`, so `φ` maps `{P : B(x P) ≠ 0}` into
`{R, -R}` and `ψ ∘ φ` maps it into `{ψ R, -ψ R}` for a completely arbitrary
homomorphism `ψ`. Hence:

* `x (ψ (φ P))` is the single constant `e := x (ψ R)`, and `(C e * B, B)` is an
  `x`-witness — at the zeros of `B` both sides are `0`, which is why the factor `B`
  must be kept;
* `y (ψ (φ P))` takes the two values `y(ψ R)` and `y(-ψ R)`, and which one occurs is
  determined by `y(φ P)`, which is rational in `(x P, y P)` through `φ`'s own
  `y`-certificate. The affine interpolation `α · y(R) + β = y(ψ R)`,
  `α · y(-R) + β = y(-ψ R)` gives the `y`-witness `(α Cx B, (α D + β E) B, E B)`.

The interpolation needs no case split on `R = -R`: when `y(R) = y(-R)` the slope
`α` is `0/0 = 0` in Lean, and that is the correct answer, because `y(R) = y(-R)`
forces `R = -R`, hence `ψ R = ψ (-R) = -ψ R` and the two interpolation conditions
coincide. -/
theorem IsRationalMap.comp_of_constX {φ : W.Point →+ W'.Point} {ψ : W'.Point →+ W''.Point}
    {B Cx D E : F[X]} (hB : B ≠ 0) (hE : E ≠ 0) (c : F)
    (hxc : ∀ P : W.Point, φ P ≠ 0 → B.eval (veluPointX P) ≠ 0 → veluPointX (φ P) = c)
    (hyc : ∀ P : W.Point, φ P ≠ 0 →
      veluPointY (φ P) * E.eval (veluPointX P)
        = Cx.eval (veluPointX P) * veluPointY P + D.eval (veluPointX P)) :
    IsRationalMap (ψ.comp φ) := by
  classical
  by_cases hex : ∃ P₀ : W.Point, ψ (φ P₀) ≠ 0 ∧ B.eval (veluPointX P₀) ≠ 0
  swap
  · -- No point contributes: `B` vanishes wherever the composite is nonzero.
    refine ⟨0, B, 0, 0, B, hB, hB, fun P hP => ?_⟩
    have hb : B.eval (veluPointX P) = 0 := by
      by_contra hb
      exact hex ⟨P, hP, hb⟩
    simp [hb]
  obtain ⟨P₀, hS₀, hB₀⟩ := hex
  have hR₀ : φ P₀ ≠ 0 := fun h => hS₀ (by rw [h, map_zero])
  -- Affine interpolation of `y ∘ ψ` across the two-element fibre `{φ P₀, -(φ P₀)}`.
  obtain ⟨α, β, hlin, hlin'⟩ : ∃ α β : F,
      α * veluPointY (φ P₀) + β = veluPointY (ψ (φ P₀)) ∧
        α * veluPointY (-(φ P₀)) + β = veluPointY (-(ψ (φ P₀))) := by
    set yR := veluPointY (φ P₀) with hyRdef
    set yR' := veluPointY (-(φ P₀)) with hyRdef'
    set yS := veluPointY (ψ (φ P₀)) with hySdef
    set yS' := veluPointY (-(ψ (φ P₀))) with hySdef'
    refine ⟨(yS - yS') / (yR - yR'), yS - (yS - yS') / (yR - yR') * yR, by ring, ?_⟩
    by_cases hyy : yR - yR' = 0
    · -- `y(R) = y(-R)` forces `R = -R`, hence `ψ R = -ψ R` and the two conditions agree.
      have hRR : φ P₀ = -(φ P₀) :=
        eq_of_veluPoint_eq hR₀ (neg_ne_zero.2 hR₀) (velu_pointX_neg _).symm (sub_eq_zero.1 hyy)
      have hSS : ψ (φ P₀) = -(ψ (φ P₀)) := by
        conv_lhs => rw [hRR]
        rw [map_neg]
      have hy : yS = yS' := congrArg veluPointY hSS
      rw [hyy, div_zero, hy]
      ring
    · have hmul : (yS - yS') / (yR - yR') * (yR - yR') = yS - yS' := div_mul_cancel₀ _ hyy
      linear_combination -hmul
  -- The pointwise description of the composite on the good locus.
  have key : ∀ P : W.Point, ψ (φ P) ≠ 0 → B.eval (veluPointX P) ≠ 0 →
      veluPointX (ψ (φ P)) = veluPointX (ψ (φ P₀)) ∧
        veluPointY (ψ (φ P)) = α * veluPointY (φ P) + β := by
    intro P hP hBP
    have hφP : φ P ≠ 0 := fun h => hP (by rw [h, map_zero])
    have hxeq : veluPointX (φ P) = veluPointX (φ P₀) := by
      rw [hxc P hφP hBP, hxc P₀ hR₀ hB₀]
    rcases eq_or_eq_neg_of_veluPointX_eq hφP hR₀ hxeq with h | h
    · rw [h]
      exact ⟨rfl, hlin.symm⟩
    · have hψeq : ψ (φ P) = -(ψ (φ P₀)) := by rw [h, map_neg]
      rw [hψeq, h]
      exact ⟨velu_pointX_neg _, hlin'.symm⟩
  refine ⟨Polynomial.C (veluPointX (ψ (φ P₀))) * B, B,
    Polynomial.C α * Cx * B, (Polynomial.C α * D + Polynomial.C β * E) * B, E * B,
    hB, mul_ne_zero hE hB, fun P hP => ?_⟩
  by_cases hBP : B.eval (veluPointX P) = 0
  · simp [hBP]
  have hPc : ψ (φ P) ≠ 0 := hP
  have hφP : φ P ≠ 0 := fun h => hPc (by rw [h, map_zero])
  obtain ⟨hkx, hky⟩ := key P hPc hBP
  refine ⟨?_, ?_⟩
  · simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [show veluPointX ((ψ.comp φ) P) = veluPointX (ψ (φ P)) from rfl, hkx]
  · simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C]
    rw [show veluPointY ((ψ.comp φ) P) = veluPointY (ψ (φ P)) from rfl, hky]
    linear_combination (α * B.eval (veluPointX P)) * (hyc P hφP)

/-- The composite of two rational maps is rational.

Away from the degenerate case this is exactly substitution: `x (ψ (φ P))` satisfies
`ψ`'s certificate at `u = x (φ P)`, and `u` satisfies `φ`'s certificate at
`t = x P`, so multiplying `ψ`'s certificate through by `B(t) ^ d` replaces every
`A'(u)`, `B'(u)` by `homogSubst A B d A'`, `homogSubst A B d B'` evaluated at `t`.
The same computation on the `y`-side uses `φ`'s `y`-certificate to rewrite
`y(φ P) · E(t)` as `C(t) y(P) + D(t)`.

The side conditions `B'' ≠ 0`, `E'' ≠ 0` are where the work is, and
`exists_const_of_homogSubst_eq_zero` shows they can only fail when `x ∘ φ` is
constant — which is `IsRationalMap.comp_of_constX`. -/
theorem IsRationalMap.comp {φ : W.Point →+ W'.Point} {ψ : W'.Point →+ W''.Point}
    (hφ : IsRationalMap φ) (hψ : IsRationalMap ψ) : IsRationalMap (ψ.comp φ) := by
  obtain ⟨A, B, Cx, D, E, hB, hE, hcert⟩ := hφ
  by_cases hconst : ∃ c : F, A = Polynomial.C c * B
  · obtain ⟨c, hcc⟩ := hconst
    refine IsRationalMap.comp_of_constX (Cx := Cx) (D := D) hB hE c
      (fun P hP hBP => ?_) (fun P hP => (hcert P hP).2)
    have hx := (hcert P hP).1
    rw [hcc] at hx
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at hx
    exact mul_right_cancel₀ hBP hx
  obtain ⟨A', B', C', D', E', hB', hE', hcert'⟩ := hψ
  set d := max A'.natDegree B'.natDegree with hd
  set d' := max (max C'.natDegree D'.natDegree) E'.natDegree with hd'
  have hne : ∀ Q : F[X], Q ≠ 0 → ∀ n : ℕ, Q.natDegree ≤ n → homogSubst A B n Q ≠ 0 :=
    fun Q hQ n hn hz => hconst (exists_const_of_homogSubst_eq_zero hB hQ hn hz)
  refine ⟨homogSubst A B d A', homogSubst A B d B',
    homogSubst A B d' C' * Cx,
    homogSubst A B d' C' * D + homogSubst A B d' D' * E,
    homogSubst A B d' E' * E,
    hne B' hB' d (le_max_right _ _),
    mul_ne_zero (hne E' hE' d' (le_max_right _ _)) hE, fun P hP => ?_⟩
  have hφP : φ P ≠ 0 := fun hcz => hP (by show ψ (φ P) = 0; rw [hcz, map_zero])
  obtain ⟨hx, hy⟩ := hcert P hφP
  obtain ⟨hx', hy'⟩ := hcert' (φ P) hP
  have hxA : (homogSubst A B d A').eval (veluPointX P)
      = (B.eval (veluPointX P)) ^ d * A'.eval (veluPointX (φ P)) :=
    eval_homogSubst (le_max_left _ _) hx
  have hxB : (homogSubst A B d B').eval (veluPointX P)
      = (B.eval (veluPointX P)) ^ d * B'.eval (veluPointX (φ P)) :=
    eval_homogSubst (le_max_right _ _) hx
  have hyC : (homogSubst A B d' C').eval (veluPointX P)
      = (B.eval (veluPointX P)) ^ d' * C'.eval (veluPointX (φ P)) :=
    eval_homogSubst (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hyD : (homogSubst A B d' D').eval (veluPointX P)
      = (B.eval (veluPointX P)) ^ d' * D'.eval (veluPointX (φ P)) :=
    eval_homogSubst (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hyE : (homogSubst A B d' E').eval (veluPointX P)
      = (B.eval (veluPointX P)) ^ d' * E'.eval (veluPointX (φ P)) :=
    eval_homogSubst (le_max_right _ _) hx
  refine ⟨?_, ?_⟩
  · rw [hxA, hxB]
    linear_combination (B.eval (veluPointX P)) ^ d * hx'
  · simp only [Polynomial.eval_mul, Polynomial.eval_add, hyC, hyD, hyE]
    linear_combination
      ((B.eval (veluPointX P)) ^ d' * E.eval (veluPointX P)) * hy'
        + ((B.eval (veluPointX P)) ^ d' * C'.eval (veluPointX (φ P))) * hy

/-- **LEAF.** The pointwise sum of two rational maps is rational.

This is the affine addition formula on `W'` applied to the two images: `x` and
`y` of `φ P + ψ P` are rational in `x(φ P), y(φ P), x(ψ P), y(ψ P)`, each of
which is rational in `x P, y P`, and `y P` occurs to degree at most one after
reduction by the Weierstrass equation. The case analysis is over the three
branches of the group law.

Notes for whoever closes it, from having closed `IsRationalMap.comp`.

*The real obstruction is not the algebra, it is that `x` must come out a function
of `x P` alone.* The certificate demands `x((φ+ψ)P) = A(x P) / B(x P)` with no
`y P` in sight. That is true — `(φ+ψ)(-P) = -((φ+ψ)P)` and `x` is `±`-invariant, so
`x ∘ (φ+ψ)` really does factor through `x` — but it is not visible in the chord
formula: the slope `λ = (y₂-y₁)/(x₂-x₁)` is affine in `y P`, and `λ²` produces a
`(y P)²` that must be reduced by the Weierstrass equation before the residual
`y P`-dependence cancels. Budget for that cancellation; it is the step that makes
this leaf harder than `comp`, not the branch analysis.

*The branch analysis is cheaper than it looks*, because of technique 1 in the module
docstring. The branches are cut out by polynomial conditions in `x P`:
`x(φ P) = x(ψ P)` is `A₁ B₂ - A₂ B₁ = 0` at `x P`. So a witness valid only on
`{A₁B₂ - A₂B₁ ≠ 0}` becomes valid everywhere after multiplying through by
`A₁B₂ - A₂B₁`; there is no need to make one formula cover the doubling branch.

*Reductions that are free*: `φ = 0` gives `φ + ψ = ψ`, `ψ = 0` gives `φ`, and
`ψ = -φ` gives `0` — all three already rational (`IsRationalMap.zero`).

*The `≠ 0` side conditions* will degenerate in exactly the same way as in `comp`;
`exists_const_of_homogSubst_eq_zero` above is available and is the tool for them. -/
theorem IsRationalMap.add {φ ψ : W.Point →+ W'.Point}
    (hφ : IsRationalMap φ) (hψ : IsRationalMap ψ) : IsRationalMap (φ + ψ) :=
  sorry

/-! ### Isogenies -/

/-- An **isogeny** `W → W'`: a homomorphism of point groups given by rational
functions in the coordinates which, unless it is the zero map, is surjective with
finite kernel.

The zero map is admitted, with degree `0`, so that `End W` is a ring.

`surjective` and `finite_ker` are *fields* rather than consequences on purpose.
Both are genuinely geometric — surjectivity of a non-constant morphism of curves
is properness, and it is false for a general group homomorphism with divisible
image — so a construction that produces an isogeny must discharge them, and the
cost is paid where the geometry is rather than silently. -/
structure IsIsogeny (φ : W.Point →+ W'.Point) : Prop where
  /-- The map is given by rational functions in the coordinates. -/
  isRationalMap : IsRationalMap φ
  /-- A nonzero isogeny is surjective on points. -/
  surjective : φ ≠ 0 → Function.Surjective φ
  /-- A nonzero isogeny has finite kernel. -/
  finite_ker : φ ≠ 0 → (AddMonoidHom.ker φ : Set W.Point).Finite

theorem IsIsogeny.zero : IsIsogeny (0 : W.Point →+ W'.Point) where
  isRationalMap := IsRationalMap.zero
  surjective h := absurd rfl h
  finite_ker h := absurd rfl h

theorem IsIsogeny.id : IsIsogeny (AddMonoidHom.id W.Point) where
  isRationalMap := IsRationalMap.id
  surjective _ := Function.surjective_id
  finite_ker _ := by
    have h : (AddMonoidHom.ker (AddMonoidHom.id W.Point) : Set W.Point) = {0} := by
      ext P; simp
    rw [h]; exact Set.finite_singleton _

theorem IsIsogeny.neg {φ : W.Point →+ W'.Point} (h : IsIsogeny φ) : IsIsogeny (-φ) where
  isRationalMap := h.isRationalMap.neg
  surjective hne := by
    have hφ : φ ≠ 0 := fun hc => hne (by rw [hc, neg_zero])
    intro Q
    obtain ⟨P, hP⟩ := h.surjective hφ (-Q)
    exact ⟨P, by simp [hP]⟩
  finite_ker hne := by
    have hφ : φ ≠ 0 := fun hc => hne (by rw [hc, neg_zero])
    have hker : (AddMonoidHom.ker (-φ) : Set W.Point) = (AddMonoidHom.ker φ : Set W.Point) := by
      ext P; simp [AddMonoidHom.mem_ker]
    rw [hker]; exact h.finite_ker hφ

/-! ### FALSITY AUDIT: `IsIsogeny.add` was FALSE, and is repaired here

**Refuted 2026-07-26 by the machine-checked counterexample below; the axiom audit
of `NotIsIsogenyAdd.isIsogeny_add_is_false` is `[propext, Classical.choice,
Quot.sound]`, so this is a genuine refutation and not a vacuous one.**

The statement as originally cut carried no hypothesis on `F`:

  `theorem IsIsogeny.add {φ ψ : W.Point →+ W'.Point}`
  `    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ) : IsIsogeny (φ + ψ)`

Instantiate it at `φ = ψ = AddMonoidHom.id`. That *is* an isogeny over **every**
field — `IsIsogeny.id` is proven unconditionally, because the identity is rational,
surjective, and has kernel `{0}` — so the conclusion asserts that
`[2] : W(F) → W(F)` is surjective whenever it is nonzero, i.e. that `W(F)` is
2-divisible. That is false for most curves over most fields: `E(ℚ)` of positive
rank is the familiar instance, and a finite field gives the cheapest formalisable
one.

Take `W₅ : y² = x³ - x` over `𝔽₅`, whose group of points is `ℤ/2 × ℤ/4`:

* `T = (0,0)` has `y = W₅.negY x y`, so `T + T = 0` while `T ≠ 0`;
* `P = (2,1)` has `y ≠ W₅.negY x y`, so `P + P ≠ 0`, hence `[2] ≠ 0`.

`W₅(𝔽₅)` is finite (via `Affine.nonsingularPointEquiv`), so `[2]` — not injective,
because it kills both `0` and `T` — cannot be surjective either.

**Why it is false, in one line.** Surjectivity *on `F`-points* is not a property of
a morphism of curves at all; it is a property of the base field. The file already
knows this: `nsmul_surjective` carries `[IsAlgClosed F]` for exactly this reason,
and `[2]` is the very map that leaf is about. `IsIsogeny.add` simply failed to
carry the same hypothesis.

**The repair, below.** `IsIsogeny.add` is restated with `[IsAlgClosed F]` and is
then a theorem, proven from `IsRationalMap.add` together with one new leaf,
`IsRationalMap.isIsogeny`, which isolates the honest geometric content: over an
algebraically closed field the `surjective` and `finite_ker` fields of `IsIsogeny`
are automatic.

**Consequence for consumers.** `endSubring` — and hence `End W`,
`End.sq_eq_intCast_iff`, `End.toIsogeny` — inherit `[IsAlgClosed F]`. Every
existing consumer (`MazurTorsion.lean`'s Atkin–Lehner leaves at levels 125 and
169) already works over `AlgebraicClosure ℚ`, so nothing downstream is lost.
`IsIsogeny.zero`, `IsIsogeny.id`, `IsIsogeny.neg` and `IsIsogeny.comp` are
untouched: each is true over an arbitrary field, and each is proven.
-/

namespace NotIsIsogenyAdd

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- `y² = x³ - x` over `𝔽₅`. Its group of points is `ℤ/2 × ℤ/4`. -/
def W₅ : Affine (ZMod 5) := ⟨0, 0, 0, -1, 0⟩

theorem nonsingular_zero_zero : W₅.Nonsingular 0 0 := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  exact ⟨by decide, Or.inl (by decide)⟩

theorem nonsingular_two_one : W₅.Nonsingular 2 1 := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  exact ⟨by decide, Or.inr (by decide)⟩

/-- The 2-torsion point `(0,0)`. -/
def T : W₅.Point := Affine.Point.some 0 0 nonsingular_zero_zero

/-- A point of order 4, witnessing that `[2] ≠ 0`. -/
def P : W₅.Point := Affine.Point.some 2 1 nonsingular_two_one

theorem T_ne_zero : T ≠ 0 := Affine.Point.some_ne_zero _

theorem T_add_T : T + T = 0 :=
  Affine.Point.add_self_of_Y_eq (h₁ := nonsingular_zero_zero)
    (show (0 : ZMod 5) = W₅.negY 0 0 by decide)

theorem P_add_P_ne_zero : P + P ≠ 0 := by
  rw [show P + P = _ from Affine.Point.add_self_of_Y_ne (h₁ := nonsingular_two_one)
    (show (1 : ZMod 5) ≠ W₅.negY 2 1 by decide)]
  exact Affine.Point.some_ne_zero _

/-- Doubling on `W₅(𝔽₅)` is not an isogeny: it is nonzero, but on a finite group it
is not injective, hence not surjective. -/
theorem not_isIsogeny_add :
    ¬ IsIsogeny (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) := by
  intro h
  haveI : Finite W₅.Point := by
    haveI : Finite (WithZero {xy : ZMod 5 × ZMod 5 // W₅.Nonsingular xy.1 xy.2}) :=
      inferInstanceAs (Finite (Option _))
    exact Finite.of_equiv _ (Affine.nonsingularPointEquiv W₅).symm
  have happ : ∀ Q : W₅.Point,
      (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) Q = Q + Q := fun Q => rfl
  have hne : AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point ≠ 0 := by
    intro hc
    have hc' := congrArg (fun f : W₅.Point →+ W₅.Point => f P) hc
    simp only [AddMonoidHom.zero_apply, happ] at hc'
    exact P_add_P_ne_zero hc'
  have hinj : Function.Injective (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) :=
    (Finite.injective_iff_surjective
      (f := fun Q => (AddMonoidHom.id W₅.Point + AddMonoidHom.id W₅.Point) Q)).2
      (h.surjective hne)
  exact T_ne_zero (hinj (by simp only [happ, T_add_T, add_zero]))

/-- **The refutation, assembled.** Both hypotheses of the original `IsIsogeny.add`
are discharged by `IsIsogeny.id`, so the unconditional statement is false. -/
theorem isIsogeny_add_is_false :
    ¬ ∀ {F : Type} [Field F] [DecidableEq F] {W W' : Affine F}
        {φ ψ : W.Point →+ W'.Point}, IsIsogeny φ → IsIsogeny ψ → IsIsogeny (φ + ψ) :=
  fun h => not_isIsogeny_add (h IsIsogeny.id IsIsogeny.id)

end NotIsIsogenyAdd

/-- **LEAF.** Over an **algebraically closed** field, a homomorphism of point groups
that is given by rational functions in the coordinates already **is** an isogeny:
the `surjective` and `finite_ker` fields of `IsIsogeny` come for free there.

This is the honest geometric content that the unconditional `IsIsogeny.add`
silently assumed, and the FALSITY AUDIT above is the proof that it cannot be
dropped.

The mathematics. A nonzero homomorphism `φ` is a nonconstant morphism of curves, so
each fibre is finite — in particular `ker φ` is. Its image is then a subgroup of
`W'(F)` of finite index in no proper way: over an algebraically closed field
`W'(F)` is divisible, and a divisible group has no proper subgroup of finite index,
while a nonconstant morphism of complete curves has closed, cofinite image. Hence
`φ` is surjective.

Relation to the other geometric leaves of this file: this statement SUBSUMES
`nsmul_surjective`, and the `n`-torsion half of `finite_nsmulKer`, as soon as
`mulByHom W n` is known to be rational (division polynomials). Those two leaves
have a separate owner and are deliberately left in place; consolidating them is a
cut-level decision, not one to make here. -/
theorem IsRationalMap.isIsogeny [IsAlgClosed F] {φ : W.Point →+ W'.Point}
    (h : IsRationalMap φ) : IsIsogeny φ :=
  sorry

/-- The pointwise sum of two isogenies over an **algebraically closed** field is an
isogeny — this is the statement that `Hom(W, W')` is a group under addition in the
category of curves.

`[IsAlgClosed F]` is NOT removable: see the FALSITY AUDIT above, where dropping it
makes the statement false already for `φ = ψ = id` over `𝔽₅`. -/
theorem IsIsogeny.add [IsAlgClosed F] {φ ψ : W.Point →+ W'.Point}
    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ) : IsIsogeny (φ + ψ) :=
  (hφ.isRationalMap.add hψ.isRationalMap).isIsogeny

/-- The composite of two isogenies is an isogeny. -/
theorem IsIsogeny.comp {φ : W.Point →+ W'.Point} {ψ : W'.Point →+ W''.Point}
    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ) : IsIsogeny (ψ.comp φ) where
  isRationalMap := hφ.isRationalMap.comp hψ.isRationalMap
  surjective hne := by
    have hφ0 : φ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    have hψ0 : ψ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    exact (hψ.surjective hψ0).comp (hφ.surjective hφ0)
  finite_ker hne := by
    have hφ0 : φ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    have hψ0 : ψ ≠ 0 := by rintro rfl; exact hne (by ext P; simp)
    -- `ker (ψ ∘ φ)` is contained in the union, over the finite set `ker ψ`, of the
    -- fibres of `φ`; each nonempty fibre of `φ` is a coset of the finite `ker φ`.
    have hfib : ∀ Q : W'.Point, {P : W.Point | φ P = Q}.Finite := by
      intro Q
      by_cases hQ : ∃ P₀ : W.Point, φ P₀ = Q
      · obtain ⟨P₀, hP₀⟩ := hQ
        have hcoset : {P : W.Point | φ P = Q}
            = (fun k : W.Point => P₀ + k) '' (AddMonoidHom.ker φ : Set W.Point) := by
          ext P
          simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, AddMonoidHom.mem_ker]
          constructor
          · intro hp
            exact ⟨P - P₀, by rw [map_sub, hp, hP₀, sub_self], by abel⟩
          · rintro ⟨k, hk, rfl⟩
            rw [map_add, hk, add_zero, hP₀]
        rw [hcoset]
        exact Set.Finite.image _ (hφ.finite_ker hφ0)
      · simp only [not_exists] at hQ
        have hempty : {P : W.Point | φ P = Q} = ∅ := by
          ext P; simpa using hQ P
        rw [hempty]; exact Set.finite_empty
    have hsub : (AddMonoidHom.ker (ψ.comp φ) : Set W.Point) ⊆
        ⋃ Q ∈ (AddMonoidHom.ker ψ : Set W'.Point), {P : W.Point | φ P = Q} := by
      intro P hP
      have hQ : φ P ∈ (AddMonoidHom.ker ψ : Set W'.Point) := by
        have := (AddMonoidHom.mem_ker (f := ψ.comp φ)).1 hP
        simpa [SetLike.mem_coe, AddMonoidHom.mem_ker] using this
      exact Set.mem_biUnion hQ rfl
    exact Set.Finite.subset
      (Set.Finite.biUnion (hψ.finite_ker hψ0) (fun Q _ => hfib Q)) hsub

/-- Multiplication by `n` on the points of `W`, as a homomorphism. This is the
`[n]` that appears in `ψ̂ ∘ ψ = [deg ψ]`; it agrees with the image of `n` in
`End W` (`End.natCast_apply`). -/
def mulByHom (W : Affine F) (n : ℕ) : W.Point →+ W.Point :=
  AddMonoidHom.mk' (fun P => n • P) (fun a b => by simp [smul_add])

@[simp] theorem mulByHom_apply (n : ℕ) (P : W.Point) : mulByHom W n P = n • P := rfl

/-- The type of isogenies `W → W'`.

A one-field-plus-proof structure, so that two isogenies are equal precisely when
their maps on points are — which is what makes `End W` a ring. -/
structure Isogeny (W W' : Affine F) where
  /-- The underlying homomorphism of point groups. -/
  toHom : W.Point →+ W'.Point
  /-- The proof that it is an isogeny. -/
  isIsogeny : IsIsogeny toHom

namespace Isogeny

instance : CoeFun (Isogeny W W') (fun _ => W.Point → W'.Point) := ⟨fun φ => φ.toHom⟩

@[ext] theorem ext {φ ψ : Isogeny W W'} (h : ∀ P, φ.toHom P = ψ.toHom P) : φ = ψ := by
  cases φ; cases ψ; simp only [Isogeny.mk.injEq]; exact AddMonoidHom.ext h

/-- The zero isogeny. -/
def zero : Isogeny W W' := ⟨0, IsIsogeny.zero⟩

/-- The identity isogeny. -/
def id (W : Affine F) : Isogeny W W := ⟨AddMonoidHom.id W.Point, IsIsogeny.id⟩

/-- Composition of isogenies. -/
def comp (ψ : Isogeny W' W'') (φ : Isogeny W W') : Isogeny W W'' :=
  ⟨ψ.toHom.comp φ.toHom, IsIsogeny.comp φ.isIsogeny ψ.isIsogeny⟩

@[simp] theorem comp_toHom (ψ : Isogeny W' W'') (φ : Isogeny W W') :
    (ψ.comp φ).toHom = ψ.toHom.comp φ.toHom := rfl

@[simp] theorem comp_apply (ψ : Isogeny W' W'') (φ : Isogeny W W') (P : W.Point) :
    (ψ.comp φ).toHom P = ψ.toHom (φ.toHom P) := rfl

section Degree

open scoped Classical

/-- The **degree** of an isogeny: the cardinality of its kernel, and `0` for the
zero map.

In characteristic zero every isogeny is separable, so this is the classical
degree; see the module docstring for why it is defined this way rather than read
off the presenting polynomials. -/
noncomputable def degree (φ : Isogeny W W') : ℕ :=
  if φ.toHom = 0 then 0 else Nat.card (AddMonoidHom.ker φ.toHom)

theorem degree_of_ne_zero {φ : Isogeny W W'} (h : φ.toHom ≠ 0) :
    φ.degree = Nat.card (AddMonoidHom.ker φ.toHom) := by
  rw [degree, if_neg h]

theorem degree_of_eq_zero {φ : Isogeny W W'} (h : φ.toHom = 0) : φ.degree = 0 := by
  rw [degree, if_pos h]

end Degree

@[simp] theorem degree_zero : (zero : Isogeny W W').degree = 0 := degree_of_eq_zero rfl

/-- An isogeny has degree `0` exactly when it is the zero map. -/
theorem degree_eq_zero_iff (φ : Isogeny W W') : φ.degree = 0 ↔ φ.toHom = 0 := by
  refine ⟨fun h => by_contra fun hne => ?_, degree_of_eq_zero⟩
  rw [degree_of_ne_zero hne] at h
  haveI : Finite (AddMonoidHom.ker φ.toHom) :=
    Set.Finite.to_subtype (φ.isIsogeny.finite_ker hne)
  haveI : Nonempty (AddMonoidHom.ker φ.toHom) := ⟨0⟩
  exact absurd h Nat.card_pos.ne'

theorem degree_pos {φ : Isogeny W W'} (h : φ.toHom ≠ 0) : 0 < φ.degree :=
  Nat.pos_of_ne_zero fun hc => h ((degree_eq_zero_iff φ).1 hc)

/-- The identity has degree `1`.

The hypothesis is not removable: if `W` had only the point at infinity then the
identity *would be* the zero map, of degree `0`. Over an algebraically closed
field it is of course always satisfied. -/
theorem degree_id (h : ∃ P : W.Point, P ≠ 0) : (Isogeny.id W).degree = 1 := by
  obtain ⟨P, hP⟩ := h
  have hne : (Isogeny.id W).toHom ≠ 0 := by
    intro hc
    have hPc := congrArg (fun f : W.Point →+ W.Point => f P) hc
    simp only [Isogeny.id, AddMonoidHom.id_apply, AddMonoidHom.zero_apply] at hPc
    exact hP hPc
  rw [degree_of_ne_zero hne]
  have hker : AddMonoidHom.ker (Isogeny.id W).toHom = ⊥ := by
    ext Q; simp [Isogeny.id]
  rw [hker]
  simp

/-- Every element of the kernel of an isogeny is killed by its degree. Lagrange's
theorem in the kernel; it is what lets `[deg φ]` factor through `φ` in the
construction of the dual. -/
theorem degree_nsmul_eq_zero {φ : Isogeny W W'} {k : W.Point}
    (hk : k ∈ AddMonoidHom.ker φ.toHom) (h0 : φ.toHom ≠ 0) : φ.degree • k = 0 := by
  have h : Nat.card (AddMonoidHom.ker φ.toHom) • (⟨k, hk⟩ : AddMonoidHom.ker φ.toHom) = 0 :=
    card_nsmul_eq_zero'
  rw [degree_of_ne_zero h0]
  simpa using congrArg (Subtype.val) h

end Isogeny

/-! ### The endomorphism ring -/

/-- The endomorphisms of `W` that are isogenies form a subring of the endomorphism
ring of the abstract point group.

The `Ring` structure is inherited, and it is the *right* one: multiplication is
composition and, crucially, `((n : ℤ) : End W)` is multiplication by `n` on points
**definitionally** (`End.intCast_apply` below is `rfl`). So `ψ * ψ = -125` in
`End W` says exactly `ψ (ψ P) = -125 • P` for all `P`, with `ψ` an honest
morphism.

`[IsAlgClosed F]` is inherited from `IsIsogeny.add`, which is FALSE without it —
see the FALSITY AUDIT above. Over a general field the isogenies among the
endomorphisms of `W.Point` are **not** closed under addition, so there is no such
subring; `[2] = id + id` on `W₅(𝔽₅)` is an explicit failure of `add_mem'`. -/
def endSubring [IsAlgClosed F] (W : Affine F) : Subring (AddMonoid.End W.Point) where
  carrier := {f | IsIsogeny (f : W.Point →+ W.Point)}
  zero_mem' := IsIsogeny.zero
  one_mem' := IsIsogeny.id
  add_mem' hf hg := IsIsogeny.add hf hg
  neg_mem' hf := hf.neg
  mul_mem' hf hg := IsIsogeny.comp hg hf

/-- `End W`, the endomorphism ring of `W`. -/
abbrev End [IsAlgClosed F] (W : Affine F) : Type _ := ↥(endSubring W)

/-- **The soundness lemma of this file.** In `End W` the integer `n` acts as
multiplication by `n` on points — definitionally. Together with `IsRationalMap`
inside `IsIsogeny`, this is what makes `ψ * ψ = (-125 : End W)` a statement about
complex multiplication rather than about `M₂(Ẑ)`. -/
@[simp] theorem End.intCast_apply [IsAlgClosed F] (n : ℤ) (P : W.Point) :
    ((n : End W) : AddMonoid.End W.Point) P = n • P := rfl

@[simp] theorem End.natCast_apply [IsAlgClosed F] (n : ℕ) (P : W.Point) :
    ((n : End W) : AddMonoid.End W.Point) P = n • P := rfl

@[simp] theorem End.mul_apply [IsAlgClosed F] (f g : End W) (P : W.Point) :
    ((f * g : End W) : AddMonoid.End W.Point) P
      = (f : AddMonoid.End W.Point) ((g : AddMonoid.End W.Point) P) := rfl

/-- **The consumer-facing form of the Atkin–Lehner condition.** `ψ * ψ = (n : End W)`
in the endomorphism ring says exactly that `ψ` applied twice is multiplication by
`n` on points.

This is the lemma the `X_0(N)` descent leaves use: `ψ * ψ = (-125 : End W)` unfolds
to `ψ (ψ P) = -125 • P` for every `P`, with `ψ` carrying its `IsIsogeny` witness —
so the condition is about an actual morphism, not about `M₂(Ẑ)`. -/
theorem End.sq_eq_intCast_iff [IsAlgClosed F] (ψ : End W) (n : ℤ) :
    ψ * ψ = (n : End W) ↔ ∀ P : W.Point,
      (ψ : AddMonoid.End W.Point) ((ψ : AddMonoid.End W.Point) P) = n • P := by
  constructor
  · intro h P
    have hc := congrArg (fun f : End W => (f : AddMonoid.End W.Point) P) h
    simpa using hc
  · intro h
    refine Subtype.ext (AddMonoidHom.ext fun P => ?_)
    exact h P

/-- Every element of `End W` is an isogeny, so the endomorphism ring maps into the
type of isogenies. -/
def End.toIsogeny [IsAlgClosed F] (f : End W) : Isogeny W W := ⟨(f : AddMonoid.End W.Point), f.2⟩

@[simp] theorem End.toIsogeny_toHom [IsAlgClosed F] (f : End W) :
    (End.toIsogeny f).toHom = (f : AddMonoid.End W.Point) := rfl

/-! ### The two geometric inputs -/

/-- **LEAF.** Multiplication by a nonzero integer is surjective on the points of
an elliptic curve over an algebraically closed field.

This is the divisibility of `E(F)`, and it is one of the two geometric inputs on
which the degree/dual arithmetic rests. It is *not* formal: a homomorphic image
of a divisible group need not be the whole target. -/
theorem nsmul_surjective [IsAlgClosed F] [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (fun P : W.Point => n • P) :=
  sorry

/-- **LEAF.** The `n`-torsion of an elliptic curve is finite.

The second geometric input. Over an algebraically closed field of characteristic
zero it is in fact `(ℤ/n)²`; only finiteness is used here. -/
theorem finite_nsmulKer [IsAlgClosed F] [W.IsElliptic] {n : ℕ} (hn : n ≠ 0) :
    {P : W.Point | n • P = 0}.Finite :=
  sorry

/-! ### The dual isogeny -/

namespace Isogeny

/-- The dual of a nonzero isogeny, as a homomorphism of point groups.

Construction: `ker φ` is a group of order `n = deg φ`, so `n • k = 0` for every
`k ∈ ker φ` (`degree_nsmul_eq_zero`); hence multiplication by `n` on `W` kills
`ker φ` and descends along the isomorphism `W.Point ⧸ ker φ ≃+ W'.Point` supplied
by surjectivity. That the result is again an isogeny is `isRationalMap_dualHom`
plus the two geometric leaves — see `dual`. -/
noncomputable def dualHom (φ : Isogeny W W') (h0 : φ.toHom ≠ 0) : W'.Point →+ W.Point :=
  (QuotientAddGroup.lift (AddMonoidHom.ker φ.toHom) (mulByHom W φ.degree)
      (fun k hk => by
        simpa using degree_nsmul_eq_zero hk h0)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective φ.toHom
      (φ.isIsogeny.surjective h0)).symm.toAddMonoidHom

/-- **`ψ̂ ∘ ψ = [deg ψ]`** — the defining property of the dual isogeny. -/
theorem dualHom_comp (φ : Isogeny W W') (h0 : φ.toHom ≠ 0) (P : W.Point) :
    φ.dualHom h0 (φ.toHom P) = φ.degree • P := by
  have hsymm : (QuotientAddGroup.quotientKerEquivOfSurjective φ.toHom
      (φ.isIsogeny.surjective h0)).symm (φ.toHom P)
      = (QuotientAddGroup.mk P : W.Point ⧸ AddMonoidHom.ker φ.toHom) :=
    (QuotientAddGroup.quotientKerEquivOfSurjective φ.toHom
      (φ.isIsogeny.surjective h0)).symm_apply_eq.2 rfl
  simp only [dualHom, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, hsymm]
  rfl

/-- **LEAF.** The dual of an isogeny is again given by rational functions.

This is the one genuinely geometric half of the dual construction: the map
induced on the quotient is a morphism of curves.

A warning about its generality, recorded 2026-07-26. This statement carries **no**
`[IsAlgClosed F]`, and it is stated for a `φ` whose `IsIsogeny` witness asserts
surjectivity *on `F`-points*. Over a general field that hypothesis is extremely
strong — strong enough that the FALSITY AUDIT of `IsIsogeny.add` shows `[2]` on
`W(𝔽₅)` fails it — so the leaf is not false, but its `F`-point surjectivity
hypothesis is doing work that a reader will not expect. Whoever closes it should
consider adding `[IsAlgClosed F]` to match `dual`, which already carries it: that
costs nothing (every consumer is over `AlgebraicClosure ℚ`) and makes the
hypothesis honest rather than accidental.

The mathematics is not the substitution algebra of `IsRationalMap.comp` — the dual
is not obtained by composing given rational maps — so `homogSubst` will not help
directly. The classical route is via divisors: `φ̂` is `Pic⁰` functoriality, i.e.
`φ̂ = ι ∘ φ^* ∘ ι'⁻¹` through the isomorphisms `E ≅ Pic⁰(E)`, and rationality
comes from pullback of divisors being algebraic. Nothing in the current tree
provides `Pic⁰` of a Weierstrass curve, though `Affine.Point.toClass` into
`ClassGroup W.CoordinateRing` (mathlib, already used to prove associativity of the
group law) is the closest existing handle and is worth examining before building
divisor theory from scratch. -/
theorem isRationalMap_dualHom (φ : Isogeny W W') (h0 : φ.toHom ≠ 0) :
    IsRationalMap (φ.dualHom h0) :=
  sorry

/-- The dual isogeny, as an isogeny. -/
noncomputable def dual [IsAlgClosed F] [W.IsElliptic] (φ : Isogeny W W') (h0 : φ.toHom ≠ 0) :
    Isogeny W' W :=
  ⟨φ.dualHom h0,
   { isRationalMap := isRationalMap_dualHom φ h0
     surjective := fun _ Q => by
       obtain ⟨P, hP⟩ := nsmul_surjective (W := W) (degree_pos h0).ne' Q
       exact ⟨φ.toHom P, by rw [dualHom_comp]; exact hP⟩
     finite_ker := fun _ => by
       -- `ker φ̂ = φ (W[n])`, the image of the finite `n`-torsion.
       refine Set.Finite.subset
         ((finite_nsmulKer (W := W) (n := φ.degree) (degree_pos h0).ne').image φ.toHom) ?_
       intro Q hQ
       obtain ⟨P, rfl⟩ := φ.isIsogeny.surjective h0 Q
       refine ⟨P, ?_, rfl⟩
       have hd := dualHom_comp φ h0 P
       have hz : φ.dualHom h0 (φ.toHom P) = 0 := hQ
       rw [hd] at hz
       exact hz }⟩

@[simp] theorem dual_toHom [IsAlgClosed F] [W.IsElliptic] (φ : Isogeny W W')
    (h0 : φ.toHom ≠ 0) : (φ.dual h0).toHom = φ.dualHom h0 := rfl

/-- **`ψ̂ ∘ ψ = [deg ψ]`**, packaged as an equation of isogenies. -/
theorem dual_comp [IsAlgClosed F] [W.IsElliptic] (φ : Isogeny W W') (h0 : φ.toHom ≠ 0)
    (P : W.Point) : ((φ.dual h0).comp φ).toHom P = φ.degree • P :=
  dualHom_comp φ h0 P

/-- **LEAF.** The degree is multiplicative under composition.

Group-theoretically this is `#ker (ψ ∘ φ) = #ker φ · #ker ψ`, from the short exact
sequence `ker φ ↪ ker (ψ ∘ φ) ↠ ker ψ` whose surjectivity is surjectivity of
`φ`. -/
theorem degree_comp (φ : Isogeny W W') (ψ : Isogeny W' W'') :
    (ψ.comp φ).degree = ψ.degree * φ.degree :=
  sorry

end Isogeny

end WeierstrassCurve
