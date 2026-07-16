/-
TorsionFinite.lean — own work for the Fermat project (not vendored from the
FLT project).

Finiteness of the `n`-torsion of an elliptic curve over a field, reduced to
two explicit polynomial statements about division polynomials:

* `eval_ΨSq_eq_zero_of_smul_eq_zero` (sorry node): a nonzero affine point
  killed by `n ≠ 0` has its `x`-coordinate a root of the univariate
  polynomial `ΨSq n`. This is the heart of the theory of division
  polynomials (the multiplication-by-`n` formulas); mathlib has the
  polynomials themselves (`Mathlib.AlgebraicGeometry.EllipticCurve.
  DivisionPolynomial.*`, D. Angdinata) but not yet their relation to the
  group law.

* `ΨSq_ne_zero_of_charDvd` (sorry node): `ΨSq n ≠ 0` also when the
  characteristic divides `n` (mathlib's `ΨSq_ne_zero` covers `(n : k) ≠ 0`).

Given these, the argument is elementary: a nonzero `n`-torsion point has
`x`-coordinate among the finitely many roots of `ΨSq n ≠ 0`, and for each
`x` there are at most two `y`'s (roots of the monic quadratic in `y` given
by the Weierstrass equation), so the coordinate map injects the `n`-torsion
into a finite set.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.Algebra.Module.Torsion.Basic

@[expose] public section

namespace TorsionFinite

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

/-- **Torsion points are cut out by division polynomials** (sorry node):
if a nonzero affine point `(x, y)` of the base change `E⁄k` is killed by
`n ≠ 0`, then `x` is a root of the univariate division polynomial `ΨSq n`.

This is the content of the multiplication-by-`n` formulas for division
polynomials; the polynomials are in mathlib, the relation to the group law
is ongoing work of D. Angdinata which must (per the project policy) also be
formalized in this tree. -/
theorem eval_ΨSq_eq_zero_of_smul_eq_zero {n : ℤ} (hn : n ≠ 0) {x y : k}
    (h : (E⁄k).Nonsingular x y)
    (hP : n • (WeierstrassCurve.Affine.Point.some x y h) = 0) :
    (WeierstrassCurve.ΨSq (E⁄k) n).IsRoot x :=
  sorry

/-- **Nonvanishing of division polynomials in the char-divides case**
(sorry node): `ΨSq n ≠ 0` for `n ≠ 0` even when the characteristic of `k`
divides `n` (so that mathlib's leading-coefficient argument fails; here
ellipticity is genuinely needed — the statement is false for a cuspidal
cubic in characteristic `p ∣ n`). -/
theorem ΨSq_ne_zero_of_charDvd {n : ℤ} (hn : n ≠ 0) (hchar : (n : k) = 0) :
    WeierstrassCurve.ΨSq (E⁄k) n ≠ 0 :=
  sorry

/-- `ΨSq n ≠ 0` for all `n ≠ 0`, over any field. -/
theorem ΨSq_ne_zero' {n : ℤ} (hn : n ≠ 0) : WeierstrassCurve.ΨSq (E⁄k) n ≠ 0 := by
  by_cases hchar : (n : k) = 0
  · exact ΨSq_ne_zero_of_charDvd E hn hchar
  · exact WeierstrassCurve.ΨSq_ne_zero (E⁄k) hchar

/-- The `n`-torsion of an elliptic curve over a field is finite (`n ≠ 0`). -/
theorem finite_torsionBy {n : ℤ} (hn : n ≠ 0) :
    Finite (Submodule.torsionBy ℤ (E⁄k).Point n) := by
  classical
  -- the monic quadratic in `y` obtained by fixing `x` in the Weierstrass equation
  let q : k → k[X] := fun x =>
    X ^ 2 + C ((E⁄k).a₁ * x + (E⁄k).a₃) * X
      - C (x ^ 3 + (E⁄k).a₂ * x ^ 2 + (E⁄k).a₄ * x + (E⁄k).a₆)
  have hq_ne : ∀ x, q x ≠ 0 := by
    intro x
    have h1 : (C ((E⁄k).a₁ * x + (E⁄k).a₃) * X
        - C (x ^ 3 + (E⁄k).a₂ * x ^ 2 + (E⁄k).a₄ * x + (E⁄k).a₆)).degree < 2 :=
      lt_of_le_of_lt
        ((Polynomial.degree_sub_le _ _).trans (max_le
          (Polynomial.degree_C_mul_X_le _)
          (Polynomial.degree_C_le.trans (by norm_num))))
        (by norm_num)
    have hmonic : (q x).Monic := by
      have := Polynomial.monic_X_pow_add (n := 2) h1
      simpa [q, add_sub_assoc] using this
    exact hmonic.ne_zero
  -- a point on the curve with abscissa `x` has ordinate a root of `q x`
  have hq_root : ∀ x y : k, (E⁄k).Equation x y → (q x).IsRoot y := by
    intro x y hxy
    rw [WeierstrassCurve.Affine.equation_iff] at hxy
    simp only [q, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination hxy
  -- the finite set of possible coordinate pairs
  set T : Set (k × k) :=
    ⋃ x ∈ {x : k | (WeierstrassCurve.ΨSq (E⁄k) n).IsRoot x},
      {x} ×ˢ {y : k | (q x).IsRoot y} with hTdef
  have hT : T.Finite :=
    Set.Finite.biUnion (Polynomial.finite_setOf_isRoot (ΨSq_ne_zero' E hn))
      fun x _ => (Set.finite_singleton x).prod (Polynomial.finite_setOf_isRoot (hq_ne x))
  -- the coordinate map
  let F : (E⁄k).Point → Option (k × k) := fun P =>
    match P with
    | .zero => none
    | .some x y _ => some (x, y)
  have hFinj : ∀ P Q : (E⁄k).Point, F P = F Q → P = Q := by
    intro P Q hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => rfl
      | some x y h => simp [F] at hPQ
    | some x y h =>
      cases Q with
      | zero => simp [F] at hPQ
      | some x' y' h' =>
        simp only [F, Option.some.injEq, Prod.mk.injEq] at hPQ
        obtain ⟨rfl, rfl⟩ := hPQ
        rfl
  -- torsion points map into `insert none (some '' T)`
  have hFmem : ∀ P : Submodule.torsionBy ℤ (E⁄k).Point n,
      F P.1 ∈ insert none (Option.some '' T) := by
    rintro ⟨P0, hP0⟩
    cases P0 with
    | zero => exact Set.mem_insert _ _
    | some x y h =>
      refine Set.mem_insert_of_mem _ ⟨(x, y), ?_, rfl⟩
      have hsmul : n • (WeierstrassCurve.Affine.Point.some x y h) = 0 := hP0
      exact Set.mem_biUnion (eval_ΨSq_eq_zero_of_smul_eq_zero E hn h hsmul)
        ⟨rfl, hq_root x y h.1⟩
  haveI := ((hT.image Option.some).insert none).to_subtype
  exact Finite.of_injective
    (fun P : Submodule.torsionBy ℤ (E⁄k).Point n =>
      (⟨F P.1, hFmem P⟩ : ↥(insert none (Option.some '' T))))
    fun P Q hPQ => Subtype.ext (hFinj _ _ (congrArg Subtype.val hPQ))

end TorsionFinite
