module

public import Fermat.FLT.EllipticCurve.DifferentialCharacter

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine
open _root_.Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] {W W' : Affine F}

/-- **The `1`-part of the `y`-witness is automatic**: any rational-map witness tuple of a
GROUP HOMOMORPHISM satisfies `2·D·B + a₁′·A·E + a₃′·B·E = C·B·(a₁X + a₃)`. -/
theorem diffChar_yWitness_onePart [IsAlgClosed F] [W.IsElliptic]
    {φ : W.Point →+ W'.Point} (hker : (AddMonoidHom.ker φ : Set W.Point).Finite)
    {A B Cx D E : F[X]}
    (hrat : ∀ P : W.Point, φ P ≠ 0 →
      veluPointX (φ P) * B.eval (veluPointX P) = A.eval (veluPointX P) ∧
      veluPointY (φ P) * E.eval (veluPointX P)
        = Cx.eval (veluPointX P) * veluPointY P + D.eval (veluPointX P)) :
    C 2 * D * B + C W'.a₁ * A * E + C W'.a₃ * B * E
      = Cx * B * (C W.a₁ * X + C W.a₃) := by
  classical
  set p : F[X] := C 2 * D * B + C W'.a₁ * A * E + C W'.a₃ * B * E
      - Cx * B * (C W.a₁ * X + C W.a₃) with hp
  have hbad : (veluPointX '' (AddMonoidHom.ker φ : Set W.Point)).Finite := hker.image _
  have hsub : (veluPointX '' (AddMonoidHom.ker φ : Set W.Point))ᶜ ⊆ {t : F | p.IsRoot t} := by
    intro t ht
    obtain ⟨P, hP0, hPx⟩ := exists_point_veluPointX_eq (W := W) t
    have hφP : φ P ≠ 0 := fun hc => ht ⟨P, hc, hPx⟩
    have hnP0 : -P ≠ 0 := neg_ne_zero.2 hP0
    have hφnP : φ (-P) ≠ 0 := by rw [map_neg]; exact neg_ne_zero.2 hφP
    obtain ⟨hx, hy⟩ := hrat P hφP
    obtain ⟨-, hy'⟩ := hrat (-P) hφnP
    rw [velu_pointX_neg, velu_pointY_neg P hP0, map_neg,
      velu_pointY_neg (φ P) hφP] at hy'
    rw [hPx] at hx hy hy'
    show p.eval t = 0
    rw [hp]
    simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X]
    linear_combination (-(B.eval t)) * hy + (-(B.eval t)) * hy'
      + (-(W'.a₁ * E.eval t)) * hx
  have hzero : p = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.Infinite.mono hsub hbad.infinite_compl)
  rw [hp] at hzero
  linear_combination hzero

/-- **The denominator of `ω′` at `φ P`, in terms of the `y`-witness**: `ψ₂′(φP)·E = C·ψ₂(P)`
after clearing `B`. This is what turns the reduced differential certificate into a purely
polynomial statement. -/
theorem diffChar_psi_image_eq [IsAlgClosed F] [W.IsElliptic]
    {φ : W.Point →+ W'.Point} (hker : (AddMonoidHom.ker φ : Set W.Point).Finite)
    {A B Cx D E : F[X]}
    (hrat : ∀ P : W.Point, φ P ≠ 0 →
      veluPointX (φ P) * B.eval (veluPointX P) = A.eval (veluPointX P) ∧
      veluPointY (φ P) * E.eval (veluPointX P)
        = Cx.eval (veluPointX P) * veluPointY P + D.eval (veluPointX P))
    (P : W.Point) (hφP : φ P ≠ 0) :
    (2 * veluPointY (φ P) + W'.a₁ * veluPointX (φ P) + W'.a₃)
        * E.eval (veluPointX P) * B.eval (veluPointX P)
      = Cx.eval (veluPointX P) * B.eval (veluPointX P)
        * (2 * veluPointY P + W.a₁ * veluPointX P + W.a₃) := by
  obtain ⟨hx, hy⟩ := hrat P hφP
  have hone := congrArg (Polynomial.eval (veluPointX P))
    (diffChar_yWitness_onePart (W' := W') hker hrat)
  simp only [eval_add, eval_mul, eval_C, eval_X] at hone
  linear_combination 2 * B.eval (veluPointX P) * hy
    + W'.a₁ * E.eval (veluPointX P) * hx + hone

end WeierstrassCurve
