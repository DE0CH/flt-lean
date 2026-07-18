/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on admissible changes of variables

Material for `Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange`: decidable equality,
the negation automorphism `[-1]`, compatibility of changes of variables with base change,
and Galois descent for changes of variables.
-/

@[expose] public section

namespace WeierstrassCurve

universe u


variable {K : Type u} [Field K] (E : WeierstrassCurve K)

/-- The automorphism `[-1] : (x, y) ↦ (x, -y - a₁x - a₃)` of a Weierstrass curve, as an admissible
change of variables `⟨-1, 0, -a₁, -a₃⟩`. It fixes `E` (`negVariableChange_smul_self`) and is an
involution (`negVariableChange_mul_self`). -/
def negVariableChange : VariableChange K :=
  ⟨-1, 0, -E.a₁, -E.a₃⟩



-- (module-system note: consumed by Aut.lean proofs whose exported bodies hide
-- the edges from the term-cone detector — do not delete as free-floating.)
@[simp] lemma negVariableChange_u : E.negVariableChange.u = -1 := rfl

lemma negVariableChange_smul_self : E.negVariableChange • E = E := by
  simp [variableChange_def, negVariableChange]
  ring_nf

lemma negVariableChange_mul_self : E.negVariableChange * E.negVariableChange = 1 := by
  simp [VariableChange.mul_def, VariableChange.one_def, negVariableChange,
    Odd.neg_one_pow (by decide : Odd 3)]

lemma negVariableChange_inv : E.negVariableChange⁻¹ = E.negVariableChange :=
  inv_eq_of_mul_eq_one_right E.negVariableChange_mul_self

/-- Base change commutes with the negation automorphism: mapping `[-1]` on `W` through a ring
homomorphism `φ` gives `[-1]` on `W.map φ`. -/
lemma negVariableChange_map {A B : Type*} [Field A] [Field B] (W : WeierstrassCurve A)
    (φ : A →+* B) : W.negVariableChange.map φ = (W.map φ).negVariableChange := by
  ext <;> simp [negVariableChange]


section

variable (L : Type*) [Field L] [Algebra K L]


/-- Base change commutes with the action of changes of variables. -/
lemma baseChange_smul_baseChange (C : VariableChange K) (V : WeierstrassCurve K) :
    (C.baseChange L) • V.baseChange L = (C • V).baseChange L :=
  map_variableChange (W := V) (C := C) (φ := algebraMap K L)



end

end WeierstrassCurve

end
