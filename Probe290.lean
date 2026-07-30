import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Ideal.Norm.RelNorm

open NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- 1. The action of the Galois group on the ring of integers.
example : MulSemiringAction (L ≃ₐ[K] L) (𝓞 L) := inferInstance

-- 2. Commutation with the base.
example : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := inferInstance

-- 3. Finiteness of residue fields.
example (Q : Ideal (𝓞 L)) (hQ : Q ≠ ⊥) : Finite (𝓞 L ⧸ Q) := by
  infer_instance

-- 4. Invariance: 𝓞 K is the fixed ring.
example : Algebra.IsInvariant (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) := by
  infer_instance

-- 5. The Frobenius element itself.
noncomputable example (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite (𝓞 L ⧸ Q)] : L ≃ₐ[K] L :=
  arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q
