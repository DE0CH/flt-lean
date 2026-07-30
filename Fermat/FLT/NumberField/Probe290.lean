/-
SCRATCH PROBE — flt-lean-290. DELETE BEFORE COMMITTING.
-/
module

public import Fermat.FLT.NumberField.UnramifiedClassFieldBound
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.NumberTheory.RamificationInertia.Galois

@[expose] public section

open scoped nonZeroDivisors NumberField

namespace Probe290

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

-- basic tower facts
example : FiniteDimensional K L := inferInstance
example : Module.Finite (𝓞 K) (𝓞 L) := inferInstance
example : IsIntegralClosure (𝓞 L) (𝓞 K) L := inferInstance
example : IsScalarTower (𝓞 K) (𝓞 L) L := inferInstance
example : IsScalarTower (𝓞 K) K L := inferInstance

-- the Galois action on the ring of integers
example : MulSemiringAction (L ≃ₐ[K] L) L := inferInstance
example : MulSemiringAction (L ≃ₐ[K] L) (𝓞 L) := inferInstance
example : SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) := inferInstance
example : Algebra.IsInvariant (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) := inferInstance

-- residue fields are finite
example (Q : Ideal (𝓞 L)) [Q.IsMaximal] : Finite (𝓞 L ⧸ Q) := inferInstance

-- perfect fraction field, for relNorm of a prime
example : PerfectField (FractionRing (𝓞 K)) := inferInstance

-- inertia degree signature
example (Q : Ideal (𝓞 L)) : ℕ := Q.inertiaDeg (𝓞 K)

end Probe290
