/-
Chebotarev.lean — own work for the Fermat project (not vendored from the
FLT project).

The decomposition of the Chebotarev–Brauer–Nesbitt node
(`not_isIrreducible_of_charFrob_eq`, `HardlyRamified/Lift.lean`) begins
here. This file provides:

* `GaloisRepresentation.globalFrob v : Γ K` — the global (arithmetic)
  Frobenius element at a finite place `v`: the image of the local
  arithmetic Frobenius `Frobᵥ ∈ Γ Kᵥ` under the map `Γ Kᵥ → Γ K` induced
  by `K → Kᵥ` (and the arbitrary-but-fixed embedding of algebraic closures
  built into `Field.absoluteGaloisGroup.map`). This is the group element
  at which `GaloisRep.charFrob` evaluates: `ρ.charFrob v =
  (ρ (globalFrob v)).charpoly` holds by definition
  (`charFrob_eq_charpoly_globalFrob`).

* **Chebotarev density** (`dense_conjClasses_globalFrob`, sorry node): for
  any finite set `S` of finite places of `ℚ`, the union of the conjugacy
  classes of the global Frobenius elements at places outside `S` is dense
  in `Γ ℚ`. This is the topological form of the Chebotarev density theorem
  needed here (density of Frobenii); the full measure-theoretic statement
  is strictly stronger and not required.

The remaining pieces of the decomposition (Brauer–Nesbitt for
2-dimensional mod-`ℓ` representations, the mod-`ℓ` cyclotomic character as
a continuous character, and its value `q` at `globalFrob q`) follow in
later layers; see `PROGRESS.md`.
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep

@[expose] public section

namespace GaloisRepresentation

open IsDedekindDomain
open scoped NumberField

universe u

variable {K : Type u} [Field K] [NumberField K]

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)

/-- The global arithmetic Frobenius element at a finite place `v` of a
number field `K`: the image in `Γ K` of the local arithmetic Frobenius
`Frobᵥ ∈ Γ Kᵥ` under the map induced by `K → Kᵥ` (with the same
arbitrary-but-fixed embedding of algebraic closures that
`GaloisRep.toLocal` uses, so that `charFrob` literally evaluates at this
element). Well-defined only up to conjugacy and up to inertia at `v`;
every statement below is conjugation-invariant and concerns places where
the representations at hand are unramified. -/
noncomputable def globalFrob (v : Ω K) : Γ K :=
  Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K))
    (Field.AbsoluteGaloisGroup.adicArithFrob v)

/-- `charFrob` is the characteristic polynomial of the representation
evaluated at the global Frobenius element — by definition. -/
lemma GaloisRep.charFrob_eq_charpoly_globalFrob {A : Type*} [CommRing A]
    [TopologicalSpace A] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) (v : Ω K) :
    ρ.charFrob v = (ρ (globalFrob v)).charpoly :=
  rfl

set_option warn.sorry false in
/-- **Chebotarev density, topological form** (sorry node): for a finite
set `S` of finite places of a number field `K`, the union of the conjugacy
classes of the global Frobenius elements at the places outside `S` is
dense in the absolute Galois group. -/
theorem dense_conjClasses_globalFrob (S : Finset (Ω K)) :
    Dense {x : Γ K | ∃ v : Ω K, v ∉ S ∧ ∃ g : Γ K,
      x = g * globalFrob v * g⁻¹} :=
  sorry

end GaloisRepresentation
