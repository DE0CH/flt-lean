/-
DiscriminantIdentity.lean — own work for the Fermat project.

The classical discriminant identity `E₄³ − E₆² = 1728·Δ` for level-one
modular forms, en route to the formal identity `TateCurve.ΔFormal_eq`
(the η²⁴/Jacobi discriminant identity in `ℤ⟦X⟧`).

Strategy (all-mathlib): the difference
`D := E₄·E₄·E₄ − E₆·E₆ − 1728·Δ` is a level-one modular form of weight
`12`; its `q`-expansion coefficients in degrees `0` and `1` vanish
(Eisenstein `q`-expansions `1 + 240σ₃`, `1 − 504σ₅`, and the
discriminant's order-`1` normalized expansion), so its `q`-expansion
order exceeds `12/12` and the Sturm bound
(`ModularForm.sturm_bound_levelOne`) forces `D = 0`.

This file currently contains the definition of `D` and the weight
bookkeeping; the coefficient computations and the Sturm application
follow in subsequent iterations.
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.Discriminant

@[expose] public section

noncomputable section

namespace DiscriminantIdentity

open UpperHalfPlane ModularForm SlashInvariantForm MatrixGroups

/-- The Eisenstein form `E₄` of weight `4`. -/
def E₄ : ModularForm 𝒮ℒ 4 := ModularForm.E (by norm_num)

/-- The Eisenstein form `E₆` of weight `6`. -/
def E₆ : ModularForm 𝒮ℒ 6 := ModularForm.E (by norm_num)

/-- `E₄³` as a modular form of weight `12`. -/
def E₄cubed : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num) (E₄.mul (E₄.mul E₄))

/-- `E₆²` as a modular form of weight `12`. -/
def E₆squared : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num) (E₆.mul E₆)

/-- The modular discriminant as a bundled `ModularForm` of weight `12`
(the underlying cusp form, with vanishing weakened to boundedness). -/
def discriminantMF : ModularForm 𝒮ℒ 12 where
  toSlashInvariantForm := CuspForm.discriminant.toSlashInvariantForm
  holo' := CuspForm.discriminant.holo'
  bdd_at_cusps' hc g hg :=
    (CuspForm.discriminant.zero_at_cusps' hc g hg).boundedAtFilter

/-- The difference `E₄³ − E₆² − 1728·Δ`, a level-one modular form of
weight `12`; the Sturm bound will show it vanishes. -/
def D : ModularForm 𝒮ℒ 12 :=
  E₄cubed - E₆squared - (1728 : ℂ) • discriminantMF

@[simp]
lemma E₄cubed_apply (z : ℍ) : E₄cubed z = E₄ z * (E₄ z * E₄ z) := rfl

@[simp]
lemma E₆squared_apply (z : ℍ) : E₆squared z = E₆ z * E₆ z := rfl

@[simp]
lemma D_apply (z : ℍ) :
    D z = E₄ z * (E₄ z * E₄ z) - E₆ z * E₆ z -
      1728 * ModularForm.discriminant z := by
  simp only [D, ModularForm.sub_apply]
  rfl

end DiscriminantIdentity
