/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The degree of a principal divisor on a proper curve is zero

For a nonzero `g` in the function field of a smooth proper curve `X` over a field `K`,

  `∑_x ord_x(g) · [κ(x) : K] = 0`,

the sum running over the codimension-`1` (= closed) points of `X`.  Equivalently: `g` has
as many zeros as poles, both counted with multiplicity *and* with residue degree.

## Why this module exists, and why it is a whole module

**TWO blocked leaves of `Fermat/FLT/ModularCurve/X0.lean` reduce to this statement and to
nothing else**, so it is built once, here, rather than twice inside an 80 000-line file.
Both reductions were written into their own docstrings on 2026-07-31:

* `card_relPoint_not_liesIn_le_of_finite_toAffineLine` — the `K`-rational points of
  `X_K ∖ U_K` are `K`-rational POLES of `φ*t`, and the pole divisor has degree
  `deg φ ≤ 2`.  This is that leaf's only `ℙ¹`-free route.  The shape it consumes is
  `card_le_poleDegree` + `poleDegree_eq_zeroDegree` below.
* `hasDoubleCoverOfAffineLine_of_iso_sectionIdeal` — obligation (3) of three: the fibre of
  `f` over a `K`-point `c` is the zero divisor of `f − c`, of degree
  `deg (f)_∞ = 2`.  The shape it consumes is `zeroDegree_eq_poleDegree` below.

## The design decision, and why it is NOT `AlgebraicCycle`

`Mathlib` at this pin has `Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean`, but that
file holds only `mapCoeff`, `map` and `map_id`: there is **no degree of a cycle** and no
degree of a principal divisor, in any capitalisation (checked 2026-07-31).  So a
formulation over `AlgebraicCycle` would have to supply the degree anyway, and it would
cost something extra that the bespoke formulation does not:

* `AlgebraicCycle X R = Function.locallyFinsupp X R` is a BUNDLED object carrying a
  local-finiteness proof.  To write `div g` as an `AlgebraicCycle` one must first prove
  that `x ↦ ord_x g` has locally finite support — which is exactly the open leaf
  `finite_divSupport` below.  The definition would then be blocked behind a `sorry`, and
  a `Classical.choose` on a sorried existence puts `sorryAx` into the *type* of everything
  downstream (`/home/chend/.flt-agent-doctrine.md`, "A `Classical.choose` ON A SORRIED
  EXISTENCE PUTS `sorryAx` INTO THE *TYPE*").
* With `finsum` (`∑ᶠ`) every algebraic identity is *stateable* unconditionally, and
  finiteness enters only in the lemmas that genuinely need it, as an explicit hypothesis
  `(Scheme.divSupport g).Finite`.  Nothing here is blocked on `finite_divSupport`; that
  leaf is a separate, independently dispatchable obligation.

The price is the usual `finsum` junk convention: `∑ᶠ` over an infinite support is `0`.
That is why `finite_divSupport` is stated as a leaf at all — see its audit for what would
be silently vacuous without it, and see `divDegree_eq_zero_of_ne_zero`'s audit for the one
place the convention could make the main theorem true for the wrong reason.

## Degree of a point

The weight attached to a point `x` is `Scheme.Hom.residueDegree strX x`, i.e.
`[κ(x) : κ(strX x)]` — `Mathlib`'s own notion, the one `AlgebraicCycle.mapCoeff` uses.
Over `S = Spec K` the base residue field is `K`, so this is `[κ(x) : K]`.  It carries
`Mathlib`'s junk convention `finrank = 0` for an infinite extension, which is what makes
the whole development *degenerate* rather than *false* in dimension `≥ 2`; see the audit
on `divDegree_eq_zero_of_ne_zero`.

## Contents

* `Scheme.divSupport`, `Scheme.Hom.divCoeff`, `Scheme.Hom.divDegree` — the divisor of a
  rational function and its degree.  `Scheme.Hom.zeroCoeff`/`zeroDegree` and
  `poleCoeff`/`poleDegree` are its positive and negative parts.
* PROVEN, and unconditional on any curve hypothesis: `ord_one`, `ord_inv`, `divCoeff_one`,
  `divDegree_one`, `divCoeff_mul`, `divDegree_mul`, `divDegree_inv`,
  `divDegree_eq_zeroDegree_sub_poleDegree`, `zeroDegree_eq_poleDegree_inv`,
  `zeroDegree_nonneg`, `poleDegree_nonneg`, `card_le_poleDegree`, `card_le_zeroDegree`.
* PROVEN, and what makes "`K`-rational" usable: `residueDegree_eq_one_of_retraction` and
  `residueDegree_eq_one_of_section` — a section `Spec K ⟶ X` of `strX` has residue degree
  `1` at its image, which is what discharges the `1 ≤ residueDegree` hypothesis of the two
  counting lemmas.
* OPEN (sorry leaves, each with its own audit): `finite_divSupport`,
  `poleDegree_inv_eq_poleDegree`.
* PROVEN from those: `divDegree_eq_zero_of_ne_zero`, `divDegree_eq_zero`,
  `zeroDegree_eq_poleDegree`, `card_le_zeroDegree_of_poles` — the last is the exact shape
  `card_relPoint_not_liesIn_le_of_finite_toAffineLine` needs.

## THE SAME THEOREM IS ALREADY CUT TO ONE LEAF IN THIS DEVELOPMENT

`Fermat/FLT/ModularCurve/HyperellipticJacobian.lean` carries an abstract-places version of
`Σ_v ord_v(g)·[κ(v) : K] = 0` (`PlaceData.degOf_divisor_eq_zero`) which is **PROVEN**, over
the single leaf `degOf_poleDivisor_eq_finrank_of_transcendental` (Stichtenoth I.4.11).  So
there is exactly one open mathematical node behind both this module and that one, and the
cheapest way to close `poleDegree_inv_eq_poleDegree` here is a BRIDGE to that
formulation — not a second proof.  The full argument, including why
`HyperellipticJacobian.lean`'s `PlaceSystem` is already general enough to be the meeting
point, is in `poleDegree_inv_eq_poleDegree`'s own docstring.  Read it before starting.

## THE RIVAL MODULE `CurveDivisorDegree.lean`, AND WHY IT WAS DELETED (2026-07-31)

Two branches built this layer twice.  `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean`
was the other one; it is DELETED, and this module is the survivor.  Recover its text with
`git show fe5131ca:Fermat/FLT/Mathlib/AlgebraicGeometry/CurveDivisorDegree.lean`.

The two were the SAME NOTION, not two notions under one name — machine-checked, not read
off: its `divDegree strX f` unfolds to `∑ᶠ z, Scheme.ord f z * (strX.residueDegree z : ℤ)`,
which is this module's `Scheme.Hom.divDegree strX f` by `rfl`, and its `finite_support_ord`
has literally this module's `finite_divSupport` conclusion (`Scheme.divSupport` IS
`Function.support (Scheme.ord ·)` by `rfl`).  So the deletion is a de-duplication and not a
choice between rival mathematics.  This module was kept because it is strictly stronger on
every axis: it is stated over an ARBITRARY base `S` where the other fixed
`Spec (CommRingCat.of K)`; it carries the zero/pole decomposition, the two counting lemmas
and the `K`-rational-point bridge, none of which the other had; and its `divDegree_eq_zero`
needs no `g ≠ 0` where the other's `divDegree_eq_zero_curve` was a `sorry` leaf that did.
Nothing anywhere in `Fermat/` used a `CurveDivisorDegree`-only name, and no module imported
it at all, so its three leaves were compiled by nothing and were invisible to every build
and to the census — CLAUDE.md's FOURTH INVISIBILITY CLASS.

**WHAT WAS LOST, AND IT IS WORTH REINSTATING WITH A CONSUMER.**  Two of its three leaves
were duplicates of this module's (above).  The third was not, and neither was the theorem
built on it:

* `exists_hom_functionField_ratFunc_of_ord_eq_sub` (leaf) — a rational function with a
  single simple pole at a `K`-rational point generates the function field, so
  `K(X) ↪ K(t)`.  Stichtenoth I.4.11 in its sharp form;
* `birationalOver_affineLine_of_ord_eq_sub` (PROVEN over it, ~18 lines) — from
  `div f = [x] − [y]` with `x ≠ y` both `K`-rational, the curve is
  `Scheme.BirationalOver` the affine line, assembled from
  `BirationalFunctionField.lean`'s three sorry-free theorems.

That pair was aimed at `X0.lean`'s open leaf
`birationalOver_affineLine_of_relPicEquiv_sectionIdeal`, and it went with the module because
it had no consumer: a `sorry`-bodied leaf contributes no dependency edges, so reinstating it
on its own would be FREE-FLOATING CODE, which this project forbids.  It becomes legal the
moment the same edit rewrites that `X0.lean` leaf's body to consume it, which needs one
further sheaf-theoretic leaf — "an isomorphism `𝒪(−x) ≅ 𝒪(−y)` of invertible sheaves on an
integral scheme is multiplication by a rational function whose divisor is `[x] − [y]`".
That is a `1 → 2` trade in leaf count and a large gain in captured geometry; it is queued.

**AND THE COLLISION THAT KEPT THE TWO MODULES APART WAS ALREADY GONE.**  `X0.lean` carried
a note (release 31) saying the two collide on `AlgebraicGeometry.Scheme.ord_one` and
`Scheme.ord_inv`, and dropped its import of the other module on that basis.  Measured
2026-07-31: they do NOT collide, and importing both is green.  Lean's module system rejects
a duplicate full name across imports only when the two declarations DIFFER in what it
serialises — and THEOREM proof bodies are elided, so two theorems with the SAME STATEMENT
and different proofs are silently accepted, one shadowing the other with no diagnostic.
`ord_one` and `ord_inv` have the same statement in both files.  The collision release 29
really hit was `AlgebraicGeometry.divDegree_eq_zero`, whose two statements differed by an
`f ≠ 0`, and release 29 fixed it by renaming the other file's copy to
`divDegree_eq_zero_curve`.  See CLAUDE.md for the reproduction.

## References

Hartshorne, *Algebraic Geometry*, II.6.10 and IV.1; Stichtenoth, *Algebraic Function
Fields and Codes*, Theorem I.4.11 (`deg (x)_∞ = [F : K(x)]`, whence `deg (x) = 0`);
Fulton, *Algebraic Curves*, §8; the Stacks project's *Algebraic Curves* chapter, where the
statement is proven for an arbitrary proper curve with no normality hypothesis.
-/

@[expose] public section

open CategoryTheory Order

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

section Defs

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The support of the divisor of `g`: the points at which `g` has a zero or a pole.
`Scheme.ord` is `0` off the codimension-`1` points, so on a curve this is a set of closed
points. -/
def Scheme.divSupport (g : X.functionField) : Set X := Function.support (Scheme.ord g)

lemma Scheme.mem_divSupport_iff {g : X.functionField} {x : X} :
    x ∈ Scheme.divSupport g ↔ Scheme.ord g x ≠ 0 := Iff.rfl

/-- The coefficient of the divisor of `g` at `x`, weighted by the residue degree of `x`
over the base: `ord_x(g) · [κ(x) : κ(strX x)]`. -/
noncomputable def Scheme.Hom.divCoeff (strX : X ⟶ S) (g : X.functionField) (x : X) : ℤ :=
  Scheme.ord g x * (strX.residueDegree x : ℤ)

/-- The positive part of `divCoeff`: the coefficient of the ZERO divisor of `g`. -/
noncomputable def Scheme.Hom.zeroCoeff (strX : X ⟶ S) (g : X.functionField) (x : X) : ℤ :=
  max (Scheme.ord g x) 0 * (strX.residueDegree x : ℤ)

/-- The negative part of `divCoeff`, with its sign flipped: the coefficient of the POLE
divisor of `g`. -/
noncomputable def Scheme.Hom.poleCoeff (strX : X ⟶ S) (g : X.functionField) (x : X) : ℤ :=
  max (-Scheme.ord g x) 0 * (strX.residueDegree x : ℤ)

/-- The degree of the divisor of `g`. -/
noncomputable def Scheme.Hom.divDegree (strX : X ⟶ S) (g : X.functionField) : ℤ :=
  ∑ᶠ x : X, strX.divCoeff g x

/-- The degree of the zero divisor of `g`. -/
noncomputable def Scheme.Hom.zeroDegree (strX : X ⟶ S) (g : X.functionField) : ℤ :=
  ∑ᶠ x : X, strX.zeroCoeff g x

/-- The degree of the pole divisor of `g`. -/
noncomputable def Scheme.Hom.poleDegree (strX : X ⟶ S) (g : X.functionField) : ℤ :=
  ∑ᶠ x : X, strX.poleCoeff g x

end Defs

section Basic

variable [IsIntegral X] [IsLocallyNoetherian X] (strX : X ⟶ S)

@[simp]
lemma Scheme.ord_one (x : X) : Scheme.ord (1 : X.functionField) x = 0 := by
  have h := Scheme.ord_mul (x := x) (f := (1 : X.functionField)) (g := 1) one_ne_zero one_ne_zero
  simp only [mul_one] at h
  omega

lemma Scheme.ord_inv {g : X.functionField} (hg : g ≠ 0) (x : X) :
    Scheme.ord g⁻¹ x = -Scheme.ord g x := by
  have h := Scheme.ord_mul (x := x) (f := g) (g := g⁻¹) hg (inv_ne_zero hg)
  rw [mul_inv_cancel₀ hg, Scheme.ord_one] at h
  omega

lemma Scheme.divSupport_inv {g : X.functionField} (hg : g ≠ 0) :
    Scheme.divSupport g⁻¹ = Scheme.divSupport g := by
  ext x
  simp [Scheme.divSupport, Scheme.ord_inv hg]

@[simp]
lemma Scheme.divSupport_one : Scheme.divSupport (1 : X.functionField) = (∅ : Set X) := by
  ext x
  simp [Scheme.divSupport]

@[simp]
lemma Scheme.divSupport_zero : Scheme.divSupport (0 : X.functionField) = (∅ : Set X) := by
  ext x
  simp [Scheme.divSupport]

@[simp]
lemma Scheme.Hom.divCoeff_one (x : X) : strX.divCoeff (1 : X.functionField) x = 0 := by
  simp [Scheme.Hom.divCoeff]

@[simp]
lemma Scheme.Hom.divCoeff_zero (x : X) : strX.divCoeff (0 : X.functionField) x = 0 := by
  simp [Scheme.Hom.divCoeff]

@[simp]
lemma Scheme.Hom.divDegree_one : strX.divDegree (1 : X.functionField) = 0 := by
  simp [Scheme.Hom.divDegree]

@[simp]
lemma Scheme.Hom.divDegree_zero : strX.divDegree (0 : X.functionField) = 0 := by
  simp [Scheme.Hom.divDegree]

lemma Scheme.Hom.support_divCoeff_subset (g : X.functionField) :
    Function.support (strX.divCoeff g) ⊆ Scheme.divSupport g := by
  intro x hx
  simp only [Function.mem_support, Scheme.Hom.divCoeff, ne_eq, mul_eq_zero, not_or] at hx
  exact hx.1

lemma Scheme.Hom.support_zeroCoeff_subset (g : X.functionField) :
    Function.support (strX.zeroCoeff g) ⊆ Scheme.divSupport g := by
  intro x hx
  simp only [Function.mem_support, Scheme.Hom.zeroCoeff, ne_eq, mul_eq_zero, not_or] at hx
  intro h
  exact hx.1 (by omega)

lemma Scheme.Hom.support_poleCoeff_subset (g : X.functionField) :
    Function.support (strX.poleCoeff g) ⊆ Scheme.divSupport g := by
  intro x hx
  simp only [Function.mem_support, Scheme.Hom.poleCoeff, ne_eq, mul_eq_zero, not_or] at hx
  intro h
  exact hx.1 (by omega)

lemma Scheme.Hom.divCoeff_eq_zeroCoeff_sub_poleCoeff (g : X.functionField) (x : X) :
    strX.divCoeff g x = strX.zeroCoeff g x - strX.poleCoeff g x := by
  rw [Scheme.Hom.divCoeff, Scheme.Hom.zeroCoeff, Scheme.Hom.poleCoeff, ← sub_mul]
  congr 1
  omega

lemma Scheme.Hom.zeroCoeff_nonneg (g : X.functionField) (x : X) : 0 ≤ strX.zeroCoeff g x :=
  mul_nonneg (le_max_right _ _) (Int.natCast_nonneg _)

lemma Scheme.Hom.poleCoeff_nonneg (g : X.functionField) (x : X) : 0 ≤ strX.poleCoeff g x :=
  mul_nonneg (le_max_right _ _) (Int.natCast_nonneg _)

/-- Rewrite a `finsum` over the points of `X` as a `Finset.sum` over any finite superset of
`divSupport g`.  This is the single bridge every conditional lemma below goes through. -/
lemma Scheme.Hom.divDegree_eq_sum {g : X.functionField} (hfin : (Scheme.divSupport g).Finite) :
    strX.divDegree g = ∑ x ∈ hfin.toFinset, strX.divCoeff g x :=
  finsum_eq_sum_of_support_subset _ (by
    simpa [Set.Finite.coe_toFinset] using strX.support_divCoeff_subset g)

lemma Scheme.Hom.zeroDegree_eq_sum {g : X.functionField} (hfin : (Scheme.divSupport g).Finite) :
    strX.zeroDegree g = ∑ x ∈ hfin.toFinset, strX.zeroCoeff g x :=
  finsum_eq_sum_of_support_subset _ (by
    simpa [Set.Finite.coe_toFinset] using strX.support_zeroCoeff_subset g)

lemma Scheme.Hom.poleDegree_eq_sum {g : X.functionField} (hfin : (Scheme.divSupport g).Finite) :
    strX.poleDegree g = ∑ x ∈ hfin.toFinset, strX.poleCoeff g x :=
  finsum_eq_sum_of_support_subset _ (by
    simpa [Set.Finite.coe_toFinset] using strX.support_poleCoeff_subset g)

lemma Scheme.Hom.zeroDegree_nonneg {g : X.functionField} (hfin : (Scheme.divSupport g).Finite) :
    0 ≤ strX.zeroDegree g := by
  rw [strX.zeroDegree_eq_sum hfin]
  exact Finset.sum_nonneg fun x _ => strX.zeroCoeff_nonneg g x

lemma Scheme.Hom.poleDegree_nonneg {g : X.functionField} (hfin : (Scheme.divSupport g).Finite) :
    0 ≤ strX.poleDegree g := by
  rw [strX.poleDegree_eq_sum hfin]
  exact Finset.sum_nonneg fun x _ => strX.poleCoeff_nonneg g x

lemma Scheme.Hom.divDegree_eq_zeroDegree_sub_poleDegree {g : X.functionField}
    (hfin : (Scheme.divSupport g).Finite) :
    strX.divDegree g = strX.zeroDegree g - strX.poleDegree g := by
  rw [strX.divDegree_eq_sum hfin, strX.zeroDegree_eq_sum hfin, strX.poleDegree_eq_sum hfin,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => strX.divCoeff_eq_zeroCoeff_sub_poleCoeff g x

/-- **THE ZEROS OF `g` ARE THE POLES OF `g⁻¹`** — formal, and the reason the main theorem
can be cut down to `poleDegree_inv_eq_poleDegree` rather than left as a bare `sorry`. -/
lemma Scheme.Hom.zeroCoeff_eq_poleCoeff_inv {g : X.functionField} (hg : g ≠ 0) (x : X) :
    strX.zeroCoeff g x = strX.poleCoeff g⁻¹ x := by
  rw [Scheme.Hom.zeroCoeff, Scheme.Hom.poleCoeff, Scheme.ord_inv hg, neg_neg]

lemma Scheme.Hom.zeroDegree_eq_poleDegree_inv {g : X.functionField} (hg : g ≠ 0) :
    strX.zeroDegree g = strX.poleDegree g⁻¹ :=
  finsum_congr fun x => strX.zeroCoeff_eq_poleCoeff_inv hg x

lemma Scheme.Hom.divCoeff_mul {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) (x : X) :
    strX.divCoeff (f * g) x = strX.divCoeff f x + strX.divCoeff g x := by
  rw [Scheme.Hom.divCoeff, Scheme.Hom.divCoeff, Scheme.Hom.divCoeff,
    Scheme.ord_mul hf hg, add_mul]

lemma Scheme.divSupport_mul_subset {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    Scheme.divSupport (f * g) ⊆ Scheme.divSupport f ∪ Scheme.divSupport g := by
  intro x hx
  rw [Scheme.mem_divSupport_iff, Scheme.ord_mul hf hg] at hx
  by_contra h
  simp only [Set.mem_union, not_or, Scheme.mem_divSupport_iff, ne_eq, not_not] at h
  exact hx (by rw [h.1, h.2]; ring)

/-- The degree of a divisor is additive: `div (f * g) = div f + div g`. -/
lemma Scheme.Hom.divDegree_mul {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfinf : (Scheme.divSupport f).Finite) (hfing : (Scheme.divSupport g).Finite) :
    strX.divDegree (f * g) = strX.divDegree f + strX.divDegree g := by
  classical
  set s : Finset X := hfinf.toFinset ∪ hfing.toFinset with hs
  have hsub : ∀ h : X.functionField, Scheme.divSupport h ⊆ (s : Set X) →
      strX.divDegree h = ∑ x ∈ s, strX.divCoeff h x := fun h hh =>
    finsum_eq_sum_of_support_subset _ ((strX.support_divCoeff_subset h).trans hh)
  have hf' : Scheme.divSupport f ⊆ (s : Set X) := by
    intro x hx; simp [hs, hx]
  have hg' : Scheme.divSupport g ⊆ (s : Set X) := by
    intro x hx; simp [hs, hx]
  have hfg' : Scheme.divSupport (f * g) ⊆ (s : Set X) := fun x hx => by
    rcases Scheme.divSupport_mul_subset hf hg hx with h | h
    · exact hf' h
    · exact hg' h
  rw [hsub _ hfg', hsub _ hf', hsub _ hg', ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => strX.divCoeff_mul hf hg x

lemma Scheme.Hom.divDegree_inv {g : X.functionField} (hg : g ≠ 0)
    (hfin : (Scheme.divSupport g).Finite) (hfinv : (Scheme.divSupport g⁻¹).Finite) :
    strX.divDegree g⁻¹ = -strX.divDegree g := by
  have hginv : g⁻¹ ≠ 0 := inv_ne_zero hg
  have := strX.divDegree_mul hg hginv hfin hfinv
  rw [mul_inv_cancel₀ hg, strX.divDegree_one] at this
  omega

end Basic

section RationalPoints

/-! ### `K`-rational points have residue degree `1`

The counting lemmas below ask for `1 ≤ strX.residueDegree x`, and a consumer holds its
points as SECTIONS `Spec K ⟶ X` of `strX`.  These two lemmas are the bridge, and they also
discharge the one thing that could have made this module's definitions junk rather than
merely open: that `Scheme.Hom.residueDegree` over a base point really is `[κ(x) : K]` and
not `Module.finrank`'s `0`.  At a section it is `1` ON THE NOSE, which no junk value could
produce. -/

/-- **A SPLIT MONOMORPHISM OF RESIDUE FIELDS IS AN ISOMORPHISM** (PROVEN 2026-07-31): if
`κ(strX x) ⟶ κ(x)` admits a retraction then the residue degree at `x` is `1`.

Both maps are field homomorphisms, hence injective; a retraction then forces
`i ∘ r = id` as well, because `r (i (r b)) = r b` and `r` is injective. -/
theorem residueDegree_eq_one_of_retraction (strX : X ⟶ S) (x : X)
    (r : X.residueField x ⟶ S.residueField (strX x))
    (hr : strX.residueFieldMap x ≫ r = 𝟙 _) :
    strX.residueDegree x = 1 := by
  letI : Algebra (S.residueField (strX x)) (X.residueField x) :=
    (strX.residueFieldMap x).hom.toAlgebra
  have hri : ∀ a, r.hom ((strX.residueFieldMap x).hom a) = a := by
    intro a
    have h := congrArg (fun f : S.residueField (strX x) ⟶ S.residueField (strX x) => f.hom a) hr
    simpa using h
  have hsurj : Function.Surjective (strX.residueFieldMap x).hom := fun b =>
    ⟨r.hom b, (RingHom.injective r.hom) (hri (r.hom b))⟩
  have hinj : Function.Injective (strX.residueFieldMap x).hom := RingHom.injective _
  have hbij : Function.Bijective
      (Algebra.ofId (S.residueField (strX x)) (X.residueField x)) := by
    refine ⟨?_, ?_⟩
    · simpa [Algebra.ofId, RingHom.algebraMap_toAlgebra] using hinj
    · simpa [Algebra.ofId, RingHom.algebraMap_toAlgebra] using hsurj
  have e := AlgEquiv.ofBijective
    (Algebra.ofId (S.residueField (strX x)) (X.residueField x)) hbij
  show Module.finrank (S.residueField (strX x)) (X.residueField x) = 1
  rw [← LinearEquiv.finrank_eq e.toLinearEquiv]
  exact Module.finrank_self _

/-- **A SECTION HAS RESIDUE DEGREE `1` AT ITS IMAGE** (PROVEN 2026-07-31 over
`residueDegree_eq_one_of_retraction`).

This is what "`K`-rational" means for the counting lemmas: a `K`-point of `X` over
`Spec K` is a section `s` of `strX`, and `[κ(s y) : K] = 1`.

The proof has to generalise `s ≫ strX` before rewriting it to `𝟙`, because
`(s ≫ strX).residueFieldMap y` has a TYPE that mentions `(s ≫ strX) y` — a direct
`rw [hs]` is not type-correct.  The `key` step is that generalisation. -/
theorem residueDegree_eq_one_of_section {strX : X ⟶ S} {s : S ⟶ X} (hs : s ≫ strX = 𝟙 S)
    (y : S) : strX.residueDegree (s y) = 1 := by
  have hy : (s ≫ strX) y = y := by rw [hs]; rfl
  have key : ∀ (t : S ⟶ S), t = 𝟙 S → ∀ h : t y = y,
      t.residueFieldMap y ≫ (S.residueFieldCongr h).inv = 𝟙 _ := by
    rintro t rfl h
    rw [Scheme.residueFieldMap_id]
    simp
  refine residueDegree_eq_one_of_retraction strX (s y)
    (s.residueFieldMap y ≫ (S.residueFieldCongr hy).inv) ?_
  rw [← Category.assoc, ← Scheme.residueFieldMap_comp]
  exact key (s ≫ strX) hs hy

end RationalPoints

section Bounds

variable [IsIntegral X] [IsLocallyNoetherian X] (strX : X ⟶ S)

/-- **A FINITE SET OF POLES OF RESIDUE DEGREE `≥ 1` IS BOUNDED BY THE POLE DEGREE.**

This is the counting half of `card_relPoint_not_liesIn_le_of_finite_toAffineLine`'s
reduction: a `K`-rational point has `[κ(x) : K] = 1`, and a `K`-rational point of
`X_K ∖ U_K` is a pole of `φ*t`, so `#(X_K ∖ U_K)(K) ≤ deg (φ*t)_∞`.

The two hypotheses are exactly what is used and neither can be dropped: without
`ord < 0` a point contributes `0`, and without `1 ≤ residueDegree` a point of INFINITE
residue degree contributes `0` through `Mathlib`'s `finrank` junk convention. -/
lemma Scheme.Hom.card_le_poleDegree {g : X.functionField} (T : Finset X)
    (hT : ∀ x ∈ T, Scheme.ord g x < 0) (hd : ∀ x ∈ T, 1 ≤ strX.residueDegree x)
    (hfin : (Scheme.divSupport g).Finite) :
    (T.card : ℤ) ≤ strX.poleDegree g := by
  classical
  have hTsub : T ⊆ hfin.toFinset := by
    intro x hx
    exact hfin.mem_toFinset.mpr (by
      rw [Scheme.mem_divSupport_iff]; exact ne_of_lt (hT x hx))
  have hone : ∀ x ∈ T, (1 : ℤ) ≤ strX.poleCoeff g x := by
    intro x hx
    have h1 : (1 : ℤ) ≤ max (-Scheme.ord g x) 0 := by have := hT x hx; omega
    have h2 : (1 : ℤ) ≤ (strX.residueDegree x : ℤ) := by exact_mod_cast hd x hx
    calc (1 : ℤ) = 1 * 1 := by ring
      _ ≤ max (-Scheme.ord g x) 0 * (strX.residueDegree x : ℤ) := by
          exact mul_le_mul h1 h2 zero_le_one (by omega)
      _ = strX.poleCoeff g x := rfl
  calc (T.card : ℤ) = ∑ _x ∈ T, (1 : ℤ) := by simp
    _ ≤ ∑ x ∈ T, strX.poleCoeff g x := Finset.sum_le_sum hone
    _ ≤ ∑ x ∈ hfin.toFinset, strX.poleCoeff g x :=
        Finset.sum_le_sum_of_subset_of_nonneg hTsub
          (fun x _ _ => strX.poleCoeff_nonneg g x)
    _ = strX.poleDegree g := (strX.poleDegree_eq_sum hfin).symm

/-- The mirror image of `card_le_poleDegree`: a finite set of ZEROS of residue degree
`≥ 1` is bounded by the zero degree. -/
lemma Scheme.Hom.card_le_zeroDegree {g : X.functionField} (T : Finset X)
    (hT : ∀ x ∈ T, 0 < Scheme.ord g x) (hd : ∀ x ∈ T, 1 ≤ strX.residueDegree x)
    (hfin : (Scheme.divSupport g).Finite) :
    (T.card : ℤ) ≤ strX.zeroDegree g := by
  classical
  have hTsub : T ⊆ hfin.toFinset := by
    intro x hx
    exact hfin.mem_toFinset.mpr (by
      rw [Scheme.mem_divSupport_iff]; exact ne_of_gt (hT x hx))
  have hone : ∀ x ∈ T, (1 : ℤ) ≤ strX.zeroCoeff g x := by
    intro x hx
    have h1 : (1 : ℤ) ≤ max (Scheme.ord g x) 0 := by have := hT x hx; omega
    have h2 : (1 : ℤ) ≤ (strX.residueDegree x : ℤ) := by exact_mod_cast hd x hx
    calc (1 : ℤ) = 1 * 1 := by ring
      _ ≤ max (Scheme.ord g x) 0 * (strX.residueDegree x : ℤ) := by
          exact mul_le_mul h1 h2 zero_le_one (by omega)
      _ = strX.zeroCoeff g x := rfl
  calc (T.card : ℤ) = ∑ _x ∈ T, (1 : ℤ) := by simp
    _ ≤ ∑ x ∈ T, strX.zeroCoeff g x := Finset.sum_le_sum hone
    _ ≤ ∑ x ∈ hfin.toFinset, strX.zeroCoeff g x :=
        Finset.sum_le_sum_of_subset_of_nonneg hTsub
          (fun x _ _ => strX.zeroCoeff_nonneg g x)
    _ = strX.zeroDegree g := (strX.zeroDegree_eq_sum hfin).symm

end Bounds

section Curve

variable {K : Type u} [Field K] [IsIntegral X] [IsLocallyNoetherian X]

/-- **THE DIVISOR OF A RATIONAL FUNCTION ON A CURVE HAS FINITE SUPPORT** (sorry leaf,
2026-07-31) — the first of the two obligations of `divDegree_eq_zero`, and the one that has
nothing to do with properness.

TRUE, and it is true far more generally than stated here: on ANY Noetherian integral
scheme the set `{x | ord_x g ≠ 0}` is finite-dimensional-ly small — `ord_x g ≠ 0` forces
`coheight x = 1`, and such an `x` is a generic point of a component of the vanishing locus
of the numerator or of the denominator of `g` on some affine chart, of which there are
finitely many because the scheme is Noetherian.  On a QUASI-COMPACT such scheme finitely
many charts suffice, and the total is finite.  Properness is used here only through
quasi-compactness, and smoothness is not used at all.

**THE STATEMENT IS DELIBERATELY NOT `LocallyFinite`.**  `Mathlib`'s `AlgebraicCycle`
asks for a locally finite support, which is the right condition on a general scheme; here
the curve is proper, hence quasi-compact, so locally finite and finite coincide and the
stronger conclusion is the useful one — `Finset.sum` is what every counting lemma above
consumes.

**WHY IT IS A LEAF AND NOT A `have`.**  It is the ONLY thing standing between the
unconditional `finsum` API above and honest statements: `Scheme.Hom.divDegree_mul`,
`divDegree_eq_zeroDegree_sub_poleDegree`, `card_le_poleDegree` and `card_le_zeroDegree` are
all PROVEN, but each takes `(Scheme.divSupport g).Finite` as a hypothesis, and without this
leaf no consumer can discharge it.

**NOT VACUOUS, and this is the sharp point.**  `∑ᶠ` over an infinite support is `0` by
`Mathlib`'s junk convention, so `divDegree_eq_zero` below would be TRUE FOR THE WRONG
REASON on any object where the support were infinite.  This leaf is what rules that out
and what makes the main theorem carry content.  A successor must not "simplify" the
development by deleting it.

**FALSE if `hproper` is dropped and `X` is allowed to be non-quasi-compact**: an infinite
disjoint union of affine lines is smooth of relative dimension `1` over `K` but not
integral, so the honest counterexample needs care — the correct statement of the failure is
that on a NON-quasi-compact integral scheme the support is only locally finite, e.g. `X`
the spectrum of a non-Noetherian valuation ring gives `ord` with infinite support.  The
hypothesis actually consumed is quasi-compactness, and `IsProper` supplies it.

**What a prover should use**: `Scheme.ord_eq_zero_of_coheight_neq_one` cuts the problem
down to codimension-`1` points immediately; `IsLocallyNoetherian` plus quasi-compactness of
a proper scheme gives a finite affine cover by spectra of Noetherian rings; and on
`Spec A` with `A` Noetherian and `g = a / b`, `{P | height P = 1, ord_P g ≠ 0}` is contained
in the minimal primes of `(a)` together with those of `(b)`, finite by
`Ideal.finite_minimalPrimes_of_isNoetherianRing` (or `minimalPrimes.finite_of_isNoetherian`,
whichever name the pin carries). -/
theorem finite_divSupport {strX : X ⟶ Spec (CommRingCat.of K)} (_hproper : IsProper strX)
    (_hcurve : SmoothOfRelativeDimension 1 strX) {g : X.functionField} (_hg : g ≠ 0) :
    (Scheme.divSupport g).Finite :=
  sorry

/-- **A NONZERO RATIONAL FUNCTION ON A SMOOTH PROPER CURVE HAS AS MANY POLES AS `g⁻¹`
DOES** (sorry leaf, 2026-07-31) — equivalently `deg (g)_0 = deg (g)_∞`, and the heart of
this module: the single statement to which the two blocked `X0.lean` leaves named in the
module docstring both reduce.

`deg (g)_0 = deg (g)_∞` is written here as `deg (g⁻¹)_∞ = deg (g)_∞` because
`zeroDegree g = poleDegree g⁻¹` is FORMAL (`Scheme.Hom.zeroDegree_eq_poleDegree_inv`,
PROVEN, from `ord g⁻¹ = −ord g`), so this shape carries all of the content and none of the
bookkeeping.  `divDegree_eq_zero_of_ne_zero` below is the assembly.

## THE SAME MATHEMATICS IS ALREADY CUT TO ONE LEAF ELSEWHERE IN THIS DEVELOPMENT — READ
THIS BEFORE STARTING

`Fermat/FLT/ModularCurve/HyperellipticJacobian.lean` carries an ABSTRACT-PLACES version of
this whole theorem, and it is already decomposed:

* `PlaceData.degOf_divisor_eq_zero` — `Σ_v ord_v(g)·[κ(v) : K] = 0` — is **PROVEN** there;
* it rests on `degOf_poleDivisor_eq_finrank_of_transcendental`:
  `deg (div_∞ g) = [F : K(g)]`, Stichtenoth I.4.11, "the single deep node of the whole
  Picard layer" in that file's own words.  **That name is a moving target, so cite the
  MATHEMATICS, not the name**: on `main` at `5b621e59` it is itself the leaf; on `merger`
  as of 2026-07-31 it is PROVEN by `le_antisymm` over two fresh leaves,
  `degOf_poleDivisor_le_finrank_of_transcendental` (weak approximation) and
  `finrank_le_degOf_poleDivisor_of_transcendental` (Riemann spaces).  Check the tree before
  quoting a count;
* the bookkeeping this leaf's shape performs — `div = div_0 − div_∞`,
  `div_0 g = div_∞ g⁻¹`, `K(g) = K(g⁻¹)`, and the algebraic/constant case — is likewise
  already Lean there (`divisor_eq_zeroDivisor_sub_poleDivisor`, `poleDivisor_inv`,
  `adjoin_inv_eq`, `poleDivisor_eq_zero_of_isAlgebraic`).

So there is exactly ONE open mathematical node behind both formulations, and it is
Stichtenoth I.4.11.  Two consequences, both operational:

1. **Do not re-prove I.4.11 here.**  If it closes over there, the work left here is a
   BRIDGE — scheme-theoretic closed points of `X` versus the abstract `Places` of
   `X.functionField` — not a proof.
2. `HyperellipticJacobian.lean`'s `PlaceSystem` (as opposed to `PlaceData`) is already a
   general function-field-of-one-variable interface: `ord_injective` and `ord_complete` say
   `Places` is EXACTLY the set of normalised `K`-trivial discrete valuations of `F`, and
   `ord_finite` is `finite_divSupport`'s analogue.  `PlaceData.toPlaceSystem` exists on
   `merger` as of 2026-07-31, so the abstraction is live.  The degree theorem there is
   stated over `PlaceData` only because that is where `degOf` was written; its proof uses
   nothing about the sextic (`_hsep` is already underscored in `degOf_divisor_eq_zero`).
   **Hoisting it from `PlaceData` to `PlaceSystem`, and then building the bridge
   "smooth proper curve `X/K` ⟹ `PlaceSystem K X.functionField` with
   `ord = Scheme.ord` and `degOf = residueDegree`", closes this leaf with no new
   mathematics.**  That is the cheapest route and it is why this audit is longer than the
   statement.

   Where properness enters on that route, and it is worth knowing before starting: the one
   `PlaceSystem` axiom that is NOT a local fact about `X` is `ord_complete` — every
   normalised `K`-trivial discrete valuation of `X.functionField` is the order at a point
   of `X`.  That is the valuative criterion, i.e. exactly `IsProper strX`, and
   `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean` plus
   `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean` are where the machinery sits.
   `ord_surjective` and `ord_add` come from the stalks being DVRs
   (`isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one`, PROVEN there), and
   `ord_finite` is `finite_divSupport` above.

The audit below is the leaf's own audit and stands on its own; it was written before the
cross-check above was run, and nothing in it is changed by it.

## FALSITY AUDIT

`∑_x ord_x(g) · [κ(x) : K] = 0`: a nonzero rational function on a complete curve has as
many zeros as poles, counted with multiplicity and with residue degree.

TRUE and classical — Hartshorne II.6.10 (stated there for a nonsingular projective curve
over an algebraically closed field, but the proof is the degree formula for a finite
morphism and needs neither), Stichtenoth I.4.11, Fulton *Algebraic Curves* §8, and the
Stacks project's *Algebraic Curves* chapter, which proves it for an arbitrary proper curve
over a field with `ord` defined by length, i.e. with no normality hypothesis at all.

**NOT VACUOUS, with an explicit witness.**  `X = ℙ¹_ℚ`, `g = t`: `div t = [0] − [∞]`, both
points `ℚ`-rational, degree `1 · 1 − 1 · 1 = 0`.  A witness where the residue degrees are
NOT all `1`, which is the case that distinguishes this statement from a naive point count:
`X = ℙ¹_ℚ`, `g = (t² + 1) / t`.  The zero divisor is the single closed point cut out by
`t² + 1`, with residue field `ℚ(i)`, so `deg (g)_0 = 1 · 2 = 2`; the pole divisor is
`[0] + [∞]`, of degree `1 · 1 + 1 · 1 = 2`.  So the theorem is `2 − 2 = 0` and the residue
degrees are load-bearing in it — a version weighting every point by `1` is FALSE on this
very example.

**`hproper` IS LOAD-BEARING AND THE LEAF IS FALSE WITHOUT IT**, with the smallest possible
witness: `X = 𝔸¹_ℚ = Spec ℚ[t]` is integral, Noetherian and smooth of relative dimension
`1` over `ℚ`, and `g = t` has `div t = [0]`, of degree `1 ≠ 0`.  Every hypothesis except
`IsProper` holds.  So a successor must not "generalise" this leaf by dropping properness,
and a consumer that has only an affine curve cannot use it.

**`hcurve` IS *NOT* MATHEMATICALLY LOAD-BEARING, AND IS CARRIED ON PURPOSE.**  The
statement is true for an arbitrary proper INTEGRAL curve over a field, singularities and
all, because `Mathlib`'s `Scheme.ord` is built from `Ring.ordFrac` at a Noetherian local
ring of Krull dimension `≤ 1` — the length-theoretic order, which is exactly the one the
general theorem is stated for.  `SmoothOfRelativeDimension 1` is carried because

1. both `X0.lean` consumers have it in hand, so it costs them nothing;
2. it supplies DVR stalks through
   `isDiscreteValuationRing_stalk_of_smoothOfRelativeDimension_one`, PROVEN in
   `Fermat/FLT/Mathlib/AlgebraicGeometry/CurveExtension.lean`, which is what makes `ord` an
   honest discrete valuation and what every route below actually consumes;
3. it is what pins the DIMENSION to `1`, and the dimension hypothesis cannot be dropped —
   see the next paragraph.

Removing it is a STRENGTHENING of this leaf, not a repair of it, and a successor who
removes it should say so rather than silently restate.

**DROPPING THE DIMENSION HYPOTHESIS MAKES THE LEAF VACUOUS, NOT FALSE — and that is the
trap in this module.**  On a proper integral scheme of dimension `≥ 2` the codimension-`1`
points have residue fields of positive transcendence degree over `K`, so
`Scheme.Hom.residueDegree` is `Module.finrank` of an INFINITE extension, which is `0` by
`Mathlib`'s junk convention.  Every `divCoeff` is then `0` and `divDegree` is `0` for
trivial reasons.  A "generalisation" of this leaf to arbitrary proper `X` would therefore
compile, be true, and prove nothing.  The honest higher-dimensional statement is
`deg(div g · H^{n−1}) = 0` for an ample `H`, which is a different theorem needing
intersection theory the pin does not have.

**`g ≠ 0` IS NOT NEEDED FOR TRUTH**, and that is why the consumer-facing
`divDegree_eq_zero` below drops it: `Scheme.ord_zero` gives `ord 0 = 0`, so
`divDegree strX 0 = 0` outright.  It is kept HERE because every proof route divides by `g`,
and a prover should not have to carry the degenerate branch through the geometry.

**THE FINITENESS CAVEAT.**  `∑ᶠ` over an infinite support is `0`, so this statement would
be true for the wrong reason if `divSupport g` were infinite.  It is not — that is
`finite_divSupport` above — but the two leaves are genuinely independent and a prover of
this one may assume the other.

## ROUTE 1 — THE FUNDAMENTAL IDENTITY.  This is the one to try first, because its
arithmetic core ALREADY EXISTS IN THE PIN.

For `g` nonconstant, write `B = K[t]` mapping to `X.functionField` by `t ↦ g`, and let `A`
be the integral closure of `B` in `X.functionField`.  Then:

* `A` is a Dedekind domain, module-finite over `B`, and `Frac A = X.functionField`;
* the primes of `A` over `(t)` are exactly the points where `g` vanishes, with
  `ord_P(g) = e_P` (the ramification index) and `[κ(P) : K] = f_P` (the inertia degree,
  since `κ((t)) = K[t]/(t) = K`);
* **`Ideal.sum_ramification_inertia`** (`Mathlib/NumberTheory/RamificationInertia/Basic.lean`,
  PROVEN in the pin) gives `∑_P e_P f_P = [Frac A : Frac B]`, i.e.

      deg (g)_0 = [K(X) : K(g)].

* Applying the same with `g⁻¹` in place of `g` gives `deg (g)_∞ = [K(X) : K(g⁻¹)]`, and
  `K(g) = K(g⁻¹)` as subfields of `K(X)`, so the two degrees agree and their difference is
  `0`.

What this route still needs, and it is the whole of the remaining work: the identification
of `Spec A` with the open subscheme of `X` on which `g` is regular.  That is where
properness enters — it is what makes `X` minus the poles of `g` AFFINE with coordinate ring
exactly `A` — and it is the step to attack.  `Mathlib/AlgebraicGeometry/Normalization.lean`
(`Scheme.Hom.normalization`, `fromNormalization` is `IsIntegralHom`, `normalizationDesc` its
universal property) and `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean` are the two
files that speak about this, and
`Fermat/FLT/Mathlib/AlgebraicGeometry/CurveAffineComplement.lean`
(`isAffineOpen_compl_singleton_of_isSmoothProperCurve`, PROVEN) already does the
one-point case of exactly this affineness statement in this development.

## ROUTE 2 — PROPER PUSHFORWARD OF CYCLES.  Cleaner, and further from the pin.

`deg` is the pushforward of the cycle `div g` along `strX : X ⟶ Spec K` followed by the
identification of a cycle on a point with an integer, and the statement is that proper
pushforward kills principal divisors (Fulton, *Intersection Theory*, Prop. 1.4).
`Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean` has `AlgebraicCycle.map` — the
pushforward — but NOTHING about degrees or about principal cycles, so this route would have
to build the whole comparison first.  Recorded so that a successor does not mistake the
existence of `AlgebraicCycle.map` for the existence of this theorem.

## THE CHECK THAT WOULD REFUTE THIS VERDICT

A proper smooth integral curve over a field carrying a rational function with
`deg (g)_0 ≠ deg (g)_∞`.  There is none; but the CHEAP thing to check first, and the thing
that would refute the *formalisation* rather than the mathematics, is whether
`Scheme.Hom.residueDegree` really is `[κ(x) : K]` at a closed point of `X` over
`Spec K` — i.e. whether `(Spec (CommRingCat.of K)).residueField (strX x)` is `K` and not
something with an unexpected junk value. -/
theorem poleDegree_inv_eq_poleDegree {strX : X ⟶ Spec (CommRingCat.of K)}
    (_hproper : IsProper strX) (_hcurve : SmoothOfRelativeDimension 1 strX)
    {g : X.functionField} (_hg : g ≠ 0) :
    strX.poleDegree g⁻¹ = strX.poleDegree g :=
  sorry

/-- **THE DEGREE OF A PRINCIPAL DIVISOR ON A SMOOTH PROPER CURVE IS ZERO** (PROVEN
2026-07-31 over `poleDegree_inv_eq_poleDegree` and `finite_divSupport`, along the
`div = div_0 − div_∞` / `div_0 g = div_∞ g⁻¹` seam — the same seam
`HyperellipticJacobian.lean`'s `degOf_divisor_eq_zero` uses).

The whole of the content is in `poleDegree_inv_eq_poleDegree`; read its audit. -/
theorem divDegree_eq_zero_of_ne_zero {strX : X ⟶ Spec (CommRingCat.of K)}
    (hproper : IsProper strX) (hcurve : SmoothOfRelativeDimension 1 strX)
    {g : X.functionField} (hg : g ≠ 0) :
    strX.divDegree g = 0 := by
  have hfin := finite_divSupport hproper hcurve hg
  rw [strX.divDegree_eq_zeroDegree_sub_poleDegree hfin,
    strX.zeroDegree_eq_poleDegree_inv hg,
    poleDegree_inv_eq_poleDegree hproper hcurve hg, sub_self]

/-- **THE DEGREE OF A PRINCIPAL DIVISOR ON A SMOOTH PROPER CURVE IS ZERO**, with the
degenerate `g = 0` branch absorbed (PROVEN 2026-07-31 over
`divDegree_eq_zero_of_ne_zero`).  This is the form consumers should cite. -/
theorem divDegree_eq_zero {strX : X ⟶ Spec (CommRingCat.of K)} (hproper : IsProper strX)
    (hcurve : SmoothOfRelativeDimension 1 strX) (g : X.functionField) :
    strX.divDegree g = 0 := by
  by_cases hg : g = 0
  · subst hg; simp
  · exact divDegree_eq_zero_of_ne_zero hproper hcurve hg

/-- **ZEROS = POLES**: on a smooth proper curve the zero divisor and the pole divisor of a
nonzero rational function have the same degree (PROVEN 2026-07-31 over
`divDegree_eq_zero` and `finite_divSupport`).

This is the form `hasDoubleCoverOfAffineLine_of_iso_sectionIdeal` consumes: the fibre of
`f` over a `K`-point `c` is the zero divisor of `f − c`, and its degree is
`deg (f)_∞`, which is `2`. -/
theorem zeroDegree_eq_poleDegree {strX : X ⟶ Spec (CommRingCat.of K)} (hproper : IsProper strX)
    (hcurve : SmoothOfRelativeDimension 1 strX) {g : X.functionField} (hg : g ≠ 0) :
    strX.zeroDegree g = strX.poleDegree g := by
  have hfin := finite_divSupport hproper hcurve hg
  have h := strX.divDegree_eq_zeroDegree_sub_poleDegree hfin
  rw [divDegree_eq_zero hproper hcurve g] at h
  omega

/-- **A `K`-RATIONAL POLE SET IS BOUNDED BY THE ZERO DEGREE** (PROVEN 2026-07-31 over
`card_le_poleDegree`, `zeroDegree_eq_poleDegree` and `finite_divSupport`).

This is the exact shape `card_relPoint_not_liesIn_le_of_finite_toAffineLine` needs.  There,
`g = φ*t` for the finite `φ : U ⟶ 𝔸¹`, the points of `X_K ∖ U_K` are `K`-rational poles of
`g`, and `deg (g)_0 ≤ 2` because `φ` has degree at most `2` — giving
`#(X_K ∖ U_K)(K) ≤ 2` with no projective line anywhere.

The residue-degree hypothesis `hd` is what "`K`-rational" means: `[κ(x) : K] = 1`, and it is
discharged by `residueDegree_eq_one_of_section` above whenever the points of `T` are images
of sections of `strX`, which is how every consumer holds them.  It cannot be weakened to
"`x` is a closed point": a closed point of residue degree `2` costs `2` against the zero
degree, and the count would be off by a factor of two. -/
theorem card_le_zeroDegree_of_poles {strX : X ⟶ Spec (CommRingCat.of K)} (hproper : IsProper strX)
    (hcurve : SmoothOfRelativeDimension 1 strX) {g : X.functionField} (hg : g ≠ 0) (T : Finset X)
    (hT : ∀ x ∈ T, Scheme.ord g x < 0) (hd : ∀ x ∈ T, 1 ≤ strX.residueDegree x) :
    (T.card : ℤ) ≤ strX.zeroDegree g := by
  have hfin := finite_divSupport hproper hcurve hg
  have h := strX.card_le_poleDegree T hT hd hfin
  rw [zeroDegree_eq_poleDegree hproper hcurve hg]
  exact h

end Curve

end AlgebraicGeometry
