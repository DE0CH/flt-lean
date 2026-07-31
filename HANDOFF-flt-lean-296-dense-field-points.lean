/-
HANDOFF — flt-lean-296, 2026-07-31.  VERIFIED GREEN, NOT WIRED IN.

`lake env lean` on this file returns clean (imports mathlib ONLY — no `Fermat`
module is needed, which is the whole point).  It is parked at the repository
root rather than under `Fermat/` on purpose: a `.lean` file under `Fermat/`
that nothing imports is compiled by nobody and is invisible to `lake build`,
to the `declaration uses 'sorry'` warning set and to every frontier scan
(CLAUDE.md's fourth invisibility class), and three declarations with no
consumer would be free-floating code, which this project forbids.  Move it
into `Fermat/FLT/Mathlib/AlgebraicGeometry/` in the SAME commit as its first
consumer.

## WHAT IT IS FOR

`ModularCurve/X0.lean`'s `exists_commutingHeckeAlbaneseFamily_values` — the
single live leaf of the Hecke-commutation cluster, with two consumers — carries
a three-step proof plan in its docstring.  Step 2 is:

> *THE REAL GAP IS DENSITY OF THE MODULI POINTS IN `X`, and it is one clean
> statement*: two morphisms `X ⟶ J` over `SpecQ` agreeing at every
> `jY ∘ classify d`, `d : Gamma0Datum N ℚ̄`, are equal.

That plan lists the PROJECT-side inputs and does not know that **mathlib
already carries the engine**, in a 2026 file this development has never
imported:

    Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean
      AlgebraicGeometry.ext_of_apply_eq          -- over an ALG. CLOSED base
      AlgebraicGeometry.pointEquivClosedPoint    -- K-points ≃ closed points
    Mathlib/AlgebraicGeometry/Morphisms/UnderlyingMap.lean (etc.)
      AlgebraicGeometry.ext_of_fromSpecResidueField_eq   -- over ANY base
      AlgebraicGeometry.ext_of_isDominant_of_isSeparated

`ext_of_apply_eq` is the statement wanted, but its base must be algebraically
closed, so using it over `SpecQ` costs a base change to `ℚ̄` and a descent.
**`ext_of_fromSpecResidueField_eq` is stated over an ARBITRARY base `Z`** and
needs no base change at all — it asks for agreement after
`X.fromSpecResidueField x`, not after a `K`-point.  The three lemmas below are
exactly the bridge from `K`-points to residue-field points, so that the
arbitrary-base lemma can be driven by the `ℚ̄`-points this development actually
has.  Checked at our pin (`a3364fa`) on 2026-07-31: all four mathlib names
above exist with the signatures used here.

## WHAT IS STILL OWED, and it is the only project-shaped part

`ext_of_dense_fieldPoints` asks the caller to produce, at every point of the
dense set, a `K`-point lying over it.  For `X_0(N)` that is two steps:

1. **a `ℚ̄`-point over every CLOSED point of `Y`.**  `Y ⟶ SpecQ` is locally of
   finite type, so `JacobsonSpace Y` (`LocallyOfFiniteType.jacobsonSpace`, with
   `JacobsonSpace (Spec ℚ)` from `IsJacobsonRing ℚ`), and at a closed point
   `isClosed_singleton_iff_locallyOfFiniteType` makes `Y.fromSpecResidueField x`
   locally of finite type; so `κ(x)` is a finite-type `ℚ`-algebra AND a field,
   hence finite over `ℚ` by Zariski's lemma
   (`finite_of_finite_type_of_isJacobsonRing`, `@[stacks 0CY7]`), hence
   algebraic, hence `IsAlgClosed.lift` gives `κ(x) →ₐ[ℚ] ℚ̄` and
   `(Scheme.SpecToEquivOfField ℚ̄ Y).symm ⟨x, ·⟩` is the point.  The fiddly part
   is the `ℚ`-ALGEBRA structure on `κ(x)`: take it from
   `Scheme.Hom.residueFieldMap` of the structure morphism and nothing else, or
   the `IsScalarTower` needed by `IsAlgClosed.lift` will not synthesize.
2. **density of the closed points of `Y` in `X`.**  `JacobsonSpace.closure_‑
   inter_closedPoints_eq_closure` (needs `IsLocallyClosed (Set.range jY.base)`,
   which is free — it is OPEN) reduces it to `Dense (Set.range jY.base)`, i.e.
   to `Y` dense in `X`.  `X` is irreducible (smooth + geometrically connected
   over a field) and `Y` is a nonempty open of it — nonempty because
   `h.coarse.classify (specAlgClos ℚ) d₀` is a point of it, which is where the
   `d₀ : Gamma0Datum N ℚ̄` hypothesis of `_values` is spent.  `IsReduced X` is
   `isReduced_of_smooth_over_field_stalkwise` (`Modularity/TateModule.lean`) or
   the smooth-implies-reduced route already in `Fermat/FLT/Mathlib/`.

Then `IsCoarseModuliY0.exists_gamma0Datum_of_algClosPoint` (PROVEN, X0.lean
~16966) turns each `ℚ̄`-point of `Y` into a `classify d`, which is what makes
the hypothesis of step 2 usable.

## WHAT THIS DOES NOT CLOSE

Step 3 of that plan — the double sum over pairs `(D, D')` of a cyclic
`ℓ`-subgroup and a cyclic `ℓ'`-subgroup, and its symmetry — is untouched, and
it needs the enumeration of the cyclic `ℓ`-subgroups by `Γ₀`-isogenies, i.e.
the correspondence scheme `X₀(N, ℓ)`.  Do NOT read this file as reducing
`_values` to density: without an enumeration the recipe is a `∀` over
decomposition data that may be UNINHABITED at a given datum, and then it
constrains nothing there.  That is the same "intermediate regime" the
`_values` docstring's own falsity audit describes.
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

open AlgebraicGeometry CategoryTheory

universe u

/-- **`Spec` of a field extension is DOMINANT** (PROVEN).

Both spectra are single points, so the range is nonempty in a subsingleton
space.  This is the one instance `ext_of_isDominant_of_isSeparated` needs
below and which typeclass search does not find: there is no
`IsDominant (Spec.map φ)` instance for a map of fields at this pin. -/
theorem isDominant_specMap_residueField {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
    (φ : X.residueField x ⟶ CommRingCat.of K) : IsDominant (Spec.map φ) := by
  haveI : Subsingleton (Spec (X.residueField x)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (X.residueField x)))
  haveI : Nonempty (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum K))
  rw [isDominant_iff, DenseRange]
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun y => ?_)
  exact subset_closure ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩

/-- **A `K`-POINT SEES AS MUCH AS ITS RESIDUE-FIELD POINT** (PROVEN) — if two
morphisms into a separated `Y` agree after a `K`-point `p`, they agree after
`X.fromSpecResidueField` at the image of `p`.

This is the bridge that makes `ext_of_fromSpecResidueField_eq` — which is
stated over an ARBITRARY base — usable from `K`-points, and so removes the base
change to `ℚ̄` that `ext_of_apply_eq` would otherwise force.

`Scheme.SpecToEquivOfField` factors `p` as `Spec.map φ ≫ fromSpecResidueField x`
(**on the nose — that direction of the equivalence is `rfl`**), and `Spec.map φ`
is dominant by the lemma above, so `ext_of_isDominant_of_isSeparated` cancels
it.  Note `Spec κ(x)` is reduced for free, so no hypothesis on `X` is used
here; `IsReduced X` is needed only by the caller below. -/
theorem fromSpecResidueField_comp_eq_of_fieldPoint {X Y Z : Scheme.{u}} {f g : X ⟶ Y}
    (i : Y ⟶ Z) [IsSeparated i] (hfg : f ≫ i = g ≫ i)
    {K : Type u} [Field K] (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ f = p ≫ g) :
    X.fromSpecResidueField ((Scheme.SpecToEquivOfField K X p).1) ≫ f
      = X.fromSpecResidueField ((Scheme.SpecToEquivOfField K X p).1) ≫ g := by
  have hp' : p = Spec.map (Scheme.SpecToEquivOfField K X p).2
      ≫ X.fromSpecResidueField (Scheme.SpecToEquivOfField K X p).1 := by
    conv_lhs => rw [← (Scheme.SpecToEquivOfField K X).symm_apply_apply p]
    rfl
  haveI := isDominant_specMap_residueField (Scheme.SpecToEquivOfField K X p).2
  refine ext_of_isDominant_of_isSeparated i ?_ (Spec.map (Scheme.SpecToEquivOfField K X p).2) ?_
  · rw [Category.assoc, Category.assoc, hfg]
  · rw [← Category.assoc, ← Category.assoc, ← hp']; exact hp

/-- **TWO MORPHISMS AGREEING AT A DENSE SET OF `K`-POINTS ARE EQUAL** (PROVEN),
over an ARBITRARY base and with no hypothesis that the base be algebraically
closed — `K` itself need not even be algebraically closed.

`X` reduced and `i` separated are exactly the hypotheses of
`ext_of_fromSpecResidueField_eq`, which this drives.  The caller owes, at each
point of the dense set, a `K`-point lying over it; for a finite-type scheme
over a field with `K` an algebraic closure of that field, that is Zariski's
lemma plus `IsAlgClosed.lift` — see the header. -/
theorem ext_of_dense_fieldPoints {X Y Z : Scheme.{u}} {f g : X ⟶ Y} (i : Y ⟶ Z)
    [IsSeparated i] [IsReduced X] {K : Type u} [Field K]
    (S : Set X) (hS : Dense S)
    (H : ∀ x ∈ S, ∃ p : Spec (CommRingCat.of K) ⟶ X,
      (Scheme.SpecToEquivOfField K X p).1 = x ∧ p ≫ f = p ≫ g)
    (hfg : f ≫ i = g ≫ i) : f = g := by
  refine ext_of_fromSpecResidueField_eq f g i S hS ?_ hfg
  intro x hx
  obtain ⟨p, hpx, hp⟩ := H x hx
  subst hpx
  exact fromSpecResidueField_comp_eq_of_fieldPoint i hfg p hp
