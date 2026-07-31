/-
Mathlib/AlgebraicGeometry/BirationalBaseChange.lean — own work for the Fermat
project (not vendored).

# Birationality ASCENDS along a base change with irreducible total spaces

`Mathlib`'s `Scheme.BirationalOver` (in `Mathlib/AlgebraicGeometry/Birational/`)
carries `refl`, `symm`, `trans`, `isRationalOver`, `Opens.birationalOver_of_dense`
and `Hom.birationalOver`, and **no base-change lemma at all** — checked 2026-07-30
and again 2026-07-31 by reading the whole directory.  This file supplies the one
that is missing:

* `Scheme.BirationalOver.pullback_snd` — if `X` and `Y` are `S`-birational, `g : T ⟶ S`
  is surjective and both `X ×_S T` and `Y ×_S T` are irreducible, then `X ×_S T` and
  `Y ×_S T` are `T`-birational.

The three hypotheses are all needed and none of them is decoration:

* **surjectivity of `g`** is what keeps the base-changed dense open NONEMPTY.  Without
  it the statement is false for a silly reason: take `T = ∅`, `X` a curve and `Y` a
  point — every scheme over `∅` is `∅`, so that case is in fact fine, but take instead
  `S = S₁ ⊔ S₂`, `T = S₁`, `X = Y = S` with the birational structure supported on `S₂`;
  the base change to `S₁` is then a partial isomorphism with EMPTY source, which is not
  dense.
* **irreducibility of the two base changes** is what turns "nonempty open" back into
  "dense open".  It is the place where geometric integrality of the fibres enters at
  every call site, and it cannot be dropped: over a non-irreducible `X ×_S T` a dense
  open of `X` can base change to an open missing a whole component.

## The shape of the proof, and why it never touches `Opens`

The three-line observation that makes this cheap is that `BirationalOver sX sY` is
*equivalent* to the existence of a single scheme `W` with two DOMINANT OPEN IMMERSIONS
`a : W ⟶ X`, `b : W ⟶ Y` satisfying `b ≫ sY = a ≫ sX` — that is
`Scheme.birationalOver_of_common_open` and `Scheme.BirationalOver.exists_common_open`
below, each of which is four lines over `Mathlib`'s `Scheme.Hom.birationalOver` and
`Scheme.Opens.isDominant_ι`.  In that presentation the base change is just
`pullback.lift`, and the two facts to check about it are

* it is an open immersion — because it IS the base change of `a`, which
  `pullbackRightPullbackFstIso` identifies on the nose (`isOpenImmersion_baseChangeHom`);
* it is dominant — because its source is nonempty and its target is irreducible
  (`isDominant_of_isOpenImmersion_of_nonempty`).

No `Scheme.Opens`, no `Scheme.PartialIso`, no density argument about subsets of `X ×_S T`
is ever written down.  Working with `PartialIso.source`/`target` directly — the shape the
consumer's docstring predicted this would need — costs the identification of `f⁻¹ᵁ U` with
a pullback, which is exactly what the `W`-presentation deletes.

## Where this is used

`Fermat/FLT/ModularCurve/X1.lean`'s `hasNoFibreAffineLine_of_notGeometricallyRational`,
whose whole content is this ascent: a nonconstant `𝔸¹_{K'} ⟶ X_{K'}` makes `X_{K'}`
rational over `K'`, and the hypothesis it must contradict is about `X_L` for `L` an
algebraic closure.

**THIS FILE IS SORRY-FREE.**
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

@[expose] public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {S T X Y W : Scheme.{u}}

/-! ### A nonempty open of an irreducible scheme is dominant -/

/-- **A nonempty open immersion into an irreducible scheme is dominant.**  Pure topology:
an open set meets every nonempty open of a preirreducible space, and `dense_iff_inter_open`
is exactly that characterisation of density. -/
theorem isDominant_of_isOpenImmersion_of_nonempty (m : X ⟶ Y) [IsOpenImmersion m]
    [Nonempty X] [IrreducibleSpace Y] : IsDominant m :=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace m.base m.isOpenEmbedding.isOpenMap⟩

/-! ### `BirationalOver` through a common dominant open -/

/-- **A common dominant open makes two `S`-schemes `S`-birational.** -/
theorem Scheme.birationalOver_of_common_open {sX : X ⟶ S} {sY : Y ⟶ S}
    (a : W ⟶ X) (b : W ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b]
    [IsDominant a] [IsDominant b] (hab : b ≫ sY = a ≫ sX) :
    Scheme.BirationalOver sX sY :=
  (Scheme.Hom.birationalOver a sX (a ≫ sX) rfl).symm.trans
    (Scheme.Hom.birationalOver b sY (a ≫ sX) hab)

/-- **The converse: an `S`-birational pair has a common dominant open.**  The witness is
the source of the partial isomorphism, mapped in by `ι` on one side and by the partial
isomorphism followed by `ι` on the other. -/
theorem Scheme.BirationalOver.exists_common_open {sX : X ⟶ S} {sY : Y ⟶ S}
    (h : Scheme.BirationalOver sX sY) :
    ∃ (W : Scheme.{u}) (a : W ⟶ X) (b : W ⟶ Y), IsOpenImmersion a ∧ IsOpenImmersion b ∧
      IsDominant a ∧ IsDominant b ∧ b ≫ sY = a ≫ sX := by
  obtain ⟨f, hf⟩ := h
  haveI : IsDominant f.target.ι := Opens.isDominant_ι f.dense_target
  exact ⟨f.source.toScheme, f.source.ι, f.iso.hom ≫ f.target.ι, inferInstance, inferInstance,
    Opens.isDominant_ι f.dense_source, inferInstance, by rw [Category.assoc]; exact hf⟩

/-- **`BirationalOver` transports along isomorphisms over the base.** -/
theorem Scheme.BirationalOver.of_isoOver {X' Y' : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S}
    {sX' : X' ⟶ S} {sY' : Y' ⟶ S} (eX : X' ≅ X) (eY : Y' ≅ Y)
    (hX : eX.hom ≫ sX = sX') (hY : eY.hom ≫ sY = sY')
    (h : Scheme.BirationalOver sX sY) : Scheme.BirationalOver sX' sY' := by
  obtain ⟨W, a, b, hoa, hob, hda, hdb, hab⟩ := h.exists_common_open
  haveI := hoa; haveI := hob; haveI := hda; haveI := hdb
  refine Scheme.birationalOver_of_common_open (a ≫ eX.inv) (b ≫ eY.inv) ?_
  rw [← hX, ← hY, Category.assoc, Category.assoc, ← Category.assoc eY.inv, eY.inv_hom_id,
    Category.id_comp, ← Category.assoc eX.inv, eX.inv_hom_id, Category.id_comp]
  exact hab

/-! ### Base change of a map over the base -/

/-- **The base change of `a : W ⟶ X` along `g : T ⟶ S`**, where `W` is given its structure
morphism through `a`.  Stated with `sW` a variable and `ha : sW = a ≫ sX` a hypothesis
rather than with `a ≫ sX` literally, because the consumer applies it twice to the SAME
source `pullback sW g` with two different `(a, sX)`. -/
noncomputable def baseChangeHom {a : W ⟶ X} {sX : X ⟶ S} {sW : W ⟶ S}
    (ha : sW = a ≫ sX) (g : T ⟶ S) : pullback sW g ⟶ pullback sX g :=
  pullback.lift (pullback.fst sW g ≫ a) (pullback.snd sW g)
    (by rw [Category.assoc, ← ha]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem baseChangeHom_fst {a : W ⟶ X} {sX : X ⟶ S} {sW : W ⟶ S}
    (ha : sW = a ≫ sX) (g : T ⟶ S) :
    baseChangeHom ha g ≫ pullback.fst sX g = pullback.fst sW g ≫ a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeHom_snd {a : W ⟶ X} {sX : X ⟶ S} {sW : W ⟶ S}
    (ha : sW = a ≫ sX) (g : T ⟶ S) :
    baseChangeHom ha g ≫ pullback.snd sX g = pullback.snd sW g :=
  pullback.lift_snd _ _ _

/-- **The base change of an open immersion is an open immersion** — `baseChangeHom` really
is the base change of `a`, which `pullbackRightPullbackFstIso` says on the nose. -/
instance isOpenImmersion_baseChangeHom {a : W ⟶ X} [IsOpenImmersion a] {sX : X ⟶ S}
    {sW : W ⟶ S} (ha : sW = a ≫ sX) (g : T ⟶ S) : IsOpenImmersion (baseChangeHom ha g) := by
  subst ha
  have h : baseChangeHom (rfl : a ≫ sX = a ≫ sX) g
      = (pullbackRightPullbackFstIso sX g a).inv ≫ pullback.snd a (pullback.fst sX g) := by
    apply pullback.hom_ext <;> simp
  rw [h]
  infer_instance

/-! ### The ascent -/

/-- **BIRATIONALITY ASCENDS ALONG A SURJECTIVE BASE CHANGE WITH IRREDUCIBLE TOTAL SPACES.**

This is the lemma `Mathlib` does not have.  See the module docstring for why each of the
three hypotheses is load-bearing. -/
theorem Scheme.BirationalOver.pullback_snd {sX : X ⟶ S} {sY : Y ⟶ S} (g : T ⟶ S)
    (hg : Surjective g) (h : Scheme.BirationalOver sX sY)
    [IrreducibleSpace ↥(pullback sX g)] [IrreducibleSpace ↥(pullback sY g)] :
    Scheme.BirationalOver (pullback.snd sX g) (pullback.snd sY g) := by
  obtain ⟨W, a, b, hoa, hob, hda, hdb, hab⟩ := h.exists_common_open
  haveI := hoa; haveI := hob; haveI := hda; haveI := hdb
  haveI : Nonempty X :=
    Nonempty.map (pullback.fst sX g).base (inferInstanceAs (Nonempty ↥(pullback sX g)))
  haveI : Nonempty ↥W := (Scheme.Hom.denseRange a).nonempty
  haveI hsurj : Surjective (pullback.fst (a ≫ sX) g) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ hg
  haveI : Nonempty ↥(pullback (a ≫ sX) g) := by
    obtain ⟨w⟩ := ‹Nonempty W›
    obtain ⟨p, -⟩ := hsurj.surj w
    exact ⟨p⟩
  haveI : IsDominant (baseChangeHom (rfl : a ≫ sX = a ≫ sX) g) :=
    isDominant_of_isOpenImmersion_of_nonempty _
  haveI : IsDominant (baseChangeHom hab.symm g) :=
    isDominant_of_isOpenImmersion_of_nonempty _
  exact Scheme.birationalOver_of_common_open (baseChangeHom (rfl : a ≫ sX = a ≫ sX) g)
    (baseChangeHom hab.symm g) (by simp)

end AlgebraicGeometry
