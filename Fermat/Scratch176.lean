/-
SCRATCH — delete before committing.  Develops the braiding-free monoidal
argument for `exists_trivialization_of_modTensor_trivial`.
-/
module

public import Fermat.FLT.ModularCurve.RelativePicard

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open TopologicalSpace MonoidalCategory Opposite

namespace Fermat

variable {Z : Scheme.{u}}

/-- Local copy of `AmpleSheaf.lean`'s `modTensorMap`, so the scratch can be
developed without elaborating that file. -/
noncomputable def modTensorMap' {L L' M M' : Z.Modules}
    (e : L ⟶ L') (e' : M ⟶ M') : modTensor L M ⟶ modTensor L' M' :=
  (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map
    (MonoidalCategory.tensorHom
      ((SheafOfModules.forget _).map e) ((SheafOfModules.forget _).map e'))

/-- `modTensorMap` preserves identities. -/
lemma modTensorMap'_id (L M : Z.Modules) :
    modTensorMap' (𝟙 L) (𝟙 M) = 𝟙 (modTensor L M) := by
  unfold modTensorMap'
  simp

/-- `modTensorMap` preserves composition. -/
lemma modTensorMap'_comp {L L' L'' M M' M'' : Z.Modules}
    (e : L ⟶ L') (f : L' ⟶ L'') (e' : M ⟶ M') (f' : M' ⟶ M'') :
    modTensorMap' (e ≫ f) (e' ≫ f') = modTensorMap' e e' ≫ modTensorMap' f f' := by
  unfold modTensorMap'
  simp [MonoidalCategory.tensor_comp]

/-- Naturality of the left unitor. -/
lemma modTensorUnitLeftIso_naturality {M M' : Z.Modules} (g : M ⟶ M') :
    modTensorMap' (𝟙 (modUnit Z)) g ≫ (modTensorUnitLeftIso M').hom =
      (modTensorUnitLeftIso M).hom ≫ g := by
  unfold modTensorMap' modTensorUnitLeftIso modSheafifyValIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  sorry

/-- Naturality of the right unitor. -/
lemma modTensorUnitRightIso_naturality {L L' : Z.Modules} (g : L ⟶ L') :
    modTensorMap' g (𝟙 (modUnit Z)) ≫ (modTensorUnitRightIso L').hom =
      (modTensorUnitRightIso L).hom ≫ g := by
  sorry

end Fermat
