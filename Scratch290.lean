import Fermat.FLT.NumberField.UnramifiedClassFieldExistence

open NumberField

open scoped nonZeroDivisors

namespace Scratch290

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- candidate for the single shared reciprocity leaf. -/
theorem newleaf [IsGalois K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∃ ψ : (L ≃ₐ[K] L) →* ClassGroup (𝓞 K) ⧸ relNormClassSubgroup K L,
      Function.Surjective ψ ∧
      (IsUnramifiedAtInfinitePlaces K L → Function.Injective ψ) :=
  sorry

/-- leaf 3 from `newleaf`. -/
theorem leaf3 [IsGalois K L] [IsUnramifiedAtInfinitePlaces K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∃ φ : ClassGroup (𝓞 K) →* (L ≃ₐ[K] L), Function.Surjective φ ∧
      ∀ (I : Ideal (𝓞 L)) (J : (Ideal (𝓞 K))⁰), I ≠ ⊥ →
        (J : Ideal (𝓞 K)) = Ideal.relNorm (𝓞 K) I → φ (ClassGroup.mk0 J) = 1 := by
  obtain ⟨ψ, hsurj, hinj⟩ := newleaf K L habel hunr
  let e : (L ≃ₐ[K] L) ≃* ClassGroup (𝓞 K) ⧸ relNormClassSubgroup K L :=
    MulEquiv.ofBijective ψ ⟨hinj inferInstance, hsurj⟩
  refine ⟨(e.symm : _ →* _).comp (QuotientGroup.mk' (relNormClassSubgroup K L)), ?_, ?_⟩
  · exact e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro I J hI hJ
    have hmem : ClassGroup.mk0 J ∈ relNormClassSubgroup K L :=
      Subgroup.subset_closure ⟨I, hI, congrArg ClassGroup.mk0 (Subtype.ext hJ)⟩
    have : (QuotientGroup.mk' (relNormClassSubgroup K L)) (ClassGroup.mk0 J) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hmem
    simp [MonoidHom.comp_apply, this]

/-- leaf 2 from `newleaf`. -/
theorem leaf2 [IsGalois K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    (relNormClassSubgroup K L).index ≤ Module.finrank K L := by
  obtain ⟨ψ, hsurj, -⟩ := newleaf K L habel hunr
  calc (relNormClassSubgroup K L).index
      = Nat.card (ClassGroup (𝓞 K) ⧸ relNormClassSubgroup K L) := Subgroup.index_eq_card _
    _ ≤ Nat.card (L ≃ₐ[K] L) := Nat.card_le_card_of_surjective _ hsurj
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L

end Scratch290
