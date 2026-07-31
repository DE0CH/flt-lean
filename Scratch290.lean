module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.HilbertModularity

@[expose] public section

open NumberField IsDedekindDomain Polynomial
open scoped NumberField

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

universe u v

namespace Scratch290

/-- The kernel of `ρbar|_{G_F}` is open, normal, of finite index, acts trivially
on `ad⁰ρbar(1)`, and swallows the inertia at every place outside `S`. -/
theorem exists_openNormal_trivial_hilbertAdZeroTwist
    (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V] (ρbar : GaloisRep ℚ k V)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hSunr : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      (ρbar.map (algebraMap ℚ F)).IsUnramifiedAt w) :
    ∃ N₁ : Subgroup (Γ F),
      N₁.Normal ∧ IsOpen (N₁ : Set (Γ F)) ∧ N₁.FiniteIndex ∧
      (∀ g ∈ N₁, ∀ m : ↥(hilbertAdZeroTwist F ρbar),
        (hilbertAdZeroTwist F ρbar).ρ g m = m) ∧
      (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
        ∀ σ : ↥(localInertiaGroup w), hilbertInertiaToGlobalHom F w σ ∈ N₁) := by
  classical
  letI := moduleTopology k (Module.End k V)
  haveI : DiscreteTopology (Module.End k V) := discreteTopology_moduleTopology _ _
  refine ⟨(ρbar.map (algebraMap ℚ F)).ker, inferInstance, ?_, ?_, ?_, ?_⟩
  · -- OPEN: preimage of the open singleton `{1}` under a continuous map
    have hcont : Continuous fun g : Γ F => (ρbar.map (algebraMap ℚ F)) g :=
      ContinuousMonoidHom.continuous_toFun (ρbar.map (algebraMap ℚ F))
    have hrw : ((ρbar.map (algebraMap ℚ F)).ker : Set (Γ F)) =
        (fun g : Γ F => (ρbar.map (algebraMap ℚ F)) g) ⁻¹' {1} := rfl
    rw [hrw]
    exact (isOpen_discrete ({1} : Set (Module.End k V))).preimage hcont
  · -- FINITE INDEX: an open subgroup of the compact group `Γ F`
    haveI : CompactSpace (Γ F) :=
      inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
    have hopen : IsOpen ((ρbar.map (algebraMap ℚ F)).ker : Set (Γ F)) := by
      have hcont : Continuous fun g : Γ F => (ρbar.map (algebraMap ℚ F)) g :=
        ContinuousMonoidHom.continuous_toFun (ρbar.map (algebraMap ℚ F))
      have hrw : ((ρbar.map (algebraMap ℚ F)).ker : Set (Γ F)) =
          (fun g : Γ F => (ρbar.map (algebraMap ℚ F)) g) ⁻¹' {1} := rfl
      rw [hrw]
      exact (isOpen_discrete ({1} : Set (Module.End k V))).preimage hcont
    haveI : Finite (Γ F ⧸ (ρbar.map (algebraMap ℚ F)).ker) :=
      Subgroup.quotient_finite_of_isOpen _ hopen
    exact Subgroup.finiteIndex_of_finite_quotient
  · -- TRIVIAL ACTION on `ad⁰ρbar(1)`
    intro g hg m
    have hg1 : (ρbar.map (algebraMap ℚ F)) g = 1 := hg
    have hginv : (ρbar.map (algebraMap ℚ F)) g⁻¹ = 1 :=
      (inv_mem (G := Γ F) (H := (ρbar.map (algebraMap ℚ F)).ker) hg :
        g⁻¹ ∈ (ρbar.map (algebraMap ℚ F)).ker)
    have h : (hilbertAdZeroTwist F ρbar).ρ g = (hilbertAdZeroTwist F ρbar).ρ 1 := by
      refine hilbertAdZeroTwist_rho_eq_of_apply_eq F ρbar ?_ ?_
      · rw [hg1, map_one]
      · rw [hginv, inv_one, map_one]
    rw [h, map_one]
    rfl
  · -- INERTIA outside `S`
    intro w hw σ
    exact GaloisRep.IsUnramifiedAt.localInertiaGroup_le (self := hSunr w hw) σ.2

/-- **A uniform bound on the size of the image of a cocycle.** -/
theorem exists_bound_forall_mem_finset_eval₁_hilbertAdZeroTwist
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V] (ρbar : GaloisRep ℚ k V)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hSram : hilbertHardlyRamifiedPlaces ℓ F ⊆ (S : Set (HeightOneSpectrum (𝓞 F))))
    (hSunr : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      (ρbar.map (algebraMap ℚ F)).IsUnramifiedAt w) :
    ∃ m : ℕ, ∀ z : ContinuousCohomology.cocycles₁ (hilbertAdZeroTwist F ρbar),
      ContinuousCohomology.cocycleClass (hilbertAdZeroTwist F ρbar) 1 z ∈
          hilbertH1TwistUnramified ℓ F ρbar →
        ∃ T : Finset ↥(hilbertAdZeroTwist F ρbar), T.card ≤ m ∧
          ∀ g : Γ F, ContinuousCohomology.eval₁ (hilbertAdZeroTwist F ρbar) z.1 g ∈ T :=
  sorry

/-- The assembly. -/
theorem exists_mem_hilbertInertiaOutsideSubgroups_resSubgroup_eq_zero'
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type u) [Field F] [NumberField F]
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    [Module.Free k V] (ρbar : GaloisRep ℚ k V)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hSram : hilbertHardlyRamifiedPlaces ℓ F ⊆ (S : Set (HeightOneSpectrum (𝓞 F))))
    (hSunr : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      (ρbar.map (algebraMap ℚ F)).IsUnramifiedAt w) :
    ∃ n : ℕ, ∀ c ∈ hilbertH1TwistUnramified ℓ F ρbar,
      ∃ N ∈ hilbertInertiaOutsideSubgroups F S n,
        c ∈ LinearMap.ker (hilbertResSubgroupTwist1 F ρbar N).hom.toLinearMap := by
  classical
  haveI hdisc : DiscreteTopology ↥(hilbertAdZeroTwist F ρbar) :=
    inferInstanceAs (DiscreteTopology (HilbertAdZero k V))
  obtain ⟨N₁, hN₁norm, hN₁open, hN₁FI, hN₁triv, hN₁inert⟩ :=
    exists_openNormal_trivial_hilbertAdZeroTwist F ρbar S hSunr
  obtain ⟨m, hm⟩ :=
    exists_bound_forall_mem_finset_eval₁_hilbertAdZeroTwist ℓ F ρbar S hSram hSunr
  haveI := hN₁norm
  haveI := hN₁FI
  refine ⟨N₁.index * m, ?_⟩
  intro c hc
  obtain ⟨z, hz⟩ :=
    ContinuousCohomology.exists_cocycleClass_eq (X := hilbertAdZeroTwist F ρbar) 1 c
  obtain ⟨T, hTcard, hTmem⟩ := hm z (hz ▸ hc)
  set e : Γ F → ↥(hilbertAdZeroTwist F ρbar) :=
    fun g => ContinuousCohomology.eval₁ (hilbertAdZeroTwist F ρbar) z.1 g with hedef
  have hmul : ∀ g h : Γ F,
      e (g * h) = e g + (hilbertAdZeroTwist F ρbar).ρ g (e h) :=
    fun g h => ContinuousCohomology.cocycles₁_eval₁_mul z g h
  have hone : e 1 = 0 :=
    ContinuousCohomology.eval₁_one (ContinuousCohomology.cocycles₁_d_eq_zero z)
  have hinvv : ∀ g : Γ F,
      e g⁻¹ = - (hilbertAdZeroTwist F ρbar).ρ g⁻¹ (e g) :=
    fun g => ContinuousCohomology.eval₁_inv (ContinuousCohomology.cocycles₁_d_eq_zero z) g
  -- vanishing of the cocycle on the inertia away from `S`
  have hinert0 : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      ∀ σ : ↥(localInertiaGroup w), e (hilbertInertiaToGlobalHom F w σ) = 0 := by
    intro w hw σ
    have hv : w ∉ hilbertHardlyRamifiedPlaces ℓ F := fun h => hw (hSram h)
    have hker : c ∈ LinearMap.ker
        (hilbertLocResInertiaTwist1 F ρbar w).hom.toLinearMap := by
      have h1 := (Submodule.mem_iInf _).mp hc w
      exact (Submodule.mem_iInf _).mp h1 hv
    have hzero : ContinuousCohomology.cocycleClass
        (hilbertAdZeroTwistInertia F ρbar w) 1
        (ContinuousCohomology.cocyclesMapKer (hilbertInertiaToGlobalHom F w)
          (CategoryTheory.CategoryStruct.id (hilbertAdZeroTwistInertia F ρbar w)) 1 z) = 0 := by
      rw [← ContinuousCohomology.map_cocycleClass_cocyclesMapKer, hz]
      exact hker
    obtain ⟨mm, hmm⟩ :=
      ContinuousCohomology.exists_eval₁_eq_sub_of_cocycleClass_eq_zero _ hzero
    have h1 := hmm σ
    rw [ContinuousCohomology.eval₁_cocyclesMapKer] at h1
    have h2 : (hilbertAdZeroTwist F ρbar).ρ (hilbertInertiaToGlobalHom F w σ) mm = mm :=
      hN₁triv _ (hN₁inert w hw σ) mm
    have h3 : (hilbertAdZeroTwistInertia F ρbar w).ρ σ mm = mm := h2
    rw [h3, sub_self] at h1
    exact h1
  -- the subgroup
  set Nsub : Subgroup (Γ F) :=
    { carrier := {g | g ∈ N₁ ∧ e g = 0}
      one_mem' := ⟨one_mem _, hone⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [hmul, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        rw [hinvv, ha.2, map_zero, neg_zero]⟩ } with hNsubdef
  have hle : Nsub ≤ N₁ := fun g hg => hg.1
  have hNnorm : Nsub.Normal := by
    refine ⟨fun x hx g => ⟨hN₁norm.conj_mem x hx.1 g, ?_⟩⟩
    have hconj := ContinuousCohomology.eval₁_conj
      (ContinuousCohomology.cocycles₁_d_eq_zero z) g x
    show e (g * x * g⁻¹) = 0
    rw [hedef]
    show ContinuousCohomology.eval₁ (hilbertAdZeroTwist F ρbar) z.1 (g * x * g⁻¹) = 0
    rw [hconj,
      show ContinuousCohomology.eval₁ (hilbertAdZeroTwist F ρbar) z.1 x = e x from rfl,
      hx.2, map_zero, zero_add, hN₁triv _ (hN₁norm.conj_mem x hx.1 g), sub_self]
  have hNopen : IsOpen (Nsub : Set (Γ F)) := by
    have h1 : (Nsub : Set (Γ F)) = (N₁ : Set (Γ F)) ∩ (e ⁻¹' {0}) := rfl
    rw [h1]
    exact hN₁open.inter
      ((isOpen_discrete ({0} : Set ↥(hilbertAdZeroTwist F ρbar))).preimage
        (ContinuousCohomology.continuous_eval₁ (hilbertAdZeroTwist F ρbar) z.1))
  -- the index bound
  have hwd : ∀ a b : Γ F, a⁻¹ * b ∈ Nsub →
      ((QuotientGroup.mk a : Γ F ⧸ N₁), (⟨e a, hTmem a⟩ : ↥T)) =
      ((QuotientGroup.mk b : Γ F ⧸ N₁), (⟨e b, hTmem b⟩ : ↥T)) := by
    intro a b hab
    refine Prod.ext ((QuotientGroup.eq (s := N₁)).mpr (hle hab)) ?_
    have hb : b = a * (a⁻¹ * b) := by group
    refine Subtype.ext ?_
    show e a = e b
    rw [hb, hmul, hab.2, map_zero, add_zero]
  set Q : Γ F ⧸ Nsub → (Γ F ⧸ N₁) × ↥T :=
    Quotient.lift (fun g => ((QuotientGroup.mk g : Γ F ⧸ N₁), (⟨e g, hTmem g⟩ : ↥T)))
      (fun a b hab => hwd a b (QuotientGroup.leftRel_apply.mp hab)) with hQdef
  have hQinj : Function.Injective Q := by
    refine fun x y => Quotient.inductionOn₂ x y ?_
    intro a b hEq
    have h1 : (QuotientGroup.mk a : Γ F ⧸ N₁) = QuotientGroup.mk b :=
      congrArg Prod.fst hEq
    have h2 : e a = e b := congrArg Subtype.val (congrArg Prod.snd hEq)
    have hab1 : a⁻¹ * b ∈ N₁ := (QuotientGroup.eq (s := N₁)).mp h1
    have hab2 : e (a⁻¹ * b) = 0 := by
      have hb : b = a * (a⁻¹ * b) := by group
      have h3 : e b = e a + (hilbertAdZeroTwist F ρbar).ρ a (e (a⁻¹ * b)) := by
        rw [← hmul, ← hb]
      rw [h2] at h3
      have h4 : (hilbertAdZeroTwist F ρbar).ρ a (e (a⁻¹ * b)) = 0 := by
        have := h3.symm
        rwa [add_eq_left] at this
      have h5 := congrArg (fun t => (hilbertAdZeroTwist F ρbar).ρ a⁻¹ t) h4
      simpa [ContinuousCohomology.rho_inv_apply] using h5
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ⟨hab1, hab2⟩)
  haveI hfinQ : Finite (Γ F ⧸ Nsub) := Finite.of_injective Q hQinj
  have hidx : Nsub.index ≤ N₁.index * m := by
    have h1 : Nsub.index = Nat.card (Γ F ⧸ Nsub) := rfl
    have h2 : N₁.index = Nat.card (Γ F ⧸ N₁) := rfl
    calc Nsub.index = Nat.card (Γ F ⧸ Nsub) := h1
      _ ≤ Nat.card ((Γ F ⧸ N₁) × ↥T) := Nat.card_le_card_of_injective Q hQinj
      _ = Nat.card (Γ F ⧸ N₁) * Nat.card ↥T := Nat.card_prod _ _
      _ ≤ N₁.index * m := by
          rw [← h2]
          exact Nat.mul_le_mul_left _ (by simpa using hTcard)
  haveI hNFI : Nsub.FiniteIndex := by
    refine ⟨?_⟩
    show Nat.card (Γ F ⧸ Nsub) ≠ 0
    exact Nat.card_pos.ne'
  -- the class dies on `Nsub`
  have hkerc : c ∈ LinearMap.ker (hilbertResSubgroupTwist1 F ρbar Nsub).hom.toLinearMap := by
    have hzero : ContinuousCohomology.cocycleClass
        (hilbertAdZeroTwistSubgroup F ρbar Nsub) 1
        (ContinuousCohomology.cocyclesMapKer (hilbertSubgroupToGlobalHom F Nsub)
          (CategoryTheory.CategoryStruct.id
            (hilbertAdZeroTwistSubgroup F ρbar Nsub)) 1 z) = 0 := by
      refine ContinuousCohomology.cocycleClass_eq_zero_of_eval₁_eq_sub _ 0
        (by simpa using continuous_const) ?_
      intro h
      rw [ContinuousCohomology.eval₁_cocyclesMapKer, map_zero, sub_zero]
      exact h.2.2
    have hmc := ContinuousCohomology.map_cocycleClass_cocyclesMapKer
      (hilbertSubgroupToGlobalHom F Nsub)
      (CategoryTheory.CategoryStruct.id (hilbertAdZeroTwistSubgroup F ρbar Nsub)) 1 z
    rw [hzero, hz] at hmc
    exact hmc
  exact ⟨Nsub, ⟨hNnorm, hNopen, hNFI, hidx,
    fun w hw σ => ⟨hN₁inert w hw σ, hinert0 w hw σ⟩⟩, hkerc⟩

end Scratch290

end GaloisRepresentation
