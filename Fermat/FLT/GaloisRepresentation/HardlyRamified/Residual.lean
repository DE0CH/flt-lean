/-
Residual.lean — own work for the Fermat project (not vendored from the
FLT project).

# Residual reduction of hardly ramified representations at a general odd prime

General-`p` analogue of the residual-reduction assembly of
`Threeadic.lean` (`IsHardlyRamified.exists_residual_isHardlyRamified`,
which is the `p = 3` instance): the reduction of a hardly ramified
`p`-adic representation modulo the maximal ideal of its coefficient
ring is a mod-`p` hardly ramified representation over the finite
residue field.

The route follows `Threeadic.lean` step by step, with one genuine
difference: the coefficient ring `R` here is a module-finite local
topological `ℤ_p`-algebra that is a NONTRIVIAL ring (in the intended
consumer, a domain) rather than a FREE `ℤ_p`-module, so the
compact-Hausdorff-via-basis argument of `Threeadic.lean`'s residue
package is unavailable.  Instead:

* `R` is compact as the continuous image of `ℤ_p^n` under a surjection
  furnished by module-finiteness (linear maps into a module-topology
  module are continuous);
* `p` lands in the maximal ideal `𝔪` of `R` by Nakayama (were it a
  unit, `⊤ = 𝔪_{ℤ_p} • ⊤` would force `R = 0`);
* `𝔪` is OPEN because the surjection `π : ℤ_p^n → R` is an open map
  (`IsModuleTopology.isOpenMap_of_surjective`) and `π⁻¹ 𝔪` is a
  submodule containing the open submodule `∏ (p ℤ_p)` — this replaces
  the `IsLocalRing.isOpen_maximalIdeal` route, which needs a Hausdorff
  hypothesis we never establish;
* the residue field `R ⧸ 𝔪` is finite as the quotient of a compact
  group by an open subgroup.

Everything else — the equivariant identification of the doubly
base-changed local space, the transfer of flatness and tameness, the
determinant and unramifiedness transfers — is prime-generic and is
restated here at a general place `v` (resp. general odd `p`), with the
proofs of the `p = 3` file carried over.
-/
module

public import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
import Mathlib.LinearAlgebra.Charpoly.BaseChange
-- `LinearMap.det_baseChange`, used in the determinant transfer
import Mathlib.Topology.Algebra.OpenSubgroup
-- `Submodule.isOpen_mono` and `AddSubgroup.quotient_finite_of_isOpen`:
-- openness of the maximal ideal and finiteness of the residue field
import Mathlib.NumberTheory.Padics.ProperSpace
-- the `CompactSpace ℤ_[p]` instance behind compactness of `R`
import Mathlib.RingTheory.Nakayama
-- `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`: `p` is a non-unit
-- in `R`

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

-- Same local instance boost as `Threeadic.lean`: keep the canonical
-- `Algebra ℚ` instances findable next to `DivisionRing.toRatAlgebra`.
attribute [local instance 2000] AlgebraicClosure.instAlgebra
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

open scoped TensorProduct

open IsDedekindDomain

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

universe u v

/-- **The residue package at a general prime** (general-`p` analogue of
`exists_residue_package` in `Threeadic.lean`): a local, topological,
module-finite `ℤ_p`-algebra `R` that is a nontrivial ring has a residue
field `kk` — finite, of characteristic `p`, discrete — with a surjective
continuous `ℤ_p`-algebra map `R → kk` whose kernel is the (open) maximal
ideal, and base change along it preserves the rank.  Unlike the `p = 3`
version, `R` is not assumed free over `ℤ_p`: compactness of `R` comes
from a module-finiteness surjection `ℤ_p^n → R` (continuous into the
module topology), openness of `𝔪` from that surjection being an open map
with `π⁻¹ 𝔪 ⊇ ∏ (p ℤ_p)` (using `p ∈ 𝔪`, itself Nakayama), and
finiteness of `R ⧸ 𝔪` from compactness of `R` and openness of `𝔪`. -/
theorem exists_residue_package_odd {p : ℕ} [Fact p.Prime] {R : Type u}
    [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[p] R]
    (V : Type v) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (hV : Module.rank R V = 2) :
    ∃ (kk : Type u) (_ : Field kk) (_ : Finite kk) (_ : Algebra ℤ_[p] kk)
      (_ : TopologicalSpace kk) (_ : DiscreteTopology kk)
      (_ : IsTopologicalRing kk) (_ : Algebra R kk)
      (_ : ContinuousSMul R kk) (_ : IsScalarTower ℤ_[p] R kk),
      Function.Surjective (algebraMap R kk) ∧
      IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) ∧
      RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R ∧
      Module.rank kk (kk ⊗[R] V) = 2 := by
  classical
  -- a module-finiteness surjection `π : ℤ_p^n → R`, continuous and open
  -- for the module topology on `R`
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[p] R
  have hπcont : Continuous π := IsModuleTopology.continuous_of_linearMap π
  have hπopen : IsOpenMap π := IsModuleTopology.isOpenMap_of_surjective hπ
  -- `R` is compact: the continuous image of the compact `ℤ_p^n`
  haveI : CompactSpace R := by
    constructor
    have himg : (Set.univ : Set R) = π '' Set.univ := by
      rw [Set.image_univ]
      exact (Set.range_eq_univ.mpr hπ).symm
    rw [himg]
    exact isCompact_univ.image hπcont
  -- `p` maps into the maximal ideal of `R`: otherwise it is a unit,
  -- `⊤ = 𝔪_{ℤ_p} • ⊤` and Nakayama forces `R = 0`
  have hp_mem : algebraMap ℤ_[p] R p ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨u, hu⟩ := hunit
    have htop : (⊤ : Submodule ℤ_[p] R) ≤
        (IsLocalRing.maximalIdeal ℤ_[p]) • (⊤ : Submodule ℤ_[p] R) := by
      intro r _
      have hr : r = (p : ℤ_[p]) • ((↑u⁻¹ : R) * r) := by
        rw [Algebra.smul_def, ← hu, Units.mul_inv_cancel_left]
      rw [hr]
      exact Submodule.smul_mem_smul
        (by rw [PadicInt.maximalIdeal_eq_span_p]
            exact Ideal.subset_span rfl) trivial
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal ℤ_[p]) ⊤ Module.Finite.fg_top htop
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
    exact absurd hbot top_ne_bot
  -- `π⁻¹ 𝔪` contains the open submodule `∏ (p ℤ_p)`, so `𝔪` is open
  have hspan_open : IsOpen ((Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    have hset : ((Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) =
        {x : ℤ_[p] | ‖x‖ < 1} := by
      ext x
      simp [Ideal.mem_span_singleton, PadicInt.norm_lt_one_iff_dvd]
    rw [hset]
    exact isOpen_lt continuous_norm continuous_const
  have hopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) := by
    have hle : Submodule.pi Set.univ (fun _ : Fin n => Ideal.span {(p : ℤ_[p])}) ≤
        Submodule.comap π
          ((IsLocalRing.maximalIdeal R).restrictScalars ℤ_[p]) := by
      intro x hx
      rw [Submodule.mem_pi] at hx
      choose c hc using fun i =>
        Ideal.mem_span_singleton.mp (hx i (Set.mem_univ i))
      have hxc : x = (p : ℤ_[p]) • c := funext fun i => by
        rw [Pi.smul_apply, smul_eq_mul, ← hc i]
      rw [Submodule.mem_comap, hxc, map_smul]
      show (p : ℤ_[p]) • π c ∈ IsLocalRing.maximalIdeal R
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ hp_mem
    have hUopen : IsOpen ((Submodule.pi Set.univ
        (fun _ : Fin n => Ideal.span {(p : ℤ_[p])})) :
          Set (Fin n → ℤ_[p])) := by
      have hcoe : ((Submodule.pi Set.univ
          (fun _ : Fin n => Ideal.span {(p : ℤ_[p])})) :
            Set (Fin n → ℤ_[p])) =
          Set.pi Set.univ
            (fun _ : Fin n => ((Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) :
              Set ℤ_[p])) := by
        ext x
        simp [Set.mem_pi]
      rw [hcoe]
      exact isOpen_set_pi Set.finite_univ fun i _ => hspan_open
    have hPopen : IsOpen ((Submodule.comap π
        ((IsLocalRing.maximalIdeal R).restrictScalars ℤ_[p])) :
          Set (Fin n → ℤ_[p])) :=
      Submodule.isOpen_mono hle hUopen
    have himg := hπopen _ hPopen
    rwa [show ((Submodule.comap π
        ((IsLocalRing.maximalIdeal R).restrictScalars ℤ_[p])) :
          Set (Fin n → ℤ_[p])) =
        π ⁻¹' ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) from rfl,
      Set.image_preimage_eq _ hπ] at himg
  -- the residue field is finite: quotient of a compact group by an open
  -- subgroup
  haveI hfinres : Finite (IsLocalRing.ResidueField R) :=
    AddSubgroup.quotient_finite_of_isOpen
      (IsLocalRing.maximalIdeal R).toAddSubgroup hopen
  -- the residue field with the discrete topology
  letI : TopologicalSpace (IsLocalRing.ResidueField R) := ⊥
  haveI : DiscreteTopology (IsLocalRing.ResidueField R) := ⟨rfl⟩
  haveI : IsTopologicalRing (IsLocalRing.ResidueField R) :=
    { continuous_add := continuous_of_discreteTopology
      continuous_mul := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  letI algZp : Algebra ℤ_[p] (IsLocalRing.ResidueField R) :=
    ((algebraMap R (IsLocalRing.ResidueField R)).comp
      (algebraMap ℤ_[p] R)).toAlgebra
  haveI hST : IsScalarTower ℤ_[p] R (IsLocalRing.ResidueField R) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  -- the residue map is continuous (the open kernel makes it locally
  -- constant), hence the scalar action is continuous
  have hresid_cont : Continuous (algebraMap R (IsLocalRing.ResidueField R)) := by
    refine continuous_def.mpr fun s _ => ?_
    have hcover : (algebraMap R (IsLocalRing.ResidueField R)) ⁻¹' s =
        ⋃ y ∈ s, (algebraMap R (IsLocalRing.ResidueField R)) ⁻¹' {y} := by
      ext r
      simp
    rw [hcover]
    refine isOpen_biUnion fun y _ => ?_
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : R,
        algebraMap R (IsLocalRing.ResidueField R) r₀ = y := by
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      exact IsLocalRing.residue_surjective y
    have hcoset : (algebraMap R (IsLocalRing.ResidueField R)) ⁻¹' {y} =
        (fun x => r₀ + x) '' ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) := by
      ext r
      constructor
      · intro hr
        refine ⟨r - r₀, ?_, by ring⟩
        have h1 : algebraMap R (IsLocalRing.ResidueField R) (r - r₀) = 0 := by
          rw [map_sub]
          have h2 : algebraMap R (IsLocalRing.ResidueField R) r = y := hr
          have h3 : algebraMap R (IsLocalRing.ResidueField R) r₀ = y := hr₀
          rw [h2, h3, sub_self]
        rwa [← RingHom.mem_ker, IsLocalRing.ResidueField.algebraMap_eq,
          IsLocalRing.ker_residue] at h1
      · rintro ⟨m, hm, rfl⟩
        have h1 : algebraMap R (IsLocalRing.ResidueField R) m = 0 := by
          rw [← RingHom.mem_ker, IsLocalRing.ResidueField.algebraMap_eq,
            IsLocalRing.ker_residue]
          exact hm
        show algebraMap R (IsLocalRing.ResidueField R) (r₀ + m) = y
        rw [map_add, h1, add_zero, hr₀]
    rw [hcoset]
    exact (Homeomorph.addLeft r₀).isOpenMap _ hopen
  haveI hCS : ContinuousSMul R (IsLocalRing.ResidueField R) := by
    constructor
    have hfact : (fun q : R × IsLocalRing.ResidueField R => q.1 • q.2) =
        (fun q : IsLocalRing.ResidueField R × IsLocalRing.ResidueField R =>
          q.1 * q.2) ∘ (fun q : R × IsLocalRing.ResidueField R =>
          (algebraMap R (IsLocalRing.ResidueField R) q.1, q.2)) := by
      funext q
      simp [Algebra.smul_def]
    rw [hfact]
    exact continuous_of_discreteTopology.comp
      ((hresid_cont.comp continuous_fst).prodMk continuous_snd)
  refine ⟨IsLocalRing.ResidueField R, inferInstance, hfinres, algZp,
    inferInstance, inferInstance, inferInstance, inferInstance, hCS, hST,
    (by rw [IsLocalRing.ResidueField.algebraMap_eq]
        exact IsLocalRing.residue_surjective), hopen,
    (by rw [IsLocalRing.ResidueField.algebraMap_eq]
        exact IsLocalRing.ker_residue), ?_⟩
  -- the rank transfers along the base change
  rw [Module.rank_baseChange, hV]
  simp

/-- **Degenerate flatness over the trivial quotient, at a general place**
(general-`v` analogue of `hasFlatProlongationAt_of_subsingleton` in
`Threeadic.lean`, same proof): a Galois representation on a subsingleton
module has a flat prolongation at any finite place `v` — the trivial
group scheme `Spec 𝒪ᵥ` works, its geometric points being the single
algebra map matched with the single element of the space. -/
theorem hasFlatProlongationAt_of_subsingleton_at
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {A' : Type*} [CommRing A']
    [TopologicalSpace A'] {M' : Type*} [AddCommGroup M'] [Module A' M']
    [Subsingleton M'] (ρ' : GaloisRep ℚ A' M') :
    ρ'.HasFlatProlongationAt v := by
  classical
  set Kv := IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
  set Ov := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
  -- every `Kᵥ`-algebra map out of `Kᵥ ⊗[𝒪ᵥ] 𝒪ᵥ ≅ Kᵥ` is the canonical one
  haveI hsub : Subsingleton (Kv ⊗[Ov] Ov →ₐ[Kv] AlgebraicClosure Kv) := by
    constructor
    intro f g
    have hcomp : ∀ h : Kv ⊗[Ov] Ov →ₐ[Kv] AlgebraicClosure Kv,
        h = ((h.comp (Algebra.TensorProduct.rid Ov Kv Kv).symm.toAlgHom).comp
          (Algebra.TensorProduct.rid Ov Kv Kv).toAlgHom) := by
      intro h
      ext
    rw [hcomp f, hcomp g]
    congr 1
    exact AlgHom.ext fun x =>
      ((f.comp (Algebra.TensorProduct.rid Ov Kv Kv).symm.toAlgHom).commutes
        x).trans
        ((g.comp
          (Algebra.TensorProduct.rid Ov Kv Kv).symm.toAlgHom).commutes x).symm
  haveI hspace : Subsingleton ((ρ'.toLocal v).Space) :=
    inferInstanceAs (Subsingleton M')
  refine ⟨Ov, inferInstance, inferInstance, inferInstance, inferInstance,
    ?_, ?_, ?_⟩
  · -- étale generic fibre: base change of the étale identity
    exact inferInstance
  · -- the zero equivariant map into the subsingleton space
    exact
      { toFun := fun _ => 0
        map_smul' := fun g _ => (smul_zero g).symm
        map_zero' := rfl
        map_add' := fun _ _ => (add_zero (0 : M')).symm }
  · constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      refine ⟨Additive.ofMul ((Algebra.ofId Kv (AlgebraicClosure Kv)).comp
        (Algebra.TensorProduct.rid Ov Kv Kv).toAlgHom), ?_⟩
      exact Subsingleton.elim _ y

/-- **The residual space identification, at a general place**
(general-`v` analogue of `flat_space_equiv_residue` in `Threeadic.lean`,
same proof): the double base change `(kk ⧸ ⊥) ⊗_kk (kk ⊗_R V)` is
`Γ Kᵥ`-equivariantly isomorphic to `(R ⧸ 𝔪) ⊗_R V` — the
quotient-by-`⊥` collapses, and `kk ≅ R ⧸ 𝔪` along the (surjective,
kernel-`𝔪`) residue map transports the coefficients. -/
theorem flat_space_equiv_residue_at
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (kk : Type u) [Field kk]
    [TopologicalSpace kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R)
    {ρ : GaloisRep ℚ R V} :
    ∃ e : ((((ρ.baseChange kk).baseChange (kk ⧸ (⊥ : Ideal kk))).toLocal
        v).Space ≃+
      ((ρ.baseChange (R ⧸ IsLocalRing.maximalIdeal R)).toLocal v).Space),
      ∀ (g : Γ (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))
        (x : (((ρ.baseChange kk).baseChange (kk ⧸ (⊥ : Ideal kk))).toLocal
          v).Space),
        e (g • x) = g • e x := by
  classical
  -- the coefficient identification `kk ⧸ ⊥ ≃+* R ⧸ 𝔪`
  let ψ₂ : R ⧸ RingHom.ker (algebraMap R kk) ≃+* kk :=
    RingHom.quotientKerEquivOfSurjective hsurj
  let φ : (kk ⧸ (⊥ : Ideal kk)) ≃+* (R ⧸ IsLocalRing.maximalIdeal R) :=
    (RingEquiv.quotientBot kk).trans
      (ψ₂.symm.trans (Ideal.quotEquivOfEq hker))
  have hφalg : ∀ r : R,
      φ (algebraMap R (kk ⧸ (⊥ : Ideal kk)) r) =
        algebraMap R (R ⧸ IsLocalRing.maximalIdeal R) r := by
    intro r
    have h1 : (RingEquiv.quotientBot kk)
        (algebraMap R (kk ⧸ (⊥ : Ideal kk)) r) = algebraMap R kk r := rfl
    have h2 : ψ₂ (Ideal.Quotient.mk _ r) = algebraMap R kk r := rfl
    have h3 : ψ₂.symm (algebraMap R kk r) = Ideal.Quotient.mk _ r := by
      rw [← h2, RingEquiv.symm_apply_apply]
    show (Ideal.quotEquivOfEq hker) (ψ₂.symm ((RingEquiv.quotientBot kk)
      (algebraMap R (kk ⧸ (⊥ : Ideal kk)) r))) = _
    rw [h1, h3]
    rfl
  -- the `R`-linear form of `φ`
  let φlin : (kk ⧸ (⊥ : Ideal kk)) ≃ₗ[R] (R ⧸ IsLocalRing.maximalIdeal R) :=
    { φ.toAddEquiv with
      map_smul' := fun r x => by
        show φ (r • x) = r • φ x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφalg] }
  -- assemble: cancel the middle base change, then transport coefficients
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange R kk
    (kk ⧸ (⊥ : Ideal kk)) (kk ⧸ (⊥ : Ideal kk)) V
  let e₂ := TensorProduct.congr φlin (LinearEquiv.refl R V)
  refine ⟨e₁.toAddEquiv.trans e₂.toAddEquiv, ?_⟩
  intro g x
  show (e₁.toAddEquiv.trans e₂.toAddEquiv)
      ((((ρ.baseChange kk).baseChange (kk ⧸ (⊥ : Ideal kk))).toLocal v) g x) =
    (((ρ.baseChange (R ⧸ IsLocalRing.maximalIdeal R)).toLocal v) g)
      ((e₁.toAddEquiv.trans e₂.toAddEquiv) x)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul c y =>
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [show (c ⊗ₜ[kk] (0 : kk ⊗[R] V)) =
        (0 : (kk ⧸ (⊥ : Ideal kk)) ⊗[kk] (kk ⊗[R] V)) from
        TensorProduct.tmul_zero _ _]
      simp
    | add a b ha hb =>
      rw [TensorProduct.tmul_add]
      simp only [map_add, ha, hb]
    | tmul d w => rfl

/-- **Flatness transfers to the residue field, at a general place**
(general-`v` analogue of `isFlatAt_baseChange_residue` in
`Threeadic.lean`, same proof): the ideals of the discrete field `kk` are
`⊥` and `⊤`; the `⊥` case is the `I = 𝔪` instance of `ρ.IsFlatAt v`
transported along the equivariant space isomorphism, and the `⊤` case is
degenerate. -/
theorem isFlatAt_baseChange_residue_at
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (kk : Type u) [Field kk]
    [TopologicalSpace kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    (hsurj : Function.Surjective (algebraMap R kk))
    (hopen : IsOpen ((IsLocalRing.maximalIdeal R : Ideal R) : Set R))
    (hker : RingHom.ker (algebraMap R kk) = IsLocalRing.maximalIdeal R)
    {ρ : GaloisRep ℚ R V}
    (hflat : ρ.IsFlatAt v) :
    (ρ.baseChange kk).IsFlatAt v := by
  constructor
  intro I hI
  rcases Ideal.eq_bot_or_top I with rfl | rfl
  · -- `I = ⊥`: transport the `𝔪`-instance of `hflat` along the space iso
    obtain ⟨e, he⟩ := flat_space_equiv_residue_at v kk hsurj hker (ρ := ρ)
    refine (hflat.cond (IsLocalRing.maximalIdeal R) hopen).of_equiv _ e.symm ?_
    intro g x
    apply e.injective
    rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]
  · -- `I = ⊤`: the trivial quotient ring, degenerate flatness
    letI : Subsingleton (kk ⧸ (⊤ : Ideal kk)) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    letI : Subsingleton ((kk ⧸ (⊤ : Ideal kk)) ⊗[kk] (kk ⊗[R] V)) :=
      Module.subsingleton (kk ⧸ (⊤ : Ideal kk)) _
    exact hasFlatProlongationAt_of_subsingleton_at v _

/-- **Tameness at `2` transfers to the residue field** (general
coefficient-ring analogue of `isTameAtTwo_baseChange_residue` in
`Threeadic.lean`, same proof — the statement is about the prime `2` only
and never mentions the residue characteristic): the rank-1 tame
quadratic quotient of `ρ` at `2` base-changes to one for the residual
representation. Content: `π ⊗ 1 : kk ⊗ V → kk ⊗ R ≅ kk` and the
pushforward of `δ` along the residue map; the three conditions transfer
by the diagram chase on simple tensors. -/
theorem isTameAtTwo_baseChange_residue_res
    {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (kk : Type u) [Field kk]
    [TopologicalSpace kk] [IsTopologicalRing kk]
    [Algebra R kk] [ContinuousSMul R kk]
    {ρ : GaloisRep ℚ R V}
    (htame : ∃ (π : V →ₗ[R] R) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] R R),
      ∀ g : Γ ℚ_[2], ∀ v : V,
        π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Γ ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Γ ℚ_[2], δ g' * δ g' = 1)) :
    ∃ (π : (kk ⊗[R] V) →ₗ[kk] kk) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] kk kk),
      ∀ g : Γ ℚ_[2], ∀ v : kk ⊗[R] V,
        π ((ρ.baseChange kk).map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup :
            AddSubgroup Z2bar) (Γ ℚ_[2]) ≤ δ.ker) ∧
        (∀ g' : Γ ℚ_[2], δ g' * δ g' = 1) := by
  obtain ⟨π, hπsurj, δ, h⟩ := htame
  -- the canonical identification `kk ⊗[R] R ≃ₗ[kk] kk`
  let e : (kk ⊗[R] R) ≃ₗ[kk] kk := TensorProduct.AlgebraTensorModule.rid R kk kk
  -- the base-changed projection and character
  refine ⟨e.toLinearMap ∘ₗ LinearMap.baseChange kk π, ?_,
    (δ.baseChange kk).conj e, ?_⟩
  · -- surjectivity: hit `c` with `c ⊗ v₀` for a preimage `v₀` of `1`
    intro c
    obtain ⟨v₀, hv₀⟩ := hπsurj 1
    refine ⟨c ⊗ₜ v₀, ?_⟩
    simp [e, LinearMap.baseChange_tmul, hv₀,
      TensorProduct.AlgebraTensorModule.rid_tmul]
  · intro g w
    refine ⟨?_, ?_, ?_⟩
    · -- equivariance, by linearity on simple tensors
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul c v =>
        have h1 := (h g v).1
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [show ((ρ.baseChange kk).map (algebraMap ℚ ℚ_[2])) g (c ⊗ₜ v) =
          c ⊗ₜ ((ρ.map (algebraMap ℚ ℚ_[2])) g v) from rfl,
          LinearMap.baseChange_tmul, h1,
          GaloisRep.conj_apply, LinearMap.baseChange_tmul]
        rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, LinearEquiv.coe_coe,
          TensorProduct.AlgebraTensorModule.rid_symm_apply,
          show ((δ.baseChange kk) g : Module.End kk (kk ⊗[R] R)) =
            LinearMap.baseChange kk (δ g) from rfl,
          LinearMap.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.rid_tmul]
        rw [show (δ g) (π v) = π v • (δ g) 1 from by
          conv_lhs => rw [show (π v : R) = π v • (1 : R) from by
            rw [smul_eq_mul, mul_one]]
          rw [map_smul]]
        simp [e, TensorProduct.AlgebraTensorModule.rid_tmul, smul_smul,
          mul_comm]
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    · -- unramifiedness: the kernel only grows under base change + conj
      intro σ hσ
      have hδσ : δ σ = 1 := (h 1 0).2.1 hσ
      have hone : (δ.baseChange kk).conj e σ = 1 := by
        rw [GaloisRep.conj_apply]
        rw [show (δ.baseChange kk) σ =
          LinearMap.baseChange kk (δ σ) from rfl, hδσ]
        refine LinearMap.ext fun c => ?_
        simp
      exact hone
    · -- the quadratic condition transfers through the monoid hom
      intro g'
      have hsq : δ g' * δ g' = 1 := (h 1 0).2.2 g'
      calc (δ.baseChange kk).conj e g' * (δ.baseChange kk).conj e g'
          = (δ.baseChange kk).conj e (g' * g') := (map_mul _ _ _).symm
        _ = 1 := by
            rw [GaloisRep.conj_apply]
            rw [show (δ.baseChange kk) (g' * g') =
              LinearMap.baseChange kk (δ (g' * g')) from rfl,
              map_mul δ, hsq]
            refine LinearMap.ext fun c => ?_
            simp

/-- **Residual hardly-ramifiedness at a general odd prime** (general-`p`
analogue of `exists_residual_isHardlyRamified` in `Threeadic.lean`, same
assembly over the general-`p` residue package and the general-place
flatness/tameness transfer lemmas above; the determinant and
unramifiedness conditions are proven here directly —
`LinearMap.det_baseChange` and the base-change instance of
`IsUnramifiedAt`): the reduction of a `p`-adic hardly ramified
representation modulo the maximal ideal is mod-`p` hardly ramified over
the residue field.  The coefficient ring is only assumed to be a
nontrivial module-finite local topological `ℤ_p`-algebra (in the
intended consumer, a domain) — not free over `ℤ_p`. -/
theorem exists_residual_odd {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {R : Type u} [CommRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[p] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V]
    (hv : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified hpodd hv ρ) :
    ∃ (kk : Type u) (_ : Field kk) (_ : Finite kk) (_ : Algebra ℤ_[p] kk)
      (_ : TopologicalSpace kk) (_ : DiscreteTopology kk)
      (_ : IsTopologicalRing kk) (_ : Algebra R kk)
      (_ : ContinuousSMul R kk)
      (_ : Function.Surjective (algebraMap R kk))
      (hVbar : Module.rank kk (kk ⊗[R] V) = 2),
      IsHardlyRamified hpodd hVbar (ρ.baseChange kk) := by
  obtain ⟨kk, hField, hFinite, hAp, hTop, hDisc, hTR, hAR, hCS, hST,
    hsurj, hopen, hker, hrank⟩ := exists_residue_package_odd (p := p) V hv
  letI := hField
  letI := hFinite
  letI := hAp
  letI := hTop
  letI := hDisc
  letI := hTR
  letI := hAR
  letI := hCS
  letI := hST
  refine ⟨kk, hField, hFinite, hAp, hTop, hDisc, hTR, hAR, hCS, hsurj,
    hrank, ?_⟩
  constructor
  · -- the determinant condition maps along the residue map
    intro g
    have hdet : (ρ.baseChange kk).det g =
        algebraMap R kk (ρ.det g) := by
      show LinearMap.det ((ρ.baseChange kk) g) = _
      rw [show ((ρ.baseChange kk) g : Module.End kk (kk ⊗[R] V)) =
        LinearMap.baseChange kk (ρ g) from rfl, LinearMap.det_baseChange]
      rfl
    rw [hdet, hρ.det g, ← IsScalarTower.algebraMap_apply]
  · -- unramifiedness passes to the base change (existing instance)
    intro q hq hqq
    letI : ρ.IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat :=
      hρ.isUnramified q hq hqq
    infer_instance
  · -- flatness at `p` (general-place transfer lemma)
    exact isFlatAt_baseChange_residue_at _ kk hsurj hopen hker hρ.isFlat
  · -- tameness at `2` (transfer lemma)
    exact isTameAtTwo_baseChange_residue_res kk hρ.isTameAtTwo

end GaloisRepresentation.IsHardlyRamified
