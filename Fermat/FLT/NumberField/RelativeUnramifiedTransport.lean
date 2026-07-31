/-
RelativeUnramifiedTransport.lean — own work for the Fermat project (not
vendored from the FLT project).

**The `F`-level inertia dictionary, run inside an ARBITRARY algebraic closure.**

`HardlyRamified/HilbertModularity.lean` proves the relative inertia dictionary
`isUnramifiedAt_of_hilbertInertiaTrivialAt`: for a number field `F`, a finite
Galois `K ⊆ Fᵃˡᵍ` whose local inertia at a place `w` acts trivially is
unramified over `𝓞 F` at every prime above `w`.  It is stated inside Lean's
CANONICAL `AlgebraicClosure F`, because that is where `Γ F` lives.

Consumers, however, meet `K` inside a DIFFERENT algebraic closure: in
`Modularity/Interface.lean` the whole Galois dictionary (`Γℚ`, `ker χ`,
`localInertiaGroup`, `muSubfield p`) is run inside `AlgebraicClosure ℚ`, and the
extension whose unramifiedness is wanted is an `IntermediateField (muSubfield p)
(AlgebraicClosure ℚ)`.  This module supplies the three bridges:

* `Field.absoluteGaloisGroup.exists_conj_localInertiaGroup` — the
  ALL-PLACES form of `GaloisRepTransport.lean`'s
  `Field.absoluteGaloisGroup.exists_finset_conj_localInertiaGroup_le`.  That
  theorem carries a finite exceptional set `T` because it is stated relative to
  a finite set `S` of places of the base to be avoided; with no `S` there is no
  exception, and the proof below is the same one with the bookkeeping deleted.
  The exceptional set is fatal for the use below, which needs the comparison at
  the single place `w` it is handed — including, in the cyclotomic application,
  the ramified place above `p`.
* `GaloisRepresentation.isUnramifiedAt_of_hilbertInertiaTrivialAt_ambient` —
  the inertia dictionary transported along an `F`-isomorphism
  `ee : Fᵃˡᵍ ≃ₐ[F] Ω` of ambient algebraic closures, with the inertia
  hypothesis phrased as an equation in `Ω`.
* `GaloisRepresentation.exists_conj_localInertia_restrict_of_algebraicClosureEquiv`
  — the group-side companion: the action on `Kᵃˡᵍ` of a local inertia element at
  a place `w` of `L`, read through `ee`, IS a `Γ K`-conjugate of the image of a
  local inertia element of the base field `K`.  This is what lets a hypothesis
  stated over `K` (over `ℚ`, in the application) be applied to an inertia
  element of `L`.
-/

module

-- `isUnramifiedAt_of_hilbertInertiaTrivialAt` and `HilbertInertiaTrivialAt`.
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.HilbertModularity
-- `NumberField.isUnramifiedAt_of_algEquiv`.
public import Fermat.FLT.NumberField.CyclotomicModelTransport
-- `Field.absoluteGaloisGroup.exists_conj_map_comp'` and the completion-map
-- machinery its arithmetic sibling uses.
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRepTransport

@[expose] public section

open IsDedekindDomain
open scoped NumberField

universe u v

section AllPlaces

variable (K : Type u) [Field K] [NumberField K] (L : Type v) [Field L] [NumberField L]

/-- **Local inertia over a finite extension comes from local inertia over the
place below it — at EVERY place** (PROVEN; the all-places form of
`Field.absoluteGaloisGroup.exists_finset_conj_localInertiaGroup_le`).

That theorem excludes a finite set `T` of places of `L`, namely the ones lying
over a prescribed finite set `S` of places of `K`; taking `S = ∅` makes `T`
empty, and the proof below is that theorem's proof with the `S`/`T`
bookkeeping deleted.  The place of `K` produced is `w.under (𝓞 K)`, and the
conjugator `τ` compares the two factorisations `K → K_v → L_w` and
`K → L → L_w` of the same embedding. -/
theorem Field.absoluteGaloisGroup.exists_conj_localInertiaGroup [Algebra K L]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    ∃ (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
      (τ : Field.absoluteGaloisGroup K),
      ∀ ι ∈ localInertiaGroup w, ∃ κ ∈ localInertiaGroup v,
        Field.absoluteGaloisGroup.map
            ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L)) ι =
          τ * Field.absoluteGaloisGroup.map
            (algebraMap K (v.adicCompletion K)) κ * τ⁻¹ := by
  classical
  set v : HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    w.under (NumberField.RingOfIntegers K) with hvdef
  have hcomm : ∀ a : NumberField.RingOfIntegers K,
      (algebraMap K L) (algebraMap (NumberField.RingOfIntegers K) K a)
        = algebraMap (NumberField.RingOfIntegers L) L
            (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) a) := by
    intro a
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hmem : v.asIdeal ≤ Ideal.comap
      (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L))
      w.asIdeal := le_rfl
  have hcompl : ∀ s : NumberField.RingOfIntegers K, s ∉ v.asIdeal →
      algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) s
        ∉ w.asIdeal := fun _ hs => hs
  have hψ : UniformContinuous
      (WithVal.map (v.valuation K) (w.valuation L) (algebraMap K L)) :=
    WithVal.uniformContinuous_map_of_le _ _
      (IsDedekindDomain.HeightOneSpectrum.valuation_surjective K v) _
      (fun x hx => IsDedekindDomain.HeightOneSpectrum.valuation_map_le_of_le_one v w _ _
        hcomm hmem hcompl x hx)
  have hint : ∀ x ∈ v.adicCompletionIntegers K,
      IsDedekindDomain.HeightOneSpectrum.adicCompletionMap v w (algebraMap K L) hψ x
        ∈ w.adicCompletionIntegers L :=
    fun x hx => IsDedekindDomain.HeightOneSpectrum.adicCompletionMap_mem_integers v w _ hψ
      _ hcomm hx
  obtain ⟨τ, hτ⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp'
    (algebraMap K (v.adicCompletion K))
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionMap v w (algebraMap K L) hψ)
    ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L))
    (RingHom.ext fun x =>
      IsDedekindDomain.HeightOneSpectrum.adicCompletionMap_coe v w (algebraMap K L) hψ x)
  exact ⟨v, τ, fun ι hι =>
    ⟨Field.absoluteGaloisGroup.map _ ι,
      Field.absoluteGaloisGroup.map_mem_localInertiaGroup v w _ hint ι hι, hτ ι⟩⟩

end AllPlaces

namespace GaloisRepresentation

/-- **The relative inertia dictionary inside an ARBITRARY algebraic closure**
(PROVEN; transport of `isUnramifiedAt_of_hilbertInertiaTrivialAt` along an
`F`-isomorphism `ee : Fᵃˡᵍ ≃ₐ[F] Ω` of ambient algebraic closures).

`ee` is a HYPOTHESIS rather than `IsAlgClosure.equiv` built inside, for the
reason recorded at `NumberField.exists_unramifiedAbelian_of_algebraicClosureEquiv`:
with it opaque no defeq check can try to unfold `IsAlgClosed.lift`.

The inertia hypothesis is stated as an equation in `Ω` — "the local inertia at
`w`, read through `ee`, fixes `K` pointwise" — which is the form a consumer
working inside `Ω` can supply without ever mentioning `Fᵃˡᵍ`. -/
theorem isUnramifiedAt_of_hilbertInertiaTrivialAt_ambient
    (F : Type u) [Field F] [NumberField F]
    {Ω : Type v} [Field Ω] [Algebra F Ω]
    (ee : AlgebraicClosure F ≃ₐ[F] Ω)
    (K : IntermediateField F Ω) [FiniteDimensional F K] [IsGalois F K] [NumberField ↥K]
    (w : HeightOneSpectrum (𝓞 F))
    (hinert : ∀ n ∈ localInertiaGroup w, ∀ y ∈ K,
      ee (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F)) n (ee.symm y)) = y)
    (P : Ideal (𝓞 ↥K)) [P.IsPrime] [P.LiesOver w.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 F) P := by
  classical
  -- the model of `K` inside the canonical algebraic closure
  set K' : IntermediateField F (AlgebraicClosure F) := K.map ee.symm.toAlgHom with hK'def
  let eK : ↥K ≃ₐ[F] ↥K' := IntermediateField.intermediateFieldMap ee.symm K
  haveI : FiniteDimensional F ↥K' := Module.Finite.equiv eK.toLinearEquiv
  haveI : IsGalois F ↥K' := IsGalois.of_algEquiv eK
  haveI : FiniteDimensional ℚ ↥K' := Module.Finite.trans (R := ℚ) F ↥K'
  haveI : NumberField ↥K' := ⟨⟩
  -- the inertia hypothesis, back inside `Fᵃˡᵍ`
  have hinert' : HilbertInertiaTrivialAt w K'.fixingSubgroup := by
    intro n hn
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr ?_
    intro z hz
    rw [hK'def, IntermediateField.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    refine ee.injective ?_
    show ee (Field.absoluteGaloisGroup.map (algebraMap F (w.adicCompletion F)) n
      (ee.symm y)) = ee (ee.symm y)
    rw [AlgEquiv.apply_symm_apply]
    exact hinert n hn y hy
  -- the prime, moved across
  let f : (𝓞 ↥K') ≃ₐ[𝓞 F] (𝓞 ↥K) := NumberField.RingOfIntegers.mapAlgEquiv eK.symm
  set P' : Ideal (𝓞 ↥K') := Ideal.comap (f : 𝓞 ↥K' →+* 𝓞 ↥K) P with hP'def
  haveI : P'.IsPrime := Ideal.comap_isPrime _ _
  haveI : P'.LiesOver w.asIdeal := by
    refine ⟨?_⟩
    have hover : w.asIdeal = Ideal.comap (algebraMap (𝓞 F) (𝓞 ↥K)) P :=
      ‹P.LiesOver w.asIdeal›.over
    rw [hover, hP'def, Ideal.under, Ideal.comap_comap]
    congr 1
    exact (RingHom.ext fun x => (f.commutes x).symm)
  exact NumberField.isUnramifiedAt_of_algEquiv f P' P rfl
    (isUnramifiedAt_of_hilbertInertiaTrivialAt F K' w hinert' P')

/-- **A local inertia element of `L`, read inside an ambient algebraic closure of
the base `K`, is a `Γ K`-conjugate of a local inertia element of `K`** (PROVEN
over `Field.absoluteGaloisGroup.exists_conj_localInertiaGroup` and
`Field.absoluteGaloisGroup.exists_conj_map_comp'`).

The `L`-automorphism of `Kᵃˡᵍ` obtained by conjugating the image of
`n ∈ localInertiaGroup w` through `ee` is exhibited as `σ * κ̃ * σ⁻¹` with `κ` in
the local inertia of `K` at the place below `w`.  Two conjugations are
composed: the one comparing the two factorisations of `K → L_w` (which is
`exists_conj_map_comp'`), and the one comparing the arbitrary `ee` with the
chosen embedding `Kᵃˡᵍ → Lᵃˡᵍ` underlying
`Field.absoluteGaloisGroup.map (algebraMap K L)` — the latter composite is an
algebra endomorphism of `Kᵃˡᵍ`, hence bijective, hence itself an element of
`Γ K`. -/
theorem exists_conj_localInertia_restrict_of_algebraicClosureEquiv
    (K : Type u) [Field K] [NumberField K] (L : Type v) [Field L] [NumberField L]
    [Algebra K L] [Algebra L (AlgebraicClosure K)]
    [IsScalarTower K L (AlgebraicClosure K)]
    (ee : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure K)
    (w : HeightOneSpectrum (𝓞 L))
    (n : Field.absoluteGaloisGroup (w.adicCompletion L)) (hn : n ∈ localInertiaGroup w) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (σ : Field.absoluteGaloisGroup K)
      (κ : Field.absoluteGaloisGroup (v.adicCompletion K)), κ ∈ localInertiaGroup v ∧
      ∀ x : AlgebraicClosure K,
        ee (Field.absoluteGaloisGroup.map (algebraMap L (w.adicCompletion L)) n (ee.symm x)) =
          (σ * Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K)) κ * σ⁻¹) x := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : Field.absoluteGaloisGroup L,
      Field.absoluteGaloisGroup.map (algebraMap L (w.adicCompletion L)) n = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Field.absoluteGaloisGroup K,
      Field.absoluteGaloisGroup.map (algebraMap K L) a = b := ⟨_, rfl⟩
  rw [ha]
  -- the comparison of the two ways of reading `n` into `Γ K`
  obtain ⟨v, τ, hτ⟩ :=
    Field.absoluteGaloisGroup.exists_conj_localInertiaGroup K L w
  obtain ⟨κ, hκ, hmain⟩ := hτ n hn
  obtain ⟨τ₀, hτ₀⟩ := Field.absoluteGaloisGroup.exists_conj_map_comp' (algebraMap K L)
    (algebraMap L (w.adicCompletion L))
    ((algebraMap L (w.adicCompletion L)).comp (algebraMap K L)) rfl
  have hbconj : b = τ₀⁻¹ * (τ * Field.absoluteGaloisGroup.map
      (algebraMap K (v.adicCompletion K)) κ * τ⁻¹) * τ₀ := by
    have h1 := hτ₀ n
    rw [ha, hb, hmain] at h1
    rw [h1]
    group
  -- `δ`: the chosen embedding `Kᵃˡᵍ → Lᵃˡᵍ`, followed by `ee`
  let δ₀ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K :=
    { toFun := fun x => ee (AlgebraicClosure.map (algebraMap K L) x)
      map_one' := by simp
      map_mul' := fun x y => by simp
      map_zero' := by simp
      map_add' := fun x y => by simp
      commutes' := fun q => by
        show ee (AlgebraicClosure.map (algebraMap K L)
          (algebraMap K (AlgebraicClosure K) q)) = _
        rw [AlgebraicClosure.map_algebraMap, AlgEquiv.commutes,
          ← IsScalarTower.algebraMap_apply K L (AlgebraicClosure K)] }
  let δ : Field.absoluteGaloisGroup K :=
    AlgEquiv.ofBijective δ₀ (Algebra.IsAlgebraic.algHom_bijective δ₀)
  have hδ : ∀ x : AlgebraicClosure K,
      δ x = ee (AlgebraicClosure.map (algebraMap K L) x) := fun _ => rfl
  -- `δ` intertwines `b` with the transported action of `a`
  have hkey : ∀ x : AlgebraicClosure K, ee (a (ee.symm (δ x))) = δ (b x) := by
    intro x
    have h2 : ee.symm (δ x) = AlgebraicClosure.map (algebraMap K L) x := by
      rw [hδ]; exact ee.symm_apply_apply _
    rw [h2, hδ, ← hb]
    exact congrArg ee (Field.absoluteGaloisGroup.lift_map (algebraMap K L) a x).symm
  have hδinv : ∀ x : AlgebraicClosure K, δ (δ⁻¹ x) = x := by
    intro x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel]
    rfl
  refine ⟨v, δ * (τ₀⁻¹ * τ), κ, hκ, fun x => ?_⟩
  have h2 : δ * (τ₀⁻¹ * τ) * Field.absoluteGaloisGroup.map
      (algebraMap K (v.adicCompletion K)) κ * (δ * (τ₀⁻¹ * τ))⁻¹ = δ * b * δ⁻¹ := by
    rw [hbconj]; group
  rw [h2, show (δ * b * δ⁻¹) x = δ (b (δ⁻¹ x)) from rfl, ← hkey (δ⁻¹ x), hδinv]

end GaloisRepresentation
