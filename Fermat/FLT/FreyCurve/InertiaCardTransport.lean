/-
InertiaCardTransport.lean — own work for the Fermat project (not vendored
from the FLT project).

**The quantitative local-to-global inertia transport.** MazurTorsion.lean
proves the QUALITATIVE statement (`inertia_eq_bot_of_le_fixingSubgroup`):
if the image in `Γ ℚ` of the local inertia group at `q` fixes a finite
Galois extension `L/ℚ` pointwise, the ideal-inertia of every prime of
`𝓞 L` above `q` is trivial.  This file proves the QUANTITATIVE
strengthening needed by the discriminant bookkeeping of the mod-3
hardly-ramified analysis (`Fermat.FLT.GaloisRepresentation.HardlyRamified.
ModThree`): for `K/ℚ` finite Galois cut out by a group homomorphism
`u : Γ ℚ →* G₂` (i.e. `K.fixingSubgroup = u.ker`), the order of the
ideal-inertia subgroup of `Gal(K/ℚ)` at any prime `Q` over `q` divides
the order of the image under `u` of the (mapped) local inertia at `q`.

The argument (no local class field theory, no decomposition-group
surjectivity):

1. `nat_card_subgroup_map_eq_of_ker_eq`: the restriction
   `π : Γ ℚ → Gal(K/ℚ)` has kernel `K.fixingSubgroup = ker u`, so the
   image `H := π(I_q)` of the mapped local inertia `I_q` in `Gal(K/ℚ)`
   has the same cardinality as `u(I_q)` (both are quotients of `I_q` by
   the same kernel).
2. `K' := fixedField H` is fixed pointwise by `I_q`, so the Minkowski
   embedding construction — repeated here WITHOUT any Galois hypothesis
   on `K'/ℚ` as `exists_prime_over_not_mem_sq_of_le_fixingSubgroup`, in
   membership form `q ∈ Q₀'`, `q ∉ Q₀'²` — produces a prime `Q₀'` of
   `𝓞 K'` above `q` with ramification index `e(Q₀'|q) = 1`.
3. Pick a prime `Q₀` of `𝓞 K` above `Q₀'` (going-up).  Multiplicativity
   of the ramification index in the tower `ℤ ⊆ 𝓞 K' ⊆ 𝓞 K` gives
   `e(Q₀|q) = e(Q₀|Q₀')`, and `e(Q₀|Q₀') = #I_{Gal(K/K')}(Q₀)` divides
   `#Gal(K/K') = [K:K'] = #H` (Lagrange; `K/K'` IS Galois).
4. In the Galois extension `K/ℚ` the inertia order is prime-independent
   (`Ideal.card_inertia_eq_ramificationIdxIn`), so the bound at the
   distinguished prime `Q₀` is the bound at the given prime `Q`.
-/
module

public import Fermat.FLT.FreyCurve.MazurTorsion
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.Different
import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

@[expose] public section

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

open NumberField

/-- **Images under equal-kernel homomorphisms have equal cardinality**:
if `f : G →* G₁` and `g : G →* G₂` have the same kernel, then for any
subgroup `S ≤ G` the images `f(S)` and `g(S)` have the same (possibly
infinite, via `Nat.card`) cardinality.  Both are isomorphic to
`S ⧸ (ker ∩ S)` by the first isomorphism theorem applied to the
restrictions `f|_S`, `g|_S`. -/
theorem nat_card_subgroup_map_eq_of_ker_eq {G G₁ G₂ : Type*} [Group G] [Group G₁]
    [Group G₂] (f : G →* G₁) (g : G →* G₂) (h : f.ker = g.ker) (S : Subgroup G) :
    Nat.card (S.map f) = Nat.card (S.map g) := by
  have h₁ : (f.comp S.subtype).range = S.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h₂ : (g.comp S.subtype).range = S.map g := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : (f.comp S.subtype).ker = (g.comp S.subtype).ker := by
    have hmem : ∀ x : S, f x = 1 ↔ g x = 1 := fun x => by
      rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker, h]
    ext x
    simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.subtype_apply]
      using hmem x
  rw [← h₁, ← h₂,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.comp S.subtype)).toEquiv,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (g.comp S.subtype)).toEquiv,
    hk]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- **Minkowski surjectivity transport, membership form** (the
non-Galois variant of `exists_prime_over_inertia_eq_bot_of_le_fixingSubgroup`
from MazurTorsion.lean; same construction, but the conclusion is stated
as `q ∈ Q₀ ∖ Q₀²` — i.e. `e(Q₀|q) = 1` in membership form — so that no
Galois hypothesis on `L/ℚ` is needed): if the image in `G_ℚ` of the
local inertia group at `q` fixes the finite extension `L/ℚ` pointwise,
then SOME prime `Q₀` of `𝓞 L` contains `q` but not in its square.
Construction: the chosen embedding `ι : ℚᵃˡᵍ → (ℚ_q)ᵃˡᵍ` carries `L`
into the finite subextension `M := ℚ_q(ι(L))`, which the hypothesis
places inside the fixed field of the local inertia; the local node
`maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup` then makes `q`
a uniformizer of the integral closure `𝒪_M`.  Pulling the maximal ideal
of `𝒪_M` back along `ι : 𝓞 L → 𝒪_M` yields a prime `Q₀ ∋ q`; if
`q ∈ Q₀²` then `q ∈ 𝔪_M² = (q²)`, making `q` a unit of `𝒪_M` — absurd. -/
theorem exists_prime_over_not_mem_sq_of_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    [NumberField L]
    {q : ℕ} (hq : q.Prime)
    (hle : Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat)
      ≤ L.fixingSubgroup) :
    ∃ (Q₀ : Ideal (NumberField.RingOfIntegers L)) (_ : Q₀.IsPrime),
      (q : NumberField.RingOfIntegers L) ∈ Q₀ ∧
        (q : NumberField.RingOfIntegers L) ∉ Q₀ ^ 2 := by
  classical
  -- the chosen embedding of algebraic closures underlying the map of
  -- absolute Galois groups
  set f : ℚ →+* IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
      hq.toHeightOneSpectrumRingOfIntegersRat :=
    algebraMap ℚ _
  set ι : AlgebraicClosure ℚ →+* AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) :=
    AlgebraicClosure.map f
  -- a finite generating set for `L/ℚ`
  obtain ⟨s, hs⟩ := L.fg_iff_finiteType.mpr (inferInstanceAs (Algebra.FiniteType ℚ L))
  have hL : L = IntermediateField.adjoin ℚ ↑s :=
    IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ hs.symm
  -- the image field `M := ℚ_q(ι(s)) = ℚ_q(ι(L))`
  set M : IntermediateField
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    IntermediateField.adjoin _ (ι '' ↑s) with hM
  -- `ι` carries all of `L` into `M`
  have hsub : ∀ x ∈ L, ι x ∈ M := by
    intro x hx
    rw [hL] at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | algebraMap c =>
        rw [AlgebraicClosure.map_algebraMap]
        exact M.algebraMap_mem _
    | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
    | inv x hx ihx => rw [map_inv₀]; exact inv_mem ihx
    | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
  -- `M/ℚ_q` is finite: it is generated by the finite set `ι '' s` of
  -- integral (= algebraic) elements
  haveI hfdM : FiniteDimensional
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M := by
    haveI : Finite (ι '' (↑s : Set (AlgebraicClosure ℚ))) :=
      (s.finite_toSet.image ι).to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      fun x _ => Algebra.IsIntegral.isIntegral x
  -- the hypothesis places `M` inside the fixed field of the local inertia
  have hMfix : M ≤ IntermediateField.fixedField
      (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) := by
    rw [hM, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    -- `σ (ι y) = ι ((map f σ) y) = ι y` by `lift_map` and the hypothesis
    have hmem : (Field.absoluteGaloisGroup.map f) σ ∈ L.fixingSubgroup :=
      hle (Subgroup.mem_map_of_mem _ hσ)
    have hfixy : (Field.absoluteGaloisGroup.map f σ) y = y :=
      (IntermediateField.mem_fixingSubgroup_iff L ((Field.absoluteGaloisGroup.map f) σ)).mp
        hmem y (hL ▸ IntermediateField.subset_adjoin _ _ hy)
    calc σ (ι y) = ι ((Field.absoluteGaloisGroup.map f σ) y) :=
          (Field.absoluteGaloisGroup.lift_map f σ y).symm
      _ = ι y := by rw [hfixy]
  -- the local node: `q` generates the maximal ideal of `𝒪_M`
  have hmax := maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup
    hq.toHeightOneSpectrumRingOfIntegersRat M hMfix
  have hspan : IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M) =
      Ideal.span {(q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M)} := by
    rw [← hmax, maximalIdeal_adicCompletionIntegers_eq_span hq, Ideal.map_span,
      Set.image_singleton, map_natCast]
  -- the ring homomorphism `ψ : L → M` induced by `ι`
  let ψ : L →+* M :=
    { toFun := fun y => ⟨ι (y : AlgebraicClosure ℚ), hsub _ y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun a b => by
        apply Subtype.ext
        simp }
  -- `ψ` carries the ring of integers of `L` into `𝒪_M`
  have hψint : ∀ x : NumberField.RingOfIntegers L,
      ψ (algebraMap (NumberField.RingOfIntegers L) L x) ∈
        integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M := by
    intro x
    have h1 : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers L) L x) :=
      NumberField.RingOfIntegers.isIntegral_coe x
    -- promote `ψ` to a `ℤ`-algebra homomorphism with the AMBIENT `ℤ`-algebra
    -- structures (all ring homs from `ℤ` agree, so `commutes'` is by
    -- uniqueness of `ℤ →+* ·`)
    let ψℤ : L →ₐ[ℤ] M :=
      { toRingHom := ψ
        commutes' := fun n => by
          rw [RingHom.eq_intCast' (algebraMap ℤ L), RingHom.eq_intCast' (algebraMap ℤ M)]
          exact map_intCast ψ n }
    have h2 : IsIntegral ℤ (ψ (algebraMap (NumberField.RingOfIntegers L) L x)) :=
      h1.map ψℤ
    -- pass from `ℤ`-integrality to `𝒪ᵥ`-integrality by pushing the monic
    -- witness through `ℤ → 𝒪ᵥ` (instance-agnostic: all ring homs from `ℤ`
    -- agree)
    obtain ⟨p, hp, hpeval⟩ := h2
    refine ⟨p.map (Int.castRingHom
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, Subsingleton.elim
      ((algebraMap
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M).comp
        (Int.castRingHom
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat)))
      (algebraMap ℤ M)]
    exact hpeval
  let φ : NumberField.RingOfIntegers L →+*
      IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M :=
    (ψ.comp (algebraMap (NumberField.RingOfIntegers L) L)).codRestrict
      (integralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M) hψint
  -- the embedding prime: the pullback of the maximal ideal of `𝒪_M`
  haveI hmaxprime : (IsLocalRing.maximalIdeal
      (IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M)).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  refine ⟨Ideal.comap φ (IsLocalRing.maximalIdeal _), Ideal.IsPrime.comap φ, ?_, ?_⟩
  · -- `q` lands in the pullback: `φ q = q ∈ 𝔪_M = (q)`
    rw [Ideal.mem_comap, map_natCast, hspan]
    exact Ideal.mem_span_singleton_self _
  -- `q ∉ Q₀²`: otherwise `φ q = q ∈ 𝔪_M² = (q²)`, making `q` a unit
  intro hqQ2
  have hcomap2 : (Ideal.comap φ (IsLocalRing.maximalIdeal _)) ^ 2 ≤
      Ideal.comap φ ((IsLocalRing.maximalIdeal _) ^ 2) := by
    rw [pow_two, pow_two]
    exact Ideal.mul_le.mpr fun r hr t ht => Ideal.mem_comap.mpr
      (by rw [map_mul]; exact Ideal.mul_mem_mul hr ht)
  have hφq := Ideal.mem_comap.mp (hcomap2 hqQ2)
  rw [map_natCast, hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hφq
  obtain ⟨c, hc⟩ := hφq
  -- `q ≠ 0` in `𝒪_M` (its image in `(ℚ_q)ᵃˡᵍ` is `q ≠ 0` by char zero)
  haveI : CharZero (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat)) :=
    charZero_of_injective_algebraMap (algebraMap
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) _).injective
  have hq0 : ((q : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun z => (algebraMap M (AlgebraicClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))
      ((algebraMap (IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M) M) z))) h0
    simp only [map_natCast, map_zero] at h1
    exact Nat.cast_ne_zero.mpr hq.ne_zero h1
  -- cancel one factor of `q`: `q · c = 1`
  have hcancel : (q : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M) * c = 1 := by
    have hmul : (q : IntegralClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat) M) *
        ((q : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) M) * c) =
        (q : IntegralClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
            hq.toHeightOneSpectrumRingOfIntegersRat) M) * 1 := by
      rw [mul_one, ← mul_assoc, ← pow_two]
      exact hc.symm
    exact mul_left_cancel₀ hq0 hmul
  -- but `q` lies in the proper maximal ideal — contradiction
  have hqmem : (q : IntegralClosure
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat) M) ∈
      IsLocalRing.maximalIdeal _ := by
    rw [hspan]; exact Ideal.mem_span_singleton_self _
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hqmem
      (isUnit_iff_exists.mpr ⟨c, hcancel, by rwa [mul_comm] at hcancel⟩))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **The quantitative local-to-global inertia transport** (the
strengthening of `inertia_eq_bot_of_le_fixingSubgroup` from
"image trivial ⇒ inertia trivial" to "inertia order divides the image
order"): for a Galois number field `K` cut out by a group homomorphism
`u : Γ ℚ →* G₂` (`K.fixingSubgroup = u.ker`) and any prime `Q` of `𝓞 K`
over `q`, the order of the ideal-inertia subgroup of `Gal(K/ℚ)` at `Q`
divides any multiple `n` of the order of the image under `u` of the
mapped local inertia at `q`.  See the file docstring for the proof
outline. -/
theorem inertia_card_dvd_of_card_map_localInertiaGroup_dvd
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsGalois ℚ K]
    {G₂ : Type*} [Group G₂] (u : Γ ℚ →* G₂)
    (hfix : K.fixingSubgroup = u.ker)
    {q : ℕ} (hq : q.Prime)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : ((q : ℕ) : NumberField.RingOfIntegers K) ∈ Q)
    (n : ℕ)
    (hn : Nat.card (Subgroup.map u
      (Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
          hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
        (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat))) ∣ n) :
    Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) ∣ n := by
  classical
  set Iloc : Subgroup (Γ ℚ) :=
    Subgroup.map (Field.absoluteGaloisGroup.map (algebraMap ℚ
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
        hq.toHeightOneSpectrumRingOfIntegersRat))).toMonoidHom
      (localInertiaGroup hq.toHeightOneSpectrumRingOfIntegersRat) with hIloc
  set π : (Γ ℚ) →* (K ≃ₐ[ℚ] K) := AlgEquiv.restrictNormalHom K with hπdef
  -- (1) equal kernels: the images of `Iloc` under `π` and `u` have the
  -- same cardinality
  have hcard_eq : Nat.card (Subgroup.map π Iloc) = Nat.card (Subgroup.map u Iloc) :=
    nat_card_subgroup_map_eq_of_ker_eq π u
      (by rw [hπdef, IntermediateField.restrictNormalHom_ker, hfix]) Iloc
  -- (2) the image subgroup and its fixed field
  set H : Subgroup (K ≃ₐ[ℚ] K) := Subgroup.map π Iloc with hHdef
  set K' : IntermediateField ℚ K := IntermediateField.fixedField H with hK'def
  -- (3) `Iloc` fixes the ambient copy `K'.map K.val` of `K'` pointwise
  have hle : Iloc ≤ (K'.map K.val).fixingSubgroup := by
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x hx
    rw [IntermediateField.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hπσ : π σ ∈ H := hHdef ▸ Subgroup.mem_map_of_mem π hσ
    have hfixy : π σ y = y := by
      rw [hK'def, IntermediateField.mem_fixedField_iff] at hy
      exact hy (π σ) hπσ
    calc σ (K.val y) = K.val (π σ y) :=
          (AlgEquiv.restrictNormalHom_apply K σ y).symm
      _ = K.val y := by rw [hfixy]
  -- (4) instances for the ambient copy of `K'`, and the Minkowski prime
  haveI hfdmap : FiniteDimensional ℚ (K'.map K.val) :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap K' K.val).toLinearEquiv
  haveI hczmap : CharZero (K'.map K.val) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (K'.map K.val)).injective
  haveI hnfmap : NumberField (K'.map K.val) := { }
  obtain ⟨P₀, hP₀prime, hP₀mem, hP₀nsq⟩ :=
    exists_prime_over_not_mem_sq_of_le_fixingSubgroup (K'.map K.val) hq hle
  -- (5) transport `P₀` to a prime `P'` of `𝓞 K'` along the canonical
  -- isomorphism `K' ≃ₐ[ℚ] K'.map K.val`
  set ε : NumberField.RingOfIntegers K' ≃+* NumberField.RingOfIntegers (K'.map K.val) :=
    NumberField.RingOfIntegers.mapRingEquiv
      (IntermediateField.equivMap K' K.val).toRingEquiv
  set P' : Ideal (NumberField.RingOfIntegers K') := P₀.comap ε with hP'def
  haveI hP'prime : P'.IsPrime := hP₀prime.comap _
  have hP'mem : ((q : ℕ) : NumberField.RingOfIntegers K') ∈ P' := by
    rw [hP'def, Ideal.mem_comap, map_natCast]
    exact hP₀mem
  have hP'nsq : ((q : ℕ) : NumberField.RingOfIntegers K') ∉ P' ^ 2 := by
    intro hmem2
    apply hP₀nsq
    have hPmap : P' = Ideal.map ε.symm P₀ := by
      rw [hP'def, Ideal.map_symm]
    rw [hPmap, ← Ideal.map_pow] at hmem2
    obtain ⟨x, hx, hxq⟩ := Ideal.mem_map_iff_of_surjective _ ε.symm.surjective |>.mp hmem2
    have hxval : x = ((q : ℕ) : NumberField.RingOfIntegers (K'.map K.val)) := by
      have := congrArg ε hxq
      rwa [RingEquiv.apply_symm_apply, map_natCast] at this
    rwa [hxval] at hx
  -- (6) the going-up prime `Q₀` of `𝓞 K` above `P'`
  haveI hfaith : FaithfulSMul (NumberField.RingOfIntegers K')
      (NumberField.RingOfIntegers K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (NumberField.RingOfIntegers.algebraMap.injective ↥K' ↥K)
  obtain ⟨⟨Q₀, hQ₀prime, hQ₀lies⟩⟩ :=
    (inferInstance : Nonempty (P'.primesOver (NumberField.RingOfIntegers K)))
  haveI := hQ₀prime
  haveI := hQ₀lies
  -- (7) the arithmetic bookkeeping at `q`
  have hqZ : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hq
  have hqne : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  haveI hsp : (Ideal.span {((q : ℕ) : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hqZ
  haveI hliesQ : Q.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff hQ.ne_top hqZ).mpr (by exact_mod_cast hmem)
  haveI hliesP' : P'.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff hP'prime.ne_top hqZ).mpr (by exact_mod_cast hP'mem)
  haveI hliesQ₀ : Q₀.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) :=
    Ideal.LiesOver.trans Q₀ P' (Ideal.span {((q : ℕ) : ℤ)})
  -- (8) `#I(Q) = ramificationIdxIn = e(Q₀|ℤ)` (prime-independence in the
  -- Galois extension `K/ℚ`)
  haveI := IsGaloisGroup.of_isFractionRing (K ≃ₐ[ℚ] K) ℤ
    (NumberField.RingOfIntegers K) ℚ ↥K
  have hQcard : Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) =
      Ideal.ramificationIdxIn (Ideal.span {((q : ℕ) : ℤ)})
        (NumberField.RingOfIntegers K) :=
    Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {((q : ℕ) : ℤ)}) Q
  have hIn : Ideal.ramificationIdxIn (Ideal.span {((q : ℕ) : ℤ)})
      (NumberField.RingOfIntegers K) = Q₀.ramificationIdx ℤ :=
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {((q : ℕ) : ℤ)}) Q₀
      (K ≃ₐ[ℚ] K)
  -- (9) `e(P'|ℤ) = 1` from `q ∈ P' ∖ P'²`
  have hP'e1 : P'.ramificationIdx ℤ = 1 := by
    have hple : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K'))
        (Ideal.span {((q : ℕ) : ℤ)}) ≤ P' := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_le,
        Set.singleton_subset_iff]
      exact_mod_cast hP'mem
    have h1 : Ideal.ramificationIdx' (Ideal.span {((q : ℕ) : ℤ)}) P' = 1 := by
      by_contra hne1
      have hsq := (Ideal.ramificationIdx'_ne_one_iff hple).mp hne1
      apply hP'nsq
      refine hsq ?_
      have : algebraMap ℤ (NumberField.RingOfIntegers K') ((q : ℕ) : ℤ) ∈
          Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K'))
            (Ideal.span {((q : ℕ) : ℤ)}) :=
        Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
      simpa using this
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {((q : ℕ) : ℤ)})
      P' hqne]
    exact h1
  -- (10) the tower `ℤ ⊆ 𝓞 K' ⊆ 𝓞 K`: `e(Q₀|ℤ) = e(Q₀|𝓞 K')`
  haveI : IsScalarTower ℤ (NumberField.RingOfIntegers K')
      (NumberField.RingOfIntegers K) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Module.Finite (NumberField.RingOfIntegers K')
      (NumberField.RingOfIntegers K) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  have htower : Q₀.ramificationIdx ℤ =
      P'.ramificationIdx ℤ * Q₀.ramificationIdx (NumberField.RingOfIntegers K') :=
    Ideal.ramificationIdx_tower P' Q₀
  -- (11) `e(Q₀|𝓞 K') = #I(Q₀)` over `K'`, which divides `#Gal(K/K') = #H`
  haveI := IsGaloisGroup.of_isFractionRing (K ≃ₐ[K'] K)
    (NumberField.RingOfIntegers K') (NumberField.RingOfIntegers K) ↥K' ↥K
  have hQ₀card : Nat.card (Q₀.inertia (K ≃ₐ[K'] K)) =
      Q₀.ramificationIdx (NumberField.RingOfIntegers K') := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn P' Q₀,
      Ideal.ramificationIdxIn_eq_ramificationIdx P' Q₀ (K ≃ₐ[K'] K)]
  have hLag : Nat.card (Q₀.inertia (K ≃ₐ[K'] K)) ∣ Nat.card (K ≃ₐ[K'] K) :=
    Subgroup.card_subgroup_dvd_card (Q₀.inertia (K ≃ₐ[K'] K))
  have hcardGal : Nat.card (K ≃ₐ[K'] K) = Nat.card H := by
    rw [IsGalois.card_aut_eq_finrank ↥K' ↥K, hK'def,
      IntermediateField.finrank_fixedField_eq_card]
  -- assemble
  have hchain : Nat.card (Q.inertia (K ≃ₐ[ℚ] K)) =
      Q₀.ramificationIdx (NumberField.RingOfIntegers K') := by
    rw [hQcard, hIn, htower, hP'e1, one_mul]
  rw [hchain, ← hQ₀card]
  exact (hLag.trans (dvd_of_eq (hcardGal.trans hcard_eq))).trans hn

/-! ## Automorphism-invariance of the different ideal

The transport input to the Fontaine-at-`3` conjugacy reduction in
`Fermat.FLT.GaloisRepresentation.HardlyRamified.ModThree`: an
`A`-algebra automorphism of `B` fixes `differentIdeal A B`, because the
trace form is invariant under the induced automorphism of the fraction
field (`Algebra.trace_eq_of_algEquiv`), so the automorphism permutes
the trace-dual lattice `(traceDual A K 1)` and hence fixes
`𝔡 = (1 / traceDual A K 1) ∩ B`. -/

section DifferentInvariance

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain A]
  [Algebra A B] [IsIntegrallyClosed A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]

omit [IsIntegrallyClosed A] in
/-- One inclusion of the automorphism-invariance of the different
ideal: `g(𝔡_{B/A}) ≤ 𝔡_{B/A}` for an `A`-algebra automorphism `g` of
`B`.  Unfolding the definition, `x ∈ 𝔡` iff `x · y ∈ B` for every `y`
in the trace-dual lattice `T := (traceDual A K 1)`; for such `x` and
`y ∈ T`, the extension `ĝ` of `g` to the fraction field satisfies
`ĝ⁻¹ y ∈ T` (the trace form is `ĝ`-invariant), so
`g x · y = ĝ(x · ĝ⁻¹ y) ∈ ĝ(B) = B`. -/
theorem map_differentIdeal_le_of_algEquiv (g : B ≃ₐ[A] B) :
    (differentIdeal A B).map g ≤ differentIdeal A B := by
  classical
  set K := FractionRing A
  set L := FractionRing B
  -- the extension of `g` to the fraction field
  set ĝ : L ≃ₐ[K] L := IsFractionRing.fieldEquivOfAlgEquiv K L L g with hĝdef
  have hĝalg : ∀ b : B, ĝ (algebraMap B L b) = algebraMap B L (g b) := fun b =>
    IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K L L g b
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap]
  -- unfold the definition of the different ideal on both sides
  have hx' : algebraMap B L x ∈
      (1 / Submodule.traceDual A K 1 : Submodule B L) := hx
  show algebraMap B L (g x) ∈ (1 / Submodule.traceDual A K 1 : Submodule B L)
  rw [Submodule.mem_div_iff_forall_mul_mem] at hx' ⊢
  intro y hy
  -- `ĝ⁻¹ y` is again in the trace-dual lattice
  have hy' : ĝ.symm y ∈ Submodule.traceDual A K (1 : Submodule B L) := by
    rw [Submodule.mem_traceDual] at hy ⊢
    intro a ha
    rw [Submodule.one_eq_range, LinearMap.mem_range] at ha
    obtain ⟨b, rfl⟩ := ha
    have htr : Algebra.traceForm K L (ĝ.symm y) (Algebra.linearMap B L b) =
        Algebra.traceForm K L y (algebraMap B L (g b)) := by
      rw [Algebra.traceForm_apply, Algebra.traceForm_apply,
        ← Algebra.trace_eq_of_algEquiv ĝ, map_mul,
        AlgEquiv.apply_symm_apply]
      congr 1
      exact congrArg (y * ·) (hĝalg b)
    rw [htr]
    exact hy _ (by rw [Submodule.one_eq_range]; exact ⟨g b, rfl⟩)
  -- transport the product back through `ĝ`
  have hmem := hx' (ĝ.symm y) hy'
  rw [Submodule.one_eq_range, LinearMap.mem_range] at hmem ⊢
  obtain ⟨c, hc⟩ := hmem
  refine ⟨g c, ?_⟩
  have h3 : ĝ (algebraMap B L c) = algebraMap B L (g x) * y := by
    have h4 := congrArg ĝ hc
    rw [Algebra.linearMap_apply] at h4
    rw [h4, map_mul, AlgEquiv.apply_symm_apply, hĝalg x]
  rw [Algebra.linearMap_apply, ← hĝalg c, h3]

omit [IsIntegrallyClosed A] in
/-- **Automorphism-invariance of the different ideal**: an `A`-algebra
automorphism of `B` fixes `differentIdeal A B`.  Both inclusions come
from `map_differentIdeal_le_of_algEquiv` (applied to `g` and `g⁻¹`). -/
theorem map_differentIdeal_eq_of_algEquiv (g : B ≃ₐ[A] B) :
    (differentIdeal A B).map g = differentIdeal A B := by
  refine le_antisymm (map_differentIdeal_le_of_algEquiv g) fun x hx => ?_
  have h1 : g.symm x ∈ differentIdeal A B :=
    map_differentIdeal_le_of_algEquiv g.symm (Ideal.mem_map_of_mem _ hx)
  have h2 : g (g.symm x) ∈ (differentIdeal A B).map g :=
    Ideal.mem_map_of_mem _ h1
  rwa [AlgEquiv.apply_symm_apply] at h2

end DifferentInvariance

open scoped Pointwise in
/-- **Automorphism-invariance of the different ideal of a number
field**, in the pointwise-action form consumed by the Fontaine-at-`3`
conjugacy reduction: a `ℚ`-automorphism `σ` of a number field `F`
fixes `𝔡_{F/ℚ}` under the pointwise action of `Gal(F/ℚ)` on ideals of
`𝓞 F`. -/
theorem smul_differentIdeal_eq {F : Type*} [Field F] [NumberField F]
    (σ : F ≃ₐ[ℚ] F) :
    σ • differentIdeal ℤ (NumberField.RingOfIntegers F) =
      differentIdeal ℤ (NumberField.RingOfIntegers F) := by
  -- the automorphism of `𝓞 F` induced by `σ`, as a `ℤ`-algebra
  -- automorphism
  let g : NumberField.RingOfIntegers F ≃ₐ[ℤ] NumberField.RingOfIntegers F :=
    AlgEquiv.ofRingEquiv (f := NumberField.RingOfIntegers.mapRingEquiv
      (σ : F ≃+* F))
      (fun n => by
        rw [algebraMap_int_eq]
        exact map_intCast _ n)
  have h1 : σ • differentIdeal ℤ (NumberField.RingOfIntegers F) =
      (differentIdeal ℤ (NumberField.RingOfIntegers F)).map g := rfl
  rw [h1, map_differentIdeal_eq_of_algEquiv]
