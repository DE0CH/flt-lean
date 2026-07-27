/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Framed descent: rebuilding a framed representation over a subring

Two purely FORMAL steps of Carayol's Théorème 1, stated over a VARIABLE base
number field and factored out of both `HardlyRamified/HilbertModularity.lean`
and `HardlyRamified/Deformation.lean`.

* `exists_framedGaloisRep_toMatrix'_map_eq_of_forall_mem` — a family of
  matrices over `B` that is unital, multiplicative, continuous entrywise and
  has all its entries in a subring `C ⊆ B` IS the entrywise image of a genuine
  `FramedGaloisRep F C (Fin 2)`.
* `exists_conj_baseChange_of_matrix` — an invertible `E` over `B`
  intertwining the `ψ`-image of a framed representation over `R` with one over
  `B` exhibits the base change `ρ ⊗ B` as the second, after the change of
  framing given by `E`.

Neither statement involves any arithmetic, any local condition or any trace
subring: they are the plumbing that turns Carayol's matrix-level conclusion
into the `∃ ρ' ∃ e` shape the deformation files use.

## Why this module exists

Both lemmas were written twice — hard-coded to `ℚ` in `Deformation.lean` and
in an `F`-variable copy in `HilbertModularity.lean` — because
`Deformation.lean` `public import`s `HilbertModularity.lean` and so cannot be
imported back from it. Nothing in either statement or proof mentions the base
field beyond carrying it as a parameter, so the copies are removed by putting
the `F`-variable versions HERE, upstream of both. The `ℚ`-level call sites
instantiate `F := ℚ` by unification and are otherwise untouched.

The module deliberately imports only `GaloisRep.lean` and mathlib, so it adds
nothing to the import cone of either consumer.
-/

@[expose] public section

open scoped NumberField

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

/-- **A matrix-valued representation with entries in a subring descends to
that subring** (PROVEN 2026-07-26).

A family of matrices `Φ : Γ F → M₂(B)` that is unital, multiplicative,
continuous entrywise, and whose entries all lie in a subring `C ⊆ B`, is the
entrywise image of a genuine `FramedGaloisRep F C (Fin 2)`.

Proof. The entrywise corestriction `G g := ⟨Φ g i j, _⟩` is a monoid
homomorphism into `M₂(C)` because `Matrix.map` along the injective inclusion
`C.subtype` reflects both the unit and the product. Continuity is the only
delicate point, because `GaloisRep` demands continuity INTO `Module.End C (C²)`
for the MODULE topology, which is the FINEST topology making the module
topological — so maps into it are not continuous for free. It is obtained by
factoring through matrices: `M₂(C)` carries the module topology, being a finite
product of copies of `C`, so the `C`-linear `Matrix.toLin'` out of it is
automatically continuous. -/
theorem exists_framedGaloisRep_toMatrix'_map_eq_of_forall_mem
    {F : Type*} [Field F] [NumberField F]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (C : Subring B)
    (Φ : Γ F → Matrix (Fin 2) (Fin 2) B)
    (hcont : ∀ i j, Continuous fun g => Φ g i j)
    (hone : Φ 1 = 1)
    (hmul : ∀ g h, Φ (g * h) = Φ g * Φ h)
    (hmem : ∀ g i j, Φ g i j ∈ C) :
    ∃ τ : FramedGaloisRep F C (Fin 2),
      ∀ g, (LinearMap.toMatrix' (τ g)).map C.subtype = Φ g := by
  classical
  letI := moduleTopology C (Module.End C (Fin 2 → C))
  haveI hMT : IsModuleTopology C (Module.End C (Fin 2 → C)) := ⟨rfl⟩
  haveI : ContinuousAdd (Module.End C (Fin 2 → C)) :=
    IsModuleTopology.toContinuousAdd C (Module.End C (Fin 2 → C))
  haveI : IsModuleTopology C (Matrix (Fin 2) (Fin 2) C) :=
    inferInstanceAs (IsModuleTopology C (Fin 2 → Fin 2 → C))
  -- entrywise corestriction of `Φ` to `C`
  set G : Γ F → Matrix (Fin 2) (Fin 2) C :=
    fun g => Matrix.of fun i j => (⟨Φ g i j, hmem g i j⟩ : C)
  have hGmap : ∀ g, (G g).map C.subtype = Φ g := by
    intro g; ext i j; rfl
  -- `Matrix.map` along the injective inclusion is injective
  have hinj : Function.Injective
      (fun M : Matrix (Fin 2) (Fin 2) C => M.map C.subtype) := by
    intro M N hMN
    ext i j
    exact congrFun (congrFun hMN i) j
  have hGone : G 1 = 1 := by
    refine hinj ?_
    show (G 1).map C.subtype = (1 : Matrix (Fin 2) (Fin 2) C).map C.subtype
    rw [hGmap, hone, Matrix.map_one C.subtype (map_zero _) (map_one _)]
  have hGmul : ∀ g h, G (g * h) = G g * G h := by
    intro g h
    refine hinj ?_
    show (G (g * h)).map C.subtype = ((G g) * (G h)).map C.subtype
    rw [hGmap, hmul, Matrix.map_mul, hGmap, hGmap]
  have hGcont : Continuous G := by
    refine continuous_matrix fun i j => ?_
    exact continuous_induced_rng.mpr (hcont i j)
  have htolin : Continuous
      (Matrix.toLin' (R := C) (m := Fin 2) (n := Fin 2)) :=
    IsModuleTopology.continuous_of_linearMap
      (Matrix.toLin' (R := C) (m := Fin 2) (n := Fin 2)).toLinearMap
  refine ⟨⟨⟨⟨fun g => Matrix.toLin' (G g), ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · show Matrix.toLin' (G 1) = 1
    rw [hGone, Matrix.toLin'_one]
    rfl
  · intro g h
    show Matrix.toLin' (G (g * h)) = Matrix.toLin' (G g) * Matrix.toLin' (G h)
    rw [hGmul, Matrix.toLin'_mul]
    rfl
  · exact htolin.comp hGcont
  · intro g
    show (LinearMap.toMatrix' (Matrix.toLin' (G g))).map C.subtype = Φ g
    rw [LinearMap.toMatrix'_toLin']
    exact hGmap g

open scoped TensorProduct Matrix in
/-- **A conjugating matrix turns a base change into a change of framing**
(PROVEN 2026-07-26).

If `E` is an invertible matrix over `B` intertwining the `ψ`-image of a framed
representation `ρ` over `R` with a framed representation `σ` over `B`, then the
base change `ρ ⊗ B` is `σ` after the change of framing given by `E`. -/
theorem exists_conj_baseChange_of_matrix
    {F : Type*} [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (ψ : R →+* B) (hψ : Continuous ψ)
    (ρ : FramedGaloisRep F R (Fin 2)) (σ : FramedGaloisRep F B (Fin 2))
    (E : Matrix (Fin 2) (Fin 2) B) (hE : IsUnit E.det)
    (hconj : ∀ g : Γ F,
      E * (LinearMap.toMatrix' (ρ g)).map ⇑ψ =
        (LinearMap.toMatrix' (σ g)) * E) :
    letI : Algebra R B := ψ.toAlgebra
    letI : ContinuousSMul R B := continuousSMul_of_algebraMap R B
      (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
    ∃ e : (B ⊗[R] (Fin 2 → R)) ≃ₗ[B] (Fin 2 → B),
      (ρ.baseChange B).conj e = σ := by
  letI : Algebra R B := ψ.toAlgebra
  letI : ContinuousSMul R B := continuousSMul_of_algebraMap R B
    (by rw [RingHom.algebraMap_toAlgebra]; exact hψ)
  haveI : Invertible E := Matrix.invertibleOfIsUnitDet E hE
  set e : (B ⊗[R] (Fin 2 → R)) ≃ₗ[B] (Fin 2 → B) :=
    (TensorProduct.piScalarRight R B B (Fin 2)).trans
      (Matrix.toLinearEquiv' E inferInstance) with he
  -- the scalar action of `R` on `B` is `ψ`
  have hsmul : ∀ (r : R) (b : B), r • b = ψ r * b := fun r b => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  -- `e` on a simple tensor is `E` applied to the `ψ`-image, scaled by `b`
  have hetmul : ∀ (b : B) (w : Fin 2 → R),
      e (b ⊗ₜ[R] w) = b • (E *ᵥ (fun j => ψ (w j))) := by
    intro b w
    rw [he]
    show E *ᵥ (TensorProduct.piScalarRight R B B (Fin 2) (b ⊗ₜ[R] w)) = _
    rw [TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    rw [show (fun j => w j • b) = b • (fun j => ψ (w j)) from by
      funext j
      rw [hsmul]
      show ψ (w j) * b = b * ψ (w j)
      rw [mul_comm]]
    exact Matrix.mulVec_smul E b _
  refine ⟨e, GaloisRep.ext fun g => ?_⟩
  rw [GaloisRep.conj_apply]
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.conj_apply_apply]
  -- the identity on simple tensors, extended by linearity
  have key : ∀ x : B ⊗[R] (Fin 2 → R),
      e ((ρ.baseChange B) g x) = σ g (e x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b w =>
      rw [GaloisRep.baseChange_tmul, hetmul, hetmul]
      have hmap : (fun j => ψ ((ρ g w) j)) =
          (LinearMap.toMatrix' (ρ g)).map ⇑ψ *ᵥ (fun j => ψ (w j)) := by
        funext i
        rw [show (ρ g w) = LinearMap.toMatrix' (ρ g) *ᵥ w from
          (LinearMap.toMatrix'_mulVec (ρ g) w).symm]
        exact RingHom.map_mulVec ψ (LinearMap.toMatrix' (ρ g)) w i
      rw [hmap, Matrix.mulVec_mulVec]
      rw [show σ g (b • (E *ᵥ (fun j => ψ (w j)))) =
          b • (LinearMap.toMatrix' (σ g) *ᵥ (E *ᵥ (fun j => ψ (w j)))) from by
        rw [map_smul, ← LinearMap.toMatrix'_mulVec (σ g)]]
      rw [Matrix.mulVec_mulVec, hconj g]
  rw [key (e.symm v), LinearEquiv.apply_symm_apply]


/-! ### Closed subrings of a complete local ring with finite residue field

Hoisted 2026-07-27 out of `HardlyRamified/Deformation.lean`, unchanged. Pure
commutative algebra and topology: no base field, no Galois representation and
no trace subring occurs. It sits here because the Peirce/idempotent cluster
below consumes it and BOTH `HilbertModularity.lean` and `Deformation.lean`
consume that. -/

open Filter Topology in
/-- **A closed subring of a complete local ring with FINITE residue
field inverts its own units** (PROVEN 2026-07-25 — the engine of the
soft half of Carayol's Théorème 1): if `A` is local, its topology is
the `𝔪`-adic one, and `A/𝔪` is finite, then for a closed subring
`C ⊆ A` every `x ∈ C` with `x ∉ 𝔪` is already a unit OF `C`.

The classical argument writes `x⁻¹` as a limit of a geometric series in
`1 − x/a` for a lift `a ∈ C` of the residue of `x`, and therefore needs
`C ↠ A/𝔪`. FINITENESS of the residue field removes that hypothesis
entirely: the residue of `x` is a nonzero element of the finite field
`A/𝔪`, so `x^(q−1) ∈ 1 + 𝔪` for `q = |A/𝔪|`, and the geometric series
`∑ (1 − x^(q−1))^n` — all of whose partial sums lie in `C`, the argument
`y = 1 − x^(q−1)` lying in `𝔪 ∩ C` — converges in `A` to the inverse of
`x^(q−1)`, because `y^N ∈ 𝔪^N → 0` for the adic topology. `C` is closed,
so that inverse lies in `C`, and `x⁻¹ = x^(q−2) · (x^(q−1))⁻¹`.

Note that no completeness of `A` is used: the limit is exhibited
explicitly as the inverse that already exists in the LOCAL ring `A`;
only closedness of `C` and the adic topology are consumed. -/
theorem isUnit_of_isClosed_of_notMem_maximalIdeal {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A))
    {C : Subring A} (hC : IsClosed (C : Set A)) (x : C)
    (hx : (x : A) ∉ IsLocalRing.maximalIdeal A) : IsUnit x := by
  classical
  haveI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  set q := Fintype.card (IsLocalRing.ResidueField A)
  have hq1 : 0 < q - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  -- `x ^ (q - 1) = 1 - y` with `y ∈ 𝔪 ∩ C`
  have hres : IsLocalRing.residue A ((x : A) ^ (q - 1)) = 1 := by
    rw [map_pow]
    exact FiniteField.pow_card_sub_one_eq_one _
      (fun hz => hx ((IsLocalRing.residue_eq_zero_iff _).mp hz))
  set y : C := 1 - x ^ (q - 1) with hy
  have hyc : ((y : C) : A) = 1 - (x : A) ^ (q - 1) := by rw [hy]; push_cast; ring
  have hyR : (y : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, hyc, map_sub, hres, map_one, sub_self]
  have hone : (1 : A) - (y : A) = (x : A) ^ (q - 1) := by rw [hyc]; ring
  -- the inverse of `1 - y` in `A`
  have hu : IsUnit ((1 : A) - (y : A)) := by
    rw [← IsLocalRing.notMem_maximalIdeal, hone]
    intro hmem
    exact hx ((Ideal.IsPrime.pow_mem_iff_mem
      ((IsLocalRing.maximalIdeal.isMaximal A).isPrime) _ hq1).mp hmem)
  set u := hu.unit
  set L : A := ((u⁻¹ : Aˣ) : A) with hL
  have huL : ((1 : A) - (y : A)) * L = 1 := by
    rw [hL, show ((1 : A) - (y : A)) = (u : A) from (hu.unit_spec).symm]
    exact u.mul_inv
  -- the partial sums of the geometric series lie in `C`
  set s : ℕ → C := fun N => ∑ i ∈ Finset.range N, y ^ i with hs
  have hsc : ∀ N, ((s N : C) : A) = ∑ i ∈ Finset.range N, (y : A) ^ i := by
    intro N
    rw [hs]
    push_cast
    rfl
  have hsL : ∀ N, L - ((s N : C) : A) = L * (y : A) ^ N := by
    intro N
    have h1 : ((1 : A) - (y : A)) * ((s N : C) : A) = 1 - (y : A) ^ N := by
      rw [hsc]; exact mul_neg_geom_sum _ _
    have h2 : ((s N : C) : A) = L * (1 - (y : A) ^ N) := by
      calc ((s N : C) : A) = (L * ((1 : A) - (y : A))) * ((s N : C) : A) := by
            rw [mul_comm L, huL, one_mul]
        _ = L * (((1 : A) - (y : A)) * ((s N : C) : A)) := by ring
        _ = L * (1 - (y : A) ^ N) := by rw [h1]
    rw [h2]; ring
  -- so their limit `L` lies in `C`
  have htend : Tendsto (fun N => ((s N : C) : A)) atTop (𝓝 L) := by
    rw [(hadic.hasBasis_nhds L).tendsto_right_iff]
    intro n _
    filter_upwards [eventually_ge_atTop n] with N hN
    refine ⟨-(L * (y : A) ^ N), ?_, ?_⟩
    · refine Ideal.pow_le_pow_right hN ?_
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hyR N))
    · rw [← hsL N]; ring
  have hLC : L ∈ C := hC.mem_of_tendsto htend (.of_forall fun N => (s N).2)
  -- hence `1 - y = x ^ (q - 1)` is a unit of `C`, and therefore so is `x`
  have hunit : IsUnit (1 - y : C) := by
    refine ⟨⟨1 - y, ⟨L, hLC⟩, ?_, ?_⟩, rfl⟩
    · ext
      push_cast
      exact huL
    · ext
      push_cast
      rw [mul_comm]
      exact huL
  have hxq : IsUnit (x ^ (q - 1) : C) := by
    have hxy : (1 - y : C) = x ^ (q - 1) := by rw [hy]; ring
    rwa [hxy] at hunit
  refine isUnit_of_mul_isUnit_left (y := x ^ (q - 1 - 1)) ?_
  have hpow : x * x ^ (q - 1 - 1) = x ^ (q - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow]
  exact hxq

/-- **A closed subring of a local ring with finite residue field and
adic topology is LOCAL** (PROVEN 2026-07-25): the nonunits of `C` are
exactly `𝔪 ∩ C` by `isUnit_of_isClosed_of_notMem_maximalIdeal`, and that
is an ideal. -/
theorem isLocalRing_of_isClosed_subring {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A))
    {C : Subring A} (hC : IsClosed (C : Set A)) : IsLocalRing C := by
  haveI : Nontrivial C := ⟨⟨0, 1, fun hz => zero_ne_one (congrArg Subtype.val hz)⟩⟩
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  have hmem : ∀ c : C, c ∈ nonunits C → (c : A) ∈ IsLocalRing.maximalIdeal A := by
    intro c hc
    by_contra hcm
    exact hc (isUnit_of_isClosed_of_notMem_maximalIdeal hadic hC c hcm)
  intro hab
  have hsum : ((a : A) + (b : A)) ∈ IsLocalRing.maximalIdeal A :=
    Ideal.add_mem _ (hmem a ha) (hmem b hb)
  have hunit : IsUnit ((a : A) + (b : A)) := by simpa using hab.map C.subtype
  exact IsLocalRing.notMem_maximalIdeal.mpr hunit hsum

/-- **The maximal ideal of such a closed subring is `𝔪 ∩ C`** (PROVEN
2026-07-25), the companion of `isLocalRing_of_isClosed_subring`. -/
theorem maximalIdeal_eq_comap_of_isClosed_subring {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsLocalRing A] [Finite (IsLocalRing.ResidueField A)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal A))
    {C : Subring A} (hC : IsClosed (C : Set A)) [IsLocalRing C] :
    IsLocalRing.maximalIdeal C =
      Ideal.comap C.subtype (IsLocalRing.maximalIdeal A) := by
  ext a
  rw [IsLocalRing.mem_maximalIdeal, Ideal.mem_comap]
  constructor
  · intro ha
    by_contra hcm
    exact ha (isUnit_of_isClosed_of_notMem_maximalIdeal hadic hC a hcm)
  · intro ha hu
    have hunit : IsUnit (a : A) := by simpa using hu.map C.subtype
    exact IsLocalRing.notMem_maximalIdeal.mpr hunit ha

/-! ### The trace form of `Mₙ`, Burnside density, and basis extraction

Hoisted 2026-07-27 out of `HardlyRamified/Deformation.lean`, unchanged. Pure
linear algebra and representation theory over a field: these are the inputs to
Carayol's Théorème 1 step 1 at BOTH the `ℚ` level (`Deformation.lean`) and the
`F` level (`HilbertModularity.lean`), which is why they live upstream of both. -/

/-- **The trace form of `Mₙ` separates points, in EVERY characteristic**
(PROVEN 2026-07-26): pairing a matrix `X` against the elementary matrix
`E_{b a}` reads off the entry `X a b`. This one line is the whole content
of the nondegeneracy of `(X, Y) ↦ tr (X Y)`, and it consumes no
hypothesis on the coefficient ring — in particular no separability and no
restriction on the characteristic, which is why the Gram determinant
below is a unit even for `ℓ ∣ n`. -/
theorem trace_single_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] (a b : n) (X : Matrix n n R) :
    Matrix.trace (Matrix.single b a 1 * X) = X a b := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single, ite_and,
    Finset.sum_ite_eq]

/-- **The trace Gram matrix of a basis of `Mₙ(K)` is nonsingular** (PROVEN
2026-07-26, over a FIELD, in every characteristic): if
`det (tr (cᵢ cⱼ)) = 0` then some nonzero vector `v` is killed by the Gram
matrix (`Matrix.exists_mulVec_eq_zero_iff`), so `X = ∑ⱼ vⱼ cⱼ` is
trace-orthogonal to every `cᵢ`, hence — the `cᵢ` spanning — to EVERY
matrix, hence zero by `trace_single_mul`; and then `v = 0` by linear
independence, a contradiction. -/
theorem det_traceGram_ne_zero {K : Type*} [Field K] {n : Type*} [Fintype n]
    [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Module.Basis ι K (Matrix n n K)) :
    (Matrix.of fun i j => Matrix.trace (c i * c j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set X : Matrix n n K := ∑ j, v j • c j with hX
  have hrow : ∀ i, Matrix.trace (c i * X) = 0 := by
    intro i
    have h := congrFun hmul i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
    rw [hX, Finset.mul_sum, Matrix.trace_sum, ← h]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_comm]
  have hall : ∀ Y : Matrix n n K, Matrix.trace (Y * X) = 0 := by
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range (c : ι → Matrix n n K)) := by
      rw [c.span_eq]; trivial
    induction hY using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hrow i
    | zero => simp
    | add u w _ _ hu hw => rw [Matrix.add_mul, Matrix.trace_add, hu, hw, add_zero]
    | smul a u _ hu => rw [Matrix.smul_mul, Matrix.trace_smul, hu, smul_zero]
  have hX0 : X = 0 := by
    ext a b
    have h := hall (Matrix.single b a 1)
    rw [trace_single_mul] at h
    simpa using h
  refine hv (funext fun i => ?_)
  have hsum : ∑ j, v j • c j = 0 := by rw [← hX]; exact hX0
  simpa using Fintype.linearIndependent_iff.mp c.linearIndependent v hsum i

/-- The coordinates of a matrix against `Matrix.stdBasis` are its entries. -/
theorem stdBasis_repr_apply {R : Type*} [CommRing R] {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n R) (p : m × n) :
    (Matrix.stdBasis R m n).repr M p = M p.1 p.2 := by
  simp [Matrix.stdBasis]

/-- **BURNSIDE'S THEOREM** (PROVEN 2026-07-26, in any dimension and any
characteristic): if a monoid acts on a finite-dimensional `K`-vector space
`W` with no proper nonzero stable subspace, and the commutant of the image
is exactly the scalars, then the `K`-SPAN of the image is ALL of
`End_K W`.

Route: Jacobson density (mathlib's `jacobson_density`), applied over the
`K`-subalgebra `A = K⟨τ(G)⟩` of `End_K W`, which acts on `W` by
`Module.compHom` along `A.val`. Three things have to be checked and all
three are exactly the hypotheses:

* `W` is a SIMPLE `A`-module, because an `A`-submodule is in particular a
  `K`-submodule (`K` acts through `c • 1 ∈ A`) stable under every `τ g`,
  so `hirr` applies; the two lattices have literally the same carriers,
  which is why the transfer is a `SetLike.ext`.
* Every `φ ∈ End_A W` is `K`-linear (same reason) and commutes with every
  `τ g` (that is `A`-linearity at the element `τ g ∈ A`), hence is a
  scalar `c` by `hcomm`; so any `f ∈ End_K W` commutes with every
  `φ ∈ End_A W`, which is precisely the hypothesis Jacobson density needs.
* Density then gives, for a finite `K`-generating set `s` of `W`, an
  element `b ∈ A` with `f = b` on `s`; both sides being `K`-linear, they
  agree everywhere (`Submodule.span_induction`), so `f = b ∈ A`.

Finally `A = ⊤` and `Algebra.adjoin K (range τ) = span K (range τ)`
because `range τ` is already a SUBMONOID (`Submonoid.closure_eq` at
`MonoidHom.mrange τ`), which is where the multiplicativity of `τ` is used
and the only place it is used.

Reference: Curtis–Reiner, *Methods of Representation Theory* §3.3
(Burnside); Lam, *A First Course in Noncommutative Rings* §11. -/
theorem span_range_eq_top_of_irreducible_of_commutant
    {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Finite K W] [Nontrivial W]
    {G : Type*} [Monoid G] (τ : G →* Module.End K W)
    (hirr : ∀ p : Submodule K W, (∀ g : G, ∀ w ∈ p, τ g w ∈ p) → p = ⊥ ∨ p = ⊤)
    (hcomm : ∀ f : Module.End K W, (∀ g : G, f * τ g = τ g * f) →
      ∃ c : K, f = c • 1) :
    Submodule.span K (Set.range (τ : G → Module.End K W)) = ⊤ := by
  classical
  set A : Subalgebra K (Module.End K W) :=
    Algebra.adjoin K (Set.range (τ : G → Module.End K W)) with hAdef
  letI : Module A W := Module.compHom W (A.val : A →+* Module.End K W)
  have hsmul : ∀ (a : A) (w : W), a • w = (a : Module.End K W) w := fun a w => rfl
  have hone : ∀ (c : K) (w : W), (c • (1 : A)) • w = c • w := by
    intro c w
    rw [hsmul]
    simp
  have hτmem : ∀ g : G, (τ g : Module.End K W) ∈ A := fun g =>
    Algebra.subset_adjoin ⟨g, rfl⟩
  -- `A`-submodules are exactly the `τ`-stable `K`-submodules, so `W` is `A`-simple
  haveI hnt : Nontrivial (Submodule A W) := by
    refine ⟨⊥, ⊤, ?_⟩
    intro hcon
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have hmem : w ∈ (⊥ : Submodule A W) := by rw [hcon]; trivial
    exact hw (by simpa using hmem)
  haveI hso : IsSimpleOrder (Submodule A W) := by
    refine { eq_bot_or_eq_top := fun p => ?_ }
    set q : Submodule K W :=
      { carrier := (p : Set W)
        add_mem' := fun {a b} ha hb => p.add_mem ha hb
        zero_mem' := p.zero_mem
        smul_mem' := fun c w hw => by
          have h1 : (c • (1 : A)) • w ∈ p := p.smul_mem _ hw
          rwa [hone] at h1 } with hq
    have hmemq : ∀ w : W, w ∈ q ↔ w ∈ p := fun w => Iff.rfl
    have hstab : ∀ g : G, ∀ w ∈ q, τ g w ∈ q := by
      intro g w hw
      have h1 : (⟨τ g, hτmem g⟩ : A) • w ∈ p := p.smul_mem _ ((hmemq w).mp hw)
      exact (hmemq _).mpr h1
    rcases hirr q hstab with h | h
    · left
      refine SetLike.ext fun w => ?_
      constructor
      · intro hw
        have h2 : w ∈ q := (hmemq w).mpr hw
        rw [h] at h2
        simpa using h2
      · intro hw
        simp only [Submodule.mem_bot] at hw
        rw [hw]; exact p.zero_mem
    · right
      refine SetLike.ext fun w => ?_
      simp only [Submodule.mem_top, iff_true]
      have h2 : w ∈ q := by rw [h]; trivial
      exact (hmemq w).mp h2
  haveI hsimple : IsSimpleModule A W := ⟨⟩
  -- every `K`-endomorphism is realized by an element of `A` (Jacobson density)
  have hsurj : ∀ f : Module.End K W, f ∈ A := by
    intro f
    have hf : ∀ (φ : Module.End A W) (x : W), f (φ x) = φ (f x) := by
      intro φ x
      have hK : ∀ (c : K) (y : W), φ (c • y) = c • φ y := by
        intro c y
        have h2 : φ ((c • (1 : A)) • y) = (c • (1 : A)) • φ y := map_smul φ _ _
        rw [hone] at h2
        rw [h2, hone]
      set ψ : Module.End K W :=
        { toFun := fun y => φ y
          map_add' := fun y z => map_add φ y z
          map_smul' := fun c y => by simpa using hK c y } with hψ
      have hψcomm : ∀ g : G, ψ * τ g = τ g * ψ := by
        intro g
        refine LinearMap.ext fun y => ?_
        show φ ((τ g : Module.End K W) y) = (τ g : Module.End K W) (φ y)
        exact map_smul φ (⟨τ g, hτmem g⟩ : A) y
      obtain ⟨c, hc⟩ := hcomm ψ hψcomm
      have hφc : ∀ y, φ y = c • y := by
        intro y
        have h4 := congrArg (fun m : Module.End K W => m y) hc
        simpa [hψ] using h4
      rw [hφc x, hφc (f x), map_smul f c x]
    set F : Module.End (Module.End A W) W :=
      { toFun := fun y => f y
        map_add' := fun y z => map_add f y z
        map_smul' := fun φ y => by simpa [Module.End.smul_def] using hf φ y } with hF
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := W)
    obtain ⟨b, hb⟩ := jacobson_density (R := A) (M := W) F s
    have hall : ∀ w : W, f w = (b : Module.End K W) w := by
      intro w
      have hw : w ∈ Submodule.span K (s : Set W) := by rw [hs]; trivial
      induction hw using Submodule.span_induction with
      | mem m hm => exact hb m hm
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, map_add, hu, hv]
      | smul c u _ hu => rw [map_smul, map_smul, hu]
    have hfb : f = (b : Module.End K W) := LinearMap.ext hall
    rw [hfb]
    exact b.2
  have hclosure : ((Submonoid.closure (Set.range (τ : G → Module.End K W)) :
      Submonoid (Module.End K W)) : Set (Module.End K W))
      = Set.range (τ : G → Module.End K W) := by
    rw [show Set.range (τ : G → Module.End K W)
        = ((MonoidHom.mrange τ : Submonoid (Module.End K W)) :
          Set (Module.End K W)) from rfl]
    rw [Submonoid.closure_eq]
  refine eq_top_iff.mpr fun f _ => ?_
  have hf : f ∈ A := hsurj f
  rw [← Subalgebra.mem_toSubmodule, hAdef, Algebra.adjoin_eq_span, hclosure] at hf
  exact hf

/-- **A spanning family of a finite-dimensional space contains a basis,
indexed by any type of the right cardinality** (PROVEN 2026-07-26): pure
linear algebra over `exists_linearIndependent`, `Module.Basis.mk` and
`Fintype.equivOfCardEq`. Stated in the "reindexed and pulled back to the
index set" form the Burnside consumer below needs: it returns the
selection function `w : κ → ι` as well as the basis. -/
theorem exists_basis_of_span_range_eq_top
    {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    [Module.Finite K W] {ι : Type*} {κ : Type*} [Fintype κ]
    (hcard : Module.finrank K W = Fintype.card κ)
    (v : ι → W) (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ w : κ → ι, ∃ c : Module.Basis κ K W, ∀ i, c i = v (w i) := by
  classical
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent K (Set.range v)
  have hsp : ⊤ ≤ Submodule.span K (Set.range (Subtype.val : t → W)) := by
    rw [Subtype.range_val, hspan, hv]
  set bt : Module.Basis t K W := Module.Basis.mk hli hsp with hbt
  haveI hfin : Finite t := Module.Finite.finite_basis bt
  haveI : Fintype t := Fintype.ofFinite _
  have hct : Fintype.card t = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis bt, hcard]
  set e : κ ≃ t := (Fintype.equivOfCardEq hct).symm with he
  choose w hw using fun i : κ => hts (e i).2
  refine ⟨w, bt.reindex e.symm, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hbt, Module.Basis.mk_apply]
  exact (hw i).symm

/-! ### Carayol's Théorème 1, step 2: splitting a `C`-order in `M₂(B)`

Hoisted 2026-07-27 out of `HardlyRamified/Deformation.lean`, unchanged except
that `exists_conj_entries_mem_of_basis_repr_mem`'s coefficient ring binder is
now `Type*` rather than the file-level `Type u`, so its universe is
independent of every other binder in scope at a call site.

PURE ALGEBRA: no Galois representation, no base field and no arithmetic occurs
anywhere in the cluster. It was previously written TWICE — once here (at the
`ℚ` level) and once in `HilbertModularity.lean`, where the copy
`exists_conj_entries_mem_of_basis_repr_mem_hilbert` had to stand as an open
`sorry` because `Deformation.lean` `public import`s `HilbertModularity.lean`
and so cannot be imported back from it. Hoisting the cluster upstream of both
deletes that duplicate leaf outright. -/

/-- **Entrywise congruence of matrices modulo an ideal is multiplicative**
(PROVEN 2026-07-26): `X ≡ X'` and `Y ≡ Y'` entrywise mod `I` imply
`X Y ≡ X' Y'`, by the usual `XY − X'Y' = (X−X')Y + X'(Y−Y')`. -/
theorem matrix_sub_mem_mul {B : Type*} [CommRing B] {n : Type*} [Fintype n]
    (I : Ideal B) {X Y X' Y' : Matrix n n B}
    (hX : ∀ i j, (X - X') i j ∈ I) (hY : ∀ i j, (Y - Y') i j ∈ I) :
    ∀ i j, (X * Y - X' * Y') i j ∈ I := by
  intro i j
  have hEq : X * Y - X' * Y' = (X - X') * Y + X' * (Y - Y') := by noncomm_ring
  rw [hEq, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact Ideal.add_mem _
    (Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (hX i m))
    (Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hY m j))

/-- **The coordinates of a matrix against any basis are a fixed linear
form in its ENTRIES** (PROVEN 2026-07-26): expanding `M` in the elementary
matrices turns `b.repr M i` into `∑ₚ,q M p q · b.repr (E_{pq}) i`. This is
what makes each coordinate map CONTINUOUS over a topological ring, which
is how the `C`-order below is shown to be a closed subring. -/
theorem basis_repr_eq_sum_entries {B : Type*} [CommRing B] {n : Type*}
    [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι B (Matrix n n B)) (M : Matrix n n B) (i : ι) :
    b.repr M i = ∑ p : n, ∑ q : n, M p q * b.repr (Matrix.single p q 1) i := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  rw [map_sum]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [show Matrix.single p q (M p q) = M p q • Matrix.single p q (1 : B) by
    ext a c; simp [Matrix.single]]
  rw [map_smul]
  simp

/-- **Carayol's Théorème 1, step 2a: idempotent lifting inside a CLOSED
subring of a complete matrix algebra** (PROVEN 2026-07-26; cut the same
day out of `exists_conj_entries_mem_of_basis_repr_mem`; PURE
ALGEBRA): over a local
ring `B` carrying its `𝔪`-adic topology and `𝔪`-adically complete, an
element `x` of a closed subring `A ⊆ Mₙ(B)` which is idempotent MODULO `𝔪`
is congruent mod `𝔪` to a genuine idempotent OF `A`.

Newton's iteration `f(z) = 3z² − 2z³ = z − (2z−1)(z² − z)` does it. The
polynomial identity that makes it converge is

    f(z)² − f(z) = (z² − z)² · ((2z−1)² − 4),

so writing `t = x² − x` and `x₀ = x`, `x_{m+1} = f(x_m)`, one has
`x_m² − x_m ∈ 𝔪^{2^m}` and `x_{m+1} − x_m ∈ 𝔪^{2^m}` entrywise. The
sequence is therefore Cauchy for the `𝔪`-adic filtration in each of the
`n²` entries; `IsAdicComplete` supplies the limit entrywise, the adic
topology makes that limit a topological limit of the sequence, CLOSEDNESS
of `A` puts it in `A`, and continuity of multiplication passes `x_m² −
x_m → 0` to `u² = u`.

BOTH TOPOLOGICAL HYPOTHESES ARE LOAD-BEARING and neither can be traded
for the other: completeness produces the limit, closedness keeps it
inside `A`. Without closedness the limit is an idempotent of `Mₙ(B)` with
no reason to have coordinates in `C`, which is exactly what the caller
needs. -/
theorem exists_isIdempotentElem_mem_of_sq_sub_mem
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B]
    (hadic : IsAdic (IsLocalRing.maximalIdeal B))
    (hcompl : IsAdicComplete (IsLocalRing.maximalIdeal B) B)
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Subring (Matrix n n B))
    (hA : IsClosed ((A : Subring (Matrix n n B)) : Set (Matrix n n B)))
    {x : Matrix n n B} (hxA : x ∈ A)
    (hx : ∀ i j, (x * x - x) i j ∈ IsLocalRing.maximalIdeal B) :
    ∃ u ∈ A, u * u = u ∧ ∀ i j, (u - x) i j ∈ IsLocalRing.maximalIdeal B := by
  classical
  -- entrywise ideal membership is inherited through matrix products
  have hmulL : ∀ (I : Ideal B) (X Y : Matrix n n B), (∀ i j, X i j ∈ I) →
      ∀ i j, (X * Y) i j ∈ I := by
    intro I X Y hX i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (hX i m)
  have hmulR : ∀ (I : Ideal B) (X Y : Matrix n n B), (∀ i j, Y i j ∈ I) →
      ∀ i j, (X * Y) i j ∈ I := by
    intro I X Y hY i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hY m j)
  have hmulM : ∀ (I J : Ideal B) (X Y : Matrix n n B), (∀ i j, X i j ∈ I) →
      (∀ i j, Y i j ∈ J) → ∀ i j, (X * Y) i j ∈ I * J := by
    intro I J X Y hX hY i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_mul (hX i m) (hY m j)
  -- Newton's map `f z = 3z² − 2z³`, written without numerals so that
  -- membership in the subring `A` is immediate
  set f : Matrix n n B → Matrix n n B :=
    fun z => (z * z + z * z + z * z) - (z * z * z + z * z * z) with hf
  have hfA : ∀ z ∈ A, f z ∈ A := by
    intro z hz
    simp only [hf]
    exact A.sub_mem (A.add_mem (A.add_mem (A.mul_mem hz hz) (A.mul_mem hz hz))
      (A.mul_mem hz hz))
      (A.add_mem (A.mul_mem (A.mul_mem hz hz) hz) (A.mul_mem (A.mul_mem hz hz) hz))
  -- the two polynomial identities: `f(z)² − f(z) = (z²−z)²((2z−1)²−4)` …
  have hfsq : ∀ z : Matrix n n B, f z * f z - f z
      = ((z * z - z) * (z * z - z)) * ((2 * z - 1) * (2 * z - 1) - 4) := by
    intro z; simp only [hf]; noncomm_ring
  -- … and `f(z) − z = −(2z−1)(z²−z)`
  have hfdiff : ∀ z : Matrix n n B, f z - z = -((2 * z - 1) * (z * z - z)) := by
    intro z; simp only [hf]; noncomm_ring
  set seq : ℕ → Matrix n n B := fun m => f^[m] x with hseq
  have hseq0 : seq 0 = x := rfl
  have hseqS : ∀ m, seq (m + 1) = f (seq m) := fun m =>
    Function.iterate_succ_apply' f m x
  have hinvA : ∀ m, seq m ∈ A := by
    intro m
    induction m with
    | zero => rw [hseq0]; exact hxA
    | succ m ih => rw [hseqS]; exact hfA _ ih
  -- quadratic convergence of the defect
  have hinvP : ∀ m, ∀ p q, (seq m * seq m - seq m) p q ∈
      IsLocalRing.maximalIdeal B ^ (2 ^ m) := by
    intro m
    induction m with
    | zero => simpa [hseq0] using hx
    | succ m ih =>
      intro p q
      rw [hseqS, hfsq]
      refine hmulL _ _ _ (fun i j => ?_) p q
      have h2 := hmulM _ _ _ _ ih ih i j
      rwa [← pow_add, show 2 ^ m + 2 ^ m = 2 ^ (m + 1) by ring] at h2
  have hdiff : ∀ m, ∀ p q, (seq (m + 1) - seq m) p q ∈
      IsLocalRing.maximalIdeal B ^ (2 ^ m) := by
    intro m p q
    rw [hseqS, hfdiff]
    have h1 := hmulR _ (2 * seq m - 1) (seq m * seq m - seq m) (hinvP m) p q
    simpa using neg_mem h1
  have hmono : ∀ m m', m ≤ m' → ∀ p q, (seq m' - seq m) p q ∈
      IsLocalRing.maximalIdeal B ^ (2 ^ m) := by
    intro m m' hle
    induction m', hle using Nat.le_induction with
    | base => intro p q; simp
    | succ m' hle ih =>
      intro p q
      have hsplit : seq (m' + 1) - seq m
          = (seq (m' + 1) - seq m') + (seq m' - seq m) := by noncomm_ring
      rw [hsplit, Matrix.add_apply]
      refine Ideal.add_mem _ ?_ (ih p q)
      exact Ideal.pow_le_pow_right (Nat.pow_le_pow_right (by norm_num) hle)
        (hdiff m' p q)
  -- entrywise adic completeness produces the limit
  have hprec : ∀ p q : n, ∃ L : B, ∀ m, seq m p q - L ∈
      IsLocalRing.maximalIdeal B ^ m := by
    intro p q
    have hc : ∀ {a b : ℕ}, a ≤ b → seq a p q ≡ seq b p q
        [SMOD (IsLocalRing.maximalIdeal B ^ a) • (⊤ : Submodule B B)] := by
      intro a b hab
      simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      refine Ideal.pow_le_pow_right (le_of_lt Nat.lt_two_pow_self) ?_
      have h2 := hmono a b hab p q
      have h3 : seq a p q - seq b p q = -((seq b - seq a) p q) := by simp
      rw [h3]
      exact neg_mem h2
    obtain ⟨L, hL⟩ := hcompl.toIsPrecomplete.prec hc
    refine ⟨L, fun m => ?_⟩
    have h4 := hL m
    simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using h4
  choose L hL using hprec
  set u : Matrix n n B := Matrix.of fun p q => L p q with hu
  have hLu : ∀ m p q, (seq m - u) p q ∈ IsLocalRing.maximalIdeal B ^ m := by
    intro m p q
    simpa [hu] using hL p q m
  -- the limit is topological, so CLOSEDNESS of `A` keeps it inside `A`
  have htend : Filter.Tendsto seq Filter.atTop (nhds u) := by
    refine tendsto_pi_nhds.mpr fun p => tendsto_pi_nhds.mpr fun q => ?_
    rw [(hadic.hasBasis_nhds (u p q)).tendsto_right_iff]
    intro i _
    filter_upwards [Filter.eventually_ge_atTop i] with N hN
    exact ⟨seq N p q - u p q, Ideal.pow_le_pow_right hN (hLu N p q), by ring⟩
  have huA : u ∈ A := hA.mem_of_tendsto htend (.of_forall fun m => hinvA m)
  -- and separatedness turns the vanishing defect into an exact identity
  have huu : u * u = u := by
    have hall : ∀ p q, (u * u - u) p q = 0 := by
      intro p q
      refine hcompl.toIsHausdorff.haus _ (fun m => ?_)
      simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      have hus : ∀ i j, (u - seq m) i j ∈ IsLocalRing.maximalIdeal B ^ m := by
        intro i j
        have h5 := hLu m i j
        have h6 : (u - seq m) i j = -((seq m - u) i j) := by simp
        rw [h6]
        exact neg_mem h5
      have hsplit : u * u - u
          = (u * u - seq m * seq m) + ((seq m * seq m - seq m) + (seq m - u)) := by
        noncomm_ring
      rw [hsplit, Matrix.add_apply, Matrix.add_apply]
      refine Ideal.add_mem _ (matrix_sub_mem_mul _ hus hus p q)
        (Ideal.add_mem _ ?_ (hLu m p q))
      exact Ideal.pow_le_pow_right (le_of_lt Nat.lt_two_pow_self) (hinvP m p q)
    ext p q
    have h7 := hall p q
    rw [Matrix.sub_apply, sub_eq_zero] at h7
    exact h7
  refine ⟨u, huA, huu, ?_⟩
  intro p q
  have h1 : u - x = -(seq 1 - u) + (seq 1 - seq 0) := by rw [hseq0]; noncomm_ring
  rw [h1, Matrix.add_apply]
  refine Ideal.add_mem _ ?_ ?_
  · have h8 := hLu 1 p q
    rw [pow_one] at h8
    have h9 : (-(seq 1 - u)) p q = -((seq 1 - u) p q) := by simp
    rw [h9]
    exact neg_mem h8
  · have h10 := hdiff 0 p q
    simpa using h10

/-- **Carayol's Théorème 1, step 2b: an idempotent of `M₂(B)` congruent to
`E₁₁` is CONJUGATE to `E₁₁`** (PROVEN 2026-07-26, elementary and with an
explicit conjugating matrix): over a local ring `B`, if `u² = u` and
`u ≡ E₁₁ mod 𝔪` entrywise then `E⁻¹ u E = E₁₁` for the invertible

    E := u · E₁₁ + (1 − u) · E₂₂

(whose columns are `u e₁` and `(1 − u) e₂` — the classical choice).

Two computations, no analysis. First `u E = E E₁₁`: expanding and using
`E₁₁² = E₁₁`, `E₂₂E₁₁ = 0` and `u² = u`, both sides equal `u E₁₁`.
Second, `E` is invertible: writing `w := u − E₁₁` (entries in `𝔪`) and
using `E₁₁ + E₂₂ = 1`, `E₁₁² = E₁₁`, `E₂₂² = E₂₂`, one gets exactly
`E − 1 = w (E₁₁ − E₂₂)`, so `E ≡ 1` entrywise, so `det E ≡ 1 mod 𝔪` by
`Matrix.det_fin_two`, so `det E ∉ 𝔪` — and `B` is local. Then
`E⁻¹ u E = E⁻¹ (u E) = E⁻¹ (E E₁₁) = E₁₁`.

Note what is NOT needed: no completeness, no topology, no finiteness of
the residue field, and no hypothesis on the characteristic. -/
theorem exists_conj_eq_single_of_mul_self
    {B : Type*} [CommRing B] [IsLocalRing B]
    {u : Matrix (Fin 2) (Fin 2) B} (hu : u * u = u)
    (hures : ∀ i j, (u - (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) B)) i j ∈
      IsLocalRing.maximalIdeal B) :
    ∃ E : Matrix (Fin 2) (Fin 2) B, IsUnit E.det ∧
      E⁻¹ * u * E = Matrix.single 0 0 1 := by
  classical
  set F₀ : Matrix (Fin 2) (Fin 2) B := Matrix.single 0 0 1 with hF₀
  set F₁ : Matrix (Fin 2) (Fin 2) B := Matrix.single 1 1 1 with hF₁
  have hF₀F₀ : F₀ * F₀ = F₀ := by rw [hF₀]; simp
  have hF₁F₁ : F₁ * F₁ = F₁ := by rw [hF₁]; simp
  have hF₁F₀ : F₁ * F₀ = 0 := by
    rw [hF₀, hF₁]
    ext p q
    fin_cases p <;> fin_cases q <;> simp [Matrix.single, Matrix.mul_apply]
  have hFsum : F₀ + F₁ = 1 := by
    rw [hF₀, hF₁]
    ext p q
    fin_cases p <;> fin_cases q <;> simp [Matrix.single]
  set E : Matrix (Fin 2) (Fin 2) B := u * F₀ + (1 - u) * F₁ with hE
  have hkey : u * E = E * F₀ := by
    rw [hE]
    have h1 : u * (u * F₀ + (1 - u) * F₁) = (u * u) * F₀ + (u - u * u) * F₁ := by
      noncomm_ring
    have h2 : (u * F₀ + (1 - u) * F₁) * F₀ = u * (F₀ * F₀) + (1 - u) * (F₁ * F₀) := by
      noncomm_ring
    rw [h1, h2, hu, hF₀F₀, hF₁F₀, sub_self]
    simp
  set w : Matrix (Fin 2) (Fin 2) B := u - F₀ with hw
  have hE1 : E - 1 = w * (F₀ - F₁) := by
    have hu' : u = F₀ + w := by rw [hw]; abel
    have h3 : E = F₀ * F₀ + w * F₀ + (F₁ * F₁ - w * F₁) := by
      rw [hE, hu', ← hFsum]
      noncomm_ring
    rw [h3, hF₀F₀, hF₁F₁]
    rw [show F₀ + w * F₀ + (F₁ - w * F₁) - 1 = (F₀ + F₁) - 1 + w * (F₀ - F₁) by
      noncomm_ring, hFsum, sub_self, zero_add]
  have hEres : ∀ p q, (E - 1) p q ∈ IsLocalRing.maximalIdeal B := by
    intro p q
    rw [hE1, Matrix.mul_apply]
    exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (hures p m)
  have hdet : IsUnit E.det := by
    refine IsLocalRing.notMem_maximalIdeal.mp ?_
    intro hmem
    have h00 : E 0 0 - 1 ∈ IsLocalRing.maximalIdeal B := by
      simpa [Matrix.one_apply] using hEres 0 0
    have h11 : E 1 1 - 1 ∈ IsLocalRing.maximalIdeal B := by
      simpa [Matrix.one_apply] using hEres 1 1
    have h10 : E 1 0 ∈ IsLocalRing.maximalIdeal B := by
      simpa [Matrix.one_apply] using hEres 1 0
    have hd1 : E.det - 1 ∈ IsLocalRing.maximalIdeal B := by
      rw [Matrix.det_fin_two]
      rw [show E 0 0 * E 1 1 - E 0 1 * E 1 0 - 1
          = (E 0 0 - 1) * E 1 1 + (E 1 1 - 1) - E 0 1 * E 1 0 by ring]
      exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ h00) h11)
        (Ideal.mul_mem_left _ _ h10)
    have hone : (1 : B) ∈ IsLocalRing.maximalIdeal B := by
      have hsub : E.det - (E.det - 1) ∈ IsLocalRing.maximalIdeal B :=
        Ideal.sub_mem _ hmem hd1
      rwa [sub_sub_cancel] at hsub
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      (Ideal.eq_top_iff_one _ |>.mpr hone)
  refine ⟨E, hdet, ?_⟩
  rw [show E⁻¹ * u * E = E⁻¹ * (u * E) by noncomm_ring, hkey,
    ← mul_assoc, Matrix.nonsing_inv_mul E hdet, one_mul]

/-- **Peirce decomposition in coordinates** (PROVEN 2026-07-26): a subring
`A ⊆ M₂(B)` containing the matrix unit `E₁₁` — hence also
`E₂₂ = 1 − E₁₁` — contains a matrix `M` if and only if it contains each of
the four "corner" matrices `Mᵢⱼ · Eᵢⱼ`.

Forward is `Eᵢᵢ M Eⱼⱼ = Mᵢⱼ · Eᵢⱼ` (`Matrix.single_mul_mul_single`);
backward is `M = ∑ᵢⱼ Mᵢⱼ · Eᵢⱼ` (`Matrix.matrix_eq_sum_single`) and
closure under addition.

WHAT THIS IS FOR. It converts the module-theoretic Peirce decomposition
`A = ⨁ᵢⱼ Eᵢᵢ A Eⱼⱼ` into a statement about the four `C`-submodules
`Iᵢⱼ := {x : B | x · Eᵢⱼ ∈ A}` of `B`: the lemma says exactly
`A = {M | ∀ i j, Mᵢⱼ ∈ Iᵢⱼ}`, and multiplicativity of `A` says
`Iᵢⱼ · Iⱼₗ ⊆ Iᵢₗ`, with `1 ∈ I₁₁ ∩ I₂₂`. See the leaf below for how the
rest of the argument runs from here. -/
theorem mem_iff_smul_single_mem {B : Type*} [CommRing B]
    (A : Subring (Matrix (Fin 2) (Fin 2) B))
    (h11 : (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) B) ∈ A)
    (M : Matrix (Fin 2) (Fin 2) B) :
    M ∈ A ↔ ∀ i j : Fin 2,
      (M i j) • (Matrix.single i j 1 : Matrix (Fin 2) (Fin 2) B) ∈ A := by
  classical
  have hdiag : ∀ i : Fin 2,
      (Matrix.single i i 1 : Matrix (Fin 2) (Fin 2) B) ∈ A := by
    intro i
    fin_cases i
    · exact h11
    · have h1 : (Matrix.single 1 1 1 : Matrix (Fin 2) (Fin 2) B)
          = 1 - Matrix.single 0 0 1 := by
        ext p q
        fin_cases p <;> fin_cases q <;> simp [Matrix.single]
      simpa [h1] using A.sub_mem A.one_mem h11
  have hsingle : ∀ (i j : Fin 2), (Matrix.single i j (M i j)
      : Matrix (Fin 2) (Fin 2) B) = (M i j) • Matrix.single i j 1 := by
    intro i j
    ext a c
    simp [Matrix.single]
  constructor
  · intro hM i j
    have hprod : (Matrix.single i i 1 : Matrix (Fin 2) (Fin 2) B) * M
        * Matrix.single j j 1 = Matrix.single i j (M i j) := by
      rw [Matrix.single_mul_mul_single]
      simp
    rw [← hsingle, ← hprod]
    exact A.mul_mem (A.mul_mem (hdiag i) hM) (hdiag j)
  · intro hM
    rw [Matrix.matrix_eq_sum_single M]
    refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
    rw [hsingle]
    exact hM i j

open scoped TensorProduct in
/-- **A finite product of modules over a LOCAL ring, free with basis indexed
by the index type itself and with every factor nonzero, has CYCLIC factors**
(PROVEN 2026-07-26 — the module-theoretic engine of the Peirce corner
analysis below; pure commutative algebra, nothing matrix-specific).

The proof is the residue-field rank count plus Nakayama, in exactly the form
`IsLocalRing.map_tensorProduct_mk_eq_top` packages it. Base-changing the
basis gives `dim_k (k ⊗ ∏ᵢ Nᵢ) = |ι|`; `TensorProduct.piRight` splits that as
`∑ᵢ dim_k (k ⊗ Nᵢ)`; each summand is nonzero by
`IsLocalRing.subsingleton_tensorProduct` (this is where `Nontrivial (N i)`
and finiteness of each `N i` are consumed), so each is exactly `1`; and a
one-dimensional `k ⊗ Nᵢ` has a generator of the form `1 ⊗ a`, which by
Nakayama generates `Nᵢ` itself.

Note the hypothesis is a basis indexed by `ι` — i.e. the free rank equals the
NUMBER OF FACTORS. That is the whole content: it is what forces every factor
to have residual dimension exactly one, and it is why the Peirce argument
needs `A'` to be `C`-free of rank `4` rather than merely finite. -/
theorem exists_span_eq_top_of_pi_basis
    {C : Type*} [CommRing C] [IsLocalRing C]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module C (N i)]
    (b : Module.Basis ι C ((i : ι) → N i))
    (hne : ∀ i, Nontrivial (N i)) (i : ι) :
    ∃ a : N i, Submodule.span C {a} = ⊤ := by
  classical
  haveI hfin : Module.Finite C ((i : ι) → N i) := Module.Finite.of_basis b
  haveI hfini : ∀ j, Module.Finite C (N j) := fun j =>
    Module.Finite.of_surjective (LinearMap.proj j (R := C) (φ := N))
      (fun x => ⟨Pi.single j x, by simp⟩)
  set k := IsLocalRing.ResidueField C with hk
  haveI : ∀ j, Module.Finite k (k ⊗[C] N j) := fun j => Module.Finite.base_change _ _ _
  have hrank : Module.finrank k (k ⊗[C] ((j : ι) → N j)) = Fintype.card ι := by
    rw [Module.finrank_eq_card_basis (b.baseChange k)]
  have he : (k ⊗[C] ((j : ι) → N j)) ≃ₗ[k] ((j : ι) → k ⊗[C] N j) :=
    TensorProduct.piRight C k k N
  have h2 : Module.finrank k ((j : ι) → k ⊗[C] N j) = Fintype.card ι := by
    rw [← he.finrank_eq]; exact hrank
  rw [Module.finrank_pi_fintype] at h2
  have hpos : ∀ j, 1 ≤ Module.finrank k (k ⊗[C] N j) := by
    intro j
    haveI : Nontrivial (k ⊗[C] N j) := by
      rw [← not_subsingleton_iff_nontrivial, IsLocalRing.subsingleton_tensorProduct]
      rw [not_subsingleton_iff_nontrivial]
      exact hne j
    exact Module.finrank_pos
  have hone : ∀ j, Module.finrank k (k ⊗[C] N j) = 1 := by
    intro j
    by_contra hcon
    have hp := hpos j
    have h3 : 2 ≤ Module.finrank k (k ⊗[C] N j) := by omega
    have hlt : ∑ _x : ι, (1 : ℕ) < ∑ x : ι, Module.finrank k (k ⊗[C] N x) :=
      Finset.sum_lt_sum (fun x _ => hpos x) ⟨j, Finset.mem_univ j, by omega⟩
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hlt
    rw [h2] at hlt
    exact lt_irrefl _ hlt
  have hne1 : Nontrivial (k ⊗[C] N i) := by
    rw [← not_subsingleton_iff_nontrivial, IsLocalRing.subsingleton_tensorProduct]
    rw [not_subsingleton_iff_nontrivial]
    exact hne i
  obtain ⟨v, hv⟩ := exists_ne (0 : k ⊗[C] N i)
  obtain ⟨a, ha⟩ : ∃ a : N i, (TensorProduct.mk C k (N i) 1) a = v :=
    TensorProduct.mk_surjective C (N i) k Ideal.Quotient.mk_surjective v
  refine ⟨a, ?_⟩
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top]
  rw [Submodule.map_span]
  have himg : (TensorProduct.mk C k (N i) 1) '' {a} = {v} := by
    rw [Set.image_singleton, ha]
  rw [himg]
  rw [← Submodule.restrictScalars_span C k Ideal.Quotient.mk_surjective {v}]
  have hspan : Submodule.span k {v} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero v hv).mp (hone i)
  rw [hspan]
  rfl

open scoped Matrix in
/-- **Each PEIRCE CORNER of a rank-`4` `C`-order in `M₂(B)` is a principal
`C`-module generated by a UNIT of `B`** (PROVEN 2026-07-26 — steps 1 and 2 of
Carayol's step 2c, in the coordinate form the file uses).

`A` is the `C`-order, presented through `hA` as `{M | ∀ n, b.repr M n ∈ C}`
so that no subring structure is needed here; `hpeirce` is the PROVEN
`mem_iff_smul_single_mem` above, supplied as a hypothesis so that this lemma
stays pure module theory. Writing `Iᵢⱼ = {x : B | x·Eᵢⱼ ∈ A}`, the four `Iᵢⱼ`
assemble into a `C`-module isomorphic to `A` (that is `hpeirce`), and `A` is
`C`-free of rank `4` on `b` (that is `hA`); so
`exists_span_eq_top_of_pi_basis` applies verbatim with `ι = Fin 2 × Fin 2`.

Nonvanishing of each corner — the remaining hypothesis of that lemma — comes
from `hb`: expanding `Eᵢⱼ` in the `B`-basis `b` and reading off the `(i,j)`
entry gives `1 = ∑ₙ (b.repr Eᵢⱼ n)·(bₙ)ᵢⱼ`, so some `(bₙ)ᵢⱼ` lies outside
`𝔪_B`; it lies in `Iᵢⱼ` by `hpeirce`, and being a unit it is nonzero. The
same element makes the generator `a` a unit, since `a` divides it.

**The projectivity detour recorded in the older plan is NOT used**: no
`Module.free_of_flat_of_isLocalRing`, no projective modules, no rank
bookkeeping over a possibly non-domain `C`. Cyclic — which is all the
conjugation step needs — comes straight out of Nakayama. -/
theorem exists_peirceCornerGenerator
    {B : Type*} [CommRing B] [IsLocalRing B]
    (C : Subring B) [IsLocalRing C]
    (A : Submodule C (Matrix (Fin 2) (Fin 2) B))
    (b : Module.Basis (Fin 4) B (Matrix (Fin 2) (Fin 2) B))
    (hb : ∀ n, b n ∈ A)
    (hA : ∀ M : Matrix (Fin 2) (Fin 2) B, M ∈ A ↔ ∀ n, b.repr M n ∈ C)
    (hpeirce : ∀ M : Matrix (Fin 2) (Fin 2) B,
      M ∈ A ↔ ∀ i j : Fin 2,
        (M i j) • (Matrix.single i j 1 : Matrix (Fin 2) (Fin 2) B) ∈ A)
    (p : Fin 2 × Fin 2) :
    ∃ a : B, IsUnit a ∧ ∀ x : B,
      x • (Matrix.single p.1 p.2 1 : Matrix (Fin 2) (Fin 2) B) ∈ A ↔
        ∃ c : C, x = (c : B) * a := by
  classical
  -- entrywise expansion of a sum of corners
  have hentry : ∀ (f : Fin 2 × Fin 2 → B) (i j : Fin 2),
      (∑ q : Fin 2 × Fin 2,
          f q • (Matrix.single q.1 q.2 1 : Matrix (Fin 2) (Fin 2) B)) i j = f (i, j) := by
    intro f i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single, Fintype.sum_prod_type,
      smul_eq_mul, Matrix.of_apply]
    fin_cases i <;> fin_cases j <;> simp
  have hsum : ∀ N : Matrix (Fin 2) (Fin 2) B,
      ∑ q : Fin 2 × Fin 2,
        (N q.1 q.2) • (Matrix.single q.1 q.2 1 : Matrix (Fin 2) (Fin 2) B) = N := by
    intro N; ext i j; exact hentry (fun q => N q.1 q.2) i j
  -- the four corner submodules
  set I : Fin 2 × Fin 2 → Submodule C B := fun q =>
    { carrier := {x : B | x • (Matrix.single q.1 q.2 1 : Matrix (Fin 2) (Fin 2) B) ∈ A}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq, add_smul]
        exact A.add_mem hx hy
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_assoc]
        exact A.smul_mem c hx } with hIdef
  have hAmem : ∀ (M : Matrix (Fin 2) (Fin 2) B), M ∈ A → ∀ q : Fin 2 × Fin 2,
      M q.1 q.2 ∈ I q := fun M hM q => (hpeirce M).mp hM q.1 q.2
  -- the element of `A` assembled from prescribed corners
  set F : ((q : Fin 2 × Fin 2) → I q) → Matrix (Fin 2) (Fin 2) B := fun x =>
    ∑ q : Fin 2 × Fin 2,
      ((x q : B)) • (Matrix.single q.1 q.2 1 : Matrix (Fin 2) (Fin 2) B) with hFdef
  have hFmem : ∀ x, F x ∈ A := fun x => Submodule.sum_mem _ fun q _ => (x q).2
  have hFadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    simp only [hFdef]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [← add_smul]; rfl
  have hFsmul : ∀ (c : C) x, F (c • x) = (c : B) • F x := by
    intro c x
    simp only [hFdef]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [smul_smul]; rfl
  have hFentry : ∀ x (q : Fin 2 × Fin 2), F x q.1 q.2 = (x q : B) := by
    intro x q
    have hq := hentry (fun q => (x q : B)) q.1 q.2
    simp only [hFdef]
    rw [hq]
  -- the product of the corners is `C`-free of rank `4`
  let φ : ((q : Fin 2 × Fin 2) → I q) ≃ₗ[C] (Fin 4 → C) :=
    { toFun := fun x n => ⟨b.repr (F x) n, (hA _).mp (hFmem x) n⟩
      map_add' := by
        intro x y
        funext n
        apply Subtype.ext
        show (b.repr (F (x + y))) n = (b.repr (F x)) n + (b.repr (F y)) n
        rw [hFadd, map_add]
        simp
      map_smul' := by
        intro c x
        funext n
        apply Subtype.ext
        show (b.repr (F (c • x))) n = (c : B) * (b.repr (F x)) n
        rw [hFsmul, map_smul]
        simp
      invFun := fun c q =>
        ⟨(∑ n : Fin 4, ((c n : B)) • b n) q.1 q.2,
          hAmem _ ((hA _).mpr (by
            intro m
            rw [b.repr_sum_self]
            exact (c m).2)) q⟩
      left_inv := by
        intro x
        funext q
        apply Subtype.ext
        show (∑ n : Fin 4, ((b.repr (F x) n : B)) • b n) q.1 q.2 = (x q : B)
        rw [b.sum_repr]
        exact hFentry x q
      right_inv := by
        intro c
        funext n
        apply Subtype.ext
        show (b.repr (∑ q : Fin 2 × Fin 2,
            (((∑ m : Fin 4, ((c m : B)) • b m) q.1 q.2))
              • (Matrix.single q.1 q.2 1 : Matrix (Fin 2) (Fin 2) B))) n = (c n : B)
        rw [hsum, b.repr_sum_self] }
  have e4 : Fin 4 ≃ (Fin 2 × Fin 2) :=
    (Fintype.equivFinOfCardEq (α := Fin 2 × Fin 2) (by simp)).symm
  have hbasis : Module.Basis (Fin 2 × Fin 2) C ((q : Fin 2 × Fin 2) → I q) :=
    (Module.Basis.ofEquivFun φ).reindex e4
  -- every corner contains an element outside the maximal ideal
  have hunit : ∀ q : Fin 2 × Fin 2,
      ∃ n : Fin 4, (b n) q.1 q.2 ∉ IsLocalRing.maximalIdeal B := by
    intro q
    by_contra hcon
    push Not at hcon
    have hE : (Matrix.single q.1 q.2 1 : Matrix (Fin 2) (Fin 2) B) q.1 q.2 = 1 := by
      simp [Matrix.single]
    have hrepr := b.sum_repr (Matrix.single q.1 q.2 1 : Matrix (Fin 2) (Fin 2) B)
    have h1 : (1 : B)
        = ∑ n : Fin 4, (b.repr (Matrix.single q.1 q.2 1
            : Matrix (Fin 2) (Fin 2) B) n) * ((b n) q.1 q.2) := by
      conv_lhs => rw [← hE, ← hrepr]
      simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have hone : (1 : B) ∈ IsLocalRing.maximalIdeal B := by
      rw [h1]
      exact Ideal.sum_mem _ fun n _ => Ideal.mul_mem_left _ _ (hcon n)
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      (Ideal.eq_top_iff_one _ |>.mpr hone)
  have hnt : ∀ q : Fin 2 × Fin 2, Nontrivial (I q) := by
    intro q
    obtain ⟨n, hn⟩ := hunit q
    refine ⟨⟨⟨(b n) q.1 q.2, hAmem (b n) (hb n) q⟩, 0, ?_⟩⟩
    intro hzero
    exact hn (by rw [show (b n) q.1 q.2 = (0 : B) from congrArg Subtype.val hzero]; simp)
  -- Nakayama: each corner is cyclic
  obtain ⟨a₀, ha₀⟩ := exists_span_eq_top_of_pi_basis hbasis hnt p
  refine ⟨(a₀ : B), ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hunit p
    have hmem : (⟨(b n) p.1 p.2, hAmem (b n) (hb n) p⟩ : I p) ∈ Submodule.span C {a₀} := by
      rw [ha₀]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hval : (c : B) * (a₀ : B) = (b n) p.1 p.2 := congrArg Subtype.val hc
    have hu : IsUnit ((b n) p.1 p.2) := by
      rwa [← IsLocalRing.notMem_maximalIdeal]
    rw [← hval] at hu
    exact isUnit_of_mul_isUnit_right hu
  · intro x
    constructor
    · intro hx
      have hmem : (⟨x, hx⟩ : I p) ∈ Submodule.span C {a₀} := by rw [ha₀]; trivial
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      exact ⟨c, (congrArg Subtype.val hc).symm⟩
    · rintro ⟨c, rfl⟩
      exact (I p).smul_mem c a₀.2

open scoped Matrix in
/-- **The PEIRCE CORNERS of a `C`-order containing `E₁₁` are principal, with
unit off-diagonal generators** (**PROVEN 2026-07-26**; cut 2026-07-26 out of
`exists_conj_entries_mem_of_single_mem` below — steps 1–4 of that leaf's
grading argument; PURE MODULE THEORY, no matrices beyond the four corners
and no topology beyond `hclosed`).

PROOF, as carried out: steps 1 and 2 are the new
`exists_peirceCornerGenerator` above, which runs the residue-field rank count
of `exists_span_eq_top_of_pi_basis` on the four corners and returns each
`Iᵢⱼ = C·aᵢⱼ` with `aᵢⱼ` a unit of `B`. Step 3 is the local `hdiag` below:
`1 ∈ Iᵢᵢ` gives `1 = c·aᵢᵢ` with `c ∈ C`, so `c` is a unit of `B`, hence a
unit of `C` by the PROVEN `isUnit_of_isClosed_of_notMem_maximalIdeal` — the
ONLY place `hclosed` and the finiteness of the residue field are consumed —
whence `aᵢᵢ = c⁻¹ ∈ C` and `Iᵢᵢ = C`. Step 4 is then one line: the product
`(a₀₁·E₀₁)(a₁₀·E₁₀) = (a₀₁a₁₀)·E₀₀` lies in the SUBRING `Asub` (which has
the same carrier as the submodule `A`), so `a₀₁a₁₀ ∈ I₀₀ = C`.

`hcompl` and `hres` are genuinely UNUSED here — they are inherited from
`exists_conj_entries_mem_of_single_mem`'s package, where `hres` is consumed
by the idempotent-lifting reduction and `hcompl` upstream of it. They are
kept so the two halves share one signature, exactly as the note below says.

The hypotheses are verbatim those of `exists_conj_entries_mem_of_single_mem`,
so that the two halves can be redistributed freely. Write
`A' = {M | ∀ n, b.repr M n ∈ C}` for the order (this is `∑ᵢ C·bᵢ`; the
`Subring` structure is built in the consumer) and

    Iᵢⱼ = {x : B | x • Eᵢⱼ ∈ A'},

which is what the four `↔`s below say, spelled out through
`hmemA : M ∈ A' ↔ ∀ n, b.repr M n ∈ C` so that `A'` itself need not appear in
the statement. The conclusion is exactly:

* `I₀₁ = C·a₀₁` and `I₁₀ = C·a₁₀` are PRINCIPAL (step 1),
* `a₀₁` is a UNIT of `B` (step 2),
* `I₀₀ = I₁₁ = C` (step 3),
* `a₀₁·a₁₀ ∈ C` (step 4).

Step 5 — the conjugation by `diag(1, a₀₁⁻¹)` that turns these four facts
into the conclusion of `exists_conj_entries_mem_of_single_mem` — is PROVEN
in that consumer, so this is now the whole residual of Carayol's step 2c.

THE ARGUMENT, and one simplification worth recording. The PROVEN
`mem_iff_smul_single_mem` gives `A' = {M | ∀ i j, Mᵢⱼ ∈ Iᵢⱼ}`, i.e. an
isomorphism of `C`-modules `A' ≅ I₀₀ ⊕ I₀₁ ⊕ I₁₀ ⊕ I₁₁`, and `A'` is free
of rank `4` over the local ring `C` (`isLocalRing_of_isClosed_subring`, `b`
being `C`-linearly independent because it is `B`-linearly independent).

The plan previously recorded here routed step 1 through PROJECTIVITY —
each `Iᵢⱼ` is a direct summand of a free module, hence finitely generated
projective, hence free over the local `C` by
`Module.free_of_flat_of_isLocalRing`, with the four ranks summing to `4`.
**That detour is unnecessary.** `Iᵢⱼ` is the image of the `C`-linear
entry map `A' → B`, `M ↦ Mᵢⱼ`, so it is finitely generated; by
`maximalIdeal_eq_comap_of_isClosed_subring` the residue field of `C` is
`k`, so `A'/𝔪_C A'` has `k`-dimension `4` and splits as
`⊕ᵢⱼ Iᵢⱼ/𝔪_C Iᵢⱼ`; each summand is nonzero because the `B`-span of `A'`
is all of `M₂(B)`, forcing `B·Iᵢⱼ = B`; so each summand has dimension
exactly `1`, and NAKAYAMA makes each `Iᵢⱼ` CYCLIC. Cyclic is all step 1
needs — freeness is never used — which removes the projective-module
theory from the critical path entirely.

Steps 2–4 are then as before: `B·Iᵢⱼ = B` and `B` local give `a₀₁, a₁₀ ∉ 𝔪`;
writing `1 = c·a₀₀` with `c ∈ C` makes `c` a unit of `B`, hence of `C` by the
PROVEN `isUnit_of_isClosed_of_notMem_maximalIdeal` — the ONLY place
closedness and the finite residue field are consumed — so `I₀₀ = C`, and
likewise `I₁₁`; and `a₀₁·a₁₀ ∈ I₀₀ = C`.

`hadic`, `hcompl` and `hres` are inherited from the consumer's signature.
`hres` is what makes the residual algebra split (see the note on the
consumer); `hcompl` is used only by the idempotent lifting that happens
upstream of this leaf, and is kept here solely so the two halves share one
hypothesis package.

References: Carayol, Contemp. Math. 165, Théorème 1; Nyssen, Math. Ann.
306; Auslander–Goldman, *The Brauer group of a commutative ring*. -/
theorem exists_peirceGenerators_of_single_mem
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Finite (IsLocalRing.ResidueField B)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal B))
    (hcompl : IsAdicComplete (IsLocalRing.maximalIdeal B) B)
    (C : Subring B) (hclosed : IsClosed ((C : Subring B) : Set B))
    (hres : ∀ y : B, ∃ x : C, (x : B) - y ∈ IsLocalRing.maximalIdeal B)
    (S : Submonoid (Matrix (Fin 2) (Fin 2) B))
    (b : Module.Basis (Fin 4) B (Matrix (Fin 2) (Fin 2) B))
    (hbS : ∀ i : Fin 4, b i ∈ S)
    (hrepr : ∀ M ∈ S, ∀ i : Fin 4, b.repr M i ∈ C)
    (hone : ∀ i : Fin 4,
      b.repr (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) B) i ∈ C) :
    ∃ a01 a10 : B, IsUnit a01 ∧ (a01 * a10) ∈ C ∧
      (∀ x : B, (∀ n : Fin 4,
          b.repr (x • (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) B)) n ∈ C) ↔
        ∃ c : C, x = (c : B) * a01) ∧
      (∀ x : B, (∀ n : Fin 4,
          b.repr (x • (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) B)) n ∈ C) ↔
        ∃ c : C, x = (c : B) * a10) ∧
      (∀ x : B, (∀ n : Fin 4,
          b.repr (x • (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) B)) n ∈ C) ↔
        x ∈ C) ∧
      (∀ x : B, (∀ n : Fin 4,
          b.repr (x • (Matrix.single 1 1 1 : Matrix (Fin 2) (Fin 2) B)) n ∈ C) ↔
        x ∈ C) := by
  classical
  haveI hCloc : IsLocalRing C := isLocalRing_of_isClosed_subring hadic hclosed
  -- the `C`-order, as a subring and as a `C`-submodule with the SAME carrier
  set Asub : Subring (Matrix (Fin 2) (Fin 2) B) :=
    { carrier := {M | ∀ i, b.repr M i ∈ C}
      zero_mem' := by intro i; simp
      one_mem' := fun i => hrepr 1 S.one_mem i
      add_mem' := fun {x y} hx hy i => by simpa using C.add_mem (hx i) (hy i)
      neg_mem' := fun {x} hx i => by simpa using C.neg_mem (hx i)
      mul_mem' := by
        intro x y hx hy n
        have hxy : x * y = ∑ i, ∑ j, (b.repr x i * b.repr y j) • (b i * b j) := by
          conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [hxy]
        simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
        exact C.mul_mem (C.mul_mem (hx i) (hy j))
          (hrepr _ (S.mul_mem (hbS i) (hbS j)) n) } with hAsubdef
  set A : Submodule C (Matrix (Fin 2) (Fin 2) B) :=
    { carrier := {M | ∀ i, b.repr M i ∈ C}
      zero_mem' := by intro i; simp
      add_mem' := fun {x y} hx hy i => by simpa using C.add_mem (hx i) (hy i)
      smul_mem' := fun c x hx i => by
        simpa [Subring.smul_def] using C.mul_mem c.2 (hx i) } with hAdef
  have hAmemiff : ∀ M : Matrix (Fin 2) (Fin 2) B, M ∈ A ↔ ∀ n, b.repr M n ∈ C :=
    fun _ => Iff.rfl
  have hAAsub : ∀ M : Matrix (Fin 2) (Fin 2) B, M ∈ A ↔ M ∈ Asub := fun _ => Iff.rfl
  have hbA : ∀ n, b n ∈ A := fun n => hrepr (b n) (hbS n)
  have hE00 : (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) B) ∈ A := hone
  have hpeirce : ∀ M : Matrix (Fin 2) (Fin 2) B,
      M ∈ A ↔ ∀ i j : Fin 2,
        (M i j) • (Matrix.single i j 1 : Matrix (Fin 2) (Fin 2) B) ∈ A := by
    intro M
    exact mem_iff_smul_single_mem Asub hE00 M
  obtain ⟨a01, hu01, hI01⟩ := exists_peirceCornerGenerator C A b hbA hAmemiff hpeirce (0, 1)
  obtain ⟨a10, hu10, hI10⟩ := exists_peirceCornerGenerator C A b hbA hAmemiff hpeirce (1, 0)
  obtain ⟨a00, hu00, hI00⟩ := exists_peirceCornerGenerator C A b hbA hAmemiff hpeirce (0, 0)
  obtain ⟨a11, hu11, hI11⟩ := exists_peirceCornerGenerator C A b hbA hAmemiff hpeirce (1, 1)
  -- `E₂₂ = 1 − E₁₁ ∈ A`
  have hE11 : (Matrix.single 1 1 1 : Matrix (Fin 2) (Fin 2) B) ∈ A := by
    have h1 : (Matrix.single 1 1 1 : Matrix (Fin 2) (Fin 2) B)
        = 1 - Matrix.single 0 0 1 := by
      ext p q
      fin_cases p <;> fin_cases q <;> simp [Matrix.single]
    rw [h1]
    exact A.sub_mem (fun i => hrepr 1 S.one_mem i) hE00
  -- STEP 3: a diagonal corner containing `1` is exactly `C`
  have hdiag : ∀ (i : Fin 2) (a : B),
      (∀ x : B, x • (Matrix.single i i 1 : Matrix (Fin 2) (Fin 2) B) ∈ A ↔
        ∃ c : C, x = (c : B) * a) →
      (Matrix.single i i 1 : Matrix (Fin 2) (Fin 2) B) ∈ A →
      a ∈ C ∧ ∀ x : B,
        (x • (Matrix.single i i 1 : Matrix (Fin 2) (Fin 2) B) ∈ A ↔ x ∈ C) := by
    intro i a hchar hmem
    have h1mem : (1 : B) • (Matrix.single i i 1 : Matrix (Fin 2) (Fin 2) B) ∈ A := by
      rw [one_smul]; exact hmem
    obtain ⟨c, hc⟩ := (hchar 1).mp h1mem
    have hcu : IsUnit c := by
      refine isUnit_of_isClosed_of_notMem_maximalIdeal hadic hclosed c ?_
      intro hcm
      have hone' : (1 : B) ∈ IsLocalRing.maximalIdeal B := by
        rw [hc]
        exact Ideal.mul_mem_right _ _ hcm
      exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top
        (Ideal.eq_top_iff_one _ |>.mpr hone')
    obtain ⟨cu, hcu'⟩ := hcu
    have haC : a ∈ C := by
      have hinv : (((cu⁻¹ : Cˣ) : C) : B) * (((cu : Cˣ) : C) : B) = 1 := by
        exact_mod_cast congrArg (fun z : C => (z : B)) cu.inv_mul
      have hval : a = (((cu⁻¹ : Cˣ) : C) : B) := by
        calc a = 1 * a := (one_mul a).symm
        _ = ((((cu⁻¹ : Cˣ) : C) : B) * (((cu : Cˣ) : C) : B)) * a := by rw [hinv]
        _ = (((cu⁻¹ : Cˣ) : C) : B) * ((((cu : Cˣ) : C) : B) * a) := by ring
        _ = (((cu⁻¹ : Cˣ) : C) : B) * 1 := by rw [hcu', ← hc]
        _ = (((cu⁻¹ : Cˣ) : C) : B) := by ring
      rw [hval]
      exact ((cu⁻¹ : Cˣ) : C).2
    refine ⟨haC, fun x => ⟨?_, ?_⟩⟩
    · intro hx
      obtain ⟨c', hc'⟩ := (hchar x).mp hx
      rw [hc']
      exact C.mul_mem c'.2 haC
    · intro hx
      refine (hchar x).mpr ⟨⟨x, hx⟩ * c, ?_⟩
      have hxc : ((⟨x, hx⟩ * c : C) : B) * a = x * ((c : B) * a) := by
        push_cast; ring
      rw [hxc, ← hc, mul_one]
  obtain ⟨ha00C, hI00'⟩ := hdiag 0 a00 hI00 hE00
  obtain ⟨ha11C, hI11'⟩ := hdiag 1 a11 hI11 hE11
  -- STEP 4: `a₀₁·a₁₀ ∈ I₀₀ = C`
  have hprod : (a01 * a10) ∈ C := by
    refine (hI00' (a01 * a10)).mp ?_
    have hx01 : a01 • (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) B) ∈ A :=
      (hI01 a01).mpr ⟨1, by simp⟩
    have hx10 : a10 • (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) B) ∈ A :=
      (hI10 a10).mpr ⟨1, by simp⟩
    have hmul : (a01 • (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) B))
        * (a10 • (Matrix.single 1 0 1 : Matrix (Fin 2) (Fin 2) B))
        = (a01 * a10) • (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) B) := by
      ext p q
      fin_cases p <;> fin_cases q <;>
        simp [Matrix.single, Matrix.mul_apply, mul_comm]
    rw [hAAsub] at hx01 hx10 ⊢
    rw [← hmul]
    exact Asub.mul_mem hx01 hx10
  exact ⟨a01, a10, hu01, hprod, hI01, hI10, hI00', hI11'⟩

open scoped Matrix in
/-- **Carayol's Théorème 1, step 2c: a `C`-order CONTAINING `E₁₁` is
conjugate into `M₂(C)`** (PROVEN 2026-07-26 over the single sub-leaf
`exists_peirceGenerators_of_single_mem` above; cut 2026-07-26 out of
`exists_conj_entries_mem_of_basis_repr_mem`; PURE ALGEBRA — this is the
Peirce/grading core of the theorem and all that remains of it): the
hypotheses are verbatim those of
`exists_conj_entries_mem_of_basis_repr_mem` PLUS `hone`, which says that
the matrix unit `E₁₁` already lies in the order `A' = ∑ᵢ C·bᵢ`. The
reduction of the general case to this one is PROVEN below, by lifting an
idempotent and conjugating it to `E₁₁`.

THE GRADING ARGUMENT, IN THE COORDINATES THIS FILE ALREADY HAS. Work with
the four `C`-submodules of `B`

    Iᵢⱼ := {x : B | x · Eᵢⱼ ∈ A'},      A' = ∑ᵢ C·bᵢ.

The PROVEN `mem_iff_smul_single_mem` above says exactly
`A' = {M | ∀ i j, Mᵢⱼ ∈ Iᵢⱼ}` — that is the Peirce decomposition, with no
direct sums to construct — and multiplicativity of `A'` gives
`Iᵢⱼ · Iⱼₗ ⊆ Iᵢₗ`, while `E₁₁, E₂₂ ∈ A'` gives `1 ∈ I₁₁ ∩ I₂₂`. Five steps
were listed here; **steps 1–4 are now the sub-leaf
`exists_peirceGenerators_of_single_mem` above, and step 5 is PROVEN below**,
so this node is closed over that one leaf. The list is kept because it is
the map of the remaining work:

1. *Each `Iᵢⱼ` is a PRINCIPAL `C`-submodule* `Iᵢⱼ = C·aᵢⱼ`. This is the
   one genuinely module-theoretic step: `A'` is free of rank `4` over the
   local `C` (`isLocalRing_of_isClosed_subring`, `b` being `C`-linearly
   independent because it is `B`-linearly independent), and the four
   `Iᵢⱼ` are its `C`-module direct summands, hence finitely generated
   projective, hence FREE over the local `C`, with ranks summing to `4`;
   each is nonzero because `A'` contains a `B`-basis of `M₂(B)`, so each
   rank is exactly `1`.
2. *`a₁₂` and `a₂₁` are UNITS OF `B`.* The `B`-span of `A'` is
   `{M | Mᵢⱼ ∈ B·Iᵢⱼ}` and equals `M₂(B)`, so `B·aᵢⱼ = B`; `B` is local,
   so `aᵢⱼ ∉ 𝔪`.
3. *`I₁₁ = I₂₂ = C`.* Write `1 = c·a₁₁` with `c ∈ C`. Then `c` is a unit
   of `B`, so `c ∈ C^×` by the PROVEN
   `isUnit_of_isClosed_of_notMem_maximalIdeal` — THIS is where closedness
   and the finite residue field re-enter, and it is the only place — hence
   `a₁₁ = c⁻¹ ∈ C` and `I₁₁ = C·a₁₁ = C`. Same for `I₂₂`.
4. *`a₁₂·a₂₁ ∈ C^×`*: it lies in `I₁₁ = C` by step 1, and is a unit of `B`
   by step 2, so again `isUnit_of_isClosed_of_notMem_maximalIdeal`.
5. *Conjugate.* PROVEN below. The conjugator is `E = diag(1, a₁₂⁻¹)` —
   **not** `diag(1, a₁₂)`, which is what this line used to say and which
   conjugates the wrong way: with `E = diag(d₁, d₂)` one has
   `(E⁻¹ M E)ᵢⱼ = dᵢ⁻¹ Mᵢⱼ dⱼ`, so it is `d₂ = a₁₂⁻¹` that sends
   `I₁₂ = C·a₁₂` into `C`. (The rest of the old line was already computing
   with `a₁₂⁻¹`, so only the displayed matrix was wrong.) The corners then
   become `I'₁₂ = I₁₂·a₁₂⁻¹ = C`, `I'₂₁ = a₁₂·I₂₁ = C·a₁₂a₂₁ = C`, and
   `I'₁₁ = I'₂₂ = C` unchanged — the last because `B` is COMMUTATIVE, so
   the diagonal conjugation `x ↦ d x d⁻¹` is the identity. By
   `mem_iff_smul_single_mem` again, the conjugate of `A'` is exactly
   `M₂(C)`. Note `diag(1, a₁₂⁻¹)` fixes `E₁₁`, so it composes with the
   caller's conjugation without disturbing step 2c's hypothesis.

WHAT `hres` BUYS, AND WHY IT IS NOT DROPPABLE. `hres` is not used by the
grading argument itself; it is what makes the CALLER able to produce an
element of `A'` congruent to `E₁₁`, i.e. it is consumed in the reduction
below. Kept in this signature because the reduction and this core are two
halves of one theorem and a successor may wish to redistribute the work.
Without `hres` the residual algebra `A'/𝔪_C A'` is only a `k'`-FORM of
`M₂(k)` over the subfield `k' = C/𝔪_C ⊆ k` — a quaternion algebra — and
one needs Wedderburn's little theorem (`k'` finite ⟹ split) to find a
rank-one idempotent at all; over an INFINITE `k'` that form may be a
DIVISION algebra, `A'` a maximal order in it, and the statement outright
FALSE. That is the fallback route, recorded here deliberately.

References: Carayol, Contemp. Math. 165, Théorème 1; Nyssen, Math. Ann.
306; Auslander–Goldman, *The Brauer group of a commutative ring*. -/
theorem exists_conj_entries_mem_of_single_mem
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Finite (IsLocalRing.ResidueField B)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal B))
    (hcompl : IsAdicComplete (IsLocalRing.maximalIdeal B) B)
    (C : Subring B) (hclosed : IsClosed ((C : Subring B) : Set B))
    (hres : ∀ y : B, ∃ x : C, (x : B) - y ∈ IsLocalRing.maximalIdeal B)
    (S : Submonoid (Matrix (Fin 2) (Fin 2) B))
    (b : Module.Basis (Fin 4) B (Matrix (Fin 2) (Fin 2) B))
    (hbS : ∀ i : Fin 4, b i ∈ S)
    (hrepr : ∀ M ∈ S, ∀ i : Fin 4, b.repr M i ∈ C)
    (hone : ∀ i : Fin 4,
      b.repr (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) B) i ∈ C) :
    ∃ E : Matrix (Fin 2) (Fin 2) B, IsUnit E.det ∧
      ∀ M ∈ S, ∀ i j : Fin 2, (E⁻¹ * M * E) i j ∈ C := by
  classical
  -- the `C`-order `A' = ∑ᵢ C·bᵢ`, as a subring of `M₂(B)`
  set A : Subring (Matrix (Fin 2) (Fin 2) B) :=
    { carrier := {M | ∀ i, b.repr M i ∈ C}
      zero_mem' := by intro i; simp
      one_mem' := fun i => hrepr 1 S.one_mem i
      add_mem' := fun {x y} hx hy i => by simpa using C.add_mem (hx i) (hy i)
      neg_mem' := fun {x} hx i => by simpa using C.neg_mem (hx i)
      mul_mem' := by
        intro x y hx hy n
        have hxy : x * y = ∑ i, ∑ j, (b.repr x i * b.repr y j) • (b i * b j) := by
          conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [hxy]
        simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
        exact C.mul_mem (C.mul_mem (hx i) (hy j))
          (hrepr _ (S.mul_mem (hbS i) (hbS j)) n) }
  have hE11A : (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) B) ∈ A := hone
  -- the Peirce corner generators, from the sub-leaf
  obtain ⟨a01, a10, hu01, hprod, hI01, hI10, hI00, hI11⟩ :=
    exists_peirceGenerators_of_single_mem hadic hcompl C hclosed hres S b hbS
      hrepr hone
  obtain ⟨v, hv⟩ := hu01
  -- STEP 5: conjugate by `diag(1, a₀₁⁻¹)`
  refine ⟨Matrix.diagonal ![1, ((v⁻¹ : Bˣ) : B)], ?_, ?_⟩
  · rw [Matrix.det_diagonal]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul]
    exact (v⁻¹ : Bˣ).isUnit
  · have hEinv : (Matrix.diagonal ![1, ((v⁻¹ : Bˣ) : B)])⁻¹
        = Matrix.diagonal ![1, ((v : Bˣ) : B)] := by
      refine Matrix.inv_eq_right_inv ?_
      have hfun : (fun i => ![1, ((v⁻¹ : Bˣ) : B)] i * ![1, ((v : Bˣ) : B)] i)
          = (1 : Fin 2 → B) := by
        funext i; fin_cases i <;> simp
      rw [Matrix.diagonal_mul_diagonal, hfun]
      exact Matrix.diagonal_one
    intro M hM
    have hMA : M ∈ A := fun n => hrepr M hM n
    have hpeirce := (mem_iff_smul_single_mem A hE11A M).mp hMA
    have hentry : ∀ i j : Fin 2,
        ((Matrix.diagonal ![1, ((v⁻¹ : Bˣ) : B)])⁻¹ * M
          * Matrix.diagonal ![1, ((v⁻¹ : Bˣ) : B)]) i j
        = ![1, ((v : Bˣ) : B)] i * M i j * ![1, ((v⁻¹ : Bˣ) : B)] j := by
      intro i j
      rw [hEinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Fin.forall_fin_two, hentry, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, one_mul, mul_one]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (hI00 (M 0 0)).mp (hpeirce 0 0)
    · obtain ⟨c, hc⟩ := (hI01 (M 0 1)).mp (hpeirce 0 1)
      have key : M 0 1 * ((v⁻¹ : Bˣ) : B) = (c : B) := by
        rw [hc, ← hv, mul_assoc, Units.mul_inv, mul_one]
      rw [key]
      exact c.2
    · obtain ⟨c, hc⟩ := (hI10 (M 1 0)).mp (hpeirce 1 0)
      have key : ((v : Bˣ) : B) * M 1 0 = (c : B) * (a01 * a10) := by
        rw [hc, hv]; ring
      rw [key]
      exact C.mul_mem c.2 hprod
    · have h := (hI11 (M 1 1)).mp (hpeirce 1 1)
      have key : ((v : Bˣ) : B) * M 1 1 * ((v⁻¹ : Bˣ) : B) = M 1 1 := by
        rw [mul_comm ((v : Bˣ) : B) (M 1 1), mul_assoc, Units.mul_inv, mul_one]
      rw [key]
      exact h

open scoped Matrix in
/-- **Carayol's Théorème 1, step 2: a `C`-order in `M₂(B)` with split
residual algebra is conjugate into `M₂(C)`** (PROVEN 2026-07-26 over the
single sub-leaf `exists_conj_entries_mem_of_single_mem`, the two
auxiliary nodes `exists_isIdempotentElem_mem_of_sq_sub_mem` and
`exists_conj_eq_single_of_mul_self` being PROVEN; cut 2026-07-26
out of `exists_framedGaloisRep_baseChange_traceSubring`; PURE ALGEBRA —
no Galois representation and no arithmetic occurs in it): let `B` be a
local topological ring whose topology is `𝔪`-adic, which is `𝔪`-adically
complete and separated, and whose residue field is FINITE; let `C ⊆ B` be
a CLOSED subring; and let `S` be a multiplicative set of matrices
containing a `B`-basis `b` of `M₂(B)` and having all its `b`-coordinates
in `C`. Then a single conjugation `M ↦ E⁻¹ M E` by an invertible
`E ∈ M₂(B)` moves every member of `S` into `M₂(C)`.

This is the SPLITTING of the order, and every hypothesis is load-bearing.

Write `A' := ∑ᵢ C·bᵢ`. It is a subring of `M₂(B)` — it is the `C`-span of
the multiplicative `S`, and `1 ∈ S` — free of rank `4` over `C`; and
because `C` is closed, `𝔪_C = 𝔪 ∩ C`
(`maximalIdeal_eq_comap_of_isClosed_subring`), so `A' / 𝔪_C A' ↪ M₂(k)`
is a `k'`-subalgebra of `k'`-dimension `4`, where `k' = C/𝔪_C ⊆ k`.

The hypothesis `hres` — `C` meets every residue class of `B`, i.e. `C`
surjects onto the residue field — says exactly `k' = k`. So the image is
a `k`-subspace of `M₂(k)` of `k`-dimension `4`, hence ALL of `M₂(k)`:
`A'/𝔪_C A' ≅ M₂(k)` with nothing to prove. **`hres` is what makes this
leaf elementary**, and it is why no Brauer-group input is needed — see
the note below on what its absence would cost.

WHAT THE PROOF BELOW ESTABLISHES, all of it verified: that `A'` really is
a subring of `M₂(B)` (its `mul_mem'` is the expansion
`(∑ cᵢbᵢ)(∑ dⱼbⱼ) = ∑ cᵢdⱼ (bᵢbⱼ)` together with `bᵢbⱼ ∈ S`); that `A'` is
CLOSED, being the preimage of `C⁴` under the coordinate maps, which are
continuous because each is a fixed linear form in the matrix ENTRIES
(`basis_repr_eq_sum_entries`); that `A'` contains an element `x` with
`x ≡ E₁₁ mod 𝔪` entrywise — this is the ONE place `hres` is consumed,
each coordinate of `E₁₁` being replaced by a `C`-element congruent to it —
hence with `x² ≡ x`; and, given the idempotent `u ∈ A'` produced by
`exists_isIdempotentElem_mem_of_sq_sub_mem` and the conjugation `E₀`
produced by `exists_conj_eq_single_of_mul_self`, that the WHOLE
hypothesis package transports along `M ↦ E₀⁻¹ M E₀` (a monoid isomorphism
and a `B`-linear automorphism at once) to an instance of
`exists_conj_entries_mem_of_single_mem`, whose conjugation `E₁` composes
with `E₀` into the required `E = E₀E₁`.

What is left open is therefore exactly ONE thing, the Peirce/grading
argument, which runs: after the
conjugation `E₁₁, E₂₂ ∈ A'` and `A' = ⨁ᵢⱼ EᵢᵢA'Eⱼⱼ` with each summand a
rank-one `C`-submodule `C·aᵢⱼ` of `B`. The diagonal ones contain `1` and
are closed under multiplication, so `a₁₁, a₂₂ ∈ C^×` and `A₁₁ = A₂₂ = C`;
then `a₁₂a₂₁` generates `A₁₁ = C`, so it is a unit of `C`, and the
further conjugation by `diag(1, a₁₂⁻¹)` turns `A'` into exactly `M₂(C)`.

WHY THE HYPOTHESES CANNOT BE DROPPED. Completeness and closedness are
both needed to lift the idempotent INSIDE `A'`.

WITHOUT `hres` THE LEAF IS STRICTLY HARDER, AND WITHOUT IT *AND*
FINITENESS IT IS FALSE. If `k'` is a proper subfield of `k`, then
`A'/𝔪_C A'` is only a `k'`-FORM of `M₂(k)` — a quaternion algebra over
`k'` — and one needs Wedderburn's little theorem (`k'` finite ⟹ the form
is split) to find the rank-one idempotent at all. Over an INFINITE `k'`
that form may be a DIVISION algebra, and then `A'` is a maximal order in
a division algebra, not `M₂(C)`, and the statement is FALSE. `hres`
removes that entire branch of the argument, together with its
missing-from-mathlib input (forms of `M₂` and Wedderburn); finiteness of
the residue field is retained only because the surrounding subring API
(`isUnit_of_isClosed_of_notMem_maximalIdeal`,
`maximalIdeal_eq_comap_of_isClosed_subring`) is stated with it.

`hres` is not an extra burden on the caller: for `C = traceSubring ℓ D.ρ`
it is exactly the Teichmüller-root clause of the generating set — every
residue class of `D.R` contains a Teichmüller root
(`exists_mem_teichmullerRoots_map_eq`, Hensel), and every Teichmüller
root lies in the trace subring
(`mem_traceSubring_of_mem_teichmullerRoots`). This is the repair that
also killed `subring_closure_charFrob_coeff_eq_top`; the residue field of
`R'` is `k` ON THE NOSE, not the Frobenius-trace subfield, so no descent
of `ρbar` to a trace field is needed anywhere in this cluster.

References: Carayol, Contemp. Math. 165, Théorème 1; Nyssen, Math. Ann.
306; Auslander–Goldman, *The Brauer group of a commutative ring*
(Azumaya algebras over local rings are split when residually split) — the
last needed only in the `hres`-free form of the statement. -/
theorem exists_conj_entries_mem_of_basis_repr_mem
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsLocalRing B] [Finite (IsLocalRing.ResidueField B)]
    (hadic : IsAdic (IsLocalRing.maximalIdeal B))
    (hcompl : IsAdicComplete (IsLocalRing.maximalIdeal B) B)
    (C : Subring B) (hclosed : IsClosed ((C : Subring B) : Set B))
    (hres : ∀ y : B, ∃ x : C, (x : B) - y ∈ IsLocalRing.maximalIdeal B)
    (S : Submonoid (Matrix (Fin 2) (Fin 2) B))
    (b : Module.Basis (Fin 4) B (Matrix (Fin 2) (Fin 2) B))
    (hbS : ∀ i : Fin 4, b i ∈ S)
    (hrepr : ∀ M ∈ S, ∀ i : Fin 4, b.repr M i ∈ C) :
    ∃ E : Matrix (Fin 2) (Fin 2) B, IsUnit E.det ∧
      ∀ M ∈ S, ∀ i j : Fin 2, (E⁻¹ * M * E) i j ∈ C := by
  classical
  -- the `C`-order `A' = ∑ᵢ C·bᵢ`, as a subring of `M₂(B)`
  set A : Subring (Matrix (Fin 2) (Fin 2) B) :=
    { carrier := {M | ∀ i, b.repr M i ∈ C}
      zero_mem' := by intro i; simp
      one_mem' := fun i => hrepr 1 S.one_mem i
      add_mem' := fun {x y} hx hy i => by simpa using C.add_mem (hx i) (hy i)
      neg_mem' := fun {x} hx i => by simpa using C.neg_mem (hx i)
      mul_mem' := by
        intro x y hx hy n
        have hxy : x * y = ∑ i, ∑ j, (b.repr x i * b.repr y j) • (b i * b j) := by
          conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [hxy]
        simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
        exact C.mul_mem (C.mul_mem (hx i) (hy j))
          (hrepr _ (S.mul_mem (hbS i) (hbS j)) n) } with hAdef
  have hmemA : ∀ M : Matrix (Fin 2) (Fin 2) B, M ∈ A ↔ ∀ i, b.repr M i ∈ C :=
    fun M => Iff.rfl
  -- each coordinate map is continuous, so the order is CLOSED
  have hcont : ∀ i : Fin 4,
      Continuous (fun M : Matrix (Fin 2) (Fin 2) B => b.repr M i) := by
    intro i
    have hEq : (fun M : Matrix (Fin 2) (Fin 2) B => b.repr M i) =
        fun M => ∑ p : Fin 2, ∑ q : Fin 2, M p q * b.repr (Matrix.single p q 1) i := by
      funext M
      exact basis_repr_eq_sum_entries b M i
    rw [hEq]
    refine continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ => ?_
    exact Continuous.mul (by fun_prop) continuous_const
  have hAclosed : IsClosed ((A : Subring (Matrix (Fin 2) (Fin 2) B)) :
      Set (Matrix (Fin 2) (Fin 2) B)) := by
    have hEq : ((A : Subring (Matrix (Fin 2) (Fin 2) B)) :
          Set (Matrix (Fin 2) (Fin 2) B))
        = ⋂ i : Fin 4, (fun M : Matrix (Fin 2) (Fin 2) B => b.repr M i) ⁻¹'
            (C : Set B) := by
      ext M
      simp [hmemA M, Set.mem_iInter]
    rw [hEq]
    exact isClosed_iInter fun i => hclosed.preimage (hcont i)
  -- `hres` puts an element congruent to `E₁₁` into the order
  set E11 : Matrix (Fin 2) (Fin 2) B := Matrix.single 0 0 1 with hE11
  have hE11sq : E11 * E11 = E11 := by rw [hE11]; simp
  choose cc hcc using fun i : Fin 4 => hres (b.repr E11 i)
  set x : Matrix (Fin 2) (Fin 2) B := ∑ i, ((cc i : B)) • b i with hx
  have hxA : x ∈ A := by
    rw [hmemA]
    intro n
    rw [hx]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Subring.sum_mem _ fun i _ => C.mul_mem (cc i).2 (hrepr _ (hbS i) n)
  have hxres : ∀ p q, (x - E11) p q ∈ IsLocalRing.maximalIdeal B := by
    have hdiff : x - E11 = ∑ i, ((cc i : B) - b.repr E11 i) • b i := by
      conv_lhs => rw [hx, ← b.sum_repr E11]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    intro p q
    rw [hdiff]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hcc i)
  have hxsq : ∀ p q, (x * x - x) p q ∈ IsLocalRing.maximalIdeal B := by
    intro p q
    have hsplit : x * x - x = (x * x - E11 * E11) + (E11 - x) := by
      rw [hE11sq]; noncomm_ring
    rw [hsplit, Matrix.add_apply]
    refine Ideal.add_mem _ (matrix_sub_mem_mul _ hxres hxres p q) ?_
    have hneg : (E11 - x) p q = -((x - E11) p q) := by simp
    rw [hneg]
    exact neg_mem (hxres p q)
  -- lift it to a genuine idempotent of the order, and conjugate that to `E₁₁`
  obtain ⟨u, huA, hu2, hures⟩ :=
    exists_isIdempotentElem_mem_of_sq_sub_mem hadic hcompl A hAclosed hxA hxsq
  have hures' : ∀ p q, (u - E11) p q ∈ IsLocalRing.maximalIdeal B := by
    intro p q
    have hsplit : u - E11 = (u - x) + (x - E11) := by noncomm_ring
    rw [hsplit, Matrix.add_apply]
    exact Ideal.add_mem _ (hures p q) (hxres p q)
  obtain ⟨E₀, hE₀det, hE₀u⟩ := exists_conj_eq_single_of_mul_self hu2 hures'
  have hinv1 : E₀⁻¹ * E₀ = 1 := Matrix.nonsing_inv_mul _ hE₀det
  have hinv2 : E₀ * E₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hE₀det
  -- transport the whole hypothesis package along `M ↦ E₀⁻¹ M E₀`
  set Φ : Matrix (Fin 2) (Fin 2) B →* Matrix (Fin 2) (Fin 2) B :=
    { toFun := fun M => E₀⁻¹ * M * E₀
      map_one' := by simp only [mul_one]; exact hinv1
      map_mul' := fun M N => by
        show E₀⁻¹ * (M * N) * E₀ = (E₀⁻¹ * M * E₀) * (E₀⁻¹ * N * E₀)
        have h1 : (E₀⁻¹ * M * E₀) * (E₀⁻¹ * N * E₀)
            = E₀⁻¹ * M * (E₀ * E₀⁻¹) * N * E₀ := by noncomm_ring
        rw [h1, hinv2, mul_one]
        noncomm_ring } with hΦ
  set Ψ : Matrix (Fin 2) (Fin 2) B ≃ₗ[B] Matrix (Fin 2) (Fin 2) B :=
    { toFun := fun M => E₀⁻¹ * M * E₀
      map_add' := fun M N => by noncomm_ring
      map_smul' := fun c M => by simp [Matrix.smul_mul]
      invFun := fun M => E₀ * M * E₀⁻¹
      left_inv := fun M => by
        show E₀ * (E₀⁻¹ * M * E₀) * E₀⁻¹ = M
        have h1 : E₀ * (E₀⁻¹ * M * E₀) * E₀⁻¹ = (E₀ * E₀⁻¹) * M * (E₀ * E₀⁻¹) := by
          noncomm_ring
        rw [h1, hinv2, one_mul, mul_one]
      right_inv := fun M => by
        show E₀⁻¹ * (E₀ * M * E₀⁻¹) * E₀ = M
        have h1 : E₀⁻¹ * (E₀ * M * E₀⁻¹) * E₀ = (E₀⁻¹ * E₀) * M * (E₀⁻¹ * E₀) := by
          noncomm_ring
        rw [h1, hinv1, one_mul, mul_one] } with hΨ
  have hΨΦ : ∀ M, Ψ M = Φ M := fun M => rfl
  have hreprmap : ∀ (M : Matrix (Fin 2) (Fin 2) B) (i : Fin 4),
      (b.map Ψ).repr M i = b.repr (Ψ.symm M) i := by
    intro M i
    rw [Module.Basis.map_repr]
    rfl
  have hbS' : ∀ i : Fin 4, (b.map Ψ) i ∈ S.map Φ := by
    intro i
    rw [Module.Basis.map_apply]
    exact ⟨b i, hbS i, (hΨΦ (b i)).symm⟩
  have hrepr' : ∀ M ∈ S.map Φ, ∀ i : Fin 4, (b.map Ψ).repr M i ∈ C := by
    rintro _ ⟨N, hN, rfl⟩ i
    rw [hreprmap]
    rw [show Ψ.symm (Φ N) = N from by rw [← hΨΦ N]; exact Ψ.symm_apply_apply N]
    exact hrepr N hN i
  have hone' : ∀ i : Fin 4, (b.map Ψ).repr E11 i ∈ C := by
    intro i
    rw [hreprmap]
    rw [show Ψ.symm E11 = u from by
      rw [hE11, ← hE₀u]
      exact Ψ.symm_apply_apply u]
    exact (hmemA u).mp huA i
  obtain ⟨E₁, hE₁det, hE₁mem⟩ :=
    exists_conj_entries_mem_of_single_mem hadic hcompl C hclosed hres (S.map Φ)
      (b.map Ψ) hbS' hrepr' hone'
  refine ⟨E₀ * E₁, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact hE₀det.mul hE₁det
  · intro M hM i j
    have hMS' : Φ M ∈ S.map Φ := ⟨M, hM, rfl⟩
    have hres2 := hE₁mem (Φ M) hMS' i j
    have heq : (E₀ * E₁)⁻¹ * M * (E₀ * E₁) = E₁⁻¹ * (E₀⁻¹ * M * E₀) * E₁ := by
      rw [Matrix.mul_inv_rev]; noncomm_ring
    rw [heq]
    exact hres2

end GaloisRepresentation
