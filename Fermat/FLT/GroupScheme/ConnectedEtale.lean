/-
ConnectedEtale.lean — own work for the Fermat project.

# The connected component of a finite flat Hopf algebra over a
# complete DVR: the counit idempotent

Core of the connected–étale decomposition used by the Hopf-package
sorry nodes of `HardlyRamified/ModThree.lean` and
`HardlyRamified/Threeadic.lean` (Tate, *Finite flat group schemes*,
in Cornell–Silverman–Stevens; Raynaud 1974).

Over a complete Noetherian local domain `A`, a module-finite
bialgebra `G` carries a PRIMITIVE idempotent `e₀` with counit value
`1` whose comultiplication absorbs `e₀ ⊗ e₀`:

* `exists_minimal_counit_idempotent` — a minimal idempotent with
  counit `1` exists (Noetherian maximality on the complement ideals
  `⟨1 − e⟩`);
* `mul_eq_zero_or_mul_eq_of_minimal` — minimality forces
  primitivity: `x·e₀ ∈ {0, e₀}` for every idempotent `x`;
* `exists_pow_mem_of_counit_mem_maximalIdeal` — the corner `Ge₀` is
  local-with-residue-field-`𝓀(A)` modulo `𝔪_A`: corner elements with
  counit in `𝔪_A` are nilpotent modulo `𝔪_A G` (henselian idempotent
  lifting along the complete pair `(C, 𝔪_A C)` plus artinian
  locality);
* `Bialgebra.exists_connected_counit_idempotent` — the package,
  including the comultiplication absorption
  `Δe₀·(e₀ ⊗ e₀) = e₀ ⊗ e₀` (the connected component is closed under
  the group law: the defect is an idempotent which is nilpotent
  modulo `𝔪_A (G ⊗ G)`, hence lands in the Jacobson radical and
  dies);
* `IsAdicComplete` for `𝒪ᵥ = adicCompletionIntegers ℚ v` — the
  gateway instance that makes all of the above available over the
  local integer rings of the tree's Galois vocabulary (transport of
  the mathlib `IsNonarchimedeanLocalField` completeness along the
  identity of subrings `𝒪[K_v] = 𝒪ᵥ`).
-/
module

public import Fermat.FLT.Mathlib.RingTheory.AdicCompletion.Finite
public import Fermat.FLT.Mathlib.NumberTheory.Padics.LocalField
public import Fermat.FLT.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
-- `LinearMap.convRing`: the CONVOLUTION RING on `G →ₗ[R] A`, in which
-- the `p`-torsion of a point of the kernel of reduction becomes a
-- binomial identity (the `ConvFiltration` section below)
public import Mathlib.RingTheory.Coalgebra.Convolution
-- `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` — Nakayama, the
-- endgame of the same argument
public import Mathlib.RingTheory.Nakayama
-- `Commute.add_pow` and `Nat.Prime.dvd_choose_self`: the binomial
-- expansion of `(1 + d)^p` and the `p`-divisibility of its middle
-- coefficients
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Dvd
-- `Φ_p(1) = p` and `Φ_n = ∏ (X − μ)` over the primitive roots: the
-- cyclotomic input `p ∣ (1 − ζ_p)^{p−1}` of the Oort–Tate node below
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Tactic.Module
-- the Galois/points vocabulary of the shared Oort–Tate `μ`-type node
-- below: `localInertiaGroup`, the vendored convolution monoid on the
-- geometric points of a Hopf order, `cyclotomicCharacter`, `ℤ_[p]`
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
-- `HopfAlgebra.antipodeAlgHom` and the `WithConv` antipode lemmas,
-- used in the STATEMENT-adjacent helpers of the Oort–Tate node
public import Mathlib.RingTheory.HopfAlgebra.Convolution
-- the convolution/points transport toolkit (`liftEquiv_symm_convMul`,
-- `vendored_mul_eq_convMul`, `liftEquiv_symm_comp`), proof-body use
-- only in the displacement-connectedness lemma
import Fermat.FLT.Deformations.RepresentationTheory.FlatProlongation
-- `maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup` ("the fixed
-- field of local inertia is unramified") and `integralClosureInclusion`:
-- the ramification input of the Oort–Tate node, used only in the proof
-- of `mem_span_natCast_of_inertia_invariant`
import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField

@[expose] public section

open IsLocalRing

open scoped WithZero TensorProduct

/-! ### Transport of adic completeness to `adicCompletionIntegers` -/

/-- **A ring isomorphism carries the maximal ideal onto the maximal
ideal** (both rings local). -/
theorem map_maximalIdeal_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    (maximalIdeal R).map e = maximalIdeal S := by
  have h0 : (maximalIdeal R).map (e : R →+* S) = maximalIdeal S := by
    rw [Ideal.map_comap_of_equiv]
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ e.symm.surjective)
  exact h0

namespace IsDedekindDomain.HeightOneSpectrum

open ValuativeRel

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

/-- **The `ValuativeRel` integer subring of `K_v` is
`adicCompletionIntegers`**: the canonical `ValuativeRel` valuation of
the completion is equivalent to the `Valued` valuation, so the two
`≤ 1` loci coincide. -/
theorem integer_valuation_eq_adicCompletionIntegers :
    (𝒪[HeightOneSpectrum.adicCompletion ℚ v] :
      Subring (HeightOneSpectrum.adicCompletion ℚ v)) =
    (v.adicCompletionIntegers ℚ).toSubring := by
  ext x
  show x ∈ (ValuativeRel.valuation
    (HeightOneSpectrum.adicCompletion ℚ v)).integer ↔ _
  rw [Valuation.mem_integer_iff, ValuationSubring.mem_toSubring,
    mem_adicCompletionIntegers]
  exact Valuation.isEquiv_iff_val_le_one.mp
    (ValuativeRel.isEquiv
      (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion ℚ v))
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion ℚ v) ℤᵐ⁰))

/-- **`adicCompletionIntegers ℚ v` is adically complete** at its
maximal ideal: transport of the mathlib
`IsNonarchimedeanLocalField` completeness of `𝒪[K_v]` along the
subring identity above. The instance that unlocks the henselian
idempotent theory of the connected–étale decomposition at `3`. -/
instance : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers ℚ))
    (v.adicCompletionIntegers ℚ) := by
  haveI h1 : IsAdicComplete
      (maximalIdeal ↥(𝒪[HeightOneSpectrum.adicCompletion ℚ v] :
        Subring (HeightOneSpectrum.adicCompletion ℚ v)))
      ↥(𝒪[HeightOneSpectrum.adicCompletion ℚ v] :
        Subring (HeightOneSpectrum.adicCompletion ℚ v)) :=
    inferInstance
  let e : ↥(𝒪[HeightOneSpectrum.adicCompletion ℚ v] :
      Subring (HeightOneSpectrum.adicCompletion ℚ v)) ≃+*
      ↥(v.adicCompletionIntegers ℚ) :=
    RingEquiv.subringCongr (integer_valuation_eq_adicCompletionIntegers v)
  have h2 := (IsAdicComplete.congr_ringEquiv (maximalIdeal _) e).mpr h1
  rwa [map_maximalIdeal_ringEquiv e] at h2

end IsDedekindDomain.HeightOneSpectrum

/-! ### The minimal counit idempotent of a finite bialgebra -/

/-- A bialgebra over a nontrivial ring is nontrivial: the counit is
unital. -/
theorem Bialgebra.nontrivial_of_counit (A : Type*) {G : Type*}
    [CommRing A] [Nontrivial A] [CommRing G] [Bialgebra A G] :
    Nontrivial G := by
  refine ⟨0, 1, fun h01 => ?_⟩
  have h := congrArg (Coalgebra.counit (R := A)) h01
  rw [map_zero, Bialgebra.counit_one] at h
  exact zero_ne_one h

section CounitIdempotent

variable {A : Type*} {G : Type*} [CommRing A] [IsDomain A]
  [CommRing G] [Bialgebra A G]

omit [IsDomain A] in
/-- **A minimal idempotent with counit `1` exists**: Noetherian
maximality applied to the complement ideals `⟨1 − e⟩`. Minimality is
stated as: every idempotent `y ≤ e₀` with `ε(y) = 1` equals `e₀`. -/
theorem exists_minimal_counit_idempotent
    [IsNoetherianRing A] [Module.Finite A G] :
    ∃ e₀ : G, IsIdempotentElem e₀ ∧
      Coalgebra.counit (R := A) e₀ = (1 : A) ∧
      (∀ y : G, IsIdempotentElem y → y * e₀ = y →
        Coalgebra.counit (R := A) y = (1 : A) → y = e₀) := by
  haveI : IsNoetherianRing G := IsNoetherianRing.of_finite A G
  -- the set of complement ideals of counit-one idempotents
  set T : Set (Ideal G) := {J | ∃ e : G, IsIdempotentElem e ∧
    Coalgebra.counit (R := A) e = (1 : A) ∧ J = Ideal.span {1 - e}}
    with hT
  have hne : T.Nonempty := by
    refine ⟨Ideal.span {1 - 1}, 1, ?_, Bialgebra.counit_one, rfl⟩
    show (1 : G) * 1 = 1
    rw [mul_one]
  obtain ⟨J, hJT, hJmax⟩ :=
    (set_has_maximal_iff_noetherian.mpr inferInstance) T hne
  obtain ⟨e₀, he₀, hε₀, hJ⟩ := hJT
  refine ⟨e₀, he₀, hε₀, ?_⟩
  intro y hy hye hεy
  -- the complement ideal of `y` contains the complement ideal of `e₀`
  have hle : Ideal.span {1 - e₀} ≤ Ideal.span {(1 : G) - y} := by
    refine Ideal.span_le.mpr ?_
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    have hfac : ((1 : G) - y) * (1 - e₀) = 1 - e₀ := by
      have : ((1 : G) - y) * (1 - e₀) = 1 - e₀ - (y - y * e₀) := by ring
      rw [this, hye, sub_self, sub_zero]
    rw [← hfac]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  -- maximality forces equality of the complement ideals
  have heq : Ideal.span {(1 : G) - y} = Ideal.span {1 - e₀} := by
    by_contra hne'
    have hlt : J < Ideal.span {(1 : G) - y} := by
      rw [hJ]
      exact lt_of_le_of_ne hle (fun h => hne' h.symm)
    exact hJmax (Ideal.span {(1 : G) - y}) ⟨y, hy, hεy, rfl⟩ hlt
  -- extract `1 − y = g·(1 − e₀)` and multiply by `e₀`
  have hmem : (1 : G) - y ∈ Ideal.span {(1 : G) - e₀} := by
    rw [← heq]
    exact Ideal.subset_span rfl
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hmem
  have h1 : ((1 : G) - y) * e₀ = 0 := by
    rw [← hg]
    have hexp : g * (1 - e₀) * e₀ = g * (e₀ - e₀ * e₀) := by ring
    rw [hexp, he₀.eq, sub_self, mul_zero]
  have he₀y : e₀ - y * e₀ = 0 := by
    have h3 : ((1 : G) - y) * e₀ = e₀ - y * e₀ := by ring
    rw [h3] at h1
    exact h1
  have h3 : y * e₀ = e₀ := (sub_eq_zero.mp he₀y).symm
  rw [← hye, h3]

/-- **Minimality forces primitivity**: `x·e₀ ∈ {0, e₀}` for every
idempotent `x` — the counit of the idempotent `x·e₀` is `0` or `1`
in the domain `A`; in the first case `e₀ − x·e₀` is a counit-one
idempotent below `e₀`, in the second `x·e₀` itself is. -/
theorem mul_eq_zero_or_mul_eq_of_minimal
    {e₀ : G} (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := A) e₀ = (1 : A))
    (hmin : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := A) y = (1 : A) → y = e₀)
    (x : G) (hx : IsIdempotentElem x) :
    x * e₀ = 0 ∨ x * e₀ = e₀ := by
  set y : G := x * e₀ with hy
  have hyidem : IsIdempotentElem y := by
    show y * y = y
    calc x * e₀ * (x * e₀) = (x * x) * (e₀ * e₀) := by ring
      _ = x * e₀ := by rw [hx.eq, he₀.eq]
  have hye : y * e₀ = y := by
    show x * e₀ * e₀ = x * e₀
    calc x * e₀ * e₀ = x * (e₀ * e₀) := by ring
      _ = x * e₀ := by rw [he₀.eq]
  have hεx : Coalgebra.counit (R := A) y =
      Coalgebra.counit (R := A) x * (1 : A) := by
    rw [hy, Bialgebra.counit_mul, hε₀]
  have hεidem : IsIdempotentElem (Coalgebra.counit (R := A) x) := by
    show _ * _ = _
    rw [← Bialgebra.counit_mul, hx.eq]
  rcases hεidem.eq_zero_or_eq_one_of_isDomain with h0 | h1
  · -- counit of the corner piece is `0`: the complement is minimal
    refine Or.inl ?_
    have hz : IsIdempotentElem (e₀ - y) := by
      show (e₀ - y) * (e₀ - y) = e₀ - y
      have hexp : (e₀ - y) * (e₀ - y) =
          e₀ * e₀ - (y * e₀ + y * e₀ - y * y) := by ring
      rw [hexp, he₀.eq, hye, hyidem.eq]
      ring
    have hze : (e₀ - y) * e₀ = e₀ - y := by
      have hexp : (e₀ - y) * e₀ = e₀ * e₀ - y * e₀ := by ring
      rw [hexp, he₀.eq, hye]
    have hεz : Coalgebra.counit (R := A) (e₀ - y) = (1 : A) := by
      rw [map_sub, hε₀, hεx, h0, zero_mul, sub_zero]
    have hzz := hmin _ hz hze hεz
    -- `e₀ − y = e₀` forces `y = 0`
    have h2 := congrArg (e₀ - ·) hzz
    simpa using h2
  · -- counit of the corner piece is `1`: it is minimal itself
    exact Or.inr (hmin y hyidem hye (by rw [hεx, h1, one_mul]))

/-- **Corner nilpotency mod `𝔪`**: over a complete Noetherian local
ring, if `e₀` is a minimal counit-one idempotent of the finite
bialgebra `G`, then every corner element `x = x·e₀` whose counit lies
in `𝔪_A` is nilpotent modulo `𝔪_A G`. The corner of the artinian
reduction `G/𝔪G` is local: a non-nilpotent corner element would
produce (by artinian stabilization of the powers) a nonzero
counit-zero idempotent below `ē₀`, which lifts along the henselian
pair `(G, 𝔪G)` and contradicts minimality. -/
theorem exists_pow_mem_of_counit_mem_maximalIdeal
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Module.Finite A G]
    {e₀ : G} (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := A) e₀ = (1 : A))
    (hmin : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := A) y = (1 : A) → y = e₀)
    {x : G} (hxe : x * e₀ = x)
    (hεx : Coalgebra.counit (R := A) x ∈ maximalIdeal A) :
    ∃ n : ℕ, x ^ n ∈ (maximalIdeal A).map (algebraMap A G) := by
  haveI : Nontrivial G := Bialgebra.nontrivial_of_counit A
  set M : Ideal G := (maximalIdeal A).map (algebraMap A G) with hM
  -- the counit maps `M` into `𝔪`
  have hMcomap : M ≤ (maximalIdeal A).comap
      (Bialgebra.counitAlgHom A G : G →+* A) := by
    rw [hM, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    simpa using ha
  have hMne : M ≠ ⊤ := by
    intro htop
    have h1 : (1 : G) ∈ M := htop ▸ Submodule.mem_top
    have h2 := hMcomap h1
    rw [Ideal.mem_comap, map_one] at h2
    exact (Ideal.ne_top_iff_one _).mp
      (Ideal.IsMaximal.ne_top inferInstance) h2
  -- `M` lies over `𝔪`, giving the residue algebra structure
  haveI hlies : M.LiesOver (maximalIdeal A) := ⟨by
    refine le_antisymm Ideal.le_comap_map (IsLocalRing.le_maximalIdeal ?_)
    intro htop
    apply hMne
    rw [Ideal.eq_top_iff_one] at htop ⊢
    have := Ideal.mem_comap.mp htop
    rwa [map_one] at this⟩
  haveI : IsArtinianRing (A ⧸ maximalIdeal A) := by
    letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
    exact DivisionRing.instIsArtinianRing
  haveI : IsArtinianRing (G ⧸ M) :=
    IsArtinianRing.of_finite (A ⧸ maximalIdeal A) (G ⧸ M)
  haveI : HenselianRing G M := HenselianRing.of_finite_algebra A G
  set π : G →+* G ⧸ M := Ideal.Quotient.mk M with hπ
  -- the reduced counit on the residue algebra
  set ε' : G ⧸ M →+* A ⧸ maximalIdeal A :=
    Ideal.quotientMap (maximalIdeal A)
      (Bialgebra.counitAlgHom A G : G →+* A) hMcomap with hε'
  have hε'mk : ∀ g : G, ε' (π g) =
      Ideal.Quotient.mk (maximalIdeal A) (Coalgebra.counit (R := A) g) := by
    intro g
    rw [hε', hπ, Ideal.quotientMap_mk]
    simp
  -- artinian stabilization of the powers of `π x`
  obtain ⟨m, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (π x) (1 : G ⧸ M)
  rw [smul_eq_mul, smul_eq_mul, mul_one] at hy
  set N : ℕ := m + 1 with hN
  have hstep : ∀ i : ℕ, (π x) ^ (m + i + 1) * y = (π x) ^ (m + i) := by
    intro i
    have h1 : (π x) ^ (m + i + 1) * y = (π x) ^ i * ((π x) ^ (m + 1) * y) := by
      ring
    rw [h1, hy, ← pow_add]
    ring_nf
  have hiter : ∀ i : ℕ, (π x) ^ N = (π x) ^ (N + i) * y ^ i := by
    intro i
    induction i with
    | zero => rw [pow_zero, mul_one, add_zero]
    | succ j ih =>
      have h1 : (π x) ^ (N + (j + 1)) * y ^ (j + 1) =
          ((π x) ^ (m + (j + 1) + 1) * y) * y ^ j := by
        rw [hN]
        ring
      rw [h1, hstep (j + 1)]
      have h2 : (π x) ^ (m + (j + 1)) * y ^ j = (π x) ^ (N + j) * y ^ j := by
        rw [hN]
        ring_nf
      rw [h2, ← ih]
  -- the idempotent produced by stabilization
  set e : G ⧸ M := (π x) ^ N * y ^ N with he_def
  have he : IsIdempotentElem e := by
    show e * e = e
    rw [he_def]
    have h1 : (π x) ^ N * y ^ N * ((π x) ^ N * y ^ N) =
        ((π x) ^ (N + N) * y ^ N) * y ^ N := by ring
    rw [h1, ← hiter N]
  have hxbar : π x * π e₀ = π x := by rw [← map_mul, hxe]
  have hee₀ : e * π e₀ = e := by
    rw [he_def]
    have h1 : (π x) ^ N * y ^ N * π e₀ = ((π x) ^ m * (π x * π e₀)) * y ^ N := by
      rw [hN]
      ring
    rw [h1, hxbar]
    ring
  have hεe : ε' e = 0 := by
    rw [he_def, map_mul, map_pow, hε'mk x, map_pow]
    have h0 : Ideal.Quotient.mk (maximalIdeal A)
        (Coalgebra.counit (R := A) x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hεx
    rw [h0, hN, zero_pow (Nat.succ_ne_zero m), zero_mul]
  -- lift `e` to an idempotent of `G` and apply the primitivity dichotomy
  obtain ⟨f, hf, hfmk⟩ := HenselianRing.exists_isIdempotentElem_mk_eq he
  rcases mul_eq_zero_or_mul_eq_of_minimal he₀ hε₀ hmin f hf with h0 | h1
  · -- `f·e₀ = 0`: reduction kills `e`, so `(π x)^N = 0`
    have hπ0 : e * π e₀ = 0 := by
      rw [← hfmk]
      show π f * π e₀ = 0
      rw [← map_mul, h0, map_zero]
    have he0 : e = 0 := by rw [← hee₀, hπ0]
    refine ⟨N, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    have hxN : π (x ^ N) = (π x) ^ N := map_pow π x N
    rw [hxN, hiter N]
    have h2 : (π x) ^ (N + N) * y ^ N = (π x) ^ N * e := by
      rw [he_def, pow_add]
      ring
    rw [h2, he0, mul_zero]
  · -- `f·e₀ = e₀`: then `e = π e₀` has counit both `0` and `1`
    exfalso
    have hπ1 : e * π e₀ = π e₀ := by
      rw [← hfmk]
      show π f * π e₀ = π e₀
      rw [← map_mul, h1]
    have heeq : e = π e₀ := by rw [← hee₀, hπ1]
    have hε1 : ε' (π e₀) = 1 := by
      rw [hε'mk e₀, hε₀, map_one]
    rw [heeq, hε1] at hεe
    haveI : Nontrivial (A ⧸ maximalIdeal A) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance)
    exact one_ne_zero hεe

omit [IsDomain A] in
/-- **The counit absorbs the comultiplication**: `ε_{G⊗G} ∘ Δ = ε`.
Choose a representation `Δg = ∑ xᵢ ⊗ yᵢ`; the tensor counit sends it
to `∑ ε(yᵢ)·ε(xᵢ) = ε(∑ ε(yᵢ)·xᵢ) = ε(g)` by the right counit
axiom. -/
theorem Bialgebra.counit_comulAlgHom_apply (g : G) :
    Coalgebra.counit (R := A) (Bialgebra.comulAlgHom A G g) =
      Coalgebra.counit (R := A) g := by
  set 𝓡 := Coalgebra.Repr.arbitrary A g with h𝓡
  have hmirror : ∑ i ∈ 𝓡.index,
      Coalgebra.counit (R := A) (𝓡.right i) • 𝓡.left i = g := by
    have h := Coalgebra.sum_tmul_counit_eq 𝓡
    have h2 : _root_.TensorProduct.rid A G (∑ i ∈ 𝓡.index,
          𝓡.left i ⊗ₜ[A] Coalgebra.counit (R := A) (𝓡.right i)) =
        _root_.TensorProduct.rid A G (g ⊗ₜ[A] (1 : A)) := by rw [h]
    simpa only [map_sum, _root_.TensorProduct.rid_tmul, one_smul] using h2
  calc Coalgebra.counit (R := A) (Bialgebra.comulAlgHom A G g)
      = Coalgebra.counit (R := A) (Coalgebra.comul (R := A) g) := by
        rw [Bialgebra.comulAlgHom_apply]
    _ = Coalgebra.counit (R := A)
        (∑ i ∈ 𝓡.index, 𝓡.left i ⊗ₜ[A] 𝓡.right i) := by rw [𝓡.eq]
    _ = ∑ i ∈ 𝓡.index,
        Coalgebra.counit (R := A) (𝓡.left i ⊗ₜ[A] 𝓡.right i) :=
          map_sum _ _ _
    _ = ∑ i ∈ 𝓡.index, Coalgebra.counit (R := A) (𝓡.right i) *
        Coalgebra.counit (R := A) (𝓡.left i) := by
          simp [smul_eq_mul]
    _ = Coalgebra.counit (R := A) (∑ i ∈ 𝓡.index,
        Coalgebra.counit (R := A) (𝓡.right i) • 𝓡.left i) := by
          rw [map_sum]
          simp [smul_eq_mul]
    _ = Coalgebra.counit (R := A) g := by rw [hmirror]

omit [IsDomain A] in
/-- A pure tensor with right factor in `𝔪G` lies in `𝔪(G⊗G)`. -/
theorem tmul_mem_map_of_right_mem [IsLocalRing A] (x : G) {m : G}
    (hm : m ∈ (maximalIdeal A).map (algebraMap A G)) :
    x ⊗ₜ[A] m ∈ (maximalIdeal A).map (algebraMap A (G ⊗[A] G)) := by
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at hm ⊢
  refine Submodule.smul_induction_on hm (fun a ha n _ => ?_)
    (fun u v hu hv => ?_)
  · rw [TensorProduct.tmul_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ hu hv

omit [IsDomain A] in
/-- A pure tensor with left factor in `𝔪G` lies in `𝔪(G⊗G)`. -/
theorem tmul_mem_map_of_left_mem [IsLocalRing A] (x : G) {m : G}
    (hm : m ∈ (maximalIdeal A).map (algebraMap A G)) :
    m ⊗ₜ[A] x ∈ (maximalIdeal A).map (algebraMap A (G ⊗[A] G)) := by
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at hm ⊢
  refine Submodule.smul_induction_on hm (fun a ha n _ => ?_)
    (fun u v hu hv => ?_)
  · rw [← TensorProduct.smul_tmul']
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [TensorProduct.add_tmul]
    exact Submodule.add_mem _ hu hv

/-- **Tensor primitivity** (Tate; "connected × connected is
connected"): over a complete Noetherian local domain, the tensor
square `e₀ ⊗ e₀` of a minimal counit-one idempotent is itself a
minimal counit-one idempotent of `G ⊗[A] G`. The defect
`d = e₀⊗e₀ − w` is an idempotent below `e₀ ⊗ e₀` with counit `0`;
splitting each corner tensor factor as
`u·e₀ = ε(u·e₀)·e₀ + (nilpotent mod 𝔪G)` (corner nilpotency in `G`)
shows `d` is a sum of nilpotents modulo `𝔪(G⊗G)` once the scalar part
`∑ ε⊗ε = ε(d) = 0` cancels; an idempotent that is nilpotent mod
`𝔪(G⊗G)` lies in `𝔪(G⊗G) ⊆ Jacobson(G⊗G)`, hence vanishes. -/
theorem Bialgebra.tmul_minimal_counit_idempotent
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Module.Finite A G]
    {e₀ : G} (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := A) e₀ = (1 : A))
    (hmin : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := A) y = (1 : A) → y = e₀) :
    ∀ w : G ⊗[A] G, IsIdempotentElem w → w * (e₀ ⊗ₜ[A] e₀) = w →
      Coalgebra.counit (R := A) w = (1 : A) → w = e₀ ⊗ₜ[A] e₀ := by
  intro w hw hwb hεw
  set b : G ⊗[A] G := e₀ ⊗ₜ[A] e₀ with hb_def
  have hb : IsIdempotentElem b := by
    show b * b = b
    rw [hb_def, Algebra.TensorProduct.tmul_mul_tmul, he₀.eq]
  -- the defect idempotent `d = b − w`, a counit-zero corner idempotent
  set d : G ⊗[A] G := b - w with hd_def
  have hd : IsIdempotentElem d := by
    show d * d = d
    rw [hd_def]
    have hexp : (b - w) * (b - w) = b * b - (w * b + (w * b - w * w)) := by
      ring
    rw [hexp, hb.eq, hwb, hw.eq]
    ring
  have hεd : Coalgebra.counit (R := A) d = 0 := by
    have hεb : Coalgebra.counit (R := A) b = 1 := by
      rw [hb_def]
      simp [hε₀]
    rw [hd_def, map_sub, hεw, hεb, sub_self]
  have hdb : d * b = d := by
    rw [hd_def]
    have hexp : (b - w) * b = b * b - w * b := by ring
    rw [hexp, hb.eq, hwb]
  -- reduction mod `𝔪(G⊗G)`, as an algebra map
  set MT : Ideal (G ⊗[A] G) :=
    (maximalIdeal A).map (algebraMap A (G ⊗[A] G)) with hMT_def
  set πₐ : G ⊗[A] G →ₐ[A] (G ⊗[A] G) ⧸ MT :=
    Ideal.Quotient.mkₐ A MT with hπₐ_def
  -- corner elements of `G` with counit zero give nilpotent reductions
  have hcorner_left : ∀ g : G, g * e₀ = g →
      Coalgebra.counit (R := A) g = 0 → ∀ y : G,
      IsNilpotent (πₐ (g ⊗ₜ[A] y)) := by
    intro g hge hεg y
    obtain ⟨k, hk⟩ := exists_pow_mem_of_counit_mem_maximalIdeal
      he₀ hε₀ hmin hge (by rw [hεg]; exact zero_mem _)
    refine ⟨k + 1, ?_⟩
    rw [← map_pow, Algebra.TensorProduct.tmul_pow]
    have hmem : g ^ (k + 1) ∈ (maximalIdeal A).map (algebraMap A G) := by
      rw [pow_succ]
      exact Ideal.mul_mem_right _ _ hk
    rw [hπₐ_def, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (tmul_mem_map_of_left_mem _ hmem)
  have hcorner_right : ∀ g : G, g * e₀ = g →
      Coalgebra.counit (R := A) g = 0 → ∀ y : G,
      IsNilpotent (πₐ (y ⊗ₜ[A] g)) := by
    intro g hge hεg y
    obtain ⟨k, hk⟩ := exists_pow_mem_of_counit_mem_maximalIdeal
      he₀ hε₀ hmin hge (by rw [hεg]; exact zero_mem _)
    refine ⟨k + 1, ?_⟩
    rw [← map_pow, Algebra.TensorProduct.tmul_pow]
    have hmem : g ^ (k + 1) ∈ (maximalIdeal A).map (algebraMap A G) := by
      rw [pow_succ]
      exact Ideal.mul_mem_right _ _ hk
    rw [hπₐ_def, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (tmul_mem_map_of_right_mem _ hmem)
  -- write `d` as a finite sum of corner tensors
  obtain ⟨S, hS⟩ := _root_.TensorProduct.exists_finset d
  have hdS : d = ∑ p ∈ S, (p.1 * e₀) ⊗ₜ[A] (p.2 * e₀) := by
    calc d = d * b := hdb.symm
      _ = (∑ p ∈ S, p.1 ⊗ₜ[A] p.2) * b := by rw [← hS]
      _ = ∑ p ∈ S, (p.1 * e₀) ⊗ₜ[A] (p.2 * e₀) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hb_def, Algebra.TensorProduct.tmul_mul_tmul]
  -- the ε-split of each corner factor
  set α : G × G → A := fun p => Coalgebra.counit (R := A) (p.1 * e₀)
    with hα_def
  set β : G × G → A := fun p => Coalgebra.counit (R := A) (p.2 * e₀)
    with hβ_def
  set n : G × G → G := fun p => p.1 * e₀ - α p • e₀ with hn_def
  set m : G × G → G := fun p => p.2 * e₀ - β p • e₀ with hm_def
  have hsplit1 : ∀ p : G × G, p.1 * e₀ = α p • e₀ + n p := by
    intro p
    rw [hn_def]
    ring_nf
  have hsplit2 : ∀ p : G × G, p.2 * e₀ = β p • e₀ + m p := by
    intro p
    rw [hm_def]
    ring_nf
  have hncorner : ∀ p : G × G, n p * e₀ = n p := by
    intro p
    rw [hn_def]
    show (p.1 * e₀ - α p • e₀) * e₀ = p.1 * e₀ - α p • e₀
    rw [sub_mul, mul_assoc, he₀.eq, smul_mul_assoc, he₀.eq]
  have hmcorner : ∀ p : G × G, m p * e₀ = m p := by
    intro p
    rw [hm_def]
    show (p.2 * e₀ - β p • e₀) * e₀ = p.2 * e₀ - β p • e₀
    rw [sub_mul, mul_assoc, he₀.eq, smul_mul_assoc, he₀.eq]
  have hnε : ∀ p : G × G, Coalgebra.counit (R := A) (n p) = 0 := by
    intro p
    rw [hn_def]
    show Coalgebra.counit (R := A) (p.1 * e₀ - α p • e₀) = 0
    rw [map_sub, map_smul, hε₀, smul_eq_mul, mul_one, hα_def, sub_self]
  have hmε : ∀ p : G × G, Coalgebra.counit (R := A) (m p) = 0 := by
    intro p
    rw [hm_def]
    show Coalgebra.counit (R := A) (p.2 * e₀ - β p • e₀) = 0
    rw [map_sub, map_smul, hε₀, smul_eq_mul, mul_one, hβ_def, sub_self]
  -- the total scalar weight is the counit of `d`, which vanishes
  have hsum0 : ∑ p ∈ S, α p * β p = 0 := by
    have h1 := congrArg (Coalgebra.counit (R := A)) hdS
    rw [hεd, map_sum] at h1
    have h2 : ∀ p ∈ S, Coalgebra.counit (R := A)
        ((p.1 * e₀) ⊗ₜ[A] (p.2 * e₀)) = α p * β p := by
      intro p _
      rw [hα_def, hβ_def]
      simp [mul_comm]
    rw [Finset.sum_congr rfl h2] at h1
    exact h1.symm
  -- the bilinear expansion of each summand
  have hexpand : ∀ p : G × G,
      (p.1 * e₀) ⊗ₜ[A] (p.2 * e₀) = (α p * β p) • b +
        (α p • (e₀ ⊗ₜ[A] m p) + β p • (n p ⊗ₜ[A] e₀) +
          n p ⊗ₜ[A] m p) := by
    intro p
    rw [hsplit1 p, hsplit2 p, hb_def]
    simp only [_root_.TensorProduct.tmul_add,
      _root_.TensorProduct.add_tmul, _root_.TensorProduct.tmul_smul,
      ← _root_.TensorProduct.smul_tmul']
    module
  -- the reduction of `d` is a sum of nilpotents
  have hnil : IsNilpotent (πₐ d) := by
    have hπd : πₐ d = ∑ p ∈ S,
        (α p • πₐ (e₀ ⊗ₜ[A] m p) + β p • πₐ (n p ⊗ₜ[A] e₀) +
          πₐ (n p ⊗ₜ[A] m p)) := by
      calc πₐ d = ∑ p ∈ S, πₐ ((p.1 * e₀) ⊗ₜ[A] (p.2 * e₀)) := by
            rw [hdS, map_sum]
        _ = ∑ p ∈ S, ((α p * β p) • πₐ b +
              (α p • πₐ (e₀ ⊗ₜ[A] m p) + β p • πₐ (n p ⊗ₜ[A] e₀) +
                πₐ (n p ⊗ₜ[A] m p))) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hexpand p]
            simp
        _ = (∑ p ∈ S, α p * β p) • πₐ b + ∑ p ∈ S,
              (α p • πₐ (e₀ ⊗ₜ[A] m p) + β p • πₐ (n p ⊗ₜ[A] e₀) +
                πₐ (n p ⊗ₜ[A] m p)) := by
            rw [Finset.sum_add_distrib, Finset.sum_smul]
        _ = ∑ p ∈ S,
              (α p • πₐ (e₀ ⊗ₜ[A] m p) + β p • πₐ (n p ⊗ₜ[A] e₀) +
                πₐ (n p ⊗ₜ[A] m p)) := by
            rw [hsum0, zero_smul, zero_add]
    rw [hπd]
    refine isNilpotent_sum fun p _ => ?_
    have h1 : IsNilpotent (α p • πₐ (e₀ ⊗ₜ[A] m p)) :=
      (hcorner_right (m p) (hmcorner p) (hmε p) e₀).smul (α p)
    have h2 : IsNilpotent (β p • πₐ (n p ⊗ₜ[A] e₀)) :=
      (hcorner_left (n p) (hncorner p) (hnε p) e₀).smul (β p)
    have h3 : IsNilpotent (πₐ (n p ⊗ₜ[A] m p)) :=
      hcorner_left (n p) (hncorner p) (hnε p) (m p)
    exact Commute.isNilpotent_add (Commute.all _ _)
      (Commute.isNilpotent_add (Commute.all _ _) h1 h2) h3
  -- a nilpotent idempotent reduction vanishes, so `d ∈ 𝔪(G⊗G)`
  have hdmem : d ∈ MT := by
    obtain ⟨K, hK⟩ := hnil
    have hπd0 : πₐ d = 0 := by
      rcases K with - | k
      · have h1 : (1 : (G ⊗[A] G) ⧸ MT) = 0 := by simpa using hK
        calc πₐ d = πₐ d * 1 := (mul_one _).symm
          _ = πₐ d * 0 := by rw [h1]
          _ = 0 := mul_zero _
      · have hidem : IsIdempotentElem (πₐ d) := by
          show πₐ d * πₐ d = πₐ d
          rw [← map_mul, hd.eq]
        rw [← hidem.pow_succ_eq k]
        exact hK
    rw [hπₐ_def, Ideal.Quotient.mkₐ_eq_mk] at hπd0
    exact Ideal.Quotient.eq_zero_iff_mem.mp hπd0
  -- `𝔪(G⊗G)` sits inside the Jacobson radical, killing the idempotent
  have hjac : MT ≤ Ideal.jacobson (⊥ : Ideal (G ⊗[A] G)) := by
    refine le_sInf ?_
    rintro J ⟨-, hJmax⟩
    haveI := hJmax
    have hcomax : (J.comap (algebraMap A (G ⊗[A] G))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
    rw [hMT_def, Ideal.map_le_iff_le_comap,
      IsLocalRing.eq_maximalIdeal hcomax]
  have hd0 : d = 0 := hd.eq_zero_of_mem_jacobson_bot (hjac hdmem)
  rw [hd_def] at hd0
  have := sub_eq_zero.mp hd0
  rw [hb_def] at this
  exact this.symm

/-- **The connected counit idempotent of a finite bialgebra** over a
complete Noetherian local domain: a primitive idempotent `e₀` with
counit `1` whose comultiplication absorbs `e₀ ⊗ e₀` — the coordinate
ring of the connected component of the identity, closed under the
group law. The absorption defect `z = e₀⊗e₀ − Δe₀·(e₀⊗e₀)` is an
idempotent of the corner of `e₀ ⊗ e₀` with counit `0`; corner
nilpotency puts it in `𝔪·(G⊗G)`, which lies inside the Jacobson
radical (integrality over the local base), where idempotents die. -/
theorem Bialgebra.exists_connected_counit_idempotent
    [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Module.Finite A G] :
    ∃ e₀ : G, IsIdempotentElem e₀ ∧
      Coalgebra.counit (R := A) e₀ = (1 : A) ∧
      (∀ y : G, IsIdempotentElem y → y * e₀ = y →
        Coalgebra.counit (R := A) y = (1 : A) → y = e₀) ∧
      Bialgebra.comulAlgHom A G e₀ * (e₀ ⊗ₜ[A] e₀) = e₀ ⊗ₜ[A] e₀ := by
  obtain ⟨e₀, he₀, hε₀, hmin⟩ :=
    exists_minimal_counit_idempotent (A := A) (G := G)
  refine ⟨e₀, he₀, hε₀, hmin, ?_⟩
  set a : G ⊗[A] G := Bialgebra.comulAlgHom A G e₀ with ha_def
  set b : G ⊗[A] G := e₀ ⊗ₜ[A] e₀ with hb_def
  have ha : IsIdempotentElem a := by
    show a * a = a
    rw [ha_def, ← map_mul, he₀.eq]
  have hb : IsIdempotentElem b := by
    show b * b = b
    rw [hb_def, Algebra.TensorProduct.tmul_mul_tmul, he₀.eq]
  have hεb : Coalgebra.counit (R := A) b = 1 := by
    rw [hb_def]
    simp [hε₀]
  set z : G ⊗[A] G := b - a * b with hz_def
  have hz : IsIdempotentElem z := by
    show z * z = z
    rw [hz_def]
    have hexp : (b - a * b) * (b - a * b) =
        b * b - a * (b * b) - (a * (b * b) - a * a * (b * b)) := by ring
    rw [hexp, hb.eq, ha.eq]
    ring
  have hzb : z * b = z := by
    rw [hz_def]
    have hexp : (b - a * b) * b = b * b - a * (b * b) := by ring
    rw [hexp, hb.eq]
  have hεz : Coalgebra.counit (R := A) z ∈ maximalIdeal A := by
    have hεa : Coalgebra.counit (R := A) a = 1 := by
      rw [ha_def, Bialgebra.counit_comulAlgHom_apply, hε₀]
    rw [hz_def, map_sub, Bialgebra.counit_mul, hεa, hεb, one_mul,
      sub_self]
    exact zero_mem _
  have hminT := Bialgebra.tmul_minimal_counit_idempotent he₀ hε₀ hmin
  obtain ⟨n, hzn⟩ :=
    exists_pow_mem_of_counit_mem_maximalIdeal hb hεb hminT hzb hεz
  -- `𝔪·(G⊗G)` is proper: the counit maps it into `𝔪`
  have hMTne : (maximalIdeal A).map (algebraMap A (G ⊗[A] G)) ≠ ⊤ := by
    have hMTcomap : (maximalIdeal A).map (algebraMap A (G ⊗[A] G)) ≤
        (maximalIdeal A).comap
          (Bialgebra.counitAlgHom A (G ⊗[A] G) : (G ⊗[A] G) →+* A) := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, Ideal.mem_comap]
      simpa using hr
    intro htop
    have h2 := hMTcomap
      (htop ▸ Submodule.mem_top : (1 : G ⊗[A] G) ∈ _)
    rw [Ideal.mem_comap, map_one] at h2
    exact (Ideal.ne_top_iff_one _).mp
      (Ideal.IsMaximal.ne_top inferInstance) h2
  -- the exponent is positive, so `z` itself lies in `𝔪·(G⊗G)`
  have hzmem : z ∈ (maximalIdeal A).map (algebraMap A (G ⊗[A] G)) := by
    rcases n with - | m
    · exact absurd ((Ideal.eq_top_iff_one _).mpr (by simpa using hzn))
        hMTne
    · rw [← hz.pow_succ_eq m]
      exact hzn
  -- `𝔪·(G⊗G)` sits inside the Jacobson radical, killing idempotents
  have hjac : (maximalIdeal A).map (algebraMap A (G ⊗[A] G)) ≤
      Ideal.jacobson (⊥ : Ideal (G ⊗[A] G)) := by
    refine le_sInf ?_
    rintro J ⟨-, hJmax⟩
    haveI := hJmax
    have hcomax : (J.comap (algebraMap A (G ⊗[A] G))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hcomax]
  have hz0 : z = 0 := hz.eq_zero_of_mem_jacobson_bot (hjac hzmem)
  rw [hz_def] at hz0
  exact (sub_eq_zero.mp hz0).symm

end CounitIdempotent

/-! ### The shared Oort–Tate `μ`-type node

The ONE order-`p` group-scheme classification input of the project,
stated in the neutral Hopf vocabulary of this file (no imports from
any consumer): a point of the generic fibre of a finite flat Hopf
order over `𝒪ᵥ ≅ ℤ_p` which is CONNECTED (value `1` on the connected
counit idempotent), killed by `p`, and whose convolution-cyclic group
is stable under local inertia, is moved by inertia to its
`χ_cyc mod p` convolution power — the `μ`-type/Oort–Tate dichotomy at
absolute ramification `e = 1`.

Consumers (2026-07-24 audit):
* `Modularity/Interface.lean`,
  `residual_triangular_sub_character_inertia_dichotomy_of_flat`
  (Eisenstein pillar E1b-i) — the triangular stable line is
  prime-field–valued (`χsub = ω^i`), so its cyclic point group is
  inertia-stable and the node applies verbatim;
* `HardlyRamified/ModThree.lean`,
  `inertiaFixed_connected_point_eq_one_at_three` — an inertia-FIXED
  point has inertia-stable cyclic group with exponent `m = 1`; the
  node then gives `φ = φ^n` for every `n ≡ χ_cyc(σ) mod 3`, and the
  surjectivity of `ω` from inertia onto `(ℤ/3)^×` (a fundamental-
  character input to be supplied by that owner) forces `φ = 1`;
* `HardlyRamified/Family.lean`,
  `connected_point_smul_eq_conv_pow_cyclotomicCharacter_of_hopf_package`
  — the order-`p^k` statement follows by dévissage along a stable
  filtration with cyclic-stable graded pieces (the `hchar`
  two-character hypothesis provides the one-dimensionality of the
  graded pieces); alternatively the proof of this node generalizes.
-/

namespace OortTate

open WithConv

/-- **The identity–antipode convolution cancels on the left**
(PROVEN; the `ConnectedEtale`-local copy of the ModThree helper —
this file is imported BY ModThree, so it cannot consume it):
`id ⋆ S = 1` in the convolution monoid of a commutative Hopf algebra,
reduced to the linear-level `LinearMap.id_mul_antipode`. -/
theorem toConv_id_mul_antipodeAlgHom
    {R A : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A] :
    toConv (AlgHom.id R A) * toConv (HopfAlgebra.antipodeAlgHom R A) =
      (1 : WithConv (A →ₐ[R] A)) := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  simp [LinearMap.id_mul_antipode]

/-- **Convolution right-inverse of a Hopf-algebra point** (PROVEN;
local copy, see `toConv_id_mul_antipodeAlgHom`): `χ ⋆ (χ ∘ S) = 1`
for any point `χ : A →ₐ[R] C` of a commutative Hopf algebra with
values in a commutative algebra — the postcomposition image of
`id ⋆ S = 1` under `χ`, which distributes over convolution. -/
theorem toConv_mul_comp_antipodeAlgHom
    {R A C : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
    [CommSemiring C] [Algebra R C] (χ : A →ₐ[R] C) :
    toConv χ * toConv (χ.comp (HopfAlgebra.antipodeAlgHom R A)) =
      (1 : WithConv (A →ₐ[R] C)) := by
  have h := AlgHom.comp_convMul_distrib χ (toConv (AlgHom.id R A))
    (toConv (HopfAlgebra.antipodeAlgHom R A))
  rw [toConv_id_mul_antipodeAlgHom] at h
  have h1 : χ.comp ((1 : WithConv (A →ₐ[R] A)).ofConv) =
      (1 : WithConv (A →ₐ[R] C)).ofConv := by
    rw [AlgHom.convOne_def, AlgHom.convOne_def, WithConv.ofConv_toConv,
      WithConv.ofConv_toConv, ← AlgHom.comp_assoc]
    congr 1
    refine AlgHom.ext fun r => ?_
    simp [Algebra.ofId_apply]
  rw [h1] at h
  have h2 : χ.comp ((toConv (AlgHom.id R A)).ofConv) = χ := AlgHom.comp_id χ
  rw [h2] at h
  exact (WithConv.ofConv_injective h).symm

section GenericPlace

open TensorProduct

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

local notation "𝒪ᵍᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "ℚᵍᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "ℚᵍᵥᵃˡᵍ" => AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Inertia congruence for convolution values** (PROVEN — the
generic-place statement of the identical at-`3` and at-`p` lemmas of
`ModThree.lean`/`Family.lean`, transplanted here so that the
displacement-connectedness lemma below is consumable without touching
any consumer file): for `σ` in the local inertia group at `v` and two
`𝒪ᵥ`-points `χ, ψ` of a module-finite Hopf order `G` (whose values
are automatically integral over `𝒪ᵥ`), the paired lift values of
`(σ ∘ χ, ψ)` and of `(χ, ψ)` agree on every tensor modulo the maximal
ideal of the integral closure of `𝒪ᵥ` in `ℚᵥᵃˡᵍ`: inertia moves
integral values only within the maximal ideal (the DEFINING property
of `localInertiaGroup`), and the difference on a pure tensor is an
`𝔪`-multiple of an integral value. -/
theorem lift_sub_lift_mem_of_localInertiaGroup
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵍᵥ G] [Module.Finite 𝒪ᵍᵥ G]
    (σ : Field.absoluteGaloisGroup ℚᵍᵥ)
    (hσ : σ ∈ localInertiaGroup v)
    (χ ψ : G →ₐ[𝒪ᵍᵥ] ℚᵍᵥᵃˡᵍ) (t : G ⊗[𝒪ᵍᵥ] G) :
    Algebra.TensorProduct.lift ((σ.toAlgHom.restrictScalars 𝒪ᵍᵥ).comp χ) ψ
        (fun _ _ => Commute.all _ _) t -
      Algebra.TensorProduct.lift χ ψ (fun _ _ => Commute.all _ _) t ∈
      Submodule.map (Algebra.linearMap (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) ℚᵍᵥᵃˡᵍ)
        (IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ)) := by
  haveI : Algebra.IsIntegral 𝒪ᵍᵥ G := Algebra.IsIntegral.of_finite 𝒪ᵍᵥ G
  induction t using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, sub_self]
    exact Submodule.zero_mem _
  | add x y hx hy =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Submodule.add_mem _ hx hy
  | tmul a b =>
    rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    have ha : IsIntegral 𝒪ᵍᵥ (χ a) :=
      (Algebra.IsIntegral.isIntegral (R := 𝒪ᵍᵥ) a).map χ
    have hb : IsIntegral 𝒪ᵍᵥ (ψ b) :=
      (Algebra.IsIntegral.isIntegral (R := 𝒪ᵍᵥ) b).map ψ
    set xa : IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ := ⟨χ a, ha⟩
    set xb : IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ := ⟨ψ b, hb⟩
    have hin := AddSubgroup.mem_inertia.mp hσ xa
    rw [Submodule.mem_toAddSubgroup] at hin
    have hval : algebraMap (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) ℚᵍᵥᵃˡᵍ
        (σ • xa - xa) = σ (χ a) - χ a := by
      rw [map_sub]
      congr 1
    have hkey : ((σ.toAlgHom.restrictScalars 𝒪ᵍᵥ).comp χ) a * ψ b -
        χ a * ψ b =
        xb • (algebraMap (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) ℚᵍᵥᵃˡᵍ
          (σ • xa - xa)) := by
      rw [hval, Algebra.smul_def]
      show σ (χ a) * ψ b - χ a * ψ b = ψ b * (σ (χ a) - χ a)
      ring
    rw [hkey]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hin)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The inertia displacement of a point is connected** (PROVEN —
the étale half of the connected–étale dichotomy, generic in the
place; the proof is the displacement block of the PROVEN ModThree and
Family assemblies, extracted): if `δ ⋆ φ = σ • φ` for a local inertia
element `σ` — i.e. `δ` is the displacement `(σ∘φ) ⋆ φ⁻¹` — then `δ`
takes the value `1` on any counit-one idempotent `e₀`: its value on
`e₀` is an idempotent of the field `ℚᵥᵃˡᵍ` (hence `0` or `1`)
congruent to the value `1` of `φ ⋆ φ⁻¹ = 1` modulo the maximal ideal
of the integral closure (`lift_sub_lift_mem_of_localInertiaGroup` —
inertia moves integral values only within `𝔪`), and `0 ≡ 1 mod 𝔪` is
impossible. Conceptually: the étale quotient of the model has
unramified points, so inertia displacements die in it and land in the
connected component. -/
theorem displacement_point_apply_idempotent_eq_one
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵍᵥ G] [Module.Finite 𝒪ᵍᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵍᵥ) e₀ = (1 : 𝒪ᵍᵥ))
    (σ : Field.absoluteGaloisGroup ℚᵍᵥ)
    (hσ : σ ∈ localInertiaGroup v)
    (φ δ : ℚᵍᵥ ⊗[𝒪ᵍᵥ] G →ₐ[ℚᵍᵥ] ℚᵍᵥᵃˡᵍ)
    (hδ : δ * φ = σ • φ) :
    δ ((1 : ℚᵍᵥ) ⊗ₜ[𝒪ᵍᵥ] e₀) = 1 := by
  classical
  set χm : G →ₐ[𝒪ᵍᵥ] ℚᵍᵥᵃˡᵍ :=
    (AlgHom.liftEquiv 𝒪ᵍᵥ ℚᵍᵥ G ℚᵍᵥᵃˡᵍ).symm φ with hχm
  set δd : G →ₐ[𝒪ᵍᵥ] ℚᵍᵥᵃˡᵍ :=
    (AlgHom.liftEquiv 𝒪ᵍᵥ ℚᵍᵥ G ℚᵍᵥᵃˡᵍ).symm δ with hδd
  have hvale : δd e₀ = δ ((1 : ℚᵍᵥ) ⊗ₜ[𝒪ᵍᵥ] e₀) := by
    rw [hδd, AlgHom.liftEquiv_symm_apply]
  rw [← hvale]
  -- transport `δ ⋆ φ = σ∘φ` to the `𝒪ᵥ`-points
  have h3 := congrArg (AlgHom.liftEquiv 𝒪ᵍᵥ ℚᵍᵥ G ℚᵍᵥᵃˡᵍ).symm hδ
  rw [vendored_mul_eq_convMul, liftEquiv_symm_convMul] at h3
  rw [show σ • φ =
      (σ.toAlgHom : ℚᵍᵥᵃˡᵍ →ₐ[ℚᵍᵥ] ℚᵍᵥᵃˡᵍ).comp φ from
    AlgHom.ext fun _ => rfl, liftEquiv_symm_comp] at h3
  rw [← hχm, ← hδd] at h3
  have h4 : toConv δd * toConv χm =
      toConv ((σ.toAlgHom.restrictScalars 𝒪ᵍᵥ).comp χm) := by
    have h4a := congrArg WithConv.toConv h3
    rwa [WithConv.toConv_ofConv] at h4a
  -- cancel `χ` on the right through the antipode inverse
  have h5 : toConv δd =
      toConv ((σ.toAlgHom.restrictScalars 𝒪ᵍᵥ).comp χm) *
        toConv (χm.comp (HopfAlgebra.antipodeAlgHom 𝒪ᵍᵥ G)) := by
    rw [← h4, mul_assoc, toConv_mul_comp_antipodeAlgHom, mul_one]
  have h6 : δd e₀ =
      Algebra.TensorProduct.lift ((σ.toAlgHom.restrictScalars 𝒪ᵍᵥ).comp χm)
        (χm.comp (HopfAlgebra.antipodeAlgHom 𝒪ᵍᵥ G))
        (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := 𝒪ᵍᵥ) e₀) := by
    have h7 := congrArg WithConv.ofConv h5
    rw [WithConv.ofConv_toConv] at h7
    rw [h7]
    exact AlgHom.convMul_apply _ _ e₀
  -- the corresponding value of `χ ⋆ χ⁻¹ = 1` is `ε(e₀) = 1`
  have h8 : Algebra.TensorProduct.lift χm
      (χm.comp (HopfAlgebra.antipodeAlgHom 𝒪ᵍᵥ G))
      (fun _ _ => Commute.all _ _) (Coalgebra.comul (R := 𝒪ᵍᵥ) e₀) = 1 := by
    have h9 := AlgHom.convMul_apply (toConv χm)
      (toConv (χm.comp (HopfAlgebra.antipodeAlgHom 𝒪ᵍᵥ G))) e₀
    rw [toConv_mul_comp_antipodeAlgHom] at h9
    rw [← h9]
    show algebraMap 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵍᵥ) e₀) = 1
    rw [hε₀, map_one]
  -- the inertia congruence: `δ(e₀) ≡ 1` modulo the maximal ideal
  have h10 := lift_sub_lift_mem_of_localInertiaGroup v G σ hσ χm
    (χm.comp (HopfAlgebra.antipodeAlgHom 𝒪ᵍᵥ G))
    (Coalgebra.comul (R := 𝒪ᵍᵥ) e₀)
  rw [h8, ← h6] at h10
  -- the value is an idempotent of a field, hence `0` or `1`; the
  -- congruence rules out `0`
  have h11 : δd e₀ * δd e₀ = δd e₀ := by
    rw [← map_mul, he₀.eq]
  have h12 : δd e₀ * (δd e₀ - 1) = 0 := by
    rw [mul_sub, h11, mul_one, sub_self]
  rcases mul_eq_zero.mp h12 with h13 | h13
  · exfalso
    rw [h13, zero_sub] at h10
    have h14 : (1 : ℚᵍᵥᵃˡᵍ) ∈
        Submodule.map (Algebra.linearMap (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) ℚᵍᵥᵃˡᵍ)
          (IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ)) := by
      have h15 := Submodule.neg_mem _ h10
      rwa [neg_neg] at h15
    obtain ⟨m', hm', hm1⟩ := h14
    have hm2 : m' = 1 := by
      apply Subtype.ext
      exact hm1
    rw [hm2] at hm'
    exact (IsLocalRing.maximalIdeal.isMaximal
      (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ)).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hm' isUnit_one)
  · exact sub_eq_zero.mp h13

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **A point of the connected component reduces to the counit**
(PROVEN — the algebraic form of "a connected finite group scheme has
only the identity point over the residue field"): for a geometric
point `φ` of the generic fibre of a module-finite Hopf order `G`
taking the value `1` on a PRIMITIVE counit-one idempotent `e₀`, the
value `φ (1 ⊗ g)` is congruent to `ε g` modulo the maximal ideal of
the integral closure of `𝒪ᵥ` in `ℚᵥᵃˡᵍ`, for EVERY `g ∈ G`.

Proof: primitivity `hprim₀` upgrades to the minimality hypothesis of
`exists_pow_mem_of_counit_mem_maximalIdeal` (an idempotent `y` below
`e₀` with `y · e₀ = 0` is `y = 0`, whose counit is `0 ≠ 1` in the
domain `𝒪ᵥ`). Apply that corner-nilpotency lemma to the corner
element `x = g · e₀ − ε(g) · e₀`, whose counit is
`ε g · 1 − ε g · 1 = 0 ∈ 𝔪`: some power `x^N` lies in `𝔪_{𝒪ᵥ} G`.
The values of `φ` are integral over `𝒪ᵥ` (`G` is module-finite), so
the associated `𝒪ᵥ`-point corestricts to `χ : G →ₐ[𝒪ᵥ] 𝒪̄`, and `χ`
carries `𝔪_{𝒪ᵥ} G` into `𝔪_{𝒪ᵥ} 𝒪̄ ⊆ 𝔪_{𝒪̄}` because the integral
extension `𝒪ᵥ → 𝒪̄` is a LOCAL homomorphism
(`Algebra.IsIntegral.isLocalHom`). Hence `χ(x)^N ∈ 𝔪_{𝒪̄}`, which is
a prime ideal, so `χ(x) ∈ 𝔪_{𝒪̄}`; and `χ x = φ (1 ⊗ g) − ε g` since
`χ e₀ = φ (1 ⊗ e₀) = 1`. -/
theorem point_sub_counit_mem_maximalIdeal
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵍᵥ G] [Module.Finite 𝒪ᵍᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵍᵥ) e₀ = (1 : 𝒪ᵍᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (φ : ℚᵍᵥ ⊗[𝒪ᵍᵥ] G →ₐ[ℚᵍᵥ] ℚᵍᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵍᵥ) ⊗ₜ[𝒪ᵍᵥ] e₀) = 1)
    (g : G) :
    φ ((1 : ℚᵍᵥ) ⊗ₜ[𝒪ᵍᵥ] g) -
        algebraMap 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵍᵥ) g) ∈
      Submodule.map (Algebra.linearMap (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) ℚᵍᵥᵃˡᵍ)
        (IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ)) := by
  classical
  haveI : Algebra.IsIntegral 𝒪ᵍᵥ G := Algebra.IsIntegral.of_finite 𝒪ᵍᵥ G
  set χ : G →ₐ[𝒪ᵍᵥ] ℚᵍᵥᵃˡᵍ :=
    (AlgHom.liftEquiv 𝒪ᵍᵥ ℚᵍᵥ G ℚᵍᵥᵃˡᵍ).symm φ with hχ
  have hint : ∀ a : G, χ a ∈ integralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ := fun a =>
    (Algebra.IsIntegral.isIntegral (R := 𝒪ᵍᵥ) a).map χ
  set χI : G →ₐ[𝒪ᵍᵥ] IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ :=
    AlgHom.codRestrict χ (integralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) hint with hχI
  have hval : ∀ a : G,
      algebraMap (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) ℚᵍᵥᵃˡᵍ (χI a) = χ a := fun _ => rfl
  -- minimality of `e₀` follows from its primitivity
  have hmin : ∀ y : G, IsIdempotentElem y → y * e₀ = y →
      Coalgebra.counit (R := 𝒪ᵍᵥ) y = (1 : 𝒪ᵍᵥ) → y = e₀ := by
    intro y hy hye hεy
    rcases hprim₀ y hy with h | h
    · rw [hye] at h
      rw [h, map_zero] at hεy
      exact absurd hεy zero_ne_one
    · rw [← hye, h]
  -- the corner element measuring the defect of `φ` from the counit
  set x : G := g * e₀ - Coalgebra.counit (R := 𝒪ᵍᵥ) g • e₀ with hx
  have hxe : x * e₀ = x := by
    rw [hx, sub_mul, mul_assoc, he₀.eq, smul_mul_assoc, he₀.eq]
  have hεx : Coalgebra.counit (R := 𝒪ᵍᵥ) x ∈ IsLocalRing.maximalIdeal 𝒪ᵍᵥ := by
    have hzero : Coalgebra.counit (R := 𝒪ᵍᵥ) x = 0 := by
      rw [hx, map_sub, Bialgebra.counit_mul, map_smul, hε₀, mul_one, smul_eq_mul,
        mul_one, sub_self]
    rw [hzero]
    exact Submodule.zero_mem _
  obtain ⟨N, hN⟩ :=
    exists_pow_mem_of_counit_mem_maximalIdeal he₀ hε₀ hmin hxe hεx
  -- the point carries `𝔪_{𝒪ᵥ} G` into the maximal ideal of `𝒪̄`
  have hmap : Ideal.map (χI : G →+* IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ)
      ((IsLocalRing.maximalIdeal 𝒪ᵍᵥ).map (algebraMap 𝒪ᵍᵥ G)) ≤
      IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) := by
    rw [Ideal.map_map]
    have hcomp : (χI : G →+* IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ).comp
        (algebraMap 𝒪ᵍᵥ G) =
        algebraMap 𝒪ᵍᵥ (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) := by
      ext r
      exact χI.commutes r
    rw [hcomp, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
    exact fun hu => ha (IsLocalHom.map_nonunit a hu)
  have hpow : χI x ^ N ∈
      IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) := by
    rw [← map_pow]
    exact hmap (Ideal.mem_map_of_mem _ hN)
  have hmem : χI x ∈
      IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) :=
    (IsLocalRing.maximalIdeal.isMaximal
      (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ)).isPrime.mem_of_pow_mem N hpow
  refine ⟨χI x, hmem, ?_⟩
  have hχe₀ : χ e₀ = 1 := by rw [hχ, AlgHom.liftEquiv_symm_apply]; exact hφe
  have hχg : χ g = φ ((1 : ℚᵍᵥ) ⊗ₜ[𝒪ᵍᵥ] g) := by
    rw [hχ, AlgHom.liftEquiv_symm_apply]
  show algebraMap (IntegralClosure 𝒪ᵍᵥ ℚᵍᵥᵃˡᵍ) ℚᵍᵥᵃˡᵍ (χI x) = _
  rw [hval, hx, map_sub, map_mul, map_smul, hχe₀, mul_one, Algebra.smul_def,
    mul_one, hχg]

end GenericPlace

/-! ### Exponent arithmetic for the `μ`-type node

Three elementary monoid facts consumed by the Oort–Tate node below:
an element killed by `q` only sees its exponent mod `q`, a `q`-th
root of unity `≠ 1` with `q` prime is primitive, and a primitive
`q`-th root of unity separates exponents mod `q`. Together they turn
the identity `σ ζ = ζ^m = ζ^n` at a `μ_p`-coordinate into the
congruence `m ≡ n mod p` and back into `φ^m = φ^n`. -/

/-- **Powers of an element killed by `q` depend only on the exponent
mod `q`** (PROVEN): `x ^ q = 1` and `a ≡ b [MOD q]` give
`x ^ a = x ^ b`. -/
theorem pow_eq_pow_of_natModEq {M : Type*} [Monoid M] {x : M} {q : ℕ}
    (hx : x ^ q = 1) {a b : ℕ} (hab : a ≡ b [MOD q]) :
    x ^ a = x ^ b := by
  have hmod : ∀ c : ℕ, x ^ c = x ^ (c % q) := by
    intro c
    conv_lhs => rw [← Nat.div_add_mod c q]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
  rw [hmod a, hmod b]
  exact congrArg (fun e : ℕ => x ^ e) hab

/-- **A nontrivial `q`-th root of unity is primitive for `q` prime**
(PROVEN): the order divides the prime `q` and is not `1`. -/
theorem isPrimitiveRoot_of_prime_pow_eq_one {M : Type*} [CommMonoid M]
    {q : ℕ} (hq : q.Prime) {x : M} (hx : x ^ q = 1) (hx1 : x ≠ 1) :
    IsPrimitiveRoot x q := by
  rcases hq.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hx) with
    h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h ▸ IsPrimitiveRoot.orderOf x

/-- **A primitive `q`-th root of unity separates exponents mod `q`**
(PROVEN): reduce both exponents mod `q` and apply
`IsPrimitiveRoot.pow_inj`. -/
theorem natModEq_of_pow_eq_pow {M : Type*} [CommMonoid M] {q : ℕ}
    [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q) {a b : ℕ}
    (hab : ζ ^ a = ζ ^ b) : a ≡ b [MOD q] := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have ha : ζ ^ (a % q) = ζ ^ a :=
    pow_eq_pow_of_natModEq hζ.pow_eq_one (Nat.mod_modEq a q)
  have hb : ζ ^ (b % q) = ζ ^ b :=
    pow_eq_pow_of_natModEq hζ.pow_eq_one (Nat.mod_modEq b q)
  exact hζ.pow_inj (Nat.mod_lt _ hq) (Nat.mod_lt _ hq)
    (by rw [ha, hb, hab])

/-! ### The convolution filtration of the kernel of reduction

The engine of the RAMIFICATION half of the Oort–Tate node
(`eq_one_of_inertia_invariant_of_reduction_counit` below): "the kernel
of `G(𝒪^nr) → G(𝔽̄_p)` has no `p`-torsion when `e < p − 1`", in a form
that needs neither formal groups nor the Oort–Tate classification.

The point is that mathlib's `LinearMap.convRing` — the CONVOLUTION RING
on `G →ₗ[R] A` for a coalgebra `G` and an algebra `A` — makes the
`p`-torsion condition a BINOMIAL identity. Write `c` for the point and
`d = c − 1` for its displacement from the counit; `c^p = 1` expands as

  `0 = ∑_{i=1}^{p} C(p,i) d^i`,

and if `𝔞` denotes the ideal of `A` generated by the values of `d`, then
`d^i` takes values in `𝔞^i` (`convPow_apply_mem_pow`, an induction over
`convMul_apply_mem_mul`: a convolution product is a sum of products of
one value of each factor). The binomial coefficients `C(p,i)` with
`1 ≤ i < p` are divisible by `p`, so every term with `2 ≤ i < p` lies in
`(p)·𝔞²`; and the top term `d^p` lies in `𝔞^p = 𝔞²·𝔞^{p−2} ⊆ (p)·𝔞²`
PROVIDED `𝔞 ⊆ (p)` and `p − 2 ≥ 1`. Hence `p·d(x) ∈ (p)·𝔞²`, and `p`
cancels in the domain `A`: `𝔞 ⊆ 𝔞²`. Nakayama (`𝔞` finitely generated
because `G` is module-finite, `𝔞` inside the maximal ideal of the local
ring `A`) gives `𝔞 = 0`, i.e. `c = 1`.

`p` ODD is spent exactly at `p − 2 ≥ 1`: at `p = 2` the top term `d^2`
carries no factor of `p` and the argument — like the theorem — fails.
The hypothesis `𝔞 ⊆ (p)` is exactly ABSOLUTE UNRAMIFIEDNESS of the base
(`e = 1`), supplied downstream by
`mem_span_natCast_of_inertia_invariant`; over a ramified base `𝔞` is
only inside the maximal ideal and the argument correctly breaks (`μ_p`
over `ℤ_p[ζ_p]` has `p`-torsion in the kernel of reduction). -/

section ConvFiltration

variable {R G A : Type*} [CommRing R] [AddCommMonoid G] [Module R G] [Coalgebra R G]
  [CommRing A] [Algebra R A]

omit [Coalgebra R G] in
/-- **A tensor whose two legs are read into ideals multiplies into the
product ideal** (PROVEN, by tensor induction): the pure tensors go to
`f a · g b ∈ 𝔟 · 𝔠`. The tensor-level content of
`convMul_apply_mem_mul`. -/
theorem mul'_map_mem_mul (f g : G →ₗ[R] A) {𝔟 𝔠 : Ideal A}
    (hf : ∀ x, f x ∈ 𝔟) (hg : ∀ x, g x ∈ 𝔠) (t : G ⊗[R] G) :
    LinearMap.mul' R A (TensorProduct.map f g t) ∈ 𝔟 * 𝔠 := by
  induction t with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  | tmul a b =>
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    exact Ideal.mul_mem_mul (hf a) (hg b)

/-- **A convolution product takes values in the product of the value
ideals** (PROVEN): `(f ⋆ g)(x) = ∑ f(x₍₁₎) g(x₍₂₎)` is a sum of
products of one value of each factor, so it lies in `𝔟 · 𝔠`. -/
theorem convMul_apply_mem_mul (f g : WithConv (G →ₗ[R] A)) {𝔟 𝔠 : Ideal A}
    (hf : ∀ x, f.ofConv x ∈ 𝔟) (hg : ∀ x, g.ofConv x ∈ 𝔠) (x : G) :
    (f * g).ofConv x ∈ 𝔟 * 𝔠 := by
  rw [LinearMap.convMul_apply]
  exact mul'_map_mem_mul _ _ hf hg _

/-- **The convolution filtration** (PROVEN, induction over
`convMul_apply_mem_mul`): a linear map with values in an ideal `𝔞` has
`n`-th convolution power with values in `𝔞^n`. At `n = 0` the
convolution unit is unconstrained and `𝔞^0 = ⊤` absorbs it. -/
theorem convPow_apply_mem_pow (f : WithConv (G →ₗ[R] A)) {𝔞 : Ideal A}
    (hf : ∀ x, f.ofConv x ∈ 𝔞) : ∀ (n : ℕ) (x : G), (f ^ n).ofConv x ∈ 𝔞 ^ n := by
  intro n
  induction n with
  | zero => intro x; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih => intro x; rw [pow_succ, pow_succ]; exact convMul_apply_mem_mul _ _ ih hf x

omit [Coalgebra R G] in
/-- **The value ideal of a linear map out of a module-finite module is
finitely generated** (PROVEN): the images of a finite generating set of
`G` generate it, because the map is `R`-linear and an ideal of `A` is
in particular an `R`-submodule. This is the Nakayama input. -/
theorem fg_span_range (f : G →ₗ[R] A) [Module.Finite R G] :
    (Ideal.span (Set.range f)).FG := by
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule R G).FG)
  refine ⟨S.image f, ?_⟩
  have key : ∀ g : G, f g ∈ Ideal.span (f '' (S : Set G)) := by
    intro g
    have hg : g ∈ Submodule.span R (S : Set G) := hS ▸ Submodule.mem_top
    induction hg using Submodule.span_induction with
    | mem y hy => exact Ideal.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [map_smul, Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hy
  refine le_antisymm ?_ ?_
  · rw [Finset.coe_image]
    exact Ideal.span_mono (Set.image_subset_range _ _)
  · rw [Finset.coe_image, Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    exact key g

/-- **The first-order expansion of a convolution power** (PROVEN,
induction on `m`): if the displacement `c − 1` of a point of the
convolution ring takes its values in an ideal `𝔞`, then

  `c^m = 1 + m·(c − 1) + r`   with `r` valued in `𝔞²`.

No binomial coefficients are needed: the induction step multiplies
`1 + m·e + r` by `e + 1` (`e = c − 1`) and collects `m·e² + r·e + r`
into the new remainder, each summand landing in `𝔞²` by
`convMul_apply_mem_mul`.

This is the `m`-th-power companion of `convPow_apply_mem_pow`: where
that lemma reads `c^p = 1` as a filtration statement, this one reads
`σ·c = c^m` as the statement that `σ` multiplies the displacement by
`m` MODULO `𝔞²` — i.e. that the inertia character is the "tame
character" of any generator of `𝔞`. It is the whole elementary content
of Raynaud's dichotomy below. -/
theorem exists_convPow_rem (c : WithConv (G →ₗ[R] A)) {𝔞 : Ideal A}
    (hd : ∀ x, (c - 1).ofConv x ∈ 𝔞) (m : ℕ) :
    ∃ r : WithConv (G →ₗ[R] A), (∀ x, r.ofConv x ∈ 𝔞 ^ 2) ∧
      c ^ m = 1 + (m : ℕ) • (c - 1) + r := by
  induction m with
  | zero =>
    refine ⟨0, fun x => by simp, ?_⟩
    simp
  | succ m ih =>
    obtain ⟨r, hr, hcm⟩ := ih
    refine ⟨(m : ℕ) • ((c - 1) * (c - 1)) + r * (c - 1) + r, ?_, ?_⟩
    · intro x
      have h1 : ((m : ℕ) • ((c - 1) * (c - 1))).ofConv x ∈ 𝔞 ^ 2 := by
        rw [WithConv.ofConv_smul, LinearMap.smul_apply, nsmul_eq_mul, sq]
        exact Ideal.mul_mem_left _ _ (convMul_apply_mem_mul _ _ hd hd x)
      have h2 : (r * (c - 1)).ofConv x ∈ 𝔞 ^ 2 := by
        have := convMul_apply_mem_mul r (c - 1) hr hd x
        exact (Ideal.mul_le_right : 𝔞 ^ 2 * 𝔞 ≤ 𝔞 ^ 2) this
      rw [WithConv.ofConv_add, WithConv.ofConv_add, LinearMap.add_apply, LinearMap.add_apply]
      exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) (hr x)
    · have hce : (c - 1) + 1 = c := by abel
      calc c ^ (m + 1) = c ^ m * c := pow_succ c m
        _ = (1 + (m : ℕ) • (c - 1) + r) * ((c - 1) + 1) := by rw [hcm, hce]
        _ = 1 + ((m : ℕ) • (c - 1) + (c - 1)) +
              ((m : ℕ) • ((c - 1) * (c - 1)) + r * (c - 1) + r) := by
              rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_one, mul_one, mul_one,
                one_mul, smul_mul_assoc]
              abel
        _ = 1 + ((m + 1 : ℕ)) • (c - 1) +
              ((m : ℕ) • ((c - 1) * (c - 1)) + r * (c - 1) + r) := by
              rw [succ_nsmul]

/-- **Raynaud's exponent bound `k ≤ e`, in elementary convolution
form** (PROVEN 2026-07-25): let `A` be a local domain, `p` a prime, and
`c` a point of the convolution ring `G →ₗ[R] A` with `c^p = 1` whose
displacement `c − 1` takes its values in the maximal ideal (reduction
to the counit). If the value ideal of `c − 1` is PRINCIPAL, generated by
`t ≠ 0`, then `p ∈ (t)^{p−1}`.

Read valuation-theoretically over the integral closure `𝒪̄`, this says
`(p − 1)·v(t) ≤ v(p) = e`: the exponent `k = (p − 1)·v(t)` of Raynaud's
tame character is at most the absolute ramification index. Over
`𝒪ᵥ = ℤ_p` (`e = 1`) it reads `v(t) ≤ 1/(p − 1) = v(ζ_p − 1)`, which is
one of the two inclusions of the Oort–Tate leaf below — and, unlike the
other one, it is elementary.

Proof: the binomial identity `0 = ∑_{i=1}^{p} C(p,i)·(c − 1)^i` (from
`c^p = 1`) puts every value of `p·(c − 1)` into `(p)·𝔞² ⊔ 𝔞^p`, where
`𝔞 = (t)` is the value ideal — the middle binomial coefficients are
divisible by `p` and the values of `(c−1)^i` lie in `𝔞^i`
(`convPow_apply_mem_pow`), while the top term contributes `𝔞^p`. Hence
`p·t = α·p·t² + β·t^p`; cancel one `t` in the DOMAIN `A` to get
`p·(1 − α t) = β·t^{p−1}`, and `1 − α t` is a UNIT because `t` lies in
the maximal ideal of the LOCAL ring `A`. So `p = β(1 − αt)^{-1}t^{p−1}`.

`eq_convOne_of_convPow_prime_eq_one` below is the degenerate case: its
extra hypothesis `𝔞 ⊆ (p)` forces `v(t) ≥ 1 > 1/(p − 1)`, contradicting
this bound unless `𝔞 = 0`. Note that `p` ODD is NOT needed here — it is
spent there, in absorbing the top term into `(p)·𝔞²`. -/
theorem natCast_mem_span_pow_of_convPow_prime_eq_one
    [Module.Finite R G] [IsDomain A] [IsLocalRing A]
    {p : ℕ} (hp : p.Prime)
    (c : WithConv (G →ₗ[R] A)) (hcp : c ^ p = 1)
    (hmax : ∀ x, (c - 1).ofConv x ∈ IsLocalRing.maximalIdeal A)
    (t : A) (ht0 : t ≠ 0)
    (ht : Ideal.span (Set.range (c - 1).ofConv) = Ideal.span {t}) :
    (p : A) ∈ Ideal.span {t} ^ (p - 1) := by
  classical
  have hpsub : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.pos
  set d : WithConv (G →ₗ[R] A) := c - 1 with hd_def
  set 𝔞 : Ideal A := Ideal.span (Set.range d.ofConv) with h𝔞_def
  have hd : ∀ x, d.ofConv x ∈ 𝔞 := fun x => Ideal.subset_span ⟨x, rfl⟩
  have ht𝔞 : t ∈ 𝔞 := by rw [ht]; exact Ideal.mem_span_singleton_self t
  have h𝔞max : 𝔞 ≤ IsLocalRing.maximalIdeal A := by
    rw [h𝔞_def, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    exact hmax x
  -- the binomial expansion of `c ^ p = (d + 1) ^ p`
  have hbin : ∑ m ∈ Finset.range (p + 1), (p.choose m) • d ^ m = 1 := by
    have hcd : d + 1 = c := by rw [hd_def]; abel
    have h := (Commute.one_right d).add_pow p
    rw [hcd, hcp] at h
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) h.symm
    rw [one_pow, mul_one, nsmul_eq_mul]
    exact (Nat.cast_commute _ _).eq
  have hrest : (p : ℕ) • d +
      ∑ i ∈ Finset.Ico 1 p, (p.choose (i + 1)) • d ^ (i + 1) = 0 := by
    rw [Finset.sum_range_succ' (fun m => (p.choose m) • d ^ m) p] at hbin
    simp only [Nat.choose_zero_right, pow_zero, one_smul] at hbin
    have h0 : ∑ i ∈ Finset.range p, (p.choose (i + 1)) • d ^ (i + 1) = 0 :=
      add_right_cancel (b := (1 : WithConv (G →ₗ[R] A))) (hbin.trans (zero_add _).symm)
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.pos] at h0
    simpa using h0
  -- every remaining term lands in `(p)·𝔞² ⊔ 𝔞^p`
  set K : Ideal A := Ideal.span {(p : A)} * 𝔞 ^ 2 ⊔ 𝔞 ^ p with hK_def
  have hterm : ∀ i ∈ Finset.Ico 1 p, ∀ x : G,
      ((p.choose (i + 1)) • d ^ (i + 1)).ofConv x ∈ K := by
    intro i hi x
    rw [Finset.mem_Ico] at hi
    have hz : (d ^ (i + 1)).ofConv x ∈ 𝔞 ^ (i + 1) := convPow_apply_mem_pow d hd _ x
    rw [WithConv.ofConv_smul, LinearMap.smul_apply]
    rcases eq_or_lt_of_le (show i + 1 ≤ p by omega) with heq | hlt
    · refine le_sup_right (a := Ideal.span {(p : A)} * 𝔞 ^ 2) ?_
      rw [heq, Nat.choose_self, one_smul]
      exact heq ▸ hz
    · obtain ⟨k, hk⟩ : p ∣ p.choose (i + 1) := hp.dvd_choose_self (by omega) hlt
      refine le_sup_left (b := 𝔞 ^ p) ?_
      have hz2 : (d ^ (i + 1)).ofConv x ∈ 𝔞 ^ 2 :=
        Ideal.pow_le_pow_right (by omega) hz
      rw [hk, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
        (Ideal.mul_mem_left _ _ hz2)
  have hpd : ∀ x : G, (p : A) * d.ofConv x ∈ K := by
    intro x
    have h0 : (p : ℕ) • d.ofConv x +
        ∑ i ∈ Finset.Ico 1 p, (p.choose (i + 1)) • (d ^ (i + 1)).ofConv x = 0 := by
      have h1 := congrArg (fun f : WithConv (G →ₗ[R] A) => f.ofConv x) hrest
      simp only [WithConv.ofConv_add, WithConv.ofConv_sum, WithConv.ofConv_smul,
        WithConv.ofConv_zero, LinearMap.add_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, LinearMap.zero_apply] at h1
      exact h1
    have hsm : ∑ i ∈ Finset.Ico 1 p, (p.choose (i + 1)) • (d ^ (i + 1)).ofConv x ∈ K :=
      Submodule.sum_mem _ fun i hi => by
        simpa only [WithConv.ofConv_smul, LinearMap.smul_apply] using hterm i hi x
    have hmemK : (p : ℕ) • d.ofConv x ∈ K := by
      rw [eq_neg_of_add_eq_zero_left h0]
      exact Submodule.neg_mem _ hsm
    rwa [nsmul_eq_mul] at hmemK
  have hpa : ∀ a ∈ 𝔞, (p : A) * a ∈ K := by
    intro a ha
    rw [h𝔞_def] at ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨x, rfl⟩ := hy; exact hpd x
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact K.add_mem hu hv
    | smul r u _ hu =>
      rw [smul_eq_mul, show (p : A) * (r * u) = r * ((p : A) * u) by ring]
      exact Ideal.mul_mem_left _ _ hu
  have hpt : (p : A) * t ∈ K := hpa t ht𝔞
  rw [hK_def, ht, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton] at hpt
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hpt
  obtain ⟨α, hα⟩ := Ideal.mem_span_singleton'.mp hy
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.mp hz
  have h0 : α * ((p : A) * t ^ 2) + β * t ^ p = (p : A) * t := by rw [hα, hβ]; exact hyz
  have hpow : t ^ p = t * t ^ (p - 1) := by
    conv_lhs => rw [← hpsub]
    rw [pow_succ, mul_comm]
  have heq : t * (p : A) = t * ((p : A) * (α * t) + β * t ^ (p - 1)) := by
    linear_combination (-1 : A) * h0 + β * hpow
  have hcan := mul_left_cancel₀ ht0 heq
  have hstep : (p : A) * (1 - α * t) = β * t ^ (p - 1) := by linear_combination hcan
  have ht𝔪 : t ∈ IsLocalRing.maximalIdeal A := h𝔞max ht𝔞
  have hunit : IsUnit (1 - α * t) := by
    by_contra hcon
    have h1 : (1 - α * t) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hcon
    have h2 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have h3 := Submodule.add_mem _ h1 (Ideal.mul_mem_left _ α ht𝔪)
      have h4 : (1 - α * t) + α * t = (1 : A) := by ring
      rwa [h4] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((Ideal.eq_top_iff_one _).mpr h2)
  obtain ⟨u, hu⟩ := hunit
  rw [Ideal.span_singleton_pow]
  refine Ideal.mem_span_singleton'.mpr ⟨β * (↑u⁻¹ : A), ?_⟩
  have hpu : (p : A) * (u : A) = β * t ^ (p - 1) := by rw [hu]; exact hstep
  calc β * (↑u⁻¹ : A) * t ^ (p - 1) = β * t ^ (p - 1) * (↑u⁻¹ : A) := by ring
    _ = ((p : A) * (u : A)) * (↑u⁻¹ : A) := by rw [hpu]
    _ = (p : A) := by rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

/-- **No `p`-torsion in the kernel of reduction over an absolutely
unramified base** (PROVEN — the elementary convolution-filtration form;
Raynaud, Bull. SMF 102 (1974), 3.3.2–3.3.5; Fontaine, *Il n'y a pas de
variété abélienne sur `ℤ`*, §1; Tate, "Finite flat group schemes", in
Cornell–Silverman–Stevens, §4): let `A` be a local domain, `p` an ODD
prime nonzero in `A`, and `c` a point of the convolution ring of
`G →ₗ[R] A` (`G` a module-finite `R`-coalgebra) with

* `c^p = 1` — killed by `p`;
* `c − 1` valued in `(p)` — the ABSOLUTE UNRAMIFIEDNESS input, `e = 1`;
* `c − 1` valued in the maximal ideal — reduction to the counit.

Then `c = 1`. See the section docstring for the argument; `p` odd is
spent at `𝔞^p ⊆ (p)·𝔞²`, which needs `p − 2 ≥ 1`. -/
theorem eq_convOne_of_convPow_prime_eq_one [Module.Finite R G] [IsDomain A] [IsLocalRing A]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hp0 : (p : A) ≠ 0)
    (c : WithConv (G →ₗ[R] A)) (hcp : c ^ p = 1)
    (hmem : ∀ x, (c - 1).ofConv x ∈ Ideal.span {(p : A)})
    (hmax : ∀ x, (c - 1).ofConv x ∈ IsLocalRing.maximalIdeal A) :
    c = 1 := by
  classical
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hodd
    have := hp.two_le
    omega
  have hsub : p - 2 + 2 = p := Nat.sub_add_cancel (Nat.le_of_succ_le hp3)
  have hne2 : p - 2 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.lt_of_lt_of_le (by norm_num) hp3)
  set d : WithConv (G →ₗ[R] A) := c - 1 with hd_def
  set 𝔞 : Ideal A := Ideal.span (Set.range d.ofConv) with h𝔞_def
  have hd : ∀ x, d.ofConv x ∈ 𝔞 := fun x => Ideal.subset_span ⟨x, rfl⟩
  have h𝔞p : 𝔞 ≤ Ideal.span {(p : A)} := by
    rw [h𝔞_def, Ideal.span_le]; rintro _ ⟨x, rfl⟩; exact hmem x
  -- the binomial expansion of `c ^ p = (d + 1) ^ p`
  have hbin : ∑ m ∈ Finset.range (p + 1), (p.choose m) • d ^ m = 1 := by
    have hcd : d + 1 = c := by rw [hd_def]; abel
    have h := (Commute.one_right d).add_pow p
    rw [hcd, hcp] at h
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) h.symm
    rw [one_pow, mul_one, nsmul_eq_mul]
    exact (Nat.cast_commute _ _).eq
  -- peel off the constant term `1` and the linear term `p · d`
  have hrest : (p : ℕ) • d +
      ∑ i ∈ Finset.Ico 1 p, (p.choose (i + 1)) • d ^ (i + 1) = 0 := by
    rw [Finset.sum_range_succ' (fun m => (p.choose m) • d ^ m) p] at hbin
    simp only [Nat.choose_zero_right, pow_zero, one_smul] at hbin
    have h0 : ∑ i ∈ Finset.range p, (p.choose (i + 1)) • d ^ (i + 1) = 0 :=
      add_right_cancel (b := (1 : WithConv (G →ₗ[R] A))) (hbin.trans (zero_add _).symm)
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.pos] at h0
    simpa using h0
  -- every remaining term takes values in `(p) · 𝔞²`
  set K : Ideal A := Ideal.span {(p : A)} * 𝔞 ^ 2 with hK_def
  have hpowle : 𝔞 ^ p ≤ K := by
    have h1 : 𝔞 ^ p = 𝔞 ^ (p - 2) * 𝔞 ^ 2 := by rw [← pow_add, hsub]
    rw [h1, hK_def]
    exact Ideal.mul_mono (le_trans (Ideal.pow_le_self hne2) h𝔞p) le_rfl
  have hterm : ∀ i ∈ Finset.Ico 1 p, ∀ x : G,
      ((p.choose (i + 1)) • d ^ (i + 1)).ofConv x ∈ K := by
    intro i hi x
    rw [Finset.mem_Ico] at hi
    have hz : (d ^ (i + 1)).ofConv x ∈ 𝔞 ^ (i + 1) := convPow_apply_mem_pow d hd _ x
    rw [WithConv.ofConv_smul, LinearMap.smul_apply]
    rcases eq_or_lt_of_le (show i + 1 ≤ p by omega) with heq | hlt
    · -- the top term `d ^ p`, absorbed through `𝔞 ^ p ≤ (p) · 𝔞²`
      rw [heq, Nat.choose_self, one_smul]
      exact hpowle (heq ▸ hz)
    · -- `1 < i + 1 < p`: the binomial coefficient is divisible by `p`
      obtain ⟨k, hk⟩ : p ∣ p.choose (i + 1) := hp.dvd_choose_self (by omega) hlt
      have hz2 : (d ^ (i + 1)).ofConv x ∈ 𝔞 ^ 2 :=
        Ideal.pow_le_pow_right (by omega) hz
      rw [hk, nsmul_eq_mul, Nat.cast_mul, mul_assoc, hK_def]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
        (Ideal.mul_mem_left _ _ hz2)
  -- hence `p · d x ∈ (p) · 𝔞²`, and `p` cancels in the domain
  have hsq : ∀ x : G, d.ofConv x ∈ 𝔞 ^ 2 := by
    intro x
    have h0 : (p : ℕ) • d.ofConv x +
        ∑ i ∈ Finset.Ico 1 p, (p.choose (i + 1)) • (d ^ (i + 1)).ofConv x = 0 := by
      have h1 := congrArg (fun f : WithConv (G →ₗ[R] A) => f.ofConv x) hrest
      simp only [WithConv.ofConv_add, WithConv.ofConv_sum, WithConv.ofConv_smul,
        WithConv.ofConv_zero, LinearMap.add_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, LinearMap.zero_apply] at h1
      exact h1
    have hmemK : (p : ℕ) • d.ofConv x ∈ K := by
      have hsm : ∑ i ∈ Finset.Ico 1 p, (p.choose (i + 1)) • (d ^ (i + 1)).ofConv x ∈ K :=
        Submodule.sum_mem _ fun i hi => by
          simpa only [WithConv.ofConv_smul, LinearMap.smul_apply] using hterm i hi x
      rw [eq_neg_of_add_eq_zero_left h0]
      exact Submodule.neg_mem _ hsm
    rw [nsmul_eq_mul, hK_def] at hmemK
    obtain ⟨z, hz, hzeq⟩ := Submodule.mem_span_singleton_mul.mp hmemK
    exact (mul_left_cancel₀ hp0 hzeq) ▸ hz
  -- Nakayama
  have hle : 𝔞 ≤ 𝔞 • 𝔞 := by
    rw [Ideal.smul_eq_mul, ← sq, h𝔞_def, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    exact hsq x
  have hjac : 𝔞 ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, h𝔞_def, Ideal.span_le]
    rintro _ ⟨x, rfl⟩
    exact hmax x
  have hbot : 𝔞 = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔞 𝔞 (fg_span_range _) hle hjac
  have hzero : d = 0 := by
    apply WithConv.ofConv_injective
    ext x
    have := hd x
    rw [hbot, Ideal.mem_bot] at this
    simpa using this
  rw [hd_def] at hzero
  exact sub_eq_zero.mp hzero

end ConvFiltration

section ConvTransport

universe uv

variable {R H : Type*} [CommRing R] [CommRing H] [Bialgebra R H]
  {S L : Type uv} [Field S] [Field L] [Algebra R S] [Algebra S L] [Algebra R L]
  [IsScalarTower R S L]

/-- **Convolution powers of a geometric point, transported to the
integral points** (PROVEN): the tensor–hom adjunction
`AlgHom.liftEquiv` carries the `k`-th power of `φ` in the vendored
convolution monoid on the generic-fibre points to the `k`-th power of
the restricted point `g ↦ φ (1 ⊗ g)` in the `WithConv` convolution
monoid on the `R`-points — induction on `k` over
`vendored_one_eq_convOne`/`vendored_mul_eq_convMul` and
`liftEquiv_symm_convOne`/`liftEquiv_symm_convMul`.

(This lemma was part of the `tensorIdeal`/`ConvPow`/`VendoredClosure`
block deleted on 2026-07-25 as free-floating. It is RESTORED here
because the ramification leaf below genuinely consumes it: it is how
`φ^p = 1` on the generic fibre becomes `χ^p = 1` on the `𝒪ᵥ`-points,
where the integral structure lives. Nothing else of that block is
needed.) -/
theorem liftEquiv_symm_vendored_pow (φ : S ⊗[R] H →ₐ[S] L) (k : ℕ) :
    (AlgHom.liftEquiv R S H L).symm (φ ^ k) =
      ((toConv ((AlgHom.liftEquiv R S H L).symm φ)) ^ k).ofConv := by
  induction k with
  | zero => rw [pow_zero, pow_zero, vendored_one_eq_convOne, liftEquiv_symm_convOne]
  | succ k ih =>
    rw [pow_succ, vendored_mul_eq_convMul, liftEquiv_symm_convMul,
      WithConv.ofConv_toConv, WithConv.ofConv_toConv, ih, pow_succ,
      WithConv.toConv_ofConv]

end ConvTransport

section ConvComp

variable {R C A B : Type*} [CommSemiring R] [CommSemiring C] [Bialgebra R C]
  [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

/-- **Postcomposition preserves the convolution unit** (PROVEN): both
sides are `(Algebra.ofId R ·) ∘ ε`, and an algebra map commutes with
the structure map. -/
theorem comp_convOne (h : A →ₐ[R] B) :
    h.comp ((1 : WithConv (C →ₐ[R] A)).ofConv) = (1 : WithConv (C →ₐ[R] B)).ofConv := by
  rw [AlgHom.convOne_def, AlgHom.convOne_def, WithConv.ofConv_toConv,
    WithConv.ofConv_toConv, ← AlgHom.comp_assoc]
  congr 1
  refine AlgHom.ext fun r => ?_
  simp [Algebra.ofId_apply]

/-- **Postcomposition is a monoid map for convolution** (PROVEN,
induction over `AlgHom.comp_convMul_distrib`). Used with an INJECTIVE
`h` to descend a convolution identity from the geometric points to the
integral points. -/
theorem comp_convPow (h : A →ₐ[R] B) (f : WithConv (C →ₐ[R] A)) (n : ℕ) :
    h.comp ((f ^ n).ofConv) = ((toConv (h.comp f.ofConv)) ^ n).ofConv := by
  induction n with
  | zero => rw [pow_zero, pow_zero, comp_convOne]
  | succ n ih =>
    rw [pow_succ, AlgHom.comp_convMul_distrib, WithConv.ofConv_toConv, ih,
      WithConv.toConv_ofConv, ← pow_succ]

end ConvComp

section CyclotomicNode

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪ᵖᵍᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))
local notation "ℚᵖᵍᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))
local notation "ℚᵖᵍᵥᵃˡᵍ" => AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)))

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The root-of-unity bridge** (PROVEN 2026-07-24): the `p`-adic
cyclotomic character computes the action of the LOCAL absolute Galois
group of `ℚᵥ` on the `p`-th roots of unity of `ℚᵥᵃˡᵍ` — for every
`σ ∈ G_{ℚᵥ}`, every `ζ ∈ ℚᵥᵃˡᵍ` with `ζ^p = 1` and every natural `n`
congruent to `χ_cyc(σ̃) mod p`, one has `σ ζ = ζ^n`.

Proof (the local analogue of the PROVEN endgame of
`cyclotomicCharacter_eq_one_of_mem_inertia_two` in `Family.lean`,
REPROVED here so that this neutral file imports no consumer): fix a
primitive `p`-th root of unity `μ` of the ABSTRACT closure `ℚᵃˡᵍ`
(`HasEnoughRootsOfUnity`); its image under the structure map
`ℚᵃˡᵍ → ℚᵥᵃˡᵍ` is primitive as well (injectivity of a field map), so
the given `ζ` is one of its powers `μ^i` — the `p`-th roots of unity
of `ℚᵥᵃˡᵍ` all descend. `Field.absoluteGaloisGroup.lift_map`
transports `σ` to the descended element `σ̃`, on which
`cyclotomicCharacter.spec` at level `1` evaluates the action as the
`(χ_cyc(σ̃) mod p)`-th power; `PadicInt.ker_toZModPow` turns the
hypothesis `χ_cyc(σ̃) − n ∈ (p)` into the congruence of exponents, and
`pow_eq_pow_of_natModEq` replaces the exponent by `n`. -/
theorem galois_apply_pow_eq_pow_of_cyclotomicCharacter
    (σ : Field.absoluteGaloisGroup ℚᵖᵍᵥ)
    (n : ℕ)
    (hn : ((cyclotomicCharacter (AlgebraicClosure ℚ) p
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
          σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]) - (n : ℤ_[p]) ∈
      Ideal.span {((p : ℕ) : ℤ_[p])})
    (ζ : ℚᵖᵍᵥᵃˡᵍ) (hζ : ζ ^ p = 1) :
    σ ζ = ζ ^ n := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- every `p`-th root of unity of `ℚᵥᵃˡᵍ` descends to `ℚᵃˡᵍ`
  obtain ⟨μ, hμ⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hFinj : Function.Injective
      (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ)) :=
    (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ)).injective
  have hFμ : IsPrimitiveRoot
      (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ) p :=
    hμ.map_of_injective hFinj
  obtain ⟨i, -, hi⟩ := hFμ.eq_pow_of_pow_eq_one hζ
  have hzp : (μ ^ i) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]
  have hFz : AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) (μ ^ i) = ζ := by
    rw [map_pow]
    exact hi
  -- the cyclotomic character evaluates the descended action
  have hspec := cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) p
    (n := 1) ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
      σ).toRingEquiv) (μ ^ i) (by rwa [pow_one])
  -- the hypothesis is exactly the mod-`p` value of the character
  have hcast : PadicInt.toZModPow 1
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
          σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]) =
      ((n : ℕ) : ZMod (p ^ 1)) := by
    have hmem : (((cyclotomicCharacter (AlgebraicClosure ℚ) p
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
          σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]) - (n : ℤ_[p])) ∈
        RingHom.ker (PadicInt.toZModPow 1 : ℤ_[p] →+* ZMod (p ^ 1)) := by
      rw [PadicInt.ker_toZModPow, pow_one]
      exact hn
    have h0 := RingHom.mem_ker.mp hmem
    rw [map_sub, sub_eq_zero, map_natCast] at h0
    exact h0
  have hmod : (PadicInt.toZModPow 1
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
          σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p])).val ≡ n [MOD p] := by
    have h1 : (((PadicInt.toZModPow 1
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p
          ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
            σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p])).val : ℕ) :
        ZMod (p ^ 1)) = ((n : ℕ) : ZMod (p ^ 1)) := by
      rw [ZMod.natCast_val, ZMod.cast_id, hcast]
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
    exact Nat.ModEq.of_dvd (dvd_pow_self p one_ne_zero) h2
  have hspec' : (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ) σ)
      (μ ^ i) = (μ ^ i) ^ n := by
    rw [show (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ) σ)
        (μ ^ i) =
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
          σ).toRingEquiv) (μ ^ i) from rfl, hspec]
    exact pow_eq_pow_of_natModEq hzp hmod
  calc σ ζ
      = AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ)
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ) σ)
          (μ ^ i)) := by
        rw [Field.absoluteGaloisGroup.lift_map, hFz]
    _ = AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) ((μ ^ i) ^ n) := by
        rw [hspec']
    _ = ζ ^ n := by rw [map_pow, hFz]

/-- **Every `p`-adic integer has a natural-number residue mod `p`**
(PROVEN): the residue `(u mod p).val` works, `PadicInt.ker_toZModPow`
identifying the kernel of the level-`1` reduction with `(p)`. Supplies
the exponent `n` at which `galois_apply_pow_eq_pow_of_cyclotomicCharacter`
reads the cyclotomic character. -/
theorem exists_natCast_sub_mem_span (u : ℤ_[p]) :
    ∃ n : ℕ, u - (n : ℤ_[p]) ∈ Ideal.span {((p : ℕ) : ℤ_[p])} := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine ⟨(PadicInt.toZModPow 1 u).val, ?_⟩
  have hk : u - (((PadicInt.toZModPow 1 u).val : ℕ) : ℤ_[p]) ∈
      RingHom.ker (PadicInt.toZModPow 1 : ℤ_[p] →+* ZMod (p ^ 1)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero, ZMod.natCast_val,
      ZMod.cast_id]
  rw [PadicInt.ker_toZModPow, pow_one] at hk
  exact hk

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The prime of `𝓞 ℚ` attached to the prime number `p` is `(p)`**
(PROVEN): unfolding `Nat.Prime.toHeightOneSpectrumRingOfIntegersRat`,
the ideal is the comap of `span {(p : ℤ)}` along
`Rat.ringOfIntegersEquiv`, and a ring isomorphism carries spans of
singletons to spans of singletons while preserving `Nat.cast`.

(A local re-derivation: the identical `asIdeal_toHeightOneSpectrumRingOfIntegersRat`
lives in `FreyCurve/MazurTorsion.lean`, which is FAR downstream of this
neutral group-scheme file and cannot be imported here. The natural home
for both this and `maximalIdeal_eq_span_natCast` below is the shim
module `Fermat/FLT/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`,
where `toHeightOneSpectrumRingOfIntegersRat` itself is defined; hoisting
them there is a bookkeeping change that touches another owner's file and
is deliberately NOT done here.) -/
theorem asIdeal_toHeightOneSpectrum_eq_span :
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)).asIdeal =
      Ideal.span {((p : ℕ) : NumberField.RingOfIntegers ℚ)} := by
  have h1 : (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)).asIdeal =
      Ideal.comap (Rat.ringOfIntegersEquiv.symm.symm) (Ideal.span {((p : ℕ) : ℤ)}) := rfl
  rw [h1, RingEquiv.symm_symm, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton,
    map_natCast]

open IsDedekindDomain.HeightOneSpectrum in
set_option maxHeartbeats 1000000 in
/-- **`p` is a uniformizer of `𝒪ᵥ = ℤ_p`** (PROVEN — the ABSOLUTE
UNRAMIFIEDNESS of the base, `e = 1`): the maximal ideal of the
`v`-adic integer ring at the place `v = v_p` of `ℚ` is the span of `p`.
Through `adicCompletion.maximalIdeal_eq_span_uniformizer` it suffices
that `v(p) = ofAdd (−1)` in `ℚᵥ`, which reduces along
`valuedAdicCompletion_eq_valuation` and `valuation_of_algebraMap` to
the `intValuation` of `p` in `𝓞 ℚ`, computed by
`intValuation_singleton` from `v_p = span {p}`
(`asIdeal_toHeightOneSpectrum_eq_span`).

(Local re-derivation of `maximalIdeal_adicCompletionIntegers_eq_span`
of `FreyCurve/MazurTorsion.lean`; see the note there.) -/
theorem maximalIdeal_eq_span_natCast :
    IsLocalRing.maximalIdeal 𝒪ᵖᵍᵥ = Ideal.span {((p : ℕ) : 𝒪ᵖᵍᵥ)} := by
  have hq0 : ((p : ℕ) : NumberField.RingOfIntegers ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hval : (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
      (Fact.out : p.Prime)).intValuation
      ((p : ℕ) : NumberField.RingOfIntegers ℚ) = Multiplicative.ofAdd (-1 : ℤ) :=
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
      (Fact.out : p.Prime)).intValuation_singleton hq0
      asIdeal_toHeightOneSpectrum_eq_span
  apply adicCompletion.maximalIdeal_eq_span_uniformizer
  have h := (valuedAdicCompletion_eq_valuation
      (v := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) (K := ℚ)
      ((p : ℕ) : NumberField.RingOfIntegers ℚ)).trans
    ((valuation_of_algebraMap
      (v := Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) (K := ℚ)
      ((p : ℕ) : NumberField.RingOfIntegers ℚ)).trans hval)
  convert h using 2
  norm_cast

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **`𝒪ᵥ = ℤ_p` is ABSOLUTELY UNRAMIFIED: an inertia-invariant element
of the maximal ideal is divisible by `p`** (PROVEN 2026-07-25 — the
whole ramification input of the Oort–Tate node).

Content: an element `x` of the integral closure `𝒪̄` of `𝒪ᵥ` in `ℚᵥᵃˡᵍ`
which is fixed by every element of `localInertiaGroup v` lies in the
maximal unramified extension `𝒪^nr`; since `𝒪ᵥ = ℤ_p` is absolutely
unramified, `𝒪^nr` has value group `ℤ` with `v(p) = 1`, so `x ∈ 𝔪`
forces `v(x) ≥ 1` and `x/p ∈ 𝒪^nr ⊆ 𝒪̄`. Over a RAMIFIED base the
statement is FALSE — for `𝒪ᵥ = ℤ_p[ζ_p]` the element `ζ_p − 1` is
inertia-invariant, lies in `𝔪`, and is not divisible by `p` — so this
is exactly where `e = 1 < p − 1` enters the node. Note `p` ODD is NOT
used here; it is spent in the binomial step of
`eq_convOne_of_convPow_prime_eq_one`.

Proof, at finite level rather than through the (non-discrete) valuation
on `𝒪̄`: let `M := ℚᵥ⟮x⟯`, finite-dimensional because `ℚᵥᵃˡᵍ/ℚᵥ` is
algebraic. `hinv` says the single generator of `M` is fixed by local
inertia, so `M ≤ IntermediateField.fixedField (localInertiaGroup v)` by
`IntermediateField.adjoin_le_iff`; hence `e(M/ℚᵥ) = 1` by the PROVEN
node `maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup` of
`Deformations/RepresentationTheory/LocalInertiaFixedField.lean`, i.e.
`𝔪 𝒪ᵥ` generates `𝔪 𝒪_M`, i.e. — by `maximalIdeal_eq_span_natCast` —
`𝔪 𝒪_M = (p)`. The element `x` lifts to `y ∈ 𝒪_M` (integrality
transfers along the injective `M ↪ ℚᵥᵃˡᵍ`), and `y` is a NONUNIT
because its image `x` is one (`hx` and locality of `𝒪̄`), so `y ∈ 𝔪 𝒪_M`
by locality of `𝒪_M`. Thus `y = z · p`, and pushing forward along
`integralClosureInclusion` — which preserves `Nat.cast` — gives
`x = (image of z) · p`. -/
theorem mem_span_natCast_of_inertia_invariant
    (x : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)
    (hx : x ∈ IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ))
    (hinv : ∀ σ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)),
      σ (algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ x) =
        algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ x) :
    x ∈ Ideal.span {((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)} := by
  classical
  set xv : ℚᵖᵍᵥᵃˡᵍ := algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ x with hxv
  -- the finite subextension generated by `x`
  have hxalg : IsIntegral ℚᵖᵍᵥ xv := Algebra.IsIntegral.isIntegral xv
  set M : IntermediateField ℚᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ := IntermediateField.adjoin ℚᵖᵍᵥ {xv} with hM
  haveI : FiniteDimensional ℚᵖᵍᵥ M := IntermediateField.adjoin.finiteDimensional hxalg
  have hxM : xv ∈ M := by
    rw [hM]; exact IntermediateField.subset_adjoin _ _ rfl
  -- it is fixed pointwise by the local inertia group
  have hMfix : M ≤ IntermediateField.fixedField
      (localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))) := by
    rw [hM]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact hinv σ hσ
  -- so `e(M/ℚᵥ) = 1`, i.e. `p` generates the maximal ideal of `𝒪_M`
  have hmap := maximalIdeal_map_eq_of_le_fixedField_localInertiaGroup
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) M hMfix
  rw [maximalIdeal_eq_span_natCast, Ideal.map_span, Set.image_singleton,
    map_natCast] at hmap
  -- `x`, viewed at the finite level
  have hxint : IsIntegral 𝒪ᵖᵍᵥ (⟨xv, hxM⟩ : M) := by
    have hinj : Function.Injective
        (IsScalarTower.toAlgHom 𝒪ᵖᵍᵥ (M : Type _) ℚᵖᵍᵥᵃˡᵍ) := by
      intro a b hab
      exact Subtype.ext hab
    rw [← isIntegral_algHom_iff _ hinj]
    exact x.2
  set y : IntegralClosure 𝒪ᵖᵍᵥ M := ⟨⟨xv, hxM⟩, hxint⟩ with hy
  have hincl : integralClosureInclusion
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) M y = x :=
    Subtype.ext rfl
  -- `y` is a nonunit, because its image is
  have hyM : y ∈ IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ M) := by
    by_contra hcon
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hcon
    have hu : IsUnit (integralClosureInclusion
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) M y) :=
      hcon.map _
    rw [hincl] at hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    exact hx hu
  rw [← hmap] at hyM
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hyM
  refine Ideal.mem_span_singleton'.mpr ⟨integralClosureInclusion
    (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)) M z, ?_⟩
  rw [← hincl, ← hz, map_mul, map_natCast]

/-- **`(1 + π)^n − 1 = π · (n + π·w)`** (PROVEN, induction on `n`): in
any commutative ring the binomial tail beyond the linear term is
divisible by `π²`. Applied with `π = ζ_p − 1` it says that a Galois
element acting on `ζ_p` by `ζ_p ↦ ζ_p^n` multiplies `ζ_p − 1` by `n`
modulo `(ζ_p − 1)²` — the "tame character" reading of the mod-`p`
cyclotomic character, and the second half of the comparison performed
by `inertia_character_trivial_or_cyclotomic` below. -/
theorem exists_one_add_pow_sub_one {A : Type*} [CommRing A] (π : A) (n : ℕ) :
    ∃ w : A, (1 + π) ^ n - 1 = π * ((n : A) + π * w) := by
  induction n with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨w + (n : A) + π * w, ?_⟩
    have h : (1 + π) ^ (n + 1) - 1 = (1 + π) * ((1 + π) ^ n - 1) + π := by ring
    rw [h, hw]
    push_cast
    ring

/-- **`p ∣ (1 − ζ_p)^{p−1}` in any domain carrying a primitive `p`-th
root of unity** (PROVEN): `p = Φ_p(1) = ∏_{μ primitive}(1 − μ)`
(`Polynomial.eval_one_cyclotomic_prime` together with
`cyclotomic_eq_prod_X_sub_primitiveRoots`), and every primitive `μ` has
`ζ` among its powers, so `1 − μ ∣ 1 − ζ`; the product of the
`p − 1 = φ(p)` factors therefore divides `(1 − ζ)^{p−1}`.

Valuation-theoretically this is `v(p) ≤ (p − 1)·v(ζ_p − 1)` — the half
of `v(ζ_p − 1) = 1/(p − 1)` that gets compared against Raynaud's
exponent bound `natCast_mem_span_pow_of_convPow_prime_eq_one`. (Only
this direction is needed; the reverse, `(1 − ζ)^{p−1} ∣ p`, is the easy
one and is not used.) -/
theorem natCast_dvd_one_sub_pow_of_isPrimitiveRoot {A : Type*} [CommRing A] [IsDomain A]
    {q : ℕ} [hq : Fact q.Prime] {ζ : A} (hζ : IsPrimitiveRoot ζ q) :
    (q : A) ∣ (1 - ζ) ^ (q - 1) := by
  classical
  have hprod : ((q : ℕ) : A) = ∏ μ ∈ primitiveRoots q A, (1 - μ) := by
    have h1 : (Polynomial.cyclotomic q A).eval 1 = (q : A) :=
      Polynomial.eval_one_cyclotomic_prime
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
    exact h1.symm
  have hdvd : ∀ μ ∈ primitiveRoots q A, (1 - μ) ∣ (1 - ζ) := by
    intro μ hμ
    have hμp : IsPrimitiveRoot μ q := (mem_primitiveRoots hq.out.pos).mp hμ
    obtain ⟨i, -, hi⟩ := hμp.eq_pow_of_pow_eq_one hζ.pow_eq_one
    have h := sub_dvd_pow_sub_pow (1 : A) μ i
    rw [one_pow, hi] at h
    exact h
  have hcard : (primitiveRoots q A).card = q - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hq.out]
  rw [hprod, ← hcard, ← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd _ _ hdvd

/-- **`p` is a NONUNIT of the integral closure `𝒪̄` of `𝒪ᵥ` in
`ℚᵥᵃˡᵍ`** (PROVEN): `𝒪̄` is integral over `𝒪ᵥ`, so the contraction of
its maximal ideal along `𝒪ᵥ → 𝒪̄` is a maximal ideal of the LOCAL ring
`𝒪ᵥ`, hence `𝔪 𝒪ᵥ = (p)` (`maximalIdeal_eq_span_natCast`); so `p` is in
`𝔪 𝒪̄` and `span {p} ≠ ⊤` in `𝒪̄`. This is what makes the descent of a
congruence from `𝒪̄` back to `ℤ` sound: a rational integer lying in
`p·𝒪̄` really is divisible by `p`, because otherwise its coprimality
with `p` would put `1` in `span {p} ⊆ 𝔪 𝒪̄`. -/
theorem natCast_mem_maximalIdeal_integralClosure :
    ((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ∈
      maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
  have hmax : ((maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)).comap
      (algebraMap 𝒪ᵖᵍᵥ (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  have heq : (maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)).comap
      (algebraMap 𝒪ᵖᵍᵥ (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)) = maximalIdeal 𝒪ᵖᵍᵥ :=
    IsLocalRing.eq_maximalIdeal hmax
  have hp' : ((p : ℕ) : 𝒪ᵖᵍᵥ) ∈ maximalIdeal 𝒪ᵖᵍᵥ := by
    rw [maximalIdeal_eq_span_natCast]
    exact Ideal.mem_span_singleton_self _
  have h := heq ▸ hp'
  rwa [Ideal.mem_comap, map_natCast] at h

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **THE ONE-DIMENSIONALITY INPUT of the Oort–Tate node** (SORRY LEAF,
cut 2026-07-25 and cut again the same day; it is the SOLE remaining
input of `inertia_character_trivial_or_cyclotomic` below, which is
PROVEN over it): for a CONNECTED geometric point `φ ≠ 1` of exact
convolution order `p` whose cyclic group `⟨φ⟩` is inertia-stable, the
ideal of `𝒪̄` generated by the values of the DISPLACEMENT
`g ↦ φ(1 ⊗ g) − ε(g)` is CONTAINED in `(ζ_p − 1)`, for a primitive
`p`-th root of unity `ζ_p`.

Valuation-theoretically: `v(t) ≥ 1/(p − 1) = v(ζ_p − 1)` for a
generator `t` of the value ideal. The REVERSE inclusion — Raynaud's
exponent bound `k ≤ e`, i.e. `v(t) ≤ 1/(p − 1)` — is elementary and is
PROVEN below as `span_zeta_sub_one_le_displacement_span`; the two
together give the equality `displacement_span_eq_span_zeta_sub_one`
that the dichotomy consumes. So what is left open here is exactly the
half that Raynaud's bound does NOT supply.

Why this half is the deep one. Connectedness alone gives only
`v(t) > 0`; upgrading that to `v(t) ≥ 1/(p − 1)` is the statement that
the tame character through which inertia acts is `𝔽_p`-valued, i.e.
that `(p − 1)·v(t)` is an INTEGER — Oort–Tate's normal form, or
equivalently the ONE-DIMENSIONALITY that `hstab` encodes. It fails
without `hstab`: see the supersingular counterexample below, where
`v(t) = 1/(p² − 1) < 1/(p − 1)` because tame inertia acts through the
level-`2` fundamental characters. Mathlib has no tame/wild inertia, no
ramification filtration and no fundamental characters, so this is not
reachable by the classical route from what is currently available.

Content (Oort–Tate, *Group schemes of prime order*, Ann. Sci. ÉNS 1970,
§2; Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974), 3.3.6/3.4.3; Tate, *Finite flat group schemes*, in
Cornell–Silverman–Stevens, §4). `hstab` makes the schematic closure `C`
of `⟨φ⟩` a finite flat closed subGROUP scheme of `Spec G` of order `p`
killed by `p`; its vanishing ideal is a Hopf ideal, so BOTH `φ` and `ε`
factor through `G ↠ 𝒪(C)` and the displacement's value ideal computed
on `G` is the one computed on `C`. Oort–Tate write
`C = Spec 𝒪ᵥ[x]/(x^p − a x)` with `ab = w_p`, `v(w_p) = e = 1` and
`ε x = 0`; the geometric points are `x ↦ α` with `α^{p−1} = a`, so the
displacement values are the powers `α^i` (`i ≥ 1`) and the value ideal
is `(α)`, of valuation `v(a)/(p − 1)`. Connectedness (`hφe`, `hprim₀`)
excludes `v(a) = 0` — the étale form `ℤ/p`, whose points have UNIT
displacement — and `v(a) + v(b) = 1` then forces `v(a) = 1`, i.e.
`v(α) = 1/(p − 1) = v(ζ_p − 1)`. In the VALUATION RING `𝒪̄` equal
valuation means associate, which is the asserted equality of ideals.

Soundness. The hypothesis set is inhabited: for
`G = 𝒪ᵥ[T]/(T^p − 1)` (the Hopf order of `μ_p`, LOCAL because its
reduction is `𝔽_p[T]/(T − 1)^p`, so `e₀ = 1` and
`he₀`/`hε₀`/`hprim₀`/`hcomul₀`/`hφe` all hold) and `φ : T ↦ ζ_p`, the
values are `ζ_p^i − 1 = (ζ_p − 1)·unit` and the ideal IS `(ζ_p − 1)`;
the same holds for every unramified twist `μ_p ⊗ ψ`, since a twist
changes the coordinate by a unit of `𝒪^nr`. Every hypothesis is
load-bearing:

* `hφ1` — for `φ = 1` the displacement vanishes and the ideal is `0`;
* the connectedness package — for the ÉTALE `ℤ/p` (`G = 𝒪ᵥ^p` with `φ`
  a coordinate projection) some displacement value is a UNIT and the
  ideal is `⊤`; that is the other branch of Raynaud's dichotomy, and it
  is excluded here exactly as `not_inertia_character_trivial_of_connected`
  excludes the trivial character;
* `hstab` — for the `p`-torsion of a SUPERSINGULAR elliptic curve over
  `ℤ_p` the model is connected and killed by `p`, but tame inertia acts
  through the level-`2` fundamental characters, no line is stable, and
  the displacement ideal has valuation `1/(p² − 1)`, not `1/(p − 1)`.

Finally, note that this asks for a VALUE (an ideal of `𝒪̄` generated by
values of `φ`), never for an `𝒪ᵥ`-rational coordinate: demanding the
coordinate is precisely what made the deleted `exists_muType_closure`
FALSE (see the CORRECTION NOTE at `exists_muType_coordinate`), because
the Oort–Tate coordinate is only defined up to an unramified twist.
The value ideal is twist-blind, so this form is faithful. -/
theorem displacement_span_le_span_zeta_sub_one
    (hpodd : Odd p)
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵍᵥ G] [Module.Flat 𝒪ᵖᵍᵥ G] [Module.Finite 𝒪ᵖᵍᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵍᵥ) e₀ = (1 : 𝒪ᵖᵍᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵍᵥ) e₀ *
      (e₀ ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = e₀ ⊗ₜ[𝒪ᵖᵍᵥ] e₀)
    (φ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = 1)
    (hord : φ ^ p = 1)
    (hstab : ∀ τ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      ∃ m : ℕ, τ • φ = φ ^ m)
    (hφ1 : φ ≠ 1)
    (ζ : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)
    (hζ : IsPrimitiveRoot
      (algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ ζ) p) :
    Ideal.span {x : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ | ∃ g : G,
        algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ x =
          φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
            algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g)} ≤
      Ideal.span {ζ - 1} :=
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Raynaud's exponent bound `k ≤ e` for the displacement ideal**
(PROVEN 2026-07-25): the reverse inclusion of the leaf above —
`(ζ_p − 1)` is CONTAINED in the ideal generated by the displacement
values of a connected geometric point `φ ≠ 1` killed by `p`.
Valuation-theoretically `v(t) ≤ 1/(p − 1)` for a generator `t`.

Neither `hstab` nor `hcomul₀` nor `p` odd is needed: this half is
elementary, and it holds for EVERY connected point killed by `p`,
one-dimensional or not (for supersingular `E[p]` it reads
`1/(p² − 1) ≤ 1/(p − 1)`).

Proof. Transport `φ` to the point `c` of the convolution ring
`G →ₗ[𝒪ᵥ] 𝒪̄` as in `eq_one_of_inertia_invariant_of_reduction_counit`,
so `c^p = 1`; connectedness (`point_sub_counit_mem_maximalIdeal`) puts
the displacement values in `𝔪 𝒪̄`. The value ideal is finitely
generated (`fg_span_range`) and `𝒪̄` is a VALUATION ring, hence Bézout,
so the ideal is principal, `= (t)`; and `t ≠ 0` because `t = 0` would
make `c` the convolution unit and hence `φ = 1`. Now

* `natCast_mem_span_pow_of_convPow_prime_eq_one` gives `p ∈ (t)^{p−1}`,
  i.e. `t^{p−1} ∣ p`;
* `natCast_dvd_one_sub_pow_of_isPrimitiveRoot` gives
  `p ∣ (1 − ζ_p)^{p−1}`;

so `t^{p−1} ∣ (1 − ζ_p)^{p−1}`, and in a valuation ring that forces
`t ∣ 1 − ζ_p`: divisibility is total, and in the other case
`1 − ζ_p = t·e⁻¹` follows after cancelling `(1 − ζ_p)^{p−1}` in the
domain `𝒪̄` and finding `e` a unit. -/
theorem span_zeta_sub_one_le_displacement_span
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵍᵥ G] [Module.Flat 𝒪ᵖᵍᵥ G] [Module.Finite 𝒪ᵖᵍᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵍᵥ) e₀ = (1 : 𝒪ᵖᵍᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (φ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = 1)
    (hord : φ ^ p = 1)
    (hφ1 : φ ≠ 1)
    (ζ : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)
    (hζ : IsPrimitiveRoot
      (algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ ζ) p) :
    Ideal.span {ζ - 1} ≤
      Ideal.span {x : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ | ∃ g : G,
        algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ x =
          φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
            algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g)} := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : Algebra.IsIntegral 𝒪ᵖᵍᵥ G := Algebra.IsIntegral.of_finite 𝒪ᵖᵍᵥ G
  set χ : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ :=
    (AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm φ with hχdef
  have hint : ∀ a : G, χ a ∈ integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ := fun a =>
    (Algebra.IsIntegral.isIntegral (R := 𝒪ᵖᵍᵥ) a).map χ
  set χI : G →ₐ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ :=
    AlgHom.codRestrict χ (integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) hint with hχIdef
  set ι : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ :=
    { algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ with
      commutes' := fun _ => rfl } with hιdef
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext h
  have hιχ : ι.comp χI = χ := AlgHom.ext fun _ => rfl
  set c : WithConv (G →ₗ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) :=
    toConv χI.toLinearMap with hcdef
  have hdval : ∀ g : G, ι ((c - 1).ofConv g) =
      φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
        algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g) := by
    intro g
    rw [WithConv.ofConv_sub, LinearMap.sub_apply, map_sub]
    congr 1
  have hset : Set.range (c - 1).ofConv =
      {x : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ | ∃ g : G,
        algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ x =
          φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
            algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g)} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, hdval g⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, hιinj ((hdval g).trans hg.symm)⟩
  rw [← hset]
  -- connectedness: every displacement value is in the maximal ideal
  have hmax : ∀ g : G, (c - 1).ofConv g ∈
      maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
    intro g
    obtain ⟨y, hy, hyeq⟩ := point_sub_counit_mem_maximalIdeal
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))
      G e₀ he₀ hε₀ hprim₀ φ hφe g
    have hgm : ι ((c - 1).ofConv g) = ι y := by rw [hdval g, ← hyeq]; rfl
    rwa [hιinj hgm]
  -- `φ ^ p = 1` transported into the convolution ring over `𝒪̄`
  have hχp : (toConv χ) ^ p = (1 : WithConv (G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)) := by
    apply WithConv.ofConv_injective
    have h := liftEquiv_symm_vendored_pow (R := 𝒪ᵖᵍᵥ) (S := ℚᵖᵍᵥ) (H := G)
      (L := ℚᵖᵍᵥᵃˡᵍ) φ p
    rw [hord, vendored_one_eq_convOne, liftEquiv_symm_convOne] at h
    exact h.symm
  have hχIp : (toConv χI) ^ p =
      (1 : WithConv (G →ₐ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)) := by
    apply WithConv.ofConv_injective
    refine AlgHom.ext fun a => hιinj ?_
    have h := comp_convPow ι (toConv χI) p
    rw [WithConv.ofConv_toConv, hιχ, hχp] at h
    have h2 := congrArg (fun f : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ => f a) h
    simpa [comp_convOne ι] using h2
  have hcp : c ^ p = 1 := by
    have h := AlgHom.toLinearMap_convPow (toConv χI) p
    rw [hχIp, AlgHom.toLinearMap_convOne] at h
    exact h.symm
  -- the value ideal is principal, with a nonzero generator
  obtain ⟨t, ht⟩ := (IsBezout.isPrincipal_of_FG
    (Ideal.span (Set.range (c - 1).ofConv)) (fg_span_range _)).principal
  have ht0 : t ≠ 0 := by
    intro htz
    apply hφ1
    have hbot : Ideal.span (Set.range (c - 1).ofConv) = ⊥ := by
      rw [ht, htz, Ideal.span_singleton_eq_bot]
    have hc1 : c = 1 := by
      have hz : ∀ g : G, (c - 1).ofConv g = 0 := by
        intro g
        have hmem : (c - 1).ofConv g ∈ Ideal.span (Set.range (c - 1).ofConv) :=
          Ideal.subset_span ⟨g, rfl⟩
        rw [hbot] at hmem
        simpa using hmem
      have : c - 1 = 0 := by
        apply WithConv.ofConv_injective
        ext g
        simpa using hz g
      exact sub_eq_zero.mp this
    apply (AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm.injective
    rw [vendored_one_eq_convOne, liftEquiv_symm_convOne]
    refine AlgHom.ext fun a => ?_
    have h : χI a = (1 : WithConv (G →ₗ[𝒪ᵖᵍᵥ]
        IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)).ofConv a := by
      have h0 := congrArg (fun f : WithConv (G →ₗ[𝒪ᵖᵍᵥ]
        IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) => f.ofConv a) hc1
      rw [hcdef] at h0
      exact h0
    calc χ a = ι (χI a) := rfl
      _ = ι (algebraMap 𝒪ᵖᵍᵥ (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)
            (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) a)) := by
          rw [h, LinearMap.convOne_apply]
      _ = algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) a) := ι.commutes _
      _ = (1 : WithConv (G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)).ofConv a := (AlgHom.convOne_apply a).symm
  -- `p ∈ (t)^{p−1}` (Raynaud's bound) and `p ∣ (1 − ζ)^{p−1}` (cyclotomic)
  have hpmem : ((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ∈
      Ideal.span {t} ^ (p - 1) :=
    natCast_mem_span_pow_of_convPow_prime_eq_one hp.out c hcp hmax t ht0 ht
  have hp2 : 2 ≤ p := hp.out.two_le
  have hζI : IsPrimitiveRoot ζ p :=
    hζ.of_map_of_injective (fun a b h => Subtype.ext h)
  have hcyc : ((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ∣ (1 - ζ) ^ (p - 1) :=
    natCast_dvd_one_sub_pow_of_isPrimitiveRoot hζI
  have hne : (1 : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) - ζ ≠ 0 := fun h =>
    hζI.ne_one hp.out.one_lt (sub_eq_zero.mp h).symm
  have hdvdpow : t ^ (p - 1) ∣ (1 - ζ) ^ (p - 1) := by
    refine dvd_trans ?_ hcyc
    rw [Ideal.span_singleton_pow] at hpmem
    exact Ideal.mem_span_singleton.mp hpmem
  -- in a valuation ring, `t^{p−1} ∣ π^{p−1}` forces `t ∣ π`
  have hdvd : t ∣ (1 - ζ) := by
    obtain ⟨e, he⟩ := ValuationRing.cond t (1 - ζ)
    rcases he with h | h
    · exact ⟨e, h.symm⟩
    · obtain ⟨s, hs⟩ := hdvdpow
      have hpow : (1 - ζ) ^ (p - 1) = (1 - ζ) ^ (p - 1) * (e ^ (p - 1) * s) := by
        conv_lhs => rw [hs, ← h, mul_pow]
        ring
      have hone : (1 : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) = e ^ (p - 1) * s :=
        mul_left_cancel₀ (pow_ne_zero _ hne) (by linear_combination hpow)
      have hsplit : e ^ (p - 1) = e * e ^ (p - 2) := by
        conv_lhs => rw [show p - 1 = (p - 2) + 1 by omega]
        rw [pow_succ, mul_comm]
      have heu : IsUnit e :=
        isUnit_of_dvd_one ⟨e ^ (p - 2) * s, by rw [← mul_assoc, ← hsplit]; exact hone⟩
      obtain ⟨u, hu⟩ := heu
      exact ⟨(↑u⁻¹ : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ), by
        rw [← h, ← hu, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]⟩
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ht]
  refine Ideal.mem_span_singleton.mpr ?_
  rw [show ζ - 1 = -((1 : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) - ζ) by ring]
  exact dvd_neg.mpr hdvd

/-- **The displacement ideal of a connected inertia-stable order-`p`
point is `(ζ_p − 1)`** (PROVEN 2026-07-25 over the single leaf
`displacement_span_le_span_zeta_sub_one`, by `le_antisymm` against the
elementary bound `span_zeta_sub_one_le_displacement_span`). This is the
Oort–Tate/Raynaud input of `inertia_character_trivial_or_cyclotomic`;
see the leaf's docstring for the mathematics and for why exactly the
`≤` half remains open. -/
theorem displacement_span_eq_span_zeta_sub_one
    (hpodd : Odd p)
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵍᵥ G] [Module.Flat 𝒪ᵖᵍᵥ G] [Module.Finite 𝒪ᵖᵍᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵍᵥ) e₀ = (1 : 𝒪ᵖᵍᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵍᵥ) e₀ *
      (e₀ ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = e₀ ⊗ₜ[𝒪ᵖᵍᵥ] e₀)
    (φ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = 1)
    (hord : φ ^ p = 1)
    (hstab : ∀ τ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      ∃ m : ℕ, τ • φ = φ ^ m)
    (hφ1 : φ ≠ 1)
    (ζ : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)
    (hζ : IsPrimitiveRoot
      (algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ ζ) p) :
    Ideal.span {x : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ | ∃ g : G,
        algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ x =
          φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
            algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g)} =
      Ideal.span {ζ - 1} :=
  le_antisymm
    (displacement_span_le_span_zeta_sub_one hpodd G e₀ he₀ hε₀ hprim₀ hcomul₀
      φ hφe hord hstab hφ1 ζ hζ)
    (span_zeta_sub_one_le_displacement_span G e₀ he₀ hε₀ hprim₀ φ hφe hord hφ1 ζ hζ)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Raynaud's dichotomy for the inertia character of an order-`p`
point** (PROVEN 2026-07-25 over `displacement_span_eq_span_zeta_sub_one`,
itself proven the same day over the single remaining leaf
`displacement_span_le_span_zeta_sub_one`): for a geometric point `φ` of exact
convolution order `p` whose cyclic group `⟨φ⟩ ≅ ℤ/p` is inertia-stable
(`hstab`), the resulting character
`χ_φ : I_v → (ℤ/p)ˣ`, `σ ↦ m(σ)` with `σ • φ = φ^{m(σ)}`, is EITHER
trivial OR the mod-`p` cyclotomic character — as a CHARACTER, i.e. one
of the two alternatives holds simultaneously for all `σ`, which is
strictly stronger than the pointwise statement `χ_φ(σ) ∈ {1, χ(σ)}`
and is what the consumer needs.

Mathematically (Raynaud, *Schémas en groupes de type `(p, …, p)`*,
Bull. SMF 102 (1974), 3.3.6/3.4.3): over a base with absolute
ramification index `e < p − 1` the action of TAME inertia on the
geometric points of a finite flat group scheme killed by `p` is through
the level-`1` fundamental character raised to exponents in `{0, …, e}`;
here `𝒪ᵥ = ℤ_p` is absolutely unramified, `e = 1`, and `p` is odd, so
only the exponents `0` and `1` survive — the trivial character (the
étale form `ℤ/p`) and `χ_cyc` (the multiplicative form `μ_p`).

**Proof (2026-07-25) — the CONNECTED alternative is proved outright,
so the disjunction is discharged by `Or.inr`.** The whole argument is
a comparison of two "tame characters" inside the integral closure
`𝒪̄` of `𝒪ᵥ` in `ℚᵥᵃˡᵍ`, and the only nonelementary input is the
valuation statement `displacement_span_eq_span_zeta_sub_one`, whose
own open half is `displacement_span_le_span_zeta_sub_one`.

Write `c` for the point read as an element of the convolution ring
`G →ₗ[𝒪ᵥ] 𝒪̄` (the transport is `liftEquiv_symm_vendored_pow` plus
`comp_convPow` along the injection `𝒪̄ ↪ ℚᵥᵃˡᵍ`, exactly as in
`eq_one_of_inertia_invariant_of_reduction_counit`), `d = c − 1` for its
displacement and `𝔞` for the ideal of `𝒪̄` generated by the values of
`d`. Then:

1. CONNECTEDNESS gives `𝔞 ⊆ 𝔪 𝒪̄` — every value of `d` is in the
   maximal ideal, by `point_sub_counit_mem_maximalIdeal`.
2. THE LEAF gives `𝔞 = (ζ_p − 1)` for a primitive `p`-th root of unity
   `ζ_p` (obtained here as the image of a primitive root of the
   abstract closure `ℚᵃˡᵍ`, integral because it is a root of
   `X^p − 1`).
3. Hence some VALUE `t = d(g₀)` is `a₀·(ζ_p − 1)` with `a₀` a UNIT:
   writing every value as `a_g·(ζ_p − 1)`, if every `a_g` were a
   nonunit then `𝔞 ⊆ 𝔪·𝔞`, and Nakayama (`fg_span_range`,
   `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`) would give
   `𝔞 = 0`, contradicting `ζ_p ≠ 1`.
4. `σ • φ = φ^m` becomes `σ ∘ c = c^m`, and `exists_convPow_rem`
   expands `c^m = 1 + m·d + r` with `r` valued in `𝔞²`. Evaluating at
   `g₀` and using that `σ` fixes the image of `𝒪ᵥ`:
   `σ(t) − m·t ∈ 𝔞² = ((ζ_p − 1)²)`.
5. On the other side, `galois_apply_pow_eq_pow_of_cyclotomicCharacter`
   gives `σ(ζ_p) = ζ_p^n` for any `n` representing `χ_cyc(σ)`, and
   `exists_one_add_pow_sub_one` turns this into
   `σ(ζ_p − 1) = (ζ_p − 1)·(n + (ζ_p − 1)·w)`.
6. Substituting `t = a₀·(ζ_p − 1)` into 4 and cancelling the single
   factor `ζ_p − 1` (a nonzero element of the domain `𝒪̄`) leaves
   `σ(a₀)·(n + (ζ_p − 1)w) = m·a₀ + z·(ζ_p − 1)`. Since `σ` is in
   INERTIA it fixes `𝒪̄` modulo `𝔪`, so `σ(a₀) ≡ a₀`, and
   `ζ_p − 1 ∈ 𝔪` by 1–2; hence `a₀·(n − m) ∈ 𝔪`, and `a₀` is a unit,
   so `n − m ∈ 𝔪`.
7. `n − m` is a rational integer, hence inertia-invariant, so
   `mem_span_natCast_of_inertia_invariant` (`e = 1`) puts it in
   `p·𝒪̄`; and `p` is a nonunit of `𝒪̄`
   (`natCast_mem_maximalIdeal_integralClosure`), so an integer coprime
   to `p` could not lie there. Therefore `p ∣ n − m`, i.e.
   `m ≡ n [MOD p]`.

Note where each hypothesis is spent: `hstab` and `hord` and `hφ1` and
the connected-component data are all consumed by the leaf; `hφe`,
`he₀`, `hε₀`, `hprim₀` are additionally used HERE, in step 1, and
`hpodd` only inside the leaf. The `e = 1` unramifiedness of the base is
used twice — in step 7 and (inside the leaf) as Raynaud's bound. -/
theorem inertia_character_trivial_or_cyclotomic
    (hpodd : Odd p)
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵍᵥ G] [Module.Flat 𝒪ᵖᵍᵥ G] [Module.Finite 𝒪ᵖᵍᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵍᵥ) e₀ = (1 : 𝒪ᵖᵍᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵍᵥ) e₀ *
      (e₀ ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = e₀ ⊗ₜ[𝒪ᵖᵍᵥ] e₀)
    (φ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = 1)
    (hord : φ ^ p = 1)
    (hstab : ∀ τ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      ∃ m : ℕ, τ • φ = φ ^ m)
    (hφ1 : φ ≠ 1) :
    (∀ σ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      ∀ m : ℕ, σ • φ = φ ^ m → m ≡ 1 [MOD p]) ∨
    (∀ σ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      ∀ m n : ℕ, σ • φ = φ ^ m →
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
              σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]) - (n : ℤ_[p]) ∈
          Ideal.span {((p : ℕ) : ℤ_[p])} → m ≡ n [MOD p]) := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : Algebra.IsIntegral 𝒪ᵖᵍᵥ G := Algebra.IsIntegral.of_finite 𝒪ᵖᵍᵥ G
  refine Or.inr ?_
  -- the point, as an `𝒪̄`-valued point of the model
  set χ : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ :=
    (AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm φ with hχdef
  have hint : ∀ a : G, χ a ∈ integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ := fun a =>
    (Algebra.IsIntegral.isIntegral (R := 𝒪ᵖᵍᵥ) a).map χ
  set χI : G →ₐ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ :=
    AlgHom.codRestrict χ (integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) hint with hχIdef
  set ι : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ :=
    { algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ with
      commutes' := fun _ => rfl } with hιdef
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext h
  have hιχ : ι.comp χI = χ := AlgHom.ext fun _ => rfl
  set c : WithConv (G →ₗ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) :=
    toConv χI.toLinearMap with hcdef
  set d : WithConv (G →ₗ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := c - 1 with hddef
  set 𝔞 : Ideal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) :=
    Ideal.span (Set.range d.ofConv) with h𝔞def
  have hd𝔞 : ∀ g : G, d.ofConv g ∈ 𝔞 := fun g => Ideal.subset_span ⟨g, rfl⟩
  have hdval : ∀ g : G, ι (d.ofConv g) =
      φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
        algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g) := by
    intro g
    rw [hddef, WithConv.ofConv_sub, LinearMap.sub_apply, map_sub]
    congr 1
  -- STEP 1: connectedness — the point reduces to the counit
  have hmax : ∀ g : G, d.ofConv g ∈
      maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
    intro g
    obtain ⟨y, hy, hyeq⟩ := point_sub_counit_mem_maximalIdeal
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))
      G e₀ he₀ hε₀ hprim₀ φ hφe g
    have hgm : ι (d.ofConv g) = ι y := by rw [hdval g, ← hyeq]; rfl
    rwa [hιinj hgm]
  have h𝔞max : 𝔞 ≤ maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
    rw [h𝔞def, Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    exact hmax g
  -- a primitive `p`-th root of unity, inside the integral closure
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hζL : IsPrimitiveRoot
      (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ) p :=
    hμ.map_of_injective (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ)).injective
  have hζint : AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ ∈
      integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ := by
    refine ⟨Polynomial.X ^ p - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 hp.out.ne_zero, ?_⟩
    simp [hζL.pow_eq_one]
  set ζ : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ :=
    ⟨AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ, hζint⟩ with hζdef
  have hιζ : ι ζ = AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ := rfl
  -- STEP 2: THE DEEP INPUT
  have hspan : 𝔞 = Ideal.span {ζ - 1} := by
    have hset : Set.range d.ofConv =
        {x : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ | ∃ g : G,
          algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ x =
            φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
              algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g)} := by
      ext x
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g, hdval g⟩
      · rintro ⟨g, hg⟩
        exact ⟨g, hιinj ((hdval g).trans hg.symm)⟩
    rw [h𝔞def, hset]
    exact displacement_span_eq_span_zeta_sub_one hpodd G e₀ he₀ hε₀ hprim₀ hcomul₀
      φ hφe hord hstab hφ1 ζ hζL
  -- STEP 3: some VALUE of the displacement is a unit times `ζ_p − 1`
  have hπ𝔞 : ζ - 1 ∈ 𝔞 := by rw [hspan]; exact Ideal.mem_span_singleton_self _
  have hπmax : ζ - 1 ∈ maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := h𝔞max hπ𝔞
  have hπne : ζ - 1 ≠ 0 := by
    intro h
    have h1 : ζ = 1 := by rwa [sub_eq_zero] at h
    have h2 : AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ = 1 := by
      have h3 := congrArg ι h1
      rwa [hιζ, map_one] at h3
    exact hζL.ne_one hp.out.one_lt h2
  have hdvd : ∀ g : G, ∃ a, a * (ζ - 1) = d.ofConv g := fun g =>
    Ideal.mem_span_singleton'.mp (hspan ▸ hd𝔞 g)
  have hunit : ∃ (g₀ : G) (a₀ : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ),
      IsUnit a₀ ∧ d.ofConv g₀ = a₀ * (ζ - 1) := by
    by_contra hcon
    have hcon' : ∀ (g : G) (a : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ), IsUnit a →
        d.ofConv g ≠ a * (ζ - 1) := fun g a hu heq => hcon ⟨g, a, hu, heq⟩
    have hle : 𝔞 ≤ maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) • 𝔞 := by
      rw [h𝔞def, Ideal.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨a, ha⟩ := hdvd g
      have hanu : a ∈ maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact hcon' g a hu ha.symm
      rw [SetLike.mem_coe, ← ha, Ideal.smul_eq_mul]
      exact Ideal.mul_mem_mul hanu hπ𝔞
    have hjac : maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ≤ Ideal.jacobson ⊥ :=
      le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm
    have hfg : 𝔞.FG := by rw [h𝔞def]; exact fg_span_range _
    have hbot : 𝔞 = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ 𝔞 hfg hle hjac
    rw [hbot, Ideal.mem_bot] at hπ𝔞
    exact hπne hπ𝔞
  obtain ⟨g₀, a₀, ha₀unit, ha₀⟩ := hunit
  -- ## the character computation
  intro σ hσ m n hm hn
  -- the Galois element, restricted to the integral closure
  have hσint : ∀ x : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ,
      σ (ι x) ∈ integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ := fun x =>
    IsIntegral.map (σ.toAlgHom.restrictScalars 𝒪ᵖᵍᵥ) x.2
  set sI : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ →ₐ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ :=
    AlgHom.codRestrict ((σ.toAlgHom.restrictScalars 𝒪ᵖᵍᵥ).comp ι)
      (integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) hσint with hsIdef
  have hsIι : ∀ x, ι (sI x) = σ (ι x) := fun _ => rfl
  have hinert : ∀ x : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ,
      sI x - x ∈ maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
    intro x
    have hs : σ • x = sI x := hιinj rfl
    have := hσ x
    rwa [hs] at this
  -- STEP 4: `σ • φ = φ ^ m`, transported to the integral points
  have hkey : ∀ g : G, σ (χ g) = ((toConv χ) ^ m).ofConv g := by
    intro g
    have h0 : (AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm (σ • φ) =
        ((toConv χ) ^ m).ofConv := by
      rw [hm, liftEquiv_symm_vendored_pow, hχdef]
    exact congrArg (fun f : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ => f g) h0
  have hmpow : ∀ g : G, sI (χI g) = ((toConv χI) ^ m).ofConv g := by
    intro g
    refine hιinj ?_
    have h1 : ι (((toConv χI) ^ m).ofConv g) = ((toConv χ) ^ m).ofConv g := by
      have h := comp_convPow ι (toConv χI) m
      rw [WithConv.ofConv_toConv, hιχ] at h
      exact congrArg (fun f : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ => f g) h
    rw [h1, hsIι]
    exact hkey g
  have hclin : ∀ g : G, sI (c.ofConv g) = (c ^ m).ofConv g := by
    intro g
    have h := AlgHom.toLinearMap_convPow (toConv χI) m
    rw [WithConv.ofConv_toConv, ← hcdef] at h
    have h2 := congrArg (fun f : WithConv (G →ₗ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) =>
      f.ofConv g) h
    simp only [AlgHom.toLinearMap_apply] at h2
    rw [← h2]
    exact hmpow g
  obtain ⟨r, hr, hcm⟩ := exists_convPow_rem c hd𝔞 m
  have hdisp : ∀ g : G, sI (d.ofConv g) -
      (m : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) * d.ofConv g = r.ofConv g := by
    intro g
    have hval : (c ^ m).ofConv g = (1 : WithConv (G →ₗ[𝒪ᵖᵍᵥ]
        IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)).ofConv g +
        (m : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) * d.ofConv g + r.ofConv g := by
      rw [hcm, ← hddef]
      simp only [WithConv.ofConv_add, WithConv.ofConv_smul, LinearMap.add_apply,
        LinearMap.smul_apply]
      rw [nsmul_eq_mul]
    have hc0 : c.ofConv g = d.ofConv g + (1 : WithConv (G →ₗ[𝒪ᵖᵍᵥ]
        IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)).ofConv g := by
      rw [hddef]
      simp only [WithConv.ofConv_sub, LinearMap.sub_apply]
      ring
    have hone : sI ((1 : WithConv (G →ₗ[𝒪ᵖᵍᵥ]
        IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)).ofConv g) =
        (1 : WithConv (G →ₗ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)).ofConv g := by
      rw [LinearMap.convOne_apply, AlgHom.commutes]
    have h := hclin g
    rw [hc0, map_add, hone, hval] at h
    linear_combination h
  -- STEP 5–6: comparison with the cyclotomic generator, then cancellation
  have h𝔞sq : 𝔞 ^ 2 = Ideal.span {(ζ - 1) ^ 2} := by
    rw [hspan, Ideal.span_singleton_pow]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (h𝔞sq ▸ hr g₀)
  have hσζ : sI ζ = ζ ^ n := by
    refine hιinj ?_
    rw [hsIι, map_pow, hιζ]
    exact galois_apply_pow_eq_pow_of_cyclotomicCharacter σ n hn _ hζL.pow_eq_one
  obtain ⟨w, hw⟩ := exists_one_add_pow_sub_one (ζ - 1) n
  have h1ζ : (1 : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) + (ζ - 1) = ζ := by ring
  rw [h1ζ] at hw
  have hσπ : sI (ζ - 1) =
      (ζ - 1) * ((n : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) + (ζ - 1) * w) := by
    rw [map_sub, hσζ, map_one, hw]
  have hcancel : (ζ - 1) * (sI a₀ * ((n : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) + (ζ - 1) * w) -
      (m : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) * a₀ - z * (ζ - 1)) = 0 := by
    have hd0 := hdisp g₀
    rw [ha₀, map_mul, hσπ, ← hz] at hd0
    linear_combination hd0
  have hcancel' : sI a₀ * ((n : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) + (ζ - 1) * w) -
      (m : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) * a₀ - z * (ζ - 1) = 0 := by
    rcases mul_eq_zero.mp hcancel with h | h
    · exact absurd h hπne
    · exact h
  set δ : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ := sI a₀ - a₀ with hδdef
  have hδ : δ ∈ maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := hinert a₀
  have hfinal : a₀ * ((n : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) -
        (m : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)) =
      (ζ - 1) * (z - a₀ * w - δ * w) - δ * (n : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
    have hσa : sI a₀ = a₀ + δ := by rw [hδdef]; ring
    rw [hσa] at hcancel'
    linear_combination hcancel'
  have hmem𝔪 : a₀ * ((n : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) -
      (m : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)) ∈
      maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
    rw [hfinal]
    exact Submodule.sub_mem _ (Ideal.mul_mem_right _ _ hπmax)
      (Ideal.mul_mem_right _ _ hδ)
  have hnm : ((n : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) -
      (m : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)) ∈
      maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
    obtain ⟨u, hu⟩ := ha₀unit
    have h := Ideal.mul_mem_left (maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ))
      ((↑u⁻¹ : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)) hmem𝔪
    rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h
  -- STEP 7: an inertia-invariant element of `𝔪` is divisible by `p`
  have hinv : ∀ τ ∈ localInertiaGroup
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)),
      τ (algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ
          ((n : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) -
            (m : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ))) =
        algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ
          ((n : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) -
            (m : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)) := by
    intro τ _
    simp only [map_sub, map_natCast]
  have hspanp := mem_span_natCast_of_inertia_invariant _ hnm hinv
  rw [Nat.modEq_iff_dvd]
  by_contra hnd
  have hpprime : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨a, b, hab⟩ := hpprime.coprime_iff_not_dvd.mpr hnd
  have hpmem : ((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ∈
      Ideal.span {((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)} :=
    Ideal.mem_span_singleton_self _
  have hkmem : ((((n : ℤ) - (m : ℤ)) : ℤ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ∈
      Ideal.span {((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)} := by
    push_cast
    exact hspanp
  have hone : (1 : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ∈
      Ideal.span {((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)} := by
    have hcast := congrArg
      (fun k : ℤ => (k : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)) hab
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one] at hcast
    rw [← hcast]
    exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ (by exact_mod_cast hpmem))
      (Ideal.mul_mem_left _ _ hkmem)
  have hle : Ideal.span {((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)} ≤
      maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact natCast_mem_maximalIdeal_integralClosure
  exact (maximalIdeal.isMaximal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)).ne_top
    ((Ideal.eq_top_iff_one _).mpr (hle hone))

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **No `p`-torsion in the kernel of reduction over the unramified
base** (PROVEN 2026-07-25 over `mem_span_natCast_of_inertia_invariant`;
stated 2026-07-25): a geometric point `φ` of the generic fibre of a
finite flat Hopf order `G` over `𝒪ᵥ ≅ ℤ_p` (`p` ODD) which is

* killed by `p` in the convolution group (`hord`),
* fixed by every local inertia element (`hinv`), and
* congruent to the counit modulo the maximal ideal of the integral
  closure (`hred`, which is what
  `point_sub_counit_mem_maximalIdeal` supplies for a point of the
  connected component)

is the convolution unit.

Content: `hinv` says every value of `φ` is fixed by inertia, hence
lies in the maximal unramified extension `ℚ_p^{nr}`; the values are
integral because `G` is module-finite, so `φ` is an `𝒪^{nr}`-point,
`φ ∈ G(𝒪^{nr})`. `hred` says it lies in the kernel of the reduction
`G(𝒪^{nr}) → G(𝔽̄_p)`. That kernel is torsion-free at `p` because
`𝒪^{nr} = W(𝔽̄_p)` is ABSOLUTELY UNRAMIFIED: `e = 1 < p − 1` for `p`
odd (`hpodd` — at `p = 2` one has `e = p − 1` and the statement is
FALSE, which is why the whole node needs `p` odd). References:
Raynaud, Bull. SMF 102 (1974), 3.3.2–3.3.5; Fontaine, *Il n'y a pas de
variété abélienne sur `ℤ`*, §1; Tate, *Finite flat group schemes*, in
Cornell–Silverman–Stevens, §4 (the `e < p − 1` bound). Concretely for
the order-`p` case: the schematic closure is `Spec 𝒪[T]/(T^p − aT)`
with `v(a) ∈ {0, 1}`, and a nonzero `𝒪^{nr}`-point with `T ∈ 𝔪`
forces `v(T)·(p − 1) = v(a) ≤ 1`, impossible.

Neither the connected idempotent nor `hstab` is needed here: the
input this leaf consumes is the congruence `hred`, which is where
connectedness has already been spent.

**PROVEN 2026-07-25, sorry-free**, by the elementary convolution-
filtration argument of `eq_convOne_of_convPow_prime_eq_one` (see the
`ConvFiltration` section docstring: `c^p = 1` is a binomial identity in
mathlib's convolution RING, the middle coefficients are divisible by
`p`, the top term is absorbed by `𝔞 ⊆ (p)`, and Nakayama finishes)
fed with the ramification input
`mem_span_natCast_of_inertia_invariant` above. Neither formal groups
nor the Oort–Tate classification are used. -/
theorem eq_one_of_inertia_invariant_of_reduction_counit
    (hpodd : Odd p)
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵍᵥ G] [Module.Flat 𝒪ᵖᵍᵥ G] [Module.Finite 𝒪ᵖᵍᵥ G]
    (φ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)
    (hord : φ ^ p = 1)
    (hinv : ∀ σ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      σ • φ = φ)
    (hred : ∀ g : G, φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
        algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g) ∈
      Submodule.map (Algebra.linearMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ)
        (IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ))) :
    φ = 1 := by
  classical
  haveI : Algebra.IsIntegral 𝒪ᵖᵍᵥ G := Algebra.IsIntegral.of_finite 𝒪ᵖᵍᵥ G
  -- the `𝒪ᵥ`-point of the model and its corestriction to `𝒪̄`
  set χ : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ :=
    (AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm φ with hχ
  have hint : ∀ a : G, χ a ∈ integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ := fun a =>
    (Algebra.IsIntegral.isIntegral (R := 𝒪ᵖᵍᵥ) a).map χ
  set χI : G →ₐ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ :=
    AlgHom.codRestrict χ (integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) hint with hχI
  set ι : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ :=
    { algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ with
      commutes' := fun _ => rfl } with hι
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext h
  have hιχ : ι.comp χI = χ := AlgHom.ext fun _ => rfl
  -- the convolution unit of the generic fibre, read on `G`
  have hunitval : ∀ g : G,
      (1 : WithConv (ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)).ofConv
          ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) =
        algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g) := by
    intro g
    have h := congrArg (fun f : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ => f g)
      (liftEquiv_symm_convOne (R := 𝒪ᵖᵍᵥ) (S := ℚᵖᵍᵥ) (H₀ := G) (B₀ := ℚᵖᵍᵥᵃˡᵍ))
    simpa [AlgHom.liftEquiv_symm_apply, AlgHom.convOne_apply] using h
  -- `p` is nonzero in the integral closure (characteristic zero)
  have hp0 : ((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ≠ 0 := by
    intro h
    have h1 : ((p : ℕ) : ℚᵖᵍᵥᵃˡᵍ) = 0 := by
      have h2 := congrArg (algebraMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ) h
      rwa [map_natCast, map_zero] at h2
    exact hp.out.ne_zero (by exact_mod_cast h1)
  -- the point, as an element of the convolution ring over `𝒪̄`
  set c : WithConv (G →ₗ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) :=
    toConv χI.toLinearMap with hc
  have hdval : ∀ g : G, ι ((c - 1).ofConv g) =
      φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
        algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g) := by
    intro g
    rw [WithConv.ofConv_sub, LinearMap.sub_apply, map_sub]
    congr 1
  -- `hred`, read inside the integral closure
  have hmax : ∀ g : G, (c - 1).ofConv g ∈
      IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) := by
    intro g
    obtain ⟨m, hm, hmeq⟩ := hred g
    have hgm : ι ((c - 1).ofConv g) = ι m := by rw [hdval g, ← hmeq]; rfl
    rwa [hιinj hgm]
  -- `hinv`: the displacement takes inertia-invariant values
  have hfix : ∀ σ ∈ localInertiaGroup
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)),
      ∀ g : G, σ (ι ((c - 1).ofConv g)) = ι ((c - 1).ofConv g) := by
    intro σ hσ g
    have hφfix : σ (φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g)) = φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) :=
      congrArg (fun ψ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ =>
        ψ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g)) (hinv σ hσ)
    have hone : σ • (1 : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ) = 1 := smul_one σ
    have h1fix : σ (algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g)) =
        algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g) := by
      rw [← hunitval g]
      exact congrArg (fun ψ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ =>
        ψ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g)) hone
    rw [hdval g, map_sub, hφfix, h1fix]
  -- THE RAMIFICATION INPUT: `e = 1`, so the values are divisible by `p`
  have hmem : ∀ g : G, (c - 1).ofConv g ∈
      Ideal.span {((p : ℕ) : IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)} := fun g =>
    mem_span_natCast_of_inertia_invariant _ (hmax g) (fun σ hσ => hfix σ hσ g)
  -- `φ^p = 1` transported to the `𝒪ᵥ`-points, then to `𝒪̄`, then to
  -- the convolution RING of linear maps
  have hχp : (toConv χ) ^ p = (1 : WithConv (G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)) := by
    apply WithConv.ofConv_injective
    have h := liftEquiv_symm_vendored_pow (R := 𝒪ᵖᵍᵥ) (S := ℚᵖᵍᵥ) (H := G)
      (L := ℚᵖᵍᵥᵃˡᵍ) φ p
    rw [hord, vendored_one_eq_convOne, liftEquiv_symm_convOne] at h
    exact h.symm
  have hχIp : (toConv χI) ^ p =
      (1 : WithConv (G →ₐ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)) := by
    apply WithConv.ofConv_injective
    refine AlgHom.ext fun a => hιinj ?_
    have h := comp_convPow ι (toConv χI) p
    rw [WithConv.ofConv_toConv, hιχ, hχp] at h
    have h2 := congrArg (fun f : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ => f a) h
    simpa [comp_convOne ι] using h2
  have hcp : c ^ p = 1 := by
    have h := AlgHom.toLinearMap_convPow (toConv χI) p
    rw [hχIp, AlgHom.toLinearMap_convOne] at h
    exact h.symm
  -- the elementary convolution-filtration argument
  have hc1 : c = 1 :=
    eq_convOne_of_convPow_prime_eq_one hp.out hpodd hp0 c hcp hmem hmax
  -- and back to `φ`
  apply (AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm.injective
  rw [vendored_one_eq_convOne, liftEquiv_symm_convOne]
  refine AlgHom.ext fun a => ?_
  have h : χI a = (1 : WithConv (G →ₗ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)).ofConv a := by
    have h0 := congrArg (fun f : WithConv (G →ₗ[𝒪ᵖᵍᵥ] IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) =>
      f.ofConv a) hc1
    rw [hc] at h0
    exact h0
  calc ((AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm φ) a
      = ι (χI a) := rfl
    _ = ι (algebraMap 𝒪ᵖᵍᵥ (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)
          (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) a)) := by
        rw [h, LinearMap.convOne_apply]
    _ = algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) a) := ι.commutes _
    _ = (1 : WithConv (G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)).ofConv a := (AlgHom.convOne_apply a).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Connectedness makes the inertia character nontrivial** (PROVEN
2026-07-25 over `point_sub_counit_mem_maximalIdeal` and
`eq_one_of_inertia_invariant_of_reduction_counit`): a nontrivial
geometric point of the CONNECTED component killed by `p` and
generating an inertia-stable cyclic group cannot have trivial inertia
character — the étale alternative of the Raynaud dichotomy is
excluded.

Proof: if every inertia element moved `φ` to `φ^m` with `m ≡ 1 mod p`
then, `φ` being killed by `p`, every inertia element would FIX `φ`;
the point of the connected component reduces to the counit
(`point_sub_counit_mem_maximalIdeal`), so `φ` would be an
`𝒪^{nr}`-point in the kernel of reduction killed by `p`, hence the
counit by `eq_one_of_inertia_invariant_of_reduction_counit` —
contradicting `hφ1`. Geometrically: a connected order-`p` group scheme
over `ℤ_p` has NO nontrivial unramified points, because its points
over the unramified base all reduce to the identity and the kernel of
reduction has no `p`-torsion at `e = 1 < p − 1`. -/
theorem not_inertia_character_trivial_of_connected
    (hpodd : Odd p)
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵍᵥ G] [Module.Flat 𝒪ᵖᵍᵥ G] [Module.Finite 𝒪ᵖᵍᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵍᵥ) e₀ = (1 : 𝒪ᵖᵍᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (φ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = 1)
    (hord : φ ^ p = 1)
    (hstab : ∀ τ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      ∃ m : ℕ, τ • φ = φ ^ m)
    (hφ1 : φ ≠ 1) :
    ¬ (∀ σ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      ∀ m : ℕ, σ • φ = φ ^ m → m ≡ 1 [MOD p]) := by
  intro htriv
  -- a trivial character means every inertia element fixes `φ` outright
  have hinv : ∀ σ ∈ localInertiaGroup
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)),
      σ • φ = φ := by
    intro σ hσ
    obtain ⟨m, hm⟩ := hstab σ hσ
    rw [hm, pow_eq_pow_of_natModEq hord (htriv σ hσ m hm), pow_one]
  -- and a point of the connected component reduces to the counit
  have hred : ∀ g : G, φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
      algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g) ∈
      Submodule.map (Algebra.linearMap (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) ℚᵖᵍᵥᵃˡᵍ)
        (IsLocalRing.maximalIdeal (IntegralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)) := fun g =>
    point_sub_counit_mem_maximalIdeal
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))
      G e₀ he₀ hε₀ hprim₀ φ hφe g
  exact hφ1 (eq_one_of_inertia_invariant_of_reduction_counit hpodd G φ hord
    hinv hred)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The Oort–Tate `μ_p`-value of an inertia-stable cyclic group of
points** (RESTATED 2026-07-25, see the CORRECTION NOTE below; PROVEN
the same day over `inertia_character_trivial_or_cyclotomic` and
`eq_one_of_inertia_invariant_of_reduction_counit`, both of which are
now themselves PROVEN, so that the shared `μ`-type node's ONLY
remaining input is the single valuation leaf
`displacement_span_le_span_zeta_sub_one`): under the hypotheses of
`connected_cyclic_point_smul_eq_conv_pow_cyclotomicCharacter` and with
`φ ≠ 1`, there is a NONTRIVIAL `p`-th root of unity `ζ ∈ ℚᵥᵃˡᵍ` which
reads the local-inertia action on the convolution-cyclic group
`⟨φ⟩`: whenever an inertia element `σ` moves `φ` to its `m`-th
convolution power, it moves `ζ` to `ζ^m`. Equivalently, `ζ` exhibits
an isomorphism `⟨φ⟩ ≅ μ_p` OF INERTIA MODULES — the `μ_p`-ness of the
schematic closure, in exactly the form the node consumes.

Geometrically: for the vanishing ideal `I` of `⟨φ⟩` in `G`,
`Spec (G/I)` is the schematic closure of the inertia-stable cyclic
group `⟨φ⟩ ≅ ℤ/p` of geometric points inside the model — a finite
flat closed subGROUP scheme of order `p` killed by `p`, connected by
`hφe`/`hprim₀`/`hcomul₀`. Over the completed maximal unramified
extension it is `μ_p`, whose coordinate ring is
`𝒪^nr[T]/(T^p − 1)` with `ΔT = T ⊗ T` and `εT = 1`, and `ζ` is the
value `φ(1 ⊗ T)` of that coordinate at `φ`.

**CORRECTION NOTE (2026-07-25): the previous form of this leaf was
FALSE and has been deleted.** It asked for the coordinate itself, over
`𝒪ᵥ`: an ideal `I ⊆ G` which is a coideal killed by `φ`, together with
`x ∈ G` satisfying `ε x = 1`, `x^p ≡ 1 mod I`,
`Δ x ≡ x ⊗ x mod (I ⊗ G + G ⊗ I)` and `φ(1 ⊗ x) ≠ 1` (the deleted
theorems `exists_muType_closure` and the deleted first form of
`exists_muType_coordinate`). Such data forces the schematic closure
`C` to be `μ_p` OVER `𝒪ᵥ = ℤ_p` itself: `x` is group-like modulo `I`
with `x^p ≡ 1`, so it is a homomorphism `C → μ_p` over `ℤ_p`,
nontrivial because `φ(1 ⊗ x) ≠ 1`; a nontrivial quotient of an
order-`p` group scheme is everything, so `ℚ_p ⊗ I = 0`, hence `I = 0`
by flatness of `G`, and a nontrivial homomorphism of finite flat group
schemes of order `p` is an isomorphism. The hypotheses do NOT force
that. By Oort–Tate the CONNECTED order-`p` group schemes over `ℤ_p`
(`p` odd, `e = 1 < p − 1`) form a family of `p − 1` pairwise
non-isomorphic schemes: the parameters `(a, b)` with `ab = w_p` modulo
`(a, b) ∼ (u^{p−1} a, u^{1−p} b)` have `v(a) = 1`, and `b` ranges over
`ℤ_p^×/(ℤ_p^×)^{p−1} ≅ ℤ/(p − 1)`. These are the twists `μ_p ⊗ ψ` of
`μ_p` by the UNRAMIFIED characters `ψ : G_{ℚ_p} → (ℤ/p)^×` of order
dividing `p − 1`, and every one of them satisfies ALL hypotheses of
this leaf: its coordinate ring becomes `𝒪^nr[T]/(T^p − 1)` — a local
ring — over `𝒪^nr`, so it has no nontrivial idempotents and `e₀ = 1`
gives `he₀`, `hε₀`, `hprim₀`, `hcomul₀`, `hφe`; its geometric points
are killed by `p` (`hord`); and Galois acts on them by `χ_cyc · ψ`,
which restricted to INERTIA is `χ_cyc` because `ψ` is unramified, so
`hstab` holds. Yet for `ψ ≠ 1` no such `x` exists. The defect is
precisely that the coordinate lives over `𝒪^nr`, not over `𝒪ᵥ`. Its
VALUE `ζ` at `φ` is nevertheless well defined and inertia-equivariant,
because inertia fixes `𝒪^nr` pointwise — and that is all the node ever
used, so the corrected statement above is what is asserted here.

**Proof (2026-07-25) — the `μ_p`-COORDINATE is never constructed; the
content is entirely a CHARACTER IDENTITY.** `φ ≠ 1` and `hord` give
`φ` exact convolution order `p`, so `hstab` produces a character
`χ_φ : I_v → (ℤ/p)ˣ` by `σ • φ = φ^{χ_φ(σ)}`, and the assertion
"`ζ` exhibits `⟨φ⟩ ≅ μ_p` as inertia modules" says exactly
`χ_φ = χ_cyc mod p` — because for a PRIMITIVE `p`-th root of unity
`ζ` the relation `σ ζ = ζ^{χ_cyc(σ)}` is automatic
(`galois_apply_pow_eq_pow_of_cyclotomicCharacter`). So ANY primitive
`p`-th root of unity of `ℚᵥᵃˡᵍ` serves as `ζ` — here the image of a
primitive root of the abstract closure `ℚᵃˡᵍ` under
`AlgebraicClosure.map`, primitive because a field map is injective —
and the whole leaf reduces to the identity of characters, which is
split into its two classical halves:

* `inertia_character_trivial_or_cyclotomic` — RAYNAUD's dichotomy at
  `e = 1 < p − 1`: `χ_φ` is either trivial or `χ_cyc`, as characters
  (PROVEN 2026-07-25 over the single valuation leaf
  `displacement_span_le_span_zeta_sub_one`, "the displacement's value
  ideal is CONTAINED in `(ζ_p − 1)`", which is the one-dimensionality
  half of Oort–Tate's `v(a) = 1` and is the only sorry left in this
  file — the reverse inclusion, Raynaud's `k ≤ e`, is proven);
* `not_inertia_character_trivial_of_connected` — CONNECTEDNESS kills
  the trivial alternative (itself proven from
  `point_sub_counit_mem_maximalIdeal`, "a connected point reduces to
  the counit", and the ramification leaf
  `eq_one_of_inertia_invariant_of_reduction_counit`, "no `p`-torsion
  in the kernel of reduction over `𝒪^nr`").

`Or.resolve_left` of the two gives `χ_φ = χ_cyc`, i.e.
`m ≡ n mod p` whenever `σ • φ = φ^m` and `n` represents
`χ_cyc(σ)` — the residue `n` being supplied by
`exists_natCast_sub_mem_span` — and `pow_eq_pow_of_natModEq` turns
that into `ζ^n = ζ^m`.

Note this route never needs the schematic closure `I`, the
`𝒪^nr`-rational coordinate `x`, or any `tensorIdeal`/`ConvPow`
group-like-modulo-a-coideal bookkeeping: an `𝒪^nr`-coordinate of the
closure is EQUIVALENT to (not stronger than) the inertia-equivariant
value `ζ` asserted here, so constructing one would only repackage the
same content while adding a base change of `G` to `𝒪^nr`. (The
`tensorIdeal`/`ConvPow`/`VendoredClosure` block that used to sit above
was accordingly DELETED on 2026-07-25 as free-floating with no
prospective consumer; recover it from git history if a future
Oort–Tate proof wants it.)

Soundness: the hypothesis set is inhabited (the nontrivial points of
`μ_p` over `ℤ_p`, with `e₀ = 1` its connected counit idempotent), and
by the classification cited the conclusion holds for every inhabitant,
including the unramified twists `μ_p ⊗ ψ` on which the earlier,
`𝒪ᵥ`-rational form of this leaf failed. `hstab` is NOT redundant —
for the `p`-torsion of a supersingular elliptic curve over `ℤ_p` tame
inertia acts through the level-`2` fundamental characters, no line is
stable, no `μ_p` sits inside the model, and no such `ζ` exists. -/
theorem exists_muType_coordinate
    (hpodd : Odd p)
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵍᵥ G] [Module.Flat 𝒪ᵖᵍᵥ G] [Module.Finite 𝒪ᵖᵍᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵍᵥ) e₀ = (1 : 𝒪ᵖᵍᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵍᵥ) e₀ *
      (e₀ ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = e₀ ⊗ₜ[𝒪ᵖᵍᵥ] e₀)
    (φ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = 1)
    (hord : φ ^ p = 1)
    (hstab : ∀ τ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      ∃ m : ℕ, τ • φ = φ ^ m)
    (hφ1 : φ ≠ 1) :
    ∃ ζ : ℚᵖᵍᵥᵃˡᵍ, ζ ^ p = 1 ∧ ζ ≠ 1 ∧
      ∀ σ ∈ localInertiaGroup
          (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
            (Fact.out : p.Prime)),
        ∀ m : ℕ, σ • φ = φ ^ m → σ ζ = ζ ^ m := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- Raynaud's dichotomy, with the unramified branch killed by connectedness
  have hcong : ∀ σ ∈ localInertiaGroup
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)),
      ∀ m n : ℕ, σ • φ = φ ^ m →
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p
            ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
              σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]) - (n : ℤ_[p]) ∈
          Ideal.span {((p : ℕ) : ℤ_[p])} → m ≡ n [MOD p] :=
    (inertia_character_trivial_or_cyclotomic hpodd G e₀ he₀ hε₀ hprim₀
      hcomul₀ φ hφe hord hstab hφ1).resolve_left
      (not_inertia_character_trivial_of_connected hpodd G e₀ he₀ hε₀ hprim₀
        φ hφe hord hstab hφ1)
  -- any primitive `p`-th root of unity of `ℚᵥᵃˡᵍ` reads the action
  obtain ⟨μ, hμ⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hζ : IsPrimitiveRoot
      (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ) p :=
    hμ.map_of_injective
      (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ)).injective
  refine ⟨_, hζ.pow_eq_one, hζ.ne_one hp.out.one_lt, ?_⟩
  intro σ hσ m hm
  obtain ⟨n, hn⟩ := exists_natCast_sub_mem_span
    (((cyclotomicCharacter (AlgebraicClosure ℚ) p
      ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
        σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]))
  have hbridge : σ (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ) =
      (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ) ^ n :=
    galois_apply_pow_eq_pow_of_cyclotomicCharacter σ n hn _ hζ.pow_eq_one
  have hmn : m ≡ n [MOD p] := hcong σ hσ m n hm hn
  rw [hbridge]
  exact (pow_eq_pow_of_natModEq hζ.pow_eq_one hmn).symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The Oort–Tate `μ`-type node** (PROVEN 2026-07-24 over the single
classification leaf `exists_muType_coordinate` — THE shared order-`p`
group-scheme input of the tree; see the section docstring for the
three consumers): a geometric point `φ`
of the generic fibre of a finite flat Hopf order `G` over
`𝒪ᵥ ≅ ℤ_p` (`p` ODD) which

* lies in the CONNECTED component — value `1` on the connected counit
  idempotent `e₀` (`hφe`, with `hprim₀`/`hcomul₀` the primitivity and
  group-law-closure of the component),
* is killed by `p` in the convolution group (`hord`), and
* generates an inertia-STABLE cyclic subgroup — every local inertia
  element moves `φ` to one of its convolution powers (`hstab`, the
  ONE-DIMENSIONALITY input placing the tame character in level 1)

is moved by any local inertia element `σ` to its `n`-th convolution
power for EVERY `n ≡ χ_cyc(σ̃) mod p`.

Proof (Oort–Tate, *Group schemes of prime order*, Ann. Sci. ÉNS 1970;
Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull. SMF 102
(1974), 3.3.6/3.4.3; Serre, Duke Math. J. 54 (1987), §2.4, §2.8
prop. 8; Tate, "Finite flat group schemes", in
Cornell–Silverman–Stevens): if `φ = 1` the statement is trivial
(`σ • 1 = 1 = 1^n`, by `MulDistribMulAction`); otherwise `φ` has
exact convolution order `p` and the CLASSIFICATION leaf
`exists_muType_coordinate` — the `μ_p`-ness of the schematic closure
of `⟨φ⟩`, the only remaining input — supplies a nontrivial `p`-th root
of unity `ζ` reading the inertia action on `⟨φ⟩`. Feeding the
stability relation `σ • φ = φ^m` of `hstab` into it gives `σ ζ = ζ^m`,
while the root-of-unity bridge
`galois_apply_pow_eq_pow_of_cyclotomicCharacter` gives `σ ζ = ζ^n`;
`ζ` is a primitive `p`-th root of unity, so `m ≡ n mod p`, and
`φ^p = 1` turns that congruence back into `φ^m = φ^n`. The inertia-
stability input is NOT redundant: for the `p`-torsion of a
supersingular elliptic curve over `ℤ_p` (connected, killed by `p`,
`e = 1`) tame inertia acts through the level-2 fundamental characters
of `𝔽_{p²}^×`, which is not a power map and stabilizes no line — so
the bare statement without `hstab` is FALSE, and any consumer must
supply a one-dimensionality input. The conclusion is well-posed
across the residues `n mod p` since `φ^p = 1`. -/
theorem connected_cyclic_point_smul_eq_conv_pow_cyclotomicCharacter
    (hpodd : Odd p)
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵍᵥ G] [Module.Flat 𝒪ᵖᵍᵥ G] [Module.Finite 𝒪ᵖᵍᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵍᵥ) e₀ = (1 : 𝒪ᵖᵍᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵍᵥ) e₀ *
      (e₀ ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = e₀ ⊗ₜ[𝒪ᵖᵍᵥ] e₀)
    (φ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)
    (hφe : φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] e₀) = 1)
    (hord : φ ^ p = 1)
    (hstab : ∀ τ ∈ localInertiaGroup
        (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
          (Fact.out : p.Prime)),
      ∃ m : ℕ, τ • φ = φ ^ m)
    (σ : Field.absoluteGaloisGroup ℚᵖᵍᵥ)
    (hσ : σ ∈ localInertiaGroup
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat
        (Fact.out : p.Prime)))
    (n : ℕ)
    (hn : ((cyclotomicCharacter (AlgebraicClosure ℚ) p
        ((Field.absoluteGaloisGroup.map (algebraMap ℚ ℚᵖᵍᵥ)
          σ).toRingEquiv) : ℤ_[p]ˣ) : ℤ_[p]) - (n : ℤ_[p]) ∈
      Ideal.span {((p : ℕ) : ℤ_[p])}) :
    σ • φ = φ ^ n := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  by_cases hφ1 : φ = 1
  · rw [hφ1, smul_one, one_pow]
  · obtain ⟨m, hm⟩ := hstab σ hσ
    obtain ⟨ζ, hζp, hζ1, hζσ⟩ :=
      exists_muType_coordinate hpodd G e₀ he₀ hε₀ hprim₀ hcomul₀ φ hφe
        hord hstab hφ1
    -- the coordinate value is a primitive `p`-th root of unity
    have hprimζ : IsPrimitiveRoot ζ p :=
      isPrimitiveRoot_of_prime_pow_eq_one hp.out hζp hζ1
    -- the inertia-stability relation, read through the coordinate value
    have hval : σ ζ = ζ ^ m := hζσ σ hσ m hm
    -- and the same value through the cyclotomic character
    have hbridge : σ ζ = ζ ^ n :=
      galois_apply_pow_eq_pow_of_cyclotomicCharacter σ n hn ζ hζp
    have hmn : m ≡ n [MOD p] :=
      natModEq_of_pow_eq_pow hprimζ (hval.symm.trans hbridge)
    rw [hm]
    exact pow_eq_pow_of_natModEq hord hmn

end CyclotomicNode

end OortTate
