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
-- `Polynomial.eval_one_cyclotomic_prime` /
-- `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`: the cyclotomic
-- factorisation `p ~ (ζ_p − 1)^(p−1)`, proof-body use in the Raynaud
-- dichotomy of the `μ`-type node below
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

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

section RaynaudDichotomy

/-! ### Raynaud's dichotomy at `e = 1`, by a displacement-valuation argument

The classification half of the `μ`-type node. See the docstring of
`inertia_character_trivial_or_cyclotomic` at the end of this section for the
argument; the declarations before it are its (generic) toolkit. -/

/-- From `cc ^ n * u = 1` with `n ≠ 0`, the base `cc` is a unit. -/
theorem isUnit_of_pow_mul_eq_one {A : Type*} [CommMonoid A] {cc u : A} {n : ℕ}
    (hn : n ≠ 0) (h : cc ^ n * u = 1) : IsUnit cc := by
  refine isUnit_iff_exists_inv.mpr ⟨cc ^ (n - 1) * u, ?_⟩
  rw [← mul_assoc, ← pow_succ', show n - 1 + 1 = n from by omega]
  exact h

/-- In a valuation ring a finset spans the same ideal as one of its
elements (or `0` when it is empty): divisibility is total, so one
generator divides all the others. -/
theorem exists_span_finset_eq_span_singleton {A : Type*} [CommRing A] [IsDomain A]
    [ValuationRing A] (T : Finset A) :
    ∃ t : A, (t = 0 ∨ t ∈ T) ∧ Ideal.span (T : Set A) = Ideal.span {t} := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨0, Or.inl rfl, le_antisymm ?_ ?_⟩
    · rw [Finset.coe_empty]
      exact Ideal.span_le.mpr (Set.empty_subset _)
    · refine Ideal.span_le.mpr ?_
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Submodule.zero_mem _
  | @insert a T _ ih =>
    obtain ⟨t, htmem, ht⟩ := ih
    have hspan : Ideal.span ((insert a T : Finset A) : Set A)
        = Ideal.span {a} ⊔ Ideal.span ((T : Finset A) : Set A) := by
      rw [Finset.coe_insert, Ideal.span_insert]
    obtain ⟨cc, hcc | hcc⟩ := ValuationRing.cond a t
    · refine ⟨a, Or.inr (Finset.mem_insert_self _ _), ?_⟩
      rw [hspan, ht, sup_eq_left, Ideal.span_singleton_le_span_singleton]
      exact ⟨cc, hcc.symm⟩
    · refine ⟨t, ?_, ?_⟩
      · rcases htmem with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_insert_of_mem h)
      · rw [hspan, ht, sup_eq_right, Ideal.span_singleton_le_span_singleton]
        exact ⟨cc, hcc.symm⟩

/-- The value ideal of a linear map out of a module-finite module into a
valuation ring is generated by a SINGLE value. -/
theorem exists_span_range_eq_span_singleton {R G A : Type*} [CommRing R]
    [AddCommMonoid G] [Module R G] [Module.Finite R G]
    [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A] (f : G →ₗ[R] A) :
    ∃ g₀ : G, Ideal.span (Set.range f) = Ideal.span {f g₀} := by
  classical
  obtain ⟨T, hT⟩ := (Module.Finite.fg_top : (⊤ : Submodule R G).FG)
  have key : ∀ g : G, f g ∈ Ideal.span (f '' (T : Set G)) := by
    intro g
    have hg : g ∈ Submodule.span R (T : Set G) := hT ▸ Submodule.mem_top
    induction hg using Submodule.span_induction with
    | mem y hy => exact Ideal.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [map_smul, Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hy
  have hrange : Ideal.span (Set.range f) = Ideal.span ((T.image f : Finset A) : Set A) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      rintro _ ⟨g, rfl⟩
      rw [Finset.coe_image]
      exact key g
    · rw [Finset.coe_image, Ideal.span_le]
      rintro _ ⟨g, _, rfl⟩
      exact Ideal.subset_span ⟨g, rfl⟩
  obtain ⟨t, htmem, ht⟩ := exists_span_finset_eq_span_singleton (T.image f)
  rcases htmem with h0 | hmem
  · exact ⟨0, by rw [hrange, ht, h0, map_zero]⟩
  · obtain ⟨g₀, -, rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨g₀, by rw [hrange, ht]⟩

/-- Cancelling an `n`-th power inside `Associated`, in a valuation ring:
if `x^n` and `z^n` are associated then so are `x` and `z`. -/
theorem associated_of_associated_pow {A : Type*} [CommRing A] [IsDomain A]
    [ValuationRing A] {x z : A} {n : ℕ} (hn : n ≠ 0)
    (h : Associated (x ^ n) (z ^ n)) : Associated x z := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨cc, hcc | hcc⟩ := ValuationRing.cond x z
  · rcases eq_or_ne x 0 with hx | hx
    · have hz : z = 0 := by rw [← hcc, hx, zero_mul]
      rw [hx, hz]
    · have hz : z ^ n = x ^ n * cc ^ n := by rw [← hcc, mul_pow]
      have h1 : x ^ n * (u : A) = x ^ n * cc ^ n := by rw [hu, hz]
      have h2 : (u : A) = cc ^ n := mul_left_cancel₀ (pow_ne_zero n hx) h1
      have h3 : IsUnit cc := by
        refine isUnit_of_pow_mul_eq_one (u := ((u⁻¹ : Aˣ) : A)) hn ?_
        rw [← h2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      exact ⟨h3.unit, by rw [IsUnit.unit_spec]; exact hcc⟩
  · rcases eq_or_ne z 0 with hz | hz
    · have hx : x = 0 := by rw [← hcc, hz, zero_mul]
      rw [hx, hz]
    · have hx : x ^ n = z ^ n * cc ^ n := by rw [← hcc, mul_pow]
      have h1 : z ^ n * (cc ^ n * (u : A)) = z ^ n * 1 := by
        rw [← mul_assoc, ← hx, hu, mul_one]
      have h2 : cc ^ n * (u : A) = 1 := mul_left_cancel₀ (pow_ne_zero n hz) h1
      have h3 : IsUnit cc := isUnit_of_pow_mul_eq_one hn h2
      exact (Associated.symm ⟨h3.unit, by rw [IsUnit.unit_spec]; exact hcc⟩)

section RaynaudFiltration

variable {R G A : Type*} [CommRing R] [AddCommMonoid G] [Module R G] [Coalgebra R G]
  [CommRing A] [Algebra R A]

/-- The ring identity behind the two displacement filtration lemmas. -/
theorem convPow_succ_sub_one (f : WithConv (G →ₗ[R] A)) (m : ℕ) :
    f ^ (m + 1) - 1 = (f ^ m - 1) + (f - 1) + (f ^ m - 1) * (f - 1) := by
  have h : (f ^ m - 1) * (f - 1) = f ^ (m + 1) - f ^ m - f + 1 := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, ← pow_succ]
    abel
  rw [h]; abel

/-- A convolution power of a point stays inside the displacement ideal. -/
theorem convPow_sub_one_apply_mem (f : WithConv (G →ₗ[R] A)) {𝔞 : Ideal A}
    (hf : ∀ x, (f - 1).ofConv x ∈ 𝔞) : ∀ (m : ℕ) (x : G), (f ^ m - 1).ofConv x ∈ 𝔞 := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    rw [convPow_succ_sub_one, WithConv.ofConv_add, WithConv.ofConv_add,
      LinearMap.add_apply, LinearMap.add_apply]
    refine Submodule.add_mem _ (Submodule.add_mem _ (ih x) (hf x)) ?_
    exact Ideal.mul_le_right (convMul_apply_mem_mul _ _ ih hf x)

/-- **The linear term of a convolution power**: `c^m − 1 ≡ m·(c − 1)`
modulo the SQUARE of the displacement ideal. -/
theorem convPow_sub_one_sub_nsmul_mem (f : WithConv (G →ₗ[R] A)) {𝔞 : Ideal A}
    (hf : ∀ x, (f - 1).ofConv x ∈ 𝔞) : ∀ (m : ℕ) (x : G),
      ((f ^ m - 1) - m • (f - 1)).ofConv x ∈ 𝔞 ^ 2 := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    have key : (f ^ (m + 1) - 1) - (m + 1) • (f - 1)
        = ((f ^ m - 1) - m • (f - 1)) + (f ^ m - 1) * (f - 1) := by
      rw [succ_nsmul, convPow_succ_sub_one]
      abel
    rw [key, WithConv.ofConv_add, LinearMap.add_apply]
    refine Submodule.add_mem _ (ih x) ?_
    rw [sq]
    exact convMul_apply_mem_mul _ _ (convPow_sub_one_apply_mem f hf m) hf x

/-- **The `p`-torsion binomial identity**, with the top term kept
separate: for `c^p = 1` the linear term `p·(c − 1)` lies in
`(p)·𝔞² ⊔ 𝔞^p`, where `𝔞` is any ideal containing the displacement
values. This is `eq_convOne_of_convPow_prime_eq_one`'s expansion without
its absolute-unramifiedness hypothesis. -/
theorem nsmul_sub_one_mem_of_convPow_prime_eq_one {q : ℕ} (hq : q.Prime)
    (c : WithConv (G →ₗ[R] A)) (hcp : c ^ q = 1) {𝔞 : Ideal A}
    (hd : ∀ x, (c - 1).ofConv x ∈ 𝔞) (x : G) :
    (q : ℕ) • ((c - 1).ofConv x) ∈ Ideal.span {(q : A)} * 𝔞 ^ 2 ⊔ 𝔞 ^ q := by
  classical
  set d : WithConv (G →ₗ[R] A) := c - 1 with hd_def
  set K : Ideal A := Ideal.span {(q : A)} * 𝔞 ^ 2 ⊔ 𝔞 ^ q with hK_def
  have hbin : ∑ m ∈ Finset.range (q + 1), (q.choose m) • d ^ m = 1 := by
    have hcd : d + 1 = c := by rw [hd_def]; abel
    have h := (Commute.one_right d).add_pow q
    rw [hcd, hcp] at h
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) h.symm
    rw [one_pow, mul_one, nsmul_eq_mul]
    exact (Nat.cast_commute _ _).eq
  have hrest : (q : ℕ) • d +
      ∑ i ∈ Finset.Ico 1 q, (q.choose (i + 1)) • d ^ (i + 1) = 0 := by
    rw [Finset.sum_range_succ' (fun m => (q.choose m) • d ^ m) q] at hbin
    simp only [Nat.choose_zero_right, pow_zero, one_smul] at hbin
    have h0 : ∑ i ∈ Finset.range q, (q.choose (i + 1)) • d ^ (i + 1) = 0 :=
      add_right_cancel (b := (1 : WithConv (G →ₗ[R] A))) (hbin.trans (zero_add _).symm)
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hq.pos] at h0
    simpa using h0
  have hterm : ∀ i ∈ Finset.Ico 1 q, ∀ z : G,
      ((q.choose (i + 1)) • d ^ (i + 1)).ofConv z ∈ K := by
    intro i hi z
    rw [Finset.mem_Ico] at hi
    have hz : (d ^ (i + 1)).ofConv z ∈ 𝔞 ^ (i + 1) :=
      convPow_apply_mem_pow d hd _ z
    rw [WithConv.ofConv_smul, LinearMap.smul_apply]
    rcases eq_or_lt_of_le (show i + 1 ≤ q by omega) with heq | hlt
    · rw [heq, Nat.choose_self, one_smul, hK_def]
      exact Submodule.mem_sup_right (heq ▸ hz)
    · obtain ⟨k, hk⟩ : q ∣ q.choose (i + 1) := hq.dvd_choose_self (by omega) hlt
      have hz2 : (d ^ (i + 1)).ofConv z ∈ 𝔞 ^ 2 :=
        Ideal.pow_le_pow_right (by omega) hz
      rw [hk, nsmul_eq_mul, Nat.cast_mul, mul_assoc, hK_def]
      exact Submodule.mem_sup_left
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
          (Ideal.mul_mem_left _ _ hz2))
  have h0 : (q : ℕ) • d.ofConv x +
      ∑ i ∈ Finset.Ico 1 q, (q.choose (i + 1)) • (d ^ (i + 1)).ofConv x = 0 := by
    have h1 := congrArg (fun f : WithConv (G →ₗ[R] A) => f.ofConv x) hrest
    simp only [WithConv.ofConv_add, WithConv.ofConv_sum, WithConv.ofConv_smul,
      WithConv.ofConv_zero, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.zero_apply] at h1
    exact h1
  have hsm : ∑ i ∈ Finset.Ico 1 q, (q.choose (i + 1)) • (d ^ (i + 1)).ofConv x ∈ K :=
    Submodule.sum_mem _ fun i hi => by
      simpa only [WithConv.ofConv_smul, LinearMap.smul_apply] using hterm i hi x
  rw [eq_neg_of_add_eq_zero_left h0]
  exact Submodule.neg_mem _ hsm

end RaynaudFiltration

/-- `(1 + π)^n = 1 + n π` modulo `π²`. -/
theorem one_add_pow_sub_one_sub_nsmul_dvd {A : Type*} [CommRing A] (π : A) (n : ℕ) :
    π ^ 2 ∣ (1 + π) ^ n - 1 - n • π := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(1 + π) * w + n, ?_⟩
    have hstep : (1 + π) ^ (n + 1) - 1 - (n + 1) • π
        = (1 + π) * ((1 + π) ^ n - 1 - n • π) + (n : A) * π ^ 2 := by
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [hstep, hw]
    ring

/-- **`p` is associated to `(ζ − 1)^(p−1)`** for a primitive `p`-th root
of unity `ζ` in a domain (the standard cyclotomic factorisation of `p`,
transcribed from mathlib's `associated_zeta_sub_one_pow_prime` for rings
of integers). -/
theorem associated_sub_one_pow_natCast {A : Type*} [CommRing A] [IsDomain A]
    {q : ℕ} [hq : Fact q.Prime] {ζ : A} (hζ : IsPrimitiveRoot ζ q) :
    Associated ((ζ - 1) ^ (q - 1)) ((q : ℕ) : A) := by
  classical
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  rw [← Polynomial.eval_one_cyclotomic_prime (R := A) (p := q),
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [← Nat.totient_prime hq.out, ← hζ.card_primitiveRoots, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun η hη => ?_
  have hη' : IsPrimitiveRoot η q := isPrimitiveRoot_of_mem_primitiveRoots hη
  obtain ⟨i, -, hi, hζη⟩ := (hζ.isPrimitiveRoot_iff).mp hη'
  have hassoc : Associated (ζ - 1) (η - 1) := by
    rw [← hζη]
    exact hζ.associated_sub_one_pow_sub_one_of_coprime hi
  simpa using hassoc.neg_right

local notation "𝒪̄ᵖᵍᵥ" => IntegralClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))) (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))))

/-- A unit plus a maximal-ideal element is a unit. -/
theorem isUnit_add_mem_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A] {a b : A}
    (ha : IsUnit a) (hb : b ∈ IsLocalRing.maximalIdeal A) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : a ∈ IsLocalRing.maximalIdeal A := by
    have h3 := Submodule.sub_mem _ h1 hb
    simpa using h3
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h2
  exact h2 ha

/-- `p` lies in the maximal ideal of `𝒪̄ᵥ`: it does in `𝒪ᵥ`
(`maximalIdeal_eq_span_natCast`) and the integral extension is a local
homomorphism. -/
theorem natCast_prime_mem_maximalIdeal :
    ((p : ℕ) : 𝒪̄ᵖᵍᵥ) ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
  have hmap : Ideal.map (algebraMap 𝒪ᵖᵍᵥ 𝒪̄ᵖᵍᵥ) (IsLocalRing.maximalIdeal 𝒪ᵖᵍᵥ) ≤
      IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
    exact fun hu => ha (IsLocalHom.map_nonunit a hu)
  have h2 : ((p : ℕ) : 𝒪ᵖᵍᵥ) ∈ IsLocalRing.maximalIdeal 𝒪ᵖᵍᵥ := by
    rw [maximalIdeal_eq_span_natCast]
    exact Ideal.mem_span_singleton_self _
  have h3 := hmap (Ideal.mem_map_of_mem (algebraMap 𝒪ᵖᵍᵥ 𝒪̄ᵖᵍᵥ) h2)
  rwa [map_natCast] at h3

/-- A natural number lying in the maximal ideal of `𝒪̄ᵥ` is divisible by
`p` (Bézout against `p`). -/
theorem dvd_of_natCast_mem_maximalIdeal (k : ℕ)
    (hk : ((k : ℕ) : 𝒪̄ᵖᵍᵥ) ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ) : p ∣ k := by
  by_contra hnd
  have hcop : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd
  obtain ⟨a, b, hab⟩ : IsCoprime ((p : ℕ) : ℤ) ((k : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop
  have hone : (1 : 𝒪̄ᵖᵍᵥ) ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
    have h := congrArg (fun z : ℤ => (z : 𝒪̄ᵖᵍᵥ)) hab
    push_cast at h
    rw [← h]
    exact Submodule.add_mem _
      (Ideal.mul_mem_left _ _ natCast_prime_mem_maximalIdeal)
      (Ideal.mul_mem_left _ _ hk)
  exact (IsLocalRing.maximalIdeal.isMaximal 𝒪̄ᵖᵍᵥ).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

/-- Two naturals congruent modulo the maximal ideal of `𝒪̄ᵥ` are
congruent mod `p`. -/
theorem natModEq_of_sub_mem_maximalIdeal {m n : ℕ}
    (h : ((m : ℕ) : 𝒪̄ᵖᵍᵥ) - ((n : ℕ) : 𝒪̄ᵖᵍᵥ) ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ) :
    m ≡ n [MOD p] := by
  rcases le_total n m with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hk : ((k : ℕ) : 𝒪̄ᵖᵍᵥ) ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
      have h2 : ((n + k : ℕ) : 𝒪̄ᵖᵍᵥ) - ((n : ℕ) : 𝒪̄ᵖᵍᵥ) = ((k : ℕ) : 𝒪̄ᵖᵍᵥ) := by
        push_cast; ring
      rwa [h2] at h
    have hd : p ∣ (n + k) - n := by
      simpa using dvd_of_natCast_mem_maximalIdeal k hk
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right n k)).mpr hd).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hk : ((k : ℕ) : 𝒪̄ᵖᵍᵥ) ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
      have h2 : -(((m : ℕ) : 𝒪̄ᵖᵍᵥ) - ((m + k : ℕ) : 𝒪̄ᵖᵍᵥ)) = ((k : ℕ) : 𝒪̄ᵖᵍᵥ) := by
        push_cast; ring
      rw [← h2]
      exact Submodule.neg_mem _ h
    have hd : p ∣ (m + k) - m := by
      simpa using dvd_of_natCast_mem_maximalIdeal k hk
    exact (Nat.modEq_iff_dvd' (Nat.le_add_right m k)).mpr hd

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **Raynaud's dichotomy for the inertia character of an order-`p`
point** (PROVEN 2026-07-25, sorry-free — was the CLASSIFICATION half of
the `μ`-type node): for a geometric point `φ` of exact convolution order
`p` whose cyclic group `⟨φ⟩ ≅ ℤ/p` is inertia-stable (`hstab`), the
character `χ_φ : I_v → (ℤ/p)ˣ`, `σ ↦ m(σ)` with `σ • φ = φ^{m(σ)}`, is
EITHER trivial OR the mod-`p` cyclotomic character — as a CHARACTER,
i.e. one of the two alternatives holds simultaneously for all `σ`.

Classically this is Raynaud, *Schémas en groupes de type `(p, …, p)`*,
Bull. SMF 102 (1974), 3.3.6/3.4.3, or Oort–Tate (*Group schemes of prime
order*, Ann. Sci. ÉNS 1970) — over a base of absolute ramification
`e = 1 < p − 1` the schematic closure of `⟨φ⟩` is `G_{a,b}` with
`ab = w_p`, so `v(a) ∈ {0, 1}` and the two cases are `ℤ/p` and `μ_p`, each
up to an unramified twist invisible to inertia.

**The proof given here needs NEITHER the Oort–Tate classification nor the
schematic closure.** It proves the RIGHT alternative outright, by a
valuation computation on the displacement `d = c − 1` of the integral
point `c : G → 𝒪̄ᵥ` attached to `φ`, inside the convolution ring of
`G →ₗ[𝒪ᵥ] 𝒪̄ᵥ` — the same ring in which
`eq_convOne_of_convPow_prime_eq_one` already works. Write
`𝔞 = (d(G))` for the displacement ideal. Then:

1. `𝔞 ⊆ 𝔪` — CONNECTEDNESS, via `point_sub_counit_mem_maximalIdeal`.
2. `𝔞 = (y)` is PRINCIPAL, generated by a single value `y = d(g₀)`,
   because `𝒪̄ᵥ` is a valuation ring (`valuationRing_integralClosure`)
   and `G` is module-finite (`exists_span_range_eq_span_singleton`);
   and `y ≠ 0` because `φ ≠ 1`.
3. `y^{p−1} ∣ p` — **the Raynaud bound `v(a) ≤ e`, made elementary**.
   The binomial expansion of `c^p = 1` gives
   `p·d(g₀) ∈ (p)·𝔞² + 𝔞^p` (`nsmul_sub_one_mem_of_convPow_prime_eq_one`,
   which is `eq_convOne_of_convPow_prime_eq_one`'s expansion with the top
   term kept separate); with `𝔞 = (y)` this reads
   `p·y = a·p·y² + b·y^p`, i.e. `p(1 − ay) = b·y^{p−1}` after cancelling
   `y` in the domain, and `1 − ay` is a unit because `y ∈ 𝔪`.
4. `p ∣ y^{p−1}` — **the sharpness, i.e. `v(a) ≥ e`**, which is the half
   that genuinely needs the group structure. Take the NORM of the
   displacement over the cyclic group of points,
   `P = ∏_{u ∈ (ℤ/p)ˣ} d_u(g₀)` with `d_k = c^k − 1`. Inertia PERMUTES
   the factors: `σ • d_k(g₀) = d_{km}(g₀)` when `σ • φ = φ^m` (the action
   is by an `𝒪ᵥ`-algebra map, so it commutes with convolution powers —
   `comp_convPow`), and `k ↦ km` is a bijection of `(ℤ/p)ˣ`. So `P` is
   EXACTLY inertia-invariant, and the PROVEN absolute-unramifiedness leaf
   `mem_span_natCast_of_inertia_invariant` puts it in `(p)`. Each factor
   is `y·(unit)` — `d_k(g₀) = k·y + O(y²)` with `k` invertible mod `p` —
   so `P = y^{p−1}·(unit)`.
5. Hence `y^{p−1} ∼ p ∼ (ζ_p − 1)^{p−1}` (`associated_sub_one_pow_natCast`,
   the cyclotomic factorisation of `p`), and cancelling the `(p−1)`-st
   power in the valuation ring (`associated_of_associated_pow`) gives
   `y ∼ ζ_p − 1`: **the displacement ideal is exactly the `μ_p`-ideal.**
6. Endgame. Write `y = (ζ_p − 1)·w⁻¹` with `w` a unit. For `σ ∈ I_v`,
   `σ • y ≡ m·y` and `σ(ζ_p − 1) ≡ n·(ζ_p − 1)` modulo the respective
   squares (`convPow_sub_one_sub_nsmul_mem` and the binomial
   `one_add_pow_sub_one_sub_nsmul_dvd`, with `σ ζ_p = ζ_p^n` supplied by
   `galois_apply_pow_eq_pow_of_cyclotomicCharacter`). Cancelling
   `ζ_p − 1` gives `n·σ(w) ≡ m·w mod 𝔪`; inertia acts TRIVIALLY on the
   residue field — that is the DEFINITION of `localInertiaGroup`, an
   `AddSubgroup.inertia` — so `σ(w) ≡ w` and `(m − n)·w ∈ 𝔪`, whence
   `m ≡ n mod p` because `w` is a unit and `𝔪 ∩ ℤ = pℤ`.

Two hypotheses are NOT used and are underscore-prefixed so the fact is
mechanically visible:

* `_hpodd` — `p` ODD is not needed. Step 3 works for every prime, and
  `mem_span_natCast_of_inertia_invariant` does not use oddness either
  (its own docstring says so). At `p = 2` the statement is true but
  empty, `(ℤ/2)ˣ` being trivial.
* `_hcomul₀` — the group-law closure of the connected component is not
  needed; only `hφe`/`he₀`/`hε₀`/`hprim₀` are, through
  `point_sub_counit_mem_maximalIdeal`.

**Note for the consumer**: contrary to the previous statement of this
leaf, this proof DOES consume the connectedness package (step 1) and
returns `Or.inr` — the trivial alternative is refuted along the way.
`not_inertia_character_trivial_of_connected`, which the consumer
`exists_muType_coordinate` applies to `resolve_left` this disjunction,
is therefore now logically redundant there; it is left untouched (it is
another owner's declaration and the assembly still typechecks). -/
theorem inertia_character_trivial_or_cyclotomic
    (_hpodd : Odd p)
    (G : Type) [CommRing G]
    [HopfAlgebra 𝒪ᵖᵍᵥ G] [Module.Flat 𝒪ᵖᵍᵥ G] [Module.Finite 𝒪ᵖᵍᵥ G]
    (e₀ : G) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝒪ᵖᵍᵥ) e₀ = (1 : 𝒪ᵖᵍᵥ))
    (hprim₀ : ∀ x : G, IsIdempotentElem x → x * e₀ = 0 ∨ x * e₀ = e₀)
    (_hcomul₀ : Coalgebra.comul (R := 𝒪ᵖᵍᵥ) e₀ *
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
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  -- ### the integral point of the model and its convolution displacement
  set χ : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ :=
    (AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm φ 
  have hint : ∀ a : G, χ a ∈ integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ := fun a =>
    (Algebra.IsIntegral.isIntegral (R := 𝒪ᵖᵍᵥ) a).map χ
  set χI : G →ₐ[𝒪ᵖᵍᵥ] 𝒪̄ᵖᵍᵥ :=
    AlgHom.codRestrict χ (integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ) hint 
  set ι : 𝒪̄ᵖᵍᵥ →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ :=
    { algebraMap 𝒪̄ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ with commutes' := fun _ => rfl } 
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext h
  have hιχ : ι.comp χI = χ := AlgHom.ext fun _ => rfl
  set c : WithConv (G →ₗ[𝒪ᵖᵍᵥ] 𝒪̄ᵖᵍᵥ) := toConv χI.toLinearMap with hc
  -- `φ^p = 1`, transported to the integral points
  have hχp : (toConv χ) ^ p = (1 : WithConv (G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)) := by
    apply WithConv.ofConv_injective
    have h := liftEquiv_symm_vendored_pow (R := 𝒪ᵖᵍᵥ) (S := ℚᵖᵍᵥ) (H := G)
      (L := ℚᵖᵍᵥᵃˡᵍ) φ p
    rw [hord, vendored_one_eq_convOne, liftEquiv_symm_convOne] at h
    exact h.symm
  have hχIp : (toConv χI) ^ p = (1 : WithConv (G →ₐ[𝒪ᵖᵍᵥ] 𝒪̄ᵖᵍᵥ)) := by
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
  -- the values of the convolution powers, read on the algebra points
  have hcE : ∀ (k : ℕ) (g : G), (c ^ k).ofConv g = ((toConv χI) ^ k).ofConv g := by
    intro k g
    have h := AlgHom.toLinearMap_convPow (toConv χI) k
    have h2 := congrArg (fun z : WithConv (G →ₗ[𝒪ᵖᵍᵥ] 𝒪̄ᵖᵍᵥ) => z.ofConv g) h
    simpa using h2.symm
  -- ### connectedness: the displacement lands in the maximal ideal
  have hred : ∀ g : G, φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
      algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g) ∈
      Submodule.map (Algebra.linearMap 𝒪̄ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ)
        (IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ) := fun g =>
    point_sub_counit_mem_maximalIdeal
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime))
      G e₀ he₀ hε₀ hprim₀ φ hφe g
  have hdval : ∀ g : G, ι ((c - 1).ofConv g) =
      φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] g) -
        algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) g) := by
    intro g
    rw [WithConv.ofConv_sub, LinearMap.sub_apply, map_sub]
    congr 1
  have hmax : ∀ g : G, (c - 1).ofConv g ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
    intro g
    obtain ⟨mm, hmm, hmeq⟩ := hred g
    have hgm : ι ((c - 1).ofConv g) = ι mm := by rw [hdval g, ← hmeq]; rfl
    rwa [hιinj hgm]
  -- ### the displacement ideal is principal, generated by one value
  obtain ⟨g₀, h𝔞⟩ := exists_span_range_eq_span_singleton (c - 1).ofConv
  set y : 𝒪̄ᵖᵍᵥ := (c - 1).ofConv g₀ with hy
  have hdmem : ∀ g : G, (c - 1).ofConv g ∈ Ideal.span {y} := by
    intro g
    rw [← h𝔞]
    exact Ideal.subset_span ⟨g, rfl⟩
  have hymax : y ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := hmax g₀
  -- `y ≠ 0`, since `φ ≠ 1`
  have hy0 : y ≠ 0 := by
    intro h0
    apply hφ1
    have hd0 : ∀ g : G, (c - 1).ofConv g = 0 := by
      intro g
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (hdmem g)
      rw [← hz, h0, mul_zero]
    have hc1 : c = 1 := by
      apply WithConv.ofConv_injective
      refine LinearMap.ext fun g => ?_
      have h := hd0 g
      rw [WithConv.ofConv_sub, LinearMap.sub_apply, sub_eq_zero] at h
      exact h
    apply (AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm.injective
    rw [vendored_one_eq_convOne, liftEquiv_symm_convOne]
    refine AlgHom.ext fun a => ?_
    have h : χI a = (1 : WithConv (G →ₗ[𝒪ᵖᵍᵥ] 𝒪̄ᵖᵍᵥ)).ofConv a := by
      have h0' := congrArg (fun f : WithConv (G →ₗ[𝒪ᵖᵍᵥ] 𝒪̄ᵖᵍᵥ) => f.ofConv a) hc1
      rw [hc] at h0'
      exact h0'
    calc ((AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm φ) a
        = ι (χI a) := rfl
      _ = ι (algebraMap 𝒪ᵖᵍᵥ 𝒪̄ᵖᵍᵥ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) a)) := by
          rw [h, LinearMap.convOne_apply]
      _ = algebraMap 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ (Coalgebra.counit (R := 𝒪ᵖᵍᵥ) a) := ι.commutes _
      _ = (1 : WithConv (G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ)).ofConv a := (AlgHom.convOne_apply a).symm
  -- ### the values of the convolution powers at the chosen generator
  set D : ℕ → 𝒪̄ᵖᵍᵥ := fun k => (c ^ k - 1).ofConv g₀ with hD
  have hD1 : D 1 = y := by simp only [hD, pow_one, hy]
  have hDmod : ∀ j k : ℕ, j ≡ k [MOD p] → D j = D k := by
    intro j k h
    simp only [hD]
    rw [pow_eq_pow_of_natModEq hcp h]
  have hDy : ∀ k : ℕ, ∃ s : 𝒪̄ᵖᵍᵥ, D k = (k : 𝒪̄ᵖᵍᵥ) * y + s * y ^ 2 := by
    intro k
    have h := convPow_sub_one_sub_nsmul_mem c hdmem k g₀
    rw [Ideal.span_singleton_pow] at h
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h
    refine ⟨s, ?_⟩
    have hexp : ((c ^ k - 1) - (k : ℕ) • (c - 1)).ofConv g₀ = D k - (k : 𝒪̄ᵖᵍᵥ) * y := by
      simp only [hD, hy]
      rw [WithConv.ofConv_sub, LinearMap.sub_apply, WithConv.ofConv_smul,
        LinearMap.smul_apply, nsmul_eq_mul]
    rw [hexp] at hs
    linear_combination -hs
  have hDunit : ∀ k : ℕ, ¬ p ∣ k → ∃ w : 𝒪̄ᵖᵍᵥˣ, D k = y * w := by
    intro k hk
    obtain ⟨s, hs⟩ := hDy k
    have hku : IsUnit ((k : ℕ) : 𝒪̄ᵖᵍᵥ) := by
      by_contra hu
      exact hk (dvd_of_natCast_mem_maximalIdeal k ((IsLocalRing.mem_maximalIdeal _).mpr hu))
    have hsum : IsUnit ((k : 𝒪̄ᵖᵍᵥ) + s * y) :=
      isUnit_add_mem_maximalIdeal hku (Ideal.mul_mem_left _ _ hymax)
    refine ⟨hsum.unit, ?_⟩
    rw [IsUnit.unit_spec, hs]
    ring
  -- ### the Raynaud bound: `y^(p-1)` divides `p`
  have hbound : y ^ (p - 1) ∣ ((p : ℕ) : 𝒪̄ᵖᵍᵥ) := by
    have h := nsmul_sub_one_mem_of_convPow_prime_eq_one hp.out c hcp hdmem g₀
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_mul_span_singleton] at h
    obtain ⟨u₁, hu₁, u₂, hu₂, hsum⟩ := Submodule.mem_sup.mp h
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hu₁
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hu₂
    have hkey : ((p : ℕ) : 𝒪̄ᵖᵍᵥ) * y = a * (((p : ℕ) : 𝒪̄ᵖᵍᵥ) * y ^ 2) + b * y ^ p := by
      rw [ha, hb, hsum, nsmul_eq_mul]
    have hunit : IsUnit (1 - a * y) := by
      have h1 : IsUnit (1 : 𝒪̄ᵖᵍᵥ) := isUnit_one
      have h2 : -(a * y) ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ :=
        Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hymax)
      have := isUnit_add_mem_maximalIdeal h1 h2
      simpa [sub_eq_add_neg] using this
    have hcancel : ((p : ℕ) : 𝒪̄ᵖᵍᵥ) * (1 - a * y) * y = b * y ^ (p - 1) * y := by
      have hpp : y ^ p = y ^ (p - 1) * y := by
        rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
      rw [hpp] at hkey
      linear_combination hkey
    have hpe : ((p : ℕ) : 𝒪̄ᵖᵍᵥ) * (1 - a * y) = b * y ^ (p - 1) :=
      mul_right_cancel₀ hy0 hcancel
    obtain ⟨uu, huu⟩ := hunit
    refine ⟨b * ((uu⁻¹ : 𝒪̄ᵖᵍᵥˣ) : 𝒪̄ᵖᵍᵥ), ?_⟩
    have h1 : ((p : ℕ) : 𝒪̄ᵖᵍᵥ) * (uu : 𝒪̄ᵖᵍᵥ) = b * y ^ (p - 1) := by
      rw [huu]; exact hpe
    calc ((p : ℕ) : 𝒪̄ᵖᵍᵥ)
        = ((p : ℕ) : 𝒪̄ᵖᵍᵥ) * (uu : 𝒪̄ᵖᵍᵥ) * ((uu⁻¹ : 𝒪̄ᵖᵍᵥˣ) : 𝒪̄ᵖᵍᵥ) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = y ^ (p - 1) * (b * ((uu⁻¹ : 𝒪̄ᵖᵍᵥˣ) : 𝒪̄ᵖᵍᵥ)) := by rw [h1]; ring
  -- ### the Galois transport of the stability hypothesis
  set ρ : Field.absoluteGaloisGroup ℚᵖᵍᵥ → (𝒪̄ᵖᵍᵥ →ₐ[𝒪ᵖᵍᵥ] 𝒪̄ᵖᵍᵥ) :=
    fun τ => MulSemiringAction.toAlgHom 𝒪ᵖᵍᵥ 𝒪̄ᵖᵍᵥ τ 
  have hρapp : ∀ (τ : Field.absoluteGaloisGroup ℚᵖᵍᵥ) (x : 𝒪̄ᵖᵍᵥ), ρ τ x = τ • x :=
    fun _ _ => rfl
  have hιρ : ∀ (τ : Field.absoluteGaloisGroup ℚᵖᵍᵥ) (x : 𝒪̄ᵖᵍᵥ), ι (ρ τ x) = τ (ι x) :=
    fun _ _ => rfl
  have hpow : ∀ (τ : Field.absoluteGaloisGroup ℚᵖᵍᵥ) (mτ : ℕ), τ • φ = φ ^ mτ →
      (ρ τ).comp χI = ((toConv χI) ^ mτ).ofConv := by
    intro τ mτ hmτ
    have h3 := congrArg (AlgHom.liftEquiv 𝒪ᵖᵍᵥ ℚᵖᵍᵥ G ℚᵖᵍᵥᵃˡᵍ).symm hmτ
    rw [show τ • φ =
        (τ.toAlgHom : ℚᵖᵍᵥᵃˡᵍ →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ).comp φ from AlgHom.ext fun _ => rfl,
      liftEquiv_symm_comp, liftEquiv_symm_vendored_pow] at h3
    have h4 := comp_convPow ι (toConv χI) mτ
    rw [WithConv.ofConv_toConv, hιχ] at h4
    refine AlgHom.ext fun a => hιinj ?_
    have h5 := congrArg (fun f : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ => f a) h3
    have h6 := congrArg (fun f : G →ₐ[𝒪ᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ => f a) h4
    simp only [AlgHom.comp_apply] at h5 h6
    rw [AlgHom.comp_apply, hιρ, h6, ← h5]
    rfl
  have hpowk : ∀ (τ : Field.absoluteGaloisGroup ℚᵖᵍᵥ) (mτ : ℕ), τ • φ = φ ^ mτ →
      ∀ k : ℕ, (ρ τ).comp (((toConv χI) ^ k).ofConv) = ((toConv χI) ^ (k * mτ)).ofConv := by
    intro τ mτ hmτ k
    have h := comp_convPow (ρ τ) (toConv χI) k
    rw [WithConv.ofConv_toConv, hpow τ mτ hmτ, WithConv.toConv_ofConv, ← pow_mul] at h
    rw [h, mul_comm]
  have hDsmul : ∀ (τ : Field.absoluteGaloisGroup ℚᵖᵍᵥ) (mτ : ℕ), τ • φ = φ ^ mτ →
      ∀ k : ℕ, τ • (D k) = D (k * mτ) := by
    intro τ mτ hmτ k
    have hval : ∀ j : ℕ, D j = ((toConv χI) ^ j).ofConv g₀ -
        (1 : WithConv (G →ₗ[𝒪ᵖᵍᵥ] 𝒪̄ᵖᵍᵥ)).ofConv g₀ := by
      intro j
      simp only [hD]
      rw [WithConv.ofConv_sub, LinearMap.sub_apply, hcE j g₀]
    rw [hval, hval, ← hρapp, map_sub]
    congr 1
    · have h := hpowk τ mτ hmτ k
      have h2 := congrArg (fun f : G →ₐ[𝒪ᵖᵍᵥ] 𝒪̄ᵖᵍᵥ => f g₀) h
      simpa using h2
    · rw [LinearMap.convOne_apply]
      exact (ρ τ).commutes _
  -- ### the norm of the displacement over the cyclic group of points
  have hcastval : ∀ x : ZMod p, ((x.val : ℕ) : ZMod p) = x := by
    intro x
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hval_ne : ∀ u : (ZMod p)ˣ, ¬ p ∣ ((u : ZMod p).val) := by
    intro u hdvd
    apply u.ne_zero
    have h1 : (((u : ZMod p).val : ℕ) : ZMod p) = 0 := by
      obtain ⟨j, hj⟩ := hdvd
      rw [hj]
      push_cast
      simp
    rwa [hcastval] at h1
  set P : 𝒪̄ᵖᵍᵥ := ∏ u : (ZMod p)ˣ, D ((u : ZMod p).val) with hP
  obtain ⟨w, hw⟩ : ∃ w : 𝒪̄ᵖᵍᵥˣ, P = y ^ (p - 1) * w := by
    choose w hw using fun u : (ZMod p)ˣ => hDunit ((u : ZMod p).val) (hval_ne u)
    refine ⟨∏ u : (ZMod p)ˣ, w u, ?_⟩
    rw [hP, Finset.prod_congr rfl (fun u _ => hw u), Finset.prod_mul_distrib,
      Finset.prod_const, Units.coe_prod]
    congr 1
    rw [Finset.card_univ, ZMod.card_units_eq_totient p, Nat.totient_prime hp.out]
  have hPmem : P ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
    rw [hw]
    refine Ideal.mul_mem_right _ _ ?_
    have hsplit : y ^ (p - 1) = y ^ (p - 1 - 1) * y := by
      rw [← pow_succ, Nat.sub_add_cancel (by have := hp.out.two_le; omega : 1 ≤ p - 1)]
    rw [hsplit]
    exact Ideal.mul_mem_left _ _ hymax
  have hPinv : ∀ τ ∈ localInertiaGroup
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : p.Prime)),
      τ • P = P := by
    intro τ hτ
    obtain ⟨mτ, hmτ⟩ := hstab τ hτ
    have hmτ0 : ¬ p ∣ mτ := by
      intro hdvd
      apply hφ1
      obtain ⟨j, rfl⟩ := hdvd
      have h1 : φ ^ (p * j) = 1 := by rw [pow_mul, hord, one_pow]
      rw [h1] at hmτ
      have := congrArg (fun z => τ⁻¹ • z) hmτ
      simpa [inv_smul_smul] using this
    have hmu : IsUnit ((mτ : ℕ) : ZMod p) := by
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hmτ0)
    set mhat : (ZMod p)ˣ := hmu.unit with hmhat
    have hstep : ∀ u : (ZMod p)ˣ,
        τ • D ((u : ZMod p).val) = D (((u * mhat : (ZMod p)ˣ) : ZMod p).val) := by
      intro u
      rw [hDsmul τ mτ hmτ]
      refine hDmod _ _ ?_
      have hc1 : (((u : ZMod p).val * mτ : ℕ) : ZMod p)
          = ((((u * mhat : (ZMod p)ˣ) : ZMod p).val : ℕ) : ZMod p) := by
        rw [Nat.cast_mul, hcastval, hcastval, Units.val_mul, hmhat, IsUnit.unit_spec]
      exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hc1)
    calc τ • P = ∏ u : (ZMod p)ˣ, τ • D ((u : ZMod p).val) := by
          rw [hP, ← hρapp, map_prod]
          exact Finset.prod_congr rfl fun u _ => (hρapp τ _).symm
      _ = ∏ u : (ZMod p)ˣ, D (((u * mhat : (ZMod p)ˣ) : ZMod p).val) :=
          Finset.prod_congr rfl fun u _ => hstep u
      _ = P := by
          rw [hP]
          exact Equiv.prod_comp (Equiv.mulRight mhat) (fun u : (ZMod p)ˣ => D ((u : ZMod p).val))
  have hPdvd : ((p : ℕ) : 𝒪̄ᵖᵍᵥ) ∣ P := by
    have h := mem_span_natCast_of_inertia_invariant P hPmem ?_
    · exact Ideal.mem_span_singleton.mp h
    · intro σ hσ
      have := hPinv σ hσ
      have h2 : ι (ρ σ P) = ι P := by rw [hρapp, this]
      rw [hιρ] at h2
      exact h2
  have hpy : ((p : ℕ) : 𝒪̄ᵖᵍᵥ) ∣ y ^ (p - 1) := by
    obtain ⟨z, hz⟩ := hPdvd
    refine ⟨z * ((w⁻¹ : 𝒪̄ᵖᵍᵥˣ) : 𝒪̄ᵖᵍᵥ), ?_⟩
    have h1 : y ^ (p - 1) = P * ((w⁻¹ : 𝒪̄ᵖᵍᵥˣ) : 𝒪̄ᵖᵍᵥ) := by
      rw [hw, mul_assoc, Units.mul_inv, mul_one]
    rw [h1, hz]; ring
  -- ### the primitive `p`-th root of unity, as an integral element
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hζfield : IsPrimitiveRoot
      (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ) p :=
    hμ.map_of_injective (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ)).injective
  have hζint : AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ ∈
      integralClosure 𝒪ᵖᵍᵥ ℚᵖᵍᵥᵃˡᵍ := by
    refine ⟨Polynomial.X ^ p - 1, ?_, ?_⟩
    · simpa using Polynomial.monic_X_pow_sub_C (1 : 𝒪ᵖᵍᵥ) hp.out.ne_zero
    · simp [hζfield.pow_eq_one]
  set ζ : 𝒪̄ᵖᵍᵥ := ⟨AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ, hζint⟩ 
  have hζcoe : ι ζ = AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ := rfl
  have hζpow : ζ ^ p = 1 := by
    apply hιinj
    rw [map_pow, hζcoe, map_one]
    exact hζfield.pow_eq_one
  have hζ1 : ζ ≠ 1 := by
    intro h
    have := congrArg ι h
    rw [hζcoe, map_one] at this
    exact hζfield.ne_one hp.out.one_lt this
  have hζ : IsPrimitiveRoot ζ p := isPrimitiveRoot_of_prime_pow_eq_one hp.out hζpow hζ1
  -- ### `y` and `ζ - 1` are associated
  have hyp1 : Associated (y ^ (p - 1)) ((p : ℕ) : 𝒪̄ᵖᵍᵥ) := associated_of_dvd_dvd hbound hpy
  have hζassoc : Associated ((ζ - 1) ^ (p - 1)) ((p : ℕ) : 𝒪̄ᵖᵍᵥ) :=
    associated_sub_one_pow_natCast hζ
  have hyζ : Associated y (ζ - 1) :=
    associated_of_associated_pow hp1 (hyp1.trans hζassoc.symm)
  obtain ⟨wu, hwu⟩ := hyζ
  -- ### the endgame: the two characters agree modulo the maximal ideal
  refine Or.inr ?_
  intro σ hσ m n hm hn
  -- the cyclotomic side
  have hσζ : σ • ζ = ζ ^ n := by
    apply hιinj
    have h := galois_apply_pow_eq_pow_of_cyclotomicCharacter σ n hn
      (AlgebraicClosure.map (algebraMap ℚ ℚᵖᵍᵥ) μ) hζfield.pow_eq_one
    calc ι (σ • ζ) = σ (ι ζ) := by rw [← hρapp, hιρ]
      _ = (ι ζ) ^ n := by rw [hζcoe]; exact h
      _ = ι (ζ ^ n) := (map_pow ι ζ n).symm
  obtain ⟨aa, haa⟩ : ∃ aa : 𝒪̄ᵖᵍᵥ,
      σ • (ζ - 1) = (n : 𝒪̄ᵖᵍᵥ) * (ζ - 1) + aa * (ζ - 1) ^ 2 := by
    obtain ⟨t, ht⟩ := one_add_pow_sub_one_sub_nsmul_dvd (ζ - 1) n
    refine ⟨t, ?_⟩
    have h1 : σ • (ζ - 1) = ζ ^ n - 1 := by
      rw [smul_sub, hσζ, smul_one]
    have h2 : (1 : 𝒪̄ᵖᵍᵥ) + (ζ - 1) = ζ := by ring
    rw [h2, nsmul_eq_mul] at ht
    rw [h1]
    linear_combination ht
  obtain ⟨bb, hbb⟩ : ∃ bb : 𝒪̄ᵖᵍᵥ,
      σ • y = (m : 𝒪̄ᵖᵍᵥ) * y + bb * y ^ 2 := by
    obtain ⟨s, hs⟩ := hDy m
    refine ⟨s, ?_⟩
    have h1 : σ • y = D m := by
      rw [← hD1, hDsmul σ m hm 1, one_mul]
    rw [h1, hs]
  -- combine the two expansions through `y * wu = ζ - 1`
  have hcomb : (m : 𝒪̄ᵖᵍᵥ) * (σ • (wu : 𝒪̄ᵖᵍᵥ)) - (n : 𝒪̄ᵖᵍᵥ) * wu ∈
      IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
    have hsmulmul : σ • (y * (wu : 𝒪̄ᵖᵍᵥ)) = (σ • y) * (σ • (wu : 𝒪̄ᵖᵍᵥ)) := by
      rw [← hρapp, ← hρapp, ← hρapp, map_mul]
    have hmain : y * ((m : 𝒪̄ᵖᵍᵥ) * (σ • (wu : 𝒪̄ᵖᵍᵥ)) - (n : 𝒪̄ᵖᵍᵥ) * wu) =
        y * (-(bb * y * (σ • (wu : 𝒪̄ᵖᵍᵥ))) + aa * y * (wu : 𝒪̄ᵖᵍᵥ) ^ 2) := by
      have h1 : σ • (ζ - 1) = (σ • y) * (σ • (wu : 𝒪̄ᵖᵍᵥ)) := by
        rw [← hwu, hsmulmul]
      rw [haa, hbb, ← hwu] at h1
      linear_combination -h1
    have hz := mul_left_cancel₀ hy0 hmain
    rw [hz]
    refine Submodule.add_mem _ (Submodule.neg_mem _ ?_) ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hymax)
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hymax)
  have hwinv : (σ • (wu : 𝒪̄ᵖᵍᵥ)) - (wu : 𝒪̄ᵖᵍᵥ) ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
    have h := AddSubgroup.mem_inertia.mp hσ (wu : 𝒪̄ᵖᵍᵥ)
    rwa [Submodule.mem_toAddSubgroup] at h
  have hfin : ((m : ℕ) : 𝒪̄ᵖᵍᵥ) - ((n : ℕ) : 𝒪̄ᵖᵍᵥ) ∈ IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
    have h1 : (m : 𝒪̄ᵖᵍᵥ) * ((σ • (wu : 𝒪̄ᵖᵍᵥ)) - (wu : 𝒪̄ᵖᵍᵥ)) ∈
        IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := Ideal.mul_mem_left _ _ hwinv
    have h2 : ((m : 𝒪̄ᵖᵍᵥ) - (n : 𝒪̄ᵖᵍᵥ)) * (wu : 𝒪̄ᵖᵍᵥ) ∈
        IsLocalRing.maximalIdeal 𝒪̄ᵖᵍᵥ := by
      have h3 := Submodule.sub_mem _ hcomb h1
      have h4 : (m : 𝒪̄ᵖᵍᵥ) * (σ • (wu : 𝒪̄ᵖᵍᵥ)) - (n : 𝒪̄ᵖᵍᵥ) * wu -
          (m : 𝒪̄ᵖᵍᵥ) * ((σ • (wu : 𝒪̄ᵖᵍᵥ)) - (wu : 𝒪̄ᵖᵍᵥ)) =
          ((m : 𝒪̄ᵖᵍᵥ) - (n : 𝒪̄ᵖᵍᵥ)) * (wu : 𝒪̄ᵖᵍᵥ) := by ring
      rwa [h4] at h3
    have h5 := Ideal.mul_mem_right ((wu⁻¹ : 𝒪̄ᵖᵍᵥˣ) : 𝒪̄ᵖᵍᵥ) _ h2
    have h6 : ((m : 𝒪̄ᵖᵍᵥ) - (n : 𝒪̄ᵖᵍᵥ)) * (wu : 𝒪̄ᵖᵍᵥ) *
        ((wu⁻¹ : 𝒪̄ᵖᵍᵥˣ) : 𝒪̄ᵖᵍᵥ) = (m : 𝒪̄ᵖᵍᵥ) - (n : 𝒪̄ᵖᵍᵥ) := by
      rw [mul_assoc, Units.mul_inv, mul_one]
    rwa [h6] at h5
  exact natModEq_of_sub_mem_maximalIdeal hfin

end RaynaudDichotomy

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
the same day over the two leaves
`inertia_character_trivial_or_cyclotomic` and
`eq_one_of_inertia_invariant_of_reduction_counit`, which are now the
shared `μ`-type node's only remaining inputs): under the hypotheses of
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
  `e = 1 < p − 1`: `χ_φ` is either trivial or `χ_cyc`, as characters;
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
