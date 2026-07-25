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

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- **The Oort–Tate `μ_p`-coordinate** (sorry node, 2026-07-24 — the
CLASSIFICATION half of the shared `μ`-type node below, isolated as its
only remaining input): under the hypotheses of
`connected_cyclic_point_smul_eq_conv_pow_cyclotomicCharacter` and with
`φ ≠ 1`, the Hopf order `G` carries an element `x` on which `φ` takes
a NONTRIVIAL `p`-th root of unity as value, and on which the whole
convolution-cyclic group `⟨φ⟩` is read off by the corresponding power:
`(φ^k)(1 ⊗ x) = (φ(1 ⊗ x))^k` for every `k`. In other words `x` is a
`μ_p`-coordinate: it pulls the group `⟨φ⟩ ≅ ℤ/p` of geometric points
back to the group `μ_p ⊆ ℚᵥᵃˡᵍ` compatibly with the group laws.

Intended proof (Oort–Tate, *Group schemes of prime order*, Ann. Sci.
ÉNS 1970; Raynaud, *Schémas en groupes de type `(p, …, p)`*, Bull.
SMF 102 (1974), 3.3.6/3.4.3; Tate, "Finite flat group schemes", in
Cornell–Silverman–Stevens): `φ ≠ 1` and `hord` give `φ` exact
convolution order `p`, so `hstab` makes the cyclic subgroup
`⟨φ⟩ ≅ ℤ/p` of generic-fibre points stable under local inertia, hence
Galois-stable over the completed maximal unramified extension
`ℚ_p^nr` whose absolute Galois group IS the inertia group. Its
schematic closure `C` in the model is then a finite flat closed
subgroup scheme of order `p` killed by `p` over `𝒪^nr = W(𝔽̄_p)`, which
is absolutely unramified (`e = 1 < p − 1`, `p` odd by `hpodd`). `hφe`
together with the group-law absorption `hcomul₀` and the primitivity
`hprim₀` of the connected counit idempotent place every convolution
power of `φ` in the connected component, so `C` lands in the local
corner `Spec (G·e₀)` and is CONNECTED; the Oort–Tate classification at
`e = 1` then leaves only `C ≅ μ_p` (the étale option `ℤ/p` is excluded
by connectedness of the nontrivial `C`). The coordinate ring of `μ_p`
is `𝒪^nr[T]/(T^p − 1)` with `ΔT = T ⊗ T`, and a preimage `x ∈ G` of
`T` under `G → 𝒪_C` has all three properties: `φ(1 ⊗ x)` is the value
of `φ` at the group-like `T`, hence a `p`-th root of unity, nontrivial
because `φ ≠ 1` generates `C`; and the convolution powers of `φ` all
factor through `𝒪_C`, where `ΔT = T ⊗ T` turns convolution into
multiplication of values, giving `(φ^k)(1 ⊗ x) = (φ(1 ⊗ x))^k`.
Soundness: the hypothesis set is inhabited (the nontrivial points of
`μ_p` over `ℤ_p`, with `e₀` its connected counit idempotent and
`x = T`), and the conclusion holds for every inhabitant by the
classification cited; `hstab` is NOT redundant — for the `p`-torsion
of a supersingular elliptic curve over `ℤ_p` tame inertia acts through
the level-`2` fundamental characters, no line is stable, and no such
coordinate exists. -/
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
    ∃ x : G,
      (φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] x)) ^ p = 1 ∧
      φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] x) ≠ 1 ∧
      ∀ k : ℕ, (φ ^ k) ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] x) =
        (φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] x)) ^ k :=
  sorry

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
of `⟨φ⟩`, the only remaining input — supplies a coordinate `x ∈ G` on
which `φ` takes a nontrivial `p`-th root of unity `ζ` as value and on
which convolution powers become powers of `ζ`. Evaluating the
stability relation `σ • φ = φ^m` of `hstab` at `x` gives `σ ζ = ζ^m`,
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
    obtain ⟨x, hxp, hx1, hxpow⟩ :=
      exists_muType_coordinate hpodd G e₀ he₀ hε₀ hprim₀ hcomul₀ φ hφe
        hord hstab hφ1
    -- the coordinate value is a primitive `p`-th root of unity
    have hprimζ : IsPrimitiveRoot (φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] x)) p :=
      isPrimitiveRoot_of_prime_pow_eq_one hp.out hxp hx1
    -- the inertia-stability relation, read at the coordinate
    have hval : σ (φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] x)) =
        (φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] x)) ^ m := by
      have h := congrArg
        (fun ψ : ℚᵖᵍᵥ ⊗[𝒪ᵖᵍᵥ] G →ₐ[ℚᵖᵍᵥ] ℚᵖᵍᵥᵃˡᵍ =>
          ψ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] x)) hm
      rw [hxpow m] at h
      exact h
    -- and the same value through the cyclotomic character
    have hbridge : σ (φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] x)) =
        (φ ((1 : ℚᵖᵍᵥ) ⊗ₜ[𝒪ᵖᵍᵥ] x)) ^ n :=
      galois_apply_pow_eq_pow_of_cyclotomicCharacter σ n hn _ hxp
    have hmn : m ≡ n [MOD p] :=
      natModEq_of_pow_eq_pow hprimζ (hval.symm.trans hbridge)
    rw [hm]
    exact pow_eq_pow_of_natModEq hord hmn

end CyclotomicNode

end OortTate
