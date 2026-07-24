/-
AdicCompletion/Finite.lean — own work for the Fermat project.

Adic completeness of finite modules over a complete Noetherian local
ring, and its henselian consequences for module-finite algebras: the
maximal-ideal extension is a henselian pair, idempotents lift along
it, and artinian rings with no nontrivial idempotents are local.
These are the commutative-algebra bricks of the connected–étale
decomposition of a finite flat Hopf algebra over `ℤ₃`
(`Fermat.FLT.GroupScheme.ConnectedEtale`), consumed by the
Hopf-package cores of `HardlyRamified/ModThree.lean` and
`HardlyRamified/Threeadic.lean`.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Jacobson.Ideal

@[expose] public section

open IsLocalRing

/-! ### Componentwise membership in `I ^ n • ⊤` of a finite pi module -/

/-- Membership in `I ^ n • ⊤ ⊆ (ι → R)` is detected componentwise
(easy direction: evaluation is linear). -/
theorem Submodule.apply_mem_of_mem_smul_top_pi {R : Type*} [CommRing R]
    {ι : Type*} (J : Ideal R) {x : ι → R}
    (hx : x ∈ J • (⊤ : Submodule R (ι → R))) (i : ι) :
    x i ∈ J • (⊤ : Submodule R R) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb

/-- `Pi.single` maps members of `J • ⊤ ⊆ R` to members of
`J • ⊤ ⊆ (ι → R)`. -/
theorem Submodule.single_mem_smul_top_pi {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι] (J : Ideal R) {c : R}
    (hc : c ∈ J • (⊤ : Submodule R R)) (i : ι) :
    Pi.single i c ∈ J • (⊤ : Submodule R (ι → R)) := by
  refine Submodule.smul_induction_on hc ?_ ?_
  · intro r hr y _
    rw [Pi.single_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro a b ha hb
    rw [Pi.single_add]
    exact Submodule.add_mem _ ha hb

/-- **Precompleteness of finite pi modules**: if `R` is `I`-adically
precomplete then so is `ι → R` for finite `ι` — compatible sequences
converge componentwise. -/
theorem IsPrecomplete.pi {R : Type*} [CommRing R] (I : Ideal R)
    (ι : Type*) [Finite ι] [IsPrecomplete I R] :
    IsPrecomplete I (ι → R) := by
  cases nonempty_fintype ι
  classical
  constructor
  intro f hf
  have hcomp : ∀ i : ι, ∀ {m n : ℕ}, m ≤ n →
      f m i ≡ f n i [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro i m n hmn
    rw [SModEq.sub_mem]
    exact Submodule.apply_mem_of_mem_smul_top_pi _
      ((SModEq.sub_mem).mp (hf hmn)) i
  choose L hL using fun i : ι =>
    IsPrecomplete.prec ‹IsPrecomplete I R› (f := fun n => f n i)
      (fun {m n} hmn => hcomp i hmn)
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem]
  have hsum : f n - L = ∑ i, Pi.single i (f n i - L i) := by
    have h := Finset.univ_sum_single (f n - L)
    simpa using h.symm
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.single_mem_smul_top_pi _
    ((SModEq.sub_mem).mp (hL i n)) i

/-- **Precompleteness of finite modules**: a finite module over an
`I`-adically precomplete ring is `I`-adically precomplete — lift a
compatible sequence along a finite free presentation using the
surjectivity of the induced map on adic completions. -/
theorem IsPrecomplete.of_finite_module {R M : Type*} [CommRing R]
    (I : Ideal R) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI : IsPrecomplete I (Fin n → R) := IsPrecomplete.pi I _
  rw [← AdicCompletion.of_surjective_iff]
  have hcomp : Function.Surjective
      (Submodule.mkQ (I • ⊤) ∘ₗ π) := by
    rw [LinearMap.coe_comp]
    exact (Submodule.mkQ_surjective _).comp hπ
  have hmap : Function.Surjective (AdicCompletion.map I π) :=
    AdicCompletion.map_surjective_of_mkQ_comp_surjective hcomp
  have hof : Function.Surjective (AdicCompletion.of I (Fin n → R)) :=
    AdicCompletion.of_surjective_iff.mpr inferInstance
  intro y
  obtain ⟨x', hx'⟩ := hmap y
  obtain ⟨x, hx⟩ := hof x'
  exact ⟨π x, by rw [← AdicCompletion.map_of, hx, hx']⟩

/-- **Adic completeness of finite modules** over a complete Noetherian
local ring (Hausdorffness is the Krull intersection theorem, already
in mathlib; precompleteness is `IsPrecomplete.of_finite_module`). -/
theorem IsAdicComplete.of_finite_module {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete (maximalIdeal R) M :=
  haveI : IsPrecomplete (maximalIdeal R) M :=
    IsPrecomplete.of_finite_module _
  ⟨⟩

/-- **The henselian pair of a module-finite algebra** over a complete
Noetherian local ring: `(S, 𝔪_R S)` is a henselian pair, by adic
completeness of the finite module `S` transported to the extended
ideal. -/
theorem HenselianRing.of_finite_algebra (R S : Type*) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [Algebra R S] [Module.Finite R S] :
    HenselianRing S ((maximalIdeal R).map (algebraMap R S)) := by
  haveI h1 : IsAdicComplete (maximalIdeal R) S :=
    IsAdicComplete.of_finite_module
  haveI h2 : IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal R) S).mpr h1
  exact IsAdicComplete.henselianRing S _

/-! ### Idempotent lifting along a henselian pair -/

/-- **Idempotents lift along a henselian pair**: apply Hensel's lemma
to `X² − X`, whose derivative `2X − 1` squares to `1` at any
idempotent of the quotient. -/
theorem HenselianRing.exists_isIdempotentElem_mk_eq {S : Type*}
    [CommRing S] [Nontrivial S] {J : Ideal S} [HenselianRing S J]
    {c : S ⧸ J} (hc : IsIdempotentElem c) :
    ∃ y : S, IsIdempotentElem y ∧ Ideal.Quotient.mk J y = c := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hmonic : (Polynomial.X ^ 2 - Polynomial.X : Polynomial S).Monic :=
    Polynomial.monic_X_pow_sub
      (by rw [Polynomial.degree_X]; norm_num)
  have heval : (Polynomial.X ^ 2 - Polynomial.X : Polynomial S).eval z ∈ J := by
    have h0 : Ideal.Quotient.mk J (z ^ 2 - z) = 0 := by
      rw [map_sub, map_pow, sq, hc.eq, sub_self]
    simpa using Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hderiv : IsUnit (Ideal.Quotient.mk J
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial S).derivative.eval z)) := by
    have hd : (Polynomial.X ^ 2 - Polynomial.X : Polynomial S).derivative.eval z =
        2 * z - 1 := by
      simp
      ring
    rw [hd]
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk J (2 * z - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have hz : Ideal.Quotient.mk J (z * z) = Ideal.Quotient.mk J z := hc.eq
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hz
    have : (2 * z - 1) * (2 * z - 1) - 1 = 4 * (z * z - z) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hz
  obtain ⟨a, ha, haz⟩ := HenselianRing.is_henselian
    (Polynomial.X ^ 2 - Polynomial.X) hmonic z heval hderiv
  refine ⟨a, ?_, ?_⟩
  · have h0 : a ^ 2 - a = 0 := by simpa using ha
    have : a * a = a := by
      have := sub_eq_zero.mp h0
      rwa [sq] at this
    exact this
  · rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact haz

/-! ### Local rings from idempotents -/

/-- **Idempotents in a domain are `0` or `1`.** -/
theorem IsIdempotentElem.eq_zero_or_eq_one_of_isDomain {A : Type*}
    [CommRing A] [IsDomain A] {a : A} (ha : IsIdempotentElem a) :
    a = 0 ∨ a = 1 := by
  rcases mul_eq_zero.mp
      (show a * (a - 1) = 0 by rw [mul_sub, ha.eq, mul_one, sub_self]) with
    h | h
  · exact Or.inl h
  · exact Or.inr (by rwa [sub_eq_zero] at h)

/-- **An idempotent in the Jacobson radical vanishes**: `1 − e` is a
unit and kills `e`. -/
theorem IsIdempotentElem.eq_zero_of_mem_jacobson_bot {S : Type*}
    [CommRing S] {e : S} (he : IsIdempotentElem e)
    (hmem : e ∈ Ideal.jacobson (⊥ : Ideal S)) : e = 0 := by
  have hunit : IsUnit (1 - e) := by
    have h := Ideal.mem_jacobson_bot.mp hmem (-1)
    have h1 : e * (-1) + 1 = 1 - e := by ring
    rwa [h1] at h
  have hzero : (1 - e) * e = 0 := by
    rw [sub_mul, one_mul, he.eq, sub_self]
  obtain ⟨u, hu⟩ := hunit
  calc e = (↑u⁻¹ * (1 - e)) * e := by rw [← hu]; simp
    _ = ↑u⁻¹ * ((1 - e) * e) := by ring
    _ = 0 := by rw [hzero, mul_zero]

/-- **An artinian commutative ring with no nontrivial idempotents is
local**: the descending chain `(aⁿ)` stabilizes, producing an
idempotent `x·aᴺ` which is `0` (then `a` is nilpotent and `1 − a` is
a unit) or `1` (then `a` is a unit). -/
theorem IsLocalRing.of_isArtinianRing_isIdempotentElem {S : Type*}
    [CommRing S] [IsArtinianRing S] [Nontrivial S]
    (h : ∀ x : S, IsIdempotentElem x → x = 0 ∨ x = 1) :
    IsLocalRing S := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  -- the descending chain of principal ideals generated by powers
  have hmono : Monotone (fun n : ℕ =>
      OrderDual.toDual (Ideal.span {a ^ n})) := by
    intro m n hmn
    refine Ideal.span_le.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have : a ^ n = a ^ (n - m) * a ^ m := by
      rw [← pow_add]
      congr 1
      omega
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes
    (⟨fun n : ℕ => OrderDual.toDual (Ideal.span {a ^ n}), hmono⟩ :
      ℕ →o (Ideal S)ᵒᵈ)
  set N : ℕ := n + 1 with hN
  have hspan : Ideal.span {a ^ N} = Ideal.span {a ^ (2 * N)} := by
    have h1 := hn N (by omega)
    have h2 := hn (2 * N) (by omega)
    exact (h1.symm.trans h2 :)
  have hmem : a ^ N ∈ Ideal.span {a ^ (2 * N)} := by
    rw [← hspan]
    exact Ideal.subset_span rfl
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hmem
  -- `x * aᴺ` is idempotent
  have hidem : IsIdempotentElem (x * a ^ N) := by
    show x * a ^ N * (x * a ^ N) = x * a ^ N
    calc x * a ^ N * (x * a ^ N) = x * (x * (a ^ N * a ^ N)) := by ring
      _ = x * (x * a ^ (2 * N)) := by rw [← pow_add]; ring_nf
      _ = x * a ^ N := by rw [hx]
  rcases h _ hidem with h0 | h1
  · -- `aᴺ = 0`, so `a` is nilpotent and `1 − a` is a unit
    refine Or.inr ?_
    have haN : a ^ N = 0 := by
      calc a ^ N = x * a ^ (2 * N) := hx.symm
        _ = (x * a ^ N) * a ^ N := by rw [two_mul, pow_add]; ring
        _ = 0 := by rw [h0, zero_mul]
    exact IsNilpotent.isUnit_one_sub ⟨N, haN⟩
  · -- `x * aᴺ = 1`, so `a` is a unit
    refine Or.inl ?_
    refine IsUnit.of_mul_eq_one (x * a ^ n) ?_
    calc a * (x * a ^ n) = x * a ^ N := by rw [hN]; ring
      _ = 1 := h1
