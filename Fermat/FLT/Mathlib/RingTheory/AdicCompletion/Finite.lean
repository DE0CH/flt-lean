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

The final section (added 2026-07-26) splits off the LOCAL FACTOR of a
module-finite algebra at a maximal ideal. It has NO CONSUMER YET, and the
consumer it was written for is named precisely in the docstring of
`exists_isIdempotentElem_isLocalRing_quotient_of_moduleFinite` below: the
`W(k)` base-change narrowing recorded under "NARROWINGS IDENTIFIED" in the
docstring of `nonempty_potentialHeckeDatum_of_five_le`
(`HardlyRamified/HilbertModularity.lean`), which that audit names as "the
next real reduction" of the potential-modularity citation and records as
blocked on exactly this missing decomposition. Writing the consumer is a
CUT-LEVEL change to the `HilbertHeckeAlgebra` structure and was therefore
deliberately not made here — see the report note in the commit message.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Over

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

/-! ### Splitting off the local factor at a maximal ideal

The three declarations below supply what a survey of the mathlib pin
(2026-07-26) found to be genuinely absent: the decomposition of a
module-finite algebra over a complete Noetherian local ring into local
factors. Mathlib has `HenselianLocalRing` (used nowhere else in the
library), idempotent lifting along a NILPOTENT kernel
(`CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`) and the
decomposition of a REDUCED artinian ring (`IsArtinianRing.equivPi`), but
not the statement proven here, and neither does `~/cs/FLT`.

The route is the classical one, and every step is already in this file or
in mathlib: the maximal-ideal extension is a henselian pair
(`HenselianRing.of_finite_algebra`); the quotient by it is artinian; in an
artinian ring the maximal ideals are finite in number and the Jacobson
radical is nilpotent, so a maximal ideal is cut out by an idempotent
obtained from a comaximal splitting and Newton's iteration; and that
idempotent lifts along the henselian pair.
-/

/-- **A quotient with a unique maximal ideal above it is local.** If `I ≤ 𝔪`
with `𝔪` maximal, and `𝔪` is the ONLY maximal ideal containing `I`, then
`A ⧸ I` is a local ring: maximal ideals of `A ⧸ I` are determined by their
contractions, which are forced to be `𝔪`. -/
theorem IsLocalRing.of_quotient_unique_isMaximal {A : Type*} [CommRing A]
    (I 𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) (hI : I ≤ 𝔪)
    (huniq : ∀ M : Ideal A, M.IsMaximal → I ≤ M → M = 𝔪) :
    IsLocalRing (A ⧸ I) := by
  haveI : Nontrivial (A ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (fun htop => h𝔪.ne_top (top_le_iff.mp (htop ▸ hI)))
  have hsurj := Ideal.Quotient.mk_surjective (I := I)
  have key : ∀ M' : Ideal (A ⧸ I), M'.IsMaximal →
      Ideal.comap (Ideal.Quotient.mk I) M' = 𝔪 := by
    intro M' hM'
    haveI := hM'
    refine huniq _ (Ideal.comap_isMaximal_of_surjective _ hsurj) ?_
    intro x hx
    show Ideal.Quotient.mk I x ∈ M'
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact M'.zero_mem
  obtain ⟨M₀, hM₀⟩ := Ideal.exists_maximal (A ⧸ I)
  refine IsLocalRing.of_unique_max_ideal ⟨M₀, hM₀, ?_⟩
  intro M' hM'
  rw [← Ideal.map_comap_of_surjective _ hsurj M', ← Ideal.map_comap_of_surjective _ hsurj M₀,
    key M' hM', key M₀ hM₀]

/-- **A maximal ideal of an artinian ring is cut out by an idempotent.**
For `𝔪` maximal in an artinian commutative ring there is an idempotent `e`
with `1 - e ∈ 𝔪` and `e` in every OTHER maximal ideal — so `e` is the
"characteristic function" of the factor at `𝔪`.

An artinian ring has finitely many maximal ideals
(`IsArtinianRing.setOf_isMaximal_finite`), so with `K` the intersection of
those other than `𝔪` one has `𝔪 ⊔ K = ⊤` (else a maximal ideal would
contain both, forcing `K ≤ 𝔪` and, `𝔪` being prime and the family finite,
`𝔪` to BE one of them) and `𝔪 ⊓ K ≤ jacobson ⊥`. Writing `1 = a + b` with
`a ∈ 𝔪`, `b ∈ K` makes `b` idempotent modulo the Jacobson radical, which
is nilpotent (`IsArtinianRing.isNilpotent_jacobson_bot`), so Newton's
iteration (`exists_isIdempotentElem_eq_of_ker_isNilpotent`) turns it into a
genuine idempotent congruent to `b`. -/
theorem IsArtinianRing.exists_isIdempotentElem_of_isMaximal {A : Type*} [CommRing A]
    [IsArtinianRing A] (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    ∃ e : A, IsIdempotentElem e ∧ 1 - e ∈ 𝔪 ∧
      ∀ M : Ideal A, M.IsMaximal → M ≠ 𝔪 → e ∈ M := by
  classical
  haveI := h𝔪
  set N : Ideal A := Ideal.jacobson (⊥ : Ideal A) with hNdef
  have hfin : {I : Ideal A | I.IsMaximal}.Finite := IsArtinianRing.setOf_isMaximal_finite A
  set T : Finset (Ideal A) := hfin.toFinset.erase 𝔪 with hTdef
  have hTmem : ∀ M ∈ T, M.IsMaximal ∧ M ≠ 𝔪 := by
    intro M hM
    rw [hTdef, Finset.mem_erase, Set.Finite.mem_toFinset] at hM
    exact ⟨hM.2, hM.1⟩
  have hTof : ∀ M : Ideal A, M.IsMaximal → M ≠ 𝔪 → M ∈ T := by
    intro M hM hne
    rw [hTdef, Finset.mem_erase, Set.Finite.mem_toFinset]
    exact ⟨hne, hM⟩
  set K : Ideal A := T.inf id with hKdef
  have hNle : ∀ M : Ideal A, M.IsMaximal → N ≤ M := fun M hM => sInf_le ⟨bot_le, hM⟩
  have hinf : 𝔪 ⊓ K ≤ N := by
    refine le_sInf ?_
    rintro J ⟨-, hJ⟩
    by_cases hJ𝔪 : J = 𝔪
    · exact hJ𝔪 ▸ inf_le_left
    · exact inf_le_right.trans (Finset.inf_le (f := id) (hTof J hJ hJ𝔪))
  have hsup : 𝔪 ⊔ K = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM𝔪 : 𝔪 = M := h𝔪.eq_of_le hM.ne_top (le_sup_left.trans hle)
    have hKle : K ≤ 𝔪 := hM𝔪 ▸ (le_sup_right.trans hle)
    obtain ⟨M', hM'T, hM'le⟩ := (Ideal.IsPrime.inf_le' h𝔪.isPrime).mp hKle
    exact (hTmem M' hM'T).2 ((hTmem M' hM'T).1.eq_of_le h𝔪.ne_top hM'le)
  have h1mem : (1 : A) ∈ 𝔪 ⊔ K := by rw [hsup]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1mem
  have hbsq : b * b - b ∈ N := by
    have haeq : a = 1 - b := eq_sub_of_add_eq hab
    have hrw : b * b - b = -(a * b) := by rw [haeq]; ring
    rw [hrw]
    exact neg_mem (hinf ⟨Ideal.mul_mem_right _ _ ha, Ideal.mul_mem_left _ _ hb⟩)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have hnil : ∀ x ∈ RingHom.ker (Ideal.Quotient.mk N), IsNilpotent x := by
    intro x hx
    rw [Ideal.mk_ker] at hx
    refine ⟨n, ?_⟩
    have hxp : x ^ n ∈ N ^ n := Ideal.pow_mem_pow hx n
    rw [hNdef] at hxp
    rw [hn] at hxp
    simpa using hxp
  have hidq : IsIdempotentElem (Ideal.Quotient.mk N b) := by
    show Ideal.Quotient.mk N b * Ideal.Quotient.mk N b = Ideal.Quotient.mk N b
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hbsq
  obtain ⟨e, he, hfe⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk N) hnil _ ⟨b, rfl⟩ hidq
  have heb : e - b ∈ N := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]; exact hfe
  refine ⟨e, he, ?_, ?_⟩
  · have haeq : a = 1 - b := eq_sub_of_add_eq hab
    have hsplit : (1 : A) - e = a - (e - b) := by rw [haeq]; ring
    rw [hsplit]
    exact Ideal.sub_mem _ ha (hNle 𝔪 h𝔪 heb)
  · intro M hM hne
    have hbM : b ∈ M := Finset.inf_le (f := id) (hTof M hM hne) hb
    have hsplit : e = b + (e - b) := by ring
    rw [hsplit]
    exact Ideal.add_mem _ hbM (hNle M hM heb)

/-- **The local factor of a module-finite algebra over a complete
Noetherian local ring is a direct factor, cut out by an idempotent.**

Given `A` module-finite over a complete Noetherian local `R` and a maximal
ideal `𝔪` of `A`, there is an idempotent `e ∈ A` with `1 - e ∈ 𝔪` such that
`A ⧸ (1 - e)` is a LOCAL ring and `A ≃ₐ[R] A ⧸ (1 - e) × A ⧸ (e)`. The first
factor is the local ring of `A` at `𝔪`.

This is the statement that lets one pass from a Hecke algebra to its
localization at a maximal ideal — and, with `R = W(k)`, from `𝕋 ⊗ W(k)` to
the local factor — without citing it. The proof reduces modulo the extended
maximal ideal `J = 𝔪_R · A`, which makes `A ⧸ J` a finite algebra over the
residue field of `R`, hence artinian; applies
`IsArtinianRing.exists_isIdempotentElem_of_isMaximal` there; and lifts the
idempotent back along the henselian pair `(A, J)` of
`HenselianRing.of_finite_algebra`. Locality of the factor comes from
`IsLocalRing.of_quotient_unique_isMaximal`: since `J` sits in the Jacobson
radical, maximal ideals of `A` and of `A ⧸ J` correspond, and downstairs `e`
already separated `𝔪` from all the others. -/
theorem exists_isIdempotentElem_isLocalRing_quotient_of_moduleFinite
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {A : Type*} [CommRing A] [Algebra R A] [Module.Finite R A]
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    ∃ e : A, IsIdempotentElem e ∧ 1 - e ∈ 𝔪 ∧
      IsLocalRing (A ⧸ Ideal.span {1 - e}) ∧
      Nonempty (A ≃ₐ[R] (A ⧸ Ideal.span {1 - e}) × (A ⧸ Ideal.span {e})) := by
  classical
  haveI := h𝔪
  haveI hnt : Nontrivial A := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact h𝔪.ne_top (Subsingleton.elim _ _)
  set J : Ideal A := (IsLocalRing.maximalIdeal R).map (algebraMap R A) with hJdef
  haveI hHen : HenselianRing A J := HenselianRing.of_finite_algebra R A
  have hJjac : J ≤ Ideal.jacobson (⊥ : Ideal A) := hHen.jac
  have hJmax : ∀ M : Ideal A, M.IsMaximal → J ≤ M :=
    fun M hM => hJjac.trans (sInf_le ⟨bot_le, hM⟩)
  haveI hlies : J.LiesOver (IsLocalRing.maximalIdeal R) := by
    constructor
    refine le_antisymm Ideal.le_comap_map (IsLocalRing.le_maximalIdeal ?_)
    intro htop
    have h1 : (1 : R) ∈ Ideal.under R J := by rw [htop]; trivial
    have h2 : (1 : A) ∈ J := by simpa using h1
    simpa using Ideal.mem_jacobson_bot.mp (hJjac h2) (-1)
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  haveI hart : IsArtinianRing (A ⧸ J) :=
    IsArtinianRing.of_finite (R ⧸ IsLocalRing.maximalIdeal R) (A ⧸ J)
  have hsurj := Ideal.Quotient.mk_surjective (I := J)
  set 𝔪₀ : Ideal (A ⧸ J) := 𝔪.map (Ideal.Quotient.mk J) with h𝔪₀def
  have hcm : ∀ M : Ideal A, J ≤ M →
      Ideal.comap (Ideal.Quotient.mk J) (M.map (Ideal.Quotient.mk J)) = M := by
    intro M hM
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hM]
  have hmaxmap : ∀ M : Ideal A, M.IsMaximal → (M.map (Ideal.Quotient.mk J)).IsMaximal := by
    intro M hM
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hM with htop | h
    · exact absurd (by rw [← hcm M (hJmax M hM), htop, Ideal.comap_top]) hM.ne_top
    · exact h
  haveI h𝔪₀ : 𝔪₀.IsMaximal := hmaxmap 𝔪 h𝔪
  obtain ⟨ebar, hebar, hebar𝔪, hebarM⟩ :=
    IsArtinianRing.exists_isIdempotentElem_of_isMaximal 𝔪₀ h𝔪₀
  obtain ⟨e, he, hmke⟩ := HenselianRing.exists_isIdempotentElem_mk_eq (J := J) hebar
  have hone : (1 : A) - e ∈ 𝔪 := by
    have hmem : Ideal.Quotient.mk J (1 - e) ∈ 𝔪₀ := by
      rw [map_sub, map_one, hmke]; exact hebar𝔪
    rw [← hcm 𝔪 (hJmax 𝔪 h𝔪)]
    exact hmem
  have huniq : ∀ M : Ideal A, M.IsMaximal → Ideal.span {(1 : A) - e} ≤ M → M = 𝔪 := by
    intro M hM hspan
    have h1eM : (1 : A) - e ∈ M := hspan (Ideal.subset_span rfl)
    have hM₀ : (M.map (Ideal.Quotient.mk J)).IsMaximal := hmaxmap M hM
    by_cases hcase : M.map (Ideal.Quotient.mk J) = 𝔪₀
    · rw [← hcm M (hJmax M hM), hcase, hcm 𝔪 (hJmax 𝔪 h𝔪)]
    · exfalso
      have hebarM' : ebar ∈ M.map (Ideal.Quotient.mk J) := hebarM _ hM₀ hcase
      have h1bar : (1 : A ⧸ J) - ebar ∈ M.map (Ideal.Quotient.mk J) := by
        have hmm : Ideal.Quotient.mk J (1 - e) ∈ M.map (Ideal.Quotient.mk J) :=
          Ideal.mem_map_of_mem _ h1eM
        rwa [map_sub, map_one, hmke] at hmm
      have hone' : (1 : A ⧸ J) ∈ M.map (Ideal.Quotient.mk J) := by
        have hsum := Ideal.add_mem _ h1bar hebarM'
        simpa using hsum
      exact hM₀.ne_top (Ideal.eq_top_of_isUnit_mem _ hone' isUnit_one)
  refine ⟨e, he, hone, ?_, ?_⟩
  · exact IsLocalRing.of_quotient_unique_isMaximal _ 𝔪 h𝔪
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hone)) huniq
  · exact ⟨AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he (by ring) (by
      have hmul : (1 - e) * e = e - e * e := by ring
      rw [hmul, he.eq, sub_self])⟩
