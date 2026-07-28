/-
GaloisRepresentation/HardlyRamified/DifferentIdeal.lean — own work for the
Fermat project (not vendored from the FLT project).
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.Order.KonigLemma
/-!
# Different-ideal and discriminant-exponent bounds for a number field

Three statements of ordinary algebraic number theory, hoisted out of
`GaloisRepresentation/HardlyRamified/ModThree.lean` at the release-15
integration (2026-07-28).  Nothing here mentions an elliptic curve, a Galois
representation, or the mod-`3` argument; they are `differentIdeal`,
`NumberField.discr` and `Ideal.ramificationIdx'` and nothing else.

**WHY THIS MODULE EXISTS: it is a BUILD-TIME cut, not a mathematical one.**
`HermiteMinkowski.lean` used exactly TWO names from `ModThree.lean`
(`discr_factorization_le_of_forall_differentIdeal_pow_dvd` and
`not_pow_ramificationIdx_dvd_differentIdeal`) and imported the whole 66 000-line
module for them.  `ModThree` is the single most expensive module in the tree
(~680 s of single-threaded elaboration, and elaboration is one core per file),
and that import put it on the critical path *before*
`HermiteMinkowski → HilbertModularity → Deformation → KhareWintenberger →
Patching → Interface → Family`.  Moving these three declarations here and
pointing `HermiteMinkowski` at this module instead takes `ModThree` off that
chain entirely; it still has to be built, but now in parallel with it.

`ModThree.lean` `public import`s this module, so every reference there resolves
unchanged, and `HilbertModularity.lean` — whose single `ModThree` name was
`discr_factorization_le_of_forall_differentIdeal_pow_dvd` — reaches it through
`HermiteMinkowski`.  No statement, no proof and no import of any of the three
was changed by the move.

**If you add anything here, keep it mathlib-facing.**  The value of this module
is that its import cone is `Mathlib` only; a project import would put the thing
it imports back on the critical path.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

open UniqueFactorizationMonoid in
/-- **The discriminant exponent from per-prime different-exponent
bounds** (PROVEN, isolated 2026-07-23 from the two discriminant
exponent leaves below): for a number field `K`, a rational prime `p`
and weights `a, b`, if every prime `Q` of `𝓞 K` over `p` satisfies
`a·d_Q ≤ b·e_Q` for its different exponent `d_Q` — stated
multiplicity-free: every `d` with `Q^d ∣ 𝔡_{K/ℚ}` has
`a·d ≤ b·e(Q∣p)` — then `a·v_p(d_K) ≤ b·[K:ℚ]`. Intended proof (norm
bookkeeping, no new arithmetic): `N(𝔡_{K/ℚ}) = |d_K|`
(`NumberField.absNorm_differentIdeal`), so
`v_p(d_K) = Σ_{Q∣p} f_Q·d_Q` by multiplicativity of `Ideal.absNorm`
along the factorization of the different into primes, whence
`a·v_p(d_K) = Σ_{Q∣p} f_Q·(a·d_Q) ≤ b·Σ_{Q∣p} f_Q·e_Q = b·[K:ℚ]`
(`Ideal.sum_ramification_inertia`). PROVEN 2026-07-23 along exactly
that route: the different is factored into `normalizedFactors`, the
norm is pushed through the product (`map_prod`), `Nat.factorization`
distributes over it, primes not over `p` contribute `0`
(`Ideal.exists_isMaximal_dvd_of_dvd_absNorm'`), primes over `p`
contribute `d_Q·f_Q` (`Ideal.absNorm_eq_pow_inertiaDeg'`), and the
per-prime hypothesis plus `Ideal.sum_ramification_inertia` close. -/
theorem discr_factorization_le_of_forall_differentIdeal_pow_dvd
    (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) (a b : ℕ)
    (h : ∀ Q : Ideal (NumberField.RingOfIntegers K), Q.IsPrime →
      ((p : NumberField.RingOfIntegers K) ∈ Q) → ∀ d : ℕ,
      Q ^ d ∣ differentIdeal ℤ (NumberField.RingOfIntegers K) →
      a * d ≤ b * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) Q) :
    a * (NumberField.discr K).natAbs.factorization p ≤
      b * Module.finrank ℚ K := by
  classical
  set R := NumberField.RingOfIntegers K with hRdef
  set D := differentIdeal ℤ R with hDdef
  have hD0 : D ≠ 0 := by
    rw [hDdef, Submodule.zero_eq_bot]
    exact differentIdeal_ne_bot
  have hnorm : Ideal.absNorm D = (NumberField.discr K).natAbs :=
    NumberField.absNorm_differentIdeal K R
  rw [← hnorm]
  -- the factorization of the different into primes
  have hDprod : D = ∏ Q ∈ (normalizedFactors D).toFinset,
      Q ^ (normalizedFactors D).count Q := by
    conv_lhs => rw [← associated_iff_eq.mp (prod_normalizedFactors hD0)]
    exact Finset.prod_multiset_count _
  have hQprime : ∀ Q ∈ (normalizedFactors D).toFinset, Prime Q := fun Q hQ =>
    prime_of_normalized_factor Q (Multiset.mem_toFinset.mp hQ)
  have habs0 : ∀ Q ∈ (normalizedFactors D).toFinset,
      Ideal.absNorm Q ≠ 0 := fun Q hQ => by
    rw [Ne, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
    exact (hQprime Q hQ).ne_zero
  -- multiplicativity of the norm along the factorization
  have hnormD : Ideal.absNorm D = ∏ Q ∈ (normalizedFactors D).toFinset,
      Ideal.absNorm Q ^ (normalizedFactors D).count Q := by
    conv_lhs => rw [hDprod]
    rw [map_prod]
    exact Finset.prod_congr rfl fun Q _ => map_pow _ _ _
  -- the `p`-adic valuation of the norm, term by term
  have hfact : (Ideal.absNorm D).factorization p
      = ∑ Q ∈ (normalizedFactors D).toFinset,
        (normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p := by
    rw [hnormD, Nat.factorization_prod (fun Q hQ => pow_ne_zero _ (habs0 Q hQ)),
      Finset.sum_apply']
    exact Finset.sum_congr rfl fun Q hQ => by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  -- primes not containing `p` contribute nothing
  have hmem_of_ne : ∀ Q ∈ (normalizedFactors D).toFinset,
      (normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p ≠ 0 →
      ((p : ℕ) : R) ∈ Q := by
    intro Q hQF hne
    by_contra hpnot
    apply hne
    rw [Nat.mul_eq_zero]
    right
    by_contra hne2
    have hdvd : p ∣ Ideal.absNorm Q := Nat.dvd_of_factorization_pos hne2
    obtain ⟨P, hPmax, hPunder, hPdvd⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp Q hdvd
    have hQpr : Q.IsPrime := Ideal.isPrime_of_prime (hQprime Q hQF)
    have hQ0 : Q ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact (hQprime Q hQF).ne_zero
    have hQP : Q = P := (hQpr.isMaximal hQ0).eq_of_le hPmax.ne_top
      (Ideal.le_of_dvd hPdvd)
    apply hpnot
    have hmemP : algebraMap ℤ R ((p : ℕ) : ℤ) ∈ P := by
      have hu : ((p : ℕ) : ℤ) ∈ P.under ℤ := by
        rw [hPunder]
        exact Ideal.mem_span_singleton_self _
      exact hu
    rw [map_natCast] at hmemP
    rw [hQP]
    exact hmemP
  have hsum : (Ideal.absNorm D).factorization p =
      ∑ Q ∈ (normalizedFactors D).toFinset.filter (fun Q => ((p : ℕ) : R) ∈ Q),
        (normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p := by
    rw [hfact]
    exact (Finset.sum_filter_of_ne hmem_of_ne).symm
  -- the setup at `p`
  have hpZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hspan0 : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI hspanMax : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    (((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      hpZ).isMaximal hspan0)
  have hmain := Ideal.sum_ramification_inertia R ℚ K hspan0
  -- the per-prime bound
  have hle : ∀ Q ∈ (normalizedFactors D).toFinset.filter
      (fun Q => ((p : ℕ) : R) ∈ Q),
      a * ((normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p) ≤
      b * (Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q *
        Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q) := by
    intro Q hQ
    obtain ⟨hQF, hpQ⟩ := Finset.mem_filter.mp hQ
    have hQpr : Q.IsPrime := Ideal.isPrime_of_prime (hQprime Q hQF)
    haveI := hQpr
    haveI hlies : Q.LiesOver (Ideal.span {((p : ℕ) : ℤ)}) :=
      (Ideal.liesOver_span_iff hQpr.ne_top hpZ).mpr (by exact_mod_cast hpQ)
    have hf : (Ideal.absNorm Q).factorization p =
        Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q := by
      rw [Ideal.absNorm_eq_pow_inertiaDeg' Q hp, hp.factorization_pow,
        Finsupp.single_eq_same]
    have hdvd : Q ^ (normalizedFactors D).count Q ∣ D := by
      conv_rhs => rw [hDprod]
      exact Finset.dvd_prod_of_mem _ hQF
    have hcntle : a * (normalizedFactors D).count Q ≤
        b * Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q :=
      h Q hQpr hpQ ((normalizedFactors D).count Q) hdvd
    calc a * ((normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p)
        = (a * (normalizedFactors D).count Q) *
          (Ideal.absNorm Q).factorization p := by ring
      _ ≤ (b * Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q) *
          (Ideal.absNorm Q).factorization p :=
        Nat.mul_le_mul_right _ hcntle
      _ = b * (Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q *
          Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q) := by
        rw [hf]; ring
  have hsub : (normalizedFactors D).toFinset.filter
      (fun Q => ((p : ℕ) : R) ∈ Q) ⊆
      IsDedekindDomain.primesOverFinset (Ideal.span {((p : ℕ) : ℤ)}) R := by
    intro Q hQ
    obtain ⟨hQF, hpQ⟩ := Finset.mem_filter.mp hQ
    have hQpr : Q.IsPrime := Ideal.isPrime_of_prime (hQprime Q hQF)
    rw [IsDedekindDomain.mem_primesOverFinset_iff hspan0]
    exact ⟨hQpr, (Ideal.liesOver_span_iff hQpr.ne_top hpZ).mpr
      (by exact_mod_cast hpQ)⟩
  rw [hsum, Finset.mul_sum]
  calc ∑ Q ∈ (normalizedFactors D).toFinset.filter
        (fun Q => ((p : ℕ) : R) ∈ Q),
        a * ((normalizedFactors D).count Q * (Ideal.absNorm Q).factorization p)
      ≤ ∑ Q ∈ (normalizedFactors D).toFinset.filter
        (fun Q => ((p : ℕ) : R) ∈ Q),
        b * (Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q *
          Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q) :=
      Finset.sum_le_sum hle
    _ ≤ ∑ Q ∈ IsDedekindDomain.primesOverFinset
          (Ideal.span {((p : ℕ) : ℤ)}) R,
        b * (Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q *
          Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q) :=
      Finset.sum_le_sum_of_subset hsub
    _ = b * Module.finrank ℚ K := by rw [← Finset.mul_sum, hmain]

open Module in
/-- **Nonvanishing of the trace form of a tame local algebra** (PROVEN
2026-07-23; the residue-theoretic core of the tame different bound
below): the trace form of a finite local algebra `C` over a field `F`
is nonzero as soon as the residue extension is separable and the
residue-field dimension of `C` is invertible in `F` (the tame case).
Proof: a Cohen-style multiplicative section `C ⧸ m →ₐ[F] C` (formal
smoothness of the separable residue extension against the nilpotent
maximal ideal, `Algebra.FormallySmooth.lift`) turns `C` into a
`C ⧸ m`-vector space, and transitivity of the trace evaluates the
trace of a residue scalar `y` as `n • Tr_{(C⧸m)/F}(y)` with
`n = dim_{C⧸m} C`, nonzero for suitable `y` because the separable
residue trace is nonzero (`Algebra.trace_ne_zero`). -/
lemma exists_trace_ne_zero_of_isNilpotent
    (F C : Type*) [Field F] [CommRing C] [Algebra F C] [Module.Finite F C]
    (m : Ideal C) (hm : IsNilpotent m) [hmax : m.IsMaximal]
    [Algebra.IsSeparable F (C ⧸ m)]
    (hd : ∀ n : ℕ, finrank F C = finrank F (C ⧸ m) * n → (n : F) ≠ 0) :
    ∃ w : C, Algebra.trace F C w ≠ 0 := by
  classical
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (C ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m).toLinearMap
      Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ : ∃ y : C ⧸ m, Algebra.trace F (C ⧸ m) y ≠ 0 := by
    simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero F (C ⧸ m)
  -- the Cohen multiplicative section
  haveI : Algebra.FormallySmooth F (C ⧸ m) := by
    haveI := Algebra.FormallyEtale.of_isSeparable F (C ⧸ m)
    infer_instance
  let σ : (C ⧸ m) →ₐ[F] C :=
    Algebra.FormallySmooth.lift m hm (AlgHom.id F (C ⧸ m))
  letI : Algebra (C ⧸ m) C := σ.toAlgebra
  haveI : IsScalarTower F (C ⧸ m) C :=
    IsScalarTower.of_algebraMap_eq' σ.comp_algebraMap.symm
  haveI : Module.Finite (C ⧸ m) C :=
    Module.Finite.of_restrictScalars_finite F _ _
  refine ⟨algebraMap (C ⧸ m) C y, fun h0 => ?_⟩
  rw [← Algebra.trace_trace (S := C ⧸ m), Algebra.trace_algebraMap,
    map_nsmul, nsmul_eq_mul] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hd _ (Module.finrank_mul_finrank F (C ⧸ m) C).symm h1
  · exact hy h1

open UniqueFactorizationMonoid in
/-- **The tame different bound** (PROVEN 2026-07-23; Serre, *Corps
Locaux* III §6 Prop. 13 / Neukirch III.2.6): if the ramification index
`e = e(Q∣p)` of a prime `Q` of `𝓞 K` over the rational prime `p` is
not divisible by `p` (tame ramification — the residue extension is an
extension of finite fields, hence automatically separable), then the
different exponent of `Q` is at most `e − 1`, stated as `Q^e ∤ 𝔡_{K/ℚ}`
(mathlib has the matching lower half `pow_sub_one_dvd_differentIdeal`).
Proof: write `pO_K = Q^e · J` exactly (`Ideal.eq_prime_pow_mul_coprime`
plus the `normalizedFactors`-count characterization of `e`); the trace
form of the tame factor `O_K ⧸ Q^e` over `𝔽_p` is nonzero
(`exists_trace_ne_zero_of_isNilpotent`, with `dim = e·f` by
`Ideal.Factors.finrank_pow_ramificationIdx` and `p ∤ e`), so the CRT
lift of a trace-nonzero element supported on the `Q^e`-component has
`intTrace ∉ (p)`, and `not_dvd_differentIdeal_of_intTrace_not_mem`
closes. -/
theorem not_pow_ramificationIdx_dvd_differentIdeal
    (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (Q : Ideal (NumberField.RingOfIntegers K)) (hQ : Q.IsPrime)
    (hmem : (p : NumberField.RingOfIntegers K) ∈ Q)
    (htame : ¬ (p ∣ Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) Q)) :
    ¬ Q ^ Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) Q ∣
      differentIdeal ℤ (NumberField.RingOfIntegers K) := by
  classical
  set R := NumberField.RingOfIntegers K with hRdef
  haveI := hQ
  -- the setup at `p`
  have hpZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hspan0 : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI hspanMax : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    (((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      hpZ).isMaximal hspan0)
  haveI hlies : Q.LiesOver (Ideal.span {((p : ℕ) : ℤ)}) :=
    (Ideal.liesOver_span_iff hQ.ne_top hpZ).mpr (by exact_mod_cast hmem)
  have hmap0 : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ R) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hspan0
  have hQ0 : Q ≠ ⊥ := ne_bot_of_le_ne_bot hmap0
    (Ideal.map_le_of_le_comap (Q.over_def (Ideal.span {((p : ℕ) : ℤ)})).le)
  haveI hQmax : Q.IsMaximal := hQ.isMaximal hQ0
  set e := Ideal.ramificationIdx' (Ideal.span {((p : ℕ) : ℤ)}) Q with hedef
  have he0 : e ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q hspan0
  -- the exact factorization `map p = Q ^ e * J` with `Q ⊔ J = ⊤`
  obtain ⟨J, hsup, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hmap0 Q
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
    hmap0 hQ hQ0, ← hedef] at hfac
  have hcop : IsCoprime (Q ^ e) J :=
    (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow_left
  -- residue-quotient algebra structures
  letI : Algebra (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q ^ e) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp (Ideal.le_of_dvd ⟨J, hfac⟩))
  letI : Algebra (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.mp (Ideal.le_of_dvd
        ⟨Q ^ e, hfac.trans (mul_comm _ _)⟩))
  -- the CRT decomposition of `R ⧸ pR`
  letI ε : (R ⧸ (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ R))
      ≃ₐ[ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}] ((R ⧸ Q ^ e) × R ⧸ J) :=
    { __ := (Ideal.quotEquivOfEq hfac).trans
        (Ideal.quotientMulEquivQuotientProd (Q ^ e) J hcop),
      commutes' := Quotient.ind fun _ => rfl }
  -- the maximal ideal of `R ⧸ Q ^ e` and its residue field
  set m : Ideal (R ⧸ Q ^ e) := Q.map (Ideal.Quotient.mk (Q ^ e)) with hmdef
  have hnilp : IsNilpotent m := ⟨e, by
    rw [hmdef, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_quotient_self]⟩
  letI ε₂ : ((R ⧸ Q ^ e) ⧸ m) ≃+* R ⧸ Q :=
    DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self he0)
  haveI hmmax : m.IsMaximal := Ideal.Quotient.maximal_of_isField m
    (ε₂.toMulEquiv.isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mp hQmax))
  letI ε₂ₐ : ((R ⧸ Q ^ e) ⧸ m) ≃ₐ[ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}] (R ⧸ Q) :=
    { __ := ε₂,
      commutes' := fun x => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl }
  haveI hsep : Algebra.IsSeparable (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)})
      ((R ⧸ Q ^ e) ⧸ m) := by
    letI : Field (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) := Ideal.Quotient.field _
    letI : Field (R ⧸ Q) := Ideal.Quotient.field Q
    haveI : Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) :=
      Ring.HasFiniteQuotients.finiteQuotient hspan0
    haveI : Module.Finite ℤ (R ⧸ Q) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ Q).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI : Module.Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q) :=
      Module.Finite.of_restrictScalars_finite ℤ _ _
    haveI : Algebra.IsAlgebraic (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q) :=
      Algebra.IsAlgebraic.of_finite _ _
    exact AlgEquiv.Algebra.isSeparable ε₂ₐ.symm
  -- the dimension bookkeeping: `dim_F (R ⧸ Q^e) = e * f`, `dim_F κ = f`
  have hQmemF : Q ∈ (factors ((Ideal.span {((p : ℕ) : ℤ)}).map
      (algebraMap ℤ R))).toFinset := by
    rw [Multiset.mem_toFinset, factors_eq_normalizedFactors, ← Multiset.count_pos,
      ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 hQ hQ0]
    exact Nat.pos_of_ne_zero he0
  have hEF : Module.finrank (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q ^ e) =
      e * Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q :=
    Ideal.Factors.finrank_pow_ramificationIdx
      (Ideal.span {((p : ℕ) : ℤ)}) ⟨Q, hQmemF⟩
  have hkap : Module.finrank (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) ((R ⧸ Q ^ e) ⧸ m) =
      Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q := by
    rw [Ideal.inertiaDeg'_algebraMap]
    exact ε₂ₐ.toLinearEquiv.finrank_eq
  have hf0 : Ideal.inertiaDeg' (Ideal.span {((p : ℕ) : ℤ)}) Q ≠ 0 :=
    Ideal.inertiaDeg'_ne_zero _ _
  -- the tame trace element on `R ⧸ Q ^ e`
  letI : Field (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) := Ideal.Quotient.field _
  haveI : Module.Finite ℤ (R ⧸ Q ^ e) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ (Q ^ e)).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q ^ e) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨w, hw⟩ := exists_trace_ne_zero_of_isNilpotent
    (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ Q ^ e) m hnilp
    (fun n hn => by
      rw [hEF, hkap, mul_comm e] at hn
      have hne : n = e := Nat.eq_of_mul_eq_mul_left
        (Nat.pos_of_ne_zero hf0) hn.symm
      rw [hne]
      intro h0
      apply htame
      have hzero : (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : ℤ)}))
          ((e : ℕ) : ℤ) = 0 := by
        rw [map_natCast]
        exact h0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hzero
      exact_mod_cast hzero)
  -- the CRT lift of `(w, 0)` and its trace
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (ε.symm (w, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem ℤ (Q ^ e) J hfac.symm
    y ?_ ?_
  · have h2 := congr((ε $hy).2)
    simp only [AlgEquiv.apply_symm_apply] at h2
    simpa [ε, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.quotientMulEquivQuotientProd] using h2
  · haveI : Module.Finite ℤ (R ⧸ J) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ J).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI : Module.Finite (ℤ ⧸ Ideal.span {((p : ℕ) : ℤ)}) (R ⧸ J) :=
      Module.Finite.of_restrictScalars_finite ℤ _ _
    rw [← Ideal.Quotient.eq_zero_iff_mem,
      ← Algebra.trace_quotient_eq_of_isDedekindDomain, hy,
      Algebra.trace_eq_of_algEquiv ε.symm (w, 0),
      Algebra.trace_prod_apply]
    simpa using hw
end GaloisRepresentation.IsHardlyRamified
